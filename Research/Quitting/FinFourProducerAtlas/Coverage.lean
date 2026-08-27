/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Research.Quitting.FinFourProducerAtlas.Leaves

/-!
# Exhaustive coverage theorem for the Fin4 producer atlas

A four-player hard residual produces one of six source-distinct leaves.  The
proof performs the high-tail/low-tail split on one fixed selected-row family
and never reselects the table, minimum law, chronology, or endpoint path.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability Math.PMFProduct
open MathUE.FiniteBooleanEndpointOrbit
open QuittingNonsingletonMinimumLawTransfer

/-- The exact high-tail threshold used by the atlas. -/
private def finFourProducerTailThreshold
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound : ℝ} (source : FinFourMinimumAtomProducer reward bound) : ℝ :=
  source.point.2 (some source.atom.terminal) ^ 2 *
    quittingTerminalSemanticDebtSum source.point.1 / 16

/-- A hard residual produces one of the six source-distinct leaves and hence
one of the four natural completion modes.  No table, minimum point, law,
profile sequence, row, or finite endpoint path is reselected downstream. -/
theorem nonempty_finFourProducerResidual_of_hardResidual
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (bound : ℝ)
    (residual : FinFourQuantitativeFullSupportHardResidual reward bound) :
    Nonempty (FinFourProducerResidual reward bound) := by
  obtain ⟨source⟩ := FinFourMinimumAtomProducer.nonempty_of_hardResidual
    reward bound residual
  by_cases hsingleton : source.atom.terminal.val.card = 1
  · exact ⟨.minimumSingleton source hsingleton⟩
  have hcollision : 1 < source.atom.terminal.val.card := by
    have hpositive : 0 < source.atom.terminal.val.card :=
      Finset.card_pos.mpr source.atom.terminal.property
    omega
  obtain ⟨rows⟩ := QuittingMinimumLawCausalSuffixAtom.nonempty_selectedRows
    reward source.point source.atom source.point_mem source.minimum
      source.minimumDebt_pos hcollision
  let highTail : ℕ → Prop := fun rank =>
    finFourProducerTailThreshold source ≤ selectedTailExcess rows rank
  have hstage := rows.eventually_stageMass_gt_square_div_eight source.point_mem
  by_cases hhigh : ∃ᶠ rank in atTop, highTail rank
  · have hboth : ∃ᶠ rank in atTop,
        highTail rank ∧
          source.point.2 (some source.atom.terminal) ^ 2 / 8 <
            selectedStageMass rows rank :=
      hhigh.and_eventually hstage
    obtain ⟨subseq, hsubseq, hselected⟩ :=
      extraction_of_frequently_atTop hboth
    let escape : TailEscapeSubsequence reward source.point source.atom := {
      rows := rows
      subseq := subseq
      subseq_strictMono := hsubseq
      stage_mass_floor := fun rank => (hselected rank).2
      tail_excess_floor := fun rank => by
        simpa only [finFourProducerTailThreshold, highTail] using
          (hselected rank).1
    }
    exact ⟨.tailEscape source escape⟩
  · have hnotHigh : ∀ᶠ rank in atTop, ¬highTail rank :=
      not_frequently.mp hhigh
    have hlow : ∀ᶠ rank in atTop,
        selectedTailExcess rows rank < finFourProducerTailThreshold source :=
      hnotHigh.mono fun rank hn => lt_of_not_ge hn
    have hboth : ∀ᶠ rank in atTop,
        source.point.2 (some source.atom.terminal) ^ 2 / 8 <
            selectedStageMass rows rank ∧
          selectedTailExcess rows rank < finFourProducerTailThreshold source :=
      hstage.and hlow
    rw [Filter.eventually_atTop] at hboth
    obtain ⟨rank, hrank⟩ := hboth
    have hselected := hrank rank (le_rfl)
    let low : FinFourLowTailRow source := {
      rows := rows
      rank := rank
      stage_mass_floor := hselected.1
      tail_excess_lt := by
        simpa only [finFourProducerTailThreshold] using hselected.2
    }
    have hdispatch := quittingPartialPurification_then_finFourSameStage_dispatch
      reward source.point.1 low.profile low.stage low.lambda low.coalition
      source.semantic_mem source.minimum source.minimumDebt_pos low.lambda_pos
      low.lambda_le_stageMass low.lowTail
    rcases hdispatch with hsingleton |
        ⟨finalState, steps, hpath, hsteps, hcomplete, hterminalOrCycle⟩
    · obtain ⟨state, steps, ⟨singleton⟩, hpath, hsteps⟩ := hsingleton
      let producer : FinFourPurifiedSingletonProducer source := {
        low := low
        state := state
        steps := steps
        singleton := singleton
        path := hpath
        steps_le := hsteps
      }
      exact ⟨.purifiedSingleton source producer⟩
    · let purification : FinFourTotalPurificationProducer source := {
        low := low
        finalState := finalState
        steps := steps
        path := hpath
        steps_le := hsteps
        complete := hcomplete
      }
      rcases hterminalOrCycle with horbit |
          ⟨trace, hperiod, hgeometry, hmass, hedge⟩
      · obtain ⟨orbit⟩ := horbit
        let producer : FinFourTerminalSingletonProducer source := {
          purification := purification
          orbit := orbit
        }
        exact ⟨.terminalSingleton source producer⟩
      · let monodromy : FinFourMonodromyProducer source := {
          purification := purification
          trace := trace
          period_le_eight := hperiod
          stage_mass_floor := hmass
          edge_certificate := hedge
        }
        rcases hgeometry with ⟨host, hhost⟩ |
            ⟨first, second, hfirst, hsecond, hdisjoint, hcomplementary⟩
        · let producer : FinFourCommonHostMonodromyProducer source := {
            monodromy := monodromy
            host := host
            host_mem := hhost
          }
          exact ⟨.commonHostMonodromy source producer⟩
        · let producer : FinFourComplementaryPairMonodromyProducer source := {
            monodromy := monodromy
            first := first
            second := second
            first_card := hfirst
            second_card := hsecond
            disjoint := hdisjoint
            complementary := hcomplementary
          }
          exact ⟨.complementaryPairMonodromy source producer⟩

/-- Global four-player coverage: either a uniform-equilibrium payoff already
exists, or the same reward table produces one atlas leaf. -/
theorem uniformPayoff_or_nonempty_finFourProducerResidual
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    {bound : ℝ} (hreward : ∀ terminal who, |reward terminal who| ≤ bound) :
    (∃ payoff : Payoff (Fin 4),
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff) ∨
      Nonempty (FinFourProducerResidual reward bound) := by
  rcases uniformPayoff_or_nonempty_finFourQuantitativeFullSupportHardResidual
      reward hreward with hpayoff | hresidual
  · exact Or.inl hpayoff
  · obtain ⟨residual⟩ := hresidual
    exact Or.inr
      (nonempty_finFourProducerResidual_of_hardResidual reward bound residual)

end GameTheory
