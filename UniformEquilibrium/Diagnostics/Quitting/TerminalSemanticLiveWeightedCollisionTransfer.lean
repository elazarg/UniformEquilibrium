/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticCausalCollisionAtomicOrientation
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticOwnStrategyTransport
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPlateauDefectTelescope

/-!
# Live-weighted collision transfer at one reached row

This module keeps the live factor in the local collision charge.  At one
actual reached row, a nonsingleton stage atom pays either shifted-tail excess
or the gain of one literal pure-endpoint behavioral deviation.  The latter
gain is an exact loss of the mover's unrestricted behavioral debt and, near
the global minimum, is transferred to the other debt coordinates.

The same endpoint update routes the displayed stage atom without any further
mass loss.  These are local transfer and routing statements; no chronological
return or causal regeneration is asserted here.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

private theorem exists_sum_le_card_mul_of_nonempty
    {α : Type*} (s : Finset α) (hs : s.Nonempty) (f : α → ℝ) :
    ∃ a ∈ s, ∑ b ∈ s, f b ≤ (s.card : ℝ) * f a := by
  classical
  by_contra h
  push Not at h
  obtain ⟨a, ha⟩ := hs
  have hsum_lt :
      ∑ b ∈ s, (s.card : ℝ) * f b <
        ∑ _b ∈ s, ∑ c ∈ s, f c := by
    apply Finset.sum_lt_sum
    · intro b hb
      exact (h b hb).le
    · exact ⟨a, ha, h a ha⟩
  have hirrefl :
      (s.card : ℝ) * (∑ b ∈ s, f b) <
        (s.card : ℝ) * (∑ b ∈ s, f b) := by
    calc
      (s.card : ℝ) * (∑ b ∈ s, f b) =
          ∑ b ∈ s, (s.card : ℝ) * f b := by
            rw [Finset.mul_sum]
      _ < ∑ _b ∈ s, ∑ c ∈ s, f c := hsum_lt
      _ = (s.card : ℝ) * (∑ b ∈ s, f b) := by
        simp [nsmul_eq_mul]
  exact (lt_irrefl _ hirrefl)

/-- **Exact live-weighted collision-charge chain.**

The stage mass, live mass, charge, shifted-tail excess, and total local Nash
defect all belong to the same actual profile and row.  In particular, no
live factor is discarded between the collision telescope and the minimum
charge estimate. -/
theorem quittingLiveWeightedCollisionTransfer_chain
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (minimum : QuittingTerminalSemanticPair ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (stage : ℕ) (terminal : {S : Finset ι // S.Nonempty})
    (_hminimumCarrier : minimum ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (hcollision : 1 < terminal.val.card) :
    let minimumDebt := quittingTerminalSemanticDebtSum minimum
    let stageMass := quittingStageCoalitionMass reward profile stage terminal
    let liveMass := quittingLiveMass reward profile stage
    let charge := quittingSpineOpponentAbsorptionDebtCharge reward profile stage
    let excess := quittingSpineDebtExcess reward profile minimumDebt (stage + 1)
    let defect := quittingSpineTotalNashDefect reward profile stage
    stageMass * minimumDebt ≤ liveMass * charge ∧
      liveMass * charge ≤ liveMass * (excess + defect) ∧
      liveMass * (excess + defect) =
        liveMass * excess + liveMass * defect ∧
      liveMass * excess + liveMass * defect ≤ excess + liveMass * defect := by
  dsimp only
  let tail := quittingTerminalSemanticPair reward
    (quittingAllContinueProfileSpine reward profile (stage + 1))
  have htailCarrier : tail ∈ quittingTerminalSemanticCarrier reward :=
    quittingTerminalSemanticPair_mem_carrier reward _
  have hminimumTail : quittingTerminalSemanticDebtSum minimum ≤
      quittingTerminalSemanticDebtSum tail :=
    hminimum tail htailCarrier
  have hstageNonneg :=
    quittingStageCoalitionMass_nonneg reward profile stage terminal
  have hminimumStage := mul_le_mul_of_nonneg_left hminimumTail hstageNonneg
  have hcollisionCharge :=
    quittingStageCoalitionMass_mul_tailDebtSum_le_liveMass_mul_charge
      reward profile stage terminal hcollision
  have hfirst : quittingStageCoalitionMass reward profile stage terminal *
        quittingTerminalSemanticDebtSum minimum ≤
      quittingLiveMass reward profile stage *
        quittingSpineOpponentAbsorptionDebtCharge reward profile stage := by
    exact hminimumStage.trans hcollisionCharge
  have hcharge :=
    minimumTerminalSemantic_sum_opponentAbsorption_charge_le_excess_add_defect
      reward minimum tail (quittingProfileLiveRoot reward profile stage)
        _hminimumCarrier hminimum htailCarrier
  have hcharge' :
      quittingSpineOpponentAbsorptionDebtCharge reward profile stage ≤
        quittingSpineDebtExcess reward profile
            (quittingTerminalSemanticDebtSum minimum) (stage + 1) +
          quittingSpineTotalNashDefect reward profile stage := by
    simpa [quittingSpineOpponentAbsorptionDebtCharge,
      quittingSpineDebtExcess, quittingSpineTotalNashDefect, tail] using hcharge
  have hliveNonneg := quittingLiveMass_nonneg reward profile stage
  have hsecond := mul_le_mul_of_nonneg_left hcharge' hliveNonneg
  have hexcessNonneg : 0 ≤ quittingSpineDebtExcess reward profile
      (quittingTerminalSemanticDebtSum minimum) (stage + 1) := by
    exact quittingSpineDebtExcess_nonneg_of_minimum
      reward profile minimum hminimum (stage + 1)
  have hliveLe := quittingLiveMass_le_one reward profile stage
  have hdropNonneg : 0 ≤
      (1 - quittingLiveMass reward profile stage) *
        quittingSpineDebtExcess reward profile
          (quittingTerminalSemanticDebtSum minimum) (stage + 1) :=
    mul_nonneg (sub_nonneg.mpr hliveLe) hexcessNonneg
  refine ⟨hfirst, hsecond, ?_, ?_⟩
  · ring
  · nlinarith

/-- The sharp half split extracted from the live-weighted charge chain. -/
theorem quittingLiveWeightedCollisionTransfer_halfDichotomy
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (minimum : QuittingTerminalSemanticPair ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (stage : ℕ) (terminal : {S : Finset ι // S.Nonempty})
    (hminimumCarrier : minimum ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (hcollision : 1 < terminal.val.card) :
    let minimumDebt := quittingTerminalSemanticDebtSum minimum
    let stageMass := quittingStageCoalitionMass reward profile stage terminal
    let liveMass := quittingLiveMass reward profile stage
    let excess := quittingSpineDebtExcess reward profile minimumDebt (stage + 1)
    let defect := quittingSpineTotalNashDefect reward profile stage
    stageMass * minimumDebt / 2 ≤ liveMass * excess ∨
      stageMass * minimumDebt / 2 ≤ liveMass * defect := by
  dsimp only
  have hchain := quittingLiveWeightedCollisionTransfer_chain
    reward minimum profile stage terminal hminimumCarrier hminimum hcollision
  rcases hchain with ⟨hfirst, hsecond, heq, _⟩
  have hsum := hfirst.trans hsecond
  rw [heq] at hsum
  by_cases hescape : quittingStageCoalitionMass reward profile stage terminal *
      quittingTerminalSemanticDebtSum minimum / 2 ≤
        quittingLiveMass reward profile stage *
          quittingSpineDebtExcess reward profile
            (quittingTerminalSemanticDebtSum minimum) (stage + 1)
  · exact Or.inl hescape
  · right
    linarith

/-- **Actual pure-endpoint gain alternative.**

If the live-weighted tail-excess arm fails, one player has a literal legal
behavioral endpoint deviation at the same row.  Its exact global payoff gain
is at least the row scale divided by twice the number of players. -/
theorem quittingLiveWeightedCollisionTransfer_tailEscape_or_exists_endpointGain
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (minimum : QuittingTerminalSemanticPair ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (stage : ℕ) (terminal : {S : Finset ι // S.Nonempty})
    (hminimumCarrier : minimum ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (hminimumDebt : 0 < quittingTerminalSemanticDebtSum minimum)
    (hcollision : 1 < terminal.val.card)
    (hmass : 0 < quittingStageCoalitionMass reward profile stage terminal) :
    let tail := quittingTerminalSemanticPair reward
      (quittingAllContinueProfileSpine reward profile (stage + 1))
    let root := quittingProfileLiveRoot reward profile stage
    let minimumDebt := quittingTerminalSemanticDebtSum minimum
    let stageMass := quittingStageCoalitionMass reward profile stage terminal
    let liveMass := quittingLiveMass reward profile stage
    let excess := quittingSpineDebtExcess reward profile minimumDebt (stage + 1)
    liveMass * excess ≥ stageMass * minimumDebt / 2 ∨
      ∃ who,
        let action := quittingRootBestEndpointAction reward tail.1 root who
        let targetProfile := Function.update profile who
          (quittingStagePureEndpointBehaviorDeviation
            reward profile who stage action)
        let gain := quittingTerminalPayoff reward targetProfile who -
          quittingTerminalPayoff reward profile who
        gain = liveMass *
            quittingRootCoordinateNashDefect reward tail.1 root who ∧
          0 < gain ∧
          stageMass * minimumDebt /
              (2 * (Fintype.card ι : ℝ)) ≤ gain := by
  dsimp only
  have hdichotomy := quittingLiveWeightedCollisionTransfer_halfDichotomy
    reward minimum profile stage terminal hminimumCarrier hminimum hcollision
  rcases hdichotomy with hescape | hdefect
  · exact Or.inl hescape
  · right
    obtain ⟨who, _hwho, haverage⟩ := exists_sum_le_card_mul_of_nonempty
      Finset.univ Finset.univ_nonempty
      (fun player => quittingRootCoordinateNashDefect reward
        (quittingTerminalSemanticPair reward
          (quittingAllContinueProfileSpine reward profile (stage + 1))).1
        (quittingProfileLiveRoot reward profile stage) player)
    have hliveNonneg := quittingLiveMass_nonneg reward profile stage
    have hweighted := mul_le_mul_of_nonneg_left haverage hliveNonneg
    have hdefectFormula : quittingSpineTotalNashDefect reward profile stage =
        ∑ player, quittingRootCoordinateNashDefect reward
          (quittingTerminalSemanticPair reward
            (quittingAllContinueProfileSpine reward profile (stage + 1))).1
          (quittingProfileLiveRoot reward profile stage) player := by
      rfl
    rw [hdefectFormula] at hdefect
    have hgain :=
      quittingTerminalPayoff_stageBestEndpointDeviation_sub_eq_liveMass_mul_defect
        reward profile who stage
    let action := quittingRootBestEndpointAction reward
      (quittingTerminalSemanticPair reward
        (quittingAllContinueProfileSpine reward profile (stage + 1))).1
      (quittingProfileLiveRoot reward profile stage) who
    let targetProfile := Function.update profile who
      (quittingStagePureEndpointBehaviorDeviation
        reward profile who stage action)
    let gain := quittingTerminalPayoff reward targetProfile who -
      quittingTerminalPayoff reward profile who
    have hgainFormula : gain = quittingLiveMass reward profile stage *
        quittingRootCoordinateNashDefect reward
          (quittingTerminalSemanticPair reward
            (quittingAllContinueProfileSpine reward profile (stage + 1))).1
          (quittingProfileLiveRoot reward profile stage) who := by
      simpa only [action, targetProfile, gain] using hgain
    have hcardGain : quittingLiveMass reward profile stage *
          (∑ player, quittingRootCoordinateNashDefect reward
            (quittingTerminalSemanticPair reward
              (quittingAllContinueProfileSpine reward profile (stage + 1))).1
            (quittingProfileLiveRoot reward profile stage) player) ≤
        (Fintype.card ι : ℝ) * gain := by
      rw [hgainFormula]
      simpa [Finset.card_univ, mul_assoc, mul_left_comm, mul_comm] using hweighted
    have hscale : quittingStageCoalitionMass reward profile stage terminal *
          quittingTerminalSemanticDebtSum minimum / 2 ≤
        (Fintype.card ι : ℝ) * gain :=
      hdefect.trans hcardGain
    have hcardPos : 0 < (Fintype.card ι : ℝ) := by
      exact_mod_cast Fintype.card_pos
    have hgainPos : 0 < gain := by
      have hscalePos : 0 < quittingStageCoalitionMass reward profile stage terminal *
          quittingTerminalSemanticDebtSum minimum / 2 := by positivity
      nlinarith
    refine ⟨who, hgainFormula, hgainPos, ?_⟩
    rw [div_le_iff₀ (mul_pos (by norm_num) hcardPos)]
    nlinarith

/-- For four players, the selected actual endpoint gain is at least one
eighth of the collision-debt row scale. -/
theorem quittingFinFourLiveWeightedCollisionTransfer_tailEscape_or_endpointGain
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (minimum : QuittingTerminalSemanticPair (Fin 4))
    (profile : (quittingGame reward).BehaviorProfile)
    (stage : ℕ) (terminal : {S : Finset (Fin 4) // S.Nonempty})
    (hminimumCarrier : minimum ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (hminimumDebt : 0 < quittingTerminalSemanticDebtSum minimum)
    (hcollision : 1 < terminal.val.card)
    (hmass : 0 < quittingStageCoalitionMass reward profile stage terminal) :
    let tail := quittingTerminalSemanticPair reward
      (quittingAllContinueProfileSpine reward profile (stage + 1))
    let root := quittingProfileLiveRoot reward profile stage
    let minimumDebt := quittingTerminalSemanticDebtSum minimum
    let stageMass := quittingStageCoalitionMass reward profile stage terminal
    let liveMass := quittingLiveMass reward profile stage
    let excess := quittingSpineDebtExcess reward profile minimumDebt (stage + 1)
    liveMass * excess ≥ stageMass * minimumDebt / 2 ∨
      ∃ who,
        let action := quittingRootBestEndpointAction reward tail.1 root who
        let targetProfile := Function.update profile who
          (quittingStagePureEndpointBehaviorDeviation
            reward profile who stage action)
        let gain := quittingTerminalPayoff reward targetProfile who -
          quittingTerminalPayoff reward profile who
        gain = liveMass *
            quittingRootCoordinateNashDefect reward tail.1 root who ∧
          0 < gain ∧
          stageMass * minimumDebt / 8 ≤ gain := by
  have hresult :=
    quittingLiveWeightedCollisionTransfer_tailEscape_or_exists_endpointGain
      reward minimum profile stage terminal hminimumCarrier hminimum
        hminimumDebt hcollision hmass
  rcases hresult with hescape | ⟨who, hgain, hgainPos, hbound⟩
  · exact Or.inl hescape
  · right
    refine ⟨who, hgain, hgainPos, ?_⟩
    norm_num at hbound ⊢
    exact hbound

/-- A best-endpoint update loses exactly its actual payoff gain from the
mover's unrestricted behavioral debt. -/
theorem quittingTerminalSemanticDebt_stageBestEndpoint_eq_sub_gain
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (who : ι) (stage : ℕ) :
    let tail := quittingTerminalSemanticPair reward
      (quittingAllContinueProfileSpine reward profile (stage + 1))
    let root := quittingProfileLiveRoot reward profile stage
    let action := quittingRootBestEndpointAction reward tail.1 root who
    let targetProfile := Function.update profile who
      (quittingStagePureEndpointBehaviorDeviation
        reward profile who stage action)
    let source := quittingTerminalSemanticPair reward profile
    let target := quittingTerminalSemanticPair reward targetProfile
    let gain := quittingTerminalPayoff reward targetProfile who -
      quittingTerminalPayoff reward profile who
    quittingTerminalSemanticDebt target who =
      quittingTerminalSemanticDebt source who - gain := by
  dsimp only
  exact quittingTerminalSemanticDebt_update_self_eq_sub_payoffGain
    reward profile who _

/-- Near the global minimum, all but the source excess of the exact mover
debt loss is transferred to the other debt coordinates. -/
theorem quittingStageBestEndpoint_nearMinimum_opponentTransfer
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (minimum : QuittingTerminalSemanticPair ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (who : ι) (stage : ℕ) (epsilon : ℝ)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (hnear : quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward profile) ≤
      quittingTerminalSemanticDebtSum minimum + epsilon) :
    let tail := quittingTerminalSemanticPair reward
      (quittingAllContinueProfileSpine reward profile (stage + 1))
    let root := quittingProfileLiveRoot reward profile stage
    let action := quittingRootBestEndpointAction reward tail.1 root who
    let targetProfile := Function.update profile who
      (quittingStagePureEndpointBehaviorDeviation
        reward profile who stage action)
    let source := quittingTerminalSemanticPair reward profile
    let target := quittingTerminalSemanticPair reward targetProfile
    let gain := quittingTerminalPayoff reward targetProfile who -
      quittingTerminalPayoff reward profile who
    target ∈ quittingTerminalSemanticCarrier reward ∧
      quittingTerminalSemanticDebt target who =
        quittingTerminalSemanticDebt source who - gain ∧
      gain - epsilon ≤ ∑ other ∈ Finset.univ.erase who,
        quittingTerminalSemanticDebtChange source target other := by
  dsimp only
  let action := quittingRootBestEndpointAction reward
    (quittingTerminalSemanticPair reward
      (quittingAllContinueProfileSpine reward profile (stage + 1))).1
    (quittingProfileLiveRoot reward profile stage) who
  let targetProfile := Function.update profile who
    (quittingStagePureEndpointBehaviorDeviation
      reward profile who stage action)
  let source := quittingTerminalSemanticPair reward profile
  let target := quittingTerminalSemanticPair reward targetProfile
  let gain := quittingTerminalPayoff reward targetProfile who -
    quittingTerminalPayoff reward profile who
  have htarget : target ∈ quittingTerminalSemanticCarrier reward :=
    quittingTerminalSemanticPair_mem_carrier reward targetProfile
  have hmover : quittingTerminalSemanticDebt target who =
      quittingTerminalSemanticDebt source who - gain := by
    simpa only [action, targetProfile, source, target, gain] using
      (quittingTerminalSemanticDebt_stageBestEndpoint_eq_sub_gain
        reward profile who stage)
  have htransfer := minimumReference_opponentTransfer_of_coordinateDecrease
    reward minimum source target who gain hminimum htarget hmover
  refine ⟨htarget, hmover, ?_⟩
  linarith

/-- In a player set of cardinality at least two, the opposite face contains
one recipient at least as large as its average share of the aggregate
transfer.  Both the division-free and divided forms are exposed. -/
theorem exists_other_debtChange_ge_gain_sub_epsilon_average
    (source target : QuittingTerminalSemanticPair ι)
    (who : ι) (gain epsilon : ℝ)
    (hplayers : 1 < Fintype.card ι)
    (htransfer : gain - epsilon ≤
      ∑ other ∈ Finset.univ.erase who,
        quittingTerminalSemanticDebtChange source target other) :
    ∃ other ∈ Finset.univ.erase who,
      gain - epsilon ≤ (Fintype.card ι - 1 : ℝ) *
          quittingTerminalSemanticDebtChange source target other ∧
        (gain - epsilon) / (Fintype.card ι - 1 : ℝ) ≤
          quittingTerminalSemanticDebtChange source target other := by
  have hcardNat : (Finset.univ.erase who).card = Fintype.card ι - 1 := by
    simp
  have hfaceCardPos : 0 < (Finset.univ.erase who).card := by
    rw [hcardNat]
    omega
  have hnonempty : (Finset.univ.erase who).Nonempty :=
    Finset.card_pos.mp hfaceCardPos
  obtain ⟨other, hother, haverage⟩ :=
    exists_sum_le_card_mul_of_nonempty
      (Finset.univ.erase who) hnonempty
      (fun player => quittingTerminalSemanticDebtChange source target player)
  have hcombined : gain - epsilon ≤
      (Fintype.card ι - 1 : ℝ) *
        quittingTerminalSemanticDebtChange source target other := by
    calc
      gain - epsilon ≤ ∑ player ∈ Finset.univ.erase who,
          quittingTerminalSemanticDebtChange source target player := htransfer
      _ ≤ ((Finset.univ.erase who).card : ℝ) *
          quittingTerminalSemanticDebtChange source target other := haverage
      _ = (Fintype.card ι - 1 : ℝ) *
          quittingTerminalSemanticDebtChange source target other := by
        rw [hcardNat]
        rw [Nat.cast_sub (Nat.le_of_lt hplayers)]
        norm_num
  have hdenPos : 0 < (Fintype.card ι - 1 : ℝ) := by
    have hcardReal : (1 : ℝ) < Fintype.card ι := by exact_mod_cast hplayers
    exact sub_pos.mpr hcardReal
  refine ⟨other, hother, hcombined, ?_⟩
  rw [div_le_iff₀ hdenPos]
  simpa [mul_comm] using hcombined

/-- The three-player opposite face in `Fin 4` contains a recipient of at
least one sixth of the mover gain when the source excess is at most half the
gain. -/
theorem exists_finFour_other_debtChange_ge_gain_div_six
    (source target : QuittingTerminalSemanticPair (Fin 4))
    (who : Fin 4) (gain epsilon : ℝ)
    (htransfer : gain - epsilon ≤
      ∑ other ∈ Finset.univ.erase who,
        quittingTerminalSemanticDebtChange source target other)
    (hepsilon : epsilon ≤ gain / 2) :
    ∃ other ∈ Finset.univ.erase who,
      gain / 6 ≤ quittingTerminalSemanticDebtChange source target other := by
  have hnonempty : (Finset.univ.erase who).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    have hcard : (Finset.univ.erase who).card = 3 := by simp
    rw [hempty] at hcard
    simp at hcard
  obtain ⟨other, hother, haverage⟩ :=
    exists_sum_le_card_mul_of_nonempty
      (Finset.univ.erase who) hnonempty
      (fun player => quittingTerminalSemanticDebtChange source target player)
  have hcard : ((Finset.univ.erase who).card : ℝ) = 3 := by norm_num
  rw [hcard] at haverage
  refine ⟨other, hother, ?_⟩
  linarith

/-- Routing a nonsingleton stage atom through one pure endpoint preserves its
unconditional stage mass, and the routed coalition remains nonempty. -/
theorem quittingStageCoalitionMass_le_stagePureEndpointRouted
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (who : ι) (stage : ℕ) (terminal : {S : Finset ι // S.Nonempty})
    (action : Bool) (hcollision : 1 < terminal.val.card) :
    let routed := quittingPureEndpointRoutedCoalition terminal.val who action
    let targetProfile := Function.update profile who
      (quittingStagePureEndpointBehaviorDeviation
        reward profile who stage action)
    ∃ hrouted : routed.Nonempty,
      quittingStageCoalitionMass reward profile stage terminal ≤
        quittingStageCoalitionMass reward targetProfile stage
          ⟨routed, hrouted⟩ := by
  dsimp only
  have hrouted := quittingPureEndpointRoutedCoalition_nonempty_of_one_lt_card
    terminal.val who action hcollision
  refine ⟨hrouted, ?_⟩
  rw [quittingStageCoalitionMass_eq_liveMass_mul_rootCoalitionMass,
    quittingStageCoalitionMass_eq_liveMass_mul_rootCoalitionMass,
    quittingLiveMass_stagePureEndpoint_eq,
    quittingProfileLiveRoot_stagePureEndpoint_self]
  exact mul_le_mul_of_nonneg_left
    (quittingRootCoalitionMass_le_pureEndpointRouted
      (quittingProfileLiveRoot reward profile stage) terminal.val who action)
    (quittingLiveMass_nonneg reward profile stage)

/-- **General live-weighted collision transfer with a selected recipient.**

For an arbitrary finite player set, a nonsingleton row gives either the
live-weighted tail-excess arm or one co-realized endpoint update.  At a source
whose excess is at most half the guaranteed mover gain, the update selects a
distinct recipient at the explicit opposite-face average and routes the same
stage atom without loss. -/
theorem quittingLiveWeightedCollisionTransfer_tailEscape_or_routedTransfer
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (minimum : QuittingTerminalSemanticPair ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (stage : ℕ) (terminal : {S : Finset ι // S.Nonempty})
    (epsilon : ℝ)
    (hminimumCarrier : minimum ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (hminimumDebt : 0 < quittingTerminalSemanticDebtSum minimum)
    (hcollision : 1 < terminal.val.card)
    (hmass : 0 < quittingStageCoalitionMass reward profile stage terminal)
    (hnear : quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward profile) ≤
      quittingTerminalSemanticDebtSum minimum + epsilon)
    (hepsilon : epsilon ≤
      quittingStageCoalitionMass reward profile stage terminal *
        quittingTerminalSemanticDebtSum minimum /
          (4 * (Fintype.card ι : ℝ))) :
    let tail := quittingTerminalSemanticPair reward
      (quittingAllContinueProfileSpine reward profile (stage + 1))
    let root := quittingProfileLiveRoot reward profile stage
    let minimumDebt := quittingTerminalSemanticDebtSum minimum
    let stageMass := quittingStageCoalitionMass reward profile stage terminal
    let liveMass := quittingLiveMass reward profile stage
    let excess := quittingSpineDebtExcess reward profile minimumDebt (stage + 1)
    liveMass * excess ≥ stageMass * minimumDebt / 2 ∨
      ∃ who,
        let action := quittingRootBestEndpointAction reward tail.1 root who
        let targetProfile := Function.update profile who
          (quittingStagePureEndpointBehaviorDeviation
            reward profile who stage action)
        let source := quittingTerminalSemanticPair reward profile
        let target := quittingTerminalSemanticPair reward targetProfile
        let gain := quittingTerminalPayoff reward targetProfile who -
          quittingTerminalPayoff reward profile who
        let routed :=
          quittingPureEndpointRoutedCoalition terminal.val who action
        gain = liveMass *
            quittingRootCoordinateNashDefect reward tail.1 root who ∧
          0 < gain ∧
          stageMass * minimumDebt /
              (2 * (Fintype.card ι : ℝ)) ≤ gain ∧
          target ∈ quittingTerminalSemanticCarrier reward ∧
          quittingTerminalSemanticDebt target who =
            quittingTerminalSemanticDebt source who - gain ∧
          gain - epsilon ≤ ∑ other ∈ Finset.univ.erase who,
            quittingTerminalSemanticDebtChange source target other ∧
          (∃ other ∈ Finset.univ.erase who,
            stageMass * minimumDebt /
                (4 * (Fintype.card ι : ℝ) *
                  ((Fintype.card ι : ℝ) - 1)) ≤
              quittingTerminalSemanticDebtChange source target other) ∧
          ∃ hrouted : routed.Nonempty,
            stageMass ≤ quittingStageCoalitionMass reward targetProfile stage
              ⟨routed, hrouted⟩ := by
  dsimp only
  have hselected :=
    quittingLiveWeightedCollisionTransfer_tailEscape_or_exists_endpointGain
      reward minimum profile stage terminal hminimumCarrier hminimum
        hminimumDebt hcollision hmass
  rcases hselected with hescape | ⟨who, hgainFormula, hgainPos, hgainBound⟩
  · exact Or.inl hescape
  · right
    let action := quittingRootBestEndpointAction reward
      (quittingTerminalSemanticPair reward
        (quittingAllContinueProfileSpine reward profile (stage + 1))).1
      (quittingProfileLiveRoot reward profile stage) who
    let targetProfile := Function.update profile who
      (quittingStagePureEndpointBehaviorDeviation
        reward profile who stage action)
    let source := quittingTerminalSemanticPair reward profile
    let target := quittingTerminalSemanticPair reward targetProfile
    let gain := quittingTerminalPayoff reward targetProfile who -
      quittingTerminalPayoff reward profile who
    let routed := quittingPureEndpointRoutedCoalition terminal.val who action
    have hnearTransfer := quittingStageBestEndpoint_nearMinimum_opponentTransfer
      reward minimum profile who stage epsilon hminimum hnear
    have hnearTransfer' : target ∈ quittingTerminalSemanticCarrier reward ∧
        quittingTerminalSemanticDebt target who =
          quittingTerminalSemanticDebt source who - gain ∧
        gain - epsilon ≤ ∑ other ∈ Finset.univ.erase who,
          quittingTerminalSemanticDebtChange source target other := by
      simpa only [action, targetProfile, source, target, gain] using hnearTransfer
    rcases hnearTransfer' with ⟨htarget, hmover, htransfer⟩
    have hplayers : 1 < Fintype.card ι := by
      have hcardLe := Finset.card_le_univ terminal.val
      omega
    obtain ⟨other, hother, _hrecipientProduct, hrecipientAverage⟩ :=
      exists_other_debtChange_ge_gain_sub_epsilon_average
        source target who gain epsilon hplayers htransfer
    have hcardRealPos : 0 < (Fintype.card ι : ℝ) := by
      exact_mod_cast (Fintype.card_pos : 0 < Fintype.card ι)
    have hfaceRealPos : 0 < (Fintype.card ι : ℝ) - 1 := by
      have hplayersReal : (1 : ℝ) < Fintype.card ι := by
        exact_mod_cast hplayers
      exact sub_pos.mpr hplayersReal
    have hscaleDouble :
        quittingStageCoalitionMass reward profile stage terminal *
              quittingTerminalSemanticDebtSum minimum /
                (2 * (Fintype.card ι : ℝ)) =
          2 * (quittingStageCoalitionMass reward profile stage terminal *
              quittingTerminalSemanticDebtSum minimum /
                (4 * (Fintype.card ι : ℝ))) := by
      field_simp [ne_of_gt hcardRealPos]
      ring
    have hremaining :
        quittingStageCoalitionMass reward profile stage terminal *
              quittingTerminalSemanticDebtSum minimum /
                (4 * (Fintype.card ι : ℝ)) ≤
          gain - epsilon := by
      linarith
    have hrecipientScale :
        quittingStageCoalitionMass reward profile stage terminal *
              quittingTerminalSemanticDebtSum minimum /
                (4 * (Fintype.card ι : ℝ) *
                  ((Fintype.card ι : ℝ) - 1)) ≤
          quittingTerminalSemanticDebtChange source target other := by
      have hdivide :=
        (div_le_div_iff_of_pos_right hfaceRealPos).2 hremaining
      have hnormalize :
          (quittingStageCoalitionMass reward profile stage terminal *
                quittingTerminalSemanticDebtSum minimum /
                  (4 * (Fintype.card ι : ℝ))) /
              ((Fintype.card ι : ℝ) - 1) =
            quittingStageCoalitionMass reward profile stage terminal *
                quittingTerminalSemanticDebtSum minimum /
              (4 * (Fintype.card ι : ℝ) *
                ((Fintype.card ι : ℝ) - 1)) := by
        field_simp [ne_of_gt hcardRealPos, ne_of_gt hfaceRealPos]
      rw [hnormalize] at hdivide
      exact hdivide.trans hrecipientAverage
    have hrouting := quittingStageCoalitionMass_le_stagePureEndpointRouted
      reward profile who stage terminal action hcollision
    refine ⟨who, hgainFormula, hgainPos, hgainBound, htarget, hmover,
      htransfer, ⟨other, hother, hrecipientScale⟩, ?_⟩
    simpa only [action, targetProfile, routed] using hrouting

/-- **Four-player live-weighted collision transfer with no-loss routing.**

The tail-excess branch retains the live factor.  In the gain branch, the
same actual endpoint update realizes the `1 / 8` mover gain, the exact mover
debt loss, a `1 / 48` other-player debt increase at a sufficiently
near-minimum source, and a nonempty routed stage atom with no mass loss.
The shifted-tail excess in the first branch and the source excess `epsilon`
in the transfer branch are deliberately separate. -/
theorem quittingFinFourLiveWeightedCollisionTransfer_tailEscape_or_routedTransfer
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (minimum : QuittingTerminalSemanticPair (Fin 4))
    (profile : (quittingGame reward).BehaviorProfile)
    (stage : ℕ) (terminal : {S : Finset (Fin 4) // S.Nonempty})
    (epsilon : ℝ)
    (hminimumCarrier : minimum ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (hminimumDebt : 0 < quittingTerminalSemanticDebtSum minimum)
    (hcollision : 1 < terminal.val.card)
    (hmass : 0 < quittingStageCoalitionMass reward profile stage terminal)
    (hnear : quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward profile) ≤
      quittingTerminalSemanticDebtSum minimum + epsilon)
    (hepsilon : epsilon ≤
      quittingStageCoalitionMass reward profile stage terminal *
        quittingTerminalSemanticDebtSum minimum / 16) :
    let tail := quittingTerminalSemanticPair reward
      (quittingAllContinueProfileSpine reward profile (stage + 1))
    let root := quittingProfileLiveRoot reward profile stage
    let minimumDebt := quittingTerminalSemanticDebtSum minimum
    let stageMass := quittingStageCoalitionMass reward profile stage terminal
    let liveMass := quittingLiveMass reward profile stage
    let excess := quittingSpineDebtExcess reward profile minimumDebt (stage + 1)
    liveMass * excess ≥ stageMass * minimumDebt / 2 ∨
      ∃ who,
        let action := quittingRootBestEndpointAction reward tail.1 root who
        let targetProfile := Function.update profile who
          (quittingStagePureEndpointBehaviorDeviation
            reward profile who stage action)
        let source := quittingTerminalSemanticPair reward profile
        let target := quittingTerminalSemanticPair reward targetProfile
        let gain := quittingTerminalPayoff reward targetProfile who -
          quittingTerminalPayoff reward profile who
        let routed :=
          quittingPureEndpointRoutedCoalition terminal.val who action
        gain = liveMass *
            quittingRootCoordinateNashDefect reward tail.1 root who ∧
          0 < gain ∧
          stageMass * minimumDebt / 8 ≤ gain ∧
          target ∈ quittingTerminalSemanticCarrier reward ∧
          quittingTerminalSemanticDebt target who =
            quittingTerminalSemanticDebt source who - gain ∧
          gain - epsilon ≤ ∑ other ∈ Finset.univ.erase who,
            quittingTerminalSemanticDebtChange source target other ∧
          (∃ other ∈ Finset.univ.erase who,
            stageMass * minimumDebt / 48 ≤
              quittingTerminalSemanticDebtChange source target other) ∧
          ∃ hrouted : routed.Nonempty,
            stageMass ≤ quittingStageCoalitionMass reward targetProfile stage
              ⟨routed, hrouted⟩ := by
  dsimp only
  have hselected :=
    quittingFinFourLiveWeightedCollisionTransfer_tailEscape_or_endpointGain
      reward minimum profile stage terminal hminimumCarrier hminimum
        hminimumDebt hcollision hmass
  rcases hselected with hescape | ⟨who, hgainFormula, hgainPos, hgainBound⟩
  · exact Or.inl hescape
  · right
    let action := quittingRootBestEndpointAction reward
      (quittingTerminalSemanticPair reward
        (quittingAllContinueProfileSpine reward profile (stage + 1))).1
      (quittingProfileLiveRoot reward profile stage) who
    let targetProfile := Function.update profile who
      (quittingStagePureEndpointBehaviorDeviation
        reward profile who stage action)
    let source := quittingTerminalSemanticPair reward profile
    let target := quittingTerminalSemanticPair reward targetProfile
    let gain := quittingTerminalPayoff reward targetProfile who -
      quittingTerminalPayoff reward profile who
    let routed := quittingPureEndpointRoutedCoalition terminal.val who action
    have hnearTransfer := quittingStageBestEndpoint_nearMinimum_opponentTransfer
      reward minimum profile who stage epsilon hminimum hnear
    have hnearTransfer' : target ∈ quittingTerminalSemanticCarrier reward ∧
        quittingTerminalSemanticDebt target who =
          quittingTerminalSemanticDebt source who - gain ∧
        gain - epsilon ≤ ∑ other ∈ Finset.univ.erase who,
          quittingTerminalSemanticDebtChange source target other := by
      simpa only [action, targetProfile, source, target, gain] using hnearTransfer
    rcases hnearTransfer' with ⟨htarget, hmover, htransfer⟩
    have hepsilonHalf : epsilon ≤ gain / 2 := by
      dsimp only [gain] at hgainBound ⊢
      linarith
    obtain ⟨other, hother, hrecipient⟩ :=
      exists_finFour_other_debtChange_ge_gain_div_six
        source target who gain epsilon htransfer hepsilonHalf
    have hrecipientScale :
        quittingStageCoalitionMass reward profile stage terminal *
            quittingTerminalSemanticDebtSum minimum / 48 ≤
          quittingTerminalSemanticDebtChange source target other := by
      linarith
    have hrouting := quittingStageCoalitionMass_le_stagePureEndpointRouted
      reward profile who stage terminal action hcollision
    refine ⟨who, hgainFormula, hgainPos, hgainBound, htarget, hmover,
      htransfer, ⟨other, hother, hrecipientScale⟩, ?_⟩
    simpa only [action, targetProfile, routed] using hrouting

end GameTheory
