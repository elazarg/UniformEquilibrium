/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Research.Quitting.FinFourSameStageEndpointMonodromy
import Research.Quitting.NonsingletonMinimumLawLinearTransfer
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticFinFourMinimumLawFiniteAtom
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticLiteralSourceReturnNoGo

/-!
# Exhaustive source-preserving producer atlas on four players

This module packages the checked finite reduction from a four-player hard
residual into four natural producer modes.  Every constructor retains the
minimum joint-law source, the causal suffix atom, and every literal operation
used to reach its terminal producer.

The nonsingleton reduction is deliberately performed on the selected source
rows themselves.  A fixed tail threshold gives an exhaustive alternative:
frequent high tails produce the existing tail-escape subsequence, while
otherwise one actual low-tail row feeds the checked finite same-stage
purification.  On `Fin 4`, the latter ends in a singleton producer or a simple
cycle of length at most eight with common-host or complementary-pair geometry.

The cycle leaves also expose the checked literal-source no-go at every edge:
a positive edge cannot be inserted unchanged into an exact Nash--Bellman
chronology while preserving its root and shifted tail.  Hence the remaining
cycle completion contract is genuinely nonlocal.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability Math.PMFProduct
open MathUE.FiniteBooleanEndpointOrbit
open QuittingNonsingletonMinimumLawTransfer

/-- The common source retained by every atlas leaf. -/
structure FinFourMinimumAtomProducer
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (bound : ℝ) where
  residual : FinFourQuantitativeFullSupportHardResidual reward bound
  point : QuittingTerminalSemanticLawPoint (Fin 4)
  point_mem : point ∈ quittingTerminalSemanticLawCarrier reward
  semantic_mem : point.1 ∈ quittingTerminalSemanticCarrier reward
  minimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
    quittingTerminalSemanticDebtSum point.1 ≤
      quittingTerminalSemanticDebtSum candidate
  inf_pos : 0 < quittingTerminalDebtSumInf reward
  debt_eq_inf : quittingTerminalSemanticDebtSum point.1 =
    quittingTerminalDebtSumInf reward
  atom : QuittingMinimumLawCausalSuffixAtom reward point

namespace FinFourMinimumAtomProducer

/-- The displayed minimum point has strictly positive total debt. -/
theorem minimumDebt_pos
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound : ℝ} (source : FinFourMinimumAtomProducer reward bound) :
    0 < quittingTerminalSemanticDebtSum source.point.1 := by
  rw [source.debt_eq_inf]
  exact source.inf_pos

/-- A supplied hard residual produces the common minimum-law source without
reselecting the table or losing its residual packet. -/
theorem nonempty_of_hardResidual
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (bound : ℝ)
    (residual : FinFourQuantitativeFullSupportHardResidual reward bound) :
    Nonempty (FinFourMinimumAtomProducer reward bound) := by
  obtain ⟨point, hpoint, hsemantic, hminimum, hinf, hdebt, ⟨atom⟩⟩ :=
    exists_finFourHardResidual_minimumLaw_causalSuffixAtom
      reward bound residual
  exact ⟨{
    residual := residual
    point := point
    point_mem := hpoint
    semantic_mem := hsemantic
    minimum := hminimum
    inf_pos := hinf
    debt_eq_inf := hdebt
    atom := atom
  }⟩

end FinFourMinimumAtomProducer

/-- One literal selected row in the low-tail arm.  Its source profile, cap
roots, atom, and marked date remain inside `rows`. -/
structure FinFourLowTailRow
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound : ℝ} (source : FinFourMinimumAtomProducer reward bound) where
  rows : SelectedRows reward source.point source.atom
  rank : ℕ
  stage_mass_floor :
    source.point.2 (some source.atom.terminal) ^ 2 / 8 <
      selectedStageMass rows rank
  tail_excess_lt :
    selectedTailExcess rows rank <
      source.point.2 (some source.atom.terminal) ^ 2 *
        quittingTerminalSemanticDebtSum source.point.1 / 16

namespace FinFourLowTailRow

variable
  {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
  {bound : ℝ} {source : FinFourMinimumAtomProducer reward bound}

/-- The literal prefixed profile carrying the selected row. -/
def profile (row : FinFourLowTailRow source) :
    (quittingGame reward).BehaviorProfile :=
  prefixedProfile reward row.rows.profiles row.rows.roots row.rank

/-- The selected actual date in the prefixed profile. -/
def stage (row : FinFourLowTailRow source) : ℕ :=
  shiftedStage row.rows.roots row.rows.mark row.rank

/-- The uniform mass floor used by the finite same-stage producer. -/
def lambda (row : FinFourLowTailRow source) : ℝ :=
  source.point.2 (some source.atom.terminal) ^ 2 / 8

/-- The original marked atom viewed as a nonsingleton coalition. -/
def coalition (row : FinFourLowTailRow source) :
    QuittingNonsingletonCoalition (Fin 4) :=
  ⟨source.atom.terminal.val, row.rows.collision⟩

/-- The selected mass floor is positive. -/
theorem lambda_pos (row : FinFourLowTailRow source) : 0 < row.lambda := by
  dsimp only [lambda]
  positivity

/-- The selected source row carries the declared mass floor. -/
theorem lambda_le_stageMass (row : FinFourLowTailRow source) :
    row.lambda ≤ quittingStageCoalitionMass reward row.profile row.stage
      source.atom.terminal :=
  row.stage_mass_floor.le

/-- The atlas threshold is exactly the low-tail hypothesis consumed by the
same-stage purification theorem. -/
theorem lowTail (row : FinFourLowTailRow source) :
    quittingSpineDebtExcess reward row.profile
        (quittingTerminalSemanticDebtSum source.point.1) (row.stage + 1) <
      row.lambda * quittingTerminalSemanticDebtSum source.point.1 / 2 := by
  have h := row.tail_excess_lt
  change quittingSpineDebtExcess reward row.profile
      (quittingTerminalSemanticDebtSum source.point.1) (row.stage + 1) <
    source.point.2 (some source.atom.terminal) ^ 2 *
      quittingTerminalSemanticDebtSum source.point.1 / 16 at h
  calc
    quittingSpineDebtExcess reward row.profile
          (quittingTerminalSemanticDebtSum source.point.1) (row.stage + 1) <
        source.point.2 (some source.atom.terminal) ^ 2 *
          quittingTerminalSemanticDebtSum source.point.1 / 16 := h
    _ = row.lambda * quittingTerminalSemanticDebtSum source.point.1 / 2 := by
      dsimp only [lambda]
      ring

/-- The exact initial state used by the checked partial-purification path. -/
def initialState (row : FinFourLowTailRow source) :
    QuittingPartialPurificationState reward row.profile row.stage row.lambda :=
  quittingPartialPurificationInitialState reward row.profile row.stage row.lambda
    row.coalition row.lambda_le_stageMass

end FinFourLowTailRow

/-- A singleton reached during the bounded preliminary purification. -/
structure FinFourPurifiedSingletonProducer
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound : ℝ} (source : FinFourMinimumAtomProducer reward bound) where
  low : FinFourLowTailRow source
  state : QuittingPartialPurificationState reward low.profile low.stage low.lambda
  steps : ℕ
  singleton :
    QuittingPartialPurificationSingleton reward low.profile low.stage low.lambda state
  path : QuittingPartialPurificationPath reward low.profile low.stage low.lambda
    low.initialState state steps
  steps_le : steps ≤ Fintype.card (Fin 4)

/-- A completed bounded purification, before the finite endpoint orbit is
classified as terminal or cyclic. -/
structure FinFourTotalPurificationProducer
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound : ℝ} (source : FinFourMinimumAtomProducer reward bound) where
  low : FinFourLowTailRow source
  finalState :
    QuittingPartialPurificationState reward low.profile low.stage low.lambda
  steps : ℕ
  path : QuittingPartialPurificationPath reward low.profile low.stage low.lambda
    low.initialState finalState steps
  steps_le : steps ≤ Fintype.card (Fin 4)
  complete : ∀ who, finalState.assignment who ≠ none

namespace FinFourTotalPurificationProducer

variable
  {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
  {bound : ℝ} {source : FinFourMinimumAtomProducer reward bound}

/-- The exact source profile of the finite endpoint orbit. -/
def profile (producer : FinFourTotalPurificationProducer source) :
    (quittingGame reward).BehaviorProfile :=
  quittingPartialPurificationStateProfile reward producer.low.profile
    producer.low.stage producer.low.lambda producer.finalState

end FinFourTotalPurificationProducer

/-- A singleton reached at a terminal vertex of the finite endpoint orbit. -/
structure FinFourTerminalSingletonProducer
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound : ℝ} (source : FinFourMinimumAtomProducer reward bound) where
  purification : FinFourTotalPurificationProducer source
  orbit : DispatchedOrbit
    (QuittingSameStageSingletonRoute reward purification.profile
      purification.low.stage)
    (fun start target => Nonempty
      (QuittingSameStageEndpointEdge reward purification.profile
        purification.low.stage source.point.1 purification.low.lambda start target))
    purification.finalState.coalition

/-- The complete literal source of a simple same-stage endpoint cycle. -/
structure FinFourMonodromyProducer
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound : ℝ} (source : FinFourMinimumAtomProducer reward bound) where
  purification : FinFourTotalPurificationProducer source
  trace : DispatchedClosedSegment
    (QuittingSameStageSingletonRoute reward purification.profile
      purification.low.stage)
    (fun start target => Nonempty
      (QuittingSameStageEndpointEdge reward purification.profile
        purification.low.stage source.point.1 purification.low.lambda start target))
    purification.finalState.coalition
  period_le_eight : trace.segment.segment.period ≤ 8
  stage_mass_floor : ∀ offset : Fin trace.segment.segment.period,
    purification.low.lambda ≤ quittingStageCoalitionMass reward
      (quittingLiteralPureRootCoalitionProfile reward purification.profile
        purification.low.stage
        (trace.orbit (trace.segment.segment.start + offset)))
      purification.low.stage
      (quittingTerminalOfNonsingletonCoalition
        (trace.orbit (trace.segment.segment.start + offset)))
  edge_certificate : ∀ offset : Fin trace.segment.segment.period,
    ∃ edge : QuittingSameStageEndpointEdge reward purification.profile
        purification.low.stage source.point.1 purification.low.lambda
        (trace.orbit (trace.segment.segment.start + offset))
        (trace.orbit (trace.segment.segment.start + offset + 1)),
      edge.action = quittingRootBestEndpointAction reward
          (quittingTerminalSemanticPair reward
            (quittingAllContinueProfileSpine reward
              (quittingLiteralPureRootCoalitionProfile reward purification.profile
                purification.low.stage
                (trace.orbit (trace.segment.segment.start + offset)))
              (purification.low.stage + 1))).1
          (quittingProfileLiveRoot reward
            (quittingLiteralPureRootCoalitionProfile reward purification.profile
              purification.low.stage
              (trace.orbit (trace.segment.segment.start + offset)))
            purification.low.stage)
          edge.who ∧
        0 < quittingSameStageCoalitionGain reward purification.profile
          purification.low.stage
          (trace.orbit (trace.segment.segment.start + offset))
          edge.who edge.action ∧
        purification.low.lambda *
              quittingTerminalSemanticDebtSum source.point.1 / 8 ≤
          quittingSameStageCoalitionGain reward purification.profile
            purification.low.stage
            (trace.orbit (trace.segment.segment.start + offset))
            edge.who edge.action

/-- Common-host geometry for a literal simple endpoint cycle. -/
structure FinFourCommonHostMonodromyProducer
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound : ℝ} (source : FinFourMinimumAtomProducer reward bound) where
  monodromy : FinFourMonodromyProducer source
  host : Fin 4
  host_mem : ∀ offset : Fin monodromy.trace.segment.segment.period,
    host ∈ (monodromy.trace.orbit
      (monodromy.trace.segment.segment.start + offset)).1

/-- Complementary-pair geometry for a literal simple endpoint cycle. -/
structure FinFourComplementaryPairMonodromyProducer
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound : ℝ} (source : FinFourMinimumAtomProducer reward bound) where
  monodromy : FinFourMonodromyProducer source
  first second : Fin monodromy.trace.segment.segment.period
  first_card :
    (monodromy.trace.orbit
      (monodromy.trace.segment.segment.start + first)).1.card = 2
  second_card :
    (monodromy.trace.orbit
      (monodromy.trace.segment.segment.start + second)).1.card = 2
  disjoint : Disjoint
    (monodromy.trace.orbit
      (monodromy.trace.segment.segment.start + first)).1
    (monodromy.trace.orbit
      (monodromy.trace.segment.segment.start + second)).1
  complementary :
    (monodromy.trace.orbit
      (monodromy.trace.segment.segment.start + second)).1 =
      (monodromy.trace.orbit
        (monodromy.trace.segment.segment.start + first)).1ᶜ

/-- The finite natural producer modes.  The three ways of reaching a singleton
share one completion mode but remain separate constructors so their literal
sources are not identified. -/
inductive FinFourProducerResidual
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (bound : ℝ) : Type
  | minimumSingleton
      (source : FinFourMinimumAtomProducer reward bound)
      (terminal_card : source.atom.terminal.val.card = 1)
  | purifiedSingleton
      (source : FinFourMinimumAtomProducer reward bound)
      (producer : FinFourPurifiedSingletonProducer source)
  | terminalSingleton
      (source : FinFourMinimumAtomProducer reward bound)
      (producer : FinFourTerminalSingletonProducer source)
  | tailEscape
      (source : FinFourMinimumAtomProducer reward bound)
      (producer : TailEscapeSubsequence reward source.point source.atom)
  | commonHostMonodromy
      (source : FinFourMinimumAtomProducer reward bound)
      (producer : FinFourCommonHostMonodromyProducer source)
  | complementaryPairMonodromy
      (source : FinFourMinimumAtomProducer reward bound)
      (producer : FinFourComplementaryPairMonodromyProducer source)

/-- Four completion contracts, with all singleton origins merged only at the
obligation level. -/
inductive FinFourProducerCompletionContract
  | singletonTerminalApproximationOrRegeneration
  | escapedTailChargeOrRegeneration
  | commonHostNonlocalReturnOrRegeneration
  | complementaryPairNonlocalReturnOrRegeneration
  deriving DecidableEq

/-- Every atlas leaf has exactly one conjecture-facing completion contract. -/
def FinFourProducerResidual.completionContract
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound : ℝ} : FinFourProducerResidual reward bound →
      FinFourProducerCompletionContract
  | .minimumSingleton .. => .singletonTerminalApproximationOrRegeneration
  | .purifiedSingleton .. => .singletonTerminalApproximationOrRegeneration
  | .terminalSingleton .. => .singletonTerminalApproximationOrRegeneration
  | .tailEscape .. => .escapedTailChargeOrRegeneration
  | .commonHostMonodromy .. => .commonHostNonlocalReturnOrRegeneration
  | .complementaryPairMonodromy .. =>
      .complementaryPairNonlocalReturnOrRegeneration

/-- A checked same-stage positive edge gives the literal packet consumed by
the root--tail exactification no-go. -/
def QuittingSameStageEndpointEdge.literalPositiveActualRowPacket
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {profile : (quittingGame reward).BehaviorProfile}
    {stage : ℕ} {minimum : QuittingTerminalSemanticPair (Fin 4)}
    {lambda : ℝ} {start target : QuittingNonsingletonCoalition (Fin 4)}
    (edge : QuittingSameStageEndpointEdge reward profile stage minimum lambda
      start target)
    (mass_pos : 0 < quittingStageCoalitionMass reward
      (quittingLiteralPureRootCoalitionProfile reward profile stage start) stage
      (quittingTerminalOfNonsingletonCoalition start)) :
    QuittingLiteralPositiveActualRowPacket reward := by
  let sourceProfile :=
    quittingLiteralPureRootCoalitionProfile reward profile stage start
  refine {
    profile := sourceProfile
    stage := stage
    who := edge.who
    terminal := quittingTerminalOfNonsingletonCoalition start
    mass := quittingStageCoalitionMass reward sourceProfile stage
      (quittingTerminalOfNonsingletonCoalition start)
    mass_eq := rfl
    mass_pos := mass_pos
    gain_pos := ?_
  }
  dsimp only [quittingLiteralActualRowBestEndpointGain,
    quittingLiteralActualRowTail, quittingLiteralActualRowRoot]
  rw [← edge.action_eq_best]
  rw [← quittingTerminalPayoff_literalOneDateProfile_eq_canonical
    reward sourceProfile edge.who stage edge.action]
  simpa only [quittingSameStageCoalitionGain, sourceProfile] using edge.gain_pos

/-- Every edge of a monodromy leaf excludes the complete local
root-and-tail-preserving exact Nash--Bellman arm. -/
theorem FinFourMonodromyProducer.every_edge_no_literalExactification
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound : ℝ} {source : FinFourMinimumAtomProducer reward bound}
    (producer : FinFourMonodromyProducer source)
    (offset : Fin producer.trace.segment.segment.period) :
    ∃ edge : QuittingSameStageEndpointEdge reward producer.purification.profile
        producer.purification.low.stage source.point.1
        producer.purification.low.lambda
        (producer.trace.orbit (producer.trace.segment.segment.start + offset))
        (producer.trace.orbit
          (producer.trace.segment.segment.start + offset + 1)),
      let packet := edge.literalPositiveActualRowPacket
        ((producer.purification.low.lambda_pos).trans_le
          (producer.stage_mass_floor offset))
      ¬ ∃ current tail : QuittingNashBellmanPoint (Fin 4),
        packet.IsLiteralNashBellmanEmbedding current tail := by
  obtain ⟨edge, _haction, _hgain, _hfloor⟩ := producer.edge_certificate offset
  refine ⟨edge, ?_⟩
  exact (edge.literalPositiveActualRowPacket
    ((producer.purification.low.lambda_pos).trans_le
      (producer.stage_mass_floor offset))).not_exists_literalNashBellmanEmbedding

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
      reward hreward with hpayoff | ⟨residual⟩
  · exact Or.inl hpayoff
  · exact Or.inr
      (nonempty_finFourProducerResidual_of_hardResidual reward bound residual)

end GameTheory
