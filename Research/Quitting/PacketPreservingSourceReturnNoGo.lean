/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Research.Quitting.ActualRowDebtLocalizationAdapters
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticLiteralSourceReturnNoGo

/-!
# Positive-collision instance of the literal source-return no-go

The production theorem identifies the root--tail complementarity obstruction.
This thin adapter packages the actual positive-collision rows selected by the
stopping-law localization theorem.  It does not close the leaf: a charged
root or continuation-payoff change is still permitted.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The localized positive-collision rows form positive actual-row packets,
so none admits an exact Nash--Bellman embedding on its literal root--tail
fiber. -/
theorem positiveCollisionMarkedTailDispatch_no_packetPreservingExactSourceReturn
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {regime : QuittingCounterexampleRegime reward}
    {frontier : QuittingCounterexampleStoppingLawFrontier regime}
    (frontierPacket : QuittingStoppingLawVanishingDebtRectangleSequence
      frontier)
    {lower : ℝ} (hlower : 0 < lower)
    (dispatch : HasQuittingStoppingLawPositiveCollisionMarkedTailDispatch
      frontierPacket lower) :
    ∃ (stop : ℕ → ℕ) (subseq : ℕ → ℕ) (other : ι),
      StrictMono subseq ∧
      other ≠ frontierPacket.observer ∧
      ∀ rank,
        frontierPacket.quitTime (subseq rank) =
            some (stop (subseq rank)) ∧
          let actual := Function.update
            (quittingStoppingLawRectangleTargetProfile frontierPacket
              (subseq rank))
            frontierPacket.observer
            (quittingPureTimeBehaviorStrategy reward frontierPacket.observer
              (frontierPacket.quitTime (subseq rank)))
          ∃ row : QuittingLiteralPositiveActualRowPacket reward,
            row.profile = actual ∧
              row.stage = stop (subseq rank) ∧
              row.who = other ∧
              row.terminal = frontierPacket.terminal ∧
              lower ≤ row.mass ∧
              ¬ ∃ current tail : QuittingNashBellmanPoint ι,
                row.IsLiteralNashBellmanEmbedding current tail := by
  obtain ⟨stop, subseq, other, hsubseq, hother, _hdebt, hrows⟩ :=
    positiveCollisionMarkedTailDispatch_fixedOtherLegalDeviation
      frontierPacket hlower dispatch
  refine ⟨stop, subseq, other, hsubseq, hother, ?_⟩
  intro rank
  obtain ⟨htime, hmass, _hgainIdentity, hgainLower⟩ := hrows rank
  refine ⟨htime, ?_⟩
  dsimp only
  let actual := Function.update
    (quittingStoppingLawRectangleTargetProfile frontierPacket (subseq rank))
    frontierPacket.observer
    (quittingPureTimeBehaviorStrategy reward frontierPacket.observer
      (frontierPacket.quitTime (subseq rank)))
  let stage := stop (subseq rank)
  let players := Finset.univ.erase frontierPacket.observer
  have hotherMem : other ∈ players := by
    exact Finset.mem_erase.mpr ⟨hother, Finset.mem_univ other⟩
  have hcardNat : 0 < players.card :=
    Finset.card_pos.mpr ⟨other, hotherMem⟩
  have hcard : 0 < (players.card : ℝ) := by
    exact_mod_cast hcardNat
  have hfloor : 0 <
      lower * quittingTerminalSemanticDebtSum frontier.base / 2 := by
    exact div_pos (mul_pos hlower frontier.base_positive) (by norm_num)
  have hgainLower' :
      lower * quittingTerminalSemanticDebtSum frontier.base / 2 ≤
        (players.card : ℝ) *
          quittingLiteralActualRowBestEndpointGain reward actual other stage := by
    simpa only [actual, stage, players,
      quittingLiteralActualRowBestEndpointGain,
      quittingLiteralActualRowTail, quittingLiteralActualRowRoot] using
        hgainLower
  have hgainPos : 0 <
      quittingLiteralActualRowBestEndpointGain reward actual other stage := by
    nlinarith
  let row : QuittingLiteralPositiveActualRowPacket reward :=
    { profile := actual
      stage := stage
      who := other
      terminal := frontierPacket.terminal
      mass := quittingStageCoalitionMass reward actual stage
        frontierPacket.terminal
      mass_eq := rfl
      mass_pos := hlower.trans_le (by
        simpa only [actual, stage] using hmass)
      gain_pos := hgainPos }
  refine ⟨row, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · simpa only [row, actual, stage] using hmass
  · exact row.not_exists_literalNashBellmanEmbedding

/-- **Uniform same-fiber repair floor for the positive-collision arm.**
Along the fixed-player subsequence selected by actual-row localization, every
approximate Nash repair which reuses the literal root and continuation has
error bounded away from zero by a table-level constant.  The division-free
form is included because it does not require a separate cardinality
denominator in downstream arithmetic. -/
theorem positiveCollisionMarkedTailDispatch_sameFiberRepairErrorFloor
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {regime : QuittingCounterexampleRegime reward}
    {frontier : QuittingCounterexampleStoppingLawFrontier regime}
    (frontierPacket : QuittingStoppingLawVanishingDebtRectangleSequence
      frontier)
    {lower : ℝ} (hlower : 0 < lower)
    (dispatch : HasQuittingStoppingLawPositiveCollisionMarkedTailDispatch
      frontierPacket lower) :
    ∃ (stop : ℕ → ℕ) (subseq : ℕ → ℕ) (other : ι),
      StrictMono subseq ∧
      other ≠ frontierPacket.observer ∧
      ∀ rank (error : ℝ), 0 ≤ error →
        let actual := Function.update
          (quittingStoppingLawRectangleTargetProfile frontierPacket
            (subseq rank))
          frontierPacket.observer
          (quittingPureTimeBehaviorStrategy reward frontierPacket.observer
            (frontierPacket.quitTime (subseq rank)))
        let tail := quittingLiteralActualRowTail reward actual
          (stop (subseq rank))
        let root := quittingLiteralActualRowRoot reward actual
          (stop (subseq rank))
        IsεQuittingRootNash reward tail.1 error root →
          lower * quittingTerminalSemanticDebtSum frontier.base / 2 ≤
              ((Finset.univ.erase frontierPacket.observer).card : ℝ) * error ∧
            lower * quittingTerminalSemanticDebtSum frontier.base /
                (2 * ((Finset.univ.erase frontierPacket.observer).card : ℝ)) ≤
              error := by
  obtain ⟨stop, subseq, other, hsubseq, hother, _hdebt, hrows⟩ :=
    positiveCollisionMarkedTailDispatch_fixedOtherLegalDeviation
      frontierPacket hlower dispatch
  refine ⟨stop, subseq, other, hsubseq, hother, ?_⟩
  intro rank error herror
  dsimp only
  obtain ⟨_htime, hmass, hgainIdentity, hgainFloor⟩ := hrows rank
  let actual := Function.update
    (quittingStoppingLawRectangleTargetProfile frontierPacket (subseq rank))
    frontierPacket.observer
    (quittingPureTimeBehaviorStrategy reward frontierPacket.observer
      (frontierPacket.quitTime (subseq rank)))
  let stage := stop (subseq rank)
  let gain := quittingLiteralActualRowBestEndpointGain reward actual other stage
  let players := Finset.univ.erase frontierPacket.observer
  have hotherMem : other ∈ players :=
    Finset.mem_erase.mpr ⟨hother, Finset.mem_univ other⟩
  have hcardNat : 0 < players.card :=
    Finset.card_pos.mpr ⟨other, hotherMem⟩
  have hcard : 0 < (players.card : ℝ) := by exact_mod_cast hcardNat
  have hgainFloor' :
      lower * quittingTerminalSemanticDebtSum frontier.base / 2 ≤
        (players.card : ℝ) * gain := by
    simpa only [actual, stage, players, gain,
      quittingLiteralActualRowBestEndpointGain,
      quittingLiteralActualRowTail, quittingLiteralActualRowRoot] using
        hgainFloor
  have hgainPos : 0 < gain := by
    have hfloorPos : 0 <
        lower * quittingTerminalSemanticDebtSum frontier.base / 2 :=
      div_pos (mul_pos hlower frontier.base_positive) (by norm_num)
    nlinarith
  let row : QuittingLiteralPositiveActualRowPacket reward :=
    { profile := actual
      stage := stage
      who := other
      terminal := frontierPacket.terminal
      mass := quittingStageCoalitionMass reward actual stage
        frontierPacket.terminal
      mass_eq := rfl
      mass_pos := hlower.trans_le (by simpa only [actual, stage] using hmass)
      gain_pos := by simpa only [gain] using hgainPos }
  intro hnash
  have hgainLe : gain ≤ error := by
    simpa only [row, gain] using
      row.gain_le_nashError_of_literal_root_tail hnash
  have hdivisionFree :
      lower * quittingTerminalSemanticDebtSum frontier.base / 2 ≤
        (players.card : ℝ) * error :=
    hgainFloor'.trans (mul_le_mul_of_nonneg_left hgainLe hcard.le)
  refine ⟨by simpa only [players] using hdivisionFree, ?_⟩
  have hdenom : 0 < 2 * (players.card : ℝ) := mul_pos (by norm_num) hcard
  apply (div_le_iff₀ hdenom).2
  have halgebra :
      lower * quittingTerminalSemanticDebtSum frontier.base / 2 ≤
          (players.card : ℝ) * error ↔
        lower * quittingTerminalSemanticDebtSum frontier.base ≤
          (2 * (players.card : ℝ)) * error := by
    constructor <;> intro h <;> nlinarith
  simpa [mul_comm, mul_left_comm, mul_assoc] using
    (halgebra.mp hdivisionFree)

end GameTheory
