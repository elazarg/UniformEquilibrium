/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegime.StoppingLaw.ReachedRowDebtLocalization
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticLiteralSourceReturnNoGo

/-!
# Positive-collision instance of the literal source-return no-go

The production reached-row certificate selects actual positive-collision rows
with a uniform legal gain.  This consumer turns those rows into literal
root--tail complementarity obstructions.  It does not close the leaf: a
charged root or continuation-payoff change is still permitted.
-/

noncomputable section

namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The localized positive-collision rows form positive actual-row packets,
so none admits an exact Nash--Bellman embedding on its literal root--tail
fiber. -/
theorem positiveTargetReachedRowLocalization_no_packetPreservingExactSourceReturn
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {regime : QuittingCounterexampleRegime reward}
    {frontier : QuittingCounterexampleStoppingLawFrontier regime}
    (frontierPacket : QuittingStoppingLawVanishingDebtRectangleSequence
      frontier)
    {lower : ℝ}
    (certificate : HasQuittingStoppingLawPositiveTargetReachedRowLocalization
      frontierPacket lower) :
    ∃ (stop : ℕ → ℕ) (subseq : ℕ → ℕ) (other : ι),
      StrictMono subseq ∧
      other ≠ frontierPacket.observer ∧
      ∀ rank,
        frontierPacket.quitTime (subseq rank) =
            some (stop (subseq rank)) ∧
          let actual := quittingStoppingLawPositiveTargetReachedRowProfile
            frontierPacket (subseq rank)
          ∃ row : QuittingLiteralPositiveActualRowPacket reward,
            row.profile = actual ∧
              row.stage = stop (subseq rank) ∧
              row.who = other ∧
              row.terminal = frontierPacket.terminal ∧
              lower ≤ row.mass ∧
              ¬ ∃ current tail : QuittingNashBellmanPoint ι,
                row.IsLiteralNashBellmanEmbedding current tail := by
  obtain ⟨hlower, stop, subseq, other, hsubseq, hother, htime, hmass,
      hgain⟩ := certificate
  refine ⟨stop, subseq, other, hsubseq, hother, ?_⟩
  intro rank
  refine ⟨htime rank, ?_⟩
  dsimp only
  let actual := quittingStoppingLawPositiveTargetReachedRowProfile
    frontierPacket (subseq rank)
  let stage := stop (subseq rank)
  let players := Finset.univ.erase frontierPacket.observer
  have hotherMem : other ∈ players := by
    exact Finset.mem_erase.mpr ⟨hother, Finset.mem_univ other⟩
  have hcardNat : 0 < players.card :=
    Finset.card_pos.mpr ⟨other, hotherMem⟩
  have hcard : 0 < (players.card : ℝ) := by
    exact_mod_cast hcardNat
  have hfloor : 0 <
      quittingStoppingLawPositiveTargetReachedRowGainFloor
        frontierPacket lower := by
    unfold quittingStoppingLawPositiveTargetReachedRowGainFloor
    exact div_pos (mul_pos hlower frontier.base_positive)
      (mul_pos (by norm_num) hcard)
  have hgainLower' :
      quittingStoppingLawPositiveTargetReachedRowGainFloor
          frontierPacket lower ≤
        quittingLiteralActualRowBestEndpointGain reward actual other stage := by
    simpa only [actual, stage,
      quittingStoppingLawPositiveTargetReachedRowGain,
      quittingLiteralActualRowBestEndpointGain,
      quittingLiteralActualRowTail, quittingLiteralActualRowRoot] using
        hgain rank
  have hgainPos : 0 <
      quittingLiteralActualRowBestEndpointGain reward actual other stage := by
    exact hfloor.trans_le hgainLower'
  let row : QuittingLiteralPositiveActualRowPacket reward :=
    { profile := actual
      stage := stage
      who := other
      terminal := frontierPacket.terminal
      mass := quittingStageCoalitionMass reward actual stage
        frontierPacket.terminal
      mass_eq := rfl
      mass_pos := hlower.trans_le (by
        simpa only [actual, stage] using hmass rank)
      gain_pos := hgainPos }
  refine ⟨row, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · simpa only [row, actual, stage] using hmass rank
  · exact row.not_exists_literalNashBellmanEmbedding

/-- **Uniform same-fiber repair floor for the positive-collision arm.**
Along the fixed-player subsequence selected by actual-row localization, every
approximate Nash repair which reuses the literal root and continuation has
error bounded away from zero by a table-level constant.  The division-free
form is included because it does not require a separate cardinality
denominator in downstream arithmetic. -/
theorem positiveTargetReachedRowLocalization_sameFiberRepairErrorFloor
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {regime : QuittingCounterexampleRegime reward}
    {frontier : QuittingCounterexampleStoppingLawFrontier regime}
    (frontierPacket : QuittingStoppingLawVanishingDebtRectangleSequence
      frontier)
    {lower : ℝ}
    (certificate : HasQuittingStoppingLawPositiveTargetReachedRowLocalization
      frontierPacket lower) :
    ∃ (stop : ℕ → ℕ) (subseq : ℕ → ℕ) (other : ι),
      StrictMono subseq ∧
      other ≠ frontierPacket.observer ∧
      ∀ rank (error : ℝ),
        let actual := quittingStoppingLawPositiveTargetReachedRowProfile
          frontierPacket (subseq rank)
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
  obtain ⟨hlower, stop, subseq, other, hsubseq, hother, _htime, hmass,
      hgain⟩ := certificate
  refine ⟨stop, subseq, other, hsubseq, hother, ?_⟩
  intro rank error
  dsimp only
  let actual := quittingStoppingLawPositiveTargetReachedRowProfile
    frontierPacket (subseq rank)
  let stage := stop (subseq rank)
  let gain := quittingLiteralActualRowBestEndpointGain reward actual other stage
  let players := Finset.univ.erase frontierPacket.observer
  have hotherMem : other ∈ players :=
    Finset.mem_erase.mpr ⟨hother, Finset.mem_univ other⟩
  have hcardNat : 0 < players.card :=
    Finset.card_pos.mpr ⟨other, hotherMem⟩
  have hcard : 0 < (players.card : ℝ) := by exact_mod_cast hcardNat
  have hgainFloor' :
      lower * quittingTerminalSemanticDebtSum frontier.base /
          (2 * (players.card : ℝ)) ≤ gain := by
    simpa only [actual, stage, players, gain,
      quittingStoppingLawPositiveTargetReachedRowGainFloor,
      quittingStoppingLawPositiveTargetReachedRowGain,
      quittingLiteralActualRowBestEndpointGain,
      quittingLiteralActualRowTail, quittingLiteralActualRowRoot] using
        hgain rank
  have hgainPos : 0 < gain := by
    have hdenom : 0 < 2 * (players.card : ℝ) :=
      mul_pos (by norm_num) hcard
    exact (div_pos (mul_pos hlower frontier.base_positive) hdenom).trans_le
      hgainFloor'
  let row : QuittingLiteralPositiveActualRowPacket reward :=
    { profile := actual
      stage := stage
      who := other
      terminal := frontierPacket.terminal
      mass := quittingStageCoalitionMass reward actual stage
        frontierPacket.terminal
      mass_eq := rfl
      mass_pos := hlower.trans_le (by
        simpa only [actual, stage] using hmass rank)
      gain_pos := by simpa only [gain] using hgainPos }
  intro hnash
  have hgainLe : gain ≤ error := by
    simpa only [row, gain] using
      row.gain_le_nashError_of_literal_root_tail hnash
  have hdivided : lower * quittingTerminalSemanticDebtSum frontier.base /
        (2 * (players.card : ℝ)) ≤ error :=
    hgainFloor'.trans hgainLe
  have hdenom : 0 < 2 * (players.card : ℝ) :=
    mul_pos (by norm_num) hcard
  have hscaled : lower * quittingTerminalSemanticDebtSum frontier.base ≤
      error * (2 * (players.card : ℝ)) :=
    (div_le_iff₀ hdenom).mp hdivided
  have hdivisionFree :
      lower * quittingTerminalSemanticDebtSum frontier.base / 2 ≤
        (players.card : ℝ) * error := by
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).2
    simpa [mul_comm, mul_left_comm, mul_assoc] using hscaled
  refine ⟨by simpa only [players] using hdivisionFree, ?_⟩
  simpa only [players] using hdivided

end GameTheory
