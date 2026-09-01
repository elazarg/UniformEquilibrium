/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.AbsorptionPath.AKRSSequentialPerfectionDecoder
import UniformEquilibrium.Quitting.AbsorptionPath.RootSequenceAbsorbingCompletionChronologicalPositiveSingletonRate

/-!
# Sequentially perfect absorption paths produce branch S.3

The path-level consumer turns a supplied sequentially perfect absorption path
with no terminal total jump into the literal well-supported, completely
absorbing branch S.3.  A source-facing adapter applies it to the actual
chronological limit path; neither theorem asserts a terminal-jump branch or a
three-way classification.
-/

noncomputable section

namespace GameTheory

open Filter StochasticGame
open scoped BigOperators Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

namespace QuittingAbsorptionPath

/-- Conditional path-level S.3 capstone after isolating the exact published
positive-singleton reverse-entrance producer.  All partition, productization,
telescope, support, and vanishing-resolution work is discharged here. -/
theorem
    exists_wellSupportedAbsorbingSequence_of_sequentiallyPerfectAbsorptionPath_of_reverseEntrance
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (path : AbsorptionPath (ι := ι))
    (hpathTotal : ∀ time ∈ Set.Icc (0 : ℝ) 1,
      pathTotal path.1 time ≤ 1)
    (hperfect : IsSequentiallyPerfectAbsorptionPath reward path 0)
    (hnoTerminalJump : HasNoTerminalTotalJump path)
    (hreverse : ∀ resolution, 3 ≤ resolution →
      HasPartitionPositiveSingletonReverseEntranceEstimate
        reward path resolution) :
    QuittingWellSupportedAbsorbingSequenceExistence reward := by
  intro δ hδ
  obtain ⟨rank, hrank⟩ :=
    ((tendsto_order.1 (tendsto_partitionSupportError_add_three reward)).2
      δ hδ).exists
  let resolution := rank + 3
  have hresolution : 3 ≤ resolution := by
    dsimp only [resolution]
    omega
  let hcollision := hasPartitionSmallCellCollisionDomination path hpathTotal
    hnoTerminalJump resolution hresolution
  let roots := partitionCellRoots path hpathTotal hnoTerminalJump resolution
    hresolution hcollision
  refine ⟨roots, ?_, ?_⟩
  · exact isCompletelyAbsorbing_partitionCellRoots path hpathTotal
      hnoTerminalJump resolution hresolution hcollision
  · intro stage
    have hrow := partitionCellRoot_supportApproxNash reward path hpathTotal
      hperfect hnoTerminalJump resolution hresolution hcollision
      (hreverse resolution hresolution) stage
    apply hrow.mono
    simpa only [resolution] using hrank.le

/-- A sequentially perfect absorption path without a terminal total jump
produces well-supported completely absorbing stationary rows at every
positive tolerance. -/
theorem exists_wellSupportedAbsorbingSequence_of_sequentiallyPerfectAbsorptionPath
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (path : AbsorptionPath (ι := ι))
    (hpathTotal : ∀ time ∈ Set.Icc (0 : ℝ) 1,
      pathTotal path.1 time ≤ 1)
    (hperfect : IsSequentiallyPerfectAbsorptionPath reward path 0)
    (hnoTerminalJump : HasNoTerminalTotalJump path) :
    QuittingWellSupportedAbsorbingSequenceExistence reward := by
  apply
    exists_wellSupportedAbsorbingSequence_of_sequentiallyPerfectAbsorptionPath_of_reverseEntrance
      reward path hpathTotal hperfect hnoTerminalJump
  intro resolution hresolution
  exact hasPartitionPositiveSingletonReverseEntranceEstimate reward path
    hpathTotal hperfect hnoTerminalJump resolution hresolution

/-- Literal short specification of the no-terminal-jump S.3 consumer. -/
def SequentiallyPerfectAbsorptionPathS3Capstone : Prop :=
  ∀
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (path : AbsorptionPath (ι := ι)),
    (∀ time ∈ Set.Icc (0 : ℝ) 1, pathTotal path.1 time ≤ 1) →
    IsSequentiallyPerfectAbsorptionPath reward path 0 →
    HasNoTerminalTotalJump path →
    QuittingWellSupportedAbsorbingSequenceExistence reward

/-- The literal no-terminal-jump S.3 specification is satisfied. -/
theorem sequentiallyPerfectAbsorptionPathS3Capstone :
    SequentiallyPerfectAbsorptionPathS3Capstone (ι := ι) := by
  intro reward path hpathTotal hperfect hnoTerminalJump
  exact exists_wellSupportedAbsorbingSequence_of_sequentiallyPerfectAbsorptionPath
    reward path hpathTotal hperfect hnoTerminalJump

end QuittingAbsorptionPath

namespace QuittingRootSequenceAbsorbingCompletionDiagonal

variable
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {source : QuittingRootSequenceVanishingNashFamily reward}
    {diagonal : QuittingRootSequenceAbsorbingCompletionDiagonal reward source}

namespace ChronologicalLimit

/-- The actual chronological limit enters branch S.3 whenever it has no
terminal total jump. -/
theorem wellSupportedAbsorbingSequenceExistence_of_noTerminalTotalJump
    (limit : diagonal.ChronologicalLimit)
    (hnoTerminalJump :
      QuittingAbsorptionPath.HasNoTerminalTotalJump limit.absorptionPath) :
    QuittingWellSupportedAbsorbingSequenceExistence reward := by
  exact
    QuittingAbsorptionPath.sequentiallyPerfectAbsorptionPathS3Capstone
      reward limit.absorptionPath
      (by simpa only [absorptionPath] using limit.pathTotal_le_one)
      limit.isSequentiallyPerfectAbsorptionPath hnoTerminalJump

end ChronologicalLimit
end QuittingRootSequenceAbsorbingCompletionDiagonal
end GameTheory
