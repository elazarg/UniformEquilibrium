/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Classification.LCP.ThreeCore.AmbientCarrierElimination
import UniformEquilibrium.Quitting.Stationary.ReturnedBlockPrincipalRestriction

/-!
# Ambient returned-block gap for a four-player counterexample

Every four-player counterexample has full recursive normal core.  Consequently
the zero-hazard condition off the core in the principal returned-block gap is
vacuous, and the relative-error obstruction applies to every bounded ambient
returned block.

This theorem does not produce returned blocks and does not use projective-Q-bar
failure; it uses only counterexample-facing nonhomogeneity and full core.
-/

noncomputable section

namespace GameTheory

open QuittingLCPClassification
open ThreeCoreAmbientCarrierElimination

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Exact ambient returned-block restriction used below. -/
def HasAmbientReturnedBlockRelativeErrorGap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (K : ℝ) : Prop :=
  ∃ δ > 0, ∃ c > 0, ∀ block : QuittingReturnedProductBlock ι,
    (∀ phase who, |block.value phase who| ≤ K) →
    0 < block.totalHazard → block.totalHazard ≤ δ →
    c * block.totalHazard ≤
      block.bellmanError reward + block.endpointRegret reward

/-- A four-player counterexample has a returned-block relative-error gap for
all bounded ambient blocks.  Full core removes the off-core zero-hazard
hypothesis from the existing principal restriction theorem. -/
theorem hasAmbientReturnedBlockRelativeErrorGap_of_fourPlayer_counterexample
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hplayers : Fintype.card ι = 4)
    (hnot : ¬∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff)
    (K : ℝ) :
    HasAmbientReturnedBlockRelativeErrorGap reward K := by
  have hcore :=
    normalCore_eq_univ_of_fourPlayer_not_exists_uniformEquilibriumPayoff
      reward hplayers hnot
  have hstandard :=
    standardQMatrixSide_of_not_exists_uniformEquilibriumPayoff reward hnot
  have hno : ¬HasHomogeneousSimplexSolution
      (principalMatrix (normalizedSoloMatrix reward)
        (normalCore (normalizedSoloMatrix reward))) := by
    simpa only [normalizedNormalPlayerMatrix, normalPlayerMatrix] using
      hstandard.no_homogeneous
  obtain ⟨δ, hδ, c, hc, hgap⟩ :=
    exists_pos_ambientReturnedBlock_relativeError_gap reward
      (normalCore (normalizedSoloMatrix reward)) hstandard.normal_nonempty
      (K := K) hno
  refine ⟨δ, hδ, c, hc, fun block hvalue hpositive hsmall ↦ ?_⟩
  apply hgap block
  · intro phase who _
    exact hvalue phase who
  · intro phase who houtside
    rw [hcore] at houtside
    simp at houtside
  · exact hpositive
  · exact hsmall

end GameTheory
