/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import UniformEquilibrium.Quitting.Classification.LCP.FullNormalCoreHomogeneousTransfer
import UniformEquilibrium.Quitting.Classification.LCP.ThreeCore.AmbientCarrierElimination

/-! # Uniform singleton-column blockers for a four-player counterexample -/

noncomputable section

namespace GameTheory

open Filter Set
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

open QuittingLCPClassification Math.LinearProgramming
open ThreeCoreAmbientCarrierElimination

/-- One fixed off-diagonal blocker in every singleton column, together with
the common strictly positive gap obtained by minimizing over the finite
player set. -/
structure SingletonColumnBlockerCertificate
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) where
  blocker : ι → ι
  gap : ℝ
  gap_pos : 0 < gap
  blocker_ne : ∀ owner, blocker owner ≠ owner
  gap_le : ∀ owner, gap ≤
    quittingSoloReward reward (blocker owner) (blocker owner) -
      quittingSoloReward reward owner (blocker owner)

/-- Equation (24): a four-player counterexample has no homogeneous solution
for its full normalized singleton matrix and therefore admits a fixed blocker
in every column with one common positive gap. -/
theorem exists_singletonColumnBlockerCertificate_of_fourPlayer_noUniform
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hplayers : Fintype.card ι = 4)
    (hno : ¬ ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff) :
    (¬HasHomogeneousSimplexSolution (normalizedSoloMatrix reward)) ∧
      Nonempty (SingletonColumnBlockerCertificate reward) := by
  letI : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
  have hside := standardQMatrixSide_of_not_exists_uniformEquilibriumPayoff reward hno
  have hcore := normalCore_eq_univ_of_fourPlayer_not_exists_uniformEquilibriumPayoff
    reward hplayers hno
  have hnoFull : ¬HasHomogeneousSimplexSolution (normalizedSoloMatrix reward) :=
    mt (singletonLCPFeasible_normalPlayerMatrix_iff_of_normalCore_eq_univ
      (normalizedSoloMatrix reward) hcore).mpr hside.no_homogeneous
  classical
  choose blocker hnegative using fun owner ↦
    exists_negative_entry_in_column_of_noHomogeneous
      (normalizedSoloMatrix reward) (normalizedSoloMatrix_diagonal reward) hnoFull owner
  let gaps : Finset ℝ := Finset.univ.image fun owner ↦
    -(normalizedSoloMatrix reward (blocker owner) owner)
  have hgaps : gaps.Nonempty := Finset.image_nonempty.mpr Finset.univ_nonempty
  let gap := gaps.min' hgaps
  have hgapPos : 0 < gap := by
    have hmem := Finset.min'_mem gaps hgaps
    rw [Finset.mem_image] at hmem
    obtain ⟨owner, _, hgap⟩ := hmem
    change 0 < gaps.min' hgaps
    rw [← hgap]
    exact neg_pos.mpr (hnegative owner)
  refine ⟨hnoFull, ⟨{
    blocker := blocker
    gap := gap
    gap_pos := hgapPos
    blocker_ne := ?_
    gap_le := ?_ }⟩⟩
  · intro owner heq
    have h := hnegative owner
    rw [heq, normalizedSoloMatrix_diagonal] at h
    linarith
  · intro owner
    have hle : gap ≤ -(normalizedSoloMatrix reward (blocker owner) owner) :=
      Finset.min'_le gaps _ (Finset.mem_image.mpr ⟨owner, Finset.mem_univ _, rfl⟩)
    rw [normalizedSoloMatrix_eq_projectiveLCPMatrix] at hle
    simpa [quittingProjectiveLCPMatrix, quittingSoloReward,
      quittingProjectiveSingletonTerminal] using hle

end GameTheory
