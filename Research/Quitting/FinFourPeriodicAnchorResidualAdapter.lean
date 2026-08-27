/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import
  UniformEquilibrium.Diagnostics.Quitting.Collision.SingletonPacket.FullSupportHardPrincipalSize
import UniformEquilibrium.Quitting.Stationary.ReturnedBlockTangentObstruction
import MathUE.LocalPeriodicAnchor

/-!
# Fin4 periodic-anchor residual adapter

The first layer is an explicit-kernel reindexing adapter: a nonnegative
normalized kernel for the ambient Fin4 singleton matrix is transported to the
maintained hard residual on the recursively screened normal-core subtype.
The second layer is a conditional returned-block family composition.  Under
fixed reward and matrix data, individual hazard-mesh bounds, eventual value
and anchor tubes, positive hazards, and a vector-norm signed seam, it derives
the additive singleton linearization, extracts the normalized kernel, and
contradicts the hard residual.

Neither layer produces returned blocks, periodic roots, or packet hypotheses
from an arbitrary game; the periodic family and its numerical hypotheses are
supplied by the caller.
-/

noncomputable section

namespace GameTheory

open QuittingLCPClassification
open Math.LinearProgramming
open Filter
open scoped BigOperators Topology

/-- An explicit nonnegative normalized kernel vector for a Fin4 matrix. -/
structure FinFourNormalizedKernel (M : Fin 4 → Fin 4 → ℝ) where
  value : Fin 4 → ℝ
  nonneg : ∀ player, 0 ≤ value player
  sum_eq_one : ∑ player, value player = 1
  kernel : ∀ player, ∑ owner, value owner * M player owner = 0

/-- The full ambient type is equivalent to the recursive normal-core subtype
when the latter is full.  The orientation is chosen for `reindexMatrix`. -/
def finFourNormalCoreEquiv
    (M : Fin 4 → Fin 4 → ℝ)
    (hcore : normalCore M = Finset.univ) :
    Fin 4 ≃ normalCore M where
  toFun player := ⟨player, by rw [hcore]; simp⟩
  invFun player := player.1
  left_inv _ := rfl
  right_inv player := Subtype.ext (by rfl)

/-- Under a full normal core, the normal-player matrix is the ambient matrix
reindexed onto that core subtype. -/
theorem normalPlayerMatrix_eq_finFour_reindex
    (M : Fin 4 → Fin 4 → ℝ)
    (hcore : normalCore M = Finset.univ) :
    normalPlayerMatrix M =
      reindexMatrix (finFourNormalCoreEquiv M hcore) M := by
  funext player owner
  rfl

/-- An explicit normalized kernel vector is a homogeneous simplex-LCP witness.
The equality hypotheses are intentionally stronger than feasibility, matching
the output of a signed period-closure calculation. -/
theorem hasHomogeneousSimplexSolution_of_finFourNormalizedKernel
    (M : Fin 4 → Fin 4 → ℝ)
    (kernel : FinFourNormalizedKernel M) :
    HasHomogeneousSimplexSolution M := by
  let direction : stdSimplex ℝ (Fin 4) :=
    ⟨kernel.value, kernel.nonneg, kernel.sum_eq_one⟩
  refine ⟨direction, ?_, ?_⟩
  · intro player
    rw [singletonLCPResidual_def, wsum, dotProduct]
    change 0 ≤ ∑ owner, kernel.value owner * M player owner
    rw [kernel.kernel player]
  · intro player
    rw [singletonLCPResidual_def, wsum, dotProduct]
    change kernel.value player *
        ∑ owner, kernel.value owner * M player owner = 0
    rw [kernel.kernel player]
    ring

/-- The explicit ambient kernel certificate contradicts the hard residual
after reindexing its full recursive normal core. -/
theorem finFourNormalizedKernel_false_of_residualHardClass
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound : ℝ}
    (hard : FinFourQuantitativeFullSupportHardResidual reward bound)
    (kernel : FinFourNormalizedKernel (normalizedSoloMatrix reward)) :
    False := by
  have hambient :=
    hasHomogeneousSimplexSolution_of_finFourNormalizedKernel
      (normalizedSoloMatrix reward) kernel
  have hno : ¬HasHomogeneousSimplexSolution
      (normalPlayerMatrix (normalizedSoloMatrix reward)) := by
    simpa [normalizedNormalPlayerMatrix] using
      hard.residualHardClass.no_homogeneous
  apply hno
  rw [normalPlayerMatrix_eq_finFour_reindex
    (normalizedSoloMatrix reward) hard.normalCore_eq_univ]
  exact singletonLCPFeasible_reindexMatrix_of
    (finFourNormalCoreEquiv (normalizedSoloMatrix reward)
      hard.normalCore_eq_univ) hambient

/-- Same contradiction packaged for the residual class alone, exposing the
full-core equality that callers must supply explicitly. -/
theorem finFourNormalizedKernel_false_of_residualHardClass_fields
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    (hcore : normalCore (normalizedSoloMatrix reward) = Finset.univ)
    (hno : ¬HasHomogeneousSimplexSolution
      (normalPlayerMatrix (normalizedSoloMatrix reward)))
    (kernel : FinFourNormalizedKernel (normalizedSoloMatrix reward)) :
    False := by
  have hambient :=
    hasHomogeneousSimplexSolution_of_finFourNormalizedKernel
      (normalizedSoloMatrix reward) kernel
  apply hno
  rw [normalPlayerMatrix_eq_finFour_reindex
    (normalizedSoloMatrix reward) hcore]
  exact singletonLCPFeasible_reindexMatrix_of
    (finFourNormalCoreEquiv (normalizedSoloMatrix reward) hcore) hambient

namespace QuittingReturnedProductBlock

/-- The signed successor seam differs from the aggregate singleton
linearization only by the quadratic product-law remainder.  The proof uses
the exact cyclic telescope, rather than an absolute Bellman-error bound. -/
theorem abs_sum_successorMinusValue_sub_singletonLinearization_le
    (block : QuittingReturnedProductBlock (Fin 4))
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)) {M : ℝ}
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hvalue : ∀ phase who, |block.value phase who| ≤ M) (who : Fin 4) :
    |∑ phase, (quittingRootSuccessorPayoff reward
        (block.value (block.next phase)) (block.root phase) who -
        block.value phase who) -
      ∑ phase, ∑ owner, block.hazard phase owner *
        (reward (quittingSingletonTerminal owner) who -
          block.value (block.next phase) who)| ≤
      2 * M * block.totalHazard ^ 2 := by
  let linear : Fin (block.extraPhases + 1) → ℝ := fun phase =>
    ∑ owner, block.hazard phase owner *
      (reward (quittingSingletonTerminal owner) who -
        block.value (block.next phase) who)
  let move : Fin (block.extraPhases + 1) → ℝ := fun phase =>
    quittingRootSuccessorPayoff reward (block.value (block.next phase))
      (block.root phase) who - block.value (block.next phase) who
  have hrow : ∀ phase, |move phase - linear phase| ≤
      2 * M * block.phaseHazard phase ^ 2 := by
    intro phase
    simpa [move, linear, QuittingReturnedProductBlock.hazard,
      QuittingReturnedProductBlock.phaseHazard, quittingRootQuitRates] using
      (abs_quittingRootSuccessorPayoff_sub_tail_sub_singletonLinearization_le
        reward (block.value (block.next phase)) (block.root phase) who hreward
        (hvalue (block.next phase) who))
  have hcycle : ∑ phase,
      (block.value (block.next phase) who - block.value phase who) = 0 := by
    have hnext := block.sum_comp_next (fun phase => block.value phase who)
    rw [Finset.sum_sub_distrib, hnext]
    exact sub_self _
    
  have hsum :
      (∑ phase, (quittingRootSuccessorPayoff reward
        (block.value (block.next phase)) (block.root phase) who -
        block.value phase who)) - ∑ phase, linear phase =
      ∑ phase, (move phase - linear phase) := by
    have hsplit :
        (∑ phase, (quittingRootSuccessorPayoff reward
          (block.value (block.next phase)) (block.root phase) who -
          block.value phase who)) - ∑ phase, linear phase =
          (∑ phase, (move phase - linear phase)) +
            ∑ phase, (block.value (block.next phase) who -
              block.value phase who) := by
      calc
        (∑ phase, (quittingRootSuccessorPayoff reward
          (block.value (block.next phase)) (block.root phase) who -
          block.value phase who)) - ∑ phase, linear phase =
            ∑ phase, ((quittingRootSuccessorPayoff reward
              (block.value (block.next phase)) (block.root phase) who -
              block.value phase who) - linear phase) := by
                simp only [Finset.sum_sub_distrib]
        _ = ∑ phase, ((move phase - linear phase) +
              (block.value (block.next phase) who -
                block.value phase who)) := by
                apply Finset.sum_congr rfl
                intro phase _
                dsimp [move]
                ring
        _ = (∑ phase, (move phase - linear phase)) +
              ∑ phase, (block.value (block.next phase) who -
                block.value phase who) := by
                rw [Finset.sum_add_distrib]
    rw [hsplit, hcycle, add_zero]
  have hM : 0 ≤ M := quittingRewardCoordinateBound_nonneg_of_player
    reward (0 : Fin 4) hreward
  have hsquare := block.sum_phaseHazard_sq_le
  rw [hsum]
  calc
    |∑ phase, (move phase - linear phase)| ≤
        ∑ phase, |move phase - linear phase| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ phase, 2 * M * block.phaseHazard phase ^ 2 := by
      gcongr with phase
      exact hrow phase
    _ = 2 * M * ∑ phase, block.phaseHazard phase ^ 2 := by
      rw [Finset.mul_sum]
    _ ≤ 2 * M * block.totalHazard ^ 2 := by
      exact mul_le_mul_of_nonneg_left hsquare (by positivity)

theorem abs_sum_successorMinusValue_sub_singletonLinearization_le_of_square_bound
    (block : QuittingReturnedProductBlock (Fin 4))
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)) {M squareBound : ℝ}
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hvalue : ∀ phase who, |block.value phase who| ≤ M)
    (hsquare : ∑ phase, block.phaseHazard phase ^ 2 ≤ squareBound)
    (who : Fin 4) :
    |∑ phase, (quittingRootSuccessorPayoff reward
        (block.value (block.next phase)) (block.root phase) who -
        block.value phase who) -
      ∑ phase, ∑ owner, block.hazard phase owner *
        (reward (quittingSingletonTerminal owner) who -
          block.value (block.next phase) who)| ≤ 2 * M * squareBound := by
  let linear : Fin (block.extraPhases + 1) → ℝ := fun phase =>
    ∑ owner, block.hazard phase owner *
      (reward (quittingSingletonTerminal owner) who -
        block.value (block.next phase) who)
  let move : Fin (block.extraPhases + 1) → ℝ := fun phase =>
    quittingRootSuccessorPayoff reward (block.value (block.next phase))
      (block.root phase) who - block.value (block.next phase) who
  have hrow : ∀ phase, |move phase - linear phase| ≤
      2 * M * block.phaseHazard phase ^ 2 := by
    intro phase
    simpa [move, linear, QuittingReturnedProductBlock.hazard,
      QuittingReturnedProductBlock.phaseHazard, quittingRootQuitRates] using
      (abs_quittingRootSuccessorPayoff_sub_tail_sub_singletonLinearization_le
        reward (block.value (block.next phase)) (block.root phase) who hreward
        (hvalue (block.next phase) who))
  have hcycle : ∑ phase,
      (block.value (block.next phase) who - block.value phase who) = 0 := by
    have hnext := block.sum_comp_next (fun phase => block.value phase who)
    rw [Finset.sum_sub_distrib, hnext]
    exact sub_self _
  have hsum :
      (∑ phase, (quittingRootSuccessorPayoff reward
        (block.value (block.next phase)) (block.root phase) who -
        block.value phase who)) - ∑ phase, linear phase =
      ∑ phase, (move phase - linear phase) := by
    have hsplit :
        (∑ phase, (quittingRootSuccessorPayoff reward
          (block.value (block.next phase)) (block.root phase) who -
          block.value phase who)) - ∑ phase, linear phase =
          (∑ phase, (move phase - linear phase)) +
            ∑ phase, (block.value (block.next phase) who -
              block.value phase who) := by
      calc
        (∑ phase, (quittingRootSuccessorPayoff reward
          (block.value (block.next phase)) (block.root phase) who -
          block.value phase who)) - ∑ phase, linear phase =
            ∑ phase, ((quittingRootSuccessorPayoff reward
              (block.value (block.next phase)) (block.root phase) who -
              block.value phase who) - linear phase) := by
                simp only [Finset.sum_sub_distrib]
        _ = ∑ phase, ((move phase - linear phase) +
              (block.value (block.next phase) who -
                block.value phase who)) := by
                apply Finset.sum_congr rfl
                intro phase _
                dsimp [move]
                ring
        _ = (∑ phase, (move phase - linear phase)) +
              ∑ phase, (block.value (block.next phase) who -
                block.value phase who) := by
                rw [Finset.sum_add_distrib]
    rw [hsplit, hcycle, add_zero]
  have hM : 0 ≤ M := quittingRewardCoordinateBound_nonneg_of_player
    reward (0 : Fin 4) hreward
  rw [hsum]
  calc
    |∑ phase, (move phase - linear phase)| ≤
        ∑ phase, |move phase - linear phase| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ phase, 2 * M * block.phaseHazard phase ^ 2 := by
      gcongr with phase
      exact hrow phase
    _ = 2 * M * ∑ phase, block.phaseHazard phase ^ 2 := by
      rw [Finset.mul_sum]
    _ ≤ 2 * M * squareBound := by
      exact mul_le_mul_of_nonneg_left hsquare (by positivity)

/-- The signed successor seam is close to the normalized singleton matrix
when the annotated tails stay in an anchor tube. -/
theorem abs_sum_successorMinusValue_div_sub_normalizedSingletonMatrix_le_of_square_bound
    (block : QuittingReturnedProductBlock (Fin 4))
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    {M anchor squareBound : ℝ}
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hvalue : ∀ phase who, |block.value phase who| ≤ M)
    (hsquare : ∑ phase, block.phaseHazard phase ^ 2 ≤ squareBound)
    (hpositive : 0 < block.totalHazard)
    (who : Fin 4)
    (hanchor : ∀ phase,
      |block.value (block.next phase) who -
        reward (quittingSingletonTerminal who) who| ≤ anchor) :
    |(∑ phase, (quittingRootSuccessorPayoff reward
        (block.value (block.next phase)) (block.root phase) who -
        block.value phase who)) / block.totalHazard -
      ∑ owner, (block.cumulativeHazard owner / block.totalHazard) *
        (reward (quittingSingletonTerminal owner) who -
          reward (quittingSingletonTerminal who) who)| ≤
      (2 * M * squareBound) / block.totalHazard + anchor := by
  have hrem :=
    block.abs_sum_successorMinusValue_sub_singletonLinearization_le_of_square_bound
      reward hreward hvalue hsquare who
  let linear : Fin (block.extraPhases + 1) → ℝ := fun phase =>
    ∑ owner, block.hazard phase owner *
      (reward (quittingSingletonTerminal owner) who -
        block.value (block.next phase) who)
  let target : ℝ := ∑ owner, block.cumulativeHazard owner *
    (reward (quittingSingletonTerminal owner) who -
      reward (quittingSingletonTerminal who) who)
  have htarget : |target - ∑ phase, linear phase| ≤
      block.totalHazard * anchor := by
    have hrewrite : target - ∑ phase, linear phase =
        ∑ phase, ∑ owner, block.hazard phase owner *
          (block.value (block.next phase) who -
            reward (quittingSingletonTerminal who) who) := by
      unfold target linear QuittingReturnedProductBlock.cumulativeHazard
      have hexpand :
          (∑ owner, (∑ phase, block.hazard phase owner) *
            (reward (quittingSingletonTerminal owner) who -
              reward (quittingSingletonTerminal who) who)) =
            ∑ phase, ∑ owner, block.hazard phase owner *
              (reward (quittingSingletonTerminal owner) who -
                reward (quittingSingletonTerminal who) who) := by
        simp_rw [Finset.sum_mul]
        rw [Finset.sum_comm]
      rw [hexpand]
      calc
        (∑ phase, ∑ owner, block.hazard phase owner *
            (reward (quittingSingletonTerminal owner) who -
              reward (quittingSingletonTerminal who) who)) -
            ∑ phase, ∑ owner, block.hazard phase owner *
              (reward (quittingSingletonTerminal owner) who -
                block.value (block.next phase) who) =
            ∑ phase, ((∑ owner, block.hazard phase owner *
              (reward (quittingSingletonTerminal owner) who -
                reward (quittingSingletonTerminal who) who)) -
              ∑ owner, block.hazard phase owner *
                (reward (quittingSingletonTerminal owner) who -
                  block.value (block.next phase) who)) := by
              rw [Finset.sum_sub_distrib]
        _ = ∑ phase, ∑ owner, block.hazard phase owner *
            (block.value (block.next phase) who -
              reward (quittingSingletonTerminal who) who) := by
              apply Finset.sum_congr rfl
              intro phase _
              rw [← Finset.sum_sub_distrib]
              apply Finset.sum_congr rfl
              intro owner _
              ring
    rw [hrewrite]
    calc
      |∑ phase, ∑ owner, block.hazard phase owner *
          (block.value (block.next phase) who -
            reward (quittingSingletonTerminal who) who)| ≤
          ∑ phase, ∑ owner, |block.hazard phase owner *
            (block.value (block.next phase) who -
              reward (quittingSingletonTerminal who) who)| := by
        calc
          _ ≤ ∑ phase, |∑ owner, block.hazard phase owner *
              (block.value (block.next phase) who -
                reward (quittingSingletonTerminal who) who)| :=
            Finset.abs_sum_le_sum_abs _ _
          _ ≤ _ := by
            gcongr with phase
            exact Finset.abs_sum_le_sum_abs _ _
      _ = ∑ phase, ∑ owner, block.hazard phase owner *
          |block.value (block.next phase) who -
            reward (quittingSingletonTerminal who) who| := by
        apply Finset.sum_congr rfl
        intro phase _
        apply Finset.sum_congr rfl
        intro owner _
        rw [abs_mul, abs_of_nonneg (block.hazard_nonneg phase owner)]
      _ ≤ ∑ phase, ∑ owner, block.hazard phase owner * anchor := by
        apply Finset.sum_le_sum
        intro phase _
        apply Finset.sum_le_sum
        intro owner _
        exact mul_le_mul_of_nonneg_left (hanchor phase)
          (block.hazard_nonneg phase owner)
      _ = block.totalHazard * anchor := by
        calc
          (∑ phase, ∑ owner, block.hazard phase owner * anchor) =
              ∑ phase, (∑ owner, block.hazard phase owner) * anchor := by
            apply Finset.sum_congr rfl
            intro phase _
            rw [Finset.sum_mul]
          _ = (∑ phase, ∑ owner, block.hazard phase owner) * anchor := by
            rw [Finset.sum_mul]
          _ = block.totalHazard * anchor := rfl
  have hrem' :
      |(∑ phase, (quittingRootSuccessorPayoff reward
          (block.value (block.next phase)) (block.root phase) who -
          block.value phase who)) / block.totalHazard -
        (∑ phase, linear phase) / block.totalHazard| ≤
          (2 * M * squareBound) / block.totalHazard := by
    rw [← sub_div, abs_div, abs_of_pos hpositive]
    apply (div_le_iff₀ hpositive).2
    calc
      |(∑ phase, (quittingRootSuccessorPayoff reward
          (block.value (block.next phase)) (block.root phase) who -
          block.value phase who)) - ∑ phase, linear phase| ≤
          2 * M * squareBound := by simpa [linear] using hrem
      _ = (2 * M * squareBound / block.totalHazard) *
          block.totalHazard := by field_simp
  have htarget' : |(∑ phase, linear phase) / block.totalHazard -
      target / block.totalHazard| ≤ anchor := by
    rw [← sub_div, abs_div, abs_of_pos hpositive]
    apply (div_le_iff₀ hpositive).2
    calc
      |∑ phase, linear phase - target| = |target - ∑ phase, linear phase| := by
        rw [abs_sub_comm]
      _ ≤ anchor * block.totalHazard := by simpa [mul_comm] using htarget
  have htarget_eq : target / block.totalHazard =
      ∑ owner, (block.cumulativeHazard owner / block.totalHazard) *
        (reward (quittingSingletonTerminal owner) who -
          reward (quittingSingletonTerminal who) who) := by
    unfold target
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro owner _
    ring
  rw [htarget_eq] at htarget'
  calc
    |(∑ phase, (quittingRootSuccessorPayoff reward
        (block.value (block.next phase)) (block.root phase) who -
        block.value phase who)) / block.totalHazard -
      ∑ owner, (block.cumulativeHazard owner / block.totalHazard) *
        (reward (quittingSingletonTerminal owner) who -
          reward (quittingSingletonTerminal who) who)| ≤
        |(∑ phase, (quittingRootSuccessorPayoff reward
          (block.value (block.next phase)) (block.root phase) who -
          block.value phase who)) / block.totalHazard -
          (∑ phase, linear phase) / block.totalHazard| +
        |(∑ phase, linear phase) / block.totalHazard -
          ∑ owner, (block.cumulativeHazard owner / block.totalHazard) *
            (reward (quittingSingletonTerminal owner) who -
              reward (quittingSingletonTerminal who) who)| := by
      rw [← sub_add_sub_cancel]
      exact abs_add_le _ _
    _ ≤ (2 * M * squareBound) / block.totalHazard + anchor := by
      apply add_le_add hrem'
      simpa [mul_comm] using htarget'

/-- The same estimate with the residual sign used by a Bellman defect:
`value - successor` plus the singleton matrix term is small. -/
theorem abs_sum_valueMinusSuccessor_div_add_normalizedSingletonMatrix_le_of_square_bound
    (block : QuittingReturnedProductBlock (Fin 4))
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    {M anchor squareBound : ℝ}
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hvalue : ∀ phase who, |block.value phase who| ≤ M)
    (hsquare : ∑ phase, block.phaseHazard phase ^ 2 ≤ squareBound)
    (hpositive : 0 < block.totalHazard)
    (who : Fin 4)
    (hanchor : ∀ phase,
      |block.value (block.next phase) who -
        reward (quittingSingletonTerminal who) who| ≤ anchor) :
    |(∑ phase, (block.value phase who - quittingRootSuccessorPayoff reward
        (block.value (block.next phase)) (block.root phase) who)) /
        block.totalHazard +
      ∑ owner, (block.cumulativeHazard owner / block.totalHazard) *
        (reward (quittingSingletonTerminal owner) who -
          reward (quittingSingletonTerminal who) who)| ≤
      (2 * M * squareBound) / block.totalHazard + anchor := by
  have h :=
    block.abs_sum_successorMinusValue_div_sub_normalizedSingletonMatrix_le_of_square_bound
      reward hreward hvalue hsquare hpositive who hanchor
  have hneg : ∑ phase, (block.value phase who -
      quittingRootSuccessorPayoff reward (block.value (block.next phase))
        (block.root phase) who) =
      -(∑ phase, (quittingRootSuccessorPayoff reward
        (block.value (block.next phase)) (block.root phase) who -
        block.value phase who)) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro phase _
    ring
  have hidentity :
      (∑ phase, (block.value phase who - quittingRootSuccessorPayoff reward
        (block.value (block.next phase)) (block.root phase) who)) /
          block.totalHazard +
        ∑ owner, (block.cumulativeHazard owner / block.totalHazard) *
          (reward (quittingSingletonTerminal owner) who -
            reward (quittingSingletonTerminal who) who) =
        -((∑ phase, (quittingRootSuccessorPayoff reward
          (block.value (block.next phase)) (block.root phase) who -
          block.value phase who)) / block.totalHazard -
        ∑ owner, (block.cumulativeHazard owner / block.totalHazard) *
          (reward (quittingSingletonTerminal owner) who -
            reward (quittingSingletonTerminal who) who)) := by
    rw [hneg]
    ring
  rw [hidentity, abs_neg]
  exact h

theorem sum_phaseHazard_sq_le_four_mul_mesh_mul_totalHazard
    (block : QuittingReturnedProductBlock (Fin 4))
    (mesh : ℝ)
    (hphase_mesh : ∀ phase, block.phaseHazard phase ≤ 4 * mesh) :
    ∑ phase, block.phaseHazard phase ^ 2 ≤
      4 * mesh * block.totalHazard := by
  calc
    ∑ phase, block.phaseHazard phase ^ 2 ≤
        ∑ phase, (4 * mesh) * block.phaseHazard phase := by
      apply Finset.sum_le_sum
      intro phase _
      have hphase := block.phaseHazard_nonneg phase
      nlinarith [hphase_mesh phase]
    _ = 4 * mesh * block.totalHazard := by
      unfold QuittingReturnedProductBlock.totalHazard
        QuittingReturnedProductBlock.phaseHazard
      rw [← Finset.mul_sum]

theorem phaseHazard_le_four_mul_of_hazard_le
    (block : QuittingReturnedProductBlock (Fin 4))
    (mesh : ℝ)
    (hhazard : ∀ phase player, block.hazard phase player ≤ mesh) :
    ∀ phase, block.phaseHazard phase ≤ 4 * mesh := by
  have hmesh : 0 ≤ mesh := by
    exact (block.hazard_nonneg 0 0).trans (hhazard 0 0)
  intro phase
  calc
    block.phaseHazard phase ≤ ∑ _player : Fin 4, mesh := by
      unfold QuittingReturnedProductBlock.phaseHazard
      apply Finset.sum_le_sum
      intro player _
      exact hhazard phase player
    _ = 4 * mesh := by
      simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
      norm_num

theorem square_linearization_bound
    (block : QuittingReturnedProductBlock (Fin 4))
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    {M anchor squareBound : ℝ}
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hvalue : ∀ phase who, |block.value phase who| ≤ M)
    (hsquare : ∑ phase, block.phaseHazard phase ^ 2 ≤ squareBound)
    (hpositive : 0 < block.totalHazard)
    (who : Fin 4)
    (hanchor : ∀ phase,
      |block.value (block.next phase) who -
        reward (quittingSingletonTerminal who) who| ≤ anchor) :
    |(∑ phase, (block.value phase who - quittingRootSuccessorPayoff reward
        (block.value (block.next phase)) (block.root phase) who)) /
        block.totalHazard +
      ∑ owner, (block.cumulativeHazard owner / block.totalHazard) *
        (reward (quittingSingletonTerminal owner) who -
          reward (quittingSingletonTerminal who) who)| ≤
      (2 * M * squareBound) / block.totalHazard + anchor := by
  exact abs_sum_valueMinusSuccessor_div_add_normalizedSingletonMatrix_le_of_square_bound
    block reward hreward hvalue hsquare hpositive who hanchor

end QuittingReturnedProductBlock

/-! ## Periodic-anchor composition -/

open MathUE.LocalPeriodicAnchor

structure FinFourPeriodicAnchorFamily
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (M : ℝ) where
  blocks : ℕ → QuittingReturnedProductBlock (Fin 4)
  mesh : ℕ → ℝ
  anchorError : ℕ → ℝ
  reward_bound : ∀ S player, |reward S player| ≤ M
  value_bound : ∀ h phase player, |(blocks h).value phase player| ≤ M
  positive_hazard : ∀ h, 0 < (blocks h).totalHazard
  mesh_tendsto : Tendsto mesh atTop (nhds (0 : ℝ))
  individual_hazard : ∀ h phase player, (blocks h).hazard phase player ≤ mesh h
  anchor_tendsto : Tendsto anchorError atTop (nhds (0 : ℝ))
  anchor_bound : ∀ h phase player,
    |(blocks h).value phase player -
      reward (quittingSingletonTerminal player) player| ≤ anchorError h
  seam_tendsto : ∀ player, Tendsto
    (fun h =>
      (∑ (phase : Fin ((blocks h).extraPhases + 1)),
        ((blocks h).value phase player -
          quittingRootSuccessorPayoff reward ((blocks h).value ((blocks h).next phase))
            ((blocks h).root phase) player)) /
        (blocks h).totalHazard) atTop (nhds (0 : ℝ))

/-! The following theorem is the packet-facing composition. -/

theorem finFourPeriodicAnchor_false_of_returnedProductBlock_family
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound M : ℝ}
    (hard : FinFourQuantitativeFullSupportHardResidual reward bound)
    (family : FinFourPeriodicAnchorFamily reward M) :
    False := by
  let period : ℕ → ℕ := fun h => (family.blocks h).extraPhases + 1
  let q : (h : ℕ) → Fin (period h) → Fin 4 → ℝ := fun h phase player =>
    (family.blocks h).hazard phase player
  let p : (h : ℕ) → Fin (period h) → Fin 4 → ℝ := fun h phase player =>
    (family.blocks h).value phase player -
      quittingRootSuccessorPayoff reward
        ((family.blocks h).value ((family.blocks h).next phase))
        ((family.blocks h).root phase) player
  have hQ : ∀ h phase player, 0 ≤ q h phase player := by
    intro h phase player
    exact (family.blocks h).hazard_nonneg phase player
  have hpositive : ∀ h, 0 < totalHazard period q h := by
    intro h
    simpa [period, q, totalHazard, QuittingReturnedProductBlock.totalHazard,
      QuittingReturnedProductBlock.phaseHazard] using family.positive_hazard h
  have hseam : ∀ player, Tendsto
      (fun h => signedSeam period p h player / totalHazard period q h)
      atTop (nhds 0) := by
    intro player
    simpa [period, p, q, signedSeam, totalHazard,
      QuittingReturnedProductBlock.totalHazard,
      QuittingReturnedProductBlock.phaseHazard] using family.seam_tendsto player
  have hM : 0 ≤ M := quittingRewardCoordinateBound_nonneg_of_player
    reward (0 : Fin 4) family.reward_bound
  let error : ℕ → ℝ := fun h => 8 * M * family.mesh h + family.anchorError h
  have herror : Tendsto error atTop (nhds 0) := by
    dsimp [error]
    simpa [mul_comm, add_comm, add_left_comm, add_assoc] using
      (family.mesh_tendsto.const_mul (8 * M)).add family.anchor_tendsto
  have hlinear : ∀ h player,
      |signedSeam period p h player / totalHazard period q h +
        matrixApply (normalizedSoloMatrix reward)
          (normalizedHazard period q h) player| ≤ error h := by
    intro h player
    have hquad :=
      (family.blocks h).sum_phaseHazard_sq_le_four_mul_mesh_mul_totalHazard
        (family.mesh h) (QuittingReturnedProductBlock.phaseHazard_le_four_mul_of_hazard_le
          (family.blocks h) (family.mesh h) (family.individual_hazard h))
    have hrow :=
      QuittingReturnedProductBlock.square_linearization_bound
        (family.blocks h)
        reward family.reward_bound (family.value_bound h) hquad
        (family.positive_hazard h) player (fun phase =>
          family.anchor_bound h ((family.blocks h).next phase) player)
    have hmatrix :
        matrixApply (normalizedSoloMatrix reward)
            (normalizedHazard period q h) player =
          ∑ owner, ((family.blocks h).cumulativeHazard owner /
            (family.blocks h).totalHazard) *
            (reward (quittingSingletonTerminal owner) player -
              reward (quittingSingletonTerminal player) player) := by
      simp only [matrixApply, normalizedSoloMatrix_eq_soloReward_sub,
        quittingSoloReward, quittingSingletonTerminal, normalizedHazard,
        cumulativeHazard, totalHazard]
      apply Finset.sum_congr rfl
      intro owner howner
      simp only [QuittingReturnedProductBlock.cumulativeHazard,
        QuittingReturnedProductBlock.totalHazard,
        QuittingReturnedProductBlock.phaseHazard, period, q]
      ring
    rw [hmatrix]
    change
      |(∑ phase, ((family.blocks h).value phase player -
        quittingRootSuccessorPayoff reward
          ((family.blocks h).value ((family.blocks h).next phase))
          ((family.blocks h).root phase) player)) /
          (family.blocks h).totalHazard +
        ∑ owner, ((family.blocks h).cumulativeHazard owner /
          (family.blocks h).totalHazard) *
          (reward (quittingSingletonTerminal owner) player -
            reward (quittingSingletonTerminal player) player)| ≤ error h
    convert hrow using 1
    dsimp [error]
    field_simp [ne_of_gt (family.positive_hazard h)]
    ring
  obtain ⟨limit, subsequence, _, hnonneg, hsum, hkernel, _⟩ :=
    exists_normalizedHazard_subsequence_kernel_of_additive_linearization
      period q p (normalizedSoloMatrix reward) hQ hpositive hseam error herror
        hlinear
  let kernel : FinFourNormalizedKernel (normalizedSoloMatrix reward) := {
    value := limit
    nonneg := hnonneg
    sum_eq_one := hsum
    kernel := fun player => by
      simpa [matrixApply, mul_comm] using hkernel player }
  exact finFourNormalizedKernel_false_of_residualHardClass hard kernel

structure FinFourPeriodicAnchorPacketFamily
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (M : ℝ) where
  blocks : ℕ → QuittingReturnedProductBlock (Fin 4)
  mesh : ℕ → ℝ
  anchorError : ℕ → ℝ
  reward_bound : ∀ S player, |reward S player| ≤ M
  positive_hazard : ∀ h, 0 < (blocks h).totalHazard
  mesh_tendsto : Tendsto mesh atTop (nhds (0 : ℝ))
  individual_hazard : ∀ h phase player, (blocks h).hazard phase player ≤ mesh h
  value_bound_eventually : ∀ᶠ h in atTop, ∀ phase player,
    |(blocks h).value phase player| ≤ M
  anchor_tendsto : Tendsto anchorError atTop (nhds (0 : ℝ))
  anchor_bound_eventually : ∀ᶠ h in atTop, ∀ phase player,
    |(blocks h).value phase player -
      reward (quittingSingletonTerminal player) player| ≤ anchorError h
  seam_tendsto : Tendsto
    (fun h => ‖fun player : Fin 4 =>
      (∑ (phase : Fin ((blocks h).extraPhases + 1)),
        ((blocks h).value phase player -
          quittingRootSuccessorPayoff reward
            ((blocks h).value ((blocks h).next phase))
            ((blocks h).root phase) player)) /
        (blocks h).totalHazard‖)
    atTop (nhds (0 : ℝ))

theorem finFourPeriodicAnchor_false_of_packet_family
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound M : ℝ}
    (hard : FinFourQuantitativeFullSupportHardResidual reward bound)
    (family : FinFourPeriodicAnchorPacketFamily reward M) :
    False := by
  let period : ℕ → ℕ := fun h => (family.blocks h).extraPhases + 1
  let q : (h : ℕ) → Fin (period h) → Fin 4 → ℝ := fun h phase player =>
    (family.blocks h).hazard phase player
  let p : (h : ℕ) → Fin (period h) → Fin 4 → ℝ := fun h phase player =>
    (family.blocks h).value phase player -
      quittingRootSuccessorPayoff reward
        ((family.blocks h).value ((family.blocks h).next phase))
        ((family.blocks h).root phase) player
  let error : ℕ → ℝ := fun h => 8 * M * family.mesh h + family.anchorError h
  have hQ : ∀ h phase player, 0 ≤ q h phase player := by
    intro h phase player
    exact (family.blocks h).hazard_nonneg phase player
  have hpositive : ∀ h, 0 < totalHazard period q h := by
    intro h
    simpa [period, q, totalHazard,
      QuittingReturnedProductBlock.totalHazard,
      QuittingReturnedProductBlock.phaseHazard] using family.positive_hazard h
  have hseam : Tendsto
      (fun h => ‖fun player : Fin 4 =>
        signedSeam period p h player / totalHazard period q h‖)
      atTop (nhds 0) := by
    change Tendsto (fun h => ‖fun player : Fin 4 =>
      (∑ (phase : Fin ((family.blocks h).extraPhases + 1)),
        ((family.blocks h).value phase player -
          quittingRootSuccessorPayoff reward
            ((family.blocks h).value ((family.blocks h).next phase))
            ((family.blocks h).root phase) player)) /
        (family.blocks h).totalHazard‖) atTop (nhds 0)
    exact family.seam_tendsto
  have hM : 0 ≤ M := quittingRewardCoordinateBound_nonneg_of_player
    reward (0 : Fin 4) family.reward_bound
  have herror : Tendsto error atTop (nhds 0) := by
    dsimp [error]
    simpa [mul_comm, add_comm, add_left_comm, add_assoc] using
      (family.mesh_tendsto.const_mul (8 * M)).add family.anchor_tendsto
  have hlinear : ∀ᶠ h in atTop, ‖fun player : Fin 4 =>
      signedSeam period p h player / totalHazard period q h +
        matrixApply (normalizedSoloMatrix reward)
          (normalizedHazard period q h) player‖ ≤ error h := by
    filter_upwards [family.value_bound_eventually,
      family.anchor_bound_eventually] with h hvalue hanchor
    have hmesh : 0 ≤ family.mesh h := by
      exact ((family.blocks h).hazard_nonneg 0 0).trans
        (family.individual_hazard h 0 0)
    have hanchor0 : 0 ≤ family.anchorError h := by
      exact le_trans (abs_nonneg _) (hanchor 0 0)
    have herror0 : 0 ≤ error h := by
      dsimp [error]
      nlinarith
    apply (pi_norm_le_iff_of_nonneg herror0).2
    intro player
    have hquad :=
      (family.blocks h).sum_phaseHazard_sq_le_four_mul_mesh_mul_totalHazard
        (family.mesh h) (QuittingReturnedProductBlock.phaseHazard_le_four_mul_of_hazard_le
          (family.blocks h) (family.mesh h) (family.individual_hazard h))
    have hrow :=
      QuittingReturnedProductBlock.square_linearization_bound (family.blocks h)
        reward family.reward_bound (by exact hvalue) hquad
        (family.positive_hazard h) player (fun phase =>
          hanchor ((family.blocks h).next phase) player)
    have hmatrix :
        matrixApply (normalizedSoloMatrix reward)
            (normalizedHazard period q h) player =
          ∑ owner, ((family.blocks h).cumulativeHazard owner /
            (family.blocks h).totalHazard) *
            (reward (quittingSingletonTerminal owner) player -
              reward (quittingSingletonTerminal player) player) := by
      simp only [matrixApply, normalizedSoloMatrix_eq_soloReward_sub,
        quittingSoloReward, quittingSingletonTerminal, normalizedHazard,
        cumulativeHazard, totalHazard]
      apply Finset.sum_congr rfl
      intro owner _
      simp only [QuittingReturnedProductBlock.cumulativeHazard,
        QuittingReturnedProductBlock.totalHazard,
        QuittingReturnedProductBlock.phaseHazard, period, q]
      ring
    rw [hmatrix]
    have hcoord :
        |(∑ phase, ((family.blocks h).value phase player -
          quittingRootSuccessorPayoff reward
            ((family.blocks h).value ((family.blocks h).next phase))
            ((family.blocks h).root phase) player)) /
            (family.blocks h).totalHazard +
          ∑ owner, ((family.blocks h).cumulativeHazard owner /
            (family.blocks h).totalHazard) *
            (reward (quittingSingletonTerminal owner) player -
              reward (quittingSingletonTerminal player) player)| ≤ error h := by
      convert hrow using 1
      dsimp [error]
      field_simp [ne_of_gt (family.positive_hazard h)]
      ring
    simpa [signedSeam, p, period, q, totalHazard,
      QuittingReturnedProductBlock.totalHazard,
      QuittingReturnedProductBlock.phaseHazard, Real.norm_eq_abs] using hcoord
  obtain ⟨limit, subsequence, _, hnonneg, hsum, hkernel, _⟩ :=
    exists_normalizedHazard_subsequence_kernel_of_eventually_additive_norm_seam
      period q p (normalizedSoloMatrix reward) hQ hpositive hseam error herror hlinear
  let kernel : FinFourNormalizedKernel (normalizedSoloMatrix reward) := {
    value := limit
    nonneg := hnonneg
    sum_eq_one := hsum
    kernel := fun player => by
      simpa [matrixApply, mul_comm] using hkernel player }
  exact finFourNormalizedKernel_false_of_residualHardClass hard kernel

/-- A vanishing-mesh periodic anchor cannot satisfy the hard residual's
normalized singleton linearization.  The normalized kernel is produced by
the finite-dimensional compactness theorem, rather than supplied by the
caller. -/
theorem finFourPeriodicAnchor_false_of_vanishing_mesh_anchor
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound : ℝ}
    (hard : FinFourQuantitativeFullSupportHardResidual reward bound)
    (period : ℕ → ℕ)
    (q : (h : ℕ) → Fin (period h) → Fin 4 → ℝ)
    (p : (h : ℕ) → Fin (period h) → Fin 4 → ℝ)
    (mesh anchorError : ℕ → ℝ) (constant : ℝ)
    (hQ : ∀ h phase player, 0 ≤ q h phase player)
    (hpositive : ∀ h, 0 < totalHazard period q h)
    (hmesh : Tendsto mesh atTop (nhds 0))
    (hanchor : Tendsto anchorError atTop (nhds 0))
    (hseam : ∀ player, Tendsto
      (fun h => signedSeam period p h player / totalHazard period q h)
      atTop (nhds 0))
    (hlinear : ∀ h player,
      |signedSeam period p h player / totalHazard period q h -
        matrixApply (normalizedSoloMatrix reward)
          (normalizedHazard period q h) player| ≤
        constant * (mesh h + anchorError h)) :
    False := by
  obtain ⟨limit, subsequence, hsubsequence, hnonneg, hsum, hkernel, _⟩ :=
    exists_normalizedHazard_subsequence_kernel_of_vanishing_mesh_anchor
      period q p (normalizedSoloMatrix reward) mesh anchorError constant hQ
      hpositive hmesh hanchor hseam hlinear
  let kernel : FinFourNormalizedKernel (normalizedSoloMatrix reward) := {
    value := limit
    nonneg := hnonneg
    sum_eq_one := hsum
    kernel := fun player => by
      simpa [matrixApply, mul_comm] using hkernel player }
  exact finFourNormalizedKernel_false_of_residualHardClass hard kernel

/-- Generic first-order version of the periodic-anchor contradiction.  This
is the direct interface for a game-specific Bellman linearization proof. -/
theorem finFourPeriodicAnchor_false_of_linearization
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound : ℝ}
    (hard : FinFourQuantitativeFullSupportHardResidual reward bound)
    (period : ℕ → ℕ)
    (q : (h : ℕ) → Fin (period h) → Fin 4 → ℝ)
    (p : (h : ℕ) → Fin (period h) → Fin 4 → ℝ)
    (error : ℕ → ℝ)
    (hQ : ∀ h phase player, 0 ≤ q h phase player)
    (hpositive : ∀ h, 0 < totalHazard period q h)
    (hseam : ∀ player, Tendsto
      (fun h => signedSeam period p h player / totalHazard period q h)
      atTop (nhds 0))
    (herror : Tendsto error atTop (nhds 0))
    (hlinear : ∀ h player,
      |signedSeam period p h player / totalHazard period q h -
        matrixApply (normalizedSoloMatrix reward)
          (normalizedHazard period q h) player| ≤ error h) :
    False := by
  obtain ⟨limit, subsequence, hsubsequence, hnonneg, hsum, hkernel, _⟩ :=
    exists_normalizedHazard_subsequence_kernel
      period q p (normalizedSoloMatrix reward) hQ hpositive hseam error herror
        hlinear
  let kernel : FinFourNormalizedKernel (normalizedSoloMatrix reward) := {
    value := limit
    nonneg := hnonneg
    sum_eq_one := hsum
    kernel := fun player => by
      simpa [matrixApply, mul_comm] using hkernel player }
  exact finFourNormalizedKernel_false_of_residualHardClass hard kernel

end GameTheory
