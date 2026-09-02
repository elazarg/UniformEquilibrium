/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.AbsorptionPath.PrincipalQBoundaryDirection
import Mathlib.Topology.Semicontinuity.Hemicontinuity

/-!
# The principal-Q viability correspondence

The correspondence used in the viability argument consists of simplex
directions supported on the zero coordinates of the current boundary point,
with nonnegative matrix residual at every zero coordinate.

The final theorem records an obstruction in the published argument: even for
a projective-Q-bar zero-diagonal matrix, this correspondence need not have a
sequentially closed graph, and hence is not upper hemicontinuous for the reason
claimed there.  A positive coordinate may converge to zero, activating a new
residual inequality only at the limit.
-/

noncomputable section

namespace GameTheory.QuittingLCPClassification

open Finset Math.LinearProgramming Set Filter
open scoped Topology

/-- The control correspondence used in the principal-Q viability argument. -/
def principalQViabilityControls {ι : Type} [Fintype ι]
    (M : ι → ι → ℝ) (q : ι → ℝ) : Set (stdSimplex ℝ ι) :=
  {weight | (∀ i, weight i ≠ 0 → q i = 0) ∧
    ∀ i, q i = 0 → 0 ≤ singletonLCPResidual M weight i}

private def upperHemicontinuityCounterexampleMatrix : Bool → Bool → ℝ :=
  fun receiver owner => if !receiver && owner then -1 else 0

private def upperHemicontinuityCounterexamplePoint (n : ℕ) : Bool → ℝ :=
  fun player => if player then 0 else 1 / (n + 1 : ℝ)

private def upperHemicontinuityCounterexampleLimit : Bool → ℝ := 0

private noncomputable def upperHemicontinuityCounterexampleWeight :
    stdSimplex ℝ Bool :=
  stdSimplex.vertex true

private theorem upperHemicontinuityCounterexampleMatrix_projectiveQBar :
    IsProjectiveQBarMatrix upperHemicontinuityCounterexampleMatrix := by
  intro players hplayers q
  classical
  by_cases hfalse : false ∈ players
  · let owner : players := ⟨false, hfalse⟩
    refine ⟨{
      cemetery := 0
      singleton := fun player => if player = owner then 1 else 0
      cemetery_nonneg := by norm_num
      singleton_nonneg := by intro player; split <;> norm_num
      total := ?_
      residual_nonneg := ?_
      complementary := ?_ }⟩
    · simp [owner]
    · intro receiver
      have hentry :
          principalMatrix upperHemicontinuityCounterexampleMatrix players
              receiver owner = 0 := by
        simp [principalMatrix, upperHemicontinuityCounterexampleMatrix, owner]
      simpa [owner] using (le_of_eq hentry.symm)
    · intro receiver
      have hentry :
          principalMatrix upperHemicontinuityCounterexampleMatrix players
              receiver owner = 0 := by
        simp [principalMatrix, upperHemicontinuityCounterexampleMatrix, owner]
      simp [owner, hentry]
  · have htrue : true ∈ players := by
      obtain ⟨player, hplayer⟩ := hplayers
      cases player
      · exact (hfalse hplayer).elim
      · exact hplayer
    have hallTrue (player : players) : player.1 = true := by
      cases hplayer : player.1
      · exact (hfalse (hplayer ▸ player.property)).elim
      · rfl
    let owner : players := ⟨true, htrue⟩
    refine ⟨{
      cemetery := 0
      singleton := fun player => if player = owner then 1 else 0
      cemetery_nonneg := by norm_num
      singleton_nonneg := by intro player; split <;> norm_num
      total := ?_
      residual_nonneg := ?_
      complementary := ?_ }⟩
    · simp [owner]
    · intro receiver
      simp [principalMatrix, upperHemicontinuityCounterexampleMatrix, owner,
        hallTrue receiver]
    · intro receiver
      simp [principalMatrix, upperHemicontinuityCounterexampleMatrix, owner,
        hallTrue receiver]

private theorem counterexamplePoint_tendsto_limit :
    Tendsto upperHemicontinuityCounterexamplePoint atTop
      (𝓝 upperHemicontinuityCounterexampleLimit) := by
  apply tendsto_pi_nhds.2
  intro player
  cases player
  · simpa [upperHemicontinuityCounterexamplePoint,
      upperHemicontinuityCounterexampleLimit] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  · simp [upperHemicontinuityCounterexamplePoint,
      upperHemicontinuityCounterexampleLimit]

private theorem counterexampleWeight_mem (n : ℕ) :
    upperHemicontinuityCounterexampleWeight ∈
      principalQViabilityControls upperHemicontinuityCounterexampleMatrix
        (upperHemicontinuityCounterexamplePoint n) := by
  constructor
  · intro player hweight
    cases player
    · simp [upperHemicontinuityCounterexampleWeight] at hweight
    · simp [upperHemicontinuityCounterexamplePoint]
  · intro player hzero
    cases player
    · have : (n : ℝ) + 1 ≠ 0 := by positivity
      have hdenominator : (n : ℝ) + 1 = 0 := by
        simpa [upperHemicontinuityCounterexamplePoint] using hzero
      exact (this hdenominator).elim
    · simp [singletonLCPResidual, upperHemicontinuityCounterexampleWeight,
        upperHemicontinuityCounterexampleMatrix, dotProduct]

private theorem counterexampleWeight_not_mem :
    upperHemicontinuityCounterexampleWeight ∉
      principalQViabilityControls upperHemicontinuityCounterexampleMatrix
        upperHemicontinuityCounterexampleLimit := by
  intro hmem
  have hresidual := hmem.2 false rfl
  norm_num [singletonLCPResidual, upperHemicontinuityCounterexampleWeight,
    upperHemicontinuityCounterexampleMatrix, dotProduct] at hresidual

private theorem isClosed_principalQViabilityControls_at_zero
    (M : Bool → Bool → ℝ) :
    IsClosed (principalQViabilityControls M (0 : Bool → ℝ)) := by
  rw [show principalQViabilityControls M (0 : Bool → ℝ) =
      ⋂ i, {weight | 0 ≤ singletonLCPResidual M weight i} by
    ext weight
    simp [principalQViabilityControls]]
  apply isClosed_iInter
  intro i
  exact isClosed_le continuous_const (by
    unfold singletonLCPResidual wsum dotProduct
    apply continuous_finsetSum
    intro owner _
    exact ((continuous_apply owner).comp continuous_subtype_val).mul continuous_const)

/-- Even for a projective-Q-bar zero-diagonal matrix, the principal-Q
viability correspondence need not be upper hemicontinuous. -/
theorem principalQViabilityControls_not_upperHemicontinuous :
    ∃ M : Bool → Bool → ℝ,
      IsProjectiveQBarMatrix M ∧
        (∀ player, M player player = 0) ∧
        ¬ UpperHemicontinuous (principalQViabilityControls M) := by
  refine ⟨upperHemicontinuityCounterexampleMatrix,
    upperHemicontinuityCounterexampleMatrix_projectiveQBar,
    ?_, ?_⟩
  · intro player
    cases player <;> simp [upperHemicontinuityCounterexampleMatrix]
  · intro hupper
    have hmem :=
      (hupper.upperHemicontinuousAt
        upperHemicontinuityCounterexampleLimit).mem_of_tendsto
        (isClosed_principalQViabilityControls_at_zero
          upperHemicontinuityCounterexampleMatrix)
        counterexamplePoint_tendsto_limit
        (Filter.Frequently.of_forall counterexampleWeight_mem)
        tendsto_const_nhds
    exact counterexampleWeight_not_mem hmem

/-- The viability correspondence can fail the sequential closed-graph test
even for a projective-Q-bar zero-diagonal matrix: the controls are admissible
along a convergent boundary sequence but not at its limit. -/
theorem principalQViabilityControls_not_sequentially_closed :
    ∃ (M : Bool → Bool → ℝ) (q : ℕ → Bool → ℝ) (limit : Bool → ℝ)
        (weight : stdSimplex ℝ Bool),
      IsProjectiveQBarMatrix M ∧
        (∀ player, M player player = 0) ∧
        Tendsto q atTop (𝓝 limit) ∧
        (∀ n, weight ∈ principalQViabilityControls M (q n)) ∧
        weight ∉ principalQViabilityControls M limit := by
  exact ⟨upperHemicontinuityCounterexampleMatrix,
    upperHemicontinuityCounterexamplePoint,
    upperHemicontinuityCounterexampleLimit,
    upperHemicontinuityCounterexampleWeight,
    upperHemicontinuityCounterexampleMatrix_projectiveQBar,
    by intro player; cases player <;>
      simp [upperHemicontinuityCounterexampleMatrix],
    counterexamplePoint_tendsto_limit, counterexampleWeight_mem,
    counterexampleWeight_not_mem⟩

end GameTheory.QuittingLCPClassification
