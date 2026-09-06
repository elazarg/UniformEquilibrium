import UniformEquilibrium.Quitting.Projective.RobustChargedRelation
import UniformEquilibrium.Quitting.Root.BoundedEndpoint
import UniformEquilibrium.Quitting.Root.VectorTranslation

/-! # Common vector translation and displacement of robust edges -/

noncomputable section

namespace GameTheory

variable {player : Type} [Fintype player] [DecidableEq player]
variable {bound tolerance : ℝ}

omit [Fintype player] [DecidableEq player] in
/-- An inner boxed state shifted coordinatewise by `[0, ε/4]` lies in the
outer box enlarged by one when `ε ≤ 1`. -/
theorem quittingPayoffVectorTranslate_mem_enlargedBox
    (state : QuittingRobustChargedState player bound)
    (shift : Payoff player) (epsilon : ℝ)
    (hshiftNonneg : ∀ who, 0 ≤ shift who)
    (hshiftUpper : ∀ who, shift who ≤ epsilon / 4)
    (hepsilonMax : epsilon ≤ 1) :
    ∀ who, |quittingPayoffVectorTranslate state.1 shift who| ≤ bound + 1 := by
  intro who
  have hstate := (abs_le.mp (state.2 who))
  rw [abs_le]
  constructor <;> dsimp only [quittingPayoffVectorTranslate] <;>
    nlinarith [hshiftNonneg who, hshiftUpper who]

/-- Translate a boxed robust state into the box enlarged by one. -/
def QuittingRobustChargedState.vectorTranslate
    (state : QuittingRobustChargedState player bound)
    (shift : Payoff player) (epsilon : ℝ)
    (hshiftNonneg : ∀ who, 0 ≤ shift who)
    (hshiftUpper : ∀ who, shift who ≤ epsilon / 4)
    (hepsilonMax : epsilon ≤ 1) :
    QuittingRobustChargedState player (bound + 1) :=
  ⟨quittingPayoffVectorTranslate state.1 shift,
    quittingPayoffVectorTranslate_mem_enlargedBox state shift epsilon
      hshiftNonneg hshiftUpper hepsilonMax⟩

omit [Fintype player] [DecidableEq player] in
@[simp] theorem QuittingRobustChargedState.vectorTranslate_val
    (state : QuittingRobustChargedState player bound)
    (shift : Payoff player) (epsilon : ℝ)
    (hshiftNonneg : ∀ who, 0 ≤ shift who)
    (hshiftUpper : ∀ who, shift who ≤ epsilon / 4)
    (hepsilonMax : epsilon ≤ 1) :
    (state.vectorTranslate shift epsilon hshiftNonneg hshiftUpper
      hepsilonMax).1 = quittingPayoffVectorTranslate state.1 shift := rfl

/-- The translated residual obeys the sharper half-tolerance estimate used
inside the outer robust relation. -/
theorem abs_vectorTranslate_robustEdge_residual_le_half
    {reward : {S : Finset player // S.Nonempty} → Payoff player}
    {epsilon bound : ℝ}
    (edge : QuittingRobustChargedEdge reward (epsilon / 4) bound)
    (shift : Payoff player) (hshiftNonneg : ∀ who, 0 ≤ shift who)
    (hshiftUpper : ∀ who, shift who ≤ epsilon / 4) (who : player) :
    |quittingPayoffVectorTranslate edge.1.2.1 shift who -
        quittingRootSuccessorPayoff reward
          (quittingPayoffVectorTranslate edge.1.1.1.1 shift)
          (quittingRootOfSimplex edge.1.1.2) who| ≤
      epsilon / 2 * quittingRootAbsorptionMass
        (quittingRootOfSimplex edge.1.1.2) := by
  have hedge := (edge.2 who).1
  change |edge.1.2.1 who -
      quittingRootSuccessorPayoff reward edge.1.1.1.1
        (quittingRootOfSimplex edge.1.1.2) who| ≤
    epsilon / 4 * quittingRootAbsorptionMass
      (quittingRootOfSimplex edge.1.1.2) at hedge
  have habsorption := quittingRootAbsorptionMass_nonneg
    (quittingRootOfSimplex edge.1.1.2)
  rw [quittingPayoffVectorTranslate_residual_eq]
  calc
    |edge.1.2.1 who - quittingRootSuccessorPayoff reward edge.1.1.1.1
          (quittingRootOfSimplex edge.1.1.2) who +
        quittingRootAbsorptionMass
          (quittingRootOfSimplex edge.1.1.2) * shift who| ≤
      |edge.1.2.1 who - quittingRootSuccessorPayoff reward edge.1.1.1.1
          (quittingRootOfSimplex edge.1.1.2) who| +
        |quittingRootAbsorptionMass
          (quittingRootOfSimplex edge.1.1.2) * shift who| := abs_add_le _ _
    _ ≤ epsilon / 4 * quittingRootAbsorptionMass
            (quittingRootOfSimplex edge.1.1.2) +
          quittingRootAbsorptionMass
            (quittingRootOfSimplex edge.1.1.2) * (epsilon / 4) := by
      apply add_le_add hedge
      rw [abs_mul, abs_of_nonneg habsorption,
        abs_of_nonneg (hshiftNonneg who)]
      exact mul_le_mul_of_nonneg_left (hshiftUpper who) habsorption
    _ = epsilon / 2 * quittingRootAbsorptionMass
          (quittingRootOfSimplex edge.1.1.2) := by ring

/-- The translated ordinary Nash regret obeys the same sharper
half-tolerance estimate. -/
theorem vectorTranslate_robustEdge_regret_le_half
    {reward : {S : Finset player // S.Nonempty} → Payoff player}
    {epsilon bound : ℝ}
    (edge : QuittingRobustChargedEdge reward (epsilon / 4) bound)
    (shift : Payoff player) (hshiftNonneg : ∀ who, 0 ≤ shift who)
    (hshiftUpper : ∀ who, shift who ≤ epsilon / 4) (who : player) :
    quittingRootCoordinateNashDefect reward
        (quittingPayoffVectorTranslate edge.1.1.1.1 shift)
        (quittingRootOfSimplex edge.1.1.2) who ≤
      epsilon / 2 * quittingRootAbsorptionMass
        (quittingRootOfSimplex edge.1.1.2) := by
  have hedge := (edge.2 who).2
  change quittingRootCoordinateNashDefect reward edge.1.1.1.1
      (quittingRootOfSimplex edge.1.1.2) who ≤
    epsilon / 4 * quittingRootAbsorptionMass
      (quittingRootOfSimplex edge.1.1.2) at hedge
  calc
    quittingRootCoordinateNashDefect reward
        (quittingPayoffVectorTranslate edge.1.1.1.1 shift)
        (quittingRootOfSimplex edge.1.1.2) who ≤
      quittingRootCoordinateNashDefect reward edge.1.1.1.1
          (quittingRootOfSimplex edge.1.1.2) who +
        quittingRootAbsorptionMass
          (quittingRootOfSimplex edge.1.1.2) * (epsilon / 4) :=
      quittingRootCoordinateNashDefect_vectorTranslate_le reward
        edge.1.1.1.1 shift (quittingRootOfSimplex edge.1.1.2) who
          (epsilon / 4) (hshiftNonneg who) (hshiftUpper who)
    _ ≤ epsilon / 4 * quittingRootAbsorptionMass
            (quittingRootOfSimplex edge.1.1.2) +
          quittingRootAbsorptionMass
            (quittingRootOfSimplex edge.1.1.2) * (epsilon / 4) :=
      add_le_add hedge le_rfl
    _ = epsilon / 2 * quittingRootAbsorptionMass
          (quittingRootOfSimplex edge.1.1.2) := by ring

/-- Every inner robust edge, for every admissible vector shift, becomes an
outer robust edge with the same simplex root. -/
def QuittingRobustChargedEdge.vectorTranslate
    {reward : {S : Finset player // S.Nonempty} → Payoff player}
    {epsilon bound : ℝ}
    (edge : QuittingRobustChargedEdge reward (epsilon / 4) bound)
    (shift : Payoff player) (hepsilonNonneg : 0 ≤ epsilon)
    (hepsilonMax : epsilon ≤ 1)
    (hshiftNonneg : ∀ who, 0 ≤ shift who)
    (hshiftUpper : ∀ who, shift who ≤ epsilon / 4) :
    QuittingRobustChargedEdge reward epsilon (bound + 1) := by
  let source := edge.1.1.1.vectorTranslate shift epsilon
    hshiftNonneg hshiftUpper hepsilonMax
  let target := edge.1.2.vectorTranslate shift epsilon
    hshiftNonneg hshiftUpper hepsilonMax
  let data : QuittingRobustChargedEdgeData player (bound + 1) :=
    ((source, edge.1.1.2), target)
  refine ⟨data, ?_⟩
  intro who
  have hscale : epsilon / 2 * quittingRootAbsorptionMass
      (quittingRootOfSimplex edge.1.1.2) ≤
      epsilon * quittingRootAbsorptionMass (quittingRootOfSimplex edge.1.1.2) :=
    mul_le_mul_of_nonneg_right (by linarith)
      (quittingRootAbsorptionMass_nonneg _)
  exact ⟨(abs_vectorTranslate_robustEdge_residual_le_half
    edge shift hshiftNonneg hshiftUpper who).trans hscale,
    (vectorTranslate_robustEdge_regret_le_half
      edge shift hshiftNonneg hshiftUpper who).trans hscale⟩

@[simp] theorem QuittingRobustChargedEdge.vectorTranslate_root
    {reward : {S : Finset player // S.Nonempty} → Payoff player}
    {epsilon bound : ℝ}
    (edge : QuittingRobustChargedEdge reward (epsilon / 4) bound)
    (shift : Payoff player) (hepsilonNonneg : 0 ≤ epsilon)
    (hepsilonMax : epsilon ≤ 1)
    (hshiftNonneg : ∀ who, 0 ≤ shift who)
    (hshiftUpper : ∀ who, shift who ≤ epsilon / 4) :
    (QuittingRobustChargedEdge.vectorTranslate edge shift hepsilonNonneg
      hepsilonMax hshiftNonneg hshiftUpper).1.1.2 = edge.1.1.2 := rfl

@[simp] theorem QuittingRobustChargedEdge.vectorTranslate_source
    {reward : {S : Finset player // S.Nonempty} → Payoff player}
    {epsilon bound : ℝ}
    (edge : QuittingRobustChargedEdge reward (epsilon / 4) bound)
    (shift : Payoff player) (hepsilonNonneg : 0 ≤ epsilon)
    (hepsilonMax : epsilon ≤ 1)
    (hshiftNonneg : ∀ who, 0 ≤ shift who)
    (hshiftUpper : ∀ who, shift who ≤ epsilon / 4) :
    (QuittingRobustChargedEdge.vectorTranslate edge shift hepsilonNonneg
      hepsilonMax hshiftNonneg hshiftUpper).1.1.1.1 =
        quittingPayoffVectorTranslate edge.1.1.1.1 shift := rfl

@[simp] theorem QuittingRobustChargedEdge.vectorTranslate_target
    {reward : {S : Finset player // S.Nonempty} → Payoff player}
    {epsilon bound : ℝ}
    (edge : QuittingRobustChargedEdge reward (epsilon / 4) bound)
    (shift : Payoff player) (hepsilonNonneg : 0 ≤ epsilon)
    (hepsilonMax : epsilon ≤ 1)
    (hshiftNonneg : ∀ who, 0 ≤ shift who)
    (hshiftUpper : ∀ who, shift who ≤ epsilon / 4) :
    (QuittingRobustChargedEdge.vectorTranslate edge shift hepsilonNonneg
      hepsilonMax hshiftNonneg hshiftUpper).1.2.1 =
        quittingPayoffVectorTranslate edge.1.2.1 shift := rfl

@[simp] theorem QuittingRobustChargedEdge.vectorTranslate_charge
    {reward : {S : Finset player // S.Nonempty} → Payoff player}
    {epsilon bound : ℝ}
    (edge : QuittingRobustChargedEdge reward (epsilon / 4) bound)
    (shift : Payoff player) (hepsilonNonneg : 0 ≤ epsilon)
    (hepsilonMax : epsilon ≤ 1)
    (hshiftNonneg : ∀ who, 0 ≤ shift who)
    (hshiftUpper : ∀ who, shift who ≤ epsilon / 4) :
    (quittingFloorFreeRobustChargedRelation reward epsilon (bound + 1)).charge
        (QuittingRobustChargedEdge.vectorTranslate edge shift hepsilonNonneg
          hepsilonMax hshiftNonneg hshiftUpper) =
      (quittingFloorFreeRobustChargedRelation
        reward (epsilon / 4) bound).charge edge := rfl

/-- A robust edge's coordinate displacement is bounded by its actual
absorption charge times `rewardBound + bound + tolerance`. -/
theorem abs_quittingRobustChargedEdge_target_sub_source_le
    (reward : {S : Finset player // S.Nonempty} → Payoff player)
    (rewardBound tolerance bound : ℝ)
    (hreward : ∀ terminal who, |reward terminal who| ≤ rewardBound)
    (edge : QuittingRobustChargedEdge reward tolerance bound)
    (who : player) :
    |edge.1.2.1 who - edge.1.1.1.1 who| ≤
      (rewardBound + bound + tolerance) *
        quittingRootAbsorptionMass (quittingRootOfSimplex edge.1.1.2) := by
  have hedge := (edge.2 who).1
  have habsorption := quittingRootAbsorptionMass_nonneg
    (quittingRootOfSimplex edge.1.1.2)
  have habsorbing := abs_quittingRootAbsorbingContribution_le reward
    (quittingRootOfSimplex edge.1.1.2) who rewardBound hreward
  have hsource := edge.1.1.1.2 who
  have hsuccessor :
      |quittingRootSuccessorPayoff reward edge.1.1.1.1
          (quittingRootOfSimplex edge.1.1.2) who - edge.1.1.1.1 who| ≤
        (rewardBound + bound) *
          quittingRootAbsorptionMass (quittingRootOfSimplex edge.1.1.2) := by
    rw [quittingRootSuccessorPayoff_sub_tail]
    calc
      |quittingRootAbsorbingContribution reward
          (quittingRootOfSimplex edge.1.1.2) who -
        quittingRootAbsorptionMass (quittingRootOfSimplex edge.1.1.2) *
          edge.1.1.1.1 who| ≤
        |quittingRootAbsorbingContribution reward
          (quittingRootOfSimplex edge.1.1.2) who| +
        |quittingRootAbsorptionMass (quittingRootOfSimplex edge.1.1.2) *
          edge.1.1.1.1 who| := abs_sub _ _
      _ ≤ rewardBound * quittingRootAbsorptionMass
              (quittingRootOfSimplex edge.1.1.2) +
            quittingRootAbsorptionMass (quittingRootOfSimplex edge.1.1.2) *
              bound := by
        apply add_le_add habsorbing
        rw [abs_mul, abs_of_nonneg habsorption]
        exact mul_le_mul_of_nonneg_left hsource habsorption
      _ = (rewardBound + bound) *
          quittingRootAbsorptionMass (quittingRootOfSimplex edge.1.1.2) := by
        ring
  rw [show edge.1.2.1 who - edge.1.1.1.1 who =
      (edge.1.2.1 who - quittingRootSuccessorPayoff reward edge.1.1.1.1
        (quittingRootOfSimplex edge.1.1.2) who) +
      (quittingRootSuccessorPayoff reward edge.1.1.1.1
        (quittingRootOfSimplex edge.1.1.2) who - edge.1.1.1.1 who) by ring]
  calc
    |edge.1.2.1 who - quittingRootSuccessorPayoff reward edge.1.1.1.1
          (quittingRootOfSimplex edge.1.1.2) who +
        (quittingRootSuccessorPayoff reward edge.1.1.1.1
          (quittingRootOfSimplex edge.1.1.2) who - edge.1.1.1.1 who)| ≤
      |edge.1.2.1 who - quittingRootSuccessorPayoff reward edge.1.1.1.1
        (quittingRootOfSimplex edge.1.1.2) who| +
      |quittingRootSuccessorPayoff reward edge.1.1.1.1
        (quittingRootOfSimplex edge.1.1.2) who - edge.1.1.1.1 who| :=
      abs_add_le _ _
    _ ≤ tolerance * quittingRootAbsorptionMass
            (quittingRootOfSimplex edge.1.1.2) +
          (rewardBound + bound) * quittingRootAbsorptionMass
            (quittingRootOfSimplex edge.1.1.2) := add_le_add hedge hsuccessor
    _ = (rewardBound + bound + tolerance) *
        quittingRootAbsorptionMass (quittingRootOfSimplex edge.1.1.2) := by
      ring

/-- At the inner tolerance `epsilon / 4`, the displacement constant is the
literal derivative-transfer denominator `rewardBound + bound + epsilon / 4`. -/
theorem abs_innerQuittingRobustChargedEdge_target_sub_source_le
    (reward : {S : Finset player // S.Nonempty} → Payoff player)
    (rewardBound epsilon bound : ℝ)
    (hreward : ∀ terminal who, |reward terminal who| ≤ rewardBound)
    (edge : QuittingRobustChargedEdge reward (epsilon / 4) bound)
    (who : player) :
    |edge.1.2.1 who - edge.1.1.1.1 who| ≤
      (rewardBound + bound + epsilon / 4) *
        quittingRootAbsorptionMass (quittingRootOfSimplex edge.1.1.2) :=
  abs_quittingRobustChargedEdge_target_sub_source_le reward rewardBound
    (epsilon / 4) bound hreward edge who

end GameTheory
