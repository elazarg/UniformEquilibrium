import UniformEquilibrium.Quitting.Examples.BoxedNashChargeSharedMatrix
import UniformEquilibrium.Quitting.Stationary.SingletonAxisResponse
import UniformEquilibrium.Quitting.Stationary.ResponseInvariantQuotient

/-! # Literal nonlinear boxed-table response screens

The last nondiscrete candidate for the shared singleton matrix is rejected
using the actual full rewards. Its unequal quadratic responses cannot be
deduced from the singleton matrix alone.
-/

noncomputable section

namespace GameTheory.BoxedNashChargeSharedMatrix

theorem full_axis_response (rate : ℝ) (player : Fin 3) :
    quittingDiscountedDisplacement BoxedNashChargeFullCoreFixture.reward 0
      (singletonRow rate 0) player.succ =
        (![rate - 2 * rate ^ 2, rate - rate ^ 2 / 2, rate - 2 * rate ^ 2] :
          Fin 3 → ℝ) player := by
  fin_cases player <;>
    rw [quittingDiscountedDisplacement_singletonRow_of_ne _ (by decide) rate] <;>
    norm_num [weightOfReward, BoxedNashChargeFullCoreFixture.reward,
      Math.FiniteCoalition.binaryCode_finFour, Math.FiniteCoalition.binaryCode] <;> ring

theorem triple_axis_response (rate : ℝ) (player : Fin 3) :
    quittingDiscountedDisplacement BoxedNashChargeTripleFixture.reward 0
      (singletonRow rate 3) player.castSucc =
        (![rate + 3 * rate ^ 2, rate + 2 * rate ^ 2, rate + 2 * rate ^ 2] :
          Fin 3 → ℝ) player := by
  fin_cases player <;>
    rw [quittingDiscountedDisplacement_singletonRow_of_ne _ (by decide) rate] <;>
    norm_num [weightOfReward, BoxedNashChargeTripleFixture.reward,
      Math.FiniteCoalition.binaryCode_finFour, Math.FiniteCoalition.binaryCode] <;> ring

def fullPivotPartition : Fin 4 → Fin 2 := ![0, 1, 1, 1]
def triplePivotPartition : Fin 4 → Fin 2 := ![1, 1, 1, 0]

theorem full_pivotPartition_not_responseInvariant :
    ¬QuittingResponseInvariantOnUnitCube BoxedNashChargeFullCoreFixture.reward
      fullPivotPartition := by
  intro hinvariant
  have hbox : ∀ coordinate : Fin 2,
      0 ≤ (![1 / 2, 0] : Fin 2 → ℝ) coordinate ∧
        (![1 / 2, 0] : Fin 2 → ℝ) coordinate ≤ 1 := by
    intro coordinate
    fin_cases coordinate <;> norm_num
  have heq := hinvariant ![1 / 2, 0] hbox 1 2 (by rfl)
  have hlift : quittingBlockLift fullPivotPartition ![1 / 2, 0] =
      singletonRow (1 / 2) 0 := by
    funext player
    fin_cases player <;> norm_num [quittingBlockLift, fullPivotPartition, singletonRow]
  rw [hlift] at heq
  have hfirst := full_axis_response (1 / 2) 0
  have hsecond := full_axis_response (1 / 2) 1
  norm_num at hfirst hsecond
  rw [hfirst, hsecond] at heq
  norm_num at heq

theorem triple_pivotPartition_not_responseInvariant :
    ¬QuittingResponseInvariantOnUnitCube BoxedNashChargeTripleFixture.reward
      triplePivotPartition := by
  intro hinvariant
  have hbox : ∀ coordinate : Fin 2,
      0 ≤ (![1 / 2, 0] : Fin 2 → ℝ) coordinate ∧
        (![1 / 2, 0] : Fin 2 → ℝ) coordinate ≤ 1 := by
    intro coordinate
    fin_cases coordinate <;> norm_num
  have heq := hinvariant ![1 / 2, 0] hbox 0 1 (by rfl)
  have hlift : quittingBlockLift triplePivotPartition ![1 / 2, 0] =
      singletonRow (1 / 2) 3 := by
    funext player
    fin_cases player <;> norm_num [quittingBlockLift, triplePivotPartition, singletonRow]
  rw [hlift] at heq
  have hfirst := triple_axis_response (1 / 2) 0
  have hsecond := triple_axis_response (1 / 2) 1
  norm_num at hfirst hsecond
  rw [hfirst, hsecond] at heq
  norm_num at heq

end GameTheory.BoxedNashChargeSharedMatrix
