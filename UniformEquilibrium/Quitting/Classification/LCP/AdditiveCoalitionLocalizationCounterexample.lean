import MathUE.LinearProgramming.Examples.PositiveInverseFourMatrices
import UniformEquilibrium.Quitting.Classification.LCP.QuittingRewardAdapter
import UniformEquilibrium.Quitting.Paths.SureExitSet
import UniformEquilibrium.Quitting.Stationary.DiscountedDisplacement

/-!
# Additive coalition completion defeats matrix-only localization

The negative-determinant positive-inverse matrix fixture admits an additive
coalition-reward completion with both a small interior discounted fixed point
and remote fixed points carrying two sure quitters.  This is a counterexample
only to localization from matrix data alone, not to uniform-equilibrium
existence.
-/

noncomputable section

namespace GameTheory
namespace AdditiveCoalitionLocalizationCounterexample

open Math.PMFProduct QuittingLCPClassification QuittingSureSetOwnerRepair
open _root_.Math.LinearProgramming.PositiveInverseFourMatrices

abbrev Player := Fin 4

/-- The source packet's nonnegative affine anchor. -/
def anchor : Payoff Player := ![1, 0, 0, 0]

/-- The literal additive completion `a_i + sum_{j in S} M_ij`. -/
def reward : {S : Finset Player // S.Nonempty} → Payoff Player :=
  fun terminal who =>
    anchor who + ∑ owner ∈ terminal.1, NegativeDeterminant.matrix who owner

/-- The additive completion has exactly the source singleton matrix. -/
theorem quittingSingletonMatrix_reward :
    quittingSingletonMatrix reward = NegativeDeterminant.matrix := by
  funext who owner
  simp [quittingSingletonMatrix, reward, NegativeDeterminant.diagonal_zero]

/-- For the additive completion, the actual discounted displacement factors
by opponents' all-Continue mass and the displayed affine matrix residual. -/
theorem quittingDiscountedDisplacement_eq
    (discount : ℝ) (hazard : Player → ℝ) (who : Player) :
    quittingDiscountedDisplacement reward discount hazard who =
      continueMassExcl hazard who *
        (discount * anchor who -
          (1 - discount) * NegativeDeterminant.matrix.mulVec hazard who) := by
  fin_cases who
  · change quittingDiscountedDisplacement reward discount hazard 0 =
      continueMassExcl hazard 0 *
        (discount * anchor 0 -
          (1 - discount) * NegativeDeterminant.matrix.mulVec hazard 0)
    unfold quittingDiscountedDisplacement continueMassExcl sigmaValue excludedValue
    rw [show Finset.univ.erase (0 : Player) = {1, 2, 3} by decide]
    rw [show ({1, 2, 3} : Finset Player).powerset =
      {∅, {1}, {2}, {3}, {1, 2}, {1, 3}, {2, 3}, {1, 2, 3}} by decide]
    simp +decide [Finset.sdiff_eq_filter, Finset.filter_insert,
      Finset.filter_singleton, weightOfReward, reward, anchor,
      NegativeDeterminant.matrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    ring
  · change quittingDiscountedDisplacement reward discount hazard 1 =
      continueMassExcl hazard 1 *
        (discount * anchor 1 -
          (1 - discount) * NegativeDeterminant.matrix.mulVec hazard 1)
    unfold quittingDiscountedDisplacement continueMassExcl sigmaValue excludedValue
    rw [show Finset.univ.erase (1 : Player) = {0, 2, 3} by decide]
    rw [show ({0, 2, 3} : Finset Player).powerset =
      {∅, {0}, {2}, {3}, {0, 2}, {0, 3}, {2, 3}, {0, 2, 3}} by decide]
    simp +decide [Finset.sdiff_eq_filter, Finset.filter_insert,
      Finset.filter_singleton, weightOfReward, reward, anchor,
      NegativeDeterminant.matrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    ring
  · change quittingDiscountedDisplacement reward discount hazard 2 =
      continueMassExcl hazard 2 *
        (discount * anchor 2 -
          (1 - discount) * NegativeDeterminant.matrix.mulVec hazard 2)
    unfold quittingDiscountedDisplacement continueMassExcl sigmaValue excludedValue
    rw [show Finset.univ.erase (2 : Player) = {0, 1, 3} by decide]
    rw [show ({0, 1, 3} : Finset Player).powerset =
      {∅, {0}, {1}, {3}, {0, 1}, {0, 3}, {1, 3}, {0, 1, 3}} by decide]
    simp +decide [Finset.sdiff_eq_filter, Finset.filter_insert,
      Finset.filter_singleton, weightOfReward, reward, anchor,
      NegativeDeterminant.matrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    ring
  · change quittingDiscountedDisplacement reward discount hazard 3 =
      continueMassExcl hazard 3 *
        (discount * anchor 3 -
          (1 - discount) * NegativeDeterminant.matrix.mulVec hazard 3)
    unfold quittingDiscountedDisplacement continueMassExcl sigmaValue excludedValue
    rw [show Finset.univ.erase (3 : Player) = {0, 1, 2} by decide]
    rw [show ({0, 1, 2} : Finset Player).powerset =
      {∅, {0}, {1}, {2}, {0, 1}, {0, 2}, {1, 2}, {0, 1, 2}} by decide]
    simp +decide [Finset.sdiff_eq_filter, Finset.filter_insert,
      Finset.filter_singleton, weightOfReward, reward, anchor,
      NegativeDeterminant.matrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    ring

/-- The discount complement used by the displayed interior fixed point. -/
def smallDiscount : ℝ := 1 / 101

/-- The displayed small interior hazard vector. -/
def smallHazard : Player → ℝ := ![3 / 50, 1 / 20, 3 / 100, 1 / 25]

theorem smallHazard_pos (who : Player) : 0 < smallHazard who := by
  fin_cases who <;> norm_num [smallHazard]

theorem smallHazard_lt_one (who : Player) : smallHazard who < 1 := by
  fin_cases who <;> norm_num [smallHazard]

theorem quittingDiscountedDisplacement_smallHazard (who : Player) :
    quittingDiscountedDisplacement reward smallDiscount smallHazard who = 0 := by
  rw [quittingDiscountedDisplacement_eq]
  fin_cases who <;>
    norm_num [smallDiscount, smallHazard, anchor, NegativeDeterminant.matrix,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

/-- The displayed interior vector is a fixed point of the actual clipped
discounted displacement map. -/
theorem quittingDiscountedClippedMap_smallHazard :
    quittingDiscountedClippedMap reward smallDiscount smallHazard = smallHazard := by
  funext who
  rw [quittingDiscountedClippedMap]
  rw [quittingDiscountedDisplacement_smallHazard]
  have hzero := (smallHazard_pos who).le
  have hone := (smallHazard_lt_one who).le
  simp [min_eq_right hone, max_eq_right hzero]

private theorem continueMassExcl_eq_zero_of_two_sure
    (hazard : Player → ℝ) {first second who : Player}
    (hdistinct : first ≠ second) (hfirst : hazard first = 1)
    (hsecond : hazard second = 1) :
    continueMassExcl hazard who = 0 := by
  by_cases hwho : who = first
  · subst who
    unfold continueMassExcl
    apply Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hdistinct.symm, Finset.mem_univ _⟩)
    rw [hsecond]
    norm_num
  · unfold continueMassExcl
    apply Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨Ne.symm hwho, Finset.mem_univ _⟩)
    rw [hfirst]
    norm_num

/-- Every cube hazard with two distinct sure quitters is a fixed point of the
actual clipped discounted map, at every discount parameter. -/
theorem quittingDiscountedClippedMap_eq_self_of_two_sure
    (discount : ℝ) (hazard : Player → ℝ)
    (hzero : ∀ who, 0 ≤ hazard who) (hone : ∀ who, hazard who ≤ 1)
    {first second : Player} (hdistinct : first ≠ second)
    (hfirst : hazard first = 1) (hsecond : hazard second = 1) :
    quittingDiscountedClippedMap reward discount hazard = hazard := by
  funext who
  have hmass := continueMassExcl_eq_zero_of_two_sure
    hazard hdistinct hfirst hsecond (who := who)
  rw [quittingDiscountedClippedMap, quittingDiscountedDisplacement_eq, hmass,
    zero_mul, add_zero]
  simp [max_eq_right (hzero who), min_eq_right (hone who)]

/-- At all Quit, no player gains by leaving: its omitted diagonal summand is
zero.  The conclusion controls unrestricted behavioral deviations. -/
theorem allQuit_terminalNash :
    (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) 0
      (quittingStationaryProfile reward
        (quittingPureSetRoot (Finset.univ : Finset Player))) := by
  rw [isεAsymptoticNash_pureSetRoot_univ_iff]
  intro who
  have huniv : (Finset.univ : Finset Player).Nontrivial := by decide
  simp [quittingSetReward, huniv, reward, NegativeDeterminant.diagonal_zero]

end AdditiveCoalitionLocalizationCounterexample
end GameTheory
