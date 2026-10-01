import UniformEquilibrium.Quitting.Examples.BlockPair.PairedCubicStationaryExample
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! # Actual three-active-coordinate Jacobian of the paired cubic table

The active coordinates are independent: no equality of the first two hazards is
imposed until evaluation of the derivative at the original algebraic root.
Every polynomial below is identified with the original source residual.
-/

noncomputable section

namespace GameTheory.PairedCubicStationaryExample

open QuittingFinFourEndpointRows Math.Finset
open scoped Topology

def activeHazard (point : Fin 3 → ℝ) : Fin 4 → ℝ :=
  ![point 0, point 1, point 2, 0]

def activeResponse (table : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (point : Fin 3 → ℝ) : Fin 3 → ℝ :=
  fun coordinate => quittingDiscountedDisplacement table 0 (activeHazard point)
    coordinate.castSucc

def thirdActiveEquation (first second : ℝ) : ℝ :=
  (first + second - first * second) *
      (1 - 2 * first - 2 * second + 3 * first * second) - 3 * first * second

private theorem active_quit_0 (point : Fin 3 → ℝ) :
    pureQuitEndpointRowSum reward (activeHazard point) 0 = 1 + point 1 - 4 * point 1 * point 2 := by
  norm_num +decide [pureQuitEndpointRowSum, Fin.sum_univ_succ, opponentCoalitionMass,
    finFourCoalitionOfRow, Fin.prod_univ_succ, activeHazard, weightOfReward,
    reward, rationalQuittingRewardToReal, rationalReward]
  ring

private theorem active_quit_1 (point : Fin 3 → ℝ) :
    pureQuitEndpointRowSum reward (activeHazard point) 1 = 1 + point 0 - 4 * point 0 * point 2 := by
  norm_num +decide [pureQuitEndpointRowSum, Fin.sum_univ_succ, opponentCoalitionMass,
    finFourCoalitionOfRow, Fin.prod_univ_succ, activeHazard, weightOfReward,
    reward, rationalQuittingRewardToReal, rationalReward]
  ring

private theorem active_quit_2 (point : Fin 3 → ℝ) :
    pureQuitEndpointRowSum reward (activeHazard point) 2 =
      1 - 2 * point 0 - 2 * point 1 + 3 * point 0 * point 1 := by
  norm_num +decide [pureQuitEndpointRowSum, Fin.sum_univ_succ, opponentCoalitionMass,
    finFourCoalitionOfRow, Fin.prod_univ_succ, activeHazard, weightOfReward,
    reward, rationalQuittingRewardToReal, rationalReward]
  ring

private theorem active_excluded_0 (point : Fin 3 → ℝ) :
    excludedEndpointRowSum reward (activeHazard point) 0 = 4 * point 1 - 3 * point 1 * point 2 := by
  norm_num +decide [excludedEndpointRowSum, Fin.sum_univ_succ, opponentCoalitionMass,
    finFourCoalitionOfRow, Fin.prod_univ_succ, activeHazard, weightOfReward,
    reward, rationalQuittingRewardToReal, rationalReward]
  ring

private theorem active_excluded_1 (point : Fin 3 → ℝ) :
    excludedEndpointRowSum reward (activeHazard point) 1 = 4 * point 0 - 3 * point 0 * point 2 := by
  norm_num +decide [excludedEndpointRowSum, Fin.sum_univ_succ, opponentCoalitionMass,
    finFourCoalitionOfRow, Fin.prod_univ_succ, activeHazard, weightOfReward,
    reward, rationalQuittingRewardToReal, rationalReward]
  ring

private theorem active_excluded_2 (point : Fin 3 → ℝ) :
    excludedEndpointRowSum reward (activeHazard point) 2 = 3 * point 0 * point 1 := by
  norm_num +decide [excludedEndpointRowSum, Fin.sum_univ_succ, opponentCoalitionMass,
    finFourCoalitionOfRow, Fin.prod_univ_succ, activeHazard, weightOfReward,
    reward, rationalQuittingRewardToReal, rationalReward]
  ring

/-- The literal three independent active equations, for every signed hazard vector. -/
theorem activeResponse_eq (point : Fin 3 → ℝ) :
    activeResponse reward point =
      ![secondPolynomial (point 1) (point 2), secondPolynomial (point 0) (point 2),
        thirdActiveEquation (point 0) (point 1)] := by
  ext coordinate
  unfold activeResponse quittingDiscountedDisplacement
  rw [sigmaValue_eq_pureQuitEndpointRowSum, excludedValue_eq_excludedEndpointRowSum]
  fin_cases coordinate
  · change (1 - (1 - (0 : ℝ)) * continueMassExcl (activeHazard point) 0) *
        pureQuitEndpointRowSum reward (activeHazard point) 0 -
        excludedEndpointRowSum reward (activeHazard point) 0 = _
    rw [active_quit_0, active_excluded_0]
    unfold continueMassExcl
    rw [show (Finset.univ : Finset (Fin 4)).erase 0 = {1, 2, 3} by decide]
    norm_num [activeHazard, secondPolynomial, thirdActiveEquation]
    ring
  · change (1 - (1 - (0 : ℝ)) * continueMassExcl (activeHazard point) 1) *
        pureQuitEndpointRowSum reward (activeHazard point) 1 -
        excludedEndpointRowSum reward (activeHazard point) 1 = _
    rw [active_quit_1, active_excluded_1]
    unfold continueMassExcl
    rw [show (Finset.univ : Finset (Fin 4)).erase 1 = {0, 2, 3} by decide]
    norm_num [activeHazard, secondPolynomial, thirdActiveEquation]
    ring
  · change (1 - (1 - (0 : ℝ)) * continueMassExcl (activeHazard point) 2) *
        pureQuitEndpointRowSum reward (activeHazard point) 2 -
        excludedEndpointRowSum reward (activeHazard point) 2 = _
    rw [active_quit_2, active_excluded_2]
    unfold continueMassExcl
    rw [show (Finset.univ : Finset (Fin 4)).erase 2 = {0, 1, 3} by decide]
    have hsurvival :
        (∏ other ∈ ({0, 1, 3} : Finset (Fin 4)), (1 - activeHazard point other)) =
          (1 - point 0) * (1 - point 1) := by
      norm_num [activeHazard]
    rw [hsurvival]
    change (1 - (1 - (0 : ℝ)) * ((1 - point 0) * (1 - point 1))) *
        (1 - 2 * point 0 - 2 * point 1 + 3 * point 0 * point 1) -
        3 * point 0 * point 1 = thirdActiveEquation (point 0) (point 1)
    unfold thirdActiveEquation
    ring

def firstJacobianFactor (x : ℝ) : ℝ := 6 * x ^ 3 - 15 * x ^ 2 + 12 * x - 1

def secondJacobianFactor (x y : ℝ) : ℝ :=
  8 * x ^ 2 * y - 5 * x ^ 2 - 8 * x * y + 3 * x + 1

def thirdJacobianFactor (x y : ℝ) : ℝ :=
  8 * x * y ^ 2 - 10 * x * y + 2 * x - 4 * y ^ 2 + 3 * y - 3

def activeJacobian (x y : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0, thirdJacobianFactor x y, secondJacobianFactor x y;
     thirdJacobianFactor x y, 0, secondJacobianFactor x y;
     -firstJacobianFactor x, -firstJacobianFactor x, 0]

def activeJacobianMap (x y : ℝ) : (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ) :=
  (activeJacobian x y).toLin'.toContinuousLinearMap

private theorem secondEquation_hasFDerivAt
    (first second : Fin 3) (point : Fin 3 → ℝ) :
    HasFDerivAt (𝕜 := ℝ)
      (fun source : Fin 3 → ℝ => secondPolynomial (source first) (source second))
      (thirdJacobianFactor (point first) (point second) •
          (ContinuousLinearMap.proj first : (Fin 3 → ℝ) →L[ℝ] ℝ) +
        secondJacobianFactor (point first) (point second) •
          (ContinuousLinearMap.proj second : (Fin 3 → ℝ) →L[ℝ] ℝ))
      point := by
  have hfirst := hasFDerivAt_apply (𝕜 := ℝ) first point
  have hsecond := hasFDerivAt_apply (𝕜 := ℝ) second point
  have hquartic := ((hfirst.pow 2).const_mul 4).mul (hsecond.pow 2)
  have hquadraticLinear := ((hfirst.pow 2).const_mul 5).mul hsecond
  have hlinearQuadratic := (hfirst.const_mul 4).mul (hsecond.pow 2)
  have hbilinear := (hfirst.const_mul 3).mul hsecond
  have hsquare := (hquartic.sub hquadraticLinear).add (hfirst.pow 2)
  have hderivative :=
    (((hsquare.sub hlinearQuadratic).add hbilinear).sub (hfirst.const_mul 3)).add hsecond
  unfold secondPolynomial
  convert hderivative using 1
  ext direction
  simp [secondJacobianFactor, thirdJacobianFactor]
  ring

private theorem thirdEquation_hasFDerivAt (x y : ℝ) :
    HasFDerivAt (𝕜 := ℝ)
      (fun source : Fin 3 → ℝ => thirdActiveEquation (source 0) (source 1))
      (-firstJacobianFactor x •
          (ContinuousLinearMap.proj (0 : Fin 3) : (Fin 3 → ℝ) →L[ℝ] ℝ) +
        -firstJacobianFactor x •
          (ContinuousLinearMap.proj (1 : Fin 3) : (Fin 3 → ℝ) →L[ℝ] ℝ)) ![x, x, y] := by
  have hfirst := hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 3) (![x, x, y] : Fin 3 → ℝ)
  have hsecond := hasFDerivAt_apply (𝕜 := ℝ) (1 : Fin 3) (![x, x, y] : Fin 3 → ℝ)
  have hsum := (hfirst.add hsecond).sub (hfirst.mul hsecond)
  have hterm := (((hasFDerivAt_const (1 : ℝ) (![x, x, y] : Fin 3 → ℝ)).sub
    (hfirst.const_mul 2)).sub (hsecond.const_mul 2)).add
    ((hfirst.mul hsecond).const_mul 3)
  have hderivative := (hsum.mul hterm).sub ((hfirst.mul hsecond).const_mul 3)
  have hnormalized := hderivative.congr_of_eventuallyEq
    (f₁ := fun source : Fin 3 → ℝ => thirdActiveEquation (source 0) (source 1))
    (Filter.Eventually.of_forall (fun source => by
      simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply]
      unfold thirdActiveEquation
      ring))
  refine hnormalized.congr_fderiv ?_
  ext direction
  simp [firstJacobianFactor]
  ring

/-- Actual derivative of the original response, with no symmetry restriction on directions. -/
theorem activeResponse_hasFDerivAt (x y : ℝ) :
    HasFDerivAt (activeResponse reward) (activeJacobianMap x y) ![x, x, y] := by
  have hsource : activeResponse reward =
      fun point : Fin 3 → ℝ =>
        ![secondPolynomial (point 1) (point 2), secondPolynomial (point 0) (point 2),
          thirdActiveEquation (point 0) (point 1)] := funext activeResponse_eq
  rw [hsource]
  apply hasFDerivAt_pi'.mpr
  intro coordinate
  fin_cases coordinate
  · have hmap :
        (ContinuousLinearMap.proj (0 : Fin 3) : (Fin 3 → ℝ) →L[ℝ] ℝ) ∘L
            activeJacobianMap x y =
          thirdJacobianFactor x y •
              (ContinuousLinearMap.proj (1 : Fin 3) : (Fin 3 → ℝ) →L[ℝ] ℝ) +
            secondJacobianFactor x y •
              (ContinuousLinearMap.proj (2 : Fin 3) : (Fin 3 → ℝ) →L[ℝ] ℝ) := by
      ext direction
      simp [activeJacobianMap, activeJacobian, Matrix.toLin'_apply,
        dotProduct, Fin.sum_univ_succ]
    exact (secondEquation_hasFDerivAt 1 2 (![x, x, y] : Fin 3 → ℝ)).congr_fderiv
      hmap.symm
  · have hmap :
        (ContinuousLinearMap.proj (1 : Fin 3) : (Fin 3 → ℝ) →L[ℝ] ℝ) ∘L
            activeJacobianMap x y =
          thirdJacobianFactor x y •
              (ContinuousLinearMap.proj (0 : Fin 3) : (Fin 3 → ℝ) →L[ℝ] ℝ) +
            secondJacobianFactor x y •
              (ContinuousLinearMap.proj (2 : Fin 3) : (Fin 3 → ℝ) →L[ℝ] ℝ) := by
      ext direction
      simp [activeJacobianMap, activeJacobian, Matrix.toLin'_apply,
        dotProduct, Fin.sum_univ_succ]
    exact (secondEquation_hasFDerivAt 0 2 (![x, x, y] : Fin 3 → ℝ)).congr_fderiv
      hmap.symm
  · have hmap :
        (ContinuousLinearMap.proj (2 : Fin 3) : (Fin 3 → ℝ) →L[ℝ] ℝ) ∘L
            activeJacobianMap x y =
          -firstJacobianFactor x •
              (ContinuousLinearMap.proj (0 : Fin 3) : (Fin 3 → ℝ) →L[ℝ] ℝ) +
            -firstJacobianFactor x •
              (ContinuousLinearMap.proj (1 : Fin 3) : (Fin 3 → ℝ) →L[ℝ] ℝ) := by
      ext direction
      simp [activeJacobianMap, activeJacobian, Matrix.toLin'_apply,
        dotProduct, Fin.sum_univ_succ]
    exact (thirdEquation_hasFDerivAt x y).congr_fderiv hmap.symm

theorem activeJacobian_det (x y : ℝ) :
    (activeJacobian x y).det =
      -2 * firstJacobianFactor x * secondJacobianFactor x y * thirdJacobianFactor x y := by
  norm_num [activeJacobian, Matrix.det_fin_three, Matrix.of_apply]
  ring

theorem activeJacobianFactors_sign {x y : ℝ}
    (hx : x ∈ Set.Ioo (197 / 1000 : ℝ) (1 / 5))
    (hy : y ∈ Set.Ioo (1 / 2 : ℝ) (3 / 5)) :
    0 < firstJacobianFactor x ∧ 0 < secondJacobianFactor x y ∧
      thirdJacobianFactor x y < 0 := by
  have hx0 : 0 ≤ x := by linarith [hx.1]
  have hy0 : 0 ≤ y := by linarith [hy.1]
  have hxUpper : x ≤ 1 / 5 := hx.2.le
  have hyUpper : y ≤ 3 / 5 := hy.2.le
  have hxsq : x ^ 2 ≤ (1 / 5 : ℝ) ^ 2 := by
    nlinarith [mul_nonneg (show 0 ≤ 1 / 5 - x by linarith)
      (show 0 ≤ 1 / 5 + x by linarith)]
  have hproduct : x * (1 - x) ≤ (4 / 25 : ℝ) := by
    nlinarith [mul_nonneg (show 0 ≤ 1 / 5 - x by linarith)
      (show 0 ≤ 4 / 5 - x by linarith)]
  have hproductY : x * (1 - x) * y ≤ (4 / 25 : ℝ) * (3 / 5) :=
    mul_le_mul hproduct hyUpper hy0 (by norm_num)
  have hxySquare : x * y ^ 2 ≤ (1 / 5 : ℝ) * (3 / 5) ^ 2 := by
    gcongr
  have hfirst : 0 < firstJacobianFactor x := by
    unfold firstJacobianFactor
    nlinarith [pow_nonneg hx0 3, hx.1]
  have hsecond : 0 < secondJacobianFactor x y := by
    unfold secondJacobianFactor
    nlinarith [hx.1]
  have hthird : thirdJacobianFactor x y < 0 := by
    unfold thirdJacobianFactor
    nlinarith [mul_nonneg hx0 hy0, sq_nonneg y]
  exact ⟨hfirst, hsecond, hthird⟩

theorem activeJacobian_det_ne_zero {x y : ℝ}
    (hx : x ∈ Set.Ioo (197 / 1000 : ℝ) (1 / 5))
    (hy : y ∈ Set.Ioo (1 / 2 : ℝ) (3 / 5)) :
    (activeJacobian x y).det ≠ 0 := by
  obtain ⟨hfirst, hsecond, hthird⟩ := activeJacobianFactors_sign hx hy
  rw [activeJacobian_det]
  exact mul_ne_zero
    (mul_ne_zero (mul_ne_zero (by norm_num) hfirst.ne') hsecond.ne') hthird.ne

def activeBase : Fin 3 → ℝ := ![firstRoot, firstRoot, secondRoot]

theorem activeBase_response_zero : activeResponse reward activeBase = 0 := by
  rw [activeResponse_eq]
  ext coordinate
  fin_cases coordinate
  · exact secondRoot_spec.2
  · exact secondRoot_spec.2
  · change thirdActiveEquation firstRoot firstRoot = 0
    have hidentity : thirdActiveEquation firstRoot firstRoot =
        -firstRoot * firstPolynomial firstRoot := by
      unfold thirdActiveEquation firstPolynomial
      ring
    simp only [hidentity, firstRoot_spec.2, mul_zero]

theorem activeBase_derivative :
    fderiv ℝ (activeResponse reward) activeBase =
      activeJacobianMap firstRoot secondRoot :=
  (activeResponse_hasFDerivAt firstRoot secondRoot).fderiv

/-- Invertibility is internally proved from the actual Jacobian and rational brackets. -/
theorem activeBase_derivative_invertible :
    (fderiv ℝ (activeResponse reward) activeBase).IsInvertible := by
  rw [activeBase_derivative]
  let inverse : (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ) :=
    ((activeJacobian firstRoot secondRoot)⁻¹).toLin'.toContinuousLinearMap
  have hdet : IsUnit (activeJacobian firstRoot secondRoot).det :=
    isUnit_iff_ne_zero.mpr
      (activeJacobian_det_ne_zero firstRoot_spec.1 secondRoot_spec.1)
  apply ContinuousLinearMap.IsInvertible.of_inverse (g := inverse)
  · ext direction coordinate
    change ((activeJacobian firstRoot secondRoot).mulVec
      ((activeJacobian firstRoot secondRoot)⁻¹.mulVec direction)) coordinate =
        direction coordinate
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
  · ext direction coordinate
    change ((activeJacobian firstRoot secondRoot)⁻¹.mulVec
      ((activeJacobian firstRoot secondRoot).mulVec direction)) coordinate =
        direction coordinate
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mulVec]

end GameTheory.PairedCubicStationaryExample
