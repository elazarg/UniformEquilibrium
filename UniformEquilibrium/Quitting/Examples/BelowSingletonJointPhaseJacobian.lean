import UniformEquilibrium.Quitting.Examples.BelowSingletonJointPhaseFixture
import UniformEquilibrium.Quitting.Cycles.TwoPairOddsValues
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! # The actual four-odds Jacobian of the below-singleton fixture

All four odds coordinates vary independently. The response is the literal
passive Continue deficit equation of the complete reward table, rather than a
restriction to equal odds or a three-active-coordinate system.
-/

noncomputable section

namespace GameTheory.BelowSingletonJointPhaseFixture

open PairedCycle Math.CrossedMatching

def oddsResponse (table : TwoPairOdds.Reward) (point : Fin 4 → ℝ) : Fin 4 → ℝ :=
  passiveEquation (quittingProjectiveLCPMatrix table)
    (TwoPairOdds.premium table) (TwoPairOdds.passive table) point

def baseOdds : Fin 4 → ℝ := fun _ => 1 / 2

def fixtureOddsEquation (player : Fin 4) (point : Fin 4 → ℝ) : ℝ :=
  -(1 / 10 : ℝ) * point (scheduled player) *
      (1 + point (favorite player)) * (1 + point (other player)) -
    3 * point (favorite player) + point (other player) +
    (179 / 60 : ℝ) * point (favorite player) * point (other player) +
    (11 / 10 : ℝ) * point (scheduled player) / (1 + point (scheduled player))

theorem oddsResponse_eq (point : Fin 4 → ℝ) (player : Fin 4) :
    oddsResponse reward point player = fixtureOddsEquation player point := by
  have hp : TwoPairOdds.premium reward player = -11 / 10 := by
    unfold TwoPairOdds.premium
    rw [rawFamily.active_pair, singleton_eq]
    norm_num
  have hk : TwoPairOdds.passive reward player = -179 / 60 := by
    unfold TwoPairOdds.passive
    rw [rawFamily.passive_pair, singleton_eq]
    norm_num
  have hf : quittingProjectiveLCPMatrix reward player (favorite player) = 3 := by
    rw [TwoPairOdds.matrix_entry, rawFamily.favorite_singleton, singleton_eq]
    norm_num
  have ha : quittingProjectiveLCPMatrix reward player (scheduled player) = -1 := by
    rw [TwoPairOdds.matrix_entry, rawFamily.scheduled_singleton, singleton_eq]
    norm_num
  have ho : quittingProjectiveLCPMatrix reward player (other player) = -1 := by
    rw [TwoPairOdds.matrix_entry, rawFamily.other_singleton, singleton_eq]
    norm_num
  unfold oddsResponse passiveEquation
  rw [hp, hk, hf, ha, ho]
  unfold fixtureOddsEquation
  ring

theorem baseOdds_response_zero : oddsResponse reward baseOdds = 0 := by
  ext player
  rw [oddsResponse_eq]
  norm_num [fixtureOddsEquation, baseOdds]

def oddsJacobian : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0, -19 / 12, 19 / 72, 29 / 12;
    -19 / 12, 0, 29 / 12, 19 / 72;
    19 / 72, 29 / 12, 0, -19 / 12;
    29 / 12, 19 / 72, -19 / 12, 0]

def oddsJacobianMap : (Fin 4 → ℝ) →L[ℝ] (Fin 4 → ℝ) :=
  oddsJacobian.toLin'.toContinuousLinearMap

private theorem fixtureOddsEquation_hasFDerivAt (player : Fin 4) :
    HasFDerivAt (𝕜 := ℝ) (fixtureOddsEquation player)
      (-(19 / 12 : ℝ) •
          (ContinuousLinearMap.proj (favorite player) : (Fin 4 → ℝ) →L[ℝ] ℝ) +
        (19 / 72 : ℝ) • ContinuousLinearMap.proj (scheduled player) +
        (29 / 12 : ℝ) • ContinuousLinearMap.proj (other player)) baseOdds := by
  have hf := hasFDerivAt_apply (𝕜 := ℝ) (favorite player) baseOdds
  have ha := hasFDerivAt_apply (𝕜 := ℝ) (scheduled player) baseOdds
  have ho := hasFDerivAt_apply (𝕜 := ℝ) (other player) baseOdds
  have hone := hasFDerivAt_const (𝕜 := ℝ) (1 : ℝ) baseOdds
  have hquotient : HasDerivAt (fun x : ℝ => x / (1 + x)) (4 / 9 : ℝ) (1 / 2) := by
    convert (hasDerivAt_id (1 / 2 : ℝ)).div
      ((hasDerivAt_const (1 / 2 : ℝ) (1 : ℝ)).add (hasDerivAt_id (1 / 2 : ℝ)))
      (by norm_num) using 1
    · rfl
    · norm_num
  have hratio := hquotient.comp_hasFDerivAt_of_eq baseOdds ha (by rfl)
  have hproduct := (((ha.const_mul (-(1 / 10 : ℝ))).mul (hone.add hf)).mul
    (hone.add ho))
  have hresult := (((hproduct.sub (hf.const_mul 3)).add ho).add
    ((hf.const_mul (179 / 60 : ℝ)).mul ho)).add (hratio.const_mul (11 / 10 : ℝ))
  unfold fixtureOddsEquation
  convert hresult using 1
  · funext point
    simp only [Function.comp_def, Pi.add_apply, Pi.sub_apply, Pi.mul_apply]
    ring
  · ext direction
    simp [baseOdds]
    ring

/-- The derivative acts on every independent real odds direction. -/
theorem oddsResponse_hasFDerivAt :
    HasFDerivAt (oddsResponse reward) oddsJacobianMap baseOdds := by
  have hsource : oddsResponse reward = fun point player => fixtureOddsEquation player point := by
    funext point player
    exact oddsResponse_eq point player
  rw [hsource]
  apply hasFDerivAt_pi'.mpr
  intro player
  have hmap :
      (ContinuousLinearMap.proj player : (Fin 4 → ℝ) →L[ℝ] ℝ) ∘L oddsJacobianMap =
        -(19 / 12 : ℝ) • ContinuousLinearMap.proj (favorite player) +
          (19 / 72 : ℝ) • ContinuousLinearMap.proj (scheduled player) +
          (29 / 12 : ℝ) • ContinuousLinearMap.proj (other player) := by
    ext direction
    fin_cases player <;>
      simp [oddsJacobianMap, oddsJacobian, Matrix.toLin'_apply, dotProduct,
        Fin.sum_univ_succ, favorite, scheduled, other] <;> ring
  exact (fixtureOddsEquation_hasFDerivAt player).congr_fderiv hmap.symm

theorem oddsJacobian_det : oddsJacobian.det = 267486337 / 26873856 := by
  rw [Matrix.det_succ_row_zero]
  norm_num [oddsJacobian, Fin.sum_univ_succ, Matrix.det_fin_three,
    Matrix.submatrix_apply, Fin.succAbove]

theorem baseOdds_derivative :
    fderiv ℝ (oddsResponse reward) baseOdds = oddsJacobianMap :=
  oddsResponse_hasFDerivAt.fderiv

/-- Nonsingularity follows from the actual rational four-coordinate determinant. -/
theorem baseOdds_derivative_invertible :
    (fderiv ℝ (oddsResponse reward) baseOdds).IsInvertible := by
  rw [baseOdds_derivative]
  let inverse : (Fin 4 → ℝ) →L[ℝ] (Fin 4 → ℝ) :=
    (oddsJacobian⁻¹).toLin'.toContinuousLinearMap
  have hdet : IsUnit oddsJacobian.det := by
    rw [oddsJacobian_det]
    norm_num
  apply ContinuousLinearMap.IsInvertible.of_inverse (g := inverse)
  · ext direction coordinate
    change (oddsJacobian.mulVec (oddsJacobian⁻¹.mulVec direction)) coordinate =
      direction coordinate
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
  · ext direction coordinate
    change (oddsJacobian⁻¹.mulVec (oddsJacobian.mulVec direction)) coordinate =
      direction coordinate
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mulVec]

end GameTheory.BelowSingletonJointPhaseFixture
