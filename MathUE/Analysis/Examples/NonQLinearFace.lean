import MathUE.LinearProgramming.CopositiveQ
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Convex.Function

/-! # The printed convex positive-face-drift fixture without standard Q -/

noncomputable section

namespace Math.NonQLinearFace

open Set Math.LinearProgramming
open scoped BigOperators Matrix

def matrix : Matrix (Fin 2) (Fin 2) ℝ := !![0, -1; -1, 0]

def potential (point : Fin 2 → ℝ) : ℝ := point 0 + point 1

theorem potential_hasFDerivAt (point : Fin 2 → ℝ) :
    HasFDerivAt potential
      ((ContinuousLinearMap.proj 0 : (Fin 2 → ℝ) →L[ℝ] ℝ) + ContinuousLinearMap.proj 1)
      point :=
  ((ContinuousLinearMap.proj 0 : (Fin 2 → ℝ) →L[ℝ] ℝ).hasFDerivAt).add
    (ContinuousLinearMap.proj 1 : (Fin 2 → ℝ) →L[ℝ] ℝ).hasFDerivAt

theorem convexOn (domain : Set (Fin 2 → ℝ)) (hdomain : Convex ℝ domain) :
    ConvexOn ℝ domain potential := by
  refine ⟨hdomain, ?_⟩
  intro first _ second _ a b _ _ _
  apply le_of_eq
  simp only [potential, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem face_drift (point : Fin 2 → ℝ) (owner : Fin 2) (hface : point owner = 0) :
    fderiv ℝ potential point (fun who => point who - matrix who owner) =
      1 + point (1 - owner) := by
  rw [(potential_hasFDerivAt point).fderiv]
  fin_cases owner
  · change point 0 = 0 at hface
    simp [matrix, hface, add_comm]
  · change point 1 = 0 at hface
    simp [matrix, hface, add_comm]

theorem face_drift_ge_one (point : Fin 2 → ℝ)
    (hpoint : point ∈ Icc (0 : Fin 2 → ℝ) 1) (owner : Fin 2) (hface : point owner = 0) :
    1 ≤ fderiv ℝ potential point (fun who => point who - matrix who owner) := by
  rw [face_drift point owner hface]
  have hnonnegative : 0 ≤ point (1 - owner) := hpoint.1 (1 - owner)
  linarith

/-- The actual standard residual at RHS -1 is negative for every nonnegative weight. -/
theorem negative_residual (weight : Fin 2 → ℝ) (hnonnegative : ∀ who, 0 ≤ weight who)
    (who : Fin 2) : lcpResidual matrix (fun _ => -1) weight who < 0 := by
  fin_cases who <;> simp [lcpResidual, matrix, Fin.sum_univ_succ] <;>
    linarith [hnonnegative 0, hnonnegative 1]

theorem not_standardQ : ¬IsStandardQ matrix := by
  intro hQ
  obtain ⟨weight, hsolution⟩ := hQ (fun _ => -1)
  exact not_lt_of_ge (hsolution.residual_nonneg 0)
    (negative_residual weight hsolution.weight_nonneg 0)

end Math.NonQLinearFace
