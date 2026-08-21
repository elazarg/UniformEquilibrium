/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Order.Compact

/-!
# Uniform lower bounds for bounded nonsingular matrices

A compact family of square real matrices whose determinants stay away from
zero has one common lower Lipschitz bound.  Entrywise bounds provide the
compact family used here.
-/

noncomputable section

open Set
open Filter

namespace Math.LinearAlgebra

/-- The square matrix with zero diagonal and every off-diagonal entry equal
to one. -/
def offDiagonalOnes (n : Type) [DecidableEq n] : Matrix n n ℝ :=
  fun i j => if i = j then 0 else 1

/-- Multiplication by the off-diagonal-ones matrix subtracts the selected
coordinate from the sum of all coordinates. -/
theorem offDiagonalOnes_mulVec_apply {n : Type} [Fintype n] [DecidableEq n]
    (v : n → ℝ) (i : n) :
    Matrix.mulVec (offDiagonalOnes n) v i = ∑ j, v j - v i := by
  rw [Matrix.mulVec, dotProduct]
  simp only [offDiagonalOnes, ite_mul, zero_mul, one_mul]
  calc
    (∑ j, if i = j then 0 else v j) =
        (∑ j ∈ Finset.univ.erase i, if i = j then 0 else v j) := by
      rw [Finset.sum_subset (Finset.erase_subset _ _)]
      intro j _ hj
      have hji : j = i := by
        simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hj
        exact not_ne_iff.mp hj
      subst j
      simp
    _ = (∑ j ∈ Finset.univ.erase i, v j) := by
      apply Finset.sum_congr rfl
      intro j hj
      have hji : j ≠ i := Finset.ne_of_mem_erase hj
      simp [Ne.symm hji]
    _ = (∑ j, v j) - v i := by
      rw [← Finset.sum_erase_add Finset.univ v (Finset.mem_univ i)]
      ring

/-- For at least two coordinates, the off-diagonal-ones matrix is
nonsingular. -/
theorem offDiagonalOnes_det_ne_zero {n : Type} [Fintype n] [DecidableEq n]
    (hcard : 2 ≤ Fintype.card n) : (offDiagonalOnes n).det ≠ 0 := by
  have hinjective : Function.Injective (offDiagonalOnes n).mulVec := by
    intro v w hvw
    have hcoord (i : n) : (∑ j, v j) - v i = (∑ j, w j) - w i := by
      simpa only [offDiagonalOnes_mulVec_apply] using congr_fun hvw i
    let d : n → ℝ := v - w
    have hd (i : n) : d i = ∑ j, d j := by
      dsimp only [d]
      simp only [Pi.sub_apply, Finset.sum_sub_distrib]
      linarith [hcoord i]
    have hsum : ∑ j, d j = 0 := by
      have htotal : ∑ i, d i = (Fintype.card n : ℝ) * ∑ j, d j := by
        calc
          ∑ i, d i = ∑ _i : n, ∑ j, d j := Finset.sum_congr rfl fun i _ => hd i
          _ = (Fintype.card n : ℝ) * ∑ j, d j := by simp
      have hcardReal : 2 ≤ (Fintype.card n : ℝ) := by exact_mod_cast hcard
      nlinarith [htotal]
    funext i
    have hi := hd i
    dsimp only [d] at hi
    rw [hsum] at hi
    exact sub_eq_zero.mp hi
  have hunit : IsUnit (offDiagonalOnes n) :=
    Matrix.mulVec_injective_iff_isUnit.mp hinjective
  exact isUnit_iff_ne_zero.mp
    ((Matrix.isUnit_iff_isUnit_det (offDiagonalOnes n)).mp hunit)

/-- The determinant polynomial obtained by subtracting a common scalar from
every off-diagonal entry of a square matrix. -/
def offDiagonalPerturbationPolynomial {n : Type} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) : Polynomial ℝ :=
  Matrix.det ((Polynomial.X : Polynomial ℝ) •
    (-offDiagonalOnes n).map Polynomial.C + A.map Polynomial.C)

/-- The off-diagonal perturbation polynomial is nonzero as soon as its index
type has at least two elements. -/
theorem offDiagonalPerturbationPolynomial_ne_zero
    {n : Type} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (hcard : 2 ≤ Fintype.card n) :
    offDiagonalPerturbationPolynomial A ≠ 0 := by
  intro hzero
  have hcoeff := congrArg
    (fun p : Polynomial ℝ => p.coeff (Fintype.card n)) hzero
  rw [offDiagonalPerturbationPolynomial,
    Polynomial.coeff_det_X_add_C_card] at hcoeff
  simp only [Polynomial.coeff_zero] at hcoeff
  apply offDiagonalOnes_det_ne_zero hcard
  simpa only [Matrix.det_neg, mul_eq_zero, pow_eq_zero_iff', neg_eq_zero,
    one_ne_zero, false_and, false_or] using hcoeff

/-- Evaluating the determinant polynomial gives the corresponding common
off-diagonal perturbation. -/
theorem offDiagonalPerturbationPolynomial_eval
    {n : Type} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (x : ℝ) :
    (offDiagonalPerturbationPolynomial A).eval x =
      (A - x • offDiagonalOnes n).det := by
  rw [offDiagonalPerturbationPolynomial]
  change (Polynomial.evalRingHom x)
    (Matrix.det ((Polynomial.X : Polynomial ℝ) •
      (-offDiagonalOnes n).map Polynomial.C + A.map Polynomial.C)) = _
  rw [RingHom.map_det]
  rw [RingHom.mapMatrix_apply]
  congr 1
  ext i j
  change Polynomial.eval₂ (RingHom.id ℝ) x
      (Polynomial.X * Polynomial.C (-offDiagonalOnes n i j) +
        Polynomial.C (A i j)) = A i j - x * offDiagonalOnes n i j
  rw [Polynomial.eval₂_add, Polynomial.eval₂_mul,
    Polynomial.eval₂_X, Polynomial.eval₂_C, Polynomial.eval₂_C]
  simp only [RingHom.id_apply]
  ring

/-- Finitely many nonzero real polynomials admit one arbitrarily small
positive common non-root. -/
theorem exists_pos_lt_forall_polynomial_eval_ne_zero
    {k : Type} [Fintype k] (p : k → Polynomial ℝ)
    (hp : ∀ i, p i ≠ 0) {tol : ℝ} (htol : 0 < tol) :
    ∃ x : ℝ, 0 < x ∧ x < tol ∧ ∀ i, (p i).eval x ≠ 0 := by
  classical
  let roots : Finset ℝ :=
    Finset.univ.biUnion fun i => (p i).roots.toFinset
  obtain ⟨x, hxIoo, hxroots⟩ :=
    ((Set.Ioo_infinite htol).sdiff roots.finite_toSet).nonempty
  refine ⟨x, hxIoo.1, hxIoo.2, ?_⟩
  intro i heval
  apply hxroots
  change x ∈ roots
  exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i,
    Multiset.mem_toFinset.mpr <|
      (Polynomial.mem_roots (hp i)).mpr (Polynomial.IsRoot.def.mpr heval)⟩

/-- A nonsingular real matrix remains uniformly separated from singularity
under sufficiently small entrywise perturbations. -/
theorem exists_entrywise_perturbation_radius_det_lower_bound
    {n : Type} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (hdet : A.det ≠ 0) :
    ∃ η : ℝ, 0 < η ∧ ∀ d : Matrix n n ℝ,
      (∀ i j, |d i j| ≤ η) → |A.det| / 2 < |(A + d).det| := by
  by_contra hη
  push Not at hη
  have hchoice (k : ℕ) :
      ∃ d : Matrix n n ℝ,
        (∀ i j, |d i j| ≤ ((k : ℝ) + 1)⁻¹) ∧
          |(A + d).det| ≤ |A.det| / 2 := by
    exact hη (((k : ℝ) + 1)⁻¹) (by positivity)
  choose d hd hbad using hchoice
  have hscale : Tendsto (fun k : ℕ => ((k : ℝ) + 1)⁻¹)
      atTop (nhds 0) := by
    simpa only [one_div] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hdTendsto : Tendsto d atTop (nhds 0) := by
    apply tendsto_pi_nhds.2
    intro i
    apply tendsto_pi_nhds.2
    intro j
    have hcoordinate : Tendsto (fun k => d k i j) atTop (nhds 0) :=
      (tendsto_zero_iff_abs_tendsto_zero _).2 <|
        squeeze_zero (fun k => abs_nonneg (d k i j))
          (fun k => hd k i j) hscale
    convert hcoordinate using 1
    simp
  have hsumTendsto : Tendsto (fun k => A + d k) atTop (nhds A) := by
    simpa only [add_zero] using tendsto_const_nhds.add hdTendsto
  have hdetTendsto :
      Tendsto (fun k => |(A + d k).det|) atTop (nhds |A.det|) :=
    (continuous_abs.comp continuous_id.matrix_det).continuousAt.tendsto.comp
      hsumTendsto
  have hlimit : |A.det| ≤ |A.det| / 2 :=
    isClosed_Iic.mem_of_tendsto hdetTendsto
      (Filter.Eventually.of_forall hbad)
  have hpositive : 0 < |A.det| := abs_pos.mpr hdet
  linarith

open scoped Matrix.Norms.L2Operator

/-- Bounded entries and a determinant separated from zero give one common
lower Euclidean bound for matrix-vector multiplication. -/
theorem exists_uniform_mulVec_lower_bound_of_entry_det_bounds
    {n : Type} [Fintype n] [DecidableEq n]
    {B ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ A : Matrix n n ℝ,
      (∀ i j, |A i j| ≤ B) → ε ≤ |A.det| →
      ∀ v : n → ℝ,
        δ * ‖WithLp.toLp 2 v‖ ≤
          ‖WithLp.toLp 2 (Matrix.mulVec A v)‖ := by
  classical
  let box : Set (Matrix n n ℝ) :=
    Set.univ.pi fun _ => Set.univ.pi fun _ => Set.Icc (-B) B
  let family : Set (Matrix n n ℝ) :=
    box ∩ {A | ε ≤ |A.det|}
  have hbox : IsCompact box := by
    exact isCompact_univ_pi fun _ =>
      isCompact_univ_pi fun _ => isCompact_Icc
  have hdetClosed : IsClosed {A : Matrix n n ℝ | ε ≤ |A.det|} := by
    exact isClosed_Ici.preimage (continuous_abs.comp continuous_id.matrix_det)
  have hfamily : IsCompact family := hbox.inter_right hdetClosed
  by_cases hnonempty : family.Nonempty
  · have hinverse : ContinuousOn (fun A : Matrix n n ℝ => ‖A⁻¹‖) family := by
      intro A hA
      have hdet : A.det ≠ 0 := by
        have habs : ε ≤ |A.det| := hA.2
        exact abs_pos.mp (hε.trans_le habs)
      have hinv : ContinuousAt Ring.inverse A.det := by
        simpa only [Ring.inverse_eq_inv'] using continuousAt_inv₀ hdet
      exact (continuousAt_matrix_inv A hinv).norm.continuousWithinAt
    obtain ⟨Amax, hAmax, hmax⟩ :=
      hfamily.exists_isMaxOn hnonempty hinverse
    let C : ℝ := ‖Amax⁻¹‖
    let δ : ℝ := 1 / (C + 1)
    have hC : 0 ≤ C := norm_nonneg _
    have hδ : 0 < δ := by
      exact one_div_pos.mpr (by linarith)
    refine ⟨δ, hδ, ?_⟩
    intro A hentries hdetLower v
    have hAbox : A ∈ box := by
      intro i _ j _
      exact (abs_le.mp (hentries i j))
    have hAfamily : A ∈ family := ⟨hAbox, hdetLower⟩
    have hnormInv : ‖A⁻¹‖ ≤ C := hmax hAfamily
    have hdet : A.det ≠ 0 := by
      exact abs_pos.mp (hε.trans_le hdetLower)
    have hunit : IsUnit A.det := isUnit_iff_ne_zero.mpr hdet
    have hinverseBound :
        ‖WithLp.toLp 2 v‖ ≤
          ‖A⁻¹‖ * ‖WithLp.toLp 2 (Matrix.mulVec A v)‖ := by
      have hmul := A⁻¹.l2_opNorm_mulVec
        (WithLp.toLp 2 (Matrix.mulVec A v))
      have hrecover :
          Matrix.mulVec A⁻¹ (Matrix.mulVec A v) = v := by
        rw [Matrix.mulVec_mulVec, A.nonsing_inv_mul hunit, Matrix.one_mulVec]
      change ‖WithLp.toLp 2 (Matrix.mulVec A⁻¹ (Matrix.mulVec A v))‖ ≤
        ‖A⁻¹‖ * ‖WithLp.toLp 2 (Matrix.mulVec A v)‖ at hmul
      rwa [hrecover] at hmul
    have hbound :
        ‖WithLp.toLp 2 v‖ ≤
          C * ‖WithLp.toLp 2 (Matrix.mulVec A v)‖ := by
      exact hinverseBound.trans <|
        mul_le_mul_of_nonneg_right hnormInv (norm_nonneg _)
    have hδC : δ * C ≤ 1 := by
      dsimp only [δ]
      rw [one_div, inv_mul_eq_div]
      exact (div_le_one (by linarith)).mpr (by linarith)
    calc
      δ * ‖WithLp.toLp 2 v‖ ≤
          δ * (C * ‖WithLp.toLp 2 (Matrix.mulVec A v)‖) :=
        mul_le_mul_of_nonneg_left hbound hδ.le
      _ = (δ * C) * ‖WithLp.toLp 2 (Matrix.mulVec A v)‖ := by ring
      _ ≤ 1 * ‖WithLp.toLp 2 (Matrix.mulVec A v)‖ :=
        mul_le_mul_of_nonneg_right hδC (norm_nonneg _)
      _ = ‖WithLp.toLp 2 (Matrix.mulVec A v)‖ := one_mul _
  · refine ⟨1, zero_lt_one, ?_⟩
    intro A hentries hdetLower
    exfalso
    apply hnonempty
    refine ⟨A, ?_, hdetLower⟩
    intro i _ j _
    exact abs_le.mp (hentries i j)

end Math.LinearAlgebra
