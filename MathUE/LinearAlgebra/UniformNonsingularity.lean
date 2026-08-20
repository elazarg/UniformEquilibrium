/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
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
open scoped Matrix.Norms.L2Operator

namespace Math.LinearAlgebra

/-- Bounded entries and a determinant separated from zero give one common
lower Euclidean bound for matrix-vector multiplication. -/
theorem exists_uniform_mulVec_lower_bound_of_entry_det_bounds
    {n : ℕ} {B ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ A : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, |A i j| ≤ B) → ε ≤ |A.det| →
      ∀ v : Fin n → ℝ,
        δ * ‖WithLp.toLp 2 v‖ ≤
          ‖WithLp.toLp 2 (Matrix.mulVec A v)‖ := by
  classical
  let box : Set (Matrix (Fin n) (Fin n) ℝ) :=
    Set.univ.pi fun _ => Set.univ.pi fun _ => Set.Icc (-B) B
  let family : Set (Matrix (Fin n) (Fin n) ℝ) :=
    box ∩ {A | ε ≤ |A.det|}
  have hbox : IsCompact box := by
    exact isCompact_univ_pi fun _ =>
      isCompact_univ_pi fun _ => isCompact_Icc
  have hdetClosed : IsClosed {A : Matrix (Fin n) (Fin n) ℝ | ε ≤ |A.det|} := by
    exact isClosed_Ici.preimage (continuous_abs.comp continuous_id.matrix_det)
  have hfamily : IsCompact family := hbox.inter_right hdetClosed
  by_cases hnonempty : family.Nonempty
  · have hinverse : ContinuousOn (fun A : Matrix (Fin n) (Fin n) ℝ => ‖A⁻¹‖) family := by
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
