import MathUE.LinearProgramming.Examples.NegativeDegreeFourMatrix
import MathUE.LinearProgramming.SupportTestStability

/-!
# An open neighborhood with the same negative-degree support inventory

Every sufficiently close zero-diagonal matrix retains full R0, degree minus
one, and exactly the same three admissible supports at the fixed positive
test anchor. The roots themselves are the continuously varying principal
inverse candidates, not the original rational vectors.
-/

noncomputable section

open Filter
open scoped Topology

namespace Math.LinearProgramming.NegativeDegreeFourMatrix

/-- Every displayed row is its canonical inverse-principal candidate,
including the rows rejected by the sign tests. -/
theorem principalInverseCandidate_support_eq (row : Fin 11) :
    principalInverseCandidate matrix anchor (support row) = candidate row := by
  apply principalInverseCandidate_eq_of_supported_linear_system matrix anchor (support row)
    (principal_det_ne_zero row) (candidate row) (candidate_zero_off_support row)
  intro who hwho
  rw [residual_eq]
  exact residual_zero_on_support row who hwho

theorem principal_nonsingular (selected : Finset (Fin 4)) (hcard : 2 ≤ selected.card) :
    (matrix.toSquareBlockProp (fun who => who ∈ selected)).det ≠ 0 := by
  obtain ⟨row, rfl⟩ := support_complete selected hcard
  exact principal_det_ne_zero row

/-- All accepted rows are strict, and each rejected row has a strict
negative coordinate or a strict negative inactive residual. -/
theorem strict_support_inventory : HasStrictLCPSupportInventory matrix anchor := by
  intro selected hcard
  obtain ⟨row, rfl⟩ := support_complete selected hcard
  rw [principalInverseCandidate_support_eq, residual_eq]
  fin_cases row <;>
    norm_num [support, candidate, residual, Fin.forall_fin_succ, Fin.exists_fin_succ]

theorem support_mem_admissible_iff (row : Fin 11) :
    support row ∈ admissibleLCPSupports matrix anchor (principalInverseCandidate matrix anchor) ↔
      row = 6 ∨ row = 9 ∨ row = 10 := by
  rw [mem_admissibleLCPSupports_iff, principalInverseCandidate_support_eq, residual_eq]
  fin_cases row <;> norm_num [support, candidate, residual, Fin.forall_fin_succ]

/-- The exact support finset underlying the three-root calculation. -/
theorem admissible_supports_eq :
    admissibleLCPSupports matrix anchor (principalInverseCandidate matrix anchor) =
      {support 6, support 9, support 10} := by
  classical
  ext selected
  constructor
  · intro hmem
    obtain ⟨row, rfl⟩ := support_complete selected
      ((mem_admissibleLCPSupports_iff _ _ _ _).mp hmem).1
    rcases (support_mem_admissible_iff row).mp hmem with rfl | rfl | rfl <;> simp
  · intro hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with rfl | rfl | rfl
    · exact (support_mem_admissible_iff 6).mpr (by simp)
    · exact (support_mem_admissible_iff 9).mpr (by simp)
    · exact (support_mem_admissible_iff 10).mpr (by simp)

/-- Literal neighborhood persistence of R0, degree minus one, and the entire
three-support root inventory. Only zero diagonal is required of nearby matrices. -/
theorem eventually_r0Degree_neg_one_and_three_supports :
    ∀ᶠ other : Matrix (Fin 4) (Fin 4) ℝ in 𝓝 matrix,
      (∀ who, other who who = 0) → ∃ hR0 : IsR0Matrix other,
        r0Degree other hR0 = -1 ∧
        admissibleLCPSupports other anchor (principalInverseCandidate other anchor) =
          {support 6, support 9, support 10} ∧
        ∀ root : Fin 4 → ℝ, IsStandardLCPSolution other (-anchor) root ↔
          root = principalInverseCandidate other anchor (support 6) ∨
          root = principalInverseCandidate other anchor (support 9) ∨
          root = principalInverseCandidate other anchor (support 10) := by
  filter_upwards [eventually_r0Degree_eq_of_strict_support_inventory matrix anchor
    diagonal_zero anchor_pos negative_columns principal_nonsingular strict_support_inventory,
    eventually_principal_nonsingular_and_sign_eq matrix principal_nonsingular]
    with other hother hprincipalOther
  intro hdiagonal
  obtain ⟨hR0, hsupports, hdegree⟩ := hother
  have hsupports' := hsupports.trans admissible_supports_eq
  refine ⟨hR0, (hdegree hdiagonal).trans r0Degree_eq_neg_one, hsupports', ?_⟩
  intro root
  rw [isStandardLCPSolution_iff_exists_admissible_inverse_support other anchor
    hdiagonal anchor_pos (fun selected hcard => (hprincipalOther selected hcard).1), hsupports']
  constructor
  · rintro ⟨selected, hselected, hequal⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hselected
    rcases hselected with rfl | rfl | rfl
    · exact Or.inl hequal
    · exact Or.inr (Or.inl hequal)
    · exact Or.inr (Or.inr hequal)
  · rintro (hequal | hequal | hequal)
    · exact ⟨support 6, by simp, hequal⟩
    · exact ⟨support 9, by simp, hequal⟩
    · exact ⟨support 10, by simp, hequal⟩

end Math.LinearProgramming.NegativeDegreeFourMatrix
