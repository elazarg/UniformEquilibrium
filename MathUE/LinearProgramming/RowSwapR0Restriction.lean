import MathUE.LinearProgramming.CopositiveQ

/-! # A zero-diagonal R0 matrix remains R0 after one explicitly guarded row swap

Only the selected reciprocal entries are assumed positive; entries from
both selected rows to every outsider are strictly negative. No inverse,
determinant, standard-Q, or degree hypothesis replaces these premises.
-/

noncomputable section

namespace Math.LinearProgramming

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem selected_weight_pos_of_external_row
    (matrix : ι → ι → ℝ) (weight : ι → ℝ) (who partner outside : ι)
    (hweight : ∀ coordinate, 0 ≤ weight coordinate)
    (hdiagonal : matrix partner partner = 0)
    (hexternal : ∀ coordinate, coordinate ≠ who → coordinate ≠ partner →
      matrix partner coordinate < 0)
    (hrow : 0 ≤ ∑ coordinate, weight coordinate * matrix partner coordinate)
    (houtsideWho : outside ≠ who) (houtsidePartner : outside ≠ partner)
    (houtside : 0 < weight outside) : 0 < weight who := by
  by_contra hnot
  have hzero : weight who = 0 := le_antisymm (le_of_not_gt hnot) (hweight who)
  have hnegative : (∑ coordinate, weight coordinate * matrix partner coordinate) < 0 := by
    apply Finset.sum_neg'
    · intro coordinate _
      by_cases hwho : coordinate = who
      · subst coordinate
        simp only [hzero, zero_mul, le_refl]
      · by_cases hpartner : coordinate = partner
        · subst coordinate
          simp only [hdiagonal, mul_zero, le_refl]
        · exact mul_nonpos_of_nonneg_of_nonpos (hweight coordinate)
            (hexternal coordinate hwho hpartner).le
    · exact ⟨outside, Finset.mem_univ outside,
        mul_neg_of_pos_of_neg houtside (hexternal outside houtsideWho houtsidePartner)⟩
  exact (not_lt_of_ge hrow) hnegative

/-- Packet §4's matrix restriction, for an arbitrary finite index type and
the actual homogeneous complementarity problem of the row-swapped matrix. -/
theorem isR0Matrix_rowSwap_of_zero_diagonal_reciprocal_pos_external_neg
    (matrix : ι → ι → ℝ) (first second : ι)
    (hdiagonal : ∀ coordinate, matrix coordinate coordinate = 0)
    (hR0 : IsR0Matrix matrix)
    (hfirst : 0 < matrix first second) (hsecond : 0 < matrix second first)
    (hexternalFirst : ∀ outside, outside ≠ first → outside ≠ second →
      matrix first outside < 0)
    (hexternalSecond : ∀ outside, outside ≠ first → outside ≠ second →
      matrix second outside < 0) :
    IsR0Matrix (fun row column => matrix ((Equiv.swap first second) row) column) := by
  have hdistinct : first ≠ second := by
    intro hequal
    rw [← hequal, hdiagonal first] at hfirst
    exact (lt_irrefl (0 : ℝ)) hfirst
  intro weight solution
  by_cases houtsiders : ∀ outside, outside ≠ first → outside ≠ second → weight outside = 0
  · have hsum (row : ι) : (∑ coordinate, weight coordinate * matrix row coordinate) =
        weight first * matrix row first + weight second * matrix row second := by
      calc
        _ = ∑ coordinate ∈ ({first, second} : Finset ι),
            weight coordinate * matrix row coordinate := by
          symm
          apply Finset.sum_subset (Finset.subset_univ _)
          intro coordinate _ hnot
          have hne : coordinate ≠ first ∧ coordinate ≠ second := by
            simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using hnot
          rw [houtsiders coordinate hne.1 hne.2, zero_mul]
        _ = _ := Finset.sum_pair hdistinct
    have hfirstComplement := solution.complementary first
    have hsecondComplement := solution.complementary second
    simp only [lcpResidual, Pi.zero_apply, zero_add, Equiv.swap_apply_left,
      hsum second, hdiagonal second, mul_zero, add_zero] at hfirstComplement
    simp only [lcpResidual, Pi.zero_apply, zero_add, Equiv.swap_apply_right,
      hsum first, hdiagonal first, mul_zero, zero_add] at hsecondComplement
    have hfirstZero : weight first = 0 := by
      rcases mul_eq_zero.mp hfirstComplement with hzero | hzero
      · exact hzero
      · exact (mul_eq_zero.mp hzero).resolve_right hsecond.ne'
    have hsecondZero : weight second = 0 := by
      rcases mul_eq_zero.mp hsecondComplement with hzero | hzero
      · exact hzero
      · exact (mul_eq_zero.mp hzero).resolve_right hfirst.ne'
    intro coordinate
    by_cases hfirstEq : coordinate = first
    · simpa only [hfirstEq] using hfirstZero
    · by_cases hsecondEq : coordinate = second
      · simpa only [hsecondEq] using hsecondZero
      · exact houtsiders coordinate hfirstEq hsecondEq
  · push Not at houtsiders
    obtain ⟨outside, houtsideFirst, houtsideSecond, houtsideNe⟩ := houtsiders
    have houtside : 0 < weight outside :=
      lt_of_le_of_ne (solution.weight_nonneg outside) (Ne.symm houtsideNe)
    have hrowFirst : 0 ≤ ∑ coordinate, weight coordinate * matrix first coordinate := by
      simpa only [lcpResidual, Pi.zero_apply, zero_add, Equiv.swap_apply_right] using
        solution.residual_nonneg second
    have hrowSecond : 0 ≤ ∑ coordinate, weight coordinate * matrix second coordinate := by
      simpa only [lcpResidual, Pi.zero_apply, zero_add, Equiv.swap_apply_left] using
        solution.residual_nonneg first
    have hfirstPositive := selected_weight_pos_of_external_row matrix weight first second outside
      solution.weight_nonneg (hdiagonal second) hexternalSecond hrowSecond
      houtsideFirst houtsideSecond houtside
    have hsecondPositive := selected_weight_pos_of_external_row matrix weight second first outside
      solution.weight_nonneg (hdiagonal first)
      (fun coordinate hsecondNe hfirstNe => hexternalFirst coordinate hfirstNe hsecondNe)
      hrowFirst houtsideSecond houtsideFirst houtside
    have hfirstSlackZero : lcpResidual matrix 0 weight first = 0 := by
      have h := solution.complementary second
      simp only [lcpResidual, Equiv.swap_apply_right] at h
      exact (mul_eq_zero.mp h).resolve_left hsecondPositive.ne'
    have hsecondSlackZero : lcpResidual matrix 0 weight second = 0 := by
      have h := solution.complementary first
      simp only [lcpResidual, Equiv.swap_apply_left] at h
      exact (mul_eq_zero.mp h).resolve_left hfirstPositive.ne'
    have hsame (coordinate : ι) :
        lcpResidual (fun row column => matrix ((Equiv.swap first second) row) column)
          0 weight coordinate = lcpResidual matrix 0 weight coordinate := by
      by_cases hfirstEq : coordinate = first
      · subst coordinate
        have hequal : lcpResidual matrix 0 weight second = lcpResidual matrix 0 weight first := by
          rw [hsecondSlackZero, hfirstSlackZero]
        simpa only [lcpResidual, Equiv.swap_apply_left, Pi.zero_apply, zero_add] using hequal
      · by_cases hsecondEq : coordinate = second
        · subst coordinate
          have hequal : lcpResidual matrix 0 weight first = lcpResidual matrix 0 weight second := by
            rw [hfirstSlackZero, hsecondSlackZero]
          simpa only [lcpResidual, Equiv.swap_apply_right, Pi.zero_apply, zero_add] using hequal
        · simp only [lcpResidual, Equiv.swap_apply_of_ne_of_ne hfirstEq hsecondEq]
    apply hR0 weight
    refine ⟨solution.weight_nonneg, ?_, ?_⟩
    · intro coordinate
      rw [← hsame coordinate]
      exact solution.residual_nonneg coordinate
    · intro coordinate
      rw [← hsame coordinate]
      exact solution.complementary coordinate

end Math.LinearProgramming
