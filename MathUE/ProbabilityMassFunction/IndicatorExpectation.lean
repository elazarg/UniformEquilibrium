import MathUE.Probability

/-! # Indicator expectations for arbitrary PMFs -/

noncomputable section

namespace Math.Probability

/-- A singleton indicator integrates to its PMF coordinate, without a
finiteness assumption on the sample type. -/
theorem expect_singletonIndicator {Ω : Type*} [DecidableEq Ω]
    (law : PMF Ω) (point : Ω) :
    expect law (fun other ↦ if other = point then 1 else 0) =
      (law point).toReal := by
  unfold expect
  rw [tsum_eq_single point]
  · simp
  · intro other hne
    simp [hne]

/-- The complement of a singleton indicator integrates to one minus that
coordinate, without a finiteness assumption on the sample type. -/
theorem expect_complementSingletonIndicator {Ω : Type*} [DecidableEq Ω]
    (law : PMF Ω) (point : Ω) :
    expect law (fun other ↦ if other = point then 0 else 1) =
      1 - (law point).toReal := by
  let complement := fun other : Ω ↦ if other = point then (0 : ℝ) else 1
  let singleton := fun other : Ω ↦ if other = point then (1 : ℝ) else 0
  have hcomplement : ∀ other, |complement other| ≤ 1 := by
    intro other
    simp only [complement]
    split_ifs <;> norm_num
  have hsingleton : ∀ other, |singleton other| ≤ 1 := by
    intro other
    simp only [singleton]
    split_ifs <;> norm_num
  have hadd := expect_add_of_summable law complement singleton
    (expect_summable_of_bounded law complement hcomplement)
    (expect_summable_of_bounded law singleton hsingleton)
  have hpoint : (fun other ↦ complement other + singleton other) =
      fun _ ↦ (1 : ℝ) := by
    funext other
    simp only [complement, singleton]
    split_ifs <;> norm_num
  rw [hpoint, expect_const, expect_singletonIndicator] at hadd
  exact eq_sub_iff_add_eq.mpr hadd.symm

end Math.Probability
