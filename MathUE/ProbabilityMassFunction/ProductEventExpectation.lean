import MathUE.PMFProduct.Conditioning
import MathUE.ProbabilityMassFunction.FiniteSumExpectation

/-! # Real expectations of finite independent events -/

noncomputable section

namespace Math.Probability

open scoped BigOperators Classical
open Math.ProbabilityMassFunction Math.PMFProduct

/-- An arbitrary discrete event indicator integrates to its actual mass. -/
theorem expect_eventIndicator {Ω : Type*} (law : PMF Ω) (event : Ω → Prop) :
    expect law (fun point => if event point then 1 else 0) =
      (pmfMass law event).toReal := by
  classical
  unfold expect pmfMass
  rw [ENNReal.tsum_toReal_eq]
  · apply tsum_congr
    intro point
    by_cases hpoint : event point <;> simp [pmfMask, hpoint]
  · intro point
    by_cases hpoint : event point
    · simpa [pmfMask, hpoint] using PMF.apply_ne_top law point
    · simp [pmfMask, hpoint]

/-- Product-event expectation factors without finite-support assumptions. -/
theorem expect_pmfPi_forallIndicator
    {ι : Type*} [Fintype ι] {Ω : ι → Type*}
    (laws : ∀ who, PMF (Ω who)) (event : ∀ who, Ω who → Prop) :
    expect (pmfPi laws) (fun point => if ∀ who, event who (point who) then 1 else 0) =
      ∏ who, expect (laws who) (fun choice => if event who choice then 1 else 0) := by
  classical
  have hfirst := expect_eventIndicator (pmfPi laws)
    (fun point => ∀ who, event who (point who))
  calc
    _ = (pmfMass (pmfPi laws) (fun point => ∀ who, event who (point who))).toReal := by
      convert hfirst using 1
      congr 1
      funext point
      by_cases hpoint : ∀ who, event who (point who) <;>
        simp only [hpoint, ite_false]
    _ = ∏ who, expect (laws who) (fun choice => if event who choice then 1 else 0) := by
      rw [pmfMass_pmfPi_forall, ENNReal.toReal_prod]
      apply Finset.prod_congr rfl
      intro who _
      exact (expect_eventIndicator (laws who) (event who)).symm

/-- A stage-before-absorption triangular sum counts paid stages exactly. -/
theorem sum_prefix_sums_eq_absorption_weights (value : ℕ → ℝ) (horizon : ℕ) :
    (∑ stage ∈ Finset.range horizon, ∑ time ∈ Finset.range stage, value time) =
      ∑ time ∈ Finset.range horizon, (horizon - time - 1 : ℕ) * value time := by
  induction horizon with
  | zero => simp
  | succ horizon ih =>
      rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
      have hlast : horizon + 1 - horizon - 1 = 0 := by omega
      rw [hlast]
      simp only [Nat.cast_zero, zero_mul, add_zero]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro time htime
      have htimeLt := Finset.mem_range.mp htime
      have hcount : horizon + 1 - time - 1 = (horizon - time - 1) + 1 := by omega
      rw [hcount, Nat.cast_add, Nat.cast_one]
      ring

end Math.Probability
