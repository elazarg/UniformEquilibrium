import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! # Scalar algebra for the heterogeneous signed four-cycle reconstruction -/

noncomputable section

namespace Math

/-- Eight real coefficients for a four-cycle recurrence. Positivity and spectral
conditions are supplied only to the results that use them. -/
structure SignedFourCycleCoefficients where
  aZero : ℝ
  aOne : ℝ
  aTwo : ℝ
  aThree : ℝ
  dZero : ℝ
  dOne : ℝ
  dTwo : ℝ
  dThree : ℝ

namespace SignedFourCycleCoefficients

variable (c : SignedFourCycleCoefficients)

def lowerLeft : ℝ := c.aZero * c.dOne + (c.aZero * c.aOne + c.dZero) * c.aTwo
def lowerRight : ℝ := (c.aZero * c.aOne + c.dZero) * c.dTwo
def upperLeft : ℝ := c.aThree * c.lowerLeft + c.dThree * (c.dOne + c.aOne * c.aTwo)
def upperRight : ℝ := c.aThree * c.lowerRight + c.dThree * c.aOne * c.dTwo
def discriminant : ℝ := (c.upperLeft - c.lowerRight) ^ 2 + 4 * c.upperRight * c.lowerLeft
def smallerEigenvalue : ℝ := (c.upperLeft + c.lowerRight - Real.sqrt c.discriminant) / 2
def periodSurvival : ℝ := 1 / c.smallerEigenvalue
def rawWeightZero : ℝ := -c.upperRight
def rawWeightOne : ℝ := c.upperLeft - c.smallerEigenvalue
def rawWeightThree : ℝ := c.periodSurvival * (c.aTwo * c.rawWeightZero + c.dTwo * c.rawWeightOne)
def rawWeightTwo : ℝ := c.periodSurvival * c.dOne * c.rawWeightZero + c.aOne * c.rawWeightThree

theorem periodSurvival_pos (hlambda : 1 < c.smallerEigenvalue) : 0 < c.periodSurvival :=
  one_div_pos.mpr (lt_trans (by norm_num) hlambda)

theorem periodSurvival_lt_one (hlambda : 1 < c.smallerEigenvalue) : c.periodSurvival < 1 := by
  rw [periodSurvival]
  simpa only [one_div] using inv_lt_one_of_one_lt₀ hlambda

theorem rawWeightZero_pos (hk : c.upperRight < 0) : 0 < c.rawWeightZero := by
  simpa [rawWeightZero] using neg_pos.mpr hk

theorem rawWeightOne_pos (hk : 0 < c.upperLeft - c.smallerEigenvalue) : 0 < c.rawWeightOne := hk

theorem characteristic :
    0 ≤ c.discriminant →
    (c.upperLeft - c.smallerEigenvalue) * (c.lowerRight - c.smallerEigenvalue) -
      c.upperRight * c.lowerLeft = 0 := by
  intro hdisc
  have hsqrt : (Real.sqrt c.discriminant) ^ 2 = c.discriminant :=
    Real.sq_sqrt hdisc
  unfold smallerEigenvalue discriminant at hsqrt ⊢
  nlinarith [hsqrt]

theorem eigen_first : c.upperLeft * c.rawWeightZero + c.upperRight * c.rawWeightOne =
    c.smallerEigenvalue * c.rawWeightZero := by
  unfold rawWeightZero rawWeightOne
  ring

theorem eigen_second (hdisc : 0 ≤ c.discriminant) :
    c.lowerLeft * c.rawWeightZero + c.lowerRight * c.rawWeightOne =
      c.smallerEigenvalue * c.rawWeightOne := by
  have h := c.characteristic hdisc
  unfold rawWeightZero rawWeightOne
  ring_nf at h ⊢
  linarith

/-- Either eigenvector reconstruction gives the same four recurrences. -/
theorem balance_identities_of_eigenvector
    (lambda zero one : ℝ) (hlambda : lambda ≠ 0)
    (hfirst : c.upperLeft * zero + c.upperRight * one = lambda * zero)
    (hsecond : c.lowerLeft * zero + c.lowerRight * one = lambda * one) :
    let three := (c.aTwo * zero + c.dTwo * one) / lambda
    let two := c.dOne * zero / lambda + c.aOne * three
    one = c.aZero * two + c.dZero * three ∧
      zero = c.aThree * one + c.dThree * two := by
  dsimp only
  constructor
  · unfold lowerLeft lowerRight at hsecond
    field_simp [hlambda]
    linear_combination -hsecond
  · unfold upperLeft upperRight lowerLeft lowerRight at hfirst
    unfold lowerLeft lowerRight at hsecond
    field_simp [hlambda]
    linear_combination -hfirst + c.aThree * hsecond

/-- The eigenvector reconstruction solves the four cyclic linear recurrences. -/
theorem reconstructed_balance_identities
    (hdisc : 0 ≤ c.discriminant) (hlambda : 1 < c.smallerEigenvalue) :
    c.rawWeightOne = c.aZero * c.rawWeightTwo + c.dZero * c.rawWeightThree ∧
      c.rawWeightZero = c.aThree * c.rawWeightOne + c.dThree * c.rawWeightTwo ∧
      c.rawWeightTwo = c.periodSurvival * c.dOne * c.rawWeightZero + c.aOne * c.rawWeightThree ∧
      c.rawWeightThree =
        c.periodSurvival * (c.aTwo * c.rawWeightZero + c.dTwo * c.rawWeightOne) := by
  have hlambda0 : c.smallerEigenvalue ≠ 0 := ne_of_gt (lt_trans (by norm_num) hlambda)
  have hbalance := c.balance_identities_of_eigenvector
    c.smallerEigenvalue c.rawWeightZero c.rawWeightOne hlambda0 c.eigen_first
    (c.eigen_second hdisc)
  refine ⟨?_, ?_, rfl, rfl⟩
  · simpa only [rawWeightTwo, rawWeightThree, periodSurvival, one_div,
      div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc, one_mul] using hbalance.1
  · simpa only [rawWeightTwo, rawWeightThree, periodSurvival, one_div,
      div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc, one_mul] using hbalance.2

end SignedFourCycleCoefficients
end Math
