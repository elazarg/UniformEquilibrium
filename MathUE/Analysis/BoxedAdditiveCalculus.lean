import MathUE.Analysis.LowerBoxBoundarySmoothDrift
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.TangentCone.Real

/-! # Box-only derivative identification and additive coordinate calculus -/

noncomputable section

namespace Math

open Set Filter Topology
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Equality on a positive-width closed box identifies ambient derivatives
even at its boundary. One-coordinate restrictions use interval uniqueness. -/
theorem box_fderiv_eq_of_eqOn
    (lower upper point : ι → ℝ) (first second : (ι → ℝ) → ℝ)
    (hwidth : ∀ who, lower who < upper who) (hpoint : point ∈ Icc lower upper)
    (heq : EqOn first second (Icc lower upper))
    (hfirst : DifferentiableAt ℝ first point)
    (hsecond : DifferentiableAt ℝ second point) :
    fderiv ℝ first point = fderiv ℝ second point := by
  have hpartial : ∀ who, fderiv ℝ first point (Pi.single who 1) =
      fderiv ℝ second point (Pi.single who 1) := by
    intro who
    have hupdate : point = Function.update point who (point who) := by simp
    have hfirstSlice := hfirst.hasFDerivAt.comp_hasDerivAt_of_eq (point who)
      (hasDerivAt_update point who (point who)) hupdate
    have hsecondSlice := hsecond.hasFDerivAt.comp_hasDerivAt_of_eq (point who)
      (hasDerivAt_update point who (point who)) hupdate
    have heqSlice : EqOn (fun value => first (Function.update point who value))
        (fun value => second (Function.update point who value))
        (Icc (lower who) (upper who)) := by
      intro value hvalue
      apply heq
      constructor <;> intro other
      · by_cases hother : other = who
        · subst other; simpa using hvalue.1
        · simpa [hother] using hpoint.1 other
      · by_cases hother : other = who
        · subst other; simpa using hvalue.2
        · simpa [hother] using hpoint.2 other
    exact (uniqueDiffOn_Icc (hwidth who) (point who)
      ⟨hpoint.1 who, hpoint.2 who⟩).eq_deriv _
      hfirstSlice.hasDerivWithinAt
      (hsecondSlice.hasDerivWithinAt.congr (fun _ hv => heqSlice hv)
        (heqSlice ⟨hpoint.1 who, hpoint.2 who⟩))
  ext direction
  rw [pi_eq_sum_univ' direction]
  simp only [map_sum, map_smul, hpartial]

/-- The literal additive expression on an ambient coordinate space. -/
def boxAdditiveFunction (constant : ℝ) (component : ι → ℝ → ℝ)
    (point : ι → ℝ) : ℝ := constant + ∑ who, component who (point who)

/-- The additive derivative is a sum of coordinate projections. -/
def boxAdditiveDerivative (component : ι → ℝ → ℝ) (point : ι → ℝ) :
    (ι → ℝ) →L[ℝ] ℝ :=
  ∑ who, deriv (component who) (point who) • ContinuousLinearMap.proj who

omit [DecidableEq ι] in
theorem hasFDerivAt_boxAdditiveFunction
    (constant : ℝ) (component : ι → ℝ → ℝ) (point : ι → ℝ)
    (hdiff : ∀ who, DifferentiableAt ℝ (component who) (point who)) :
    HasFDerivAt (boxAdditiveFunction constant component)
      (boxAdditiveDerivative component point) point := by
  have hcoordinate : ∀ who, HasFDerivAt
      (fun input : ι → ℝ => component who (input who))
      (deriv (component who) (point who) •
        (ContinuousLinearMap.proj who : (ι → ℝ) →L[ℝ] ℝ)) point := by
    intro who
    exact (hdiff who).hasDerivAt.comp_hasFDerivAt point (hasFDerivAt_apply who point)
  have hsum := HasFDerivAt.fun_sum (u := Finset.univ) fun who _ => hcoordinate who
  change HasFDerivAt (fun input : ι → ℝ => constant + ∑ who, component who (input who))
    (∑ who, deriv (component who) (point who) • ContinuousLinearMap.proj who) point
  exact hsum.const_add constant

omit [DecidableEq ι] in
@[simp] theorem boxAdditiveDerivative_apply
    (component : ι → ℝ → ℝ) (point direction : ι → ℝ) :
    boxAdditiveDerivative component point direction =
      ∑ who, deriv (component who) (point who) * direction who := by
  simp [boxAdditiveDerivative, smul_eq_mul]

@[simp] theorem boxAdditiveDerivative_single
    (component : ι → ℝ → ℝ) (point : ι → ℝ) (who : ι) :
    boxAdditiveDerivative component point (Pi.single who 1) =
      deriv (component who) (point who) := by
  rw [boxAdditiveDerivative_apply, Finset.sum_eq_single who]
  · simp
  · intro other _ hne
    rw [Pi.single_eq_of_ne hne 1, mul_zero]
  · intro hnot
    exact False.elim (hnot (Finset.mem_univ who))

/-- Resetting one coordinate leaves all other additive partials unchanged. -/
theorem boxAdditiveDerivative_reset_partial
    (component : ι → ℝ → ℝ) (point : ι → ℝ) (owner other : ι)
    (hne : other ≠ owner) (replacement : ℝ) :
    boxAdditiveDerivative component (Function.update point owner replacement)
      (Pi.single other 1) = deriv (component other) (point other) := by
  rw [boxAdditiveDerivative_single, Function.update_of_ne hne]

/-- The one-sided lower, interior, and upper signs at an internally selected
component minimum. Flat minima and endpoint minima are included. -/
theorem interval_minimum_derivative_signs
    (component : ℝ → ℝ) (lower upper point : ℝ)
    (hwidth : lower < upper) (hpoint : point ∈ Icc lower upper)
    (hmin : IsMinOn component (Icc lower upper) point)
    (hdiff : DifferentiableAt ℝ component point) :
    (point = lower → 0 ≤ deriv component point) ∧
    (lower < point → point < upper → deriv component point = 0) ∧
    (point = upper → deriv component point ≤ 0) := by
  have hlocal : IsLocalMinOn component (Icc lower upper) point :=
    Filter.mem_of_superset self_mem_nhdsWithin hmin
  have hmove : ∀ target ∈ Icc lower upper,
      0 ≤ (target - point) * deriv component point := by
    intro target htarget
    have hnonnegative := hlocal.hasFDerivWithinAt_nonneg
      hdiff.hasDerivAt.hasFDerivAt.hasFDerivWithinAt
      (sub_mem_posTangentConeAt_of_segment_subset
        ((convex_Icc lower upper).segment_subset hpoint htarget))
    change 0 ≤ (target - point) * deriv component point at hnonnegative
    exact hnonnegative
  have hlower := hmove lower ⟨le_rfl, hwidth.le⟩
  have hupper := hmove upper ⟨hwidth.le, le_rfl⟩
  refine ⟨?_, ?_, ?_⟩
  · intro heq; rw [heq] at hupper ⊢; nlinarith
  · intro hlow hupp; nlinarith
  · intro heq; rw [heq] at hlower ⊢; nlinarith

end Math
