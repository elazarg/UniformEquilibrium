import MathUE.Probability
import MathUE.ProbabilityMassFunction.MapSupport

/-! # Collapsing late finite stopping atoms while retaining Never -/

noncomputable section

namespace Math.Probability

/-- Collapse late finite dates onto one finite deadline, retaining Never. -/
def collapseLateFiniteStoppingTime (deadline : ℕ) : Option ℕ → Option ℕ
  | none => none
  | some time => some (min time deadline)

@[simp] theorem collapseLateFiniteStoppingTime_none (deadline : ℕ) :
    collapseLateFiniteStoppingTime deadline none = none := rfl

@[simp] theorem collapseLateFiniteStoppingTime_eq_none_iff
    (deadline : ℕ) (time : Option ℕ) :
    collapseLateFiniteStoppingTime deadline time = none ↔ time = none := by
  cases time <;> simp [collapseLateFiniteStoppingTime]

theorem collapseLateFiniteStoppingTime_of_lt
    {deadline time : ℕ} (htime : time < deadline) :
    collapseLateFiniteStoppingTime deadline (some time) = some time := by
  simp [collapseLateFiniteStoppingTime, min_eq_left htime.le]

theorem collapseLateFiniteStoppingTime_of_le
    {deadline time : ℕ} (htime : deadline ≤ time) :
    collapseLateFiniteStoppingTime deadline (some time) = some deadline := by
  simp [collapseLateFiniteStoppingTime, min_eq_right htime]

/-- Actual law obtained by moving every late finite atom to the deadline;
the original Never atom is retained. -/
def collapseLateFiniteStoppingLaw (law : PMF (Option ℕ)) (deadline : ℕ) :
    PMF (Option ℕ) := law.map (collapseLateFiniteStoppingTime deadline)

@[simp] theorem collapseLateFiniteStoppingLaw_none
    (law : PMF (Option ℕ)) (deadline : ℕ) :
    collapseLateFiniteStoppingLaw law deadline none = law none := by
  classical
  rw [collapseLateFiniteStoppingLaw, PMF.map_apply, tsum_eq_single none]
  · simp
  · intro source hsource
    cases source with
    | none => exact (hsource rfl).elim
    | some time => simp [collapseLateFiniteStoppingTime]

theorem collapseLateFiniteStoppingLaw_some_of_lt
    (law : PMF (Option ℕ)) {deadline time : ℕ} (htime : time < deadline) :
    collapseLateFiniteStoppingLaw law deadline (some time) = law (some time) := by
  classical
  rw [collapseLateFiniteStoppingLaw, PMF.map_apply, tsum_eq_single (some time)]
  · simp [collapseLateFiniteStoppingTime_of_lt htime]
  · intro source hsource
    cases source with
    | none => simp
    | some chosen =>
        rw [if_neg]
        simp only [collapseLateFiniteStoppingTime, Option.some.injEq]
        have hne : chosen ≠ time := fun heq ↦ hsource (congrArg some heq)
        omega

theorem collapseLateFiniteStoppingLaw_some_of_gt
    (law : PMF (Option ℕ)) {deadline time : ℕ} (htime : deadline < time) :
    collapseLateFiniteStoppingLaw law deadline (some time) = 0 := by
  classical
  rw [collapseLateFiniteStoppingLaw, PMF.map_apply]
  apply ENNReal.tsum_eq_zero.mpr
  intro source
  cases source with
  | none => simp
  | some chosen =>
      rw [if_neg]
      simp only [collapseLateFiniteStoppingTime, Option.some.injEq]
      omega

private theorem pmf_eq_of_eq_away {α : Type*} (first second : PMF α) (point : α)
    (heq : ∀ other, other ≠ point → first other = second other) : first = second := by
  classical
  have hfirst := (pmf_toReal_summable first).tsum_eq_add_tsum_ite point
  have hsecond := (pmf_toReal_summable second).tsum_eq_add_tsum_ite point
  rw [pmf_toReal_tsum_one] at hfirst hsecond
  have hrest : (∑' other, if other = point then (0 : ℝ) else (first other).toReal) =
      ∑' other, if other = point then (0 : ℝ) else (second other).toReal := by
    apply tsum_congr
    intro other
    by_cases hother : other = point
    · simp [hother]
    · simp [hother, heq other hother]
  have hpoint : (first point).toReal = (second point).toReal := by linarith
  apply PMF.ext
  intro other
  by_cases hother : other = point
  · subst other
    exact (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp hpoint
  · exact heq other hother

/-- Head atoms and Never mass determine the collapsed finite law. Equal late
finite mass follows from probability normalization and is not a premise. -/
theorem collapseLateFiniteStoppingLaw_eq_of_head_and_never
    (first second : PMF (Option ℕ)) (deadline : ℕ)
    (hhead : ∀ time < deadline, first (some time) = second (some time))
    (hnever : first none = second none) :
    collapseLateFiniteStoppingLaw first deadline =
      collapseLateFiniteStoppingLaw second deadline := by
  apply pmf_eq_of_eq_away _ _ (some deadline)
  intro choice hchoice
  cases choice with
  | none => simpa using hnever
  | some time =>
      have hne : time ≠ deadline := fun heq ↦ hchoice (congrArg some heq)
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · rw [collapseLateFiniteStoppingLaw_some_of_lt first hlt,
          collapseLateFiniteStoppingLaw_some_of_lt second hlt]
        exact hhead time hlt
      · rw [collapseLateFiniteStoppingLaw_some_of_gt first hgt,
          collapseLateFiniteStoppingLaw_some_of_gt second hgt]

end Math.Probability
