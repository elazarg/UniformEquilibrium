import MathUE.Probability.StoppingLawReconstruction
import MathUE.ProbabilityMassFunction.LateFiniteStoppingLawCensor

/-! # Exact late-clock indicator expectations -/

noncomputable section

namespace Math.Probability

open scoped BigOperators

private theorem expect_finset_indicator {α : Type*} [DecidableEq α]
    (law : PMF α) (kept : Finset α) :
    expect law (fun choice ↦ if choice ∈ kept then 1 else 0) =
      ∑ choice ∈ kept, (law choice).toReal := by
  unfold expect
  rw [tsum_eq_sum (s := kept)]
  · simp
  · intro choice hchoice
    simp [hchoice]

private theorem expect_add_bounded {α : Type*} (law : PMF α)
    (first second : α → ℝ) {firstBound secondBound : ℝ}
    (hfirst : ∀ choice, |first choice| ≤ firstBound)
    (hsecond : ∀ choice, |second choice| ≤ secondBound) :
    expect law (fun choice ↦ first choice + second choice) =
      expect law first + expect law second :=
  expect_add_of_summable law first second
    (expect_summable_of_bounded law first hfirst)
    (expect_summable_of_bounded law second hsecond)

/-- Indicator of the entire tail after the finite head, including Never. -/
def stoppingLawTailIndicator (deadline : ℕ) (choice : Option ℕ) : ℝ :=
  if choice ∈ (Finset.range deadline).image some then 0 else 1

/-- Indicator of finite stopping dates in the half-open displayed interval. -/
def stoppingLawIntervalIndicator (lower upper : ℕ) (choice : Option ℕ) : ℝ :=
  if choice ∈ (Finset.Ico lower upper).image some then 1 else 0

theorem abs_stoppingLawTailIndicator_le_one (deadline : ℕ) (choice : Option ℕ) :
    |stoppingLawTailIndicator deadline choice| ≤ 1 := by
  unfold stoppingLawTailIndicator
  split_ifs <;> norm_num

theorem abs_stoppingLawIntervalIndicator_le_one
    (lower upper : ℕ) (choice : Option ℕ) :
    |stoppingLawIntervalIndicator lower upper choice| ≤ 1 := by
  unfold stoppingLawIntervalIndicator
  split_ifs <;> norm_num

/-- The tail indicator integrates to the actual pre-deadline survival mass. -/
theorem expect_stoppingLawTailIndicator (law : PMF (Option ℕ)) (deadline : ℕ) :
    expect law (stoppingLawTailIndicator deadline) =
      DiscreteHazard.StoppingLaw.survival law deadline := by
  let head : Option ℕ → ℝ := fun choice ↦
    if choice ∈ (Finset.range deadline).image some then 1 else 0
  have hhead : ∀ choice, |head choice| ≤ 1 := by
    intro choice
    unfold head
    split_ifs <;> norm_num
  have hsum : expect law (fun choice ↦ head choice +
      stoppingLawTailIndicator deadline choice) = 1 := by
    have hpoint : (fun choice ↦ head choice + stoppingLawTailIndicator deadline choice) =
        fun _ ↦ (1 : ℝ) := by
      funext choice
      simp only [head, stoppingLawTailIndicator]
      split_ifs <;> norm_num
    rw [hpoint, expect_const]
  rw [expect_add_bounded law head (stoppingLawTailIndicator deadline) hhead
    (abs_stoppingLawTailIndicator_le_one deadline)] at hsum
  have hheadValue : expect law head =
      ∑ time ∈ Finset.range deadline, (law (some time)).toReal := by
    rw [show head = (fun choice ↦
      if choice ∈ (Finset.range deadline).image some then 1 else 0) by rfl,
      expect_finset_indicator, Finset.sum_image]
    intro first _ second _ heq
    exact Option.some.inj heq
  rw [hheadValue] at hsum
  unfold DiscreteHazard.StoppingLaw.survival DiscreteHazard.StoppingLaw.finiteMass
  linarith

/-- The interval indicator integrates to the literal sum of its finite atoms. -/
theorem expect_stoppingLawIntervalIndicator
    (law : PMF (Option ℕ)) (lower upper : ℕ) :
    expect law (stoppingLawIntervalIndicator lower upper) =
      ∑ time ∈ Finset.Ico lower upper, (law (some time)).toReal := by
  unfold stoppingLawIntervalIndicator
  rw [expect_finset_indicator, Finset.sum_image]
  intro first _ second _ heq
  exact Option.some.inj heq

/-- A single finite-date indicator integrates to its actual PMF atom. -/
theorem expect_stoppingLaw_finite_atom (law : PMF (Option ℕ)) (time : ℕ) :
    expect law (fun choice ↦ if choice = some time then 1 else 0) =
      (law (some time)).toReal := by
  simpa using expect_finset_indicator law {some time}

/-- Integrating the signed three-indicator late response gives its exact
survival, interval-mass, and atom expression for an arbitrary complete law. -/
theorem expect_stoppingLaw_late_affine
    (law : PMF (Option ℕ)) (deadline time : ℕ) (early : Option ℕ → ℝ)
    {earlyBound : ℝ} (hearly : ∀ choice, |early choice| ≤ earlyBound)
    (weight before tie after : ℝ) :
    expect law (fun choice ↦ early choice + weight *
      (after * stoppingLawTailIndicator deadline choice +
        (before - after) * stoppingLawIntervalIndicator deadline time choice +
        (tie - after) * (if choice = some time then 1 else 0))) =
      expect law early + weight *
        (after * DiscreteHazard.StoppingLaw.survival law deadline +
          (before - after) * (∑ chosen ∈ Finset.Ico deadline time,
            (law (some chosen)).toReal) +
          (tie - after) * (law (some time)).toReal) := by
  let first := fun choice ↦ after * stoppingLawTailIndicator deadline choice
  let second := fun choice ↦
    (before - after) * stoppingLawIntervalIndicator deadline time choice
  let third := fun choice : Option ℕ ↦
    (tie - after) * (if choice = some time then 1 else 0)
  have hfirst : ∀ choice, |first choice| ≤ |after| := by
    intro choice
    dsimp only [first]
    rw [abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg after)
      (abs_stoppingLawTailIndicator_le_one deadline choice)
  have hsecond : ∀ choice, |second choice| ≤ |before - after| := by
    intro choice
    dsimp only [second]
    rw [abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg (before - after))
      (abs_stoppingLawIntervalIndicator_le_one deadline time choice)
  have hthird : ∀ choice, |third choice| ≤ |tie - after| := by
    intro choice
    unfold third
    split_ifs <;> simp
  have hfirstSecond : ∀ choice, |first choice + second choice| ≤
      |after| + |before - after| := by
    intro choice
    exact (abs_add_le _ _).trans (add_le_add (hfirst choice) (hsecond choice))
  have hsum : ∀ choice, |first choice + second choice + third choice| ≤
      |after| + |before - after| + |tie - after| := by
    intro choice
    exact (abs_add_le _ _).trans (add_le_add (hfirstSecond choice) (hthird choice))
  have hweighted : ∀ choice, |weight * (first choice + second choice + third choice)| ≤
      |weight| * (|after| + |before - after| + |tie - after|) := by
    intro choice
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hsum choice) (abs_nonneg weight)
  change expect law (fun choice ↦ early choice +
    weight * (first choice + second choice + third choice)) = _
  rw [expect_add_bounded law early _ hearly hweighted, expect_const_mul,
    expect_add_bounded law (fun choice ↦ first choice + second choice) third
      hfirstSecond hthird,
    expect_add_bounded law first second hfirst hsecond]
  simp only [first, second, third, expect_const_mul, expect_stoppingLawTailIndicator,
    expect_stoppingLawIntervalIndicator, expect_stoppingLaw_finite_atom]

/-- For a positive head length, survival is finite-tail mass plus the
original Never atom; the inclusive censor cutoff is exactly one less. -/
theorem stoppingLaw_survival_eq_lateFiniteMass_add_none
    (law : PMF (Option ℕ)) {deadline : ℕ} (hdeadline : 0 < deadline) :
    DiscreteHazard.StoppingLaw.survival law deadline =
      stoppingLawLateFiniteMass law (deadline - 1) + (law none).toReal := by
  rw [stoppingLawLateFiniteMass_eq_one_sub_none_sub_finiteHead]
  simp only [DiscreteHazard.StoppingLaw.survival, DiscreteHazard.StoppingLaw.finiteMass,
    stoppingLawFiniteHeadMass, show deadline - 1 + 1 = deadline by omega]
  ring

end Math.Probability
