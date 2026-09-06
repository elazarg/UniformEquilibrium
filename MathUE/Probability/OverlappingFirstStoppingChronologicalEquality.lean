import MathUE.Probability.OverlappingFirstStoppingInfiniteRecurrence
import MathUE.Probability.OverlappingFirstStoppingDeterministicAtom
import MathUE.Probability.OverlappingFirstStoppingPositiveContinueEquality

/-! # Chronological equality for the two overlapping first-stopping masses -/

noncomputable section

namespace Math.Probability.DiscreteHazard.ScalarHazard

open StoppingLaw

/-- At positive continuation, actual infinite boundary masses satisfy the
complete one-row equality alternatives. -/
theorem overlappingTailMasses_eq_one_step_of_continue_pos
    (first second third : ScalarHazard) (start : ℕ)
    (hcontinue : 0 < (1 - first.stop start) * (1 - second.stop start) *
      (1 - third.stop start))
    (hequality : Real.sqrt (equalFirstSecondBeforeThirdTailMass first second third start) +
      Real.sqrt (equalFirstThirdBeforeSecondTailMass first second third start) = 1) :
    (first.stop start = 0 ∧ second.stop start = 0 ∧ third.stop start = 0) ∨
      (second.stop start = 0 ∧ third.stop start = first.stop start ∧
        equalFirstSecondBeforeThirdTailMass first second third (start + 1) = 1 ∧
        equalFirstThirdBeforeSecondTailMass first second third (start + 1) = 0) ∨
      (third.stop start = 0 ∧ second.stop start = first.stop start ∧
        equalFirstSecondBeforeThirdTailMass first second third (start + 1) = 0 ∧
        equalFirstThirdBeforeSecondTailMass first second third (start + 1) = 1) := by
  rw [equalFirstSecondBeforeThirdTailMass_succ,
    equalFirstThirdBeforeSecondTailMass_succ] at hequality
  exact overlappingFirstStopping_squareRoot_step_eq_one_of_commonContinue_pos
    ⟨first.stop_nonneg start, first.stop_le_one start⟩
    ⟨second.stop_nonneg start, second.stop_le_one start⟩
    ⟨third.stop_nonneg start, third.stop_le_one start⟩
    (equalFirstSecondBeforeThirdMass_nonneg _ _ _)
    (equalFirstThirdBeforeSecondMass_nonneg _ _ _)
    (twoOverlappingFirstStoppingTailMasses_sqrt_sum_le_one first second third (start + 1))
    hcontinue hequality

/-- Boundary equality propagates through every positive-continuation row,
including an all-Continue row. -/
theorem overlappingTailMasses_sqrt_sum_eq_one_succ_of_continue_pos
    (first second third : ScalarHazard) (start : ℕ)
    (hcontinue : 0 < (1 - first.stop start) * (1 - second.stop start) *
      (1 - third.stop start))
    (hequality : Real.sqrt (equalFirstSecondBeforeThirdTailMass first second third start) +
      Real.sqrt (equalFirstThirdBeforeSecondTailMass first second third start) = 1) :
    Real.sqrt (equalFirstSecondBeforeThirdTailMass first second third (start + 1)) +
      Real.sqrt (equalFirstThirdBeforeSecondTailMass first second third (start + 1)) = 1 := by
  rcases overlappingTailMasses_eq_one_step_of_continue_pos
    first second third start hcontinue hequality with hzero | hleft | hright
  · obtain ⟨hfirst, hsecond, hthird⟩ := hzero
    rw [equalFirstSecondBeforeThirdTailMass_succ,
      equalFirstThirdBeforeSecondTailMass_succ] at hequality
    simpa only [hfirst, hsecond, hthird, mul_zero, zero_mul, sub_zero,
      one_mul, zero_add] using hequality
  · rw [hleft.2.2.1, hleft.2.2.2]
    norm_num
  · rw [hright.2.2.1, hright.2.2.2]
    norm_num

/-- Removing an initial all-Continue prefix preserves both complete event masses. -/
theorem overlappingTailMasses_eq_of_initial_zero
    (first second third : ScalarHazard) (start : ℕ)
    (hzero : ∀ time < start,
      first.stop time = 0 ∧ second.stop time = 0 ∧ third.stop time = 0) :
    equalFirstSecondBeforeThirdTailMass first second third start =
        equalFirstSecondBeforeThirdTailMass first second third 0 ∧
      equalFirstThirdBeforeSecondTailMass first second third start =
        equalFirstThirdBeforeSecondTailMass first second third 0 := by
  induction start with
  | zero => exact ⟨rfl, rfl⟩
  | succ start ih =>
      have hprevious := ih (fun time htime => hzero time (by omega))
      obtain ⟨hfirst, hsecond, hthird⟩ := hzero start (by omega)
      have hfirstStep := equalFirstSecondBeforeThirdTailMass_succ first second third start
      have hsecondStep := equalFirstThirdBeforeSecondTailMass_succ first second third start
      simp only [hfirst, hsecond, hthird, mul_zero, zero_mul, sub_zero,
        one_mul, zero_add] at hfirstStep hsecondStep
      exact ⟨hfirstStep.symm.trans hprevious.1, hsecondStep.symm.trans hprevious.2⟩

/-- Positive mass ensures a first active date. All earlier hazards vanish,
and the two residual event masses still equal their original masses. -/
theorem exists_first_active_date_of_overlappingTailMass_pos
    (first second third : ScalarHazard)
    (hpositive : 0 < equalFirstSecondBeforeThirdTailMass first second third 0) :
    ∃ start,
      (∀ time < start,
        first.stop time = 0 ∧ second.stop time = 0 ∧ third.stop time = 0) ∧
      (first.stop start ≠ 0 ∨ second.stop start ≠ 0 ∨ third.stop start ≠ 0) ∧
      equalFirstSecondBeforeThirdTailMass first second third start =
        equalFirstSecondBeforeThirdTailMass first second third 0 ∧
      equalFirstThirdBeforeSecondTailMass first second third start =
        equalFirstThirdBeforeSecondTailMass first second third 0 := by
  classical
  have hactive : ∃ time,
      first.stop time ≠ 0 ∨ second.stop time ≠ 0 ∨ third.stop time ≠ 0 := by
    by_contra hnone
    have hfirstZero : ∀ time, first.stop time = 0 := by
      intro time
      by_contra hne
      exact hnone ⟨time, Or.inl hne⟩
    have hmassZero : ∀ time, finiteMass (first.shift 0).stoppingLaw time = 0 := by
      intro time
      simp [finiteMass, stopMass, hfirstZero]
    have hzero : equalFirstSecondBeforeThirdTailMass first second third 0 = 0 := by
      simp only [equalFirstSecondBeforeThirdTailMass, equalFirstSecondBeforeThirdMass,
        hmassZero, zero_mul, tsum_zero]
    linarith
  let start := Nat.find hactive
  have hbefore : ∀ time < start,
      first.stop time = 0 ∧ second.stop time = 0 ∧ third.stop time = 0 := by
    intro time htime
    have hnot := Nat.find_min hactive htime
    simpa only [not_or, not_not] using hnot
  exact ⟨start, hbefore, Nat.find_spec hactive,
    overlappingTailMasses_eq_of_initial_zero first second third start hbefore⟩

/-- The three chronological equality configurations at the first active date.
The staggered cases retain a strictly later absolute date and its literal
normalized residual stopping laws, including the third clock's Never mass. -/
inductive OverlappingFirstStoppingBoundaryRow
    (first second third : ScalarHazard) (start : ℕ) : Prop
  | sameDate
      (hfirst : first.stop start = 1)
      (hsecond : second.stop start ∈ Set.Ioo (0 : ℝ) 1)
      (hthird : third.stop start = 1 - second.stop start)
  | firstSecondNow
      (hfirst : first.stop start ∈ Set.Ioo (0 : ℝ) 1)
      (hsecond : second.stop start = first.stop start)
      (hthird : third.stop start = 0)
      (later : ℕ) (hlater : start < later)
      (hfirstAtom : finiteMass (first.shift (start + 1)).stoppingLaw
        (later - (start + 1)) = 1)
      (hthirdAtom : finiteMass (third.shift (start + 1)).stoppingLaw
        (later - (start + 1)) = 1)
      (hsecondSurvival : StoppingLaw.survival (second.shift (start + 1)).stoppingLaw
        (later - (start + 1) + 1) = 1)
  | firstThirdNow
      (hfirst : first.stop start ∈ Set.Ioo (0 : ℝ) 1)
      (hsecond : second.stop start = 0)
      (hthird : third.stop start = first.stop start)
      (later : ℕ) (hlater : start < later)
      (hfirstAtom : finiteMass (first.shift (start + 1)).stoppingLaw
        (later - (start + 1)) = 1)
      (hsecondAtom : finiteMass (second.shift (start + 1)).stoppingLaw
        (later - (start + 1)) = 1)
      (hthirdSurvival : StoppingLaw.survival (third.shift (start + 1)).stoppingLaw
        (later - (start + 1) + 1) = 1)

/-- Positive overlapping boundary masses classify an active row completely,
with a deterministic later atom in each positive-continuation case. -/
theorem overlappingFirstStoppingBoundaryRow_of_active_of_equality
    (first second third : ScalarHazard) (start : ℕ)
    (hactive : first.stop start ≠ 0 ∨ second.stop start ≠ 0 ∨ third.stop start ≠ 0)
    (hfirstMass : 0 < equalFirstSecondBeforeThirdTailMass first second third start)
    (hsecondMass : 0 < equalFirstThirdBeforeSecondTailMass first second third start)
    (hequality : Real.sqrt (equalFirstSecondBeforeThirdTailMass first second third start) +
      Real.sqrt (equalFirstThirdBeforeSecondTailMass first second third start) = 1) :
    OverlappingFirstStoppingBoundaryRow first second third start := by
  have hfirstBound := first.stop_le_one start
  have hsecondBound := second.stop_le_one start
  have hthirdBound := third.stop_le_one start
  by_cases hcontinue : 0 < (1 - first.stop start) * (1 - second.stop start) *
      (1 - third.stop start)
  · have hfirstLt : first.stop start < 1 := by
      apply lt_of_le_of_ne hfirstBound
      intro h
      rw [h] at hcontinue
      norm_num at hcontinue
    rcases overlappingTailMasses_eq_one_step_of_continue_pos
      first second third start hcontinue hequality with hzero | hleft | hright
    · obtain ⟨hfirst, hsecond, hthird⟩ := hzero
      simp only [hfirst, hsecond, hthird, ne_eq, not_true_eq_false, or_self] at hactive
    · obtain ⟨hsecondZero, hthirdEq, hfuture, _⟩ := hleft
      have hfirstPos : 0 < first.stop start := by
        by_contra hnot
        have hzero : first.stop start = 0 :=
          le_antisymm (le_of_not_gt hnot) (first.stop_nonneg start)
        simp only [hsecondZero, hthirdEq, hzero, ne_eq, not_true_eq_false, or_self] at hactive
      obtain ⟨offset, hfirstAtom, hsecondAtom, hthirdSurvival⟩ :=
        exists_deterministicFiniteAtom_of_equalFirstSecondBeforeThirdMass_eq_one
          (first.shift (start + 1)).stoppingLaw (second.shift (start + 1)).stoppingLaw
          (third.shift (start + 1)).stoppingLaw hfuture
      have hindex : start + 1 + offset - (start + 1) = offset := by omega
      exact .firstThirdNow ⟨hfirstPos, hfirstLt⟩ hsecondZero hthirdEq
        (start + 1 + offset) (by omega)
        (by simpa only [hindex] using hfirstAtom)
        (by simpa only [hindex] using hsecondAtom)
        (by simpa only [hindex] using hthirdSurvival)
    · obtain ⟨hthirdZero, hsecondEq, _, hfuture⟩ := hright
      have hfirstPos : 0 < first.stop start := by
        by_contra hnot
        have hzero : first.stop start = 0 :=
          le_antisymm (le_of_not_gt hnot) (first.stop_nonneg start)
        simp only [hthirdZero, hsecondEq, hzero, ne_eq, not_true_eq_false, or_self] at hactive
      obtain ⟨offset, hfirstAtom, hthirdAtom, hsecondSurvival⟩ :=
        exists_deterministicFiniteAtom_of_equalFirstSecondBeforeThirdMass_eq_one
          (first.shift (start + 1)).stoppingLaw (third.shift (start + 1)).stoppingLaw
          (second.shift (start + 1)).stoppingLaw hfuture
      have hindex : start + 1 + offset - (start + 1) = offset := by omega
      exact .firstSecondNow ⟨hfirstPos, hfirstLt⟩ hsecondEq hthirdZero
        (start + 1 + offset) (by omega)
        (by simpa only [hindex] using hfirstAtom)
        (by simpa only [hindex] using hthirdAtom)
        (by simpa only [hindex] using hsecondSurvival)
  · have hcontinueZero : (1 - first.stop start) * (1 - second.stop start) *
        (1 - third.stop start) = 0 := by
      exact le_antisymm (le_of_not_gt hcontinue)
        (mul_nonneg (mul_nonneg (sub_nonneg.mpr hfirstBound)
          (sub_nonneg.mpr hsecondBound)) (sub_nonneg.mpr hthirdBound))
    have hfirstStep := equalFirstSecondBeforeThirdTailMass_succ first second third start
    have hsecondStep := equalFirstThirdBeforeSecondTailMass_succ first second third start
    rw [hcontinueZero, zero_mul, add_zero] at hfirstStep hsecondStep
    rw [hfirstStep] at hfirstMass
    rw [hsecondStep] at hsecondMass
    rw [hfirstStep, hsecondStep] at hequality
    obtain ⟨hfirstOne, hsum⟩ :=
      overlappingFirstStopping_oneRow_eq_one_of_commonContinue_zero
        ⟨first.stop_nonneg start, hfirstBound⟩
        ⟨second.stop_nonneg start, hsecondBound⟩
        ⟨third.stop_nonneg start, hthirdBound⟩
        hcontinueZero hfirstMass hsecondMass hequality
    have hsecondPos : 0 < second.stop start := by
      by_contra hnot
      have hzero : second.stop start = 0 :=
        le_antisymm (le_of_not_gt hnot) (second.stop_nonneg start)
      rw [hzero, mul_zero, zero_mul] at hfirstMass
      exact lt_irrefl 0 hfirstMass
    have hsecondLt : second.stop start < 1 := by
      apply lt_of_le_of_ne hsecondBound
      intro h
      rw [h, sub_self, mul_zero] at hsecondMass
      exact lt_irrefl 0 hsecondMass
    exact .sameDate hfirstOne ⟨hsecondPos, hsecondLt⟩ (by linarith)

/-- Every positive two-coordinate boundary law has an initial all-Continue
prefix followed by exactly one of the three chronological equality shapes. -/
theorem exists_first_active_boundaryRow_of_overlapping_equality
    (first second third : ScalarHazard)
    (hfirstMass : 0 < equalFirstSecondBeforeThirdTailMass first second third 0)
    (hsecondMass : 0 < equalFirstThirdBeforeSecondTailMass first second third 0)
    (hequality : Real.sqrt (equalFirstSecondBeforeThirdTailMass first second third 0) +
      Real.sqrt (equalFirstThirdBeforeSecondTailMass first second third 0) = 1) :
    ∃ start,
      (∀ time < start,
        first.stop time = 0 ∧ second.stop time = 0 ∧ third.stop time = 0) ∧
      OverlappingFirstStoppingBoundaryRow first second third start := by
  obtain ⟨start, hbefore, hactive, hfirstEq, hsecondEq⟩ :=
    exists_first_active_date_of_overlappingTailMass_pos first second third hfirstMass
  refine ⟨start, hbefore, overlappingFirstStoppingBoundaryRow_of_active_of_equality
    first second third start hactive ?_ ?_ ?_⟩
  · rwa [hfirstEq]
  · rwa [hsecondEq]
  · rwa [hfirstEq, hsecondEq]

private theorem firstTailMass_eq_zero_of_secondTailMass_eq_one
    (first second third : ScalarHazard) (start : ℕ)
    (hone : equalFirstThirdBeforeSecondTailMass first second third start = 1) :
    equalFirstSecondBeforeThirdTailMass first second third start = 0 := by
  have hbound := twoOverlappingFirstStoppingTailMasses_sqrt_sum_le_one
    first second third start
  rw [hone, Real.sqrt_one] at hbound
  have hnonneg := equalFirstSecondBeforeThirdMass_nonneg
    (first.shift start).stoppingLaw (second.shift start).stoppingLaw
      (third.shift start).stoppingLaw
  change 0 ≤ equalFirstSecondBeforeThirdTailMass first second third start at hnonneg
  nlinarith [Real.sqrt_nonneg
    (equalFirstSecondBeforeThirdTailMass first second third start), Real.sq_sqrt hnonneg]

private theorem secondTailMass_eq_zero_of_firstTailMass_eq_one
    (first second third : ScalarHazard) (start : ℕ)
    (hone : equalFirstSecondBeforeThirdTailMass first second third start = 1) :
    equalFirstThirdBeforeSecondTailMass first second third start = 0 :=
  firstTailMass_eq_zero_of_secondTailMass_eq_one first third second start hone

/-- Each chronological shape yields the complete sharp two-coordinate law,
with the orientation absorbed into the choice of the interior parameter. -/
theorem OverlappingFirstStoppingBoundaryRow.mass_coordinates
    {first second third : ScalarHazard} {start : ℕ}
    (hshape : OverlappingFirstStoppingBoundaryRow first second third start) :
    ∃ parameter : ℝ, parameter ∈ Set.Ioo (0 : ℝ) 1 ∧
      equalFirstSecondBeforeThirdTailMass first second third start = parameter ^ 2 ∧
      equalFirstThirdBeforeSecondTailMass first second third start = (1 - parameter) ^ 2 := by
  cases hshape with
  | sameDate hfirst hsecond hthird =>
      refine ⟨second.stop start, hsecond, ?_, ?_⟩
      · rw [equalFirstSecondBeforeThirdTailMass_succ, hfirst, hthird]
        ring
      · rw [equalFirstThirdBeforeSecondTailMass_succ, hfirst, hthird]
        ring
  | firstSecondNow hfirst hsecond hthird later _ hfirstAtom hthirdAtom hsecondSurvival =>
      have hsecondOne :
          equalFirstThirdBeforeSecondTailMass first second third (start + 1) = 1 :=
        equalFirstSecondBeforeThirdMass_eq_one_of_deterministicFiniteAtom
          (first.shift (start + 1)).stoppingLaw (third.shift (start + 1)).stoppingLaw
          (second.shift (start + 1)).stoppingLaw (later - (start + 1))
          hfirstAtom hthirdAtom hsecondSurvival
      have hfirstZero := firstTailMass_eq_zero_of_secondTailMass_eq_one
        first second third (start + 1) hsecondOne
      refine ⟨first.stop start, hfirst, ?_, ?_⟩
      · rw [equalFirstSecondBeforeThirdTailMass_succ, hsecond, hthird, hfirstZero]
        ring
      · rw [equalFirstThirdBeforeSecondTailMass_succ, hsecond, hthird, hsecondOne]
        ring
  | firstThirdNow hfirst hsecond hthird later _ hfirstAtom hsecondAtom hthirdSurvival =>
      have hfirstOne :
          equalFirstSecondBeforeThirdTailMass first second third (start + 1) = 1 :=
        equalFirstSecondBeforeThirdMass_eq_one_of_deterministicFiniteAtom
          (first.shift (start + 1)).stoppingLaw (second.shift (start + 1)).stoppingLaw
          (third.shift (start + 1)).stoppingLaw (later - (start + 1))
          hfirstAtom hsecondAtom hthirdSurvival
      have hsecondZero := secondTailMass_eq_zero_of_firstTailMass_eq_one
        first second third (start + 1) hfirstOne
      refine ⟨1 - first.stop start, ⟨by linarith [hfirst.2], by linarith [hfirst.1]⟩,
        ?_, ?_⟩
      · rw [equalFirstSecondBeforeThirdTailMass_succ, hsecond, hthird, hfirstOne]
        ring
      · rw [equalFirstThirdBeforeSecondTailMass_succ, hsecond, hthird, hsecondZero]
        ring

/-- Exact positive equality classification for arbitrary scalar hazards.
Initial silent dates and all irrelevant tails remain unrestricted. -/
theorem positive_overlapping_equality_iff_initial_zero_boundaryRow
    (first second third : ScalarHazard) :
    (0 < equalFirstSecondBeforeThirdTailMass first second third 0 ∧
      0 < equalFirstThirdBeforeSecondTailMass first second third 0 ∧
      Real.sqrt (equalFirstSecondBeforeThirdTailMass first second third 0) +
        Real.sqrt (equalFirstThirdBeforeSecondTailMass first second third 0) = 1) ↔
    ∃ start,
      (∀ time < start,
        first.stop time = 0 ∧ second.stop time = 0 ∧ third.stop time = 0) ∧
      OverlappingFirstStoppingBoundaryRow first second third start := by
  constructor
  · rintro ⟨hfirst, hsecond, hequality⟩
    exact exists_first_active_boundaryRow_of_overlapping_equality
      first second third hfirst hsecond hequality
  · rintro ⟨start, hbefore, hshape⟩
    obtain ⟨parameter, hparameter, hfirst, hsecond⟩ := hshape.mass_coordinates
    have hprefix := overlappingTailMasses_eq_of_initial_zero first second third start hbefore
    rw [hprefix.1] at hfirst
    rw [hprefix.2] at hsecond
    rw [hfirst, hsecond]
    refine ⟨sq_pos_of_pos hparameter.1, sq_pos_of_pos (by linarith [hparameter.2]), ?_⟩
    rw [Real.sqrt_sq_eq_abs, Real.sqrt_sq_eq_abs, abs_of_pos hparameter.1,
      abs_of_pos (by linarith [hparameter.2] : 0 < 1 - parameter)]
    ring

private theorem stoppingLaw_shift_zero (hazard : ScalarHazard) :
    (hazard.shift 0).stoppingLaw = hazard.stoppingLaw := by
  have heq : hazard.shift 0 = hazard := by
    apply eq_of_stop_eq
    funext time
    simp
  rw [heq]

end Math.Probability.DiscreteHazard.ScalarHazard

namespace Math.Probability.DiscreteHazard.StoppingLaw

open ScalarHazard

/-- The positive chronological classification for the original complete PMFs,
using their canonical reconstructed hazards. -/
theorem positive_overlappingMass_equality_iff_initial_zero_boundaryRow
    (first second third : PMF (Option ℕ)) :
    (0 < equalFirstSecondBeforeThirdMass first second third ∧
      0 < equalFirstThirdBeforeSecondMass first second third ∧
      Real.sqrt (equalFirstSecondBeforeThirdMass first second third) +
        Real.sqrt (equalFirstThirdBeforeSecondMass first second third) = 1) ↔
    ∃ start,
      (∀ time < start,
        (toScalarHazard first).stop time = 0 ∧
        (toScalarHazard second).stop time = 0 ∧
        (toScalarHazard third).stop time = 0) ∧
      OverlappingFirstStoppingBoundaryRow
        (toScalarHazard first) (toScalarHazard second) (toScalarHazard third) start := by
  simpa only [equalFirstSecondBeforeThirdTailMass, equalFirstThirdBeforeSecondTailMass,
    stoppingLaw_shift_zero, stoppingLaw_toScalarHazard] using
    positive_overlapping_equality_iff_initial_zero_boundaryRow
      (toScalarHazard first) (toScalarHazard second) (toScalarHazard third)

/-- Complete boundary equality classification, including both degenerate
mass-one endpoints and all three positive chronological configurations. -/
theorem overlappingMass_sqrt_sum_eq_one_iff_deterministic_or_chronological
    (first second third : PMF (Option ℕ)) :
    (Real.sqrt (equalFirstSecondBeforeThirdMass first second third) +
      Real.sqrt (equalFirstThirdBeforeSecondMass first second third) = 1) ↔
    (∃ time, finiteMass first time = 1 ∧ finiteMass second time = 1 ∧
      survival third (time + 1) = 1) ∨
    (∃ time, finiteMass first time = 1 ∧ finiteMass third time = 1 ∧
      survival second (time + 1) = 1) ∨
    (∃ start,
      (∀ time < start,
        (toScalarHazard first).stop time = 0 ∧
        (toScalarHazard second).stop time = 0 ∧
        (toScalarHazard third).stop time = 0) ∧
      OverlappingFirstStoppingBoundaryRow
        (toScalarHazard first) (toScalarHazard second) (toScalarHazard third) start) := by
  have hfirstNonneg := equalFirstSecondBeforeThirdMass_nonneg first second third
  have hsecondNonneg := equalFirstThirdBeforeSecondMass_nonneg first second third
  constructor
  · intro hequality
    by_cases hfirstZero : equalFirstSecondBeforeThirdMass first second third = 0
    · have hsecondOne : equalFirstThirdBeforeSecondMass first second third = 1 := by
        rw [hfirstZero, Real.sqrt_zero, zero_add] at hequality
        nlinarith [Real.sq_sqrt hsecondNonneg]
      exact Or.inr (Or.inl
        ((equalFirstThirdBeforeSecondMass_eq_one_iff_deterministicFiniteAtom
          first second third).mp hsecondOne))
    by_cases hsecondZero : equalFirstThirdBeforeSecondMass first second third = 0
    · have hfirstOne : equalFirstSecondBeforeThirdMass first second third = 1 := by
        rw [hsecondZero, Real.sqrt_zero, add_zero] at hequality
        nlinarith [Real.sq_sqrt hfirstNonneg]
      exact Or.inl
        ((equalFirstSecondBeforeThirdMass_eq_one_iff_deterministicFiniteAtom
          first second third).mp hfirstOne)
    · exact Or.inr (Or.inr
        ((positive_overlappingMass_equality_iff_initial_zero_boundaryRow
          first second third).mp
            ⟨hfirstNonneg.lt_of_ne' hfirstZero, hsecondNonneg.lt_of_ne' hsecondZero,
              hequality⟩))
  · intro hclassification
    have hupper := twoOverlappingFirstStoppingMasses_sqrt_sum_le_one first second third
    rcases hclassification with hfirst | hsecond | hpositive
    · have hone := (equalFirstSecondBeforeThirdMass_eq_one_iff_deterministicFiniteAtom
        first second third).mpr hfirst
      rw [hone, Real.sqrt_one] at hupper ⊢
      linarith [Real.sqrt_nonneg (equalFirstThirdBeforeSecondMass first second third)]
    · have hone := (equalFirstThirdBeforeSecondMass_eq_one_iff_deterministicFiniteAtom
        first second third).mpr hsecond
      rw [hone, Real.sqrt_one] at hupper ⊢
      linarith [Real.sqrt_nonneg (equalFirstSecondBeforeThirdMass first second third)]
    · exact ((positive_overlappingMass_equality_iff_initial_zero_boundaryRow
        first second third).mpr hpositive).2.2

end Math.Probability.DiscreteHazard.StoppingLaw
