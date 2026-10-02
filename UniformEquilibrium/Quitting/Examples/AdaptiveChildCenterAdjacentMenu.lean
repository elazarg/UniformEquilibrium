import UniformEquilibrium.Quitting.Examples.AdaptiveChildCenterRestrictionPayoff

/-! # Exact adjacent-date menu difference after deleting the anchor

Every opponent atom before K cancels. No assumption is made about clocks
strictly after K or about their Never mass.
-/

noncomputable section

namespace GameTheory.AdaptiveChildCenter

open _root_.Math.Probability _root_.Math.ProbabilityMassFunction Math.PMFProduct
open _root_.Math.Probability.DiscreteHazard.StoppingLaw

def childClockPayoff (deleted : Fin 4) (times : Fin 3 → Option ℕ) (who : Fin 3) : ℝ :=
  quittingTerminalOutcomeReward (childReward deleted) (quittingFirstStoppingOutcome times) who

theorem childClockPayoff_abs_le_two (deleted : Fin 4) (times : Fin 3 → Option ℕ)
    (who : Fin 3) : |childClockPayoff deleted times who| ≤ 2 := by
  unfold childClockPayoff
  cases quittingFirstStoppingOutcome times with
  | none => norm_num [quittingTerminalOutcomeReward]
  | some terminal => exact childReward_abs_le_two deleted terminal who

private theorem value_lt_of_before (choice : Option ℕ) (cutoff : ℕ)
    (hbefore : ¬survivesUntil cutoff choice) :
    quittingStoppingTimeValue choice < quittingStoppingTimeValue (some cutoff) := by
  cases choice with
  | none => simp [survivesUntil] at hbefore
  | some time =>
      have htime : time < cutoff := by simpa [survivesUntil] using hbefore
      simpa [quittingStoppingTimeValue] using htime

private theorem value_gt_of_survival_ne (choice : Option ℕ) (cutoff : ℕ)
    (hsurvival : survivesUntil cutoff choice) (hne : choice ≠ some cutoff) :
    quittingStoppingTimeValue (some cutoff) < quittingStoppingTimeValue choice := by
  cases choice with
  | none => simp [quittingStoppingTimeValue]
  | some time =>
      have htime : cutoff ≤ time := hsurvival
      have htimeNe : time ≠ cutoff := by simpa using hne
      have hstrict : cutoff < time := by omega
      simpa [quittingStoppingTimeValue] using hstrict

private theorem firstOutcome_at_date (times : Fin 3 → Option ℕ) (cutoff : ℕ)
    (hsurvival : ∀ who, survivesUntil cutoff (times who))
    (owner : Fin 3) (howner : times owner = some cutoff) :
    quittingFirstStoppingOutcome times =
      some ⟨Finset.univ.filter (fun who => times who = some cutoff),
        ⟨owner, by simp [howner]⟩⟩ := by
  apply quittingFirstStoppingOutcome_eq_coalition_of_strictly_later
  · intro who hwho
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hwho
  · intro who hwho
    apply value_gt_of_survival_ne _ cutoff (hsurvival who)
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hwho

private theorem childClockPayoff_three_zero_of_owner
    (times : Fin 3 → Option ℕ) (cutoff : ℕ)
    (hsurvival : ∀ who, survivesUntil cutoff (times who)) (hzero : times 0 = some cutoff) :
    childClockPayoff 3 times 0 = 1 := by
  rw [childClockPayoff, firstOutcome_at_date times cutoff hsurvival 0 hzero]
  simp [quittingTerminalOutcomeReward, childReward_three_zero, hzero]

private theorem adjacent_clockPayoff_eq_of_before
    (times : Fin 3 → Option ℕ) (cutoff : ℕ) (opponent : Fin 3) (hne : opponent ≠ 0)
    (hbefore : ¬survivesUntil cutoff (times opponent)) :
    childClockPayoff 3 (Function.update times 0 (some (cutoff + 1))) 0 =
      childClockPayoff 3 (Function.update times 0 (some cutoff)) 0 := by
  have hbeforeValue := value_lt_of_before (times opponent) cutoff hbefore
  have hbeforeNext : quittingStoppingTimeValue (times opponent) <
      quittingStoppingTimeValue (some (cutoff + 1)) :=
    hbeforeValue.trans (WithTop.coe_lt_coe.mpr (Nat.lt_succ_self cutoff))
  have hfirst := quittingFirstStoppingOutcome_eq_of_earlier_stopper
    (Function.update times 0 (some (cutoff + 1)))
    (Function.update times 0 (some cutoff)) (hidden := 0) (blocker := opponent)
    (fun who hwho => by simp [hwho])
    (by simpa [hne] using hbeforeNext) (by simpa [hne] using hbeforeValue)
  exact congrArg (fun outcome => quittingTerminalOutcomeReward (childReward 3) outcome 0) hfirst

open Classical in
/-- Pointwise payoff difference, written as three independent pair events. -/
theorem adjacent_child_clockPayoff_difference (times : Fin 3 → Option ℕ) (cutoff : ℕ) :
    childClockPayoff 3 (Function.update times 0 (some (cutoff + 1))) 0 -
        childClockPayoff 3 (Function.update times 0 (some cutoff)) 0 =
      (if survivesUntil cutoff (times 1) ∧ times 2 = some cutoff then 1 else 0) -
        (if times 1 = some cutoff ∧ survivesUntil cutoff (times 2) then 1 else 0) +
        (if times 1 = some cutoff ∧ times 2 = some cutoff then 1 else 0) := by
  classical
  by_cases hfirst : survivesUntil cutoff (times 1)
  · by_cases hsecond : survivesUntil cutoff (times 2)
    · have hnow : childClockPayoff 3 (Function.update times 0 (some cutoff)) 0 = 1 := by
        apply childClockPayoff_three_zero_of_owner _ cutoff
        · intro who
          fin_cases who
          · simp [survivesUntil]
          · simpa using hfirst
          · simpa using hsecond
        · simp
      rw [hnow]
      simp only [hfirst, hsecond, true_and, and_true]
      by_cases hfirstAtom : times 1 = some cutoff
      · have hsurvival : ∀ who,
            survivesUntil cutoff ((Function.update times 0 (some (cutoff + 1))) who) := by
          intro who
          fin_cases who
          · simp [survivesUntil]
          · simp [survivesUntil, hfirstAtom]
          · simpa using hsecond
        rw [childClockPayoff, firstOutcome_at_date _ cutoff hsurvival 1 (by simp [hfirstAtom])]
        by_cases hsecondAtom : times 2 = some cutoff <;>
          norm_num [quittingTerminalOutcomeReward, childReward_three_zero,
            hfirstAtom, hsecondAtom]
      · by_cases hsecondAtom : times 2 = some cutoff
        · have hsurvival : ∀ who,
              survivesUntil cutoff ((Function.update times 0 (some (cutoff + 1))) who) := by
            intro who
            fin_cases who
            · simp [survivesUntil]
            · simpa using hfirst
            · simp [survivesUntil, hsecondAtom]
          rw [childClockPayoff, firstOutcome_at_date _ cutoff hsurvival 2
            (by simp [hsecondAtom])]
          norm_num [quittingTerminalOutcomeReward, childReward_three_zero,
            hfirstAtom, hsecondAtom]
        · have hnext (choice : Option ℕ) (hs : survivesUntil cutoff choice)
              (ha : choice ≠ some cutoff) : survivesUntil (cutoff + 1) choice := by
            cases choice with
            | none => trivial
            | some time =>
                have htime : cutoff ≤ time := hs
                have htimeNe : time ≠ cutoff := by simpa using ha
                change cutoff + 1 ≤ time
                omega
          have hnextPayoff :
              childClockPayoff 3 (Function.update times 0 (some (cutoff + 1))) 0 = 1 := by
            apply childClockPayoff_three_zero_of_owner _ (cutoff + 1)
            · intro who
              fin_cases who
              · simp [survivesUntil]
              · simpa using hnext _ hfirst hfirstAtom
              · simpa using hnext _ hsecond hsecondAtom
            · simp
          simp [hnextPayoff, hfirstAtom, hsecondAtom]
    · have hsecondAtom : times 2 ≠ some cutoff := by
        intro heq
        apply hsecond
        simp [heq, survivesUntil]
      rw [adjacent_clockPayoff_eq_of_before times cutoff 2 (by decide) hsecond]
      simp [hfirst, hsecond, hsecondAtom]
  · have hfirstAtom : times 1 ≠ some cutoff := by
      intro heq
      apply hfirst
      simp [heq, survivesUntil]
    rw [adjacent_clockPayoff_eq_of_before times cutoff 1 (by decide) hfirst]
    simp [hfirst, hfirstAtom]

/-- The actual unrestricted child menu has the exact division-free formula. -/
theorem adjacent_child_menu_difference_raw
    (child : (quittingGame (childReward 3)).BehaviorProfile) (cutoff : ℕ) :
    quittingBehaviorPureTimePayoff (childReward 3) child 0 (some (cutoff + 1)) -
        quittingBehaviorPureTimePayoff (childReward 3) child 0 (some cutoff) =
      survival (quittingBehaviorStoppingLaws (childReward 3) child 1) cutoff *
          finiteMass (quittingBehaviorStoppingLaws (childReward 3) child 2) cutoff -
        finiteMass (quittingBehaviorStoppingLaws (childReward 3) child 1) cutoff *
          survival (quittingBehaviorStoppingLaws (childReward 3) child 2) cutoff +
        finiteMass (quittingBehaviorStoppingLaws (childReward 3) child 1) cutoff *
          finiteMass (quittingBehaviorStoppingLaws (childReward 3) child 2) cutoff := by
  classical
  let laws := quittingBehaviorStoppingLaws (childReward 3) child
  let joint := pmfPi laws
  let first : (Fin 3 → Option ℕ) → ℝ := fun times =>
    if survivesUntil cutoff (times 1) ∧ times 2 = some cutoff then 1 else 0
  let second : (Fin 3 → Option ℕ) → ℝ := fun times =>
    if times 1 = some cutoff ∧ survivesUntil cutoff (times 2) then 1 else 0
  let third : (Fin 3 → Option ℕ) → ℝ := fun times =>
    if times 1 = some cutoff ∧ times 2 = some cutoff then 1 else 0
  have hfirstBound : ∀ times, |first times| ≤ 1 := by
    intro times
    dsimp only [first]
    split_ifs <;> norm_num
  have hsecondBound : ∀ times, |second times| ≤ 1 := by
    intro times
    dsimp only [second]
    split_ifs <;> norm_num
  have hthirdBound : ∀ times, |third times| ≤ 1 := by
    intro times
    dsimp only [third]
    split_ifs <;> norm_num
  rw [quittingBehaviorPureTimePayoff_eq_expect_overwrite,
    quittingBehaviorPureTimePayoff_eq_expect_overwrite]
  change expect joint (fun times =>
    childClockPayoff 3 (Function.update times 0 (some (cutoff + 1))) 0) -
    expect joint (fun times => childClockPayoff 3 (Function.update times 0 (some cutoff)) 0) = _
  rw [← expect_sub_of_abs_bounds _ _ _ (fun _ => childClockPayoff_abs_le_two 3 _ 0)
    (fun _ => childClockPayoff_abs_le_two 3 _ 0)]
  simp_rw [adjacent_child_clockPayoff_difference]
  change expect joint (fun times => (first times - second times) + third times) = _
  have hfirstSummable := expect_summable_of_bounded joint first hfirstBound
  have hsecondSummable := expect_summable_of_bounded joint second hsecondBound
  have hdifferenceSummable := hfirstSummable.sub hsecondSummable
  have hsum := expect_add_of_summable joint
    (fun times => first times - second times) third
    (by simpa only [mul_sub] using hdifferenceSummable)
    (expect_summable_of_bounded joint third hthirdBound)
  rw [hsum, expect_sub_of_abs_bounds joint first second hfirstBound hsecondBound]
  have hfirstMass : expect joint first = (pmfMass (pmfPi laws)
      (fun times => survivesUntil cutoff (times 1) ∧ times 2 = some cutoff)).toReal := by
    convert expect_indicator_eq_pmfMass_toReal (pmfPi laws)
      (fun times => survivesUntil cutoff (times 1) ∧ times 2 = some cutoff) using 1
    apply congrArg (expect joint)
    funext times
    dsimp only [first]
    by_cases hevent : survivesUntil cutoff (times 1) ∧ times 2 = some cutoff
    · simp only [ite_eq_left hevent]
    · simp only [ite_eq_right hevent]
  have hsecondMass : expect joint second = (pmfMass (pmfPi laws)
      (fun times => times 1 = some cutoff ∧ survivesUntil cutoff (times 2))).toReal := by
    convert expect_indicator_eq_pmfMass_toReal (pmfPi laws)
      (fun times => times 1 = some cutoff ∧ survivesUntil cutoff (times 2)) using 1
    apply congrArg (expect joint)
    funext times
    dsimp only [second]
    by_cases hevent : times 1 = some cutoff ∧ survivesUntil cutoff (times 2)
    · simp only [ite_eq_left hevent]
    · simp only [ite_eq_right hevent]
  have hthirdMass : expect joint third = (pmfMass (pmfPi laws)
      (fun times => times 1 = some cutoff ∧ times 2 = some cutoff)).toReal := by
    convert expect_indicator_eq_pmfMass_toReal (pmfPi laws)
      (fun times => times 1 = some cutoff ∧ times 2 = some cutoff) using 1
    apply congrArg (expect joint)
    funext times
    dsimp only [third]
    by_cases hevent : times 1 = some cutoff ∧ times 2 = some cutoff
    · simp only [ite_eq_left hevent]
    · simp only [ite_eq_right hevent]
  rw [hfirstMass, hsecondMass, hthirdMass,
    pmfMass_pmfPi_pair_arbitrary laws 1 2 (by decide)
      (survivesUntil cutoff) (fun choice => choice = some cutoff),
    pmfMass_pmfPi_pair_arbitrary laws 1 2 (by decide)
      (fun choice => choice = some cutoff) (survivesUntil cutoff),
    pmfMass_pmfPi_pair_arbitrary laws 1 2 (by decide)
      (fun choice => choice = some cutoff) (fun choice => choice = some cutoff)]
  simp only [ENNReal.toReal_mul, pmfMass_survivesUntil_toReal, pmfMass_singleton,
    finiteMass, laws]

/-- The packet's conditional formula, with only the displayed denominators
positive. Such positivity is supplied internally by quantile rigidity. -/
theorem adjacent_child_menu_difference
    (child : (quittingGame (childReward 3)).BehaviorProfile) (cutoff : ℕ)
    (hfirst : 0 < survival (quittingBehaviorStoppingLaws (childReward 3) child 1) cutoff)
    (hsecond : 0 < survival (quittingBehaviorStoppingLaws (childReward 3) child 2) cutoff) :
    quittingBehaviorPureTimePayoff (childReward 3) child 0 (some (cutoff + 1)) -
        quittingBehaviorPureTimePayoff (childReward 3) child 0 (some cutoff) =
      survival (quittingBehaviorStoppingLaws (childReward 3) child 1) cutoff *
        survival (quittingBehaviorStoppingLaws (childReward 3) child 2) cutoff *
        (finiteMass (quittingBehaviorStoppingLaws (childReward 3) child 2) cutoff /
            survival (quittingBehaviorStoppingLaws (childReward 3) child 2) cutoff -
          finiteMass (quittingBehaviorStoppingLaws (childReward 3) child 1) cutoff /
            survival (quittingBehaviorStoppingLaws (childReward 3) child 1) cutoff +
          (finiteMass (quittingBehaviorStoppingLaws (childReward 3) child 1) cutoff /
            survival (quittingBehaviorStoppingLaws (childReward 3) child 1) cutoff) *
          (finiteMass (quittingBehaviorStoppingLaws (childReward 3) child 2) cutoff /
            survival (quittingBehaviorStoppingLaws (childReward 3) child 2) cutoff)) := by
  rw [adjacent_child_menu_difference_raw]
  field_simp [hfirst.ne', hsecond.ne']

end GameTheory.AdaptiveChildCenter
