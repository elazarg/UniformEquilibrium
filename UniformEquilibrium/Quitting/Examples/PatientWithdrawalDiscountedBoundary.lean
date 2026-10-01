import UniformEquilibrium.Quitting.Examples.PatientWithdrawalFiniteHorizonBoundary
import UniformEquilibrium.Quitting.Paths.EvaluatedPureTimeCap
import UniformEquilibrium.Quitting.Paths.DiscountedStoppingLawPayoff

/-! # A patient certificate with a literal discounted-law violation

This uses the canonical clock-law evaluation d^(t+1), whose actual-history
stage-series identification is owned by DiscountedStoppingLawPayoff. The actual child profile,
its canonical Never lift, and the complete behavioral response class are the
same as in the horizon-three example. The patient certificate remains terminal-only.
-/

noncomputable section

namespace GameTheory.PatientWithdrawalDiscountedBoundary

open scoped BigOperators
open _root_.Math.Probability Math.PMFProduct
open PatientWithdrawalFiniteHorizonBoundary

private local instance : Nonempty Survivor := ⟨⟨some 0, by simp⟩⟩

/-- Absorption at date t is evaluated with weight d^(t+1); Never has weight zero. -/
abbrev discountEvaluation (d : ℝ) : WithTop ℕ → ℝ :=
  quittingDiscountedEvaluation d

@[simp] theorem discountEvaluation_top (d : ℝ) : discountEvaluation d ⊤ = 0 := rfl

@[simp] theorem discountEvaluation_coe (d : ℝ) (time : ℕ) :
    discountEvaluation d time = d ^ (time + 1) := rfl

theorem discountEvaluation_nonneg (d : ℝ) (hd : 0 ≤ d) (clock : WithTop ℕ) :
    0 ≤ discountEvaluation d clock :=
  quittingDiscountedEvaluation_nonneg d hd clock

theorem discountEvaluation_le_one (d : ℝ) (hd : 0 ≤ d) (hdone : d ≤ 1)
    (clock : WithTop ℕ) : discountEvaluation d clock ≤ 1 :=
  quittingDiscountedEvaluation_le_one d hd hdone clock

theorem discountEvaluation_antitone (d : ℝ) (hd : 0 ≤ d) (hdone : d ≤ 1) :
    Antitone (discountEvaluation d) :=
  quittingDiscountedEvaluation_antitone d hd hdone

private def reply (d : ℝ) (who : Player) (choice : Option ℕ) : ℝ :=
  quittingStoppingLawEvaluatedPayoff reward (discountEvaluation d)
    (Function.update (fun player => PMF.pure (clocks player)) who (PMF.pure choice)) who

private theorem reply_eq_pure (d : ℝ) (who : Player) (choice : Option ℕ) :
    reply d who choice = quittingPureClockEvaluatedPayoff reward (discountEvaluation d)
      (Function.update clocks who choice) who := by
  have hfamily : Function.update (fun player => PMF.pure (clocks player)) who
      (PMF.pure choice) = fun player => PMF.pure ((Function.update clocks who choice) player) :=
    by funext player; by_cases hplayer : player = who <;> simp [hplayer]
  unfold reply quittingStoppingLawEvaluatedPayoff
  rw [hfamily, pmfPi_pure, expect_pure]

/-- All child responses, including every late date and Never, have these actual values. -/
theorem child_reply_eq (d : ℝ) (choice : Option ℕ) :
    reply d (some 0) choice = if choice = some 0 then d
      else if choice = some 1 then d ^ 2 else 2 * d ^ 2 := by
  rw [reply_eq_pure, pureClock_child_reply]
  have hzero : discountEvaluation d (0 : WithTop ℕ) = d := by
    change d ^ 1 = d
    exact pow_one d
  have hone : discountEvaluation d (1 : WithTop ℕ) = d ^ 2 := rfl
  rw [hzero, hone]

/-- All outsider responses have the actual values d, d², or zero. -/
theorem outside_reply_eq (d : ℝ) (choice : Option ℕ) :
    reply d none choice = if choice = some 0 then d
      else if choice = some 1 then d ^ 2 else 0 := by
  rw [reply_eq_pure, pureClock_outside_reply]
  have hzero : discountEvaluation d (0 : WithTop ℕ) = d := by
    change d ^ 1 = d
    exact pow_one d
  have hone : discountEvaluation d (1 : WithTop ℕ) = d ^ 2 := rfl
  rw [hzero, hone]

private theorem cap_eq_of_reply (d : ℝ) (hd : 0 ≤ d) (hdone : d ≤ 1)
    (who : Player) (bound : ℝ) (choice : Option ℕ)
    (hbound : ∀ other, reply d who other ≤ bound) (hattains : reply d who choice = bound) :
    quittingBehaviorEvaluatedDeviationPayoffCap reward (discountEvaluation d)
      liftedProfile who = bound := by
  rw [quittingBehaviorEvaluatedDeviationPayoffCap_eq_pureTime reward (discountEvaluation d)
    (discountEvaluation_nonneg d hd) (discountEvaluation_le_one d hd hdone),
    liftedProfile_stoppingLaws]
  change sSup (Set.range (reply d who)) = bound
  have hbounded : BddAbove (Set.range (reply d who)) := by
    refine ⟨bound, ?_⟩
    rintro _ ⟨other, rfl⟩
    exact hbound other
  apply le_antisymm
  · apply csSup_le
    · exact ⟨reply d who none, ⟨none, rfl⟩⟩
    · rintro _ ⟨other, rfl⟩
      exact hbound other
  · rw [← hattains]
    exact le_csSup hbounded ⟨choice, rfl⟩

/-- Exact unrestricted behavioral caps of the SAME actual lifted profile. -/
theorem discounted_caps (d : ℝ) (hd : 0 < d) (hdone : d < 1) :
    quittingBehaviorEvaluatedDeviationPayoffCap reward (discountEvaluation d)
        liftedProfile (some 0) = max d (2 * d ^ 2) ∧
      quittingBehaviorEvaluatedDeviationPayoffCap reward (discountEvaluation d)
        liftedProfile none = d := by
  have hproduct : 0 < d * (1 - d) := mul_pos hd (sub_pos.mpr hdone)
  have hsquare : d ^ 2 ≤ d := by nlinarith
  have hchild : ∀ choice, reply d (some 0) choice ≤ max d (2 * d ^ 2) := by
    intro choice
    rw [child_reply_eq]
    split_ifs
    · exact le_max_left _ _
    · exact (by nlinarith [sq_nonneg d] : d ^ 2 ≤ 2 * d ^ 2).trans (le_max_right _ _)
    · exact le_max_right _ _
  constructor
  · by_cases horder : d ≤ 2 * d ^ 2
    · apply cap_eq_of_reply d hd.le hdone.le (some 0) _ none hchild
      rw [child_reply_eq, max_eq_right horder]
      simp
    · apply cap_eq_of_reply d hd.le hdone.le (some 0) _ (some 0) hchild
      rw [child_reply_eq, max_eq_left (le_of_not_ge horder)]
      simp
  · apply cap_eq_of_reply d hd.le hdone.le none d (some 0)
    · intro choice
      rw [outside_reply_eq]
      split_ifs <;> first | exact le_rfl | exact hsquare | exact hd.le
    · simp [outside_reply_eq]

/-- Actual prescribed discounted values: child zero d², quiet outsider zero. -/
theorem discounted_payoffs (d : ℝ) :
    quittingBehaviorEvaluatedPayoff reward (discountEvaluation d) liftedProfile (some 0) = d ^ 2 ∧
      quittingBehaviorEvaluatedPayoff reward (discountEvaluation d) liftedProfile none = 0 := by
  have hvalue (who : Player) :
      quittingBehaviorEvaluatedPayoff reward (discountEvaluation d) liftedProfile who =
        quittingPureClockEvaluatedPayoff reward (discountEvaluation d) clocks who := by
    rw [quittingBehaviorEvaluatedPayoff, liftedProfile_stoppingLaws]
    unfold quittingStoppingLawEvaluatedPayoff
    rw [pmfPi_pure, expect_pure]
  constructor
  · rw [hvalue, (pureClock_prescribed_payoffs _).1]
    rfl
  · rw [hvalue, (pureClock_prescribed_payoffs _).2]

/-- Actual deleted-child debt, derived by exact deletion naturality. -/
theorem child_discounted_debt (d : ℝ) (hd : 0 < d) (hdone : d < 1) :
    quittingBehaviorEvaluatedDeviationPayoffCap (quittingDeleteReward reward (· = none))
        (discountEvaluation d) childProfile ⟨some 0, by simp⟩ -
      quittingBehaviorEvaluatedPayoff (quittingDeleteReward reward (· = none))
        (discountEvaluation d) childProfile ⟨some 0, by simp⟩ = max (d - d ^ 2) (d ^ 2) := by
  have hcap := quittingBehaviorEvaluatedDeviationPayoffCap_liftDeletedProfile
    (deleted := (· = none)) reward (discountEvaluation d) childProfile ⟨some 0, by simp⟩
  have hpayoff := quittingBehaviorEvaluatedPayoff_liftDeletedProfile
    (deleted := (· = none)) reward (discountEvaluation d) childProfile ⟨some 0, by simp⟩
  rw [← hcap, ← hpayoff]
  change quittingBehaviorEvaluatedDeviationPayoffCap reward (discountEvaluation d)
      liftedProfile (some 0) -
    quittingBehaviorEvaluatedPayoff reward (discountEvaluation d) liftedProfile (some 0) = _
  rw [(discounted_caps d hd hdone).1, (discounted_payoffs d).1, ← max_sub_sub_right]
  congr 1
  ring

/-- For every 0<d<1 the outsider law debt exceeds the patient weighted child debt.
The literal stage-series restatement is in PatientWithdrawalDiscountedStageBoundary.
This is not a failure of terminal protection. -/
theorem patient_discounted_bound_fails (d : ℝ) (hd : 0 < d) (hdone : d < 1) :
    (∑ i : Child, (certificate.advanceWeight i + certificate.withdrawalWeight i) *
      (quittingBehaviorEvaluatedDeviationPayoffCap (quittingDeleteReward reward (· = none))
          (discountEvaluation d) childProfile ⟨some i, Option.some_ne_none i⟩ -
        quittingBehaviorEvaluatedPayoff (quittingDeleteReward reward (· = none))
          (discountEvaluation d) childProfile ⟨some i, Option.some_ne_none i⟩)) <
      quittingBehaviorEvaluatedDeviationPayoffCap reward (discountEvaluation d)
          liftedProfile none -
        quittingBehaviorEvaluatedPayoff reward (discountEvaluation d) liftedProfile none := by
  simp only [certificate, Pi.zero_apply, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, zero_add, one_mul, zero_mul, add_zero]
  rw [child_discounted_debt d hd hdone, (discounted_caps d hd hdone).2,
    (discounted_payoffs d).2, sub_zero]
  apply max_lt
  · nlinarith [sq_pos_of_pos hd]
  · nlinarith [mul_pos hd (sub_pos.mpr hdone)]

end GameTheory.PatientWithdrawalDiscountedBoundary
