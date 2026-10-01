import UniformEquilibrium.Quitting.Paths.FiniteHorizonPureTimeCap
import UniformEquilibrium.Quitting.Classification.PlayerDeletionEvaluatedPayoff
import UniformEquilibrium.Quitting.Classification.QuietExtension.CappedClockChildDeletionAdapter
import UniformEquilibrium.Quitting.Classification.QuietExtension.PatientWithdrawalRaw
import Mathlib.Tactic.FinCases

/-! # A patient terminal certificate with a literal horizon-three violation

The actual deleted child uses independent sure clocks at date one, and the
actual parent is its canonical Never lift. Full finite-horizon caps are derived
from all complete behavioral replacements, not a chosen finite menu.
The valid raw patient certificate protects terminal payoff only.
-/

noncomputable section

namespace GameTheory.PatientWithdrawalFiniteHorizonBoundary

open scoped BigOperators
open _root_.Math.Probability Math.PMFProduct

abbrev Child := Fin 2
abbrev Player := Option Child
abbrev Survivor := {who : Player // ¬ who = none}

local instance : Nonempty Survivor := ⟨⟨some 0, by simp⟩⟩

/-- Complete seven-row table; the quiet outsider receives zero only at {0,1}. -/
def reward (terminal : {A : Finset Player // A.Nonempty}) (who : Player) : ℝ :=
  if who = none then
    if terminal.1 = {some 0, some 1} then 0 else 1
  else if who = some 0 then
    if terminal.1 = {some 1} then 2
    else if terminal.1 = {some 0} ∨ terminal.1 = {some 0, some 1} then 1 else 0
  else 0

@[simp] private theorem childCoalition_zero :
    cappedClockChildCoalition ({0} : Finset Child) = {some 0} := by decide

@[simp] private theorem childCoalition_one :
    cappedClockChildCoalition ({1} : Finset Child) = {some 1} := by decide

@[simp] private theorem childCoalition_pair :
    cappedClockChildCoalition ({0, 1} : Finset Child) = {some 0, some 1} := by decide

private theorem nonempty_child_cases (A : Finset Child) (hA : A.Nonempty) :
    A = {0} ∨ A = {1} ∨ A = {0, 1} :=
  (by decide +kernel : ∀ A : Finset Child, A.Nonempty →
    A = {0} ∨ A = {1} ∨ A = {0, 1}) A hA

private abbrev passiveZeroUnique :
    Unique {A : Finset Child // A.Nonempty ∧ (0 : Child) ∉ A} where
  default := ⟨{1}, by decide⟩
  uniq A := by fin_cases A; rfl

private theorem patientFloor_zero : patientWithdrawalFloor reward 0 = 1 := by
  let := passiveZeroUnique
  have hpassive (B : {A : Finset Child // A.Nonempty ∧ (0 : Child) ∉ A}) :
      B.1 = {1} := congrArg Subtype.val (passiveZeroUnique.uniq B)
  norm_num +decide [patientWithdrawalFloor, patientWithdrawalOwnNeverAlternative,
    Finset.univ_unique, hpassive, reward]

private theorem patientGain_zero (A : Finset Child) (hA : A.Nonempty) :
    patientWithdrawalGainFloor reward 0 A hA = if A = {0, 1} then 1 else 0 := by
  rcases nonempty_child_cases A hA with rfl | rfl | rfl
  · rw [patientWithdrawalGainFloor, deadlineSecurityGainFloor_singletonWithRestart,
      patientFloor_zero]
    norm_num +decide [reward]
  · norm_num +decide [patientWithdrawalGainFloor, deadlineSecurityGainFloorWithRestart,
      deadlineWithdrawalGainFloor, reward]
  · norm_num +decide [patientWithdrawalGainFloor, deadlineSecurityGainFloorWithRestart,
      deadlineWithdrawalGainFloor, reward]

/-- The complete original patient N/F/J system passes lambda=(0,0), mu=(1,0). -/
def certificate : PatientWithdrawalRewardCertificate reward where
  advanceWeight := 0
  withdrawalWeight := ![1, 0]
  advanceWeight_nonneg := by simp
  withdrawalWeight_nonneg := by intro i; fin_cases i <;> norm_num
  never_row := by
    norm_num +decide [reward, patientWithdrawalOwnNeverAlternative, Fin.sum_univ_two]
  future_row := by
    intro A hA
    rcases nonempty_child_cases A hA with rfl | rfl | rfl <;>
      norm_num +decide [reward, Fin.sum_univ_two, patientGain_zero]
  join_row := by
    intro A hA
    rcases nonempty_child_cases A hA with rfl | rfl | rfl <;>
      norm_num +decide [reward, cappedClockJoinedCoalition, Fin.sum_univ_two, patientGain_zero]

/-- The actual child profile reconstructs independent date-one Dirac laws. -/
def childProfile :
    (quittingGame (quittingDeleteReward reward (· = none))).BehaviorProfile :=
  quittingStoppingLawProfile (quittingDeleteReward reward (· = none))
    (fun _ => PMF.pure (some 1))

/-- The actual canonical deletion lift, not merely a parent law surrogate. -/
def liftedProfile : (quittingGame reward).BehaviorProfile :=
  quittingLiftDeletedProfile reward (· = none) childProfile

def clocks : Player → Option ℕ
  | none => none
  | some _ => some 1

private theorem lifted_laws :
    quittingBehaviorStoppingLaws reward liftedProfile = fun who => PMF.pure (clocks who) := by
  rw [show quittingBehaviorStoppingLaws reward liftedProfile =
      quietParentStoppingLaws (quietOutsiderChildLaws reward childProfile) from
    quittingBehaviorStoppingLaws_liftDeletedProfile_eq_quiet reward childProfile]
  funext who
  cases who with
  | none => rfl
  | some i =>
      change quittingBehaviorStoppingLaw (quittingDeleteReward reward (· = none))
        (childProfile ⟨some i, Option.some_ne_none i⟩) = PMF.pure (some 1)
      simp [childProfile]

/-- The actual canonical Never lift has these independent complete stopping laws. -/
theorem liftedProfile_stoppingLaws :
    quittingBehaviorStoppingLaws reward liftedProfile = fun who => PMF.pure (clocks who) :=
  lifted_laws

private theorem not_first_two (choice : Option ℕ)
    (hzero : choice ≠ some 0) (hone : choice ≠ some 1) :
    choice ∉ (Finset.range (1 + 1)).image some := by
  intro hmem
  obtain ⟨time, htime, hchoice⟩ := Finset.mem_image.mp hmem
  have hcases : time = 0 ∨ time = 1 := by
    have htimeLt := Finset.mem_range.mp htime
    omega
  rcases hcases with rfl | rfl
  · exact hzero hchoice.symm
  · exact hone hchoice.symm

private theorem child_event_zero :
    QuittingClockFirstEvent 0 ⟨{some 0}, by decide⟩
      (Function.update clocks (some 0) (some 0)) := by
  intro player
  cases player with
  | none => simp [clocks]
  | some i => fin_cases i <;> simp [clocks]

private theorem child_event_one :
    QuittingClockFirstEvent 1 ⟨{some 0, some 1}, by decide⟩
      (Function.update clocks (some 0) (some 1)) := by
  intro player
  cases player with
  | none => simp [clocks]
  | some i => fin_cases i <;> simp [clocks]

private theorem child_event_late (choice : Option ℕ)
    (hzero : choice ≠ some 0) (hone : choice ≠ some 1) :
    QuittingClockFirstEvent 1 ⟨{some 1}, by decide⟩
      (Function.update clocks (some 0) choice) := by
  have hnot := not_first_two choice hzero hone
  intro player
  cases player with
  | none => simp [clocks]
  | some i =>
      fin_cases i
      · simpa [clocks] using hnot
      · simp [clocks]

private theorem outside_event_zero :
    QuittingClockFirstEvent 0 ⟨{none}, by decide⟩
      (Function.update clocks none (some 0)) := by
  intro player
  cases player with
  | none => simp
  | some i => fin_cases i <;> simp [clocks]

private theorem outside_event_one :
    QuittingClockFirstEvent 1 ⟨{none, some 0, some 1}, by decide⟩
      (Function.update clocks none (some 1)) := by
  intro player
  cases player with
  | none => simp
  | some i => fin_cases i <;> simp [clocks]

private theorem outside_event_late (choice : Option ℕ)
    (hzero : choice ≠ some 0) (hone : choice ≠ some 1) :
    QuittingClockFirstEvent 1 ⟨{some 0, some 1}, by decide⟩
      (Function.update clocks none choice) := by
  have hnot := not_first_two choice hzero hone
  intro player
  cases player with
  | none => simpa using hnot
  | some i => fin_cases i <;> simp [clocks]

/-- Exact actual child replies for ANY clock evaluation, including every date and Never. -/
theorem pureClock_child_reply (evaluation : WithTop ℕ → ℝ) (choice : Option ℕ) :
    quittingPureClockEvaluatedPayoff reward evaluation
        (Function.update clocks (some 0) choice) (some 0) =
      if choice = some 0 then evaluation 0
      else if choice = some 1 then evaluation 1 else 2 * evaluation 1 := by
  by_cases hzero : choice = some 0
  · subst choice
    obtain ⟨htime, houtcome⟩ := (quittingClockFirstEvent_iff 0 _ _).mp child_event_zero
    simp only [quittingPureClockEvaluatedPayoff, houtcome, htime]
    norm_num +decide [reward]
  · by_cases hone : choice = some 1
    · subst choice
      obtain ⟨htime, houtcome⟩ := (quittingClockFirstEvent_iff 1 _ _).mp child_event_one
      simp only [quittingPureClockEvaluatedPayoff, houtcome, htime]
      norm_num +decide [reward]
    · obtain ⟨htime, houtcome⟩ := (quittingClockFirstEvent_iff 1 _ _).mp
        (child_event_late choice hzero hone)
      simp only [quittingPureClockEvaluatedPayoff, houtcome, htime]
      norm_num +decide [reward, hzero, hone]
      all_goals ring

/-- Exact actual outsider replies for ANY evaluation; late dates and Never give zero. -/
theorem pureClock_outside_reply (evaluation : WithTop ℕ → ℝ) (choice : Option ℕ) :
    quittingPureClockEvaluatedPayoff reward evaluation
        (Function.update clocks none choice) none =
      if choice = some 0 then evaluation 0
      else if choice = some 1 then evaluation 1 else 0 := by
  by_cases hzero : choice = some 0
  · subst choice
    obtain ⟨htime, houtcome⟩ := (quittingClockFirstEvent_iff 0 _ _).mp outside_event_zero
    simp only [quittingPureClockEvaluatedPayoff, houtcome, htime]
    norm_num +decide [reward]
  · by_cases hone : choice = some 1
    · subst choice
      obtain ⟨htime, houtcome⟩ := (quittingClockFirstEvent_iff 1 _ _).mp outside_event_one
      simp only [quittingPureClockEvaluatedPayoff, houtcome, htime]
      norm_num +decide [reward]
    · obtain ⟨htime, houtcome⟩ := (quittingClockFirstEvent_iff 1 _ _).mp
        (outside_event_late choice hzero hone)
      simp only [quittingPureClockEvaluatedPayoff, houtcome, htime]
      norm_num +decide [reward, hzero, hone]

/-- The SAME prescribed clock tuple: both children quit at date one. -/
theorem pureClock_prescribed_payoffs (evaluation : WithTop ℕ → ℝ) :
    quittingPureClockEvaluatedPayoff reward evaluation clocks (some 0) = evaluation 1 ∧
      quittingPureClockEvaluatedPayoff reward evaluation clocks none = 0 := by
  have hself : Function.update clocks (some 0) (some 1) = clocks := by
    change Function.update clocks (some 0) (clocks (some 0)) = clocks
    exact Function.update_eq_self _ _
  have hevent : QuittingClockFirstEvent 1 ⟨{some 0, some 1}, by decide⟩ clocks := by
    simpa only [hself] using child_event_one
  obtain ⟨htime, houtcome⟩ := (quittingClockFirstEvent_iff 1 _ _).mp hevent
  constructor <;> simp only [quittingPureClockEvaluatedPayoff, houtcome, htime] <;>
    norm_num +decide [reward]

private def reply (who : Player) (choice : Option ℕ) : ℝ :=
  quittingStoppingLawEvaluatedPayoff reward (quittingFiniteHorizonEvaluation 3)
    (Function.update (fun player => PMF.pure (clocks player)) who (PMF.pure choice)) who

private theorem reply_eq_pure (who : Player) (choice : Option ℕ) :
    reply who choice =
      quittingPureClockEvaluatedPayoff reward (quittingFiniteHorizonEvaluation 3)
        (Function.update clocks who choice) who := by
  have hfamily : Function.update (fun player => PMF.pure (clocks player)) who
      (PMF.pure choice) = fun player => PMF.pure ((Function.update clocks who choice) player) :=
    by funext player; by_cases hplayer : player = who <;> simp [hplayer]
  unfold reply quittingStoppingLawEvaluatedPayoff
  rw [hfamily, pmfPi_pure, expect_pure]

/-- The child's exact deterministic response menu includes every later date and Never. -/
theorem child_reply_eq (choice : Option ℕ) :
    reply (some 0) choice = if choice = some 1 then 1 / 3 else 2 / 3 := by
  rw [reply_eq_pure, pureClock_child_reply]
  have hzero : quittingFiniteHorizonEvaluation 3 (0 : WithTop ℕ) = 2 / 3 := by
    change (2 : ℝ) / 3 = 2 / 3
    rfl
  have hone : quittingFiniteHorizonEvaluation 3 (1 : WithTop ℕ) = 1 / 3 := by
    norm_num [quittingFiniteHorizonEvaluation, WithTop.recTopCoe]
  rw [hzero, hone]
  by_cases hchoice : choice = some 1
  · subst choice
    norm_num
  · simp only [ite_eq_right hchoice]
    split_ifs <;> norm_num

/-- The outsider's complete pure menu is two-thirds, one-third, then zero. -/
theorem outside_reply_eq (choice : Option ℕ) :
    reply none choice = if choice = some 0 then 2 / 3
      else if choice = some 1 then 1 / 3 else 0 := by
  rw [reply_eq_pure, pureClock_outside_reply]
  have hzero : quittingFiniteHorizonEvaluation 3 (0 : WithTop ℕ) = 2 / 3 := by
    change (2 : ℝ) / 3 = 2 / 3
    rfl
  have hone : quittingFiniteHorizonEvaluation 3 (1 : WithTop ℕ) = 1 / 3 := by
    norm_num [quittingFiniteHorizonEvaluation, WithTop.recTopCoe]
  rw [hzero, hone]

private theorem cap_eq_of_reply (who : Player)
    (hbound : ∀ choice, reply who choice ≤ 2 / 3)
    (hattains : reply who (some 0) = 2 / 3) :
    quittingFiniteHorizonDeviationCap reward liftedProfile 3 who = 2 / 3 := by
  rw [quittingFiniteHorizonDeviationCap_eq_pureTime, lifted_laws]
  change sSup (Set.range (reply who)) = 2 / 3
  have hbounded : BddAbove (Set.range (reply who)) := by
    refine ⟨2 / 3, ?_⟩
    rintro _ ⟨choice, rfl⟩
    exact hbound choice
  apply le_antisymm
  · apply csSup_le
    · exact ⟨reply who none, ⟨none, rfl⟩⟩
    · rintro _ ⟨choice, rfl⟩
      exact hbound choice
  · rw [← hattains]
    exact le_csSup hbounded ⟨some 0, rfl⟩

/-- Both complete actual behavioral caps at horizon three equal two-thirds. -/
theorem horizon_three_caps :
    quittingFiniteHorizonDeviationCap reward liftedProfile 3 (some 0) = 2 / 3 ∧
      quittingFiniteHorizonDeviationCap reward liftedProfile 3 none = 2 / 3 := by
  constructor
  · apply cap_eq_of_reply
    · intro choice
      rw [child_reply_eq]
      split_ifs <;> norm_num
    · norm_num [child_reply_eq]
  · apply cap_eq_of_reply
    · intro choice
      rw [outside_reply_eq]
      split_ifs <;> norm_num
    · norm_num [outside_reply_eq]

/-- Literal actual stage averages: child zero earns one-third, outsider earns zero. -/
theorem horizon_three_payoffs :
    (quittingGame reward).finiteAveragePayoff none 3 liftedProfile (some 0) = 1 / 3 ∧
      (quittingGame reward).finiteAveragePayoff none 3 liftedProfile none = 0 := by
  have hvalue (who : Player) :
      (quittingGame reward).finiteAveragePayoff none 3 liftedProfile who =
        quittingPureClockEvaluatedPayoff reward (quittingFiniteHorizonEvaluation 3)
          clocks who := by
    rw [quittingFiniteAveragePayoff_eq_stoppingLawEvaluatedPayoff, lifted_laws]
    unfold quittingStoppingLawEvaluatedPayoff
    rw [pmfPi_pure, expect_pure]
  constructor
  · rw [hvalue, (pureClock_prescribed_payoffs _).1]
    norm_num [quittingFiniteHorizonEvaluation, WithTop.recTopCoe]
  · rw [hvalue, (pureClock_prescribed_payoffs _).2]

private theorem child_zero_debt_eq :
    quittingFiniteHorizonDeviationCap (quittingDeleteReward reward (· = none))
        childProfile 3 ⟨some 0, by simp⟩ -
      (quittingGame (quittingDeleteReward reward (· = none))).finiteAveragePayoff
        none 3 childProfile ⟨some 0, by simp⟩ = 1 / 3 := by
  have hcap := quittingBehaviorEvaluatedDeviationPayoffCap_liftDeletedProfile
    (deleted := (· = none)) reward (quittingFiniteHorizonEvaluation 3)
      childProfile ⟨some 0, by simp⟩
  have hpayoff := quittingBehaviorEvaluatedPayoff_liftDeletedProfile
    (deleted := (· = none)) reward (quittingFiniteHorizonEvaluation 3)
      childProfile ⟨some 0, by simp⟩
  rw [← quittingFiniteHorizonDeviationCap_eq_evaluatedCap,
    ← quittingFiniteHorizonDeviationCap_eq_evaluatedCap] at hcap
  change quittingStoppingLawEvaluatedPayoff reward _ _ _ =
    quittingStoppingLawEvaluatedPayoff (quittingDeleteReward reward (· = none)) _ _ _
      at hpayoff
  rw [← quittingFiniteAveragePayoff_eq_stoppingLawEvaluatedPayoff,
    ← quittingFiniteAveragePayoff_eq_stoppingLawEvaluatedPayoff] at hpayoff
  rw [← hcap, ← hpayoff]
  change quittingFiniteHorizonDeviationCap reward liftedProfile 3 (some 0) -
    (quittingGame reward).finiteAveragePayoff none 3 liftedProfile (some 0) = 1 / 3
  rw [horizon_three_caps.1, horizon_three_payoffs.1]
  norm_num

/-- The actual horizon-three outside debt strictly exceeds the patient weighted child debt.
This does not contradict the valid terminal-only raw certificate. -/
theorem patient_horizon_three_bound_fails :
    (∑ i : Child, (certificate.advanceWeight i + certificate.withdrawalWeight i) *
      (quittingFiniteHorizonDeviationCap (quittingDeleteReward reward (· = none))
          childProfile 3 ⟨some i, Option.some_ne_none i⟩ -
        (quittingGame (quittingDeleteReward reward (· = none))).finiteAveragePayoff
          none 3 childProfile ⟨some i, Option.some_ne_none i⟩)) <
      quittingFiniteHorizonDeviationCap reward liftedProfile 3 none -
        (quittingGame reward).finiteAveragePayoff none 3 liftedProfile none := by
  simp only [certificate, Pi.zero_apply, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, zero_add, one_mul, zero_mul, add_zero]
  rw [child_zero_debt_eq, horizon_three_caps.2, horizon_three_payoffs.2]
  norm_num

end GameTheory.PatientWithdrawalFiniteHorizonBoundary
