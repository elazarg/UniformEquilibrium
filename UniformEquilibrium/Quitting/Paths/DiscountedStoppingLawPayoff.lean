import MathUE.RealSeries.DiscountedExitWeight
import UniformEquilibrium.Quitting.Paths.FiniteHorizonStoppingLawPayoff

/-! # Actual normalized discounted payoff from independent first-Quit laws

The canonical stochastic payoff is a normalized series of actual expected
stage rewards. The live stage has reward zero: exit at date t starts earning
the terminal reward at stage t+1. The same identity holds after every
complete behavioral replacement. Signed rewards and joint Never are kept.
-/

noncomputable section

namespace GameTheory

open scoped BigOperators Classical
open _root_.Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- The actual absorption-date weight of the normalized discounted stage series. -/
def quittingDiscountedEvaluation (discount : ℝ) : WithTop ℕ → ℝ :=
  WithTop.recTopCoe 0 (fun time => discount ^ (time + 1))

@[simp] theorem quittingDiscountedEvaluation_top (discount : ℝ) :
    quittingDiscountedEvaluation discount ⊤ = 0 := rfl

@[simp] theorem quittingDiscountedEvaluation_coe (discount : ℝ) (time : ℕ) :
    quittingDiscountedEvaluation discount (time : WithTop ℕ) = discount ^ (time + 1) := rfl

theorem quittingDiscountedEvaluation_nonneg
    (discount : ℝ) (hdiscount : 0 ≤ discount) (clock : WithTop ℕ) :
    0 ≤ quittingDiscountedEvaluation discount clock := by
  induction clock using WithTop.recTopCoe with
  | top => exact le_rfl
  | coe time => exact pow_nonneg hdiscount _

theorem quittingDiscountedEvaluation_le_one
    (discount : ℝ) (hdiscount : 0 ≤ discount) (hdiscountOne : discount ≤ 1)
    (clock : WithTop ℕ) : quittingDiscountedEvaluation discount clock ≤ 1 := by
  induction clock using WithTop.recTopCoe with
  | top => norm_num
  | coe time => exact pow_le_one₀ hdiscount hdiscountOne

theorem quittingDiscountedEvaluation_antitone
    (discount : ℝ) (hdiscount : 0 ≤ discount) (hdiscountOne : discount ≤ 1) :
    Antitone (quittingDiscountedEvaluation discount) := by
  intro first second hle
  induction first using WithTop.recTopCoe with
  | top =>
      have hsecond : second = ⊤ := top_le_iff.mp hle
      subst second
      exact le_rfl
  | coe first =>
      induction second using WithTop.recTopCoe with
      | top => exact pow_nonneg hdiscount _
      | coe second =>
          exact pow_le_pow_of_le_one hdiscount hdiscountOne
            (Nat.add_le_add_right (ENat.natCast_le_natCast.mp hle) 1)

/-- A deterministic tuple earns its terminal reward strictly after its first exit. -/
def quittingPureClockStagePayoff
    (reward : {A : Finset ι // A.Nonempty} → Payoff ι)
    (times : ι → Option ℕ) (stage : ℕ) (who : ι) : ℝ :=
  if quittingEarliestStoppingValue times < (stage : WithTop ℕ) then
    quittingPureClockTerminalPayoff reward times who else 0

omit [DecidableEq ι] in
theorem abs_quittingPureClockStagePayoff_le
    (reward : {A : Finset ι // A.Nonempty} → Payoff ι)
    (times : ι → Option ℕ) (stage : ℕ) (who : ι) :
    |quittingPureClockStagePayoff reward times stage who| ≤ quittingRewardBound reward := by
  unfold quittingPureClockStagePayoff
  split_ifs
  · unfold quittingPureClockTerminalPayoff
    cases quittingFirstStoppingOutcome times with
    | none => simpa only [abs_zero] using quittingRewardBound_nonneg reward
    | some terminal => exact abs_reward_le_quittingRewardBound reward terminal who
  · simpa only [abs_zero] using quittingRewardBound_nonneg reward

private theorem withTopNatCast_lt_iff (first second : ℕ) :
    ((first : WithTop ℕ) < (second : WithTop ℕ)) ↔ first < second :=
  WithTop.coe_lt_coe

private theorem withTopNatCast_eq_iff (first second : ℕ) :
    ((first : WithTop ℕ) = (second : WithTop ℕ)) ↔ first = second :=
  WithTop.coe_inj

private theorem pureClockStagePayoff_eq_firstEventPrefix
    (reward : {A : Finset ι // A.Nonempty} → Payoff ι)
    (times : ι → Option ℕ) (stage : ℕ) (who : ι) :
    quittingPureClockStagePayoff reward times stage who =
      ∑ time ∈ Finset.range stage, ∑ terminal : {A : Finset ι // A.Nonempty},
        (if QuittingClockFirstEvent time terminal times then 1 else 0) * reward terminal who := by
  simp_rw [quittingPureClockPayoff_timeSlice]
  unfold quittingPureClockStagePayoff
  induction quittingEarliestStoppingValue times using WithTop.recTopCoe with
  | top => simp
  | coe selected =>
      change (if (selected : WithTop ℕ) < (stage : WithTop ℕ) then
          quittingPureClockTerminalPayoff reward times who else 0) =
        ∑ time ∈ Finset.range stage,
          if (selected : WithTop ℕ) = (time : WithTop ℕ) then
            quittingPureClockTerminalPayoff reward times who else 0
      simp only [withTopNatCast_lt_iff, withTopNatCast_eq_iff,
        Finset.sum_ite_eq, Finset.mem_range]

/-- Actual history-stage expectation equals the corresponding independent-clock expectation. -/
theorem expectedStagePayoff_quittingGame_eq_pureClockStageExpectation
    (reward : {A : Finset ι // A.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (stage : ℕ) (who : ι) :
    (quittingGame reward).expectedStagePayoff profile none stage who =
      expect (pmfPi (quittingBehaviorStoppingLaws reward profile))
        (fun times => quittingPureClockStagePayoff reward times stage who) := by
  let laws := quittingBehaviorStoppingLaws reward profile
  have hbounded : ∀ time terminal times,
      |(if QuittingClockFirstEvent time terminal times then 1 else 0) *
        reward terminal who| ≤ |reward terminal who| := by
    intro time terminal times
    split_ifs <;> simp
  have hexpect :
      expect (pmfPi laws) (fun times => quittingPureClockStagePayoff reward times stage who) =
        ∑ time ∈ Finset.range stage, ∑ terminal,
          quittingStageCoalitionMass reward profile time terminal * reward terminal who := by
    simp_rw [pureClockStagePayoff_eq_firstEventPrefix]
    rw [expect_finset_sum_of_bounded
      (bound := fun _ => ∑ terminal : {A : Finset ι // A.Nonempty}, |reward terminal who|)]
    · apply Finset.sum_congr rfl
      intro time _
      rw [expect_finset_sum_of_bounded (bound := fun terminal => |reward terminal who|)]
      · apply Finset.sum_congr rfl
        intro terminal _
        rw [show (fun times =>
            (if QuittingClockFirstEvent time terminal times then 1 else 0) *
              reward terminal who) =
            (fun times => reward terminal who *
              (if QuittingClockFirstEvent time terminal times then 1 else 0)) by
                funext times; ring, expect_const_mul]
        rw [expect_quittingClockFirstEvent]
        ring
      · exact fun terminal _ times => hbounded time terminal times
    · intro time _ times
      exact (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum fun terminal _ => hbounded time terminal times)
  rw [hexpect, expectedStagePayoff_quittingGame_eq_sum_mass]
  simp_rw [quittingAbsorbedMass_eq_sum_stageCoalitionMass, Finset.sum_mul]
  exact Finset.sum_comm

omit [DecidableEq ι] in
/-- The deterministic normalized stage series retains the actual date and terminal coalition. -/
theorem quittingPureClockDiscountedStagePayoff_eq_evaluatedPayoff
    (reward : {A : Finset ι // A.Nonempty} → Payoff ι)
    (discount : ℝ) (hdiscount : 0 ≤ discount) (hdiscountOne : discount < 1)
    (times : ι → Option ℕ) (who : ι) :
    (1 - discount) * ∑' stage : ℕ,
        discount ^ stage * quittingPureClockStagePayoff reward times stage who =
      quittingPureClockEvaluatedPayoff reward
        (quittingDiscountedEvaluation discount) times who := by
  induction hearliest : quittingEarliestStoppingValue times using WithTop.recTopCoe with
  | top =>
      have houtcome : quittingFirstStoppingOutcome times = none := by
        simp [quittingFirstStoppingOutcome, hearliest]
      simp [quittingPureClockStagePayoff, quittingPureClockEvaluatedPayoff, hearliest, houtcome]
  | coe selected =>
      rw [quittingPureClockEvaluatedPayoff_eq_evaluation_mul_terminalPayoff, hearliest]
      change (1 - discount) * ∑' stage : ℕ,
          discount ^ stage * quittingPureClockStagePayoff reward times stage who =
        discount ^ (selected + 1) * quittingPureClockTerminalPayoff reward times who
      simp only [quittingPureClockStagePayoff, hearliest]
      change (1 - discount) * ∑' stage : ℕ,
          discount ^ stage *
            (if (selected : WithTop ℕ) < (stage : WithTop ℕ) then
              quittingPureClockTerminalPayoff reward times who else 0) =
        discount ^ (selected + 1) * quittingPureClockTerminalPayoff reward times who
      simp only [withTopNatCast_lt_iff]
      exact Math.RealSeries.normalized_geometric_exit_weight discount
        (quittingPureClockTerminalPayoff reward times who) hdiscount hdiscountOne selected

/-- Canonical normalized discounted history payoff is exactly the actual first-exit law value. -/
theorem quittingDiscountedPayoff_eq_stoppingLawEvaluatedPayoff
    (reward : {A : Finset ι // A.Nonempty} → Payoff ι)
    (discount : ℝ) (hdiscount : 0 ≤ discount) (hdiscountOne : discount < 1)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι) :
    (quittingGame reward).discountedPayoff discount profile none who =
      quittingStoppingLawEvaluatedPayoff reward (quittingDiscountedEvaluation discount)
        (quittingBehaviorStoppingLaws reward profile) who := by
  unfold StochasticGame.discountedPayoff quittingStoppingLawEvaluatedPayoff
  simp_rw [expectedStagePayoff_quittingGame_eq_pureClockStageExpectation]
  rw [← Math.ProbabilityMassFunction.expect_tsum_geometric_of_bounded
    (pmfPi (quittingBehaviorStoppingLaws reward profile))
    hdiscount hdiscountOne (quittingRewardBound_nonneg reward)
    (fun times stage => quittingPureClockStagePayoff reward times stage who)
    (fun times stage => abs_quittingPureClockStagePayoff_le reward times stage who),
    ← expect_const_mul]
  apply congrArg (expect (pmfPi (quittingBehaviorStoppingLaws reward profile)))
  funext times
  exact quittingPureClockDiscountedStagePayoff_eq_evaluatedPayoff
    reward discount hdiscount hdiscountOne times who

/-- The identical semantic bridge after any complete unilateral behavioral replacement. -/
theorem quittingDiscountedPayoff_update_eq_behaviorEvaluatedPayoff
    (reward : {A : Finset ι // A.Nonempty} → Payoff ι)
    (discount : ℝ) (hdiscount : 0 ≤ discount) (hdiscountOne : discount < 1)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι)
    (deviation : (quittingGame reward).BehaviorStrategy who) :
    (quittingGame reward).discountedPayoff discount
        (Function.update profile who deviation) none who =
      quittingBehaviorEvaluatedPayoff reward (quittingDiscountedEvaluation discount)
        (Function.update profile who deviation) who :=
  quittingDiscountedPayoff_eq_stoppingLawEvaluatedPayoff
    reward discount hdiscount hdiscountOne _ who

end GameTheory
