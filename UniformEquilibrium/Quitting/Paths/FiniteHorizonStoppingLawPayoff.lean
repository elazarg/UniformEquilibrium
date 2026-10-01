import MathUE.ProbabilityMassFunction.ProductEventExpectation
import MathUE.ProbabilityMassFunction.StoppingLawLateIndicators
import UniformEquilibrium.Quitting.Paths.StageCoalitionStoppingLaw
import UniformEquilibrium.Quitting.Paths.StoppingLawEvaluatedPayoff

/-! # Actual finite-horizon payoff from independent first-Quit laws

The reward paid at stage zero is zero. A first exit at date t therefore earns
exactly H-t-1 paid stages in horizon H. Never remains zero. Signed terminal
rows and arbitrary complete behavioral replacements are retained.
-/

noncomputable section

namespace GameTheory

open scoped BigOperators Classical
open _root_.Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- The exact stage-average weight, with Never explicitly retained. -/
def quittingFiniteHorizonEvaluation (horizon : ℕ) : WithTop ℕ → ℝ :=
  WithTop.recTopCoe 0 (fun time => (horizon - time - 1 : ℕ) / (horizon : ℝ))

@[simp] theorem quittingFiniteHorizonEvaluation_top (horizon : ℕ) :
    quittingFiniteHorizonEvaluation horizon ⊤ = 0 := rfl

@[simp] theorem quittingFiniteHorizonEvaluation_coe (horizon time : ℕ) :
    quittingFiniteHorizonEvaluation horizon (time : WithTop ℕ) =
      (horizon - time - 1 : ℕ) / (horizon : ℝ) := rfl

theorem quittingFiniteHorizonEvaluation_nonneg (horizon : ℕ) (clock : WithTop ℕ) :
    0 ≤ quittingFiniteHorizonEvaluation horizon clock := by
  induction clock using WithTop.recTopCoe with
  | top => simp
  | coe time => exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem quittingFiniteHorizonEvaluation_le_one (horizon : ℕ) (clock : WithTop ℕ) :
    quittingFiniteHorizonEvaluation horizon clock ≤ 1 := by
  induction clock using WithTop.recTopCoe with
  | top => simp
  | coe time =>
      by_cases hzero : horizon = 0
      · simp [hzero]
      · change (horizon - time - 1 : ℕ) / (horizon : ℝ) ≤ 1
        apply (div_le_one (by exact_mod_cast Nat.pos_of_ne_zero hzero)).mpr
        exact_mod_cast (Nat.sub_le (horizon - time) 1).trans (Nat.sub_le horizon time)

/-- The rectangular clock event for one exact finite first-quitter coalition. -/
def QuittingClockFirstEvent (time : ℕ)
    (terminal : {A : Finset ι // A.Nonempty}) (times : ι → Option ℕ) : Prop :=
  ∀ who, if who ∈ terminal.1 then times who = some time else
    times who ∉ (Finset.range (time + 1)).image some

private theorem clock_tail_iff (choice : Option ℕ) (time : ℕ) :
    choice ∉ (Finset.range (time + 1)).image some ↔
      (time : WithTop ℕ) < quittingStoppingTimeValue choice := by
  cases choice with
  | none => simp [quittingStoppingTimeValue]
  | some chosen => simp [quittingStoppingTimeValue, not_le]

private theorem clock_atom_iff (choice : Option ℕ) (time : ℕ) :
    choice = some time ↔ quittingStoppingTimeValue choice = (time : WithTop ℕ) := by
  cases choice <;> simp [quittingStoppingTimeValue]

/-- The rectangular event is the actual labelled first outcome and date. -/
theorem quittingClockFirstEvent_iff (time : ℕ)
    (terminal : {A : Finset ι // A.Nonempty}) (times : ι → Option ℕ) :
    QuittingClockFirstEvent time terminal times ↔
      quittingEarliestStoppingValue times = (time : WithTop ℕ) ∧
        quittingFirstStoppingOutcome times = some terminal := by
  classical
  constructor
  · intro hevent
    obtain ⟨selected, hselected⟩ := terminal.2
    have hselectedClock : times selected = some time := by
      have hentry := hevent selected
      simpa only [ite_eq_left hselected] using hentry
    have hselectedTime : quittingStoppingTimeValue (times selected) = time :=
      (clock_atom_iff _ _).mp hselectedClock
    have hlower : (time : WithTop ℕ) ≤ quittingEarliestStoppingValue times := by
      apply Finset.le_inf
      intro who _
      by_cases hwho : who ∈ terminal.1
      · exact le_of_eq ((clock_atom_iff _ _).mp (by
          simpa [QuittingClockFirstEvent, hwho] using hevent who)).symm
      · exact ((clock_tail_iff _ _).mp (by
          simpa [QuittingClockFirstEvent, hwho] using hevent who)).le
    have hearliest : quittingEarliestStoppingValue times = time :=
      le_antisymm ((Finset.inf_le (Finset.mem_univ selected)).trans_eq hselectedTime)
        hlower
    refine ⟨hearliest, ?_⟩
    have hcoalition : quittingEarliestStoppingCoalition times = terminal.1 := by
      ext who
      simp only [quittingEarliestStoppingCoalition, Finset.mem_filter,
        Finset.mem_univ, true_and, hearliest]
      by_cases hwho : who ∈ terminal.1
      · exact iff_of_true ((clock_atom_iff _ _).mp (by
          simpa [QuittingClockFirstEvent, hwho] using hevent who)) hwho
      · exact iff_of_false (ne_of_gt ((clock_tail_iff _ _).mp (by
          simpa [QuittingClockFirstEvent, hwho] using hevent who))) hwho
    have hfinite : quittingEarliestStoppingValue times ≠ ⊤ := by
      rw [hearliest]
      exact ENat.natCast_ne_top time
    simp only [quittingFirstStoppingOutcome, ite_eq_right hfinite]
    exact congrArg some (Subtype.ext hcoalition)
  · rintro ⟨hearliest, houtcome⟩ who
    have hcoalition : quittingEarliestStoppingCoalition times = terminal.1 := by
      have hfinite : quittingEarliestStoppingValue times ≠ ⊤ := by
        rw [hearliest]
        exact ENat.natCast_ne_top time
      have hsome : some ⟨quittingEarliestStoppingCoalition times,
          quittingEarliestStoppingCoalition_nonempty times⟩ = some terminal := by
        simpa only [quittingFirstStoppingOutcome, ite_eq_right hfinite] using houtcome
      exact congrArg Subtype.val (Option.some.inj hsome)
    by_cases hwho : who ∈ terminal.1
    · simp only [ite_eq_left hwho]
      apply (clock_atom_iff _ _).mpr
      have hmem : who ∈ quittingEarliestStoppingCoalition times := hcoalition ▸ hwho
      simpa [quittingEarliestStoppingCoalition, hearliest] using hmem
    · simp only [ite_eq_right hwho]
      apply (clock_tail_iff _ _).mpr
      have hle : (time : WithTop ℕ) ≤ quittingStoppingTimeValue (times who) := by
        rw [← hearliest]
        exact Finset.inf_le (Finset.mem_univ who)
      refine lt_of_le_of_ne hle ?_
      intro heq
      apply hwho
      rw [← hcoalition]
      simp [quittingEarliestStoppingCoalition, hearliest, heq]

omit [Nonempty ι] in
/-- The product-clock event probability is exactly the executed stage mass. -/
theorem expect_quittingClockFirstEvent
    (reward : {A : Finset ι // A.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (time : ℕ)
    (terminal : {A : Finset ι // A.Nonempty}) :
    expect (pmfPi (quittingBehaviorStoppingLaws reward profile))
        (fun times => if QuittingClockFirstEvent time terminal times then 1 else 0) =
      quittingStageCoalitionMass reward profile time terminal := by
  classical
  have hproduct := expect_pmfPi_forallIndicator (quittingBehaviorStoppingLaws reward profile)
    (fun who choice => if who ∈ terminal.1 then choice = some time else
      choice ∉ (Finset.range (time + 1)).image some)
  have hfactor : expect (pmfPi (quittingBehaviorStoppingLaws reward profile))
      (fun times => if QuittingClockFirstEvent time terminal times then 1 else 0) =
      ∏ who, expect (quittingBehaviorStoppingLaws reward profile who)
        (fun choice => if (if who ∈ terminal.1 then choice = some time else
          choice ∉ (Finset.range (time + 1)).image some) then 1 else 0) := by
    convert hproduct using 1
    · congr 1
      funext times
      by_cases hfirst : ∀ who, if who ∈ terminal.1 then times who = some time else
          times who ∉ (Finset.range (time + 1)).image some <;>
        simp only [QuittingClockFirstEvent, hfirst, ite_false]
    · apply Finset.prod_congr rfl
      intro who _
      apply congrArg (expect (quittingBehaviorStoppingLaws reward profile who))
      funext choice
      by_cases hevent : if who ∈ terminal.1 then choice = some time else
          choice ∉ (Finset.range (time + 1)).image some <;>
        simp only [hevent, ite_false]
  rw [hfactor]
  rw [quittingStageCoalitionMass_eq_stoppingLawProduct_mul_tailProduct]
  rw [← Finset.prod_mul_prod_compl terminal.1
    (fun who => expect (quittingBehaviorStoppingLaws reward profile who)
      (fun choice => if (if who ∈ terminal.1 then choice = some time else
        choice ∉ (Finset.range (time + 1)).image some) then 1 else 0))]
  congr 1
  · apply Finset.prod_congr rfl
    intro who hwho
    simp only [ite_eq_left hwho, quittingBehaviorStoppingLaws]
    exact expect_stoppingLaw_finite_atom _ time
  · apply Finset.prod_congr rfl
    intro who hwho
    have hnot : who ∉ terminal.1 := Finset.mem_compl.mp hwho
    simp only [ite_eq_right hnot]
    simp only [ite_not]
    change expect (quittingBehaviorStoppingLaw reward (profile who))
      (stoppingLawTailIndicator (time + 1)) = _
    rw [expect_stoppingLawTailIndicator,
      stoppingLawSurvival_quittingBehaviorStoppingLaw]

/-- One literal first-exit date slice, shared by finite and discounted stage laws. -/
theorem quittingPureClockPayoff_timeSlice
    (reward : {A : Finset ι // A.Nonempty} → Payoff ι)
    (times : ι → Option ℕ) (who : ι) (time : ℕ) :
    (∑ terminal : {A : Finset ι // A.Nonempty},
      (if QuittingClockFirstEvent time terminal times then 1 else 0) *
        reward terminal who) =
      if quittingEarliestStoppingValue times = (time : WithTop ℕ) then
        quittingPureClockTerminalPayoff reward times who else 0 := by
  classical
  simp_rw [quittingClockFirstEvent_iff]
  by_cases hearliest : quittingEarliestStoppingValue times = (time : WithTop ℕ)
  · simp only [hearliest, true_and, ite_true]
    unfold quittingPureClockTerminalPayoff
    cases houtcome : quittingFirstStoppingOutcome times with
    | none => simp
    | some terminal => simp
  · simp [hearliest]

private theorem pureClock_finiteHorizon_decomposition
    (reward : {A : Finset ι // A.Nonempty} → Payoff ι)
    (horizon : ℕ) (times : ι → Option ℕ) (who : ι) :
    quittingPureClockEvaluatedPayoff reward (quittingFiniteHorizonEvaluation horizon)
        times who =
      (horizon : ℝ)⁻¹ * ∑ time ∈ Finset.range horizon,
        (horizon - time - 1 : ℕ) *
          ∑ terminal : {A : Finset ι // A.Nonempty},
            (if QuittingClockFirstEvent time terminal times then 1 else 0) *
              reward terminal who := by
  classical
  simp_rw [quittingPureClockPayoff_timeSlice]
  induction hearliest : quittingEarliestStoppingValue times using WithTop.recTopCoe with
  | top =>
      have houtcome : quittingFirstStoppingOutcome times = none := by
        simp [quittingFirstStoppingOutcome, hearliest]
      simp [quittingPureClockEvaluatedPayoff, houtcome]
  | coe selected =>
      have hfinite : quittingEarliestStoppingValue times ≠ ⊤ := by simp [hearliest]
      have houtcome : quittingFirstStoppingOutcome times = some
          ⟨quittingEarliestStoppingCoalition times,
            quittingEarliestStoppingCoalition_nonempty times⟩ := by
        simp [quittingFirstStoppingOutcome, hfinite]
      rw [Finset.sum_eq_single selected]
      · simp [quittingPureClockEvaluatedPayoff, quittingPureClockTerminalPayoff,
          houtcome, hearliest, quittingFiniteHorizonEvaluation, div_eq_mul_inv, mul_comm]
        change reward ⟨quittingEarliestStoppingCoalition times,
          quittingEarliestStoppingCoalition_nonempty times⟩ who *
            ((horizon : ℝ)⁻¹ * (horizon - selected - 1 : ℕ)) = _
        ring
      · intro other _ hother
        simp [hother.symm]
      · intro hnot
        have hcount : horizon - selected - 1 = 0 := by
          have hle : horizon ≤ selected := by simpa using hnot
          omega
        simp [hcount]

/-- Actual stage averages equal the clock-weighted first-exit expectation. -/
theorem quittingFiniteAveragePayoff_eq_stoppingLawEvaluatedPayoff
    (reward : {A : Finset ι // A.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (horizon : ℕ) (who : ι) :
    (quittingGame reward).finiteAveragePayoff none horizon profile who =
      quittingStoppingLawEvaluatedPayoff reward (quittingFiniteHorizonEvaluation horizon)
        (quittingBehaviorStoppingLaws reward profile) who := by
  classical
  let laws := quittingBehaviorStoppingLaws reward profile
  let : Finite (quittingGame reward).State :=
    inferInstanceAs (Finite (Option {S : Finset ι // S.Nonempty}))
  let : ∀ player : ι, Finite ((quittingGame reward).Act player) :=
    fun _ => inferInstanceAs (Finite Bool)
  have hbounded : ∀ time terminal times,
      |(if QuittingClockFirstEvent time terminal times then 1 else 0) *
        reward terminal who| ≤ |reward terminal who| := by
    intro time terminal times
    split_ifs <;> simp
  have hexpect : quittingStoppingLawEvaluatedPayoff reward
      (quittingFiniteHorizonEvaluation horizon) laws who =
        (horizon : ℝ)⁻¹ * ∑ time ∈ Finset.range horizon,
          (horizon - time - 1 : ℕ) *
            ∑ terminal, quittingStageCoalitionMass reward profile time terminal *
              reward terminal who := by
    unfold quittingStoppingLawEvaluatedPayoff
    simp_rw [pureClock_finiteHorizon_decomposition]
    rw [expect_const_mul, expect_finset_sum_of_bounded
      (bound := fun time => (horizon - time - 1 : ℕ) *
        ∑ terminal : {A : Finset ι // A.Nonempty}, |reward terminal who|)]
    · apply congrArg ((horizon : ℝ)⁻¹ * ·)
      apply Finset.sum_congr rfl
      intro time _
      rw [expect_const_mul, expect_finset_sum_of_bounded
        (bound := fun terminal => |reward terminal who|)]
      · congr 1
        apply Finset.sum_congr rfl
        intro terminal _
        rw [show (fun times =>
            (if QuittingClockFirstEvent time terminal times then 1 else 0) *
              reward terminal who) =
            fun times => reward terminal who *
              (if QuittingClockFirstEvent time terminal times then 1 else 0) by
                funext times; ring, expect_const_mul]
        rw [expect_quittingClockFirstEvent]
        ring
      · exact fun terminal _ times => hbounded time terminal times
    · intro time _ times
      rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      exact (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum fun terminal _ => hbounded time terminal times)
  rw [hexpect]
  let initial : (quittingGame reward).State := none
  change (quittingGame reward).finiteAveragePayoff initial horizon profile who = _
  have haverage := (quittingGame reward).finiteAveragePayoff_eq_sum_expectedStagePayoff
    profile initial who horizon
  rw [haverage]
  congr 1
  have hstage (stage : ℕ) :
      (quittingGame reward).expectedStagePayoff profile initial stage who =
        ∑ terminal, quittingAbsorbedMass reward profile stage terminal * reward terminal who :=
    expectedStagePayoff_quittingGame_eq_sum_mass reward profile stage who
  simp_rw [hstage,
    quittingAbsorbedMass_eq_sum_stageCoalitionMass, Finset.sum_mul]
  conv_lhs =>
    arg 2
    ext stage
    rw [Finset.sum_comm]
  exact sum_prefix_sums_eq_absorption_weights
    (fun time => ∑ terminal,
      quittingStageCoalitionMass reward profile time terminal * reward terminal who) horizon

/-- The same exact horizon formula after every complete behavioral replacement. -/
theorem quittingFiniteAveragePayoff_update_eq_stoppingLawEvaluatedPayoff
    (reward : {A : Finset ι // A.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (horizon : ℕ) (who observer : ι)
    (deviation : (quittingGame reward).BehaviorStrategy who) :
    (quittingGame reward).finiteAveragePayoff none horizon
        (Function.update profile who deviation) observer =
      quittingStoppingLawEvaluatedPayoff reward (quittingFiniteHorizonEvaluation horizon)
        (Function.update (quittingBehaviorStoppingLaws reward profile) who
          (quittingBehaviorStoppingLaw reward deviation)) observer := by
  rw [quittingFiniteAveragePayoff_eq_stoppingLawEvaluatedPayoff,
    quittingBehaviorStoppingLaws_update]

end GameTheory
