import UniformEquilibrium.Quitting.Terminal.FiniteDeadlineFullReplyCap
import UniformEquilibrium.Quitting.Terminal.FiniteMenuEarlyAbsorptionNecessity
import UniformEquilibrium.Quitting.Terminal.FiniteDeadlineNashExistence
import UniformEquilibrium.Quitting.Punishment.FiniteMenuPunishmentRecursion
import UniformEquilibrium.Quitting.Classification.OnePlayer.FiniteMenuPunishment
import UniformEquilibrium.Quitting.Punishment.FinitePureReplyPunishment
import UniformEquilibrium.Diagnostics.Quitting.FiniteDeadlineTimingRecursion
import UniformEquilibrium.Quitting.Paths.StoppingLawOperationalDistance

noncomputable section

namespace GameTheory.TwoClockOrderedPureTimePayoff

open GameTheory

def reward : {S : Finset Bool // S.Nonempty} → Payoff Bool := fun terminal who ↦
  if who then 0 else if terminal.val = {false} then 1
    else if terminal.val = {true} then 2 else 0

def activeValue : Option ℕ → Option ℕ → ℝ
  | none, none => 0
  | none, some _ => 2
  | some _, none => 1
  | some first, some second =>
      if first < second then 1 else if second < first then 2 else 0

theorem pureTime_payoff_false (first second : Option ℕ) :
    quittingTerminalPayoff reward
        (quittingPureTimeProfileBehavior reward (Bool.rec first second)) false =
      activeValue first second := by
  rw [quittingTerminalPayoff_pureTimeProfileBehavior_eq_firstStoppingOutcome]
  cases first with
  | none =>
      cases second with
      | none =>
          simp [activeValue, quittingFirstStoppingOutcome,
            quittingEarliestStoppingValue, quittingStoppingTimeValue,
            quittingTerminalOutcomeReward]
      | some second =>
          simp [activeValue, quittingFirstStoppingOutcome,
            quittingEarliestStoppingValue, quittingStoppingTimeValue,
            quittingEarliestStoppingCoalition, quittingTerminalOutcomeReward,
            reward, Finset.ext_iff]
  | some first =>
      cases second with
      | none =>
          simp [activeValue, quittingFirstStoppingOutcome,
            quittingEarliestStoppingValue, quittingStoppingTimeValue,
            quittingEarliestStoppingCoalition, quittingTerminalOutcomeReward,
            reward, Finset.ext_iff]
      | some second =>
          rcases lt_trichotomy first second with hlt | heq | hgt
          · have hnlt : ¬ second < first := Nat.not_lt_of_ge (Nat.le_of_lt hlt)
            simp [activeValue, hlt, hnlt, quittingFirstStoppingOutcome,
              quittingEarliestStoppingValue, quittingStoppingTimeValue,
              quittingEarliestStoppingCoalition, quittingTerminalOutcomeReward,
              reward, Finset.ext_iff]
          · subst second
            simp [activeValue, quittingFirstStoppingOutcome,
              quittingEarliestStoppingValue, quittingStoppingTimeValue,
              quittingEarliestStoppingCoalition, quittingTerminalOutcomeReward,
              reward, Finset.ext_iff]
          · have hnlt : ¬ first < second := Nat.not_lt_of_ge (Nat.le_of_lt hgt)
            simp [activeValue, hgt, hnlt, quittingFirstStoppingOutcome,
              quittingEarliestStoppingValue, quittingStoppingTimeValue,
              quittingEarliestStoppingCoalition, quittingTerminalOutcomeReward,
              reward, Finset.ext_iff]

theorem pureTime_payoff_true (first second : Option ℕ) :
    quittingTerminalPayoff reward
        (quittingPureTimeProfileBehavior reward (Bool.rec first second)) true = 0 := by
  rw [quittingTerminalPayoff_pureTimeProfileBehavior_eq_firstStoppingOutcome]
  cases quittingFirstStoppingOutcome (Bool.rec first second) <;>
    simp [quittingTerminalOutcomeReward, reward]

end GameTheory.TwoClockOrderedPureTimePayoff

namespace GameTheory.TwoClockFiniteMenuRegression

open Math.Probability Math.ProbabilityMassFunction
open TwoClockOrderedPureTimePayoff

variable (N : ℕ) (hN : 2 ≤ N)

abbrev Action := QuittingFiniteDeadlineTimingAction N

def quit0 : Action N := some ⟨0, by omega⟩

def quitLast : Action N := some ⟨N - 1, by omega⟩

def halfLastNever : PMF (Action N) :=
  (bernoulliBool (1 / 2 : ℝ) (by norm_num) (by norm_num)).map
    (fun b => if b then quitLast N hN else none)

def mixed : Bool → PMF (Action N)
  | false => PMF.pure (quit0 N hN)
  | true => halfLastNever N hN

@[simp] theorem mixed_false_quit0 :
    mixed N hN false = PMF.pure (quit0 N hN) := rfl

@[simp] theorem mixed_false_never : (mixed N hN false none).toReal = 0 := by
  simp [mixed, quit0]

@[simp] theorem mixed_true_never : (mixed N hN true none).toReal = 1 / 2 := by
  simp [mixed, halfLastNever, quitLast, PMF.map_apply]
  norm_num

@[simp] theorem mixed_true_quitLast :
    (mixed N hN true (quitLast N hN)).toReal = 1 / 2 := by
  simp [mixed, halfLastNever, quitLast, PMF.map_apply]

def decode : Action N → Option ℕ
  | none => none
  | some time => some time.val

theorem pureTimingPayoff (a b : Action N) :
    quittingTerminalPayoff reward
        (quittingPureStoppingTimeProfile reward fun player =>
          quittingFiniteDeadlineTimingActionTime (Bool.rec a b player)) false =
      activeValue (decode N a) (decode N b) := by
  rw [show (quittingPureStoppingTimeProfile reward fun player =>
      quittingFiniteDeadlineTimingActionTime (Bool.rec a b player)) =
      quittingPureTimeProfileBehavior reward (Bool.rec (decode N a) (decode N b)) by
    funext player time history
    cases player <;> cases a <;> cases b <;>
      simp [quittingPureStoppingTimeProfile, quittingPureTimeProfileBehavior,
        quittingPureTimeBehaviorStrategy, quittingPureTimeHazard,
        quittingFiniteDeadlineTimingActionTime, decode]]
  exact pureTime_payoff_false (decode N a) (decode N b)

theorem pureTimingPayoff_true (a b : Action N) :
    quittingTerminalPayoff reward
        (quittingPureStoppingTimeProfile reward fun player =>
          quittingFiniteDeadlineTimingActionTime (Bool.rec a b player)) true = 0 := by
  rw [show (quittingPureStoppingTimeProfile reward fun player =>
      quittingFiniteDeadlineTimingActionTime (Bool.rec a b player)) =
      quittingPureTimeProfileBehavior reward (Bool.rec (decode N a) (decode N b)) by
    funext player time history
    cases player <;> cases a <;> cases b <;>
      simp [quittingPureStoppingTimeProfile, quittingPureTimeProfileBehavior,
        quittingPureTimeBehaviorStrategy, quittingPureTimeHazard,
        quittingFiniteDeadlineTimingActionTime, decode]]
  exact TwoClockOrderedPureTimePayoff.pureTime_payoff_true _ _

theorem expect_halfLastNever (first : Option ℕ) :
    Math.Probability.expect (halfLastNever N hN) (fun action =>
      activeValue first (decode N action)) =
      (1 / 2 : ℝ) * activeValue first (some (N - 1)) +
        (1 / 2 : ℝ) * activeValue first none := by
  rw [halfLastNever, Math.Probability.expect_map]
  simp [quitLast, decode, Math.Probability.expect_eq_sum]
  norm_num

theorem finiteNash : IsQuittingFiniteDeadlineNash reward N 0 (mixed N hN) := by
  letI : ∀ player, Fintype
      ((quittingFiniteDeadlineTimingGame reward N).Strategy player) := by
    intro player
    unfold quittingFiniteDeadlineTimingGame KernelGame.ofPureEU
    infer_instance
  apply mixedNash_isQuittingFiniteDeadlineNash
  apply ((quittingFiniteDeadlineTimingGame reward N).isNash_iff_gains_nonpos
    (mixed N hN)).2
  intro who replacement
  cases who
  · unfold KernelGame.mixedGain
    change Action N at replacement
    rw [(quittingFiniteDeadlineTimingGame reward N).mixedExtension_eu,
      (quittingFiniteDeadlineTimingGame reward N).mixedExtension_eu]
    simp only [quittingFiniteDeadlineTimingGame, KernelGame.eu_ofPureEU]
    rw [Math.PMFProduct.expect_pmfPi_boolFamily,
      Math.PMFProduct.expect_pmfPi_boolFamily]
    rw [show mixed N hN true = halfLastNever N hN by rfl]
    simp [mixed, quit0, pureTimingPayoff]
    rw [expect_halfLastNever, expect_halfLastNever]
    have hOne : 1 < N := hN
    cases replacement with
    | none =>
        simp [decode, activeValue, hOne]
        norm_num
    | some time =>
        by_cases hz : time.val = 0
        · have ht : time = ⟨0, by omega⟩ := Fin.ext hz
          simp [ht]
        · have hpos : 0 < time.val := Nat.pos_of_ne_zero hz
          have hle : time.val ≤ N - 1 := by omega
          rcases lt_or_eq_of_le hle with hlt | heq
          · simp [decode, activeValue, hlt, hOne]
          · simp [decode, activeValue, heq, hOne]
  · unfold KernelGame.mixedGain
    rw [(quittingFiniteDeadlineTimingGame reward N).mixedExtension_eu,
      (quittingFiniteDeadlineTimingGame reward N).mixedExtension_eu]
    simp only [quittingFiniteDeadlineTimingGame, KernelGame.eu_ofPureEU]
    rw [Math.PMFProduct.expect_pmfPi_boolFamily,
      Math.PMFProduct.expect_pmfPi_boolFamily]
    simp [mixed, pureTimingPayoff_true]

theorem prescribed_payoff_false :
    quittingTerminalPayoff reward
        (quittingFiniteDeadlineTimingProfile reward N (mixed N hN)) false = 1 := by
  letI : ∀ player, Fintype
      ((quittingFiniteDeadlineTimingGame reward N).Strategy player) := by
    intro player
    unfold quittingFiniteDeadlineTimingGame KernelGame.ofPureEU
    infer_instance
  rw [quittingTerminalPayoff_finiteDeadlineTimingProfile_eq_mixedEU,
    (quittingFiniteDeadlineTimingGame reward N).mixedExtension_eu]
  simp only [quittingFiniteDeadlineTimingGame, KernelGame.eu_ofPureEU]
  rw [Math.PMFProduct.expect_pmfPi_boolFamily]
  rw [show mixed N hN true = halfLastNever N hN by rfl]
  simp [mixed, quit0, pureTimingPayoff]
  rw [expect_halfLastNever]
  have hOne : 1 < N := hN
  simp [decode, activeValue, hOne]
  norm_num

theorem never_reply_payoff_false :
    quittingFiniteDeadlineNeverPayoff reward N (mixed N hN) false = 1 := by
  letI : ∀ player, Fintype
      ((quittingFiniteDeadlineTimingGame reward N).Strategy player) := by
    intro player
    unfold quittingFiniteDeadlineTimingGame KernelGame.ofPureEU
    infer_instance
  unfold quittingFiniteDeadlineNeverPayoff
  change quittingTerminalPayoff reward
      (Function.update (quittingFiniteDeadlineTimingProfile reward N (mixed N hN)) false
        (quittingPureTimeBehaviorStrategy reward false
          (quittingFiniteDeadlineTimingActionTime (none : Action N)))) false = 1
  rw [quittingFiniteDeadlineTimingProfile_update_pureTime_eq_mixedEU,
    (quittingFiniteDeadlineTimingGame reward N).mixedExtension_eu]
  simp only [quittingFiniteDeadlineTimingGame, KernelGame.eu_ofPureEU]
  rw [Math.PMFProduct.expect_pmfPi_boolFamily]
  rw [Function.update_of_ne (by decide : true ≠ false)]
  rw [show mixed N hN true = halfLastNever N hN by rfl]
  simp [pureTimingPayoff]
  rw [expect_halfLastNever]
  simp [decode, activeValue]

theorem opponentNeverProduct_false :
    quittingFiniteDeadlineOpponentNeverProduct N (mixed N hN) false = 1 / 2 := by
  unfold quittingFiniteDeadlineOpponentNeverProduct quittingOpponentNeverProduct
  rw [show (Finset.univ.erase false : Finset Bool) = {true} by decide]
  simp [← Math.Probability.CompactStoppingLaw.toPMF_apply_toReal,
    quittingFiniteDeadlineTimingLaw, mixed, halfLastNever, PMF.map_apply]
  simp [quittingFiniteDeadlineTimingActionTime, quitLast]
  norm_num

theorem omitted_quitN_payoff_false :
    quittingTerminalPayoff reward
        (Function.update (quittingFiniteDeadlineTimingProfile reward N (mixed N hN)) false
          (quittingPureTimeBehaviorStrategy reward false (some N))) false = 3 / 2 := by
  rw [quittingFiniteDeadlineTimingProfile_pureTime_eq_never_add_of_le
    reward N (mixed N hN) false (le_rfl : N ≤ N)]
  rw [never_reply_payoff_false, opponentNeverProduct_false]
  simp [reward, quittingSingletonTerminal]
  norm_num

/-- Inclusive survival of a finite timing-menu law through rows strictly before `cutoff`. -/
def menuSurvival (law : PMF (Action N)) (cutoff : ℕ) : ℝ :=
  Math.Probability.expect law fun action =>
    if cutoff ≤ (decode N action).getD cutoff then 1 else 0

theorem false_survival_before_last_eq_zero :
    menuSurvival N (mixed N hN false) (N - 1) = 0 := by
  unfold menuSurvival
  rw [show mixed N hN false = PMF.pure (quit0 N hN) by rfl,
    Math.Probability.expect_pure]
  simp [decode, quit0]
  omega

theorem deleted_false_survival_before_last_eq_one :
    menuSurvival N (mixed N hN true) (N - 1) = 1 := by
  rw [show mixed N hN true = halfLastNever N hN by rfl]
  unfold menuSurvival halfLastNever
  rw [Math.Probability.expect_map]
  simp [quitLast, decode, Math.Probability.expect_eq_sum]
  have : N ≤ N - 1 + 1 := by omega
  simp [this]

theorem joint_survival_before_last_eq_zero :
    ∏ who : Bool, menuSurvival N (mixed N hN who) (N - 1) = 0 := by
  rw [show (∏ who : Bool, menuSurvival N (mixed N hN who) (N - 1)) =
      menuSurvival N (mixed N hN false) (N - 1) *
        menuSurvival N (mixed N hN true) (N - 1) by
    rw [Fintype.prod_bool, mul_comm]]
  rw [false_survival_before_last_eq_zero, deleted_false_survival_before_last_eq_one]
  norm_num

theorem actual_deleted_false_survival_eq_one {time : ℕ}
    (hlast : time ≤ N - 1) :
    quittingOpponentSurvivalWeight
        (quittingProfileLiveRoot reward
          (quittingFiniteDeadlineTimingProfile reward N (mixed N hN))) false 0 time = 1 := by
  rw [quittingOpponentSurvivalWeight_eq_prod_hazardSurvival]
  rw [show (Finset.univ.erase false : Finset Bool) = {true} by decide]
  simp only [Finset.prod_singleton]
  change quittingHazardSurvival
      (quittingBehaviorLiveHazard reward
        ((quittingFiniteDeadlineTimingProfile reward N (mixed N hN)) true)) time = 1
  rw [← stoppingLawSurvival_quittingBehaviorStoppingLaw]
  simp only [quittingFiniteDeadlineTimingProfile,
    quittingBehaviorStoppingLaw_compactStoppingLawProfile]
  simp [mixed, Math.Probability.DiscreteHazard.StoppingLaw.survival,
    Math.Probability.DiscreteHazard.StoppingLaw.finiteMass]
  apply Finset.sum_eq_zero
  intro date hdate
  have hdateLt : date < time := Finset.mem_range.mp hdate
  let finiteDate : Fin N := ⟨date, by omega⟩
  change ((quittingFiniteDeadlineTimingLaw (mixed N hN true)).toPMF
    (WithTop.some finiteDate.val)).toReal = 0
  rw [quittingFiniteDeadlineTimingLaw_apply_some]
  simp [mixed, halfLastNever, quitLast, finiteDate, PMF.map_apply]
  have hne : date ≠ N - 1 := by omega
  simp [hne]

theorem actual_deleted_false_survival_before_last_eq_one :
    quittingOpponentSurvivalWeight
        (quittingProfileLiveRoot reward
          (quittingFiniteDeadlineTimingProfile reward N (mixed N hN))) false 0 (N - 1) = 1 :=
  actual_deleted_false_survival_eq_one N hN le_rfl

theorem actual_joint_survival_eq_zero {time : ℕ}
    (htime : 1 ≤ time) :
    quittingJointSurvivalWeight
        (quittingProfileLiveRoot reward
          (quittingFiniteDeadlineTimingProfile reward N (mixed N hN))) 0 time = 0 := by
  rw [quittingJointSurvivalWeight_eq_prod]
  have hfalse : (quittingProfileLiveRoot reward
      (quittingFiniteDeadlineTimingProfile reward N (mixed N hN)) 0 false false).toReal = 0 := by
    have hs : quittingHazardSurvival (quittingBehaviorLiveHazard reward
        ((quittingFiniteDeadlineTimingProfile reward N (mixed N hN)) false)) 1 = 0 := by
      rw [← stoppingLawSurvival_quittingBehaviorStoppingLaw]
      simp only [quittingFiniteDeadlineTimingProfile,
        quittingBehaviorStoppingLaw_compactStoppingLawProfile]
      rw [Math.Probability.DiscreteHazard.StoppingLaw.survival_succ,
        Math.Probability.DiscreteHazard.StoppingLaw.survival_zero]
      change 1 - ((quittingFiniteDeadlineTimingLaw (mixed N hN false)).toPMF
        (WithTop.some 0)).toReal = 0
      rw [show 0 = (⟨0, by omega⟩ : Fin N).val by rfl,
        quittingFiniteDeadlineTimingLaw_apply_some]
      simp [mixed, quit0]
    change (quittingBehaviorLiveHazard reward
      ((quittingFiniteDeadlineTimingProfile reward N (mixed N hN)) false) 0 false).toReal = 0
    simpa [quittingHazardSurvival, Math.survivalProduct] using hs
  have hzero : quittingStationaryContinueMass
      (quittingProfileLiveRoot reward
        (quittingFiniteDeadlineTimingProfile reward N (mixed N hN)) 0) = 0 := by
    rw [quittingStationaryContinueMass_eq_prod_continueProbability]
    exact Finset.prod_eq_zero (Finset.mem_univ false) hfalse
  exact Finset.prod_eq_zero (show 0 ∈ Finset.range time by simp; omega) hzero

theorem actual_joint_survival_before_last_eq_zero :
    quittingJointSurvivalWeight
        (quittingProfileLiveRoot reward
          (quittingFiniteDeadlineTimingProfile reward N (mixed N hN))) 0 (N - 1) = 0 :=
  actual_joint_survival_eq_zero N hN (by omega)

theorem hasFiniteMenuEarlyAbsorption :
    HasQuittingFiniteMenuEarlyAbsorption reward := by
  intro error herror horizon hhorizon reach hreach lowerDeadline
  let deadline := max (horizon + 1) lowerDeadline
  have hdeadlineTwo : 2 ≤ deadline := by
    dsimp only [deadline]
    omega
  have hdeadline : max horizon lowerDeadline ≤ deadline := by
    dsimp only [deadline]
    omega
  refine ⟨deadline, hdeadline, mixed deadline hdeadlineTwo, ?_, ?_⟩
  · intro who
    have hnash := finiteNash deadline hdeadlineTwo who
    linarith
  · have hcutPositive : 1 ≤ deadline - horizon := by
      dsimp only [deadline]
      omega
    rw [actual_joint_survival_eq_zero deadline hdeadlineTwo hcutPositive]
    exact hreach

def completedMixed : Bool → PMF (Action N)
  | false => PMF.pure (quit0 N hN)
  | true => PMF.pure none

theorem completed_payoff_false :
    quittingTerminalPayoff reward
        (quittingFiniteDeadlineTimingProfile reward N (completedMixed N hN)) false = 1 := by
  letI : ∀ player, Fintype
      ((quittingFiniteDeadlineTimingGame reward N).Strategy player) := by
    intro player
    unfold quittingFiniteDeadlineTimingGame KernelGame.ofPureEU
    infer_instance
  rw [quittingTerminalPayoff_finiteDeadlineTimingProfile_eq_mixedEU,
    (quittingFiniteDeadlineTimingGame reward N).mixedExtension_eu]
  simp only [quittingFiniteDeadlineTimingGame, KernelGame.eu_ofPureEU]
  rw [Math.PMFProduct.expect_pmfPi_boolFamily]
  simp [completedMixed, pureTimingPayoff, quit0, decode, activeValue]

theorem completed_finiteNash :
    IsQuittingFiniteDeadlineNash reward N 0 (completedMixed N hN) := by
  rw [isQuittingFiniteDeadlineNash_iff_pure]
  intro who action
  letI : ∀ player, Fintype
      ((quittingFiniteDeadlineTimingGame reward N).Strategy player) := by
    intro player
    unfold quittingFiniteDeadlineTimingGame KernelGame.ofPureEU
    infer_instance
  rw [quittingFiniteDeadlineTimingProfile_update_pureTime_eq_mixedEU,
    quittingTerminalPayoff_finiteDeadlineTimingProfile_eq_mixedEU,
    (quittingFiniteDeadlineTimingGame reward N).mixedExtension_eu,
    (quittingFiniteDeadlineTimingGame reward N).mixedExtension_eu]
  simp only [quittingFiniteDeadlineTimingGame, KernelGame.eu_ofPureEU]
  rw [Math.PMFProduct.expect_pmfPi_boolFamily,
    Math.PMFProduct.expect_pmfPi_boolFamily]
  cases who
  · change Action N at action
    simp [completedMixed, pureTimingPayoff, quit0, decode, activeValue]
    cases action <;> simp
  · simp [completedMixed, pureTimingPayoff_true]

theorem completed_never_payoff_false :
    quittingFiniteDeadlineNeverPayoff reward N (completedMixed N hN) false = 0 := by
  letI : ∀ player, Fintype
      ((quittingFiniteDeadlineTimingGame reward N).Strategy player) := by
    intro player
    unfold quittingFiniteDeadlineTimingGame KernelGame.ofPureEU
    infer_instance
  unfold quittingFiniteDeadlineNeverPayoff
  change quittingTerminalPayoff reward
      (Function.update (quittingFiniteDeadlineTimingProfile reward N (completedMixed N hN)) false
        (quittingPureTimeBehaviorStrategy reward false
          (quittingFiniteDeadlineTimingActionTime (none : Action N)))) false = 0
  rw [quittingFiniteDeadlineTimingProfile_update_pureTime_eq_mixedEU,
    (quittingFiniteDeadlineTimingGame reward N).mixedExtension_eu]
  simp only [quittingFiniteDeadlineTimingGame, KernelGame.eu_ofPureEU]
  rw [Math.PMFProduct.expect_pmfPi_boolFamily]
  rw [Function.update_of_ne (by decide : true ≠ false)]
  simp [completedMixed, pureTimingPayoff, decode, activeValue]

theorem completed_opponentNeverProduct_false :
    quittingFiniteDeadlineOpponentNeverProduct N (completedMixed N hN) false = 1 := by
  unfold quittingFiniteDeadlineOpponentNeverProduct quittingOpponentNeverProduct
  rw [show (Finset.univ.erase false : Finset Bool) = {true} by decide]
  simp [← Math.Probability.CompactStoppingLaw.toPMF_apply_toReal,
    quittingFiniteDeadlineTimingLaw, completedMixed, PMF.map_apply,
    quittingFiniteDeadlineTimingActionTime]

theorem completed_fullCap_false :
    quittingContinuationBestResponseValue reward
        (quittingFiniteDeadlineTimingProfile reward N (completedMixed N hN)) false = 1 := by
  rw [quittingContinuationBestResponseValue_finiteDeadlineTimingProfile_eq_max,
    completed_never_payoff_false, completed_opponentNeverProduct_false]
  have hcap : quittingFiniteDeadlineReplyCap reward N (completedMixed N hN) false = 1 := by
    apply le_antisymm
    · rw [← completed_payoff_false N hN]
      simpa using completed_finiteNash N hN false
    · have hreply := quittingFiniteDeadline_purePayoff_le_replyCap
          reward N (completedMixed N hN) false (quit0 N hN)
      have hvalue : quittingTerminalPayoff reward
          (Function.update
            (quittingFiniteDeadlineTimingProfile reward N (completedMixed N hN)) false
            (quittingPureTimeBehaviorStrategy reward false
              (quittingFiniteDeadlineTimingActionTime (quit0 N hN)))) false = 1 := by
        letI : ∀ player, Fintype
            ((quittingFiniteDeadlineTimingGame reward N).Strategy player) := by
          intro player
          unfold quittingFiniteDeadlineTimingGame KernelGame.ofPureEU
          infer_instance
        rw [quittingFiniteDeadlineTimingProfile_update_pureTime_eq_mixedEU,
          (quittingFiniteDeadlineTimingGame reward N).mixedExtension_eu]
        simp only [quittingFiniteDeadlineTimingGame, KernelGame.eu_ofPureEU]
        rw [Math.PMFProduct.expect_pmfPi_boolFamily]
        simp [completedMixed, pureTimingPayoff, quit0, decode, activeValue]
      linarith
  rw [hcap]
  simp [reward, quittingSingletonTerminal]

theorem full_debt_false :
    quittingTerminalDeviationDebt reward
        (quittingFiniteDeadlineTimingProfile reward N (mixed N hN)) false = 1 / 2 := by
  letI : ∀ player, Fintype
      ((quittingFiniteDeadlineTimingGame reward N).Strategy player) := by
    intro player
    unfold quittingFiniteDeadlineTimingGame KernelGame.ofPureEU
    infer_instance
  unfold quittingTerminalDeviationDebt
  rw [quittingContinuationBestResponseValue_finiteDeadlineTimingProfile_eq_max,
    prescribed_payoff_false, never_reply_payoff_false, opponentNeverProduct_false]
  have hcap : quittingFiniteDeadlineReplyCap reward N (mixed N hN) false = 1 := by
    apply le_antisymm
    · rw [← prescribed_payoff_false N hN]
      simpa using finiteNash N hN false
    · have hquit : quittingTerminalPayoff reward
          (Function.update (quittingFiniteDeadlineTimingProfile reward N (mixed N hN)) false
            (quittingPureTimeBehaviorStrategy reward false
              (quittingFiniteDeadlineTimingActionTime (quit0 N hN)))) false = 1 := by
          rw [quittingFiniteDeadlineTimingProfile_update_pureTime_eq_mixedEU,
            (quittingFiniteDeadlineTimingGame reward N).mixedExtension_eu]
          simp only [quittingFiniteDeadlineTimingGame, KernelGame.eu_ofPureEU]
          rw [Math.PMFProduct.expect_pmfPi_boolFamily]
          rw [Function.update_self, Math.Probability.expect_pure,
            Function.update_of_ne (by decide : true ≠ false)]
          rw [show mixed N hN true = halfLastNever N hN by rfl]
          simp [pureTimingPayoff]
          rw [expect_halfLastNever]
          have hOne : 1 < N := hN
          simp [quit0, decode, activeValue, hOne]
          norm_num
      rw [← hquit]
      exact quittingFiniteDeadline_purePayoff_le_replyCap
        reward N (mixed N hN) false (quit0 N hN)
  rw [hcap]
  simp [reward, quittingSingletonTerminal]

theorem oneRowCap_zero (root : Bool → PMF Bool) :
    quittingFiniteRootWordCap reward [root] false 0 =
      max (1 - (root true true).toReal) (2 * (root true true).toReal) := by
  rw [quittingFiniteRootWordCap_singleton_eq_fixedOpponents]
  simp only [quittingStationaryFixedOpponentsQuitValue,
    quittingStationaryFixedOpponentsContinueReward,
    quittingStationaryFixedOpponentsContinueMass,
    quittingFixedOpponentsContinueReward, quittingFixedOpponentsQuitValue,
    quittingRootAbsorbingContribution, quittingRootExpectedPayoff]
  rw [Math.PMFProduct.expect_pmfPi_boolFamily,
    Math.PMFProduct.expect_pmfPi_boolFamily]
  simp_rw [Math.Probability.expect_eq_sum, Fintype.sum_bool]
  simp [quittingRootPayoff, reward, quittingQuitters, Finset.ext_iff,
    Finset.nonempty_iff_ne_empty]
  rw [Math.PMFProduct.pmfBool_false_toReal]
  ring_nf

def thirdQuitRoot : Bool → PMF Bool := fun _ =>
  bernoulliBool (1 / 3 : ℝ) (by norm_num) (by norm_num)

theorem finiteMenuPunishmentOperator_zero_eq_two_thirds :
    quittingFiniteMenuPunishmentOperator reward false 0 = 2 / 3 := by
  obtain ⟨root, hroot, hlower⟩ :=
    exists_quittingFiniteMenuPunishmentOperator_minimizer reward false 0
  apply le_antisymm
  · calc
      quittingFiniteMenuPunishmentOperator reward false 0 ≤
          quittingFiniteRootWordCap reward [thirdQuitRoot] false 0 :=
        hlower thirdQuitRoot
      _ = 2 / 3 := by
        rw [oneRowCap_zero]
        simp [thirdQuitRoot]
        norm_num
  · rw [← hroot, oneRowCap_zero]
    let q := (root true true).toReal
    by_cases hq : q ≤ 1 / 3
    · exact le_max_of_le_left (by linarith)
    · exact le_max_of_le_right (by linarith)

theorem finiteMenuPunishmentValue_one_eq_two_thirds :
    quittingFiniteMenuPunishmentValue reward 1 false = 2 / 3 := by
  rw [quittingFiniteMenuPunishmentValue_eq_operator_iterate]
  change quittingFiniteMenuPunishmentOperator reward false 0 = 2 / 3
  exact finiteMenuPunishmentOperator_zero_eq_two_thirds

theorem stationaryUnilateralCap_false (root : Bool → PMF Bool) :
    quittingStationaryUnilateralCap reward root false =
      if (root true true).toReal = 0 then 1 else 2 := by
  rw [quittingStationaryUnilateralCap_eq_max_div]
  simp only [quittingStationaryFixedOpponentsQuitValue,
    quittingStationaryFixedOpponentsContinueReward,
    quittingStationaryFixedOpponentsContinueMass,
    quittingFixedOpponentsContinueReward, quittingFixedOpponentsQuitValue,
    quittingRootAbsorbingContribution, quittingRootExpectedPayoff]
  rw [Math.PMFProduct.expect_pmfPi_boolFamily,
    Math.PMFProduct.expect_pmfPi_boolFamily]
  simp_rw [Math.Probability.expect_eq_sum, Fintype.sum_bool]
  simp [quittingRootPayoff, reward, quittingQuitters, Finset.ext_iff,
    Finset.nonempty_iff_ne_empty]
  rw [quittingFixedOpponentsContinueMass_bool_false,
    Math.PMFProduct.pmfBool_false_toReal]
  by_cases hq : (root true true).toReal = 0
  · simp [hq]
  · have hcancel : (root true true).toReal * 2 / (root true true).toReal = 2 := by
      field_simp
    simp [hq, hcancel]
    have hnonneg : 0 ≤ (root true true).toReal := ENNReal.toReal_nonneg
    linarith

theorem fullPunishmentValue_false_eq_one :
    quittingPunishmentValue reward false = 1 := by
  rw [quittingPunishmentValue_eq_stationaryPunishmentValue]
  unfold quittingStationaryPunishmentValue
  apply le_antisymm
  · have h := ciInf_le (show BddBelow (Set.range fun root : Bool → PMF Bool =>
        quittingStationaryUnilateralCap reward root false) from by
          refine ⟨-2, ?_⟩
          rintro _ ⟨root, rfl⟩
          dsimp only
          rw [stationaryUnilateralCap_false]
          split <;> norm_num) (fun _ => PMF.pure false)
    simpa [stationaryUnilateralCap_false] using h
  · apply le_ciInf
    intro root
    rw [stationaryUnilateralCap_false]
    split <;> norm_num

end GameTheory.TwoClockFiniteMenuRegression

namespace GameTheory.OnePlayerSignedBoundaryRegression

open OnePlayerFiniteMenuBoundary

theorem negative_full_and_finitePureReply_boundary :
    quittingPunishmentValue (reward (-1)) PUnit.unit = 0 ∧
      quittingFinitePureReplyPunishmentValue (reward (-1)) PUnit.unit = -1 := by
  constructor
  · rw [punishmentValue_eq_max]
    norm_num
  · rw [quittingFinitePureReplyPunishmentValue_eq_min, punishmentValue_eq_max]
    norm_num [quittingSoloReward, quittingSingletonTerminal, reward]

end GameTheory.OnePlayerSignedBoundaryRegression
