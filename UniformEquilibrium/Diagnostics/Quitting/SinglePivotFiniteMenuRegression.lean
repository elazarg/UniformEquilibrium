import UniformEquilibrium.Quitting.Terminal.SinglePivotFiniteMenuSource
import UniformEquilibrium.Diagnostics.Quitting.FiniteDeadlineTimingRecursion
import UniformEquilibrium.Quitting.Paths.SureExitSet

noncomputable section

namespace GameTheory
namespace SinglePivotFiniteMenuSurePivotFixture

open Math.Probability Math.ProbabilityMassFunction
open QuittingSureSetOwnerRepair

abbrev Action := QuittingFiniteDeadlineTimingAction 1

def quit0 : Action := some ⟨0, by omega⟩

def reward : {S : Finset Bool // S.Nonempty} → Payoff Bool := fun terminal who =>
  if who then 0 else if terminal.val = {false} then 1
    else if terminal.val = {true} then 0 else -1

theorem canonical : IsSinglePivotSingletonTable reward false := by
  intro who
  cases who <;> simp [reward, quittingSingletonTerminal]

def halfLaw : PMF Action :=
  (Math.ProbabilityMassFunction.bernoulliBool (1 / 2 : ℝ) (by norm_num) (by norm_num)).map
    (fun b => if b then quit0 else none)

def mixed : Bool → PMF Action
  | false => PMF.pure quit0
  | true => halfLaw

@[simp] theorem mixed_pivot_never : (mixed false none).toReal = 0 := by
  simp [mixed, quit0]

@[simp] theorem mixed_other_never : (mixed true none).toReal = 1 / 2 := by
  simp [mixed, halfLaw, quit0, PMF.map_apply]
  norm_num

@[simp] theorem mixed_other_quit0 : (mixed true quit0).toReal = 1 / 2 := by
  simp [mixed, halfLaw, quit0, PMF.map_apply]

theorem pureTimingPayoff (a b : Action) (who : Bool) :
    quittingTerminalPayoff reward
        (quittingPureStoppingTimeProfile reward fun player =>
          quittingFiniteDeadlineTimingActionTime (Bool.rec a b player)) who =
      match a, b with
      | none, none => 0
      | none, some _ => 0
      | some _, none => if who then 0 else 1
      | some _, some _ => if who then 0 else -1 := by
  cases a with
  | none =>
      cases b with
      | none =>
          simp only
          rw [show (fun player => quittingFiniteDeadlineTimingActionTime
              (Bool.rec (none : Action) (none : Action) player)) =
                fun _ => (⊤ : WithTop ℕ) by
            funext player; cases player <;> rfl]
          change quittingTerminalPayoff reward
            (quittingPureStoppingTimeProfile reward fun _ => (⊤ : WithTop ℕ)) who = 0
          rw [show quittingPureStoppingTimeProfile reward (fun _ => (⊤ : WithTop ℕ)) =
              quittingAlwaysContinueProfile reward by
            funext player time history
            simp [quittingPureStoppingTimeProfile, quittingPureTimeBehaviorStrategy,
              quittingPureTimeHazard, quittingAlwaysContinueProfile,
              StochasticGame.stationaryBehaviorProfile]; rfl]
          exact quittingTerminalPayoff_quittingAlwaysContinue reward who
      | some tb =>
          have htb : (some tb : Action) = quit0 := by
            congr
            exact Subsingleton.elim _ _
          rw [htb]
          rw [show (fun player => quittingFiniteDeadlineTimingActionTime
              (Bool.rec (none : Action) quit0 player)) = Bool.rec ⊤ 0 by
            funext player; cases player <;> rfl]
          change quittingTerminalPayoff reward
            (quittingPureStoppingTimeProfile reward (Bool.rec ⊤ 0)) who = 0
          rw [show quittingPureStoppingTimeProfile reward (Bool.rec ⊤ 0) =
              quittingRootThenContinuationProfile reward (quittingPureSetRoot {true})
                (quittingAlwaysContinueProfile reward) by
            funext player time history
            cases player <;> cases time <;>
              simp [quittingPureStoppingTimeProfile, quittingPureTimeBehaviorStrategy,
                quittingPureTimeHazard, quittingRootThenContinuationProfile,
                quittingPureSetRoot, quittingSetAction, quittingAlwaysContinueProfile,
                StochasticGame.stationaryBehaviorProfile] <;> rfl]
          rw [quittingTerminalPayoff_pureSetRootThenContinuation_eq_setReward]
          · cases who <;> simp [quittingSetReward, reward]
          · simp
  | some ta =>
      have hta : (some ta : Action) = quit0 := by
        congr
        exact Subsingleton.elim _ _
      rw [hta]
      cases b with
      | none =>
          rw [show (fun player => quittingFiniteDeadlineTimingActionTime
              (Bool.rec quit0 (none : Action) player)) = Bool.rec 0 ⊤ by
            funext player; cases player <;> rfl]
          change quittingTerminalPayoff reward
            (quittingPureStoppingTimeProfile reward (Bool.rec 0 ⊤)) who =
              (if who then 0 else 1)
          rw [show quittingPureStoppingTimeProfile reward (Bool.rec 0 ⊤) =
              quittingRootThenContinuationProfile reward (quittingPureSetRoot {false})
                (quittingAlwaysContinueProfile reward) by
            funext player time history
            cases player <;> cases time <;>
              simp [quittingPureStoppingTimeProfile, quittingPureTimeBehaviorStrategy,
                quittingPureTimeHazard, quittingRootThenContinuationProfile,
                quittingPureSetRoot, quittingSetAction, quittingAlwaysContinueProfile,
                StochasticGame.stationaryBehaviorProfile] <;> rfl]
          rw [quittingTerminalPayoff_pureSetRootThenContinuation_eq_setReward]
          · cases who <;> simp [quittingSetReward, reward]
          · simp
      | some tb =>
          have htb : (some tb : Action) = quit0 := by
            congr
            exact Subsingleton.elim _ _
          rw [htb]
          rw [show (fun player => quittingFiniteDeadlineTimingActionTime
              (Bool.rec quit0 quit0 player)) =
                fun _ => (0 : WithTop ℕ) by
            funext player; cases player <;> rfl]
          change quittingTerminalPayoff reward
            (quittingPureStoppingTimeProfile reward (fun _ => 0)) who =
              (if who then 0 else -1)
          rw [show quittingPureStoppingTimeProfile reward (fun _ => 0) =
              quittingRootThenContinuationProfile reward (quittingPureSetRoot {false, true})
                (quittingAlwaysContinueProfile reward) by
            funext player time history
            cases player <;> cases time <;>
              simp [quittingPureStoppingTimeProfile, quittingPureTimeBehaviorStrategy,
                quittingPureTimeHazard, quittingRootThenContinuationProfile,
                quittingPureSetRoot, quittingSetAction, quittingAlwaysContinueProfile,
                StochasticGame.stationaryBehaviorProfile] <;> rfl]
          rw [quittingTerminalPayoff_pureSetRootThenContinuation_eq_setReward]
          · cases who <;> simp [quittingSetReward, reward, Finset.ext_iff]
          · simp

theorem finiteNash :
    IsQuittingFiniteDeadlineNash reward 1 0 mixed := by
  letI : ∀ player, Fintype
      ((quittingFiniteDeadlineTimingGame reward 1).Strategy player) := by
    intro player
    unfold quittingFiniteDeadlineTimingGame KernelGame.ofPureEU
    infer_instance
  apply mixedNash_isQuittingFiniteDeadlineNash
  apply ((quittingFiniteDeadlineTimingGame reward 1).isNash_iff_gains_nonpos mixed).2
  intro who replacement
  cases who
  · unfold KernelGame.mixedGain
    rw [(quittingFiniteDeadlineTimingGame reward 1).mixedExtension_eu,
      (quittingFiniteDeadlineTimingGame reward 1).mixedExtension_eu]
    simp only [quittingFiniteDeadlineTimingGame, KernelGame.eu_ofPureEU]
    rw [Math.PMFProduct.expect_pmfPi_boolFamily,
      Math.PMFProduct.expect_pmfPi_boolFamily]
    simp [mixed, halfLaw, quit0, pureTimingPayoff]
    cases replacement with
    | none =>
        simp [Math.Probability.expect_eq_sum]
        norm_num
    | some time =>
        fin_cases time
        simp [Math.Probability.expect_eq_sum]
  · unfold KernelGame.mixedGain
    rw [(quittingFiniteDeadlineTimingGame reward 1).mixedExtension_eu,
      (quittingFiniteDeadlineTimingGame reward 1).mixedExtension_eu]
    simp only [quittingFiniteDeadlineTimingGame, KernelGame.eu_ofPureEU]
    rw [Math.PMFProduct.expect_pmfPi_boolFamily,
      Math.PMFProduct.expect_pmfPi_boolFamily]
    simp [mixed, halfLaw, quit0, pureTimingPayoff]
    cases replacement with
    | none =>
        simp [Math.Probability.expect_eq_sum]
    | some time =>
        fin_cases time
        simp [Math.Probability.expect_eq_sum]

theorem pivot_payoff_eq_zero :
    quittingTerminalPayoff reward
        (quittingFiniteDeadlineTimingProfile reward 1 mixed) false = 0 := by
  letI : ∀ player, Fintype
      ((quittingFiniteDeadlineTimingGame reward 1).Strategy player) := by
    intro player
    unfold quittingFiniteDeadlineTimingGame KernelGame.ofPureEU
    infer_instance
  rw [quittingTerminalPayoff_finiteDeadlineTimingProfile_eq_mixedEU,
    (quittingFiniteDeadlineTimingGame reward 1).mixedExtension_eu]
  simp only [quittingFiniteDeadlineTimingGame, KernelGame.eu_ofPureEU]
  rw [Math.PMFProduct.expect_pmfPi_boolFamily]
  simp [mixed, halfLaw, quit0, pureTimingPayoff, Math.Probability.expect_eq_sum]
  norm_num

theorem pivot_never_payoff_eq_zero :
    quittingFiniteDeadlineNeverPayoff reward 1 mixed false = 0 := by
  letI : ∀ player, Fintype
      ((quittingFiniteDeadlineTimingGame reward 1).Strategy player) := by
    intro player
    unfold quittingFiniteDeadlineTimingGame KernelGame.ofPureEU
    infer_instance
  unfold quittingFiniteDeadlineNeverPayoff
  change quittingTerminalPayoff reward
      (Function.update (quittingFiniteDeadlineTimingProfile reward 1 mixed) false
        (quittingPureTimeBehaviorStrategy reward false
          (quittingFiniteDeadlineTimingActionTime (none : Action)))) false = 0
  rw [quittingFiniteDeadlineTimingProfile_update_pureTime_eq_mixedEU,
    (quittingFiniteDeadlineTimingGame reward 1).mixedExtension_eu]
  simp only [quittingFiniteDeadlineTimingGame, KernelGame.eu_ofPureEU]
  rw [Math.PMFProduct.expect_pmfPi_boolFamily]
  simp [mixed, halfLaw, quit0, pureTimingPayoff, Math.Probability.expect_eq_sum]

theorem opponentNeverProduct_eq_half :
    quittingFiniteDeadlineOpponentNeverProduct 1 mixed false = 1 / 2 := by
  unfold quittingFiniteDeadlineOpponentNeverProduct quittingOpponentNeverProduct
  rw [show (Finset.univ.erase false : Finset Bool) = {true} by decide]
  simp [
    ← Math.Probability.CompactStoppingLaw.toPMF_apply_toReal,
    quittingFiniteDeadlineTimingLaw, mixed, halfLaw, PMF.map_apply]
  simp [quittingFiniteDeadlineTimingActionTime, quit0]
  norm_num

theorem jointNeverProduct_eq_zero :
    quittingFiniteDeadlineJointNeverProduct 1 mixed = 0 :=
  finiteDeadlineJointNeverProduct_eq_zero_of_player_never_eq_zero 1 mixed false
    mixed_pivot_never

theorem pivot_fullDebt_eq_half :
    quittingTerminalDeviationDebt reward
        (quittingFiniteDeadlineTimingProfile reward 1 mixed) false = 1 / 2 := by
  rw [singlePivot_exactMenuNash_pivot_debt_eq_deletedNever_of_payoff_eq_never
    reward false canonical 1 mixed finiteNash]
  · exact opponentNeverProduct_eq_half
  · rw [pivot_payoff_eq_zero, pivot_never_payoff_eq_zero]

/-- The literal one-date fixture simultaneously realizes the menu equilibrium,
zero joint-Never mass, and the unrestricted half-unit pivot debt. -/
theorem exactNash_jointNever_zero_fullDebt_half :
    IsQuittingFiniteDeadlineNash reward 1 0 mixed ∧
      quittingFiniteDeadlineJointNeverProduct 1 mixed = 0 ∧
      quittingTerminalDeviationDebt reward
        (quittingFiniteDeadlineTimingProfile reward 1 mixed) false = 1 / 2 :=
  ⟨finiteNash, jointNeverProduct_eq_zero, pivot_fullDebt_eq_half⟩

end SinglePivotFiniteMenuSurePivotFixture
end GameTheory
