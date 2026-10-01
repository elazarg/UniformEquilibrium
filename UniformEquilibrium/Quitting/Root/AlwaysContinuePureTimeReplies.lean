import UniformEquilibrium.Quitting.Root.PureTimeCapPrefixSelection

/-! # Actual pure-time replies against perpetual continuation

Every finite quitting date pays the observer's actual singleton reward;
Never pays zero. The proof delegates to the common root-prefix payoff
identities, so diagnostics and literal source examples share one owner.
-/

noncomputable section

namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem quittingRootThenAlwaysContinueProfile_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    quittingRootThenContinuationProfile reward quittingAllContinueRoot
        (quittingAlwaysContinueProfile reward) =
      quittingAlwaysContinueProfile reward := by
  funext who time history
  cases time <;> rfl

theorem quittingAlwaysContinueProfile_update_pureTime_none
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (who : ι) :
    Function.update (quittingAlwaysContinueProfile reward) who
        (quittingPureTimeBehaviorStrategy reward who none) =
      quittingAlwaysContinueProfile reward := by
  rw [show quittingPureTimeBehaviorStrategy reward who none =
    quittingAlwaysContinueProfile reward who from rfl]
  exact Function.update_eq_self who _

theorem quittingTerminalPayoff_alwaysContinueProfile_update_pureTime_none
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (who : ι) :
    quittingTerminalPayoff reward
        (Function.update (quittingAlwaysContinueProfile reward) who
          (quittingPureTimeBehaviorStrategy reward who none)) who = 0 := by
  rw [quittingAlwaysContinueProfile_update_pureTime_none,
    quittingTerminalPayoff_quittingAlwaysContinue]

theorem quittingTerminalPayoff_alwaysContinueProfile_update_pureTime_some
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (who : ι) (date : ℕ) :
    quittingTerminalPayoff reward
        (Function.update (quittingAlwaysContinueProfile reward) who
          (quittingPureTimeBehaviorStrategy reward who (some date))) who =
      reward (quittingSingletonTerminal who) who := by
  induction date with
  | zero =>
      have h := quittingTerminalPayoff_rootThen_pureTime_zero_eq_quitPayoff
        reward quittingAllContinueRoot (quittingAlwaysContinueProfile reward) who
      rw [quittingRootThenAlwaysContinueProfile_eq,
        quittingRootQuitPayoff_allContinueRoot] at h
      exact h
  | succ date ih =>
      have h := quittingTerminalPayoff_rootThen_pureTime_map_succ_eq_continuePayoff
        reward quittingAllContinueRoot (quittingAlwaysContinueProfile reward) who (some date)
      simp only [Option.map_some, Nat.succ_eq_add_one] at h
      rw [quittingRootThenAlwaysContinueProfile_eq,
        quittingRootContinuePayoff_allContinueRoot, Function.update_self] at h
      exact h.trans ih

end GameTheory
