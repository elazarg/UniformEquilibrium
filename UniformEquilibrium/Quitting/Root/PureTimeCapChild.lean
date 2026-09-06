import UniformEquilibrium.Quitting.Root.TerminalGapPrefixDebtorTransport

/-! # Literal pure-time cap children

Replacing one player's strategy by a finite pure stopping time preserves the literal
opponents and exposes the consequences of actual best-response cap attainment.
-/

noncomputable section
namespace GameTheory

open Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The literal profile obtained by installing one owner's finite pure stopping time. -/
def quittingPureTimeCapChild
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (owner : ι) (deadline : ℕ) : (quittingGame reward).BehaviorProfile :=
  Function.update profile owner
    (quittingPureTimeBehaviorStrategy reward owner (some deadline))

/-- An actual cap-attaining child has zero remaining deviation debt for its owner. -/
theorem quittingPureTimeCapChild_ownerDebt_eq_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (owner : ι) (deadline : ℕ)
    (hattains : quittingTerminalPayoff reward
        (quittingPureTimeCapChild reward profile owner deadline) owner =
      quittingContinuationBestResponseValue reward profile owner) :
    quittingTerminalDeviationDebt reward
      (quittingPureTimeCapChild reward profile owner deadline) owner = 0 := by
  exact quittingTerminalDeviationDebt_update_eq_zero_of_attainsCap
    reward profile owner
      (quittingPureTimeBehaviorStrategy reward owner (some deadline)) hattains

/-- The cap-attaining owner's payoff gain is exactly the parent profile's debt. -/
theorem quittingPureTimeCapChild_ownerGain_eq_debt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (owner : ι) (deadline : ℕ)
    (hattains : quittingTerminalPayoff reward
        (quittingPureTimeCapChild reward profile owner deadline) owner =
      quittingContinuationBestResponseValue reward profile owner) :
    quittingTerminalPayoff reward
          (quittingPureTimeCapChild reward profile owner deadline) owner -
        quittingTerminalPayoff reward profile owner =
      quittingTerminalDeviationDebt reward profile owner := by
  rw [hattains]
  rfl

/-- The installed owner quits surely at the literal deadline. -/
theorem quittingPureTimeCapChild_sure_owner_at_deadline
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (owner : ι) (deadline : ℕ) :
    quittingProfileLiveRoot reward
        (quittingPureTimeCapChild reward profile owner deadline)
        deadline owner = PMF.pure true := by
  unfold quittingPureTimeCapChild
  rw [quittingProfileLiveRoot_update_eq_rootSequenceUpdate]
  unfold quittingRootSequenceUpdate
  simp [quittingBehaviorLiveHazard,
    quittingPureTimeBehaviorStrategy, quittingPureTimeHazard]

end GameTheory
