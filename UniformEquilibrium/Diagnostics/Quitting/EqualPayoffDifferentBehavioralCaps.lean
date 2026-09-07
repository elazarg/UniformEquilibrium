import UniformEquilibrium.Diagnostics.Quitting.AbsorptionWeightedRareInferiorActionBoundary
import UniformEquilibrium.Quitting.Terminal.TailCompression.ElementaryCaps

/-!
# Equal prescribed payoff with different unrestricted behavioral caps

For the sparse four-player reward table already used by the rare-action
boundary, compare two actual pure chronological profiles.  Player zero quits
at date zero in both.  In the first, player one is scheduled to quit at date
one if play remains live; in the second, every opponent continues forever.
The prescribed payoff is zero in both profiles, but player zero's unrestricted
behavioral best-response cap is respectively one and zero.
-/

noncomputable section

namespace GameTheory.EqualPayoffDifferentBehavioralCaps

open QuittingSureSetOwnerRepair
open AbsorptionWeightedRareInferiorActionBoundary

/-- Player zero quits now; if that action is counterfactually replaced by
Continue, player one quits at the next date. -/
def zeroThenOneProfile :
    (quittingGame reward).BehaviorProfile :=
  quittingRootThenContinuationProfile reward (quittingPureSetRoot {0})
    (quittingRootThenContinuationProfile reward (quittingPureSetRoot {1})
      (quittingAlwaysContinueProfile reward))

/-- Player zero quits now and every player continues forever after that first
date. -/
def zeroThenNeverProfile :
    (quittingGame reward).BehaviorProfile :=
  quittingRootThenContinuationProfile reward (quittingPureSetRoot {0})
    (quittingAlwaysContinueProfile reward)

/-- Both actual chronological profiles have the zero prescribed payoff. -/
theorem zeroThenOne_terminalPayoff_eq_zero :
    quittingTerminalPayoff reward zeroThenOneProfile = 0 := by
  funext player
  unfold zeroThenOneProfile
  rw [quittingTerminalPayoff_pureSetRootThenContinuation_eq_setReward
    ({0} : Finset (Fin 4)) (by simp)]
  fin_cases player <;> norm_num [quittingSetReward, reward]

/-- The profile with an all-Continue tail has the same zero prescribed
payoff. -/
theorem zeroThenNever_terminalPayoff_eq_zero :
    quittingTerminalPayoff reward zeroThenNeverProfile = 0 := by
  funext player
  unfold zeroThenNeverProfile
  rw [quittingTerminalPayoff_pureSetRootThenContinuation_eq_setReward
    ({0} : Finset (Fin 4)) (by simp)]
  fin_cases player <;> norm_num [quittingSetReward, reward]

private theorem playerZero_cap_after_zero_root
    (continuation : (quittingGame reward).BehaviorProfile) :
    quittingContinuationBestResponseValue reward
        (quittingRootThenContinuationProfile reward
          (quittingPureSetRoot {0}) continuation) 0 =
      max 0 (quittingContinuationBestResponseValue reward continuation 0) := by
  rw [quittingContinuationBestResponseValue_rootThenContinuation_eq_max,
    quittingRootQuitPayoff_pureSetRoot_eq_insert,
    quittingRootContinuePayoff_pureSingleton_eq_tail]
  norm_num [quittingSetReward, reward]

private theorem playerZero_cap_after_one_root
    (continuation : (quittingGame reward).BehaviorProfile) :
    quittingContinuationBestResponseValue reward
        (quittingRootThenContinuationProfile reward
          (quittingPureSetRoot {1}) continuation) 0 = 1 := by
  rw [quittingContinuationBestResponseValue_rootThenContinuation_eq_max,
    quittingRootQuitPayoff_pureSetRoot_eq_insert,
    quittingRootContinuePayoff_pureSetRoot_eq_erase_of_nonempty]
  · norm_num [quittingSetReward, reward]
  · norm_num

/-- Against the date-one quit of player one, player zero's full behavioral
response cap is one.  Continuing at date zero attains the bound. -/
theorem zeroThenOne_playerZero_responseCap :
    quittingContinuationBestResponseValue reward zeroThenOneProfile 0 = 1 := by
  unfold zeroThenOneProfile
  rw [playerZero_cap_after_zero_root, playerZero_cap_after_one_root]
  norm_num

/-- Against opponents who never quit, player zero's full behavioral response
cap is zero. -/
theorem zeroThenNever_playerZero_responseCap :
    quittingContinuationBestResponseValue reward zeroThenNeverProfile 0 = 0 := by
  unfold zeroThenNeverProfile
  rw [playerZero_cap_after_zero_root,
    quittingContinuationBestResponseValue_quittingAlwaysContinueProfile]
  norm_num [reward, quittingSingletonTerminal]

/-- The two actual pure chronological profiles have exactly the same
prescribed payoff and different unrestricted behavioral response caps. -/
theorem equal_terminalPayoff_and_different_playerZero_responseCaps :
    quittingTerminalPayoff reward zeroThenOneProfile =
        quittingTerminalPayoff reward zeroThenNeverProfile ∧
      quittingContinuationBestResponseValue reward zeroThenOneProfile 0 = 1 ∧
      quittingContinuationBestResponseValue reward zeroThenNeverProfile 0 = 0 := by
  exact ⟨zeroThenOne_terminalPayoff_eq_zero.trans
      zeroThenNever_terminalPayoff_eq_zero.symm,
    zeroThenOne_playerZero_responseCap,
    zeroThenNever_playerZero_responseCap⟩

end GameTheory.EqualPayoffDifferentBehavioralCaps
