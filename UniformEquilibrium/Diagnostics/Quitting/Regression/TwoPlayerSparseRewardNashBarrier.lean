/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.OneDateProductRootCaps
import UniformEquilibrium.Diagnostics.Quitting.ProductRootLimitCapSandwich
import UniformEquilibrium.Quitting.Paths.SureExitSet

/-!
# A product-realizable reward law that is not Nash

The pure pair outcome is realized at one product row and pays `(2,2)`, but
either player gains one by continuing and leaving the opponent as sole
quitter.  This distinguishes reward-law realization from equilibrium.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.PMFProduct QuittingSureSetOwnerRepair

/-- The two-player reward table `(1,3)`, `(3,1)`, `(2,2)` on the two
singletons and the pair. -/
def twoPlayerSparseRewardNashBarrier
    (terminal : {S : Finset (Fin 2) // S.Nonempty}) : Payoff (Fin 2) :=
  fun player =>
    if terminal.val = ({0} : Finset (Fin 2)) then
      if player = 0 then 1 else 3
    else if terminal.val = ({1} : Finset (Fin 2)) then
      if player = 0 then 3 else 1
    else 2

/-- Both players Quit at date zero and Continue forever afterwards. -/
def twoPlayerPurePairThenNeverProfile :
    (quittingGame twoPlayerSparseRewardNashBarrier).BehaviorProfile :=
  quittingOneDateThenNeverProfile twoPlayerSparseRewardNashBarrier
    (quittingPureSetRoot Finset.univ)

private theorem twoPlayerPurePairRoot_coalitionMass
    (terminal : Finset (Fin 2)) :
    quittingRootCoalitionMass (quittingPureSetRoot Finset.univ) terminal =
      if terminal = Finset.univ then 1 else 0 := by
  rw [quittingRootCoalitionMass_eq_pmfPi]
  change ((pmfPi (fun _ : Fin 2 => PMF.pure true))
    (quittingCoalitionAction terminal)).toReal = _
  rw [pmfPi_pure]
  by_cases heq : terminal = Finset.univ
  · subst terminal
    have haction : quittingCoalitionAction (Finset.univ : Finset (Fin 2)) =
        fun _ => true := by
      funext player
      simp [quittingCoalitionAction]
    rw [haction]
    simp
  · have haction : quittingCoalitionAction terminal ≠ fun _ => true := by
      intro h
      apply heq
      apply Finset.eq_univ_of_forall
      intro player
      have := congrFun h player
      simpa [quittingCoalitionAction] using this
    simp [PMF.pure_apply, haction, heq]

/-- The prescribed payoff of the pure pair profile is exactly two for both
players. -/
theorem twoPlayerPurePairThenNever_terminalPayoff (player : Fin 2) :
    quittingTerminalPayoff twoPlayerSparseRewardNashBarrier
      twoPlayerPurePairThenNeverProfile player = 2 := by
  unfold twoPlayerPurePairThenNeverProfile quittingOneDateThenNeverProfile
  rw [quittingTerminalPayoff_pureSetRootThenContinuation_eq_setReward
    Finset.univ (by simp)]
  fin_cases player <;>
    norm_num [quittingSetReward, twoPlayerSparseRewardNashBarrier,
      Finset.ext_iff]

/-- The complete terminal law is the pure pair atom, so it is literally a
one-row product law. -/
theorem twoPlayerPurePairThenNever_terminalOutcomeMass
    (outcome : QuittingTerminalOutcome (Fin 2)) :
    quittingTerminalOutcomeMass twoPlayerSparseRewardNashBarrier
      twoPlayerPurePairThenNeverProfile outcome =
        if outcome = some ⟨Finset.univ, by simp⟩ then 1 else 0 := by
  unfold twoPlayerPurePairThenNeverProfile
  cases outcome with
  | none =>
      rw [productRoot_terminalOutcomeMass_oneDateThenNever_none
        twoPlayerSparseRewardNashBarrier (quittingPureSetRoot Finset.univ)
        (quitter := 0)]
      · simp
      · simp [quittingPureSetRoot, quittingSetAction]
  | some terminal =>
      rw [productRoot_terminalOutcomeMass_oneDateThenNever_some
        twoPlayerSparseRewardNashBarrier (quittingPureSetRoot Finset.univ)
        (quitter := 0)]
      · rw [twoPlayerPurePairRoot_coalitionMass]
        simp only [Option.some.injEq, Subtype.ext_iff]
      · simp [quittingPureSetRoot, quittingSetAction]

/-- If player zero Continues instead, player one is the sole quitter and
player zero receives three. -/
theorem twoPlayerPurePairThenNever_playerZero_continuePayoff :
    quittingTerminalPayoff twoPlayerSparseRewardNashBarrier
        (Function.update twoPlayerPurePairThenNeverProfile 0
          (quittingPureTimeBehaviorStrategy
            twoPlayerSparseRewardNashBarrier 0 none)) 0 = 3 := by
  change quittingPureTimeDeviationPayoff twoPlayerSparseRewardNashBarrier
    twoPlayerPurePairThenNeverProfile 0 none = 3
  unfold twoPlayerPurePairThenNeverProfile
  rw [oneDateProductPureTimeDeviationPayoff_oneDateThenNever_none]
  unfold oneDateProductContinueEndpoint
  rw [quittingRootContinuePayoff_pureSetRoot_eq_erase_of_nonempty]
  · norm_num [quittingSetReward, twoPlayerSparseRewardNashBarrier,
      Finset.ext_iff]
    intro hsubsingleton
    have heq : (0 : Fin 2) = 1 := hsubsingleton.elim 0 1
    norm_num at heq
  · exact (by decide)

/-- If player one Continues instead, player zero is the sole quitter and
player one receives three. -/
theorem twoPlayerPurePairThenNever_playerOne_continuePayoff :
    quittingTerminalPayoff twoPlayerSparseRewardNashBarrier
        (Function.update twoPlayerPurePairThenNeverProfile 1
          (quittingPureTimeBehaviorStrategy
            twoPlayerSparseRewardNashBarrier 1 none)) 1 = 3 := by
  change quittingPureTimeDeviationPayoff twoPlayerSparseRewardNashBarrier
    twoPlayerPurePairThenNeverProfile 1 none = 3
  unfold twoPlayerPurePairThenNeverProfile
  rw [oneDateProductPureTimeDeviationPayoff_oneDateThenNever_none]
  unfold oneDateProductContinueEndpoint
  rw [quittingRootContinuePayoff_pureSetRoot_eq_erase_of_nonempty]
  · norm_num [quittingSetReward, twoPlayerSparseRewardNashBarrier,
      Finset.ext_iff]
    intro hsubsingleton
    have heq : (0 : Fin 2) = 1 := hsubsingleton.elim 0 1
    norm_num at heq
  · exact (by decide)

/-- For every error below one, the product-realizing profile is not a
terminal approximate Nash equilibrium. -/
theorem not_twoPlayerPurePairThenNever_terminalApproximateNash
    {epsilon : ℝ} (hepsilon : epsilon < 1) :
    ¬ (quittingGame twoPlayerSparseRewardNashBarrier).IsεAsymptoticNash
      (quittingTerminalPayoff twoPlayerSparseRewardNashBarrier) epsilon
      twoPlayerPurePairThenNeverProfile := by
  intro hnash
  have hdeviation := hnash 0
    (quittingPureTimeBehaviorStrategy twoPlayerSparseRewardNashBarrier 0 none)
  rw [twoPlayerPurePairThenNever_terminalPayoff,
    twoPlayerPurePairThenNever_playerZero_continuePayoff] at hdeviation
  linarith

end GameTheory
