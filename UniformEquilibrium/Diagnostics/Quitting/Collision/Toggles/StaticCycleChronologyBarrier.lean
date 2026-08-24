/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.Collision.Toggles.ReachableSimpleCycle
import UniformEquilibrium.Quitting.Boundary.Repair.JointComplementarity
import UniformEquilibrium.Quitting.Root.LiteralExactPrefixStack

/-!
# Why a static strict-toggle cycle is not a quitting chronology

A coalition vertex denotes an absorbing action, not a live continuation
state.  The literal compiler that replaces successive vertices by pure-set
roots therefore stops at its first nonempty vertex: joint survival beyond
that row is exactly zero, and its payoff is independent of every later root.

The unilateral audit has one additional sharp boundary.  If a player leaves
a coalition with another quitter, the static leave payoff is the correct
root endpoint.  If the coalition is that player's singleton, however, pure
Continue exposes the actual continuation payoff, whereas the static toggle
uses the artificial empty-coalition value zero.  The two agree exactly when
that continuation coordinate is zero.  A negative singleton followed by the
actual all-Continue continuation gives a literal behavioral-deviation
counterexample to the naive compiler.

Thus a compiler needs live roots of positive joint survival and Bellman/source
matching for their continuation payoffs.  Static coalition inequalities alone
provide neither datum.
-/

noncomputable section

namespace GameTheory

open QuittingSureSetOwnerRepair

variable {iota : Type} [Fintype iota] [DecidableEq iota]
variable {reward : {S : Finset iota // S.Nonempty} → Payoff iota}

/-- The literal but invalid attempt to execute a static coalition stream:
make exactly the displayed coalition quit surely at each live row. -/
def quittingNaiveStaticCoalitionRoots
    (coalitions : ℕ → Finset iota) : ℕ → iota → PMF Bool :=
  fun time => quittingPureSetRoot (coalitions time)

/-- A nonempty first static vertex kills all joint survival.  In particular,
none of the later vertices in a naively repeated static cycle is reached. -/
theorem quittingJointSurvivalWeight_naiveStaticCoalitions_eq_zero
    (coalitions : ℕ → Finset iota) (hfirst : (coalitions 0).Nonempty)
    (fuel : ℕ) :
    quittingJointSurvivalWeight
        (quittingNaiveStaticCoalitionRoots coalitions) 0 (fuel + 1) = 0 := by
  rw [quittingJointSurvivalWeight_eq_prod]
  apply Finset.prod_eq_zero (by simp : 0 ∈ Finset.range (fuel + 1))
  rw [show 0 + 0 = 0 by omega]
  exact stationaryContinueMass_pureSetRoot_of_nonempty hfirst

/-- Prepending a nonempty pure coalition root pays exactly that coalition's
reward, independently of the actual continuation profile. -/
theorem quittingTerminalPayoff_pureSetRootThenContinuation_eq_setReward
    (S : Finset iota) (hS : S.Nonempty)
    (continuation : (quittingGame reward).BehaviorProfile) (who : iota) :
    quittingTerminalPayoff reward
        (quittingRootThenContinuationProfile reward
          (quittingPureSetRoot S) continuation) who =
      quittingSetReward reward S who := by
  rw [quittingTerminalPayoff_rootThenContinuation_eq,
    quittingRootExpectedPayoff_eq_absorbingContribution_add,
    quittingRootAbsorbingContribution_pureSetRoot,
    stationaryContinueMass_pureSetRoot_of_nonempty hS]
  ring

/-- Pure Quit at a pure-set root is the static join endpoint, for every
declared continuation payoff. -/
theorem quittingRootQuitPayoff_pureSetRoot_eq_insert
    (tail : Payoff iota) (S : Finset iota) (who : iota) :
    quittingRootQuitPayoff reward tail (quittingPureSetRoot S) who =
      quittingSetReward reward (insert who S) who := by
  rw [quittingRootQuitPayoff,
    quittingRootExpectedPayoff_eq_absorbingContribution_add,
    update_quittingPureSetRoot_true,
    quittingRootAbsorbingContribution_pureSetRoot,
    stationaryContinueMass_pureSetRoot_of_nonempty
      (Finset.insert_nonempty who S)]
  ring

/-- Leaving a coalition that still contains a quitter is exactly the static
leave endpoint; no continuation value is exposed. -/
theorem quittingRootContinuePayoff_pureSetRoot_eq_erase_of_nonempty
    (tail : Payoff iota) (S : Finset iota) (who : iota)
    (herase : (S.erase who).Nonempty) :
    quittingRootContinuePayoff reward tail (quittingPureSetRoot S) who =
      quittingSetReward reward (S.erase who) who := by
  rw [quittingRootContinuePayoff,
    quittingRootExpectedPayoff_eq_absorbingContribution_add,
    update_quittingPureSetRoot_false,
    quittingRootAbsorbingContribution_pureSetRoot,
    stationaryContinueMass_pureSetRoot_of_nonempty herase]
  ring

/-- At a singleton vertex, leaving does not pay the static empty-coalition
value: it exposes the declared continuation coordinate exactly. -/
theorem quittingRootContinuePayoff_pureSingleton_eq_tail
    (tail : Payoff iota) (owner : iota) :
    quittingRootContinuePayoff reward tail
        (quittingPureSetRoot ({owner} : Finset iota)) owner = tail owner := by
  rw [quittingRootContinuePayoff,
    quittingRootExpectedPayoff_eq_absorbingContribution_add,
    update_quittingPureSetRoot_false]
  rw [show ({owner} : Finset iota).erase owner = ∅ by simp]
  rw [quittingRootAbsorbingContribution_pureSetRoot,
    quittingStationaryContinueMass_pureSetRoot_empty,
    quittingSetReward_empty]
  ring

/-- Exact source-matching boundary at a singleton: the static leave value and
the executable Continue endpoint agree iff the actual tail coordinate is
zero. -/
theorem pureSingleton_continue_eq_staticLeave_iff
    (tail : Payoff iota) (owner : iota) :
    quittingRootContinuePayoff reward tail
        (quittingPureSetRoot ({owner} : Finset iota)) owner =
        quittingSetReward reward (({owner} : Finset iota).erase owner) owner ↔
      tail owner = 0 := by
  rw [quittingRootContinuePayoff_pureSingleton_eq_tail]
  simp

/-- **Behavioral falsifier for the naive compiler.**  If the static cycle
uses a profitable singleton-to-empty leave edge, prepending that singleton
root to the actual all-Continue continuation is not even an exact terminal
Nash equilibrium: the owner can Continue at date zero and follow the same
all-Continue tail, improving from the negative solo payoff to zero. -/
theorem not_isZeroAsymptoticNash_pureSingletonThenAlwaysContinue_of_solo_neg
    (owner : iota) (hsolo : quittingSoloReward reward owner owner < 0) :
    ¬(quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) 0
      (quittingRootThenContinuationProfile reward
        (quittingPureSetRoot ({owner} : Finset iota))
        (quittingAlwaysContinueProfile reward)) := by
  intro hnash
  let profile := quittingRootThenContinuationProfile reward
    (quittingPureSetRoot ({owner} : Finset iota))
    (quittingAlwaysContinueProfile reward)
  let deviation := quittingRootAndContinuationDeviation reward
    (PMF.pure false) (quittingAlwaysContinueStrategy reward owner)
  have hdev := hnash owner deviation
  have hon : quittingTerminalPayoff reward profile owner =
      quittingSoloReward reward owner owner := by
    dsimp only [profile]
    rw [quittingTerminalPayoff_pureSetRootThenContinuation_eq_setReward
      ({owner} : Finset iota) (Finset.singleton_nonempty owner)]
    exact quittingSetReward_singleton_eq_soloReward reward owner owner
  have hoff : quittingTerminalPayoff reward
      (Function.update profile owner deviation) owner = 0 := by
    dsimp only [profile, deviation]
    rw [quittingTerminalPayoff_update_rootAndContinuationDeviation_eq]
    rw [update_quittingPureSetRoot_false,
      show ({owner} : Finset iota).erase owner = ∅ by simp]
    rw [quittingRootExpectedPayoff_eq_absorbingContribution_add,
      quittingRootAbsorbingContribution_pureSetRoot,
      quittingStationaryContinueMass_pureSetRoot_empty,
      quittingSetReward_empty]
    have hupdate :
        Function.update (quittingAlwaysContinueProfile reward) owner
            (quittingAlwaysContinueStrategy reward owner) =
          quittingAlwaysContinueProfile reward := by
      funext player time history
      by_cases hplayer : player = owner
      · subst player
        simp [quittingAlwaysContinueStrategy,
          quittingAlwaysContinueProfile,
          StochasticGame.stationaryBehaviorProfile]
      · simp [Function.update_of_ne hplayer]
    rw [hupdate, quittingTerminalPayoff_quittingAlwaysContinue]
    simp
  rw [hon, hoff] at hdev
  linarith

end GameTheory
