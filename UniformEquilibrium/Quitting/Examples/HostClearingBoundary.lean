/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import UniformEquilibrium.Quitting.Paths.SureExitSet
import UniformEquilibrium.Quitting.Root.LiteralRootStackSurvival
import UniformEquilibrium.Quitting.Classification.InstantPunishmentEquivalence
import UniformEquilibrium.Quitting.Root.OpponentCoalitionMass

/-! # A cleared host does not control an outsider's marked deviation

The original clock root and the cleared marked root belong to different
profiles. The marked profile has an actual diagonal all-Continue tail, but
an outsider can join the marked quitter and gain one.
-/

noncomputable section

namespace GameTheory.HostClearingBoundary

open QuittingSureSetOwnerRepair Math.Probability

def reward (coalition : {S : Finset (Fin 4) // S.Nonempty}) : Payoff (Fin 4) :=
  fun who ↦ if who = 1 ∧ coalition.val = {1, 2} then 1 else 0

def originalRoot : Fin 4 → PMF Bool := quittingPureSetRoot {0}

def markedRoot : Fin 4 → PMF Bool := quittingPureSetRoot {2}

def tail : (quittingGame reward).BehaviorProfile :=
  quittingStationaryProfile reward (quittingPureSetRoot ∅)

def marked : (quittingGame reward).BehaviorProfile :=
  quittingRootThenContinuationProfile reward markedRoot tail

def original : (quittingGame reward).BehaviorProfile :=
  quittingRootThenContinuationProfile reward originalRoot tail

theorem original_live_root : quittingProfileLiveRoot reward original 0 = originalRoot := by
  exact quittingProfileLiveRoot_rootThenContinuation_zero reward originalRoot tail

theorem marked_live_root : quittingProfileLiveRoot reward marked 0 = markedRoot := by
  exact quittingProfileLiveRoot_rootThenContinuation_zero reward markedRoot tail

theorem host_endpoint_preserves_nonhost_behavior (who : Fin 4) (hne : who ≠ 0) :
    (Function.update marked 0 (quittingAlwaysContinueStrategy reward 0)) who = marked who := by
  exact Function.update_of_ne hne _ _

theorem tail_diagonal : quittingTerminalSemanticPair reward tail = (0, 0) := by
  apply Prod.ext
  · funext who
    exact quittingTerminalPayoff_pureSetRoot reward ∅ who
  · funext who
    rw [show (quittingTerminalSemanticPair reward tail).2 who =
      quittingContinuationBestResponseValue reward tail who from rfl]
    rw [tail, quittingContinuationBestResponseValue_pureSetRoot_eq]
    have hset : ({who} : Finset (Fin 4)) ≠ {1, 2} := by
      intro heq
      have hcard := congrArg Finset.card heq
      have : ({1, 2} : Finset (Fin 4)).card = 2 := by decide
      simp only [Finset.card_singleton, this] at hcard
      contradiction
    simp [quittingSetReward, reward, hset]

theorem original_joint_zero : quittingStationaryContinueMass originalRoot = 0 := by
  exact stationaryContinueMass_pureSetRoot_of_nonempty (by simp)

theorem original_deleted_clocks (who : Fin 4) :
    quittingRootOpponentContinueMass originalRoot who = if who = 0 then 1 else 0 := by
  fin_cases who <;>
    norm_num [quittingRootOpponentContinueMass, quittingStationaryContinueMass,
      originalRoot, quittingPureSetRoot,
      quittingAllContinueAction, quittingSetAction, Fin.prod_univ_succ]

theorem marked_payoff : quittingTerminalPayoff reward marked = 0 := by
  funext who
  rw [marked, markedRoot,
    quittingTerminalPayoff_pureSetRootThenContinuation_eq_setReward {2} (by simp)]
  simp [quittingSetReward, reward, show ({2} : Finset (Fin 4)) ≠ {1, 2} by decide]

theorem marked_coalition_mass_one : quittingRootCoalitionMass markedRoot {2} = 1 := by
  unfold quittingRootCoalitionMass quittingRootQuitRates
    Math.PMFProduct.coalitionMass markedRoot quittingPureSetRoot quittingSetAction
  rw [show ({2} : Finset (Fin 4))ᶜ = {0, 1, 3} by decide]
  norm_num
  exact Finset.prod_eq_one fun who hwho ↦ by
    have hne : who ≠ (2 : Fin 4) := by
      intro heq
      subst who
      exact (by decide : (2 : Fin 4) ∉ ({0, 1, 3} : Finset (Fin 4))) hwho
    simp [hne]

/-- Clearing the host of the marked root changes no marginal, in particular
none of the nonhost behavior at that row. -/
theorem marked_host_already_clear : Function.update markedRoot 0 (PMF.pure false) =
    markedRoot := by
  apply Function.update_eq_self_iff.mpr
  simp [markedRoot, quittingPureSetRoot, quittingSetAction]

theorem marked_host_cap : quittingContinuationBestResponseValue reward marked 0 = 0 := by
  rw [marked, quittingContinuationBestResponseValue_rootThenContinuation_eq_max]
  have htail := congrArg (fun pair : QuittingTerminalSemanticPair (Fin 4) ↦ pair.2 0)
    tail_diagonal
  change quittingContinuationBestResponseValue reward tail 0 = 0 at htail
  rw [htail]
  rw [markedRoot, quittingRootQuitPayoff_pureSetRoot_eq_insert,
    quittingRootContinuePayoff_pureSetRoot_eq_erase_of_nonempty _ _ _ (by simp)]
  norm_num [quittingSetReward, reward]

theorem marked_outsider_quit_gain :
    quittingTerminalPayoff reward (Function.update marked 1
      (quittingPureTimeBehaviorStrategy reward 1 (some 0))) 1 -
      quittingTerminalPayoff reward marked 1 = 1 := by
  rw [quittingTerminalPayoff_update_quitNow_eq_fixedOpponentsQuitValue,
    marked_payoff]
  rw [marked, quittingProfileLiveRoot_rootThenContinuation_zero,
    markedRoot, quittingStationaryFixedOpponentsQuitValue_pureSetRoot]
  norm_num [quittingSetReward, reward]

theorem marked_host_debt_zero : quittingTerminalDeviationDebt reward marked 0 = 0 := by
  rw [quittingTerminalDeviationDebt, marked_host_cap, marked_payoff]
  simp

end GameTheory.HostClearingBoundary
