/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Paths.NonSoloMass
import UniformEquilibrium.Quitting.Root.SuccessorCertificate

/-!
# Pure-Quit endpoint error from opponent absorption

Forcing one player to Quit differs from that player quitting alone only when
an opponent also Quits.  The resulting endpoint error is bounded by twice the
reward bound times the opponent-absorption probability.  This is a one-stage
semantic estimate; no Nash, Bellman-spine, or path-limit hypothesis is used.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.ProbabilityMassFunction Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A supported joint action under a pure-Quit marginal has the displayed
player quitting. -/
theorem action_eq_true_of_mem_support_pmfPi_update_pure_true
    (root : ι → PMF Bool) (who : ι) (action : ι → Bool)
    (haction : action ∈
      (pmfPi (Function.update root who (PMF.pure true))).support) :
    action who = true := by
  have hcoordinate : action who ∈
      (pushforward
        (pmfPi (Function.update root who (PMF.pure true)))
        (fun joint => joint who)).support := by
    rw [pushforward, PMF.mem_support_map_iff]
    exact ⟨action, haction, rfl⟩
  rw [pmfPi_push_coord] at hcoordinate
  simpa using hcoordinate

/-- The pure-Quit endpoint differs from quitting alone only when an opponent
also quits.  Its error is at most twice the payoff bound times that event's
probability. -/
theorem abs_quittingRootQuitPayoff_sub_singletonReward_le_two_mul_opponentAbsorptionMass
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) (who : ι) (M : ℝ)
    (hreward : ∀ S player, |reward S player| ≤ M) :
    |quittingRootQuitPayoff reward tail root who -
        reward (quittingSingletonTerminal who) who| ≤
      2 * M * quittingRootOpponentAbsorptionMass root who := by
  classical
  let distribution := pmfPi (Function.update root who (PMF.pure true))
  let singletonReward := reward (quittingSingletonTerminal who) who
  let difference : (ι → Bool) → ℝ := fun action =>
    if quittingSomeOpponentQuits who action then
      quittingRootPayoff reward tail action who - singletonReward
    else 0
  have hdifferenceBound : ∀ action,
      |difference action| ≤
        2 * M * quittingSomeOpponentQuitsIndicator who action := by
    intro action
    by_cases hopponent : quittingSomeOpponentQuits who action
    · have hopponentFull := hopponent
      obtain ⟨other, _hne, hother⟩ := hopponent
      have hquit : (quittingQuitters action).Nonempty :=
        (quittingQuitters_nonempty_iff action).2 ⟨other, hother⟩
      have hrewardAction := hreward ⟨quittingQuitters action, hquit⟩ who
      have hrewardSingleton :=
        hreward (quittingSingletonTerminal who) who
      have hflag :=
        (quittingOpponentQuitFlag_eq_true_iff who action).2 hopponentFull
      simp only [difference, if_pos hopponentFull, quittingRootPayoff,
        dif_pos hquit, singletonReward,
        quittingSomeOpponentQuitsIndicator, hflag, if_true, mul_one]
      calc
        |reward ⟨quittingQuitters action, hquit⟩ who -
            reward (quittingSingletonTerminal who) who| ≤ M + M :=
          (abs_sub _ _).trans
            (add_le_add hrewardAction hrewardSingleton)
        _ = 2 * M := by ring
    · have hflag : quittingOpponentQuitFlag who action ≠ true :=
        fun h => hopponent
          ((quittingOpponentQuitFlag_eq_true_iff who action).1 h)
      simp [difference, hopponent, quittingSomeOpponentQuitsIndicator, hflag]
  have hcongr :
      expect distribution (fun action =>
          quittingRootPayoff reward tail action who - singletonReward) =
        expect distribution difference := by
    apply expect_congr_on_support
    intro action haction
    have hself :=
      action_eq_true_of_mem_support_pmfPi_update_pure_true
        root who action haction
    by_cases hopponent : quittingSomeOpponentQuits who action
    · simp [difference, hopponent]
    · have hsingleton :=
        quittingQuitters_eq_singleton_of_noOpponent_of_self
          who action hopponent hself
      simp [difference, hopponent, quittingRootPayoff,
        hsingleton, singletonReward, quittingSingletonTerminal]
  have hindicator :
      expect distribution (quittingSomeOpponentQuitsIndicator who) =
        quittingRootOpponentAbsorptionMass root who := by
    dsimp only [distribution]
    rw [expect_pmfPi_someOpponentQuits_eq_one_sub_continueMass]
    rfl
  have hupper : expect distribution difference ≤
      2 * M * quittingRootOpponentAbsorptionMass root who := by
    calc
      expect distribution difference ≤
          expect distribution (fun action =>
            2 * M * quittingSomeOpponentQuitsIndicator who action) :=
        expect_mono distribution difference _ fun action =>
          (le_abs_self _).trans (hdifferenceBound action)
      _ = _ := by rw [expect_const_mul, hindicator]
  have hlower : -(2 * M * quittingRootOpponentAbsorptionMass root who) ≤
      expect distribution difference := by
    calc
      -(2 * M * quittingRootOpponentAbsorptionMass root who) =
          expect distribution (fun action =>
            (-(2 * M)) *
              quittingSomeOpponentQuitsIndicator who action) := by
        rw [expect_const_mul, hindicator]
        ring
      _ ≤ expect distribution difference := by
        apply expect_mono
        intro action
        have h := neg_le_of_abs_le (hdifferenceBound action)
        simpa only [neg_mul] using h
  have hexpect :
      quittingRootQuitPayoff reward tail root who - singletonReward =
        expect distribution difference := by
    unfold quittingRootQuitPayoff quittingRootExpectedPayoff
    change expect distribution (fun action =>
      quittingRootPayoff reward tail action who) - singletonReward = _
    rw [← expect_const distribution singletonReward, ← expect_sub]
    exact hcongr
  rw [show reward (quittingSingletonTerminal who) who =
      singletonReward by rfl, hexpect]
  exact abs_le.mpr ⟨hlower, hupper⟩

end GameTheory
