/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Punishment.OwnerSoloCertification
import UniformEquilibrium.Quitting.Terminal.TargetTail.TerminalTargetSemantics
import UniformEquilibrium.Examples.BigMatch.Basic

/-!
# Two-player pair repair after a failed owner-solo boundary

For two players, the first escalation beyond an owner-solo stationary root is
already sufficient under the two inequalities supplied by terminal debt and
the universal owner-solo obstruction.

Player two quits surely.  Player one quits with a small positive hazard `p`.
If player one weakly prefers player two's solo exit to joining it, and player
two weakly prefers its own solo exit to waiting for player one's solo exit,
then the stationary profile is a terminal approximate equilibrium.  Its
error and its distance from player two's solo payoff are linear in `p`, so
that solo payoff is a uniform-equilibrium payoff.

This theorem is genuinely two-player.  With a simultaneous terminal set of
three or more players, making the whole set quit surely creates additional
leaver deviations inside that set; the two inequalities below do not control
those deviations.
-/

noncomputable section

namespace GameTheory

open StochasticGame Math.Probability Math.PMFProduct

namespace QuittingTwoPlayerPairRepair

/-! Player one is `false`; the blocker/player two is `true`. -/

/-- Explicit quitter set for a two-coordinate Boolean action. -/
@[simp] theorem quittingQuitters_boolAction (first second : Bool) :
    quittingQuitters (fun who : Bool ↦ if who then second else first) =
      (if first = true then {false} else ∅) ∪
        (if second = true then {true} else ∅) := by
  ext who
  cases who <;> cases first <;> cases second <;>
    simp [quittingQuitters]

/-- Player two quits surely, while player one quits with hazard `p`. -/
def pairRoot (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    Bool → PMF Bool :=
  fun who => if who then PMF.pure true else quittingHazardCoin p hp0 hp1

@[simp] theorem pairRoot_false_true
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ((pairRoot p hp0 hp1 false) true).toReal = p := by
  simp [pairRoot]

@[simp] theorem pairRoot_false_false
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ((pairRoot p hp0 hp1 false) false).toReal = 1 - p := by
  simp [pairRoot]

@[simp] theorem pairRoot_true_true
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ((pairRoot p hp0 hp1 true) true).toReal = 1 := by
  simp [pairRoot]

@[simp] theorem pairRoot_true_false
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ((pairRoot p hp0 hp1 true) false).toReal = 0 := by
  simp [pairRoot]

@[simp] theorem expect_quittingHazardCoin
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (f : Bool → ℝ) :
    expect (quittingHazardCoin p hp0 hp1) f =
      (1 - p) * f false + p * f true := by
  rw [expect_eq_sum, Fintype.sum_bool]
  simp
  ring

/-! ## Endpoint and prescribed-payoff formulas -/

theorem owner_quitPayoff
    (reward : {S : Finset Bool // S.Nonempty} → Payoff Bool)
    (tail : Payoff Bool) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    quittingRootQuitPayoff reward tail (pairRoot p hp0 hp1) false =
      quittingSingletonCollisionReward reward true false := by
  unfold quittingRootQuitPayoff quittingRootExpectedPayoff
  rw [StochasticGame.BigMatch.expect_pmfPi_bool]
  simp [pairRoot, quittingRootPayoff, quittingSingletonCollisionReward,
    quittingQuitters_boolAction]

theorem owner_continuePayoff
    (reward : {S : Finset Bool // S.Nonempty} → Payoff Bool)
    (tail : Payoff Bool) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    quittingRootContinuePayoff reward tail (pairRoot p hp0 hp1) false =
      quittingSoloReward reward true false := by
  unfold quittingRootContinuePayoff quittingRootExpectedPayoff
  rw [StochasticGame.BigMatch.expect_pmfPi_bool]
  simp [pairRoot, quittingRootPayoff, quittingSoloReward,
    quittingQuitters_boolAction]

theorem blocker_quitPayoff
    (reward : {S : Finset Bool // S.Nonempty} → Payoff Bool)
    (tail : Payoff Bool) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    quittingRootQuitPayoff reward tail (pairRoot p hp0 hp1) true =
      (1 - p) * quittingSoloReward reward true true +
        p * quittingSingletonCollisionReward reward false true := by
  have hpair : ({true, false} : Finset Bool) = {false, true} := by
    ext who
    cases who <;> simp
  unfold quittingRootQuitPayoff quittingRootExpectedPayoff
  rw [StochasticGame.BigMatch.expect_pmfPi_bool]
  simp [pairRoot, quittingRootPayoff, quittingSoloReward,
    quittingSingletonCollisionReward, quittingQuitters_boolAction, hpair]

theorem blocker_continuePayoff
    (reward : {S : Finset Bool // S.Nonempty} → Payoff Bool)
    (tail : Payoff Bool) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    quittingRootContinuePayoff reward tail (pairRoot p hp0 hp1) true =
      p * quittingSoloReward reward false true + (1 - p) * tail true := by
  unfold quittingRootContinuePayoff quittingRootExpectedPayoff
  rw [StochasticGame.BigMatch.expect_pmfPi_bool]
  simp [pairRoot, quittingRootPayoff, quittingSoloReward,
    quittingQuitters_boolAction]
  ring

theorem stationaryContinueMass_pairRoot
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    quittingStationaryContinueMass (pairRoot p hp0 hp1) = 0 := by
  unfold quittingStationaryContinueMass
  rw [pmfPi_apply]
  simp [quittingAllContinueAction, pairRoot]

/-- The sure-blocker profile absorbs at its first stage. -/
theorem terminalPayoff_pairRoot
    (reward : {S : Finset Bool // S.Nonempty} → Payoff Bool)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (who : Bool) :
    quittingTerminalPayoff reward
        (quittingStationaryProfile reward (pairRoot p hp0 hp1)) who =
      if who then
        (1 - p) * quittingSoloReward reward true true +
          p * quittingSingletonCollisionReward reward false true
      else
        (1 - p) * quittingSoloReward reward true false +
          p * quittingSingletonCollisionReward reward true false := by
  rw [quittingTerminalPayoff_stationary_eq_absorbingContribution_div
    reward (pairRoot p hp0 hp1) who (by
      rw [stationaryContinueMass_pairRoot]
      norm_num),
    stationaryContinueMass_pairRoot]
  simp only [sub_zero, div_one]
  change quittingRootSuccessorPayoff reward (0 : Payoff Bool)
    (pairRoot p hp0 hp1) who = _
  rw [quittingRootSuccessorPayoff_eq_endpointMix]
  cases who
  · rw [owner_quitPayoff, owner_continuePayoff]
    simp only [pairRoot_false_true, pairRoot_false_false,
      Bool.false_eq_true, ↓reduceIte]
    ring
  · rw [blocker_quitPayoff, blocker_continuePayoff]
    simp only [pairRoot_true_true, pairRoot_true_false, one_mul, zero_mul,
      add_zero, if_true]

/-! ## Complete unilateral caps -/

theorem fixedOpponentsContinueMass_pairRoot_owner
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    quittingStationaryFixedOpponentsContinueMass
        (pairRoot p hp0 hp1) false = 0 := by
  unfold quittingStationaryFixedOpponentsContinueMass
    quittingFixedOpponentsContinueMass quittingStationaryContinueMass
  rw [pmfPi_apply]
  simp [quittingAllContinueAction, pairRoot]

theorem fixedOpponentsContinueMass_pairRoot_blocker
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    quittingStationaryFixedOpponentsContinueMass
        (pairRoot p hp0 hp1) true = 1 - p := by
  unfold quittingStationaryFixedOpponentsContinueMass
    quittingFixedOpponentsContinueMass quittingStationaryContinueMass
  rw [pmfPi_apply]
  simp [quittingAllContinueAction, pairRoot]

theorem fixedOpponentsQuitValue_pairRoot_owner
    (reward : {S : Finset Bool // S.Nonempty} → Payoff Bool)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    quittingStationaryFixedOpponentsQuitValue reward
        (pairRoot p hp0 hp1) false =
      quittingSingletonCollisionReward reward true false := by
  simpa [quittingStationaryFixedOpponentsQuitValue,
    quittingFixedOpponentsQuitValue, quittingRootQuitPayoff,
    quittingRootAbsorbingContribution] using
      owner_quitPayoff reward (0 : Payoff Bool) p hp0 hp1

theorem fixedOpponentsContinueReward_pairRoot_owner
    (reward : {S : Finset Bool // S.Nonempty} → Payoff Bool)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    quittingStationaryFixedOpponentsContinueReward reward
        (pairRoot p hp0 hp1) false =
      quittingSoloReward reward true false := by
  simpa [quittingStationaryFixedOpponentsContinueReward,
    quittingFixedOpponentsContinueReward, quittingRootContinuePayoff,
    quittingRootAbsorbingContribution] using
      owner_continuePayoff reward (0 : Payoff Bool) p hp0 hp1

theorem fixedOpponentsQuitValue_pairRoot_blocker
    (reward : {S : Finset Bool // S.Nonempty} → Payoff Bool)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    quittingStationaryFixedOpponentsQuitValue reward
        (pairRoot p hp0 hp1) true =
      (1 - p) * quittingSoloReward reward true true +
        p * quittingSingletonCollisionReward reward false true := by
  simpa [quittingStationaryFixedOpponentsQuitValue,
    quittingFixedOpponentsQuitValue, quittingRootQuitPayoff,
    quittingRootAbsorbingContribution] using
      blocker_quitPayoff reward (0 : Payoff Bool) p hp0 hp1

theorem fixedOpponentsContinueReward_pairRoot_blocker
    (reward : {S : Finset Bool // S.Nonempty} → Payoff Bool)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    quittingStationaryFixedOpponentsContinueReward reward
        (pairRoot p hp0 hp1) true =
      p * quittingSoloReward reward false true := by
  simpa [quittingStationaryFixedOpponentsContinueReward,
    quittingFixedOpponentsContinueReward, quittingRootContinuePayoff,
    quittingRootAbsorbingContribution] using
      blocker_continuePayoff reward (0 : Payoff Bool) p hp0 hp1

/-- The sure blocker's selected unilateral cap is its immediate-Quit value
or the payoff from waiting for player one's solo exit. -/
theorem unilateralCap_pairRoot_blocker
    (reward : {S : Finset Bool // S.Nonempty} → Payoff Bool)
    (p : ℝ) (hp1 : p ≤ 1) (hp : 0 < p) :
    quittingStationaryUnilateralCap reward (pairRoot p hp.le hp1) true =
      max
        ((1 - p) * quittingSoloReward reward true true +
          p * quittingSingletonCollisionReward reward false true)
        (quittingSoloReward reward false true) := by
  unfold quittingStationaryUnilateralCap quittingStationarySelectedCap
    quittingStationaryNeverValue
  rw [fixedOpponentsQuitValue_pairRoot_blocker,
    fixedOpponentsContinueReward_pairRoot_blocker,
    fixedOpponentsContinueMass_pairRoot_blocker]
  have hpne : p ≠ 0 := ne_of_gt hp
  congr 1
  field_simp [hpne]
  ring

/-- Under the owner's joining-loss inequality, its selected cap is the
blocker's solo payoff. -/
theorem unilateralCap_pairRoot_owner
    (reward : {S : Finset Bool // S.Nonempty} → Payoff Bool)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (howner : quittingSingletonCollisionReward reward true false ≤
      quittingSoloReward reward true false) :
    quittingStationaryUnilateralCap reward (pairRoot p hp0 hp1) false =
      quittingSoloReward reward true false := by
  unfold quittingStationaryUnilateralCap quittingStationarySelectedCap
    quittingStationaryNeverValue
  rw [fixedOpponentsQuitValue_pairRoot_owner,
    fixedOpponentsContinueReward_pairRoot_owner,
    fixedOpponentsContinueMass_pairRoot_owner]
  simp [max_eq_right howner]

/-! ## Pair repair -/

/-- A convenient common error for the two players. -/
def pairRepairError
    (reward : {S : Finset Bool // S.Nonempty} → Payoff Bool)
    (p : ℝ) : ℝ :=
  p * ((quittingSoloReward reward true false -
          quittingSingletonCollisionReward reward true false) +
        |quittingSingletonCollisionReward reward false true -
          quittingSoloReward reward true true|)

theorem pairRepairError_nonneg
    (reward : {S : Finset Bool // S.Nonempty} → Payoff Bool)
    (p : ℝ) (hp0 : 0 ≤ p)
    (howner : quittingSingletonCollisionReward reward true false ≤
      quittingSoloReward reward true false) :
    0 ≤ pairRepairError reward p := by
  unfold pairRepairError
  positivity

/-- The pair-repair profile's terminal payoff is coordinatewise within its
strategic error of the sure blocker's solo payoff vector. -/
theorem abs_terminalPayoff_pairRoot_sub_soloReward_le_pairRepairError
    (reward : {S : Finset Bool // S.Nonempty} → Payoff Bool)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (howner : quittingSingletonCollisionReward reward true false ≤
      quittingSoloReward reward true false)
    (who : Bool) :
    |quittingTerminalPayoff reward
          (quittingStationaryProfile reward (pairRoot p hp0 hp1)) who -
        quittingSoloReward reward true who| ≤
      pairRepairError reward p := by
  rw [terminalPayoff_pairRoot]
  cases who
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [show
      (1 - p) * quittingSoloReward reward true false +
            p * quittingSingletonCollisionReward reward true false -
          quittingSoloReward reward true false =
        p * (quittingSingletonCollisionReward reward true false -
          quittingSoloReward reward true false) by ring,
      abs_mul, abs_of_nonneg hp0,
      abs_of_nonpos (sub_nonpos.mpr howner)]
    have habs := abs_nonneg
      (quittingSingletonCollisionReward reward false true -
        quittingSoloReward reward true true)
    unfold pairRepairError
    nlinarith [mul_nonneg hp0 habs]
  · simp only [if_true]
    rw [show
      (1 - p) * quittingSoloReward reward true true +
            p * quittingSingletonCollisionReward reward false true -
          quittingSoloReward reward true true =
        p * (quittingSingletonCollisionReward reward false true -
          quittingSoloReward reward true true) by ring,
      abs_mul, abs_of_nonneg hp0]
    unfold pairRepairError
    nlinarith [mul_nonneg hp0 (sub_nonneg.mpr howner)]

/-- **Two-player pair repair.**  The sure-blocker/vanishing-owner root caps
every behavioral unilateral deviation with error linear in `p`. -/
theorem isεAsymptoticNash_pairRoot
    (reward : {S : Finset Bool // S.Nonempty} → Payoff Bool)
    (p : ℝ) (hp1 : p ≤ 1) (hp : 0 < p)
    (howner : quittingSingletonCollisionReward reward true false ≤
      quittingSoloReward reward true false)
    (hblocker : quittingSoloReward reward false true ≤
      quittingSoloReward reward true true) :
    (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) (pairRepairError reward p)
      (quittingStationaryProfile reward (pairRoot p hp.le hp1)) := by
  apply isεAsymptoticNash_stationary_of_unilateralCap_le
  · intro who
    cases who
    · rw [fixedOpponentsContinueMass_pairRoot_owner]
      norm_num
    · rw [fixedOpponentsContinueMass_pairRoot_blocker]
      linarith
  · intro who
    cases who
    · rw [unilateralCap_pairRoot_owner reward p hp.le hp1 howner,
        terminalPayoff_pairRoot]
      simp only [Bool.false_eq_true, ↓reduceIte]
      have habs := abs_nonneg
        (quittingSingletonCollisionReward reward false true -
          quittingSoloReward reward true true)
      unfold pairRepairError
      nlinarith [mul_nonneg hp.le habs]
    · rw [unilateralCap_pairRoot_blocker reward p hp1 hp,
        terminalPayoff_pairRoot]
      simp only [if_true]
      apply max_le
      · exact le_add_of_nonneg_right
          (pairRepairError_nonneg reward p hp.le howner)
      · have habsLower := neg_abs_le
          (quittingSingletonCollisionReward reward false true -
            quittingSoloReward reward true true)
        unfold pairRepairError
        nlinarith [mul_nonneg hp.le
          (sub_nonneg.mpr howner)]

/-- The pair-repair hypotheses give terminal approximate equilibria at every
positive accuracy whose payoffs approach the sure blocker's solo payoff. -/
theorem exists_terminalNash_approxTarget_all_errors_of_pairRepair
    (reward : {S : Finset Bool // S.Nonempty} → Payoff Bool)
    (howner : quittingSingletonCollisionReward reward true false ≤
      quittingSoloReward reward true false)
    (hblocker : quittingSoloReward reward false true ≤
      quittingSoloReward reward true true) :
    ∀ ε : ℝ, 0 < ε →
      ∃ profile : (quittingGame reward).BehaviorProfile,
        (quittingGame reward).IsεAsymptoticNash
            (quittingTerminalPayoff reward) ε profile ∧
          ∀ who,
            |quittingTerminalPayoff reward profile who -
              quittingSoloReward reward true who| ≤ ε := by
  intro ε hε
  let scale :=
    (quittingSoloReward reward true false -
        quittingSingletonCollisionReward reward true false) +
      |quittingSingletonCollisionReward reward false true -
        quittingSoloReward reward true true|
  have hscale0 : 0 ≤ scale := by
    dsimp only [scale]
    positivity
  let p := ε / (scale + ε)
  have hden : 0 < scale + ε := by linarith
  have hp : 0 < p := div_pos hε hden
  have hp1 : p ≤ 1 := (div_le_one hden).2 (by linarith)
  have herror : pairRepairError reward p < ε := by
    change p * scale < ε
    rw [show p = ε / (scale + ε) by rfl]
    rw [div_mul_eq_mul_div, div_lt_iff₀ hden]
    nlinarith
  refine ⟨quittingStationaryProfile reward
      (pairRoot p hp.le hp1),
    (isεAsymptoticNash_pairRoot reward p hp1 hp
      howner hblocker).mono herror.le, ?_⟩
  intro who
  exact (abs_terminalPayoff_pairRoot_sub_soloReward_le_pairRepairError
    reward p hp.le hp1 howner who).trans herror.le

/-- The pair-repair hypotheses give terminal approximate equilibria at every
positive accuracy. -/
theorem exists_terminalNash_all_errors_of_pairRepair
    (reward : {S : Finset Bool // S.Nonempty} → Payoff Bool)
    (howner : quittingSingletonCollisionReward reward true false ≤
      quittingSoloReward reward true false)
    (hblocker : quittingSoloReward reward false true ≤
      quittingSoloReward reward true true) :
    ∀ ε : ℝ, 0 < ε →
      ∃ profile : (quittingGame reward).BehaviorProfile,
        (quittingGame reward).IsεAsymptoticNash
          (quittingTerminalPayoff reward) ε profile := by
  intro ε hε
  obtain ⟨profile, hnash, _⟩ :=
    exists_terminalNash_approxTarget_all_errors_of_pairRepair
      reward howner hblocker ε hε
  exact ⟨profile, hnash⟩

/-- The fixed payoff delivered by pair repair is the sure blocker's solo
reward vector. -/
theorem quittingGame_isUniformEquilibriumPayoff_of_pairRepair
    (reward : {S : Finset Bool // S.Nonempty} → Payoff Bool)
    (howner : quittingSingletonCollisionReward reward true false ≤
      quittingSoloReward reward true false)
    (hblocker : quittingSoloReward reward false true ≤
      quittingSoloReward reward true true) :
    (quittingGame reward).IsUniformEquilibriumPayoff none
      (quittingSoloReward reward true) := by
  apply quittingGame_isUniformEquilibriumPayoff_of_terminalNash_all_errors_approxTarget
  exact exists_terminalNash_approxTarget_all_errors_of_pairRepair
    reward howner hblocker

/-- Existential compatibility wrapper for the fixed-target pair-repair
theorem. -/
theorem exists_uniformEquilibriumPayoff_of_pairRepair
    (reward : {S : Finset Bool // S.Nonempty} → Payoff Bool)
    (howner : quittingSingletonCollisionReward reward true false ≤
      quittingSoloReward reward true false)
    (hblocker : quittingSoloReward reward false true ≤
      quittingSoloReward reward true true) :
    ∃ payoff : Payoff Bool,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  exact ⟨quittingSoloReward reward true,
    quittingGame_isUniformEquilibriumPayoff_of_pairRepair
      reward howner hblocker⟩

/-! ## Role reversal and the role-parametric statement -/

/-- The role-reversed root: player `false` is the sure blocker and player
`true` is the owner with vanishing hazard. -/
def mirrorPairRoot (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    Bool → PMF Bool :=
  fun who => if who then quittingHazardCoin p hp0 hp1 else PMF.pure true

@[simp] theorem mirrorPairRoot_false_true
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ((mirrorPairRoot p hp0 hp1 false) true).toReal = 1 := by
  simp [mirrorPairRoot]

@[simp] theorem mirrorPairRoot_false_false
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ((mirrorPairRoot p hp0 hp1 false) false).toReal = 0 := by
  simp [mirrorPairRoot]

@[simp] theorem mirrorPairRoot_true_true
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ((mirrorPairRoot p hp0 hp1 true) true).toReal = p := by
  simp [mirrorPairRoot]

@[simp] theorem mirrorPairRoot_true_false
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ((mirrorPairRoot p hp0 hp1 true) false).toReal = 1 - p := by
  simp [mirrorPairRoot]

private theorem mirror_owner_quitPayoff
    (reward : {S : Finset Bool // S.Nonempty} → Payoff Bool)
    (tail : Payoff Bool) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    quittingRootQuitPayoff reward tail (mirrorPairRoot p hp0 hp1) true =
      quittingSingletonCollisionReward reward false true := by
  have hpair : ({true, false} : Finset Bool) = {false, true} := by
    ext who
    cases who <;> simp
  unfold quittingRootQuitPayoff quittingRootExpectedPayoff
  rw [StochasticGame.BigMatch.expect_pmfPi_bool]
  simp [mirrorPairRoot, quittingRootPayoff,
    quittingSingletonCollisionReward, quittingQuitters_boolAction, hpair]

private theorem mirror_owner_continuePayoff
    (reward : {S : Finset Bool // S.Nonempty} → Payoff Bool)
    (tail : Payoff Bool) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    quittingRootContinuePayoff reward tail (mirrorPairRoot p hp0 hp1) true =
      quittingSoloReward reward false true := by
  unfold quittingRootContinuePayoff quittingRootExpectedPayoff
  rw [StochasticGame.BigMatch.expect_pmfPi_bool]
  simp [mirrorPairRoot, quittingRootPayoff, quittingSoloReward,
    quittingQuitters_boolAction]

private theorem mirror_blocker_quitPayoff
    (reward : {S : Finset Bool // S.Nonempty} → Payoff Bool)
    (tail : Payoff Bool) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    quittingRootQuitPayoff reward tail (mirrorPairRoot p hp0 hp1) false =
      (1 - p) * quittingSoloReward reward false false +
        p * quittingSingletonCollisionReward reward true false := by
  unfold quittingRootQuitPayoff quittingRootExpectedPayoff
  rw [StochasticGame.BigMatch.expect_pmfPi_bool]
  simp [mirrorPairRoot, quittingRootPayoff, quittingSoloReward,
    quittingSingletonCollisionReward, quittingQuitters_boolAction]

private theorem mirror_blocker_continuePayoff
    (reward : {S : Finset Bool // S.Nonempty} → Payoff Bool)
    (tail : Payoff Bool) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    quittingRootContinuePayoff reward tail (mirrorPairRoot p hp0 hp1) false =
      p * quittingSoloReward reward true false + (1 - p) * tail false := by
  unfold quittingRootContinuePayoff quittingRootExpectedPayoff
  rw [StochasticGame.BigMatch.expect_pmfPi_bool]
  simp [mirrorPairRoot, quittingRootPayoff, quittingSoloReward,
    quittingQuitters_boolAction]
  ring

private theorem stationaryContinueMass_mirrorPairRoot
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    quittingStationaryContinueMass (mirrorPairRoot p hp0 hp1) = 0 := by
  unfold quittingStationaryContinueMass
  rw [pmfPi_apply]
  simp [quittingAllContinueAction, mirrorPairRoot]

private theorem terminalPayoff_mirrorPairRoot
    (reward : {S : Finset Bool // S.Nonempty} → Payoff Bool)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (who : Bool) :
    quittingTerminalPayoff reward
        (quittingStationaryProfile reward (mirrorPairRoot p hp0 hp1)) who =
      if who then
        (1 - p) * quittingSoloReward reward false true +
          p * quittingSingletonCollisionReward reward false true
      else
        (1 - p) * quittingSoloReward reward false false +
          p * quittingSingletonCollisionReward reward true false := by
  rw [quittingTerminalPayoff_stationary_eq_absorbingContribution_div
    reward (mirrorPairRoot p hp0 hp1) who (by
      rw [stationaryContinueMass_mirrorPairRoot]
      norm_num),
    stationaryContinueMass_mirrorPairRoot]
  simp only [sub_zero, div_one]
  change quittingRootSuccessorPayoff reward (0 : Payoff Bool)
    (mirrorPairRoot p hp0 hp1) who = _
  rw [quittingRootSuccessorPayoff_eq_endpointMix]
  cases who
  · rw [mirror_blocker_quitPayoff, mirror_blocker_continuePayoff]
    simp only [mirrorPairRoot_false_true, mirrorPairRoot_false_false,
      one_mul, zero_mul, add_zero, Bool.false_eq_true, ↓reduceIte]
  · rw [mirror_owner_quitPayoff, mirror_owner_continuePayoff]
    simp only [mirrorPairRoot_true_true, mirrorPairRoot_true_false, if_true]
    ring

private theorem fixedOpponentsContinueMass_mirror_owner
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    quittingStationaryFixedOpponentsContinueMass
        (mirrorPairRoot p hp0 hp1) true = 0 := by
  unfold quittingStationaryFixedOpponentsContinueMass
    quittingFixedOpponentsContinueMass quittingStationaryContinueMass
  rw [pmfPi_apply]
  simp [quittingAllContinueAction, mirrorPairRoot]

private theorem fixedOpponentsContinueMass_mirror_blocker
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    quittingStationaryFixedOpponentsContinueMass
        (mirrorPairRoot p hp0 hp1) false = 1 - p := by
  unfold quittingStationaryFixedOpponentsContinueMass
    quittingFixedOpponentsContinueMass quittingStationaryContinueMass
  rw [pmfPi_apply]
  simp [quittingAllContinueAction, mirrorPairRoot]

private theorem fixedOpponentsQuitValue_mirror_owner
    (reward : {S : Finset Bool // S.Nonempty} → Payoff Bool)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    quittingStationaryFixedOpponentsQuitValue reward
        (mirrorPairRoot p hp0 hp1) true =
      quittingSingletonCollisionReward reward false true := by
  simpa [quittingStationaryFixedOpponentsQuitValue,
    quittingFixedOpponentsQuitValue, quittingRootQuitPayoff,
    quittingRootAbsorbingContribution] using
      mirror_owner_quitPayoff reward (0 : Payoff Bool) p hp0 hp1

private theorem fixedOpponentsContinueReward_mirror_owner
    (reward : {S : Finset Bool // S.Nonempty} → Payoff Bool)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    quittingStationaryFixedOpponentsContinueReward reward
        (mirrorPairRoot p hp0 hp1) true =
      quittingSoloReward reward false true := by
  simpa [quittingStationaryFixedOpponentsContinueReward,
    quittingFixedOpponentsContinueReward, quittingRootContinuePayoff,
    quittingRootAbsorbingContribution] using
      mirror_owner_continuePayoff reward (0 : Payoff Bool) p hp0 hp1

private theorem fixedOpponentsQuitValue_mirror_blocker
    (reward : {S : Finset Bool // S.Nonempty} → Payoff Bool)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    quittingStationaryFixedOpponentsQuitValue reward
        (mirrorPairRoot p hp0 hp1) false =
      (1 - p) * quittingSoloReward reward false false +
        p * quittingSingletonCollisionReward reward true false := by
  simpa [quittingStationaryFixedOpponentsQuitValue,
    quittingFixedOpponentsQuitValue, quittingRootQuitPayoff,
    quittingRootAbsorbingContribution] using
      mirror_blocker_quitPayoff reward (0 : Payoff Bool) p hp0 hp1

private theorem fixedOpponentsContinueReward_mirror_blocker
    (reward : {S : Finset Bool // S.Nonempty} → Payoff Bool)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    quittingStationaryFixedOpponentsContinueReward reward
        (mirrorPairRoot p hp0 hp1) false =
      p * quittingSoloReward reward true false := by
  simpa [quittingStationaryFixedOpponentsContinueReward,
    quittingFixedOpponentsContinueReward, quittingRootContinuePayoff,
    quittingRootAbsorbingContribution] using
      mirror_blocker_continuePayoff reward (0 : Payoff Bool) p hp0 hp1

private theorem unilateralCap_mirror_blocker
    (reward : {S : Finset Bool // S.Nonempty} → Payoff Bool)
    (p : ℝ) (hp1 : p ≤ 1) (hp : 0 < p) :
    quittingStationaryUnilateralCap reward
        (mirrorPairRoot p hp.le hp1) false =
      max
        ((1 - p) * quittingSoloReward reward false false +
          p * quittingSingletonCollisionReward reward true false)
        (quittingSoloReward reward true false) := by
  unfold quittingStationaryUnilateralCap quittingStationarySelectedCap
    quittingStationaryNeverValue
  rw [fixedOpponentsQuitValue_mirror_blocker,
    fixedOpponentsContinueReward_mirror_blocker,
    fixedOpponentsContinueMass_mirror_blocker]
  have hpne : p ≠ 0 := ne_of_gt hp
  congr 1
  field_simp [hpne]
  ring

private theorem unilateralCap_mirror_owner
    (reward : {S : Finset Bool // S.Nonempty} → Payoff Bool)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (howner : quittingSingletonCollisionReward reward false true ≤
      quittingSoloReward reward false true) :
    quittingStationaryUnilateralCap reward
        (mirrorPairRoot p hp0 hp1) true =
      quittingSoloReward reward false true := by
  unfold quittingStationaryUnilateralCap quittingStationarySelectedCap
    quittingStationaryNeverValue
  rw [fixedOpponentsQuitValue_mirror_owner,
    fixedOpponentsContinueReward_mirror_owner,
    fixedOpponentsContinueMass_mirror_owner]
  simp [max_eq_right howner]

/-- A common error for the role-reversed construction. -/
def mirrorPairRepairError
    (reward : {S : Finset Bool // S.Nonempty} → Payoff Bool)
    (p : ℝ) : ℝ :=
  p * ((quittingSoloReward reward false true -
          quittingSingletonCollisionReward reward false true) +
        |quittingSingletonCollisionReward reward true false -
          quittingSoloReward reward false false|)

private theorem mirrorPairRepairError_nonneg
    (reward : {S : Finset Bool // S.Nonempty} → Payoff Bool)
    (p : ℝ) (hp0 : 0 ≤ p)
    (howner : quittingSingletonCollisionReward reward false true ≤
      quittingSoloReward reward false true) :
    0 ≤ mirrorPairRepairError reward p := by
  unfold mirrorPairRepairError
  positivity

/-- The role-reversed pair-repair profile is coordinatewise within its
strategic error of the sure blocker's solo payoff vector. -/
theorem abs_terminalPayoff_mirrorPairRoot_sub_soloReward_le_pairRepairError
    (reward : {S : Finset Bool // S.Nonempty} → Payoff Bool)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (howner : quittingSingletonCollisionReward reward false true ≤
      quittingSoloReward reward false true)
    (who : Bool) :
    |quittingTerminalPayoff reward
          (quittingStationaryProfile reward (mirrorPairRoot p hp0 hp1)) who -
        quittingSoloReward reward false who| ≤
      mirrorPairRepairError reward p := by
  rw [terminalPayoff_mirrorPairRoot]
  cases who
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [show
      (1 - p) * quittingSoloReward reward false false +
            p * quittingSingletonCollisionReward reward true false -
          quittingSoloReward reward false false =
        p * (quittingSingletonCollisionReward reward true false -
          quittingSoloReward reward false false) by ring,
      abs_mul, abs_of_nonneg hp0]
    unfold mirrorPairRepairError
    nlinarith [mul_nonneg hp0 (sub_nonneg.mpr howner)]
  · simp only [if_true]
    rw [show
      (1 - p) * quittingSoloReward reward false true +
            p * quittingSingletonCollisionReward reward false true -
          quittingSoloReward reward false true =
        p * (quittingSingletonCollisionReward reward false true -
          quittingSoloReward reward false true) by ring,
      abs_mul, abs_of_nonneg hp0,
      abs_of_nonpos (sub_nonpos.mpr howner)]
    have habs := abs_nonneg
      (quittingSingletonCollisionReward reward true false -
        quittingSoloReward reward false false)
    unfold mirrorPairRepairError
    nlinarith [mul_nonneg hp0 habs]

private theorem isεAsymptoticNash_mirrorPairRoot
    (reward : {S : Finset Bool // S.Nonempty} → Payoff Bool)
    (p : ℝ) (hp1 : p ≤ 1) (hp : 0 < p)
    (howner : quittingSingletonCollisionReward reward false true ≤
      quittingSoloReward reward false true)
    (hblocker : quittingSoloReward reward true false ≤
      quittingSoloReward reward false false) :
    (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) (mirrorPairRepairError reward p)
      (quittingStationaryProfile reward (mirrorPairRoot p hp.le hp1)) := by
  apply isεAsymptoticNash_stationary_of_unilateralCap_le
  · intro who
    cases who
    · rw [fixedOpponentsContinueMass_mirror_blocker]
      linarith
    · rw [fixedOpponentsContinueMass_mirror_owner]
      norm_num
  · intro who
    cases who
    · rw [unilateralCap_mirror_blocker reward p hp1 hp,
        terminalPayoff_mirrorPairRoot]
      simp only [Bool.false_eq_true, ↓reduceIte]
      apply max_le
      · exact le_add_of_nonneg_right
          (mirrorPairRepairError_nonneg reward p hp.le howner)
      · have habsLower := neg_abs_le
          (quittingSingletonCollisionReward reward true false -
            quittingSoloReward reward false false)
        unfold mirrorPairRepairError
        nlinarith [mul_nonneg hp.le (sub_nonneg.mpr howner)]
    · rw [unilateralCap_mirror_owner reward p hp.le hp1 howner,
        terminalPayoff_mirrorPairRoot]
      simp only [if_true]
      have habs := abs_nonneg
        (quittingSingletonCollisionReward reward true false -
          quittingSoloReward reward false false)
      unfold mirrorPairRepairError
      nlinarith [mul_nonneg hp.le habs]

/-- The role-reversed pair repair gives terminal approximate equilibria whose
payoffs approach the sure blocker's solo payoff. -/
theorem exists_terminalNash_approxTarget_all_errors_of_mirrorPairRepair
    (reward : {S : Finset Bool // S.Nonempty} → Payoff Bool)
    (howner : quittingSingletonCollisionReward reward false true ≤
      quittingSoloReward reward false true)
    (hblocker : quittingSoloReward reward true false ≤
      quittingSoloReward reward false false) :
    ∀ ε : ℝ, 0 < ε →
      ∃ profile : (quittingGame reward).BehaviorProfile,
        (quittingGame reward).IsεAsymptoticNash
            (quittingTerminalPayoff reward) ε profile ∧
          ∀ who,
            |quittingTerminalPayoff reward profile who -
              quittingSoloReward reward false who| ≤ ε := by
  intro ε hε
  let scale :=
    (quittingSoloReward reward false true -
        quittingSingletonCollisionReward reward false true) +
      |quittingSingletonCollisionReward reward true false -
        quittingSoloReward reward false false|
  have hscale0 : 0 ≤ scale := by
    dsimp only [scale]
    positivity
  let p := ε / (scale + ε)
  have hden : 0 < scale + ε := by linarith
  have hp : 0 < p := div_pos hε hden
  have hp1 : p ≤ 1 := (div_le_one hden).2 (by linarith)
  have herror : mirrorPairRepairError reward p < ε := by
    change p * scale < ε
    rw [show p = ε / (scale + ε) by rfl]
    rw [div_mul_eq_mul_div, div_lt_iff₀ hden]
    nlinarith
  refine ⟨quittingStationaryProfile reward
      (mirrorPairRoot p hp.le hp1),
    (isεAsymptoticNash_mirrorPairRoot reward p hp1 hp
      howner hblocker).mono herror.le, ?_⟩
  intro who
  exact
    (abs_terminalPayoff_mirrorPairRoot_sub_soloReward_le_pairRepairError
      reward p hp.le hp1 howner who).trans herror.le

/-- The role-reversed pair repair also gives terminal approximate equilibria
at every positive accuracy. -/
theorem exists_terminalNash_all_errors_of_mirrorPairRepair
    (reward : {S : Finset Bool // S.Nonempty} → Payoff Bool)
    (howner : quittingSingletonCollisionReward reward false true ≤
      quittingSoloReward reward false true)
    (hblocker : quittingSoloReward reward true false ≤
      quittingSoloReward reward false false) :
    ∀ ε : ℝ, 0 < ε →
      ∃ profile : (quittingGame reward).BehaviorProfile,
        (quittingGame reward).IsεAsymptoticNash
          (quittingTerminalPayoff reward) ε profile := by
  intro ε hε
  obtain ⟨profile, hnash, _⟩ :=
    exists_terminalNash_approxTarget_all_errors_of_mirrorPairRepair
      reward howner hblocker ε hε
  exact ⟨profile, hnash⟩

/-- The fixed payoff delivered by role-reversed pair repair is the sure
blocker's solo reward vector. -/
theorem quittingGame_isUniformEquilibriumPayoff_of_mirrorPairRepair
    (reward : {S : Finset Bool // S.Nonempty} → Payoff Bool)
    (howner : quittingSingletonCollisionReward reward false true ≤
      quittingSoloReward reward false true)
    (hblocker : quittingSoloReward reward true false ≤
      quittingSoloReward reward false false) :
    (quittingGame reward).IsUniformEquilibriumPayoff none
      (quittingSoloReward reward false) := by
  apply quittingGame_isUniformEquilibriumPayoff_of_terminalNash_all_errors_approxTarget
  exact exists_terminalNash_approxTarget_all_errors_of_mirrorPairRepair
    reward howner hblocker

/-- Existential compatibility wrapper for the fixed-target role-reversed
pair-repair theorem. -/
theorem exists_uniformEquilibriumPayoff_of_mirrorPairRepair
    (reward : {S : Finset Bool // S.Nonempty} → Payoff Bool)
    (howner : quittingSingletonCollisionReward reward false true ≤
      quittingSoloReward reward false true)
    (hblocker : quittingSoloReward reward true false ≤
      quittingSoloReward reward false false) :
    ∃ payoff : Payoff Bool,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  exact ⟨quittingSoloReward reward false,
    quittingGame_isUniformEquilibriumPayoff_of_mirrorPairRepair
      reward howner hblocker⟩

/-- Role-parametric quantitative pair repair.  At every positive accuracy,
one terminal approximate equilibrium is coordinatewise close to the sure
blocker's solo reward vector. -/
theorem exists_terminalNash_approxTarget_all_errors_of_bool_pairRepair
    (reward : {S : Finset Bool // S.Nonempty} → Payoff Bool)
    (owner : Bool)
    (howner : quittingSingletonCollisionReward reward (!owner) owner ≤
      quittingSoloReward reward (!owner) owner)
    (hblocker : quittingSoloReward reward owner (!owner) ≤
      quittingSoloReward reward (!owner) (!owner)) :
    ∀ ε : ℝ, 0 < ε →
      ∃ profile : (quittingGame reward).BehaviorProfile,
        (quittingGame reward).IsεAsymptoticNash
            (quittingTerminalPayoff reward) ε profile ∧
          ∀ who,
            |quittingTerminalPayoff reward profile who -
              quittingSoloReward reward (!owner) who| ≤ ε := by
  cases owner
  · intro ε hε
    obtain ⟨profile, hnash, hclose⟩ :=
      exists_terminalNash_approxTarget_all_errors_of_pairRepair
        reward howner hblocker ε hε
    exact ⟨profile, hnash, fun who ↦ by simpa using hclose who⟩
  · intro ε hε
    obtain ⟨profile, hnash, hclose⟩ :=
      exists_terminalNash_approxTarget_all_errors_of_mirrorPairRepair
        reward howner hblocker ε hε
    exact ⟨profile, hnash, fun who ↦ by simpa using hclose who⟩

/-- Role-parametric fixed-target two-player pair repair.  The owner uses a
vanishing hazard, `!owner` quits surely, and the latter's solo reward vector
is the resulting uniform-equilibrium payoff. -/
theorem quittingGame_isUniformEquilibriumPayoff_of_bool_pairRepair
    (reward : {S : Finset Bool // S.Nonempty} → Payoff Bool)
    (owner : Bool)
    (howner : quittingSingletonCollisionReward reward (!owner) owner ≤
      quittingSoloReward reward (!owner) owner)
    (hblocker : quittingSoloReward reward owner (!owner) ≤
      quittingSoloReward reward (!owner) (!owner)) :
    (quittingGame reward).IsUniformEquilibriumPayoff none
      (quittingSoloReward reward (!owner)) := by
  apply quittingGame_isUniformEquilibriumPayoff_of_terminalNash_all_errors_approxTarget
  exact exists_terminalNash_approxTarget_all_errors_of_bool_pairRepair
    reward owner howner hblocker

/-- Existential compatibility wrapper for role-parametric pair repair. -/
theorem exists_uniformEquilibriumPayoff_of_bool_pairRepair
    (reward : {S : Finset Bool // S.Nonempty} → Payoff Bool)
    (owner : Bool)
    (howner : quittingSingletonCollisionReward reward (!owner) owner ≤
      quittingSoloReward reward (!owner) owner)
    (hblocker : quittingSoloReward reward owner (!owner) ≤
      quittingSoloReward reward (!owner) (!owner)) :
    ∃ payoff : Payoff Bool,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  exact ⟨quittingSoloReward reward (!owner),
    quittingGame_isUniformEquilibriumPayoff_of_bool_pairRepair
      reward owner howner hblocker⟩

end QuittingTwoPlayerPairRepair

end GameTheory
