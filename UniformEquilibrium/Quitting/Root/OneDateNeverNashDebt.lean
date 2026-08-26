/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Root.NashExistence
import UniformEquilibrium.Quitting.Root.TerminalDebtPrefix
import UniformEquilibrium.Quitting.Root.TerminalOpponentAdvantage
import UniformEquilibrium.Quitting.Terminal.TailCompression.ElementaryCaps

/-!
# A universal one-date-then-Never terminal debt bound

Choose an exact mixed Nash root of the finite quitting action game with zero
continuation payoff. Realize that root literally at date zero, followed by
perpetual Continue. Every player's unrestricted behavioral terminal debt is
at most two thirds of a uniform terminal-reward bound.

The proof combines the exact all-behavior root-prefix debt recursion with two
affine estimates. Opponent Continue mass controls the late solo opportunity;
opponent absorption controls the difference between joining and not joining
the same nonempty opponent coalition. Their worst crossing is at mass `2/3`.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Play one product root at date zero, then Continue forever. -/
def quittingOneDateThenNeverProfile
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) : (quittingGame reward).BehaviorProfile :=
  quittingRootThenContinuationProfile reward root
    (quittingAlwaysContinueProfile reward)

/-- The augmented Continue endpoint is the late-quit value. -/
theorem quittingRootContinuePayoff_const_singleton_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (who : ι) :
    quittingRootContinuePayoff reward
        (fun _ ↦ reward (quittingSingletonTerminal who) who) root who =
      quittingRootContinuePayoff reward (0 : Payoff ι) root who +
        quittingRootOpponentContinueMass root who *
          reward (quittingSingletonTerminal who) who := by
  unfold quittingRootContinuePayoff
  rw [quittingRootExpectedPayoff_eq_absorbingContribution_add,
    quittingRootExpectedPayoff_eq_absorbingContribution_add]
  simp [quittingRootOpponentContinueMass]

/-- The late-quit value exceeds immediate Quit by at most twice the reward
bound times the probability that some opponent quits at date zero. -/
theorem quittingRootContinue_add_solo_sub_quit_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (who : ι) {bound : ℝ}
    (hreward : ∀ terminal player, |reward terminal player| ≤ bound) :
    quittingRootContinuePayoff reward (0 : Payoff ι) root who +
          quittingRootOpponentContinueMass root who *
            reward (quittingSingletonTerminal who) who -
        quittingRootQuitPayoff reward (0 : Payoff ι) root who ≤
      2 * bound * quittingRootOpponentAbsorptionMass root who := by
  let fixed := Function.update root who (PMF.pure false)
  let advantage := quittingTerminalOpponentAdvantage reward who
  let event : (ι → Bool) → ℝ := fun action =>
    if (quittingQuitters action).Nonempty then 1 else 0
  have hadvantage : ∀ action, advantage action ≤ 2 * bound * event action := by
    intro action
    by_cases hquit : (quittingQuitters action).Nonempty
    · have hevent : event action = 1 := by
        dsimp only [event]
        rw [if_pos hquit]
      rw [hevent]
      unfold advantage quittingTerminalOpponentAdvantage
      rw [quittingRootPayoff, dif_pos hquit]
      have hupdated :
          (quittingQuitters (Function.update action who true)).Nonempty := by
        rw [quittingQuitters_update_true_of_apply_false]
        exact Finset.insert_nonempty who _
      rw [quittingRootPayoff, dif_pos hupdated]
      have hfirst := le_of_abs_le
        (hreward ⟨quittingQuitters action, hquit⟩ who)
      have hsecond := neg_le_of_abs_le
        (hreward
          ⟨quittingQuitters (Function.update action who true), hupdated⟩
          who)
      linarith
    · have hevent : event action = 0 := by
        dsimp only [event]
        rw [if_neg hquit]
      rw [hevent]
      have hempty : quittingQuitters action = ∅ :=
        Finset.not_nonempty_iff_eq_empty.mp hquit
      have hwho : action who = false := by
        cases haction : action who with
        | false => rfl
        | true =>
            exact (hquit ((quittingQuitters_nonempty_iff action).2
              ⟨who, haction⟩)).elim
      unfold advantage quittingTerminalOpponentAdvantage
      rw [quittingRootPayoff, dif_neg hquit]
      have hupdated : quittingQuitters (Function.update action who true) =
          {who} := by
        rw [quittingQuitters_update_true_of_apply_false, hempty]
        simp
      have hupdatedNonempty :
          (quittingQuitters (Function.update action who true)).Nonempty := by
        rw [hupdated]
        exact Finset.singleton_nonempty who
      rw [quittingRootPayoff, dif_pos hupdatedNonempty]
      rw [mul_zero]
      apply le_of_eq
      apply sub_eq_zero.mpr
      apply congrArg (fun terminal => reward terminal who)
      exact Subtype.ext hupdated.symm
  have hexpect : expect (pmfPi fixed) advantage ≤
      expect (pmfPi fixed) (fun action => 2 * bound * event action) :=
    expect_mono _ _ _ hadvantage
  rw [expect_const_mul] at hexpect
  have hevent : expect (pmfPi fixed) event =
      quittingRootOpponentAbsorptionMass root who := by
    have hfunction : event = fun action =>
        1 - if action = (quittingAllContinueAction : ι → Bool)
          then 1 else 0 := by
      funext action
      by_cases hquit : (quittingQuitters action).Nonempty
      · have hne : action ≠ (quittingAllContinueAction : ι → Bool) := by
          intro heq
          subst action
          simp at hquit
        rw [show event action = 1 by
          dsimp only [event]
          rw [if_pos hquit], if_neg hne]
        norm_num
      · have heq :=
          eq_quittingAllContinueAction_of_quittingQuitters_not_nonempty
            action hquit
        rw [show event action = 0 by
          dsimp only [event]
          rw [if_neg hquit], if_pos heq]
        norm_num
    rw [hfunction, expect_sub, expect_const,
      ← apply_toReal_eq_expect_indicator]
    rfl
  rw [hevent] at hexpect
  dsimp only [fixed, advantage] at hexpect
  rw [expect_terminalOpponentAdvantage reward root who,
    quittingRootContinuePayoff_const_singleton_eq] at hexpect
  exact hexpect

/-- Exact unrestricted debt formula for one product root followed by Never. -/
theorem quittingTerminalDeviationDebt_oneDateThenNever_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (who : ι)
    (hnash : IsεQuittingRootNash reward (0 : Payoff ι) 0 root) :
    quittingTerminalDeviationDebt reward
        (quittingOneDateThenNeverProfile reward root) who =
      max
          (quittingRootQuitPayoff reward (0 : Payoff ι) root who)
          (quittingRootContinuePayoff reward (0 : Payoff ι) root who +
            quittingRootOpponentContinueMass root who *
              max 0 (reward (quittingSingletonTerminal who) who)) -
        max
          (quittingRootQuitPayoff reward (0 : Payoff ι) root who)
          (quittingRootContinuePayoff reward (0 : Payoff ι) root who) := by
  have htail :
      (fun player => quittingTerminalPayoff reward
        (quittingAlwaysContinueProfile reward) player) =
      (0 : Payoff ι) := by
    funext player
    exact quittingTerminalPayoff_quittingAlwaysContinue reward player
  have hnash' : IsεQuittingRootNash reward
      (fun player => quittingTerminalPayoff reward
        (quittingAlwaysContinueProfile reward) player) 0 root := by
    rw [htail]
    exact hnash
  unfold quittingOneDateThenNeverProfile
  rw [quittingTerminalDeviationDebt_rootThenContinuation_eq
    reward root (quittingAlwaysContinueProfile reward) who hnash']
  rw [htail]
  rw [show quittingTerminalDeviationDebt reward
      (quittingAlwaysContinueProfile reward) who =
        max 0 (reward (quittingSingletonTerminal who) who) by
    unfold quittingTerminalDeviationDebt
    rw [quittingContinuationBestResponseValue_quittingAlwaysContinueProfile,
      quittingTerminalPayoff_quittingAlwaysContinue]
    ring]

/-- If a player's solo terminal reward is nonpositive, the exact zero-tail
Nash root followed by Never has zero unrestricted debt for that player. -/
theorem quittingTerminalDeviationDebt_oneDateThenNever_eq_zero_of_solo_nonpos
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (who : ι)
    (hnash : IsεQuittingRootNash reward (0 : Payoff ι) 0 root)
    (hsolo : reward (quittingSingletonTerminal who) who ≤ 0) :
    quittingTerminalDeviationDebt reward
        (quittingOneDateThenNeverProfile reward root) who = 0 := by
  have hformula := quittingTerminalDeviationDebt_oneDateThenNever_eq
    reward root who hnash
  rw [max_eq_left hsolo] at hformula
  simpa using hformula

/-- The exact zero-tail Nash recursion retains the player-specific product of
opponent Continue mass and positive solo reward. -/
theorem quittingTerminalDeviationDebt_oneDateThenNever_le_continueMass_mul_solo
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (who : ι)
    (hnash : IsεQuittingRootNash reward (0 : Payoff ι) 0 root) :
    quittingTerminalDeviationDebt reward
        (quittingOneDateThenNeverProfile reward root) who ≤
      quittingRootOpponentContinueMass root who *
        max 0 (reward (quittingSingletonTerminal who) who) := by
  have htail :
      (fun player => quittingTerminalPayoff reward
        (quittingAlwaysContinueProfile reward) player) =
      (0 : Payoff ι) := by
    funext player
    exact quittingTerminalPayoff_quittingAlwaysContinue reward player
  have hnash' : IsεQuittingRootNash reward
      (fun player => quittingTerminalPayoff reward
        (quittingAlwaysContinueProfile reward) player) 0 root := by
    rw [htail]
    exact hnash
  have hdebt := quittingTerminalDeviationDebt_rootThenContinuation_le
    reward root (quittingAlwaysContinueProfile reward) who hnash'
  change quittingTerminalDeviationDebt reward
      (quittingOneDateThenNeverProfile reward root) who ≤
    quittingRootOpponentContinueMass root who *
      quittingTerminalDeviationDebt reward
        (quittingAlwaysContinueProfile reward) who at hdebt
  rw [show quittingTerminalDeviationDebt reward
      (quittingAlwaysContinueProfile reward) who =
        max 0 (reward (quittingSingletonTerminal who) who) by
    unfold quittingTerminalDeviationDebt
    rw [quittingContinuationBestResponseValue_quittingAlwaysContinueProfile,
      quittingTerminalPayoff_quittingAlwaysContinue]
    ring] at hdebt
  exact hdebt

/-- Joining-versus-not-joining at date zero retains a second player-specific
bound: twice the reward bound times opponent absorption mass. -/
theorem quittingTerminalDeviationDebt_oneDateThenNever_le_two_mul_absorptionMass
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (who : ι) {bound : ℝ}
    (hbound_nonneg : 0 ≤ bound)
    (hreward : ∀ terminal player, |reward terminal player| ≤ bound)
    (hnash : IsεQuittingRootNash reward (0 : Payoff ι) 0 root) :
    quittingTerminalDeviationDebt reward
        (quittingOneDateThenNeverProfile reward root) who ≤
      2 * bound * quittingRootOpponentAbsorptionMass root who := by
  let debt := quittingTerminalDeviationDebt reward
    (quittingOneDateThenNeverProfile reward root) who
  let quitValue :=
    quittingRootQuitPayoff reward (0 : Payoff ι) root who
  let continueValue :=
    quittingRootContinuePayoff reward (0 : Payoff ι) root who
  let mass := quittingRootOpponentContinueMass root who
  let solo := reward (quittingSingletonTerminal who) who
  have hformula : debt =
      max quitValue (continueValue + mass * max 0 solo) -
        max quitValue continueValue := by
    exact quittingTerminalDeviationDebt_oneDateThenNever_eq
      reward root who hnash
  change debt ≤ 2 * bound * quittingRootOpponentAbsorptionMass root who
  by_cases hsolo : solo ≤ 0
  · have hzero : debt = 0 := by
      exact quittingTerminalDeviationDebt_oneDateThenNever_eq_zero_of_solo_nonpos
        reward root who hnash hsolo
    rw [hzero]
    exact mul_nonneg (mul_nonneg (by norm_num) hbound_nonneg)
      (quittingRootOpponentAbsorptionMass_nonneg root who)
  · have hsolo0 : 0 ≤ solo := le_of_not_ge hsolo
    rw [max_eq_right hsolo0] at hformula
    have hraw :
        continueValue + mass * solo - quitValue ≤
          2 * bound * quittingRootOpponentAbsorptionMass root who := by
      simpa only [continueValue, mass, solo, quitValue] using
        quittingRootContinue_add_solo_sub_quit_le reward root who hreward
    by_cases hlate : continueValue + mass * solo ≤ quitValue
    · have hdebtNonpos : debt ≤ 0 := by
        rw [hformula, max_eq_left hlate]
        exact sub_nonpos.mpr (le_max_left _ _)
      exact hdebtNonpos.trans
        (mul_nonneg (mul_nonneg (by norm_num) hbound_nonneg)
          (quittingRootOpponentAbsorptionMass_nonneg root who))
    · have hquitLate : quitValue ≤ continueValue + mass * solo :=
        le_of_not_ge hlate
      rw [hformula, max_eq_right hquitLate]
      calc
        continueValue + mass * solo - max quitValue continueValue ≤
            continueValue + mass * solo - quitValue := by
          gcongr
          exact le_max_left _ _
        _ ≤ 2 * bound * quittingRootOpponentAbsorptionMass root who := hraw

/-- Full data-sensitive certificate retained by the one-date-then-Never
construction.  The two mass bounds have worst crossing at Continue mass
`2/3`; the first clause records the exact zero arm separately. -/
theorem quittingTerminalDeviationDebt_oneDateThenNever_dataSensitive
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (who : ι) {bound : ℝ}
    (hbound_nonneg : 0 ≤ bound)
    (hreward : ∀ terminal player, |reward terminal player| ≤ bound)
    (hnash : IsεQuittingRootNash reward (0 : Payoff ι) 0 root) :
    (reward (quittingSingletonTerminal who) who ≤ 0 →
      quittingTerminalDeviationDebt reward
        (quittingOneDateThenNeverProfile reward root) who = 0) ∧
    quittingTerminalDeviationDebt reward
        (quittingOneDateThenNeverProfile reward root) who ≤
      quittingRootOpponentContinueMass root who *
        max 0 (reward (quittingSingletonTerminal who) who) ∧
    quittingTerminalDeviationDebt reward
        (quittingOneDateThenNeverProfile reward root) who ≤
      2 * bound * quittingRootOpponentAbsorptionMass root who := by
  exact ⟨quittingTerminalDeviationDebt_oneDateThenNever_eq_zero_of_solo_nonpos
      reward root who hnash,
    quittingTerminalDeviationDebt_oneDateThenNever_le_continueMass_mul_solo
      reward root who hnash,
    quittingTerminalDeviationDebt_oneDateThenNever_le_two_mul_absorptionMass
      reward root who hbound_nonneg hreward hnash⟩

/-- A zero-tail Nash root followed literally by Never has unrestricted
behavioral terminal debt at most two thirds of the reward bound. -/
theorem quittingTerminalDeviationDebt_oneDateThenNever_le_two_thirds
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (who : ι) {bound : ℝ}
    (hbound_nonneg : 0 ≤ bound)
    (hreward : ∀ terminal player, |reward terminal player| ≤ bound)
    (hnash : IsεQuittingRootNash reward (0 : Payoff ι) 0 root) :
    quittingTerminalDeviationDebt reward
        (quittingOneDateThenNeverProfile reward root) who ≤
      2 * bound / 3 := by
  let mass := quittingRootOpponentContinueMass root who
  let solo := reward (quittingSingletonTerminal who) who
  have hmass0 : 0 ≤ mass :=
    quittingRootOpponentContinueMass_nonneg root who
  have hmass1 : mass ≤ 1 :=
    quittingRootOpponentContinueMass_le_one root who
  have hsoloUpper : solo ≤ bound :=
    le_of_abs_le (hreward (quittingSingletonTerminal who) who)
  have hsoloMax : max 0 solo ≤ bound := max_le hbound_nonneg hsoloUpper
  obtain ⟨-, hfirst, hsecond⟩ :=
    quittingTerminalDeviationDebt_oneDateThenNever_dataSensitive
      reward root who hbound_nonneg hreward hnash
  have hfirstBound : quittingTerminalDeviationDebt reward
      (quittingOneDateThenNeverProfile reward root) who ≤ mass * bound :=
    hfirst.trans (mul_le_mul_of_nonneg_left hsoloMax hmass0)
  have hcomplement : quittingRootOpponentAbsorptionMass root who = 1 - mass := by
    dsimp only [mass]
    rw [quittingRootOpponentContinueMass_eq_one_sub_absorptionMass]
    ring
  rw [hcomplement] at hsecond
  by_cases hmass : mass ≤ 2 / 3
  · exact hfirstBound.trans (by nlinarith)
  · have hmassLower : 2 / 3 ≤ mass := le_of_not_ge hmass
    exact hsecond.trans (by nlinarith)

/-- Every finite quitting game admits a literal one-date-then-Never profile
whose full behavioral terminal debt is at most two thirds of the reward
bound. The returned root is an exact Nash equilibrium of the zero-tail
one-stage game. -/
theorem exists_oneDateThenNever_terminalDebt_le_two_thirds
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {bound : ℝ} (hbound_nonneg : 0 ≤ bound)
    (hreward : ∀ terminal player, |reward terminal player| ≤ bound) :
    ∃ root : ι → PMF Bool,
      IsεQuittingRootNash reward (0 : Payoff ι) 0 root ∧
        ∀ who,
          0 ≤ quittingTerminalDeviationDebt reward
              (quittingOneDateThenNeverProfile reward root) who ∧
            quittingTerminalDeviationDebt reward
                (quittingOneDateThenNeverProfile reward root) who ≤
              2 * bound / 3 := by
  obtain ⟨root, hnash⟩ :=
    exists_isZeroQuittingRootNash (reward := reward) (0 : Payoff ι)
  refine ⟨root, hnash, fun who => ⟨?_, ?_⟩⟩
  · exact quittingTerminalDeviationDebt_nonneg reward
      (quittingOneDateThenNeverProfile reward root) who
  · exact quittingTerminalDeviationDebt_oneDateThenNever_le_two_thirds
      reward root who hbound_nonneg hreward hnash

/-- Every finite quitting game has a literal one-date-then-Never terminal
`2 * bound / 3`-Nash profile against all behavioral deviations. -/
theorem exists_oneDateThenNever_isεAsymptoticNash_two_thirds
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {bound : ℝ} (hbound_nonneg : 0 ≤ bound)
    (hreward : ∀ terminal player, |reward terminal player| ≤ bound) :
    ∃ root : ι → PMF Bool,
      IsεQuittingRootNash reward (0 : Payoff ι) 0 root ∧
        (quittingGame reward).IsεAsymptoticNash
          (quittingTerminalPayoff reward) (2 * bound / 3)
          (quittingOneDateThenNeverProfile reward root) := by
  obtain ⟨root, hnash, hdebt⟩ :=
    exists_oneDateThenNever_terminalDebt_le_two_thirds
      reward hbound_nonneg hreward
  refine ⟨root, hnash, ?_⟩
  intro who deviation
  have hdeviation :=
    quittingTerminalPayoff_update_le_continuationBestResponseValue
      reward (quittingOneDateThenNeverProfile reward root) who deviation
  have hbound := (hdebt who).2
  unfold quittingTerminalDeviationDebt at hbound
  linarith

end GameTheory
