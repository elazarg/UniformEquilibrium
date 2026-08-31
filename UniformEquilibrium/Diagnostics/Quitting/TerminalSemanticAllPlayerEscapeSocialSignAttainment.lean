/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticAllPlayerEscapeMinimumConsequences

/-!
# Social-sign consequences of the all-player terminal escape account

This file derives weak debt domination and actual attainment of the minimum
debt value from nonnegative singleton rewards and nonpositive aggregate
coalition rewards.  Strictly negative aggregate rewards identify every
supplied carrier minimizer with an actual semantic pair.

Weak aggregate signs do not realize an arbitrary carrier minimizer.  These
results do not prove a Fin4 theorem, terminal Nash play, or a uniform-equilibrium
payoff.
-/

noncomputable section

namespace GameTheory

open Filter MeasureTheory Set StochasticGame
open _root_.Math.Probability _root_.Math.ProbabilityMassFunction
open scoped BigOperators ENNReal Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

namespace QuittingTerminalSemanticEscapeAccount

/-- Under the social-nonpositive sign chamber, reconstruction cannot increase
total debt when own-singleton rewards are nonnegative. -/
theorem reconstructedDebtJump_nonpos_of_singleton_nonneg_socialReward_nonpos
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {target : QuittingTerminalSemanticPair ι}
    {selected : QuittingTerminalSemanticSelectedLawLimit reward target}
    (account : QuittingTerminalSemanticEscapeAccount reward target selected)
    (hsingleton : ∀ player,
      0 ≤ reward (quittingSingletonTerminal player) player)
    (hsocial : ∀ terminal, ∑ player, reward terminal player ≤ 0) :
    account.reconstructedDebtJump ≤ 0 := by
  have hcap : 0 ≤ account.reconstructedCapDropSum := by
    unfold reconstructedCapDropSum
    exact Finset.sum_nonneg fun player _ =>
      account.reconstructedCapDrop_nonneg player (hsingleton player)
  have hsocialNonpos : account.escapeSocialReward ≤ 0 := by
    unfold escapeSocialReward
    exact Finset.sum_nonpos fun terminal _ =>
      mul_nonpos_of_nonneg_of_nonpos
        (account.escapeMass_nonneg terminal) (hsocial terminal)
  have haccount :=
    account.escapeSocialReward_eq_reconstructedDebtJump_add_capDropSum
  linarith

/-- Exact zero-account consequences at a supplied global minimum in the
social-nonpositive sign chamber. -/
structure MinimumSocialNonpositiveConsequences
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {target : QuittingTerminalSemanticPair ι}
    {selected : QuittingTerminalSemanticSelectedLawLimit reward target}
    (account : QuittingTerminalSemanticEscapeAccount reward target selected) : Prop where
  reconstructedDebtJump_eq_zero : account.reconstructedDebtJump = 0
  reconstructedCapDropSum_eq_zero : account.reconstructedCapDropSum = 0
  escapeSocialReward_eq_zero : account.escapeSocialReward = 0
  reconstructedCapDrop_eq_zero : ∀ player,
    account.reconstructedCapDrop player = 0
  socialReward_eq_zero_of_escapeMass_pos : ∀ terminal,
    0 < quittingTerminalEscapeMass reward selected.laws
        account.mass terminal →
      ∑ player, reward terminal player = 0

/-- At a global carrier minimum, weak aggregate social signs make the whole
escape/debt/cap account vanish; positive escaped mass can remain only on a
zero-social-reward coalition. -/
theorem minimumSocialNonpositiveConsequences
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {target : QuittingTerminalSemanticPair ι}
    {selected : QuittingTerminalSemanticSelectedLawLimit reward target}
    (account : QuittingTerminalSemanticEscapeAccount reward target selected)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum target ≤
        quittingTerminalSemanticDebtSum candidate)
    (hsingleton : ∀ player,
      0 ≤ reward (quittingSingletonTerminal player) player)
    (hsocial : ∀ terminal, ∑ player, reward terminal player ≤ 0) :
    account.MinimumSocialNonpositiveConsequences := by
  have hcap := account.capDropSum_nonneg_and_le_escapeSocialReward_of_minimum
    hminimum hsingleton
  have hsocialNonpos : account.escapeSocialReward ≤ 0 := by
    unfold escapeSocialReward
    exact Finset.sum_nonpos fun terminal _ =>
      mul_nonpos_of_nonneg_of_nonpos
        (account.escapeMass_nonneg terminal) (hsocial terminal)
  have hcapSumZero : account.reconstructedCapDropSum = 0 := by
    linarith [hcap.1, hcap.2]
  have hsocialZero : account.escapeSocialReward = 0 := by
    linarith [hcap.2, hcapSumZero]
  have hjumpZero : account.reconstructedDebtJump = 0 := by
    have haccount :=
      account.escapeSocialReward_eq_reconstructedDebtJump_add_capDropSum
    linarith
  have hcapZero : ∀ player, account.reconstructedCapDrop player = 0 := by
    intro player
    have hnonneg : 0 ≤ account.reconstructedCapDrop player :=
      account.reconstructedCapDrop_nonneg player (hsingleton player)
    have hle : account.reconstructedCapDrop player ≤
        account.reconstructedCapDropSum := by
      unfold reconstructedCapDropSum
      exact Finset.single_le_sum
        (fun other _ =>
          account.reconstructedCapDrop_nonneg other (hsingleton other))
        (Finset.mem_univ player)
    linarith
  refine ⟨hjumpZero, hcapSumZero, hsocialZero, hcapZero, ?_⟩
  intro terminal hmassPos
  let term := fun outcome : {S : Finset ι // S.Nonempty} =>
    quittingTerminalEscapeMass reward selected.laws account.mass outcome *
      ∑ player, reward outcome player
  have htermNonpos : ∀ outcome, term outcome ≤ 0 := by
    intro outcome
    exact mul_nonpos_of_nonneg_of_nonpos
      (account.escapeMass_nonneg outcome) (hsocial outcome)
  have hsumZero : ∑ outcome, term outcome = 0 := by
    simpa only [escapeSocialReward, term] using hsocialZero
  have hrestNonpos :
      ∑ outcome ∈ (Finset.univ.erase terminal), term outcome ≤ 0 :=
    Finset.sum_nonpos fun outcome _ => htermNonpos outcome
  have hdecomp := Finset.sum_erase_add (Finset.univ) term
    (Finset.mem_univ terminal)
  have htermNonneg : 0 ≤ term terminal := by
    rw [hsumZero] at hdecomp
    linarith
  have htermZero : term terminal = 0 :=
    le_antisymm (htermNonpos terminal) htermNonneg
  unfold term at htermZero
  exact (mul_eq_zero.mp htermZero).resolve_left (ne_of_gt hmassPos)

end QuittingTerminalSemanticEscapeAccount

/-- Every carrier point in the social-nonpositive sign chamber is weakly
debt-dominated by one actual behavioral profile. -/
theorem exists_actualProfile_debtSum_le_of_singleton_nonneg_socialReward_nonpos
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (target : QuittingTerminalSemanticPair ι)
    (htarget : target ∈ quittingTerminalSemanticCarrier reward)
    (hsingleton : ∀ player,
      0 ≤ reward (quittingSingletonTerminal player) player)
    (hsocial : ∀ terminal, ∑ player, reward terminal player ≤ 0) :
    ∃ profile : (quittingGame reward).BehaviorProfile,
      quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward profile) ≤
        quittingTerminalSemanticDebtSum target := by
  obtain ⟨selected, ⟨account⟩⟩ :=
    exists_quittingTerminalSemanticEscapeAccount_of_mem_carrier
      reward target htarget
  let profile := quittingCompactStoppingLawProfile reward selected.laws
  refine ⟨profile, ?_⟩
  have hjump :=
    account.reconstructedDebtJump_nonpos_of_singleton_nonneg_socialReward_nonpos
      hsingleton hsocial
  unfold QuittingTerminalSemanticEscapeAccount.reconstructedDebtJump at hjump
  dsimp only [profile]
  linarith

/-- A globally minimizing carrier debt value in the social-nonpositive sign
chamber is matched by one actual behavioral profile. -/
theorem exists_actualProfile_debtSum_eq_of_minimum_singleton_nonneg_socialReward_nonpos
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (target : QuittingTerminalSemanticPair ι)
    (htarget : target ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum target ≤
        quittingTerminalSemanticDebtSum candidate)
    (hsingleton : ∀ player,
      0 ≤ reward (quittingSingletonTerminal player) player)
    (hsocial : ∀ terminal, ∑ player, reward terminal player ≤ 0) :
    ∃ profile : (quittingGame reward).BehaviorProfile,
      quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward profile) =
        quittingTerminalSemanticDebtSum target := by
  obtain ⟨profile, hle⟩ :=
    exists_actualProfile_debtSum_le_of_singleton_nonneg_socialReward_nonpos
      reward target htarget hsingleton hsocial
  refine ⟨profile, le_antisymm hle ?_⟩
  exact hminimum _ (quittingTerminalSemanticPair_mem_carrier reward profile)

/-- In the social-nonpositive sign chamber, the global carrier minimum debt
value is attained by an actual profile. -/
theorem exists_actual_minimum_of_singleton_nonneg_social_nonpos
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (target : QuittingTerminalSemanticPair ι)
    (htarget : target ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum target ≤
        quittingTerminalSemanticDebtSum candidate)
    (hsingleton : ∀ player,
      0 ≤ reward (quittingSingletonTerminal player) player)
    (hsocial : ∀ terminal, ∑ player, reward terminal player ≤ 0) :
    ∃ profile : (quittingGame reward).BehaviorProfile,
      quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward profile) =
        quittingTerminalSemanticDebtSum target ∧
      ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
        quittingTerminalSemanticDebtSum
            (quittingTerminalSemanticPair reward profile) ≤
          quittingTerminalSemanticDebtSum candidate := by
  obtain ⟨profile, heq⟩ :=
    exists_actualProfile_debtSum_eq_of_minimum_singleton_nonneg_socialReward_nonpos
      reward target htarget hminimum hsingleton hsocial
  refine ⟨profile, heq, ?_⟩
  intro candidate hcandidate
  rw [heq]
  exact hminimum candidate hcandidate

/-- Under strictly negative aggregate reward at every coalition, every
globally minimizing carrier point in the nonnegative-singleton chamber is
itself the semantic pair of one actual behavioral profile. -/
theorem minimum_point_attained_of_singleton_nonneg_social_neg
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (target : QuittingTerminalSemanticPair ι)
    (htarget : target ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum target ≤
        quittingTerminalSemanticDebtSum candidate)
    (hsingleton : ∀ player,
      0 ≤ reward (quittingSingletonTerminal player) player)
    (hsocial : ∀ terminal, ∑ player, reward terminal player < 0) :
    ∃ profile : (quittingGame reward).BehaviorProfile,
      quittingTerminalSemanticPair reward profile = target := by
  obtain ⟨selected, ⟨account⟩⟩ :=
    exists_quittingTerminalSemanticEscapeAccount_of_mem_carrier
      reward target htarget
  have consequences := account.minimumSocialNonpositiveConsequences
    hminimum hsingleton (fun terminal => (hsocial terminal).le)
  let profile := quittingCompactStoppingLawProfile reward selected.laws
  have hescapeZero : ∀ terminal,
      quittingTerminalEscapeMass reward selected.laws account.mass terminal = 0 := by
    intro terminal
    apply le_antisymm
    · by_contra hnot
      have hmassPos : 0 < quittingTerminalEscapeMass reward selected.laws
          account.mass terminal :=
        lt_of_not_ge hnot
      exact (ne_of_lt (hsocial terminal))
        (consequences.socialReward_eq_zero_of_escapeMass_pos terminal hmassPos)
    · exact account.escapeMass_nonneg terminal
  refine ⟨profile, ?_⟩
  apply Prod.ext
  · funext player
    have hmoment := account.escapedRewardMoment_eq player
    have hsum :
        (∑ terminal, quittingTerminalEscapeMass reward selected.laws
          account.mass terminal * reward terminal player) = 0 := by
      simp only [hescapeZero, zero_mul, Finset.sum_const_zero]
    change quittingTerminalPayoff reward profile player = target.1 player
    linarith
  · funext player
    have hcap := consequences.reconstructedCapDrop_eq_zero player
    unfold QuittingTerminalSemanticEscapeAccount.reconstructedCapDrop at hcap
    change quittingContinuationBestResponseValue reward profile player =
      target.2 player
    linarith

end GameTheory
