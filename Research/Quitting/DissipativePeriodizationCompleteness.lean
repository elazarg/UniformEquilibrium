/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Research.Quitting.PrefixTruncationExploitability
import UniformEquilibrium.Quitting.Cycles.ConditionedPeriodicRenewal

/-!
# Purely periodic hazard words are complete on the dissipative half

Call a hazard word dissipative when every player's deleted clock vanishes,
that is when for each player the probability that nobody except possibly that
player has quit before `cutoff` tends to zero.  On a dissipative word the
truncation estimate of `Research.Quitting.PrefixTruncationExploitability` can
be driven below any prescribed tolerance by taking the cutoff late enough, and
the cheapest object agreeing with the word up to that cutoff is the word's own
prefix repeated forever.

Hence every dissipative hazard word is matched, within any positive
tolerance, by a purely periodic one
(`exists_periodic_rootSequenceExploitability_le_of_dissipative`), with no
hypothesis on the word beyond dissipativity: no bound on the period, no
regularity of the hazards, no separation of atomic from vanishing rates.  The
consequence for a screen is stated directly: a floor on maximum terminal
exploitability verified only against purely periodic hazard words already
holds against every dissipative one
(`le_rootSequenceExploitability_of_dissipative_of_periodic_floor`), and the
periodic infimum is below every dissipative word's exploitability
(`quittingPeriodicExploitabilityInf_le_of_dissipative`).

Nothing here bears on words that are not dissipative, where some player's
deleted clock stays positive and the prefix estimate does not close.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability QuittingBoundaryHolonomy
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## Dissipative hazard words -/

/-- A hazard word is dissipative when every player's deleted clock vanishes:
for each player, the probability that nobody except possibly that player has
quit before the cutoff tends to zero. -/
def QuittingDissipativeRoots (roots : ℕ → ι → PMF Bool) : Prop :=
  ∀ who : ι, Tendsto
    (fun cutoff => quittingOpponentSurvivalWeight roots who 0 cutoff)
    atTop (𝓝 0)

/-- On a dissipative word the largest deleted clock vanishes. -/
theorem tendsto_finitePlayerMax_opponentSurvivalWeight_of_dissipative
    [Nonempty ι] {roots : ℕ → ι → PMF Bool}
    (hdissipative : QuittingDissipativeRoots roots) :
    Tendsto (fun cutoff => finitePlayerMax fun who =>
        quittingOpponentSurvivalWeight roots who 0 cutoff) atTop (𝓝 0) := by
  unfold finitePlayerMax
  exact Math.Finset.tendsto_sup'_nhds_zero Finset.univ_nonempty
    (fun who cutoff => quittingOpponentSurvivalWeight roots who 0 cutoff)
    (fun who _ cutoff => quittingOpponentSurvivalWeight_nonneg roots who 0 cutoff)
    (fun who _ => hdissipative who)

/-! ## Periodizing a prefix -/

omit [Fintype ι] [DecidableEq ι] in
/-- Repeating the window `[0, window]` reproduces the source word on that
window. -/
theorem quittingPeriodizedTailWindowRoots_zero_of_lt
    (roots : ℕ → ι → PMF Bool) (window time : ℕ) (htime : time < window + 1) :
    quittingPeriodizedTailWindowRoots roots 0 window time = roots time := by
  rw [quittingPeriodizedTailWindowRoots_of_lt roots 0 window time htime,
    Nat.zero_add]

/-- **Periodizing a prefix costs at most the truncation error.**  Repeating
the window `[0, window]` forever raises maximum terminal exploitability by at
most `4M` times the largest deleted clock through that window. -/
theorem quittingRootSequenceExploitability_periodizedTailWindow_le
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (window : ℕ)
    {M error : ℝ}
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (herror : 4 * M * finitePlayerMax (fun who =>
      quittingOpponentSurvivalWeight roots who 0 (window + 1)) ≤ error) :
    quittingRootSequenceExploitability reward
        (quittingPeriodizedTailWindowRoots roots 0 window) ≤
      quittingRootSequenceExploitability reward roots + error := by
  have hbound := abs_quittingRootSequenceExploitability_sub_le_opponentSurvival
    reward (quittingPeriodizedTailWindowRoots roots 0 window) roots
    (window + 1) hreward
    (fun time htime =>
      quittingPeriodizedTailWindowRoots_zero_of_lt roots window time htime)
  have hdiff := (abs_le.mp hbound).2
  linarith

/-! ## Completeness of the purely periodic class on the dissipative half -/

/-- **Clause-(A) completeness on the dissipative half.**  Every dissipative
hazard word is matched within any positive tolerance by a purely periodic
hazard word.  No hypothesis constrains the source word: aperiodic, mixed
atomic and vanishing, or arbitrarily irregular schedules are all covered. -/
theorem exists_periodic_rootSequenceExploitability_le_of_dissipative
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool)
    (hdissipative : QuittingDissipativeRoots roots)
    {tolerance : ℝ} (htolerance : 0 < tolerance) :
    ∃ (period : ℕ) (periodic : ℕ → ι → PMF Bool),
      0 < period ∧
      (∀ time, periodic (time + period) = periodic time) ∧
      quittingRootSequenceExploitability reward periodic ≤
        quittingRootSequenceExploitability reward roots + tolerance := by
  have hreward := abs_reward_le_quittingRewardBound reward
  have hclock := tendsto_finitePlayerMax_opponentSurvivalWeight_of_dissipative
    (roots := roots) hdissipative
  have hscaled : Tendsto (fun cutoff =>
      4 * quittingRewardBound reward * finitePlayerMax fun who =>
        quittingOpponentSurvivalWeight roots who 0 cutoff) atTop (𝓝 0) := by
    simpa using hclock.const_mul (4 * quittingRewardBound reward)
  obtain ⟨cutoff, hcutoff, hone⟩ :=
    ((hscaled.eventually_le_const htolerance).and (eventually_ge_atTop 1)).exists
  obtain ⟨window, rfl⟩ : ∃ window, cutoff = window + 1 :=
    ⟨cutoff - 1, (Nat.succ_pred_eq_of_pos hone).symm⟩
  exact ⟨window + 1, quittingPeriodizedTailWindowRoots roots 0 window,
    Nat.succ_pos window,
    quittingPeriodizedTailWindowRoots_add_period roots 0 window,
    quittingRootSequenceExploitability_periodizedTailWindow_le
      reward roots window hreward hcutoff⟩

/-- A floor on maximum terminal exploitability verified against every purely
periodic hazard word already holds against every dissipative one.  A screen
validated only on the periodic class is therefore sound on the whole
dissipative half. -/
theorem le_rootSequenceExploitability_of_dissipative_of_periodic_floor
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {floor : ℝ}
    (hperiodic : ∀ (period : ℕ) (periodic : ℕ → ι → PMF Bool), 0 < period →
      (∀ time, periodic (time + period) = periodic time) →
      floor ≤ quittingRootSequenceExploitability reward periodic)
    (roots : ℕ → ι → PMF Bool)
    (hdissipative : QuittingDissipativeRoots roots) :
    floor ≤ quittingRootSequenceExploitability reward roots := by
  refine le_of_forall_pos_le_add fun tolerance htolerance => ?_
  obtain ⟨period, periodic, hpos, hcycle, hmatch⟩ :=
    exists_periodic_rootSequenceExploitability_le_of_dissipative
      reward roots hdissipative htolerance
  exact (hperiodic period periodic hpos hcycle).trans hmatch

/-! ## The periodic infimum -/

/-- Infimum of maximum terminal exploitability over purely periodic hazard
words. -/
def quittingPeriodicExploitabilityInf [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) : ℝ :=
  sInf {value : ℝ | ∃ (period : ℕ) (periodic : ℕ → ι → PMF Bool),
    0 < period ∧ (∀ time, periodic (time + period) = periodic time) ∧
    value = quittingRootSequenceExploitability reward periodic}

theorem bddBelow_quittingPeriodicExploitability [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    BddBelow {value : ℝ | ∃ (period : ℕ) (periodic : ℕ → ι → PMF Bool),
      0 < period ∧ (∀ time, periodic (time + period) = periodic time) ∧
      value = quittingRootSequenceExploitability reward periodic} := by
  refine ⟨0, ?_⟩
  rintro value ⟨-, periodic, -, -, rfl⟩
  exact quittingRootSequenceExploitability_nonneg reward periodic

/-- **The periodic infimum is below every dissipative word.**  On the
dissipative half, restricting the exploitability minimization to purely
periodic hazard words loses nothing. -/
theorem quittingPeriodicExploitabilityInf_le_of_dissipative
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool)
    (hdissipative : QuittingDissipativeRoots roots) :
    quittingPeriodicExploitabilityInf reward ≤
      quittingRootSequenceExploitability reward roots := by
  refine le_of_forall_pos_le_add fun tolerance htolerance => ?_
  obtain ⟨period, periodic, hpos, hcycle, hmatch⟩ :=
    exists_periodic_rootSequenceExploitability_le_of_dissipative
      reward roots hdissipative htolerance
  refine le_trans (csInf_le (bddBelow_quittingPeriodicExploitability reward)
    ⟨period, periodic, hpos, hcycle, rfl⟩) hmatch

/-! ## The same statements for behavior profiles -/

/-- **Clause-(A) completeness for behavior profiles.**  A behavior profile
whose live-path hazard word is dissipative is matched within any positive
tolerance by a purely periodic hazard word, read as a history-independent
profile.  Off-path prescriptions of the source profile play no role: by the
live-root factorization they are invisible to terminal exploitability. -/
theorem exists_periodic_quittingTerminalExploitability_le_of_dissipative
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (hdissipative :
      QuittingDissipativeRoots (quittingProfileLiveRoot reward profile))
    {tolerance : ℝ} (htolerance : 0 < tolerance) :
    ∃ (period : ℕ) (periodic : ℕ → ι → PMF Bool),
      0 < period ∧
      (∀ time, periodic (time + period) = periodic time) ∧
      quittingTerminalExploitability reward
          (quittingRootSequenceProfile reward periodic 0) ≤
        quittingTerminalExploitability reward profile + tolerance := by
  rw [quittingTerminalExploitability_eq_rootSequenceExploitability
    reward profile]
  exact exists_periodic_rootSequenceExploitability_le_of_dissipative
    reward (quittingProfileLiveRoot reward profile) hdissipative htolerance

end GameTheory
