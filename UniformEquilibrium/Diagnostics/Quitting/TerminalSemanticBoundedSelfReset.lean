/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPlateauTightness
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPlateauTimeDisintegration

/-!
# Bounded pure-time self-reset

Suppose every behavioral profile has some coordinate of terminal semantic debt
at least `gap`.  Reset such a debtor to an approximately optimal deterministic
quit time.  The reset leaves that player's best-response envelope unchanged,
reduces its debt to the chosen error, and gains at least `gap - error`.

If the selected deterministic time is `Never`, the player cannot already be
using literal `Never` when the error is smaller than the debt floor.  Iterating
only those `Never` outcomes therefore consumes a new player at every step.
After at most one more step than the number of players, a finite deterministic
quit time is reached.

The resulting inductive chain records every literal unilateral update, its
source debt floor, the reset debt bound, and the exact payoff/debt identity.
No counterexample regime, stopping-law packet, reward sign, or semantic
compactness argument is used.
-/

noncomputable section

namespace GameTheory

open Filter Finset Math.Probability
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A uniform positive-coordinate debt floor over all actual behavioral
profiles. -/
def HasQuittingUniformTerminalDebtFloor
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (gap : ℝ) : Prop :=
  ∀ profile : (quittingGame reward).BehaviorProfile,
    ∃ who, gap ≤ quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward profile) who

/-- One literal pure-time self-reset of a coordinate carrying the supplied
debt floor.  The structure records the exact payoff-gain identity, not only its
derived lower bound. -/
structure QuittingPureTimeSelfResetStep
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (gap error : ℝ) (source : (quittingGame reward).BehaviorProfile) where
  player : ι
  quitTime : Option ℕ
  target : (quittingGame reward).BehaviorProfile
  source_debt_floor : gap ≤ quittingTerminalSemanticDebt
    (quittingTerminalSemanticPair reward source) player
  target_eq : target = Function.update source player
    (quittingPureTimeBehaviorStrategy reward player quitTime)
  target_debt_le_error : quittingTerminalSemanticDebt
    (quittingTerminalSemanticPair reward target) player ≤ error
  payoff_gain_eq_debt_sub :
    quittingTerminalPayoff reward target player -
        quittingTerminalPayoff reward source player =
      quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward source) player -
        quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward target) player

namespace QuittingPureTimeSelfResetStep

/-- Every reset gains at least the source debt floor minus its approximation
error. -/
theorem gap_sub_error_le_payoff_gain
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {gap error : ℝ} {source : (quittingGame reward).BehaviorProfile}
    (step : QuittingPureTimeSelfResetStep reward gap error source) :
    gap - error ≤
      quittingTerminalPayoff reward step.target step.player -
        quittingTerminalPayoff reward source step.player := by
  rw [step.payoff_gain_eq_debt_sub]
  linarith [step.source_debt_floor, step.target_debt_le_error]

/-- A self-reset whose target time is `Never` cannot start from a player who
already uses literal `Never`, provided the approximation error is smaller than
the debt floor. -/
theorem player_not_literalNever_of_quitTime_eq_none
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {gap error : ℝ} {source : (quittingGame reward).BehaviorProfile}
    (step : QuittingPureTimeSelfResetStep reward gap error source)
    (herror : error < gap) (htime : step.quitTime = none) :
    source step.player ≠
      quittingPureTimeBehaviorStrategy reward step.player none := by
  intro halready
  have htarget : step.target = source := by
    rw [step.target_eq, htime]
    funext other
    by_cases hother : other = step.player
    · subst other
      simp only [Function.update_self, halready]
    · simp [Function.update, hother]
  have hzero : quittingTerminalPayoff reward step.target step.player -
      quittingTerminalPayoff reward source step.player = 0 := by
    rw [htarget, sub_self]
  linarith [step.gap_sub_error_le_payoff_gain]

end QuittingPureTimeSelfResetStep

/-- A nonempty finite chronology of literal pure-time self-resets.  Every
nonfinal reset selects `Never`; the final reset selects the displayed finite
stopping time. -/
inductive QuittingPureTimeSelfResetChain
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (gap error : ℝ) :
    (quittingGame reward).BehaviorProfile → ℕ →
      (quittingGame reward).BehaviorProfile → ι → ℕ → Prop
  | final {source : (quittingGame reward).BehaviorProfile}
      (step : QuittingPureTimeSelfResetStep reward gap error source)
      (stop : ℕ) (htime : step.quitTime = some stop) :
      QuittingPureTimeSelfResetChain reward gap error source 1
        step.target step.player stop
  | cons {source finalProfile : (quittingGame reward).BehaviorProfile}
      {length : ℕ} {finalPlayer : ι} {stop : ℕ}
      (step : QuittingPureTimeSelfResetStep reward gap error source)
      (htime : step.quitTime = none)
      (tail : QuittingPureTimeSelfResetChain reward gap error step.target
        length finalProfile finalPlayer stop) :
      QuittingPureTimeSelfResetChain reward gap error source (length + 1)
        finalProfile finalPlayer stop

namespace QuittingPureTimeSelfResetChain

/-- A reset chain has positive length. -/
theorem length_pos
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {gap error : ℝ} {source finalProfile}
    {length : ℕ} {finalPlayer : ι} {stop : ℕ}
    (chain : QuittingPureTimeSelfResetChain reward gap error source length
      finalProfile finalPlayer stop) :
    0 < length := by
  cases chain <;> omega

/-- The last player in a reset chain has debt at most the common reset error
at the final profile. -/
theorem final_debt_le_error
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {gap error : ℝ} {source finalProfile}
    {length : ℕ} {finalPlayer : ι} {stop : ℕ}
    (chain : QuittingPureTimeSelfResetChain reward gap error source length
      finalProfile finalPlayer stop) :
    quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward finalProfile) finalPlayer ≤ error := by
  induction chain with
  | final step stop htime => exact step.target_debt_le_error
  | cons step htime tail ih => exact ih

/-- The final profile is literally obtained by updating the final player to
Quit at the displayed finite time. -/
theorem exists_final_predecessor
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {gap error : ℝ} {source finalProfile}
    {length : ℕ} {finalPlayer : ι} {stop : ℕ}
    (chain : QuittingPureTimeSelfResetChain reward gap error source length
      finalProfile finalPlayer stop) :
    ∃ predecessor : (quittingGame reward).BehaviorProfile,
      finalProfile = Function.update predecessor finalPlayer
        (quittingPureTimeBehaviorStrategy reward finalPlayer (some stop)) := by
  induction chain with
  | @final source step stop htime =>
      refine ⟨source, ?_⟩
      rw [step.target_eq, htime]
  | cons step htime tail ih => exact ih

/-- The final player's displayed strategy is the advertised finite pure-time
strategy. -/
theorem final_player_strategy
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {gap error : ℝ} {source finalProfile}
    {length : ℕ} {finalPlayer : ι} {stop : ℕ}
    (chain : QuittingPureTimeSelfResetChain reward gap error source length
      finalProfile finalPlayer stop) :
    finalProfile finalPlayer =
      quittingPureTimeBehaviorStrategy reward finalPlayer (some stop) := by
  obtain ⟨predecessor, hfinal⟩ := chain.exists_final_predecessor
  rw [hfinal, Function.update_self]

end QuittingPureTimeSelfResetChain

/-- Pure-time extremality turns any coordinate above `gap` into one exact
self-reset step with arbitrarily small positive residual debt. -/
theorem exists_quittingPureTimeSelfResetStep
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (gap error : ℝ) (herror : 0 < error)
    (source : (quittingGame reward).BehaviorProfile) (who : ι)
    (hdebt : gap ≤ quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward source) who) :
    Nonempty (QuittingPureTimeSelfResetStep reward gap error source) := by
  obtain ⟨deviation, hdeviation⟩ :=
    exists_quittingContinuation_deviation_ge_sub reward source who
      (half_pos herror)
  obtain ⟨quitTime, hpure⟩ :=
    exists_quittingPureTimeBehaviorStrategy_terminalPayoff_ge_sub
      reward source who deviation (half_pos herror)
  let target := Function.update source who
    (quittingPureTimeBehaviorStrategy reward who quitTime)
  have hpayoff : quittingContinuationBestResponseValue reward source who -
      error ≤ quittingTerminalPayoff reward target who := by
    dsimp only [target]
    linarith
  have hdebtLe : quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward target) who ≤ error := by
    unfold quittingTerminalSemanticDebt quittingTerminalSemanticPair
    change quittingContinuationBestResponseValue reward target who -
      quittingTerminalPayoff reward target who ≤ error
    rw [quittingContinuationBestResponseValue_update_self]
    linarith
  have hgain : quittingTerminalPayoff reward target who -
        quittingTerminalPayoff reward source who =
      quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward source) who -
        quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward target) who := by
    unfold quittingTerminalSemanticDebt quittingTerminalSemanticPair
    dsimp only [target]
    rw [quittingContinuationBestResponseValue_update_self]
    ring
  exact ⟨{
    player := who
    quitTime := quitTime
    target := target
    source_debt_floor := hdebt
    target_eq := rfl
    target_debt_le_error := hdebtLe
    payoff_gain_eq_debt_sub := hgain
  }⟩

/-- **Bounded self-reset exit theorem.**  Under a uniform coordinate-debt
floor and an error strictly between zero and that floor, every starting
profile admits a literal self-reset chain of length at most `card ι + 1`
whose final reset Quits at a finite deterministic time. -/
theorem exists_bounded_quittingPureTimeSelfResetChain
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (gap error : ℝ) (hfloor : HasQuittingUniformTerminalDebtFloor reward gap)
    (herrorPos : 0 < error) (herrorLt : error < gap)
    (start : (quittingGame reward).BehaviorProfile) :
    ∃ (length : ℕ) (finalProfile : (quittingGame reward).BehaviorProfile)
        (finalPlayer : ι) (stop : ℕ),
      QuittingPureTimeSelfResetChain reward gap error start length
          finalProfile finalPlayer stop ∧
        length ≤ Fintype.card ι + 1 := by
  let motive := fun (remaining : Finset ι) =>
    ∀ profile : (quittingGame reward).BehaviorProfile,
      (∀ who, who ∉ remaining →
        profile who = quittingPureTimeBehaviorStrategy reward who none) →
      ∃ (length : ℕ) (finalProfile : (quittingGame reward).BehaviorProfile)
          (finalPlayer : ι) (stop : ℕ),
        QuittingPureTimeSelfResetChain reward gap error profile length
            finalProfile finalPlayer stop ∧
          length ≤ remaining.card + 1
  have haux : ∀ remaining : Finset ι, motive remaining := by
    intro remaining
    induction hcard : remaining.card using Nat.strong_induction_on generalizing remaining with
    | h card ih =>
        intro profile hnever
        obtain ⟨who, hwhoDebt⟩ := hfloor profile
        obtain ⟨step⟩ := exists_quittingPureTimeSelfResetStep
          reward gap error herrorPos profile who hwhoDebt
        cases htime : step.quitTime with
        | some stop =>
            exact ⟨1, step.target, step.player, stop,
              .final step stop htime, by omega⟩
        | none =>
            have hwhoMem : step.player ∈ remaining := by
              by_contra hwhoNot
              exact step.player_not_literalNever_of_quitTime_eq_none
                herrorLt htime (hnever step.player hwhoNot)
            have heraseCard : (remaining.erase step.player).card < card := by
              rw [← hcard]
              exact Finset.card_erase_lt_of_mem hwhoMem
            have htargetNever : ∀ other, other ∉ remaining.erase step.player →
                step.target other =
                  quittingPureTimeBehaviorStrategy reward other none := by
              intro other hother
              by_cases heq : other = step.player
              · subst other
                rw [step.target_eq, htime, Function.update_self]
              · rw [step.target_eq]
                simp only [Function.update, dif_neg heq]
                exact hnever other fun hmem =>
                  hother (Finset.mem_erase.mpr ⟨heq, hmem⟩)
            obtain ⟨length, finalProfile, finalPlayer, stop, tail, hlength⟩ :=
              ih (remaining.erase step.player).card heraseCard
                (remaining.erase step.player) rfl step.target htargetNever
            exact ⟨length + 1, finalProfile, finalPlayer, stop,
              .cons step htime tail, by
                rw [Finset.card_erase_of_mem hwhoMem] at hlength
                omega⟩
  obtain ⟨length, finalProfile, finalPlayer, stop, chain, hlength⟩ :=
    haux Finset.univ start (by simp)
  exact ⟨length, finalProfile, finalPlayer, stop, chain, by
    simpa using hlength⟩

/-- A profile whose displayed strategy for one player is a finite pure-time
strategy has zero terminal `Never` mass. -/
theorem quittingTerminalOutcomeMass_none_eq_zero_of_pureTimePlayer
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (who : ι) (stop : ℕ)
    (hstrategy : profile who =
      quittingPureTimeBehaviorStrategy reward who (some stop)) :
    quittingTerminalOutcomeMass reward profile none = 0 := by
  have hupdate : Function.update profile who
      (quittingPureTimeBehaviorStrategy reward who (some stop)) = profile :=
    by
      funext other
      by_cases hother : other = who
      · subst other
        simp only [Function.update_self, hstrategy]
      · simp [Function.update, hother]
  change quittingLiveMassLimit reward profile = 0
  rw [← hupdate]
  exact quittingLiveMassLimit_update_pureTimeBehaviorStrategy_some_eq_zero
    reward profile who stop

/-- A finite pure-time player forces some nonempty terminal coalition to have
at least the reciprocal of the number of nonempty coalitions in terminal
mass.  This is the sharp uniform finite-simplex pigeonhole scale. -/
theorem exists_terminal_mass_ge_inv_card_of_pureTimePlayer
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (who : ι) (stop : ℕ)
    (hstrategy : profile who =
      quittingPureTimeBehaviorStrategy reward who (some stop)) :
    ∃ terminal : {S : Finset ι // S.Nonempty},
      1 / (Fintype.card {S : Finset ι // S.Nonempty} : ℝ) ≤
        quittingTerminalOutcomeMass reward profile (some terminal) := by
  let labels := (Finset.univ : Finset {S : Finset ι // S.Nonempty})
  have hlabels : labels.Nonempty := by
    refine ⟨⟨{who}, Finset.singleton_nonempty who⟩, Finset.mem_univ _⟩
  have hcard : 0 < (labels.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hlabels
  have hsum : ∑ terminal : {S : Finset ι // S.Nonempty},
      quittingTerminalOutcomeMass reward profile (some terminal) = 1 := by
    have hsimplex :=
      (quittingTerminalOutcomeMass_mem_stdSimplex reward profile).2
    rw [Fintype.sum_option] at hsimplex
    rw [quittingTerminalOutcomeMass_none_eq_zero_of_pureTimePlayer
      reward profile who stop hstrategy, zero_add] at hsimplex
    exact hsimplex
  have haverage :
      ∑ _terminal : {S : Finset ι // S.Nonempty},
          1 / (Fintype.card {S : Finset ι // S.Nonempty} : ℝ) ≤
        ∑ terminal : {S : Finset ι // S.Nonempty},
          quittingTerminalOutcomeMass reward profile (some terminal) := by
    rw [hsum]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [one_div]
    change (Fintype.card {S : Finset ι // S.Nonempty} : ℝ) *
        (Fintype.card {S : Finset ι // S.Nonempty} : ℝ)⁻¹ ≤ 1
    rw [mul_inv_cancel₀ (by simpa [labels] using ne_of_gt hcard)]
  obtain ⟨terminal, _hterminal, hmass⟩ :=
    Finset.exists_le_of_sum_le hlabels haverage
  exact ⟨terminal, hmass⟩

end GameTheory
