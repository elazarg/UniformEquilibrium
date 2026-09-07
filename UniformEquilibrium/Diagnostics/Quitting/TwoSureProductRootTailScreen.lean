/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.ProductRootLimitCapSandwich
import UniformEquilibrium.Quitting.Stationary.Root

/-!
# Tail screening by two sure quitters

Two distinct sure Quit marginals make one product root absorb even after any
single player replaces their behavior.  Consequently the complete terminal
semantic pair and outcome law do not depend on what follows that root.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
/-- Unit real mass at `true` rigidifies a Boolean PMF to sure `true`. -/
theorem pmf_eq_pure_true_of_apply_true_toReal_eq_one
    (marginal : PMF Bool) (hsure : (marginal true).toReal = 1) :
    marginal = PMF.pure true := by
  apply Math.ProbabilityMassFunction.eq_of_forall_toReal_eq
  intro action
  cases action with
  | false =>
      rw [Math.PMFProduct.pmfBool_false_toReal, hsure]
      simp
  | true => simpa using hsure

/-- A product root with two distinct sure quitters screens arbitrary terminal
semantic tails, including unrestricted behavioral deviation caps. -/
theorem quittingTerminalSemanticPrefix_congr_of_twoSureQuitters
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) {first second : ι} (hne : first ≠ second)
    (hfirst : (root first true).toReal = 1)
    (hsecond : (root second true).toReal = 1)
    (left right : QuittingTerminalSemanticPair ι) :
    quittingTerminalSemanticPrefix reward root left =
      quittingTerminalSemanticPrefix reward root right := by
  have hfirstPure : root first = PMF.pure true :=
    pmf_eq_pure_true_of_apply_true_toReal_eq_one (root first) hfirst
  have hsecondPure : root second = PMF.pure true :=
    pmf_eq_pure_true_of_apply_true_toReal_eq_one (root second) hsecond
  apply Prod.ext
  · funext who
    exact quittingRootExpectedPayoff_eq_of_hasSureQuitter reward root
      ⟨first, hfirstPure⟩ left.1 right.1 who
  · funext who
    unfold quittingTerminalSemanticPrefix
    dsimp only
    congr 1
    · exact quittingRootQuitPayoff_continuation_invariant
        reward left.1 right.1 root who
    · unfold quittingRootContinuePayoff
      apply quittingRootExpectedPayoff_eq_of_hasSureQuitter
      by_cases hwho : who = first
      · exact ⟨second, by
          rw [Function.update_of_ne (Ne.symm (hwho ▸ hne))]
          exact hsecondPure⟩
      · exact ⟨first, by
          rw [Function.update_of_ne (Ne.symm hwho)]
          exact hfirstPure⟩

/-- Stationary repetition and root-then-Never have the same terminal semantic
pair when two distinct marginals quit surely at the shared root. -/
theorem quittingTerminalSemanticPair_stationary_eq_oneDateThenNever_of_twoSureQuitters
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) {first second : ι} (hne : first ≠ second)
    (hfirst : (root first true).toReal = 1)
    (hsecond : (root second true).toReal = 1) :
    quittingTerminalSemanticPair reward (quittingStationaryProfile reward root) =
      quittingTerminalSemanticPair reward
        (quittingOneDateThenNeverProfile reward root) := by
  calc
    quittingTerminalSemanticPair reward (quittingStationaryProfile reward root) =
        quittingTerminalSemanticPair reward
          (quittingRootThenContinuationProfile reward root
            (quittingStationaryProfile reward root)) := by
      rw [quittingRootThenContinuationProfile_stationary]
    _ = quittingTerminalSemanticPrefix reward root
        (quittingTerminalSemanticPair reward
          (quittingStationaryProfile reward root)) :=
      quittingTerminalSemanticPair_rootThenContinuation reward root _
    _ = quittingTerminalSemanticPrefix reward root
        (quittingTerminalSemanticPair reward
          (quittingAlwaysContinueProfile reward)) :=
      quittingTerminalSemanticPrefix_congr_of_twoSureQuitters
        reward root hne hfirst hsecond _ _
    _ = quittingTerminalSemanticPair reward
        (quittingOneDateThenNeverProfile reward root) := by
      exact (quittingTerminalSemanticPair_rootThenContinuation reward root
        (quittingAlwaysContinueProfile reward)).symm

/-- Stationary repetition and root-then-Never also have the same complete
terminal outcome law when the shared root has a sure quitter. -/
theorem quittingTerminalOutcomeMass_stationary_eq_oneDateThenNever_of_sureQuitter
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) {quitter : ι}
    (hsure : (root quitter true).toReal = 1) :
    quittingTerminalOutcomeMass reward (quittingStationaryProfile reward root) =
      quittingTerminalOutcomeMass reward
        (quittingOneDateThenNeverProfile reward root) := by
  have hpure : root quitter = PMF.pure true :=
    pmf_eq_pure_true_of_apply_true_toReal_eq_one (root quitter) hsure
  have hcontinue : quittingStationaryContinueMass root = 0 :=
    quittingStationaryContinueMass_of_sureQuitter hpure
  funext outcome
  change quittingTerminalOutcomeMass reward
      (quittingStationaryProfile reward root) outcome =
    quittingTerminalOutcomeMass reward
      (quittingRootThenContinuationProfile reward root
        (quittingAlwaysContinueProfile reward)) outcome
  have hstationary := quittingTerminalOutcomeMass_rootThenContinuation
    reward root (quittingStationaryProfile reward root) outcome
  rw [quittingRootThenContinuationProfile_stationary] at hstationary
  have honeDate := quittingTerminalOutcomeMass_rootThenContinuation
    reward root (quittingAlwaysContinueProfile reward) outcome
  rw [hstationary, honeDate]
  cases outcome <;> simp [hcontinue]

/-- Two sure quitters turn exact root Nash against an actual continuation
payoff into complete unrestricted terminal Nash of the literal prefix. -/
theorem isZeroAsymptoticNash_rootThenContinuation_of_twoSureQuitters
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool)
    (continuation : (quittingGame reward).BehaviorProfile)
    {first second : ι} (hne : first ≠ second)
    (hfirst : (root first true).toReal = 1)
    (hsecond : (root second true).toReal = 1)
    (hnash : IsεQuittingRootNash reward
      (fun who ↦ quittingTerminalPayoff reward continuation who) 0 root) :
    (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) 0
      (quittingRootThenContinuationProfile reward root continuation) := by
  let tail : Payoff ι :=
    fun who ↦ quittingTerminalPayoff reward continuation who
  have hpair : quittingTerminalSemanticPair reward
        (quittingRootThenContinuationProfile reward root continuation) =
      (quittingRootSuccessorPayoff reward tail root,
        quittingRootSuccessorPayoff reward tail root) := by
    rw [quittingTerminalSemanticPair_rootThenContinuation]
    calc
      quittingTerminalSemanticPrefix reward root
          (quittingTerminalSemanticPair reward continuation) =
          quittingTerminalSemanticPrefix reward root (tail, tail) :=
        quittingTerminalSemanticPrefix_congr_of_twoSureQuitters
          reward root hne hfirst hsecond _ _
      _ = _ := quittingTerminalSemanticPrefix_diagonal_eq_of_isZeroNash
        reward tail root hnash
  intro who deviation
  have hbound := quittingTerminalPayoff_update_sub_le_terminalSemanticDebt
    reward (quittingRootThenContinuationProfile reward root continuation)
      who deviation
  have hzero : quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward
        (quittingRootThenContinuationProfile reward root continuation)) who = 0 := by
    rw [hpair]
    simp [quittingTerminalSemanticDebt]
  rw [hzero] at hbound
  linarith

end GameTheory
