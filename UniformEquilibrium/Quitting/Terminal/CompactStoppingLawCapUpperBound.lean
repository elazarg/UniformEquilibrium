/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Terminal.OpponentTightTerminalSemanticRealization

/-!
# Cap bounds from arbitrary compact stopping laws

Late deterministic quitting against reconstructed compact stopping laws has a
limit even when some opponent law is proper: the singleton term is weighted by
the product of the opponents' Never masses.  Consequently, any common bound on
all finite pure quitting times bounds the unrestricted behavioral cap, up to
the same product times the negative part of the singleton reward.

The law-limit wrappers consume supplied semantic and marginal-law convergence.
They do not assert tightness, attainment, a minimum property, terminal Nash
play, or a uniform-equilibrium payoff.
-/

noncomputable section

namespace GameTheory

open Filter MeasureTheory Set StochasticGame
open _root_.Math.Probability _root_.Math.ProbabilityMassFunction
open _root_.Math.Probability.DiscreteHazard
open scoped BigOperators ENNReal Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nontrivial ι]

omit [Nontrivial ι] in
/-- Late deterministic quitting against arbitrary reconstructed compact laws.
The surviving singleton term is weighted by the product of the opponents'
Never masses; no properness hypothesis is required. -/
theorem quittingTerminalPayoff_update_finiteTime_tendsto_never_add_opponentNever_mul_singleton
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (laws : ι → CompactStoppingLaw) (who : ι) :
    Tendsto (fun time => quittingTerminalPayoff reward
        (Function.update
          (quittingCompactStoppingLawProfile reward laws) who
          (quittingPureTimeBehaviorStrategy reward who (some time))) who)
      atTop (nhds (quittingTerminalPayoff reward
          (Function.update
            (quittingCompactStoppingLawProfile reward laws) who
            (quittingPureTimeBehaviorStrategy reward who none)) who +
        quittingOpponentNeverProduct laws who *
          reward (quittingSingletonTerminal who) who)) := by
  let profile := quittingCompactStoppingLawProfile reward laws
  let roots := quittingProfileLiveRoot reward profile
  let weight := fun time =>
    quittingOpponentSurvivalWeight roots who 0 time
  let quitValue := fun time =>
    quittingFixedOpponentsQuitValue reward roots who time
  let q := quittingOpponentNeverProduct laws who
  let solo := reward (quittingSingletonTerminal who) who
  by_cases hq : q = 0
  · have hledger := tendsto_quittingLiveLedgerAccum reward roots who
    have hweight : Tendsto weight atTop (nhds 0) := by
      simpa only [weight, roots, profile, q, hq] using
        quittingOpponentSurvivalWeight_compactStoppingLawProfile_tendsto
          reward laws who
    have hbound (time : Nat) :
        |weight time * quitValue time| ≤
          weight time * quittingRewardBound reward := by
      rw [abs_mul, abs_of_nonneg
        (quittingOpponentSurvivalWeight_nonneg roots who 0 time)]
      exact mul_le_mul_of_nonneg_left
        (abs_quittingFixedOpponentsQuitValue_le_rewardBound
          reward roots who time)
        (quittingOpponentSurvivalWeight_nonneg roots who 0 time)
    have hboundZero : Tendsto
        (fun time => weight time * quittingRewardBound reward)
        atTop (nhds 0) := by
      simpa using hweight.mul_const (quittingRewardBound reward)
    have hweighted : Tendsto (fun time => weight time * quitValue time)
        atTop (nhds 0) := by
      rw [tendsto_zero_iff_abs_tendsto_zero]
      exact squeeze_zero (fun time => abs_nonneg _) hbound hboundZero
    have hsum := hledger.add hweighted
    simpa only [profile, roots, weight, quitValue, q, solo, hq, zero_mul,
      add_zero, quittingTerminalPayoff_update_pureTimeBehaviorStrategy,
      quittingRootSequencePureTimeTerminalValue_some_eq] using hsum
  · have hopponents : ∀ opponent ≠ who,
        ¬ compactStoppingLawIsProper (laws opponent) := by
      intro opponent hne hproper
      have hopponent : opponent ∈ Finset.univ.erase who := by
        simp [hne]
      have hfactor : (laws opponent).realMass
          ({⊤} : Set CompactStoppingTime) = 0 := hproper
      have hzero : q = 0 := by
        unfold q quittingOpponentNeverProduct
        exact Finset.prod_eq_zero hopponent hfactor
      exact hq hzero
    simpa only [q, solo] using
      quittingTerminalPayoff_update_finiteTime_tendsto_never_add_singleton
        reward laws who hopponents

omit [Nontrivial ι] in
/-- An arbitrary common bound for all finite deterministic quitting times
bounds the full behavioral deviation value, up to the surviving opponents'
Never product times the negative part of the singleton reward. -/
theorem quittingCompactStoppingLawProfile_cap_le_finiteBound_add_opponentNeverProduct_mul_negPart
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (laws : ι → CompactStoppingLaw) (who : ι) (finiteBound : Real)
    (hfinite : ∀ time : Nat,
      quittingTerminalPayoff reward
        (Function.update
          (quittingCompactStoppingLawProfile reward laws) who
          (quittingPureTimeBehaviorStrategy reward who
            (WithTop.some time))) who ≤ finiteBound) :
    quittingContinuationBestResponseValue reward
        (quittingCompactStoppingLawProfile reward laws) who ≤
      finiteBound + quittingOpponentNeverProduct laws who *
        max (-reward (quittingSingletonTerminal who) who) 0 := by
  let profile := quittingCompactStoppingLawProfile reward laws
  let menu := fun choice : Option Nat =>
    quittingTerminalPayoff reward
      (Function.update profile who
        (quittingPureTimeBehaviorStrategy reward who choice)) who
  let q := quittingOpponentNeverProduct laws who
  let solo := reward (quittingSingletonTerminal who) who
  have hq : 0 ≤ q := by
    unfold q quittingOpponentNeverProduct
    exact Finset.prod_nonneg fun opponent _ =>
      CompactStoppingLaw.realMass_nonneg (laws opponent) _
  have hlate : Tendsto (fun time => menu (some time)) atTop
      (nhds (menu none + q * solo)) := by
    simpa only [menu, profile, q, solo] using
      quittingTerminalPayoff_update_finiteTime_tendsto_never_add_opponentNever_mul_singleton
        reward laws who
  have hlateLe : menu none + q * solo ≤ finiteBound := by
    apply le_of_tendsto hlate
    exact Filter.Eventually.of_forall hfinite
  have hnever : menu none ≤ finiteBound + q * max (-solo) 0 := by
    have hneg : -solo ≤ max (-solo) 0 := le_max_left _ _
    have hscaled : q * (-solo) ≤ q * max (-solo) 0 :=
      mul_le_mul_of_nonneg_left hneg hq
    linarith
  have hfinite' (time : Nat) :
      menu (some time) ≤ finiteBound + q * max (-solo) 0 := by
    have hnonneg : 0 ≤ q * max (-solo) 0 :=
      mul_nonneg hq (le_max_right _ _)
    exact (hfinite time).trans (by linarith)
  have hcapSup : quittingContinuationBestResponseValue reward profile who =
      sSup (Set.range menu) := by
    unfold quittingContinuationBestResponseValue
    change _ = sSup (Set.range fun choice : Option Nat =>
      quittingTerminalPayoff reward
        (Function.update profile who
          (quittingPureTimeBehaviorStrategy reward who choice)) who)
    exact sSup_range_quittingTerminalPayoff_update_eq_pureTime
      reward profile who
  rw [hcapSup]
  apply csSup_le
  · exact ⟨menu none, ⟨none, rfl⟩⟩
  · rintro value ⟨choice, rfl⟩
    cases choice with
    | none => exact hnever
    | some time => exact hfinite' time

omit [Nontrivial ι] in
/-- The finite-time cap inherited from a semantic/stopping-law limit feeds the
arbitrary-law negative-singleton correction. -/
theorem
    quittingCompactStoppingLawProfile_cap_le_target_add_opponentNeverProduct_mul_negPart_of_lawLimit
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profiles : Nat → (quittingGame reward).BehaviorProfile)
    (target : QuittingTerminalSemanticPair ι)
    (laws : ι → CompactStoppingLaw)
    (hsemantic : Tendsto
      (fun n => quittingTerminalSemanticPair reward (profiles n))
      atTop (nhds target))
    (hlaw : ∀ player, Tendsto (fun n =>
      quittingCompactStoppingLawsOfProfile reward (profiles n) player)
      atTop (nhds (laws player))) (who : ι) :
    quittingContinuationBestResponseValue reward
        (quittingCompactStoppingLawProfile reward laws) who ≤
      target.2 who + quittingOpponentNeverProduct laws who *
        max (-reward (quittingSingletonTerminal who) who) 0 := by
  apply quittingCompactStoppingLawProfile_cap_le_finiteBound_add_opponentNeverProduct_mul_negPart
  intro time
  exact quittingTerminalPayoff_update_finiteTime_le_of_lawLimit
    reward profiles target laws hsemantic hlaw who time

namespace QuittingTerminalSemanticSelectedLawLimit

omit [Nontrivial ι] in
/-- Selected-law form of the reconstructed behavioral cap bound. -/
theorem reconstructedCap_le_add_opponentNeverProduct_mul_negPart
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {target : QuittingTerminalSemanticPair ι}
    (selected : QuittingTerminalSemanticSelectedLawLimit reward target)
    (who : ι) :
    quittingContinuationBestResponseValue reward
        (quittingCompactStoppingLawProfile reward selected.laws) who ≤
      target.2 who + quittingOpponentNeverProduct selected.laws who *
        max (-reward (quittingSingletonTerminal who) who) 0 := by
  exact
    quittingCompactStoppingLawProfile_cap_le_target_add_opponentNeverProduct_mul_negPart_of_lawLimit
      reward (fun n => selected.sourceProfile (selected.subseq n)) target
      selected.laws selected.semantic_tendsto selected.law_tendsto who

omit [Nontrivial ι] in
/-- A nonnegative singleton reward removes the arbitrary-law correction from
the reconstructed behavioral cap. -/
theorem reconstructedCap_le_of_singleton_nonneg
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {target : QuittingTerminalSemanticPair ι}
    (selected : QuittingTerminalSemanticSelectedLawLimit reward target)
    (who : ι)
    (hsingleton : 0 ≤ reward (quittingSingletonTerminal who) who) :
    quittingContinuationBestResponseValue reward
        (quittingCompactStoppingLawProfile reward selected.laws) who ≤
      target.2 who := by
  have hbound :=
    selected.reconstructedCap_le_add_opponentNeverProduct_mul_negPart who
  rw [max_eq_right (neg_nonpos.mpr hsingleton), mul_zero, add_zero] at hbound
  exact hbound

end QuittingTerminalSemanticSelectedLawLimit

end GameTheory
