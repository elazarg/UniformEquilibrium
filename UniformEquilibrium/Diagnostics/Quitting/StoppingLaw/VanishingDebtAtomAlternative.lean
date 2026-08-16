/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPositiveSlopeMarkedRowProvenance

/-!
# Vanishing-debt atom alternatives for a positive stopping-law slope

A positive stopping-law debt slope can be decoded with an arbitrary small
positive approximation budget.  Either it produces a prescribed terminal
payoff atom, or one pure-time response produces a rectangle atom while its
own endpoint debt is bounded by that budget.

The decoder and its canonical vanishing error scale assume no counterexample
regime, selected frontier, or asymptotic packet.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The vanishing error budget used by the sequence decoder. -/
def quittingStoppingLawAtomDecoderError (charge : ℝ) (rank : ℕ) : ℝ :=
  (charge / 8) / (rank + 1 : ℝ)

theorem quittingStoppingLawAtomDecoderError_pos {charge : ℝ}
    (hcharge : 0 < charge) (rank : ℕ) :
    0 < quittingStoppingLawAtomDecoderError charge rank := by
  unfold quittingStoppingLawAtomDecoderError
  positivity

theorem quittingStoppingLawAtomDecoderError_le {charge : ℝ}
    (hcharge : 0 ≤ charge) (rank : ℕ) :
    quittingStoppingLawAtomDecoderError charge rank ≤ charge / 8 := by
  unfold quittingStoppingLawAtomDecoderError
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < rank + 1)).2
  have hrank : (0 : ℝ) ≤ rank := by positivity
  nlinarith

theorem tendsto_quittingStoppingLawAtomDecoderError (charge : ℝ) :
    Tendsto (quittingStoppingLawAtomDecoderError charge) atTop (nhds 0) := by
  have hbase := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  have hmul : Tendsto
      (fun rank : ℕ ↦ (charge / 8) * (1 / ((rank : ℝ) + 1)))
      atTop (nhds 0) :=
    by
      simpa using
        ((tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ charge / 8)
          atTop (nhds (charge / 8))).mul hbase)
  convert hmul using 1
  funext rank
  unfold quittingStoppingLawAtomDecoderError
  ring

/-- One rank of the strengthened decoder.  In the cap branch, the same
pure-time response carries both the fixed rectangle atom and a quantitative
upper bound on its own endpoint debt. -/
def HasQuittingStoppingLawVanishingDebtAtomAlternative
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (mover observer : ι)
    (target : (quittingGame reward).BehaviorStrategy mover)
    (charge error : ℝ) : Prop :=
  (∃ terminal : {S : Finset ι // S.Nonempty},
    charge / 2 ≤
      (Fintype.card (QuittingTerminalOutcome ι) : ℝ) *
        quittingTerminalPayoffDifferenceAtom reward profile
          (Function.update profile mover target) observer (some terminal)) ∨
  ∃ quitTime : Option ℕ, ∃ terminal : {S : Finset ι // S.Nonempty},
    charge / 4 ≤
      (Fintype.card (QuittingTerminalOutcome ι) : ℝ) *
        quittingTerminalPayoffDifferenceAtom reward
          (Function.update (Function.update profile mover target) observer
            (quittingPureTimeBehaviorStrategy reward observer quitTime))
          (Function.update (Function.update profile mover (profile mover)) observer
            (quittingPureTimeBehaviorStrategy reward observer quitTime))
          observer (some terminal) ∧
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (Function.update (Function.update profile mover target) observer
            (quittingPureTimeBehaviorStrategy reward observer quitTime))) observer ≤
      error

/-- The positive-slope atom decoder with an arbitrary sufficiently small
positive approximation error. -/
theorem exists_prescribedAtom_or_pureTimeRectangleAtom_with_debtBound
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (mover observer : ι)
    (target : (quittingGame reward).BehaviorStrategy mover)
    (lambda charge error : ℝ) (hlambda0 : 0 < lambda)
    (hlambda1 : lambda ≤ 1) (hcharge : 0 < charge)
    (herror : 0 < error) (herrorLe : error ≤ charge / 8)
    (hslope : lambda * charge ≤
      quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            (Function.update profile mover
              (quittingStoppingLawMixtureBehaviorStrategy reward mover
                (profile mover) target lambda hlambda0.le hlambda1))) observer -
        quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward profile) observer) :
    HasQuittingStoppingLawVanishingDebtAtomAlternative reward profile mover
      observer target charge error := by
  let endpoint := Function.update profile mover target
  let mixed := Function.update profile mover
    (quittingStoppingLawMixtureBehaviorStrategy reward mover
      (profile mover) target lambda hlambda0.le hlambda1)
  let sourcePair := quittingTerminalSemanticPair reward profile
  let endpointPair := quittingTerminalSemanticPair reward endpoint
  let mixedPair := quittingTerminalSemanticPair reward mixed
  have hchord := quittingTerminalSemanticDebt_stoppingLawMixture_le
    reward profile mover observer (profile mover) target lambda hlambda0.le
      hlambda1
  rw [Function.update_eq_self] at hchord
  change quittingTerminalSemanticDebt mixedPair observer ≤
      (1 - lambda) * quittingTerminalSemanticDebt sourcePair observer +
        lambda * quittingTerminalSemanticDebt endpointPair observer at hchord
  have hendpointSlope : charge ≤
      quittingTerminalSemanticDebt endpointPair observer -
        quittingTerminalSemanticDebt sourcePair observer := by
    change lambda * charge ≤
      quittingTerminalSemanticDebt mixedPair observer -
        quittingTerminalSemanticDebt sourcePair observer at hslope
    have hscaled : lambda * charge ≤ lambda *
        (quittingTerminalSemanticDebt endpointPair observer -
          quittingTerminalSemanticDebt sourcePair observer) := by
      nlinarith
    nlinarith
  let sourceCap := quittingContinuationBestResponseValue reward profile observer
  let endpointCap := quittingContinuationBestResponseValue reward endpoint observer
  let sourcePayoff := quittingTerminalPayoff reward profile observer
  let endpointPayoff := quittingTerminalPayoff reward endpoint observer
  have hsplit : charge ≤
      (endpointCap - sourceCap) + (sourcePayoff - endpointPayoff) := by
    dsimp only [sourcePair, endpointPair, quittingTerminalSemanticDebt,
      quittingTerminalSemanticPair] at hendpointSlope
    dsimp only [sourceCap, endpointCap, sourcePayoff, endpointPayoff]
    linarith
  by_cases hpayoff : charge / 2 ≤ sourcePayoff - endpointPayoff
  · exact Or.inl (exists_absorbingTerminalPayoffDifferenceAtom reward profile
      endpoint observer (charge / 2) (by positivity) hpayoff)
  · right
    have hcap : charge / 2 < endpointCap - sourceCap := by linarith
    obtain ⟨deviation, hdeviation⟩ :=
      exists_quittingContinuation_deviation_ge_sub reward endpoint observer
        (half_pos herror)
    obtain ⟨quitTime, hquitTime⟩ :=
      exists_quittingPureTimeBehaviorStrategy_terminalPayoff_ge_sub
        reward endpoint observer deviation (half_pos herror)
    let pureDeviation :=
      quittingPureTimeBehaviorStrategy reward observer quitTime
    have hsourceBound :=
      quittingTerminalPayoff_update_le_continuationBestResponseValue
        reward profile observer pureDeviation
    have hpureEndpoint : endpointCap - error ≤
        quittingTerminalPayoff reward
          (Function.update endpoint observer pureDeviation) observer := by
      dsimp only [pureDeviation]
      linarith
    have hrectangle : charge / 4 ≤
        quittingTerminalPayoff reward
            (Function.update endpoint observer pureDeviation) observer -
          quittingTerminalPayoff reward
            (Function.update profile observer pureDeviation) observer := by
      dsimp only [sourceCap] at hcap hsourceBound
      linarith
    obtain ⟨terminal, hterminal⟩ :=
      exists_absorbingTerminalPayoffDifferenceAtom reward
        (Function.update endpoint observer pureDeviation)
        (Function.update profile observer pureDeviation) observer
        (charge / 4) (by positivity) hrectangle
    have hdebt : quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (Function.update endpoint observer pureDeviation)) observer ≤ error := by
      unfold quittingTerminalSemanticDebt quittingTerminalSemanticPair
      change quittingContinuationBestResponseValue reward
          (Function.update endpoint observer pureDeviation) observer -
        quittingTerminalPayoff reward
          (Function.update endpoint observer pureDeviation) observer ≤ error
      rw [quittingContinuationBestResponseValue_update_self]
      dsimp only [endpointCap] at hpureEndpoint
      linarith
    refine ⟨quitTime, terminal, ?_, ?_⟩
    · simpa only [endpoint, pureDeviation, Function.update_eq_self] using hterminal
    · simpa only [endpoint, pureDeviation] using hdebt

end GameTheory
