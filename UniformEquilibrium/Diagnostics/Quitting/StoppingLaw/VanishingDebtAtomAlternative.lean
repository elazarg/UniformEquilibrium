/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.StoppingLaw.DebtSlopeAtomAlternative
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

/-- Forget the endpoint-debt estimate from the strengthened atom alternative.
The `Never` pure-time response collapses to the prescribed atom branch; a
finite pure stopping time remains a rectangle atom. -/
theorem hasDebtSlopeAtomAlternative_of_hasVanishingDebtAtomAlternative
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (mover observer : ι)
    (target : (quittingGame reward).BehaviorStrategy mover)
    (charge error : ℝ)
    (h : HasQuittingStoppingLawVanishingDebtAtomAlternative reward profile
      mover observer target charge error) :
    HasQuittingStoppingLawDebtSlopeAtomAlternative reward profile mover
      observer target charge := by
  rcases h with hprescribed | ⟨quitTime, terminal, hatom, _hdebt⟩
  · exact Or.inl hprescribed
  · right
    cases quitTime with
    | none =>
        exact Or.inl ⟨terminal,
          by simpa only [Function.update_eq_self] using hatom⟩
    | some stop =>
        exact Or.inr ⟨stop, terminal,
          by simpa only [Function.update_eq_self] using hatom⟩

/-- One pure-time response used at both the literal source and the complete
mover-reset endpoint.  The endpoint gain and the difference between endpoint
and source gains retain the full endpoint debt rise up to the response error.
Only the positive part of the source gain is controlled by source debt. -/
structure QuittingStoppingLawCommonResponseWitness
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (mover observer : ι)
    (target : (quittingGame reward).BehaviorStrategy mover)
    (charge error : ℝ) where
  quitTime : Option ℕ
  endpointDebt_le :
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (Function.update (Function.update profile mover target) observer
            (quittingPureTimeBehaviorStrategy reward observer quitTime)))
        observer ≤ error
  endpointGain_lower :
    quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward profile) observer +
        charge - error ≤
      quittingTerminalPayoff reward
          (Function.update (Function.update profile mover target) observer
            (quittingPureTimeBehaviorStrategy reward observer quitTime)) observer -
        quittingTerminalPayoff reward
          (Function.update profile mover target) observer
  gainDifference_lower : charge - error ≤
    (quittingTerminalPayoff reward
          (Function.update (Function.update profile mover target) observer
            (quittingPureTimeBehaviorStrategy reward observer quitTime)) observer -
        quittingTerminalPayoff reward
          (Function.update profile mover target) observer) -
      (quittingTerminalPayoff reward
          (Function.update profile observer
            (quittingPureTimeBehaviorStrategy reward observer quitTime)) observer -
        quittingTerminalPayoff reward profile observer)
  sourcePositiveGain_le :
    max 0
        (quittingTerminalPayoff reward
            (Function.update profile observer
              (quittingPureTimeBehaviorStrategy reward observer quitTime)) observer -
          quittingTerminalPayoff reward profile observer) ≤
      quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward profile) observer

namespace QuittingStoppingLawCommonResponseWitness

/-- The endpoint gain of a common response is carried by one absorbing
terminal atom.  This is the direct target-edge atom, before any strategic
orientation or reached-row localization. -/
theorem exists_endpointGainAtom
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {profile : (quittingGame reward).BehaviorProfile}
    {mover observer : ι}
    {target : (quittingGame reward).BehaviorStrategy mover}
    {charge error : ℝ}
    (witness : QuittingStoppingLawCommonResponseWitness reward profile mover
      observer target charge error)
    (hpositive : 0 <
      quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward profile) observer +
        charge - error) :
    ∃ terminal : {S : Finset ι // S.Nonempty},
      quittingTerminalSemanticDebt
            (quittingTerminalSemanticPair reward profile) observer +
          charge - error ≤
        (Fintype.card (QuittingTerminalOutcome ι) : ℝ) *
          quittingTerminalPayoffDifferenceAtom reward
            (Function.update (Function.update profile mover target) observer
              (quittingPureTimeBehaviorStrategy reward observer witness.quitTime))
            (Function.update profile mover target) observer (some terminal) := by
  exact exists_absorbingTerminalPayoffDifferenceAtom reward _ _ observer
    (quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward profile) observer + charge - error)
    hpositive witness.endpointGain_lower

/-- If the literal source debt of the common-response observer vanishes, only
the positive part of that response's source gain is forced to vanish.  The
signed gain need not converge to zero. -/
theorem sourcePositiveGain_tendsto_zero
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (profile : ℕ → (quittingGame reward).BehaviorProfile)
    (mover observer : ι)
    (target : ℕ → (quittingGame reward).BehaviorStrategy mover)
    (charge error : ℕ → ℝ)
    (witness : ∀ rank,
      QuittingStoppingLawCommonResponseWitness reward (profile rank) mover
        observer (target rank) (charge rank) (error rank))
    (hdebt : Tendsto (fun rank =>
      quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward (profile rank)) observer)
      atTop (nhds 0)) :
    Tendsto (fun rank =>
      max 0
        (quittingTerminalPayoff reward
            (Function.update (profile rank) observer
              (quittingPureTimeBehaviorStrategy reward observer
                (witness rank).quitTime)) observer -
          quittingTerminalPayoff reward (profile rank) observer))
      atTop (nhds 0) := by
  apply squeeze_zero
  · intro rank
    exact le_max_left 0 _
  · intro rank
    exact (witness rank).sourcePositiveGain_le
  · exact hdebt

end QuittingStoppingLawCommonResponseWitness

/-- A full-endpoint debt rise supplies one common pure-time response.  Its
endpoint gain is at least source debt plus `charge - error`, while its
endpoint-versus-source gain difference is at least `charge - error`.  No
small-source-debt hypothesis is used. -/
theorem exists_quittingStoppingLawCommonResponseWitness_of_endpointDebtRise
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (mover observer : ι)
    (target : (quittingGame reward).BehaviorStrategy mover)
    (charge error : ℝ) (herror : 0 < error)
    (hrise : charge ≤
      quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            (Function.update profile mover target)) observer -
        quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward profile) observer) :
    Nonempty (QuittingStoppingLawCommonResponseWitness reward profile mover
      observer target charge error) := by
  let endpoint := Function.update profile mover target
  obtain ⟨deviation, hdeviation⟩ :=
    exists_quittingContinuation_deviation_ge_sub reward endpoint observer
      (half_pos herror)
  obtain ⟨quitTime, hquitTime⟩ :=
    exists_quittingPureTimeBehaviorStrategy_terminalPayoff_ge_sub
      reward endpoint observer deviation (half_pos herror)
  let pureResponse :=
    quittingPureTimeBehaviorStrategy reward observer quitTime
  let endpointResponse := Function.update endpoint observer pureResponse
  let sourceResponse := Function.update profile observer pureResponse
  have hpayoff : quittingContinuationBestResponseValue reward endpoint observer -
      error ≤ quittingTerminalPayoff reward endpointResponse observer := by
    dsimp only [endpointResponse, pureResponse]
    linarith
  have hendpointDebt : quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward endpointResponse) observer ≤ error := by
    change quittingContinuationBestResponseValue reward endpointResponse observer -
        quittingTerminalPayoff reward endpointResponse observer ≤ error
    rw [quittingContinuationBestResponseValue_update_self]
    linarith
  have hsourceDebtNonneg : 0 ≤ quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward sourceResponse) observer := by
    simpa only [quittingTerminalSemanticDebt, quittingTerminalSemanticPair,
      quittingTerminalDeviationDebt] using
      quittingTerminalDeviationDebt_nonneg reward sourceResponse observer
  have hsourceCap :=
    quittingTerminalPayoff_update_le_continuationBestResponseValue
      reward profile observer (profile observer)
  rw [Function.update_eq_self] at hsourceCap
  have hendpointGain : quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward profile) observer +
      charge - error ≤
        quittingTerminalPayoff reward endpointResponse observer -
          quittingTerminalPayoff reward endpoint observer := by
    change (quittingContinuationBestResponseValue reward profile observer -
        quittingTerminalPayoff reward profile observer) + charge - error ≤
      quittingTerminalPayoff reward endpointResponse observer -
        quittingTerminalPayoff reward endpoint observer
    change charge ≤
      (quittingContinuationBestResponseValue reward endpoint observer -
          quittingTerminalPayoff reward endpoint observer) -
        (quittingContinuationBestResponseValue reward profile observer -
          quittingTerminalPayoff reward profile observer) at hrise
    linarith
  have hgainDifference : charge - error ≤
      (quittingTerminalPayoff reward endpointResponse observer -
          quittingTerminalPayoff reward endpoint observer) -
        (quittingTerminalPayoff reward sourceResponse observer -
          quittingTerminalPayoff reward profile observer) := by
    change charge ≤
      (quittingContinuationBestResponseValue reward endpoint observer -
          quittingTerminalPayoff reward endpoint observer) -
        (quittingContinuationBestResponseValue reward profile observer -
          quittingTerminalPayoff reward profile observer) at hrise
    change 0 ≤ quittingContinuationBestResponseValue reward sourceResponse observer -
      quittingTerminalPayoff reward sourceResponse observer at hsourceDebtNonneg
    rw [quittingContinuationBestResponseValue_update_self] at hsourceDebtNonneg
    linarith
  have hsourceGain :=
    quittingTerminalPayoff_update_le_continuationBestResponseValue
      reward profile observer pureResponse
  have hsourceDebt : 0 ≤ quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward profile) observer := by
    simpa only [quittingTerminalSemanticDebt, quittingTerminalSemanticPair,
      quittingTerminalDeviationDebt] using
      quittingTerminalDeviationDebt_nonneg reward profile observer
  have hsourcePositive : max 0
      (quittingTerminalPayoff reward sourceResponse observer -
        quittingTerminalPayoff reward profile observer) ≤
      quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward profile) observer := by
    apply max_le hsourceDebt
    change quittingTerminalPayoff reward sourceResponse observer -
        quittingTerminalPayoff reward profile observer ≤
      quittingContinuationBestResponseValue reward profile observer -
        quittingTerminalPayoff reward profile observer
    exact sub_le_sub_right hsourceGain _
  refine ⟨{
    quitTime := quitTime
    endpointDebt_le := ?_
    endpointGain_lower := ?_
    gainDifference_lower := ?_
    sourcePositiveGain_le := ?_ }⟩
  · simpa only [endpoint, endpointResponse, pureResponse] using hendpointDebt
  · simpa only [endpoint, endpointResponse, pureResponse] using hendpointGain
  · simpa only [endpoint, endpointResponse, sourceResponse, pureResponse] using
      hgainDifference
  · simpa only [sourceResponse, pureResponse] using hsourcePositive

/-- With response error at most one eighth of the endpoint rise, the
common-response square exports the existing vanishing-debt atom alternative
at charge `7 * charge / 8`.  The source debt cancels from the rectangle
estimate; it is not assumed small or zero. -/
theorem hasVanishingDebtAtomAlternative_of_endpointDebtRise
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (mover observer : ι)
    (target : (quittingGame reward).BehaviorStrategy mover)
    (charge error : ℝ) (hcharge : 0 < charge) (herror : 0 < error)
    (herrorLe : error ≤ charge / 8)
    (hrise : charge ≤
      quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            (Function.update profile mover target)) observer -
        quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward profile) observer) :
    HasQuittingStoppingLawVanishingDebtAtomAlternative reward profile mover
      observer target (7 * charge / 8) error := by
  obtain ⟨witness⟩ :=
    exists_quittingStoppingLawCommonResponseWitness_of_endpointDebtRise
      reward profile mover observer target charge error herror hrise
  let pureResponse := quittingPureTimeBehaviorStrategy reward observer
    witness.quitTime
  let endpoint := Function.update profile mover target
  let endpointResponse := Function.update endpoint observer pureResponse
  let sourceResponse := Function.update profile observer pureResponse
  have hdifference : 7 * charge / 8 ≤
      (quittingTerminalPayoff reward endpointResponse observer -
          quittingTerminalPayoff reward endpoint observer) -
        (quittingTerminalPayoff reward sourceResponse observer -
          quittingTerminalPayoff reward profile observer) := by
    have := witness.gainDifference_lower
    dsimp only [endpointResponse, endpoint, sourceResponse, pureResponse]
    linarith
  by_cases hprescribed : 7 * charge / 16 ≤
      quittingTerminalPayoff reward profile observer -
        quittingTerminalPayoff reward endpoint observer
  · left
    have hpositive : 0 < 7 * charge / 16 := by positivity
    obtain ⟨terminal, hterminal⟩ :=
      exists_absorbingTerminalPayoffDifferenceAtom reward profile endpoint
        observer (7 * charge / 16) hpositive hprescribed
    refine ⟨terminal, ?_⟩
    have hcoefficient : 7 * charge / 8 / 2 = 7 * charge / 16 := by ring
    rw [hcoefficient]
    simpa only [endpoint] using hterminal
  · right
    have hrectangle : 7 * charge / 16 ≤
        quittingTerminalPayoff reward endpointResponse observer -
          quittingTerminalPayoff reward sourceResponse observer := by
      linarith
    have hpositive : 0 < 7 * charge / 16 := by positivity
    obtain ⟨terminal, hterminal⟩ :=
      exists_absorbingTerminalPayoffDifferenceAtom reward endpointResponse
        sourceResponse observer (7 * charge / 16) hpositive hrectangle
    refine ⟨witness.quitTime, terminal, ?_, witness.endpointDebt_le⟩
    have hweaker : 7 * charge / 32 ≤
        (Fintype.card (QuittingTerminalOutcome ι) : ℝ) *
          quittingTerminalPayoffDifferenceAtom reward endpointResponse
            sourceResponse observer (some terminal) := by
      linarith
    have hweaker' : 7 * charge / 8 / 4 ≤
        (Fintype.card (QuittingTerminalOutcome ι) : ℝ) *
          quittingTerminalPayoffDifferenceAtom reward endpointResponse
            sourceResponse observer (some terminal) := by
      have hcoefficient : 7 * charge / 8 / 4 = 7 * charge / 32 := by ring
      rw [hcoefficient]
      exact hweaker
    simpa only [endpointResponse, endpoint, sourceResponse, pureResponse,
      Function.update_eq_self] using hweaker'

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
