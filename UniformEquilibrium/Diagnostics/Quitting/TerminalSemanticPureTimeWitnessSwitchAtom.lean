/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.Optimization.SupremumTwoResetWitnessSwitch
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPositiveSlopeRectangle
import UniformEquilibrium.Quitting.Cycles.BehaviorPureTimeExtremality

/-!
# Pure-time atoms from an oriented best-response witness switch

A large two-reset curvature of the behavioral best-response envelope need not
come from curvature of one fixed deviation.  The generic supremum theorem
localizes the excess to a witness selected at one corner which is suboptimal at
another literal corner.

For quitting games, pure-time extremality lets both corner witnesses be chosen
as deterministic quit times (including `Never`).  The two times form a literal
four-profile payoff rectangle between the selected source and receiving
corner.  A positive rectangle is then carried by one absorbing terminal atom.

This is a corner-preserving adapter.  It does not identify the two reset
corners with consecutive Bellman states and does not assert that the receiving
corner is reachable from the source in play chronology.
-/

noncomputable section

namespace GameTheory

open Set
open Math.Optimization

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Terminal payoff from quitting at one deterministic time, or never, against
one literal opponent profile. -/
def quittingPureTimeDeviationPayoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (observer : ι) (quitTime : Option ℕ) : ℝ :=
  quittingTerminalPayoff reward
    (Function.update profile observer
      (quittingPureTimeBehaviorStrategy reward observer quitTime)) observer

/-- The all-behavior best-response envelope is exactly the supremum over pure
quit times and `Never`. -/
theorem quittingContinuationBestResponseValue_eq_sSup_pureTimeDeviationPayoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (observer : ι) :
    quittingContinuationBestResponseValue reward profile observer =
      sSup (Set.range
        (quittingPureTimeDeviationPayoff reward profile observer)) := by
  unfold quittingContinuationBestResponseValue
  simpa only [quittingPureTimeDeviationPayoff] using
    sSup_range_quittingTerminalPayoff_update_eq_pureTime
      reward profile observer

/-- Pure-time payoff values are bounded above by the behavioral best-response
envelope. -/
theorem bddAbove_range_quittingPureTimeDeviationPayoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (observer : ι) :
    BddAbove (Set.range
      (quittingPureTimeDeviationPayoff reward profile observer)) := by
  refine ⟨quittingContinuationBestResponseValue reward profile observer, ?_⟩
  rintro value ⟨quitTime, rfl⟩
  exact quittingTerminalPayoff_update_le_continuationBestResponseValue
    reward profile observer
      (quittingPureTimeBehaviorStrategy reward observer quitTime)

/-- The behavioral best-response envelope can be approached directly by a
pure deterministic quit time or `Never`. -/
theorem exists_pureTimeDeviationPayoff_ge_continuationBestResponseValue_sub
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (observer : ι)
    {eta : ℝ} (heta : 0 < eta) :
    ∃ quitTime : Option ℕ,
      quittingContinuationBestResponseValue reward profile observer - eta ≤
        quittingPureTimeDeviationPayoff reward profile observer quitTime := by
  obtain ⟨deviation, hdeviation⟩ :=
    exists_quittingContinuation_deviation_ge_sub reward profile observer
      (half_pos heta)
  obtain ⟨quitTime, hquitTime⟩ :=
    exists_quittingPureTimeBehaviorStrategy_terminalPayoff_ge_sub
      reward profile observer deviation (half_pos heta)
  refine ⟨quitTime, ?_⟩
  unfold quittingPureTimeDeviationPayoff
  linarith

/-- A corner-preserving pure-time witness switch.  `sourceTime` is
`eta`-optimal at `source`, while `receivingTime` is `eta`-optimal at
`receiving`.  Their oriented four-profile rectangle carries both a positive
payoff lower bound and one absorbing terminal atom with the same lower bound
up to the finite outcome-cardinality factor. -/
def HasQuittingPureTimeWitnessSwitchRectangle
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source receiving : (quittingGame reward).BehaviorProfile)
    (observer : ι) (charge eta : ℝ) : Prop :=
  ∃ sourceTime receivingTime : Option ℕ,
    ∃ terminal : {S : Finset ι // S.Nonempty},
      quittingContinuationBestResponseValue reward source observer - eta ≤
          quittingPureTimeDeviationPayoff reward source observer sourceTime ∧
        quittingContinuationBestResponseValue reward receiving observer - eta ≤
          quittingPureTimeDeviationPayoff reward receiving observer
            receivingTime ∧
        charge ≤
          quittingPureTimeDeviationPayoff reward receiving observer
              receivingTime -
            quittingPureTimeDeviationPayoff reward receiving observer
              sourceTime -
            quittingPureTimeDeviationPayoff reward source observer
              receivingTime +
            quittingPureTimeDeviationPayoff reward source observer sourceTime ∧
        charge ≤ (Fintype.card (QuittingTerminalOutcome ι) : ℝ) *
          quittingTerminalPayoffRectangleAtom reward
            (Function.update source observer
              (quittingPureTimeBehaviorStrategy reward observer sourceTime))
            (Function.update source observer
              (quittingPureTimeBehaviorStrategy reward observer receivingTime))
            (Function.update receiving observer
              (quittingPureTimeBehaviorStrategy reward observer sourceTime))
            (Function.update receiving observer
              (quittingPureTimeBehaviorStrategy reward observer receivingTime))
            observer (some terminal)

private theorem exists_pureTimeWitnessSwitchRectangle_of_regret
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source receiving : (quittingGame reward).BehaviorProfile)
    (observer : ι) (charge eta : ℝ)
    (hcharge : 0 < charge) (heta : 0 < eta)
    (sourceTime : Option ℕ)
    (hsource :
      quittingContinuationBestResponseValue reward source observer - eta ≤
        quittingPureTimeDeviationPayoff reward source observer sourceTime)
    (hregret : charge + 2 * eta ≤
      quittingContinuationBestResponseValue reward receiving observer -
        quittingPureTimeDeviationPayoff reward receiving observer sourceTime) :
    HasQuittingPureTimeWitnessSwitchRectangle reward source receiving observer
      charge eta := by
  obtain ⟨receivingTime, hreceiving⟩ :=
    exists_pureTimeDeviationPayoff_ge_continuationBestResponseValue_sub
      reward receiving observer heta
  have hsourceUpper :
      quittingPureTimeDeviationPayoff reward source observer receivingTime ≤
        quittingContinuationBestResponseValue reward source observer := by
    exact quittingTerminalPayoff_update_le_continuationBestResponseValue
      reward source observer
        (quittingPureTimeBehaviorStrategy reward observer receivingTime)
  have hrectangle : charge ≤
      quittingPureTimeDeviationPayoff reward receiving observer receivingTime -
        quittingPureTimeDeviationPayoff reward receiving observer sourceTime -
        quittingPureTimeDeviationPayoff reward source observer receivingTime +
        quittingPureTimeDeviationPayoff reward source observer sourceTime := by
    linarith
  let x00 := Function.update source observer
    (quittingPureTimeBehaviorStrategy reward observer sourceTime)
  let x01 := Function.update source observer
    (quittingPureTimeBehaviorStrategy reward observer receivingTime)
  let x10 := Function.update receiving observer
    (quittingPureTimeBehaviorStrategy reward observer sourceTime)
  let x11 := Function.update receiving observer
    (quittingPureTimeBehaviorStrategy reward observer receivingTime)
  have hrectangle' : charge ≤
      quittingTerminalPayoff reward x11 observer -
        quittingTerminalPayoff reward x10 observer -
        quittingTerminalPayoff reward x01 observer +
        quittingTerminalPayoff reward x00 observer := by
    simpa only [x00, x01, x10, x11, quittingPureTimeDeviationPayoff] using
      hrectangle
  obtain ⟨terminal, hatom⟩ :=
    exists_absorbingTerminalPayoffRectangleAtom reward x00 x01 x10 x11
      observer charge hcharge hrectangle'
  exact ⟨sourceTime, receivingTime, terminal, hsource, hreceiving,
    hrectangle, by simpa only [x00, x01, x10, x11] using hatom⟩

/-- Positive upper-to-base envelope curvature yields a pure-time switch from
the upper corner to the literal base corner. -/
theorem exists_pureTimeWitnessSwitchRectangle_of_upperToBase
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (x00 x10 x01 x11 : (quittingGame reward).BehaviorProfile)
    (observer : ι) (q charge eta : ℝ)
    (hcharge : 0 < charge) (heta : 0 < eta)
    (hface : ∀ quitTime : Option ℕ,
      |quittingPureTimeDeviationPayoff reward x11 observer quitTime -
          quittingPureTimeDeviationPayoff reward x10 observer quitTime -
          quittingPureTimeDeviationPayoff reward x01 observer quitTime +
          quittingPureTimeDeviationPayoff reward x00 observer quitTime| ≤ q)
    (hcurvature : charge + q + 3 * eta ≤
      quittingContinuationBestResponseValue reward x11 observer -
        quittingContinuationBestResponseValue reward x10 observer -
        quittingContinuationBestResponseValue reward x01 observer +
        quittingContinuationBestResponseValue reward x00 observer) :
    HasQuittingPureTimeWitnessSwitchRectangle reward x11 x00 observer
      charge eta := by
  let f00 := quittingPureTimeDeviationPayoff reward x00 observer
  let f10 := quittingPureTimeDeviationPayoff reward x10 observer
  let f01 := quittingPureTimeDeviationPayoff reward x01 observer
  let f11 := quittingPureTimeDeviationPayoff reward x11 observer
  obtain ⟨sourceTime, hsource⟩ :=
    exists_pureTimeDeviationPayoff_ge_continuationBestResponseValue_sub
      reward x11 observer heta
  have hcap00 :=
    quittingContinuationBestResponseValue_eq_sSup_pureTimeDeviationPayoff
      reward x00 observer
  have hcap10 :=
    quittingContinuationBestResponseValue_eq_sSup_pureTimeDeviationPayoff
      reward x10 observer
  have hcap01 :=
    quittingContinuationBestResponseValue_eq_sSup_pureTimeDeviationPayoff
      reward x01 observer
  have hcap11 :=
    quittingContinuationBestResponseValue_eq_sSup_pureTimeDeviationPayoff
      reward x11 observer
  have hupper : sSup (Set.range f11) - eta ≤ f11 sourceTime := by
    rw [← hcap11]
    exact hsource
  have hregretRaw := upperToBase_regret_ge_supMixedDifference_sub
    f00 f10 f01 f11
    (bddAbove_range_quittingPureTimeDeviationPayoff reward x10 observer)
    (bddAbove_range_quittingPureTimeDeviationPayoff reward x01 observer)
    q eta sourceTime hface hupper
  have hregret :
      (quittingContinuationBestResponseValue reward x11 observer -
          quittingContinuationBestResponseValue reward x10 observer -
          quittingContinuationBestResponseValue reward x01 observer +
          quittingContinuationBestResponseValue reward x00 observer) -
            (q + eta) ≤
        quittingContinuationBestResponseValue reward x00 observer -
          quittingPureTimeDeviationPayoff reward x00 observer sourceTime := by
    simpa only [supMixedDifference, baseRegret, f00, f10, f01, f11,
      ← hcap00, ← hcap10, ← hcap01, ← hcap11] using hregretRaw
  apply exists_pureTimeWitnessSwitchRectangle_of_regret reward x11 x00
    observer charge eta hcharge heta sourceTime hsource
  linarith

/-- Negative envelope curvature yields a pure-time switch from side `10` to
side `01`, retaining both literal side profiles. -/
theorem exists_pureTimeWitnessSwitchRectangle_of_sideOneToSideTwo
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (x00 x10 x01 x11 : (quittingGame reward).BehaviorProfile)
    (observer : ι) (q charge eta : ℝ)
    (hcharge : 0 < charge) (heta : 0 < eta)
    (hface : ∀ quitTime : Option ℕ,
      |quittingPureTimeDeviationPayoff reward x11 observer quitTime -
          quittingPureTimeDeviationPayoff reward x10 observer quitTime -
          quittingPureTimeDeviationPayoff reward x01 observer quitTime +
          quittingPureTimeDeviationPayoff reward x00 observer quitTime| ≤ q)
    (hcurvature : charge + q + 3 * eta ≤
      -(quittingContinuationBestResponseValue reward x11 observer -
        quittingContinuationBestResponseValue reward x10 observer -
        quittingContinuationBestResponseValue reward x01 observer +
        quittingContinuationBestResponseValue reward x00 observer)) :
    HasQuittingPureTimeWitnessSwitchRectangle reward x10 x01 observer
      charge eta := by
  let f00 := quittingPureTimeDeviationPayoff reward x00 observer
  let f10 := quittingPureTimeDeviationPayoff reward x10 observer
  let f01 := quittingPureTimeDeviationPayoff reward x01 observer
  let f11 := quittingPureTimeDeviationPayoff reward x11 observer
  obtain ⟨sourceTime, hsource⟩ :=
    exists_pureTimeDeviationPayoff_ge_continuationBestResponseValue_sub
      reward x10 observer heta
  have hcap00 :=
    quittingContinuationBestResponseValue_eq_sSup_pureTimeDeviationPayoff
      reward x00 observer
  have hcap10 :=
    quittingContinuationBestResponseValue_eq_sSup_pureTimeDeviationPayoff
      reward x10 observer
  have hcap01 :=
    quittingContinuationBestResponseValue_eq_sSup_pureTimeDeviationPayoff
      reward x01 observer
  have hcap11 :=
    quittingContinuationBestResponseValue_eq_sSup_pureTimeDeviationPayoff
      reward x11 observer
  have hside : sSup (Set.range f10) - eta ≤ f10 sourceTime := by
    rw [← hcap10]
    exact hsource
  have hregretRaw := sideOneToSideTwo_regret_ge_neg_supMixedDifference_sub
    f00 f10 f01 f11
    (bddAbove_range_quittingPureTimeDeviationPayoff reward x00 observer)
    (bddAbove_range_quittingPureTimeDeviationPayoff reward x11 observer)
    q eta sourceTime hface hside
  have hregret :
      -(quittingContinuationBestResponseValue reward x11 observer -
          quittingContinuationBestResponseValue reward x10 observer -
          quittingContinuationBestResponseValue reward x01 observer +
          quittingContinuationBestResponseValue reward x00 observer) -
            (q + eta) ≤
        quittingContinuationBestResponseValue reward x01 observer -
          quittingPureTimeDeviationPayoff reward x01 observer sourceTime := by
    simpa only [supMixedDifference, oppositeRegret₂, f00, f10, f01, f11,
      ← hcap00, ← hcap10, ← hcap01, ← hcap11] using hregretRaw
  apply exists_pureTimeWitnessSwitchRectangle_of_regret reward x10 x01
    observer charge eta hcharge heta sourceTime hsource
  linarith

/-- A signed envelope square larger than the fixed-witness square budget
therefore yields one of the two literal oriented pure-time rectangle atoms. -/
theorem exists_pureTimeWitnessSwitchRectangle_of_abs_envelopeCurvature
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (x00 x10 x01 x11 : (quittingGame reward).BehaviorProfile)
    (observer : ι) (q charge eta : ℝ)
    (hcharge : 0 < charge) (heta : 0 < eta)
    (hface : ∀ quitTime : Option ℕ,
      |quittingPureTimeDeviationPayoff reward x11 observer quitTime -
          quittingPureTimeDeviationPayoff reward x10 observer quitTime -
          quittingPureTimeDeviationPayoff reward x01 observer quitTime +
          quittingPureTimeDeviationPayoff reward x00 observer quitTime| ≤ q)
    (hcurvature : charge + q + 3 * eta ≤
      |quittingContinuationBestResponseValue reward x11 observer -
        quittingContinuationBestResponseValue reward x10 observer -
        quittingContinuationBestResponseValue reward x01 observer +
        quittingContinuationBestResponseValue reward x00 observer|) :
    HasQuittingPureTimeWitnessSwitchRectangle reward x11 x00 observer
        charge eta ∨
      HasQuittingPureTimeWitnessSwitchRectangle reward x10 x01 observer
        charge eta := by
  let curvature :=
    quittingContinuationBestResponseValue reward x11 observer -
      quittingContinuationBestResponseValue reward x10 observer -
      quittingContinuationBestResponseValue reward x01 observer +
      quittingContinuationBestResponseValue reward x00 observer
  by_cases hnonneg : 0 ≤ curvature
  · left
    apply exists_pureTimeWitnessSwitchRectangle_of_upperToBase reward
      x00 x10 x01 x11 observer q charge eta hcharge heta hface
    simpa only [curvature, abs_of_nonneg hnonneg] using hcurvature
  · right
    apply exists_pureTimeWitnessSwitchRectangle_of_sideOneToSideTwo reward
      x00 x10 x01 x11 observer q charge eta hcharge heta hface
    have hnegative : curvature < 0 := lt_of_not_ge hnonneg
    simpa only [curvature, abs_of_neg hnegative] using hcurvature

end GameTheory
