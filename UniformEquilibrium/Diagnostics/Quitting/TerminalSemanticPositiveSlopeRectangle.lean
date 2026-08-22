/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.Optimization.SupremumTwoResetWitnessSwitch
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPositiveSlopeAtom
import UniformEquilibrium.Quitting.Cycles.BehaviorPureTimeExtremality

/-!
# Four-profile rectangles from positive stopping-law debt slope

A positive debt increment for an observer under another player's complete
stopping-law mixture has a literal four-profile witness.  If one approximate
best response is chosen at the mixed profile, its payoff cross-difference
between the source and full reset endpoint carries the debt increment.

There are two distinct atom statements.  The positive cross-difference
exposes one absorbing terminal atom of the full endpoint rectangle.  For a
small reset weight, approximate optimality additionally forces the
target-side unilateral edge to be profitable, so that same executable edge
exposes a (possibly different) positive payoff atom.  The theorem does not
identify these two coalitions.

The endpoint rectangle is an order-one comparison of four full corner laws.
At the actually used reset mixture, its signed terminal-law cross-effect is
exactly `lambda` times that rectangle.  This must not be confused with a
separately marked event whose corner mass may stay bounded below by a fixed
constant.
-/

noncomputable section

namespace GameTheory

open StochasticGame

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Reward-weighted atom of a four-profile terminal-law rectangle. -/
def quittingTerminalPayoffRectangleAtom
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (x00 x01 x10 x11 : (quittingGame reward).BehaviorProfile)
    (observer : ι) (outcome : QuittingTerminalOutcome ι) : ℝ :=
  (quittingTerminalOutcomeMass reward x11 outcome -
      quittingTerminalOutcomeMass reward x10 outcome -
      quittingTerminalOutcomeMass reward x01 outcome +
      quittingTerminalOutcomeMass reward x00 outcome) *
    quittingTerminalOutcomeReward reward outcome observer

omit [DecidableEq ι] in
/-- The terminal atoms sum to the payoff cross-difference of the same four
literal profiles. -/
theorem sum_quittingTerminalPayoffRectangleAtom
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (x00 x01 x10 x11 : (quittingGame reward).BehaviorProfile)
    (observer : ι) :
    (∑ outcome : QuittingTerminalOutcome ι,
        quittingTerminalPayoffRectangleAtom reward x00 x01 x10 x11
          observer outcome) =
      quittingTerminalPayoff reward x11 observer -
        quittingTerminalPayoff reward x10 observer -
        quittingTerminalPayoff reward x01 observer +
        quittingTerminalPayoff reward x00 observer := by
  simp_rw [← quittingTerminalRewardMoment_outcomeMass reward]
  unfold quittingTerminalRewardMoment quittingTerminalPayoffRectangleAtom
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro outcome _
  ring

omit [DecidableEq ι] in
/-- A positive payoff rectangle is carried by a nonempty quitting coalition;
the zero-reward `Never` atom cannot carry it. -/
theorem exists_absorbingTerminalPayoffRectangleAtom
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (x00 x01 x10 x11 : (quittingGame reward).BehaviorProfile)
    (observer : ι) (charge : ℝ) (hcharge : 0 < charge)
    (hrectangle : charge ≤
      quittingTerminalPayoff reward x11 observer -
        quittingTerminalPayoff reward x10 observer -
        quittingTerminalPayoff reward x01 observer +
        quittingTerminalPayoff reward x00 observer) :
    ∃ terminal : {S : Finset ι // S.Nonempty},
      charge ≤ (Fintype.card (QuittingTerminalOutcome ι) : ℝ) *
        quittingTerminalPayoffRectangleAtom reward x00 x01 x10 x11
          observer (some terminal) := by
  let outcomes := (Finset.univ : Finset (QuittingTerminalOutcome ι))
  obtain ⟨outcome, _houtcome, houtcomeMax⟩ :=
    Finset.exists_max_image outcomes
      (quittingTerminalPayoffRectangleAtom reward x00 x01 x10 x11 observer)
      Finset.univ_nonempty
  have hsumLe :
      (∑ other : QuittingTerminalOutcome ι,
          quittingTerminalPayoffRectangleAtom reward x00 x01 x10 x11
            observer other) ≤
        (Fintype.card (QuittingTerminalOutcome ι) : ℝ) *
          quittingTerminalPayoffRectangleAtom reward x00 x01 x10 x11
            observer outcome := by
    have hbound := outcomes.sum_le_card_nsmul
      (quittingTerminalPayoffRectangleAtom reward x00 x01 x10 x11 observer)
      (quittingTerminalPayoffRectangleAtom reward x00 x01 x10 x11 observer
        outcome)
      (fun other hother => houtcomeMax other hother)
    simpa [outcomes, nsmul_eq_mul, mul_comm] using hbound
  have houtcomeCharge : charge ≤
      (Fintype.card (QuittingTerminalOutcome ι) : ℝ) *
        quittingTerminalPayoffRectangleAtom reward x00 x01 x10 x11
          observer outcome := by
    apply hrectangle.trans
    rw [← sum_quittingTerminalPayoffRectangleAtom]
    exact hsumLe
  cases outcome with
  | none =>
      simp [quittingTerminalPayoffRectangleAtom,
        quittingTerminalOutcomeReward] at houtcomeCharge
      linarith
  | some terminal => exact ⟨terminal, houtcomeCharge⟩

/-- **Positive-slope four-profile decoder.**

Let `mixed` be a complete stopping-law mixture of `source` and `target` for
`mover`.  If `observer`'s debt rises by at least `lambda * charge`, and
`deviation` is an approximate best response at `mixed` with error at most
half that charge, then the four full endpoint profiles have a positive
payoff rectangle.

When `lambda ≤ 1/4`, approximate optimality also forces the forward
target-side edge to be profitable.  Thus this one executable edge exposes a
positive terminal payoff atom, although its coalition need not be the
rectangle coalition. -/
theorem exists_rectangleAtom_and_targetEdgeAtom_of_mixedDebtSlope
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (mover observer : ι) (hne : observer ≠ mover)
    (source target : (quittingGame reward).BehaviorStrategy mover)
    (deviation : (quittingGame reward).BehaviorStrategy observer)
    (lambda charge error : ℝ)
    (hlambda0 : 0 < lambda) (hlambdaQuarter : lambda ≤ 1 / 4)
    (hcharge : 0 < charge) (herror0 : 0 ≤ error)
    (herror : error ≤ lambda * charge / 2)
    (hslope : lambda * charge ≤
      quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            (Function.update profile mover
              (quittingStoppingLawMixtureBehaviorStrategy reward mover
                source target lambda hlambda0.le
                  (hlambdaQuarter.trans (by norm_num))))) observer -
        quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            (Function.update profile mover source)) observer)
    (hbest : quittingContinuationBestResponseValue reward
          (Function.update profile mover
            (quittingStoppingLawMixtureBehaviorStrategy reward mover
              source target lambda hlambda0.le
                (hlambdaQuarter.trans (by norm_num)))) observer ≤
        quittingTerminalPayoff reward
          (Function.update
            (Function.update profile mover
              (quittingStoppingLawMixtureBehaviorStrategy reward mover
                source target lambda hlambda0.le
                  (hlambdaQuarter.trans (by norm_num))))
            observer deviation) observer + error) :
    let x00 := Function.update profile mover source
    let x01 := Function.update profile mover target
    let x10 := Function.update x00 observer deviation
    let x11 := Function.update x01 observer deviation
    (∃ terminal : {S : Finset ι // S.Nonempty},
      charge / 2 ≤ (Fintype.card (QuittingTerminalOutcome ι) : ℝ) *
        quittingTerminalPayoffRectangleAtom reward x00 x01 x10 x11
          observer (some terminal)) ∧
    charge / 4 ≤ quittingTerminalPayoff reward x11 observer -
      quittingTerminalPayoff reward x01 observer ∧
    ∃ terminal : {S : Finset ι // S.Nonempty},
      charge / 4 ≤ (Fintype.card (QuittingTerminalOutcome ι) : ℝ) *
        quittingTerminalPayoffDifferenceAtom reward x11 x01 observer
          (some terminal) := by
  dsimp only
  let mixedStrategy := quittingStoppingLawMixtureBehaviorStrategy reward mover
    source target lambda hlambda0.le (hlambdaQuarter.trans (by norm_num))
  let mixed := Function.update profile mover mixedStrategy
  let x00 := Function.update profile mover source
  let x01 := Function.update profile mover target
  let x10 := Function.update x00 observer deviation
  let x11 := Function.update x01 observer deviation
  have hsourceAffine := quittingTerminalPayoff_stoppingLawMixture_eq
    reward profile mover observer source target lambda hlambda0.le
      (hlambdaQuarter.trans (by norm_num))
  have hdeviationAffine := quittingTerminalPayoff_stoppingLawMixture_eq
    reward (Function.update profile observer deviation) mover observer source
      target lambda hlambda0.le (hlambdaQuarter.trans (by norm_num))
  have hcommuteMixed :
      Function.update (Function.update profile observer deviation) mover
          mixedStrategy = Function.update mixed observer deviation := by
    exact Function.update_comm hne deviation mixedStrategy profile
  have hcommuteSource :
      Function.update (Function.update profile observer deviation) mover source =
        x10 := by
    exact Function.update_comm hne deviation source profile
  have hcommuteTarget :
      Function.update (Function.update profile observer deviation) mover target =
        x11 := by
    exact Function.update_comm hne deviation target profile
  change quittingTerminalPayoff reward mixed observer = _ at hsourceAffine
  change quittingTerminalPayoff reward
      (Function.update (Function.update profile observer deviation) mover
        mixedStrategy) observer = _ at hdeviationAffine
  rw [hcommuteMixed, hcommuteSource, hcommuteTarget] at hdeviationAffine
  change lambda * charge ≤
      (quittingContinuationBestResponseValue reward mixed observer -
          quittingTerminalPayoff reward mixed observer) -
        (quittingContinuationBestResponseValue reward x00 observer -
          quittingTerminalPayoff reward x00 observer) at hslope
  change quittingContinuationBestResponseValue reward mixed observer ≤
    quittingTerminalPayoff reward (Function.update mixed observer deviation)
      observer + error at hbest
  have hsourceCap :=
    quittingTerminalPayoff_update_le_continuationBestResponseValue
      reward x00 observer deviation
  change quittingTerminalPayoff reward x10 observer ≤
    quittingContinuationBestResponseValue reward x00 observer at hsourceCap
  let rectangle := quittingTerminalPayoff reward x11 observer -
    quittingTerminalPayoff reward x10 observer -
    quittingTerminalPayoff reward x01 observer +
    quittingTerminalPayoff reward x00 observer
  have hscaledRectangle : lambda * charge ≤ lambda * rectangle + error := by
    dsimp only [rectangle]
    linarith
  have hrectangle : charge / 2 ≤ rectangle := by
    have hscaled : lambda * (charge / 2) ≤ lambda * rectangle := by
      nlinarith
    exact (mul_le_mul_iff_of_pos_left hlambda0).mp hscaled
  have hrectanglePositive : 0 < charge / 2 := by positivity
  have hrectangleAtom := exists_absorbingTerminalPayoffRectangleAtom reward
    x00 x01 x10 x11 observer (charge / 2) hrectanglePositive hrectangle
  have hmixedCapLower :=
    quittingTerminalPayoff_update_le_continuationBestResponseValue
      reward mixed observer (mixed observer)
  rw [Function.update_eq_self] at hmixedCapLower
  have hmixedGain : -error ≤
      quittingTerminalPayoff reward (Function.update mixed observer deviation)
          observer - quittingTerminalPayoff reward mixed observer := by
    linarith
  let targetGain := quittingTerminalPayoff reward x11 observer -
    quittingTerminalPayoff reward x01 observer
  have htargetGain : charge / 4 ≤ targetGain := by
    dsimp only [targetGain]
    have hlambda1 : lambda ≤ 1 := hlambdaQuarter.trans (by norm_num)
    have hweight : 0 ≤ 1 - 2 * lambda := by linarith
    have herrorCharge : error ≤ lambda * charge / 2 := herror
    dsimp only [rectangle] at hrectangle
    nlinarith
  have htargetPositive : 0 < charge / 4 := by positivity
  have htargetAtom := exists_absorbingTerminalPayoffDifferenceAtom reward x11
    x01 observer (charge / 4) htargetPositive htargetGain
  exact ⟨hrectangleAtom, htargetGain, htargetAtom⟩

/-- The rectangle seen after the small reset is exactly `lambda` times the
full endpoint rectangle, outcome by outcome.  Hence a cutoff-independent
full-corner atom becomes an order-`lambda` cross-toggle at the actually used
reset. -/
theorem quittingTerminalOutcomeMass_smallResetRectangle_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (mover observer : ι) (hne : observer ≠ mover)
    (source target : (quittingGame reward).BehaviorStrategy mover)
    (deviation : (quittingGame reward).BehaviorStrategy observer)
    (lambda : ℝ) (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1)
    (outcome : QuittingTerminalOutcome ι) :
    let mixedStrategy := quittingStoppingLawMixtureBehaviorStrategy reward mover
      source target lambda hlambda0 hlambda1
    let mixed := Function.update profile mover mixedStrategy
    let x00 := Function.update profile mover source
    let x01 := Function.update profile mover target
    let x10 := Function.update x00 observer deviation
    let x11 := Function.update x01 observer deviation
    quittingTerminalOutcomeMass reward
          (Function.update mixed observer deviation) outcome -
        quittingTerminalOutcomeMass reward mixed outcome -
        (quittingTerminalOutcomeMass reward x10 outcome -
          quittingTerminalOutcomeMass reward x00 outcome) =
      lambda *
        (quittingTerminalOutcomeMass reward x11 outcome -
          quittingTerminalOutcomeMass reward x10 outcome -
          quittingTerminalOutcomeMass reward x01 outcome +
          quittingTerminalOutcomeMass reward x00 outcome) := by
  dsimp only
  let mixedStrategy := quittingStoppingLawMixtureBehaviorStrategy reward mover
    source target lambda hlambda0 hlambda1
  have hbase := quittingTerminalOutcomeMass_stoppingLawMixture_eq reward profile
    mover source target lambda hlambda0 hlambda1 outcome
  have hdeviation := quittingTerminalOutcomeMass_stoppingLawMixture_eq reward
    (Function.update profile observer deviation) mover source target lambda
      hlambda0 hlambda1 outcome
  have hcommuteMixed :
      Function.update (Function.update profile observer deviation) mover
          mixedStrategy =
        Function.update (Function.update profile mover mixedStrategy) observer
          deviation := by
    exact Function.update_comm hne deviation mixedStrategy profile
  have hcommuteSource :
      Function.update (Function.update profile observer deviation) mover source =
        Function.update (Function.update profile mover source) observer
          deviation := by
    exact Function.update_comm hne deviation source profile
  have hcommuteTarget :
      Function.update (Function.update profile observer deviation) mover target =
        Function.update (Function.update profile mover target) observer
          deviation := by
    exact Function.update_comm hne deviation target profile
  change quittingTerminalOutcomeMass reward
      (Function.update profile mover mixedStrategy) outcome = _ at hbase
  change quittingTerminalOutcomeMass reward
      (Function.update (Function.update profile observer deviation) mover
        mixedStrategy) outcome = _ at hdeviation
  rw [hcommuteMixed, hcommuteSource, hcommuteTarget] at hdeviation
  rw [hbase, hdeviation]
  ring

/-! ## Oriented pure-time witness switches -/

open Math.Optimization

/-- Terminal payoff obtained by replacing one player by a deterministic quit
time, including `Never`. -/
def quittingPureTimeDeviationPayoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (observer : ι) (quitTime : Option ℕ) : ℝ :=
  quittingTerminalPayoff reward
    (Function.update profile observer
      (quittingPureTimeBehaviorStrategy reward observer quitTime)) observer

/-- Regret of one deterministic quit time against the full behavioral
best-response envelope at the same literal profile. -/
def quittingPureTimeDeviationRegret
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (observer : ι) (quitTime : Option ℕ) : ℝ :=
  quittingContinuationBestResponseValue reward profile observer -
    quittingPureTimeDeviationPayoff reward profile observer quitTime

/-- The exact behavioral best-response envelope is the supremum of the
deterministic quit-time and `Never` values. -/
theorem quittingContinuationBestResponseValue_eq_sSup_pureTimeDeviationPayoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (observer : ι) :
    quittingContinuationBestResponseValue reward profile observer =
      sSup (Set.range
        (quittingPureTimeDeviationPayoff reward profile observer)) := by
  unfold quittingContinuationBestResponseValue quittingPureTimeDeviationPayoff
  exact sSup_range_quittingTerminalPayoff_update_eq_pureTime
    reward profile observer

/-- Pure-time deviation values are bounded by the behavioral best-response
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

/-- Game-semantic strengthening of an oriented supremum witness switch.  The
generic certificate retains both witnesses and all four strategic
inequalities.  The two additional atoms separately record its signed
cross-distribution rectangle and its directly profitable receiving edge;
these terminal coalitions need not coincide. -/
structure QuittingPureTimeWitnessSwitchCertificate
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source receiving : (quittingGame reward).BehaviorProfile)
    (observer : ι) (charge eta : ℝ) where
  switch : OrientedSupremumWitnessSwitch
    (quittingPureTimeDeviationPayoff reward source observer)
    (quittingPureTimeDeviationPayoff reward receiving observer)
    charge eta
  rectangleTerminal : {S : Finset ι // S.Nonempty}
  rectangle_atom : charge ≤
    (Fintype.card (QuittingTerminalOutcome ι) : ℝ) *
      quittingTerminalPayoffRectangleAtom reward
        (Function.update source observer
          (quittingPureTimeBehaviorStrategy reward observer
            switch.sourceWitness))
        (Function.update source observer
          (quittingPureTimeBehaviorStrategy reward observer
            switch.receivingWitness))
        (Function.update receiving observer
          (quittingPureTimeBehaviorStrategy reward observer
            switch.sourceWitness))
        (Function.update receiving observer
          (quittingPureTimeBehaviorStrategy reward observer
            switch.receivingWitness))
        observer (some rectangleTerminal)
  receivingTerminal : {S : Finset ι // S.Nonempty}
  receiving_atom : charge + eta ≤
    (Fintype.card (QuittingTerminalOutcome ι) : ℝ) *
      quittingTerminalPayoffDifferenceAtom reward
        (Function.update receiving observer
          (quittingPureTimeBehaviorStrategy reward observer
            switch.receivingWitness))
        (Function.update receiving observer
          (quittingPureTimeBehaviorStrategy reward observer
            switch.sourceWitness))
        observer (some receivingTerminal)

/-- Propositional existence wrapper for the full quitting-game certificate. -/
def HasQuittingPureTimeWitnessSwitchCertificate
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source receiving : (quittingGame reward).BehaviorProfile)
    (observer : ι) (charge eta : ℝ) : Prop :=
  Nonempty (QuittingPureTimeWitnessSwitchCertificate reward source receiving
    observer charge eta)

/-- The reduced rectangle-only interface.  This is kept as a corollary
surface; consumers needing strategic orientation should use the full
certificate. -/
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

/-- Forgetting the receiving regret, both edge bounds, and the receiving-edge
atom recovers the rectangle-only interface. -/
theorem QuittingPureTimeWitnessSwitchCertificate.hasRectangle
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {source receiving : (quittingGame reward).BehaviorProfile}
    {observer : ι} {charge eta : ℝ}
    (certificate : QuittingPureTimeWitnessSwitchCertificate reward source
      receiving observer charge eta) :
    HasQuittingPureTimeWitnessSwitchRectangle reward source receiving observer
      charge eta := by
  exact ⟨certificate.switch.sourceWitness,
    certificate.switch.receivingWitness, certificate.rectangleTerminal,
    by simpa only [
      quittingContinuationBestResponseValue_eq_sSup_pureTimeDeviationPayoff]
      using certificate.switch.source_approx,
    by simpa only [
      quittingContinuationBestResponseValue_eq_sSup_pureTimeDeviationPayoff]
      using certificate.switch.receiving_approx,
    certificate.switch.rectangle, certificate.rectangle_atom⟩

private theorem hasQuittingPureTimeWitnessSwitchCertificate_of_generic
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source receiving : (quittingGame reward).BehaviorProfile)
    (observer : ι) (charge eta : ℝ)
    (hcharge : 0 < charge) (heta : 0 < eta)
    (switch : OrientedSupremumWitnessSwitch
      (quittingPureTimeDeviationPayoff reward source observer)
      (quittingPureTimeDeviationPayoff reward receiving observer)
      charge eta) :
    HasQuittingPureTimeWitnessSwitchCertificate reward source receiving
      observer charge eta := by
  let x00 := Function.update source observer
    (quittingPureTimeBehaviorStrategy reward observer switch.sourceWitness)
  let x01 := Function.update source observer
    (quittingPureTimeBehaviorStrategy reward observer switch.receivingWitness)
  let x10 := Function.update receiving observer
    (quittingPureTimeBehaviorStrategy reward observer switch.sourceWitness)
  let x11 := Function.update receiving observer
    (quittingPureTimeBehaviorStrategy reward observer switch.receivingWitness)
  have hrectangle : charge ≤
      quittingTerminalPayoff reward x11 observer -
        quittingTerminalPayoff reward x10 observer -
        quittingTerminalPayoff reward x01 observer +
        quittingTerminalPayoff reward x00 observer := by
    simpa only [x00, x01, x10, x11, quittingPureTimeDeviationPayoff] using
      switch.rectangle
  obtain ⟨rectangleTerminal, hrectangleAtom⟩ :=
    exists_absorbingTerminalPayoffRectangleAtom reward x00 x01 x10 x11
      observer charge hcharge hrectangle
  have hreceiving : charge + eta ≤
      quittingTerminalPayoff reward x11 observer -
        quittingTerminalPayoff reward x10 observer := by
    simpa only [x10, x11, quittingPureTimeDeviationPayoff] using
      switch.receiving_gain
  have hreceivingPositive : 0 < charge + eta := by linarith
  obtain ⟨receivingTerminal, hreceivingAtom⟩ :=
    exists_absorbingTerminalPayoffDifferenceAtom reward x11 x10 observer
      (charge + eta) hreceivingPositive hreceiving
  exact ⟨{
    switch := switch
    rectangleTerminal := rectangleTerminal
    rectangle_atom := by
      simpa only [x00, x01, x10, x11] using hrectangleAtom
    receivingTerminal := receivingTerminal
    receiving_atom := by simpa only [x10, x11] using hreceivingAtom
  }⟩

/-- A fixed-witness square budget and sufficiently large signed envelope
curvature produce one of the two full oriented pure-time certificates.  The
budget is `q + 3 * eta`; no best-response supremum is assumed attained. -/
theorem exists_pureTimeWitnessSwitchCertificate_of_abs_envelopeCurvature
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
    HasQuittingPureTimeWitnessSwitchCertificate reward x11 x00 observer
        charge eta ∨
      HasQuittingPureTimeWitnessSwitchCertificate reward x10 x01 observer
        charge eta := by
  let f00 := quittingPureTimeDeviationPayoff reward x00 observer
  let f10 := quittingPureTimeDeviationPayoff reward x10 observer
  let f01 := quittingPureTimeDeviationPayoff reward x01 observer
  let f11 := quittingPureTimeDeviationPayoff reward x11 observer
  have hswitch := orientedSupremumWitnessSwitch_of_abs_mixedDifference
    f00 f10 f01 f11
    (bddAbove_range_quittingPureTimeDeviationPayoff reward x00 observer)
    (bddAbove_range_quittingPureTimeDeviationPayoff reward x10 observer)
    (bddAbove_range_quittingPureTimeDeviationPayoff reward x01 observer)
    (bddAbove_range_quittingPureTimeDeviationPayoff reward x11 observer)
    q charge eta heta hface
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
  have hcurvature' : charge + q + 3 * eta ≤
      |supMixedDifference f00 f10 f01 f11| := by
    simpa only [supMixedDifference, f00, f10, f01, f11, ← hcap00,
      ← hcap10, ← hcap01, ← hcap11] using hcurvature
  specialize hswitch hcurvature'
  rcases hswitch with hswitch | hswitch
  · left
    rcases hswitch with ⟨switch⟩
    exact hasQuittingPureTimeWitnessSwitchCertificate_of_generic reward
      x11 x00 observer charge eta hcharge heta switch
  · right
    rcases hswitch with ⟨switch⟩
    exact hasQuittingPureTimeWitnessSwitchCertificate_of_generic reward
      x10 x01 observer charge eta hcharge heta switch

/-- After budgeting prescribed-payoff curvature, a debt square with margin
`charge + prescribedBound + q + 3 * eta` yields the same full strategic
certificate. -/
theorem exists_pureTimeWitnessSwitchCertificate_of_abs_debtCurvature
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (x00 x10 x01 x11 : (quittingGame reward).BehaviorProfile)
    (observer : ι) (prescribedBound q charge eta : ℝ)
    (hcharge : 0 < charge) (heta : 0 < eta)
    (hprescribed :
      |quittingTerminalPayoff reward x11 observer -
          quittingTerminalPayoff reward x10 observer -
          quittingTerminalPayoff reward x01 observer +
          quittingTerminalPayoff reward x00 observer| ≤ prescribedBound)
    (hface : ∀ quitTime : Option ℕ,
      |quittingPureTimeDeviationPayoff reward x11 observer quitTime -
          quittingPureTimeDeviationPayoff reward x10 observer quitTime -
          quittingPureTimeDeviationPayoff reward x01 observer quitTime +
          quittingPureTimeDeviationPayoff reward x00 observer quitTime| ≤ q)
    (hcurvature : charge + prescribedBound + q + 3 * eta ≤
      |quittingTerminalSemanticDebt
            (quittingTerminalSemanticPair reward x11) observer -
          quittingTerminalSemanticDebt
            (quittingTerminalSemanticPair reward x10) observer -
          quittingTerminalSemanticDebt
            (quittingTerminalSemanticPair reward x01) observer +
          quittingTerminalSemanticDebt
            (quittingTerminalSemanticPair reward x00) observer|) :
    HasQuittingPureTimeWitnessSwitchCertificate reward x11 x00 observer
        charge eta ∨
      HasQuittingPureTimeWitnessSwitchCertificate reward x10 x01 observer
        charge eta := by
  let envelopeCurvature :=
    quittingContinuationBestResponseValue reward x11 observer -
      quittingContinuationBestResponseValue reward x10 observer -
      quittingContinuationBestResponseValue reward x01 observer +
      quittingContinuationBestResponseValue reward x00 observer
  let prescribedCurvature :=
    quittingTerminalPayoff reward x11 observer -
      quittingTerminalPayoff reward x10 observer -
      quittingTerminalPayoff reward x01 observer +
      quittingTerminalPayoff reward x00 observer
  let debtCurvature :=
    quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward x11) observer -
      quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward x10) observer -
      quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward x01) observer +
      quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward x00) observer
  have hidentity : debtCurvature =
      envelopeCurvature - prescribedCurvature := by
    dsimp only [debtCurvature, envelopeCurvature, prescribedCurvature,
      quittingTerminalSemanticDebt, quittingTerminalSemanticPair]
    ring
  have habs : |debtCurvature| ≤
      |envelopeCurvature| + |prescribedCurvature| := by
    rw [hidentity]
    calc
      |envelopeCurvature - prescribedCurvature| =
          |envelopeCurvature + -prescribedCurvature| := by ring_nf
      _ ≤ |envelopeCurvature| + |-prescribedCurvature| := abs_add_le _ _
      _ = |envelopeCurvature| + |prescribedCurvature| := by rw [abs_neg]
  have henvelope : charge + q + 3 * eta ≤ |envelopeCurvature| := by
    have hprescribed' : |prescribedCurvature| ≤ prescribedBound := by
      simpa only [prescribedCurvature] using hprescribed
    have hdebt : charge + prescribedBound + q + 3 * eta ≤
        |debtCurvature| := by
      simpa only [debtCurvature] using hcurvature
    linarith
  apply exists_pureTimeWitnessSwitchCertificate_of_abs_envelopeCurvature
    reward x00 x10 x01 x11 observer q charge eta hcharge heta hface
  simpa only [envelopeCurvature] using henvelope

end GameTheory
