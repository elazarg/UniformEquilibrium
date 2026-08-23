/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.StoppingLaw.DebtSlopeAtomAlternative
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPositiveSlopeRectangle

/-!
# A common response on a positive stopping-law debt chord

A positive debt chord is evaluated at one literal source profile and one
complete-law reset of another player.  Choosing an approximately optimal
pure stopping time at the small mixed profile gives one response which is
simultaneously useful on all three profiles.

Its debt at the mixed profile is small.  Its source regret is bounded by the
small reset scale, so it becomes a source best response whenever the source
coordinate debt vanishes.  Affinity of every fixed response then turns the
normalized debt increase into an order-one endpoint interaction and endpoint
gain.

The small-debt conclusion belongs to the mixed profile, not automatically to
the full reset endpoint.  Moving it to the endpoint requires either an
additional common-witness hypothesis or the existing oriented witness-switch
alternative.
-/

noncomputable section

namespace GameTheory

open StochasticGame

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Full endpoint of one stopping-law reset. -/
def quittingStoppingLawFullResetProfile
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (mover : ι) (target : (quittingGame reward).BehaviorStrategy mover) :
    (quittingGame reward).BehaviorProfile :=
  Function.update profile mover target

/-- Small complete-law mixture on the same literal source and endpoint. -/
def quittingStoppingLawMixedResetProfile
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (mover : ι) (target : (quittingGame reward).BehaviorStrategy mover)
    (lambda : ℝ) (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1) :
    (quittingGame reward).BehaviorProfile :=
  Function.update profile mover
    (quittingStoppingLawMixtureBehaviorStrategy reward mover
      (profile mover) target lambda hlambda0 hlambda1)

/-- Gain of one deterministic stopping time against one literal profile. -/
def quittingPureTimeResponseGain
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (observer : ι) (quitTime : Option ℕ) : ℝ :=
  quittingPureTimeDeviationPayoff reward profile observer quitTime -
    quittingTerminalPayoff reward profile observer

/-- One common pure-time response carrying a positive mixed debt chord.

The source gain lies within `4 * rewardBound * lambda + eta` of the source
semantic debt.  The full endpoint gain differs from the source gain by the
normalized chord charge, up to `eta / lambda`. -/
structure QuittingStoppingLawCommonResponsePassport
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (mover observer : ι)
    (target : (quittingGame reward).BehaviorStrategy mover)
    (lambda charge eta : ℝ)
    (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1) where
  quitTime : Option ℕ
  mixed_approx :
    quittingContinuationBestResponseValue reward
          (quittingStoppingLawMixedResetProfile reward profile mover target
            lambda hlambda0 hlambda1) observer - eta ≤
      quittingPureTimeDeviationPayoff reward
        (quittingStoppingLawMixedResetProfile reward profile mover target
          lambda hlambda0 hlambda1) observer quitTime
  mixed_response_debt_le :
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (Function.update
            (quittingStoppingLawMixedResetProfile reward profile mover target
              lambda hlambda0 hlambda1)
            observer
            (quittingPureTimeBehaviorStrategy reward observer quitTime)))
        observer ≤ eta
  source_gain_le :
    quittingPureTimeResponseGain reward profile observer quitTime ≤
      quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward profile) observer
  source_gain_ge :
    quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward profile) observer -
        4 * quittingRewardBound reward * lambda - eta ≤
      quittingPureTimeResponseGain reward profile observer quitTime
  interaction_lower :
    charge - eta / lambda ≤
      quittingPureTimeResponseGain reward
          (quittingStoppingLawFullResetProfile reward profile mover target)
          observer quitTime -
        quittingPureTimeResponseGain reward profile observer quitTime
  endpoint_gain_lower :
    charge - eta / lambda - 4 * quittingRewardBound reward * lambda - eta ≤
      quittingPureTimeResponseGain reward
        (quittingStoppingLawFullResetProfile reward profile mover target)
        observer quitTime

/-- A positive mixed debt chord admits the common-response passport.  No
best-response supremum is assumed attained. -/
theorem exists_quittingStoppingLawCommonResponsePassport
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (mover observer : ι) (hne : observer ≠ mover)
    (target : (quittingGame reward).BehaviorStrategy mover)
    (lambda charge eta : ℝ)
    (hlambda0 : 0 < lambda) (hlambda1 : lambda ≤ 1)
    (hcharge : 0 ≤ charge) (heta : 0 < eta)
    (hslope : lambda * charge ≤
      quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            (quittingStoppingLawMixedResetProfile reward profile mover target
              lambda hlambda0.le hlambda1)) observer -
        quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward profile) observer) :
    Nonempty
      (QuittingStoppingLawCommonResponsePassport reward profile mover observer
        target lambda charge eta hlambda0.le hlambda1) := by
  let endpoint :=
    quittingStoppingLawFullResetProfile reward profile mover target
  let mixed := quittingStoppingLawMixedResetProfile reward profile mover target
    lambda hlambda0.le hlambda1
  obtain ⟨deviation, hdeviation⟩ :=
    exists_quittingContinuation_deviation_ge_sub reward mixed observer
      (half_pos heta)
  obtain ⟨quitTime, hquitTime⟩ :=
    exists_quittingPureTimeBehaviorStrategy_terminalPayoff_ge_sub
      reward mixed observer deviation (half_pos heta)
  let response := quittingPureTimeBehaviorStrategy reward observer quitTime
  have hmixedApprox :
      quittingContinuationBestResponseValue reward mixed observer - eta ≤
        quittingTerminalPayoff reward
          (Function.update mixed observer response) observer := by
    dsimp only [response]
    linarith
  have hsourceAffine := quittingTerminalPayoff_stoppingLawMixture_eq
    reward profile mover observer (profile mover) target lambda hlambda0.le
      hlambda1
  rw [Function.update_eq_self] at hsourceAffine
  have hresponseAffine := quittingTerminalPayoff_stoppingLawMixture_eq
    reward (Function.update profile observer response) mover observer
      (profile mover) target lambda hlambda0.le hlambda1
  have hsourceMover :
      Function.update profile observer response mover = profile mover := by
    rw [Function.update_of_ne (Ne.symm hne)]
  have hsourceUpdate :
      Function.update (Function.update profile observer response) mover
          (profile mover) = Function.update profile observer response := by
    rw [← hsourceMover, Function.update_eq_self]
  have hcommuteMixed :
      Function.update (Function.update profile observer response) mover
          (quittingStoppingLawMixtureBehaviorStrategy reward mover
            (profile mover) target lambda hlambda0.le hlambda1) =
        Function.update mixed observer response := by
    exact Function.update_comm hne response _ profile
  have hcommuteEndpoint :
      Function.update (Function.update profile observer response) mover target =
        Function.update endpoint observer response := by
    exact Function.update_comm hne response target profile
  rw [hcommuteMixed, hsourceUpdate, hcommuteEndpoint] at hresponseAffine
  let sourceGain := quittingPureTimeResponseGain reward profile observer quitTime
  let mixedGain := quittingPureTimeResponseGain reward mixed observer quitTime
  let endpointGain := quittingPureTimeResponseGain reward endpoint observer quitTime
  have hgainAffine : mixedGain =
      (1 - lambda) * sourceGain + lambda * endpointGain := by
    dsimp only [sourceGain, mixedGain, endpointGain,
      quittingPureTimeResponseGain, quittingPureTimeDeviationPayoff,
      response] at hsourceAffine hresponseAffine ⊢
    linear_combination hresponseAffine - hsourceAffine
  have hsourceCap :=
    quittingTerminalPayoff_update_le_continuationBestResponseValue
      reward profile observer response
  have hsourceGainLe : sourceGain ≤
      quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward profile) observer := by
    dsimp only [sourceGain, quittingPureTimeResponseGain,
      quittingPureTimeDeviationPayoff, response]
    unfold quittingTerminalSemanticDebt quittingTerminalSemanticPair
    linarith
  have hmixedGainLower :
      quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward mixed) observer - eta ≤
        mixedGain := by
    dsimp only [mixedGain, quittingPureTimeResponseGain,
      quittingPureTimeDeviationPayoff, response]
    unfold quittingTerminalSemanticDebt quittingTerminalSemanticPair
    linarith
  have hscaledInteraction : lambda * charge - eta ≤
      lambda * (endpointGain - sourceGain) := by
    linarith
  have hinteraction : charge - eta / lambda ≤
      endpointGain - sourceGain := by
    apply (mul_le_mul_iff_of_pos_left hlambda0).mp
    calc
      lambda * (charge - eta / lambda) = lambda * charge - eta := by
        field_simp [ne_of_gt hlambda0]
      _ ≤ lambda * (endpointGain - sourceGain) := hscaledInteraction
  have hsourcePayoffAbs := abs_quittingTerminalPayoff_le reward profile observer
    (abs_reward_le_quittingRewardBound reward)
  have hsourceResponseAbs := abs_quittingTerminalPayoff_le reward
    (Function.update profile observer response) observer
      (abs_reward_le_quittingRewardBound reward)
  have hendpointPayoffAbs := abs_quittingTerminalPayoff_le reward endpoint observer
    (abs_reward_le_quittingRewardBound reward)
  have hendpointResponseAbs := abs_quittingTerminalPayoff_le reward
    (Function.update endpoint observer response) observer
      (abs_reward_le_quittingRewardBound reward)
  rw [abs_le] at hsourcePayoffAbs hsourceResponseAbs
  rw [abs_le] at hendpointPayoffAbs hendpointResponseAbs
  have hinteractionUpper : endpointGain - sourceGain ≤
      4 * quittingRewardBound reward := by
    dsimp only [endpointGain, sourceGain, quittingPureTimeResponseGain,
      quittingPureTimeDeviationPayoff, endpoint, response]
    linarith
  have hmixedSubSource : mixedGain - sourceGain ≤
      4 * quittingRewardBound reward * lambda := by
    have hscaled :=
      mul_le_mul_of_nonneg_left hinteractionUpper hlambda0.le
    rw [hgainAffine]
    linarith
  have hscaledCharge : 0 ≤ lambda * charge :=
    mul_nonneg hlambda0.le hcharge
  have hsourceGainGe :
      quittingTerminalSemanticDebt
            (quittingTerminalSemanticPair reward profile) observer -
          4 * quittingRewardBound reward * lambda - eta ≤ sourceGain := by
    linarith
  have hsourceDebtNonneg : 0 ≤
      quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward profile) observer :=
    quittingTerminalDeviationDebt_nonneg reward profile observer
  have hendpointGainGe :
      charge - eta / lambda -
            4 * quittingRewardBound reward * lambda - eta ≤ endpointGain := by
    linarith
  have hmixedDebt : quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward
        (Function.update mixed observer response)) observer ≤ eta := by
    unfold quittingTerminalSemanticDebt quittingTerminalSemanticPair
    change quittingContinuationBestResponseValue reward
          (Function.update mixed observer response) observer -
        quittingTerminalPayoff reward
          (Function.update mixed observer response) observer ≤ eta
    rw [quittingContinuationBestResponseValue_update_self]
    linarith
  refine ⟨{
    quitTime := quitTime
    mixed_approx := ?_
    mixed_response_debt_le := ?_
    source_gain_le := ?_
    source_gain_ge := ?_
    interaction_lower := ?_
    endpoint_gain_lower := ?_
  }⟩
  · simpa only [mixed, response, quittingPureTimeDeviationPayoff] using
      hmixedApprox
  · simpa only [mixed, response] using hmixedDebt
  · simpa only [sourceGain] using hsourceGainLe
  · simpa only [sourceGain] using hsourceGainGe
  · simpa only [endpointGain, sourceGain, endpoint] using hinteraction
  · simpa only [endpointGain, endpoint] using hendpointGainGe

/-- The common response's order-one interaction splits into the existing
prescribed atom or same-response rectangle atom. -/
theorem hasQuittingStoppingLawDebtSlopeAtomAlternative_of_commonResponse
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (mover observer : ι)
    (target : (quittingGame reward).BehaviorStrategy mover)
    (quitTime : Option ℕ) (charge : ℝ) (hcharge : 0 < charge)
    (hinteraction : charge ≤
      quittingPureTimeResponseGain reward
          (quittingStoppingLawFullResetProfile reward profile mover target)
          observer quitTime -
        quittingPureTimeResponseGain reward profile observer quitTime) :
    HasQuittingStoppingLawDebtSlopeAtomAlternative reward profile mover observer
      target charge := by
  let endpoint :=
    quittingStoppingLawFullResetProfile reward profile mover target
  let response := quittingPureTimeBehaviorStrategy reward observer quitTime
  by_cases hprescribed : charge / 2 ≤
      quittingTerminalPayoff reward profile observer -
        quittingTerminalPayoff reward endpoint observer
  · exact Or.inl
      (exists_absorbingTerminalPayoffDifferenceAtom reward profile endpoint
        observer (charge / 2) (by positivity) hprescribed)
  · right
    have hrectangle : charge / 4 ≤
        quittingTerminalPayoff reward
            (Function.update endpoint observer response) observer -
          quittingTerminalPayoff reward
            (Function.update profile observer response) observer := by
      dsimp only [quittingPureTimeResponseGain,
        quittingPureTimeDeviationPayoff, endpoint, response] at hinteraction ⊢
      have hprescribedLt := lt_of_not_ge hprescribed
      linarith
    obtain ⟨terminal, hterminal⟩ :=
      exists_absorbingTerminalPayoffDifferenceAtom reward
        (Function.update endpoint observer response)
        (Function.update profile observer response) observer (charge / 4)
        (by positivity) hrectangle
    cases quitTime with
    | none =>
        exact Or.inl ⟨terminal, by
          simpa only [endpoint, response, quittingStoppingLawFullResetProfile,
            Function.update_eq_self] using hterminal⟩
    | some stop =>
        exact Or.inr ⟨stop, terminal, by
          simpa only [endpoint, response, quittingStoppingLawFullResetProfile,
            Function.update_eq_self] using hterminal⟩

/-- An explicitly supplied source witness with large regret at a receiving
profile yields the full oriented quitting-game witness-switch certificate. -/
theorem exists_quittingPureTimeWitnessSwitchCertificate_of_sourceWitness
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source receiving : (quittingGame reward).BehaviorProfile)
    (observer : ι) (sourceWitness : Option ℕ)
    (charge eta : ℝ) (hcharge : 0 < charge) (heta : 0 < eta)
    (hsourceApprox :
      quittingContinuationBestResponseValue reward source observer - eta ≤
        quittingPureTimeDeviationPayoff reward source observer sourceWitness)
    (hregret : charge + 2 * eta ≤
      quittingContinuationBestResponseValue reward receiving observer -
        quittingPureTimeDeviationPayoff reward receiving observer
          sourceWitness) :
    HasQuittingPureTimeWitnessSwitchCertificate reward source receiving
      observer charge eta := by
  obtain ⟨switch⟩ := Math.Optimization.orientedSupremumWitnessSwitch_of_regret
    (quittingPureTimeDeviationPayoff reward source observer)
    (quittingPureTimeDeviationPayoff reward receiving observer)
    (bddAbove_range_quittingPureTimeDeviationPayoff reward source observer)
    charge eta heta sourceWitness (by
      simpa only [
        quittingContinuationBestResponseValue_eq_sSup_pureTimeDeviationPayoff]
        using hsourceApprox) (by
      simpa only [
        quittingContinuationBestResponseValue_eq_sSup_pureTimeDeviationPayoff]
        using hregret)
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

/-- The common response is either already a sufficiently good witness at the
full endpoint or it produces the existing oriented witness-switch
certificate.  This is the exact correction to moving the mixed-profile debt
bound to the full endpoint without justification. -/
theorem QuittingStoppingLawCommonResponsePassport.endpointDebt_le_or_witnessSwitch
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {profile : (quittingGame reward).BehaviorProfile}
    {mover observer : ι}
    {target : (quittingGame reward).BehaviorStrategy mover}
    {lambda chordCharge chordEta : ℝ}
    {hlambda0 : 0 ≤ lambda} {hlambda1 : lambda ≤ 1}
    (passport : QuittingStoppingLawCommonResponsePassport reward profile mover
      observer target lambda chordCharge chordEta hlambda0 hlambda1)
    (switchCharge switchEta : ℝ)
    (hswitchCharge : 0 < switchCharge) (hswitchEta : 0 < switchEta)
    (hsourceError :
      4 * quittingRewardBound reward * lambda + chordEta ≤ switchEta) :
    let endpoint :=
      quittingStoppingLawFullResetProfile reward profile mover target
    let endpointResponse := Function.update endpoint observer
      (quittingPureTimeBehaviorStrategy reward observer passport.quitTime)
    quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward endpointResponse) observer ≤
        switchCharge + 2 * switchEta ∨
      HasQuittingPureTimeWitnessSwitchCertificate reward profile endpoint
        observer switchCharge switchEta := by
  dsimp only
  let endpoint :=
    quittingStoppingLawFullResetProfile reward profile mover target
  let response := quittingPureTimeBehaviorStrategy reward observer
    passport.quitTime
  let endpointResponse := Function.update endpoint observer response
  let endpointDebt := quittingTerminalSemanticDebt
    (quittingTerminalSemanticPair reward endpointResponse) observer
  by_cases hsmall : endpointDebt ≤ switchCharge + 2 * switchEta
  · exact Or.inl hsmall
  · right
    have hsourceApprox :
        quittingContinuationBestResponseValue reward profile observer -
            switchEta ≤
          quittingPureTimeDeviationPayoff reward profile observer
            passport.quitTime := by
      have hgain := passport.source_gain_ge
      dsimp only [quittingPureTimeResponseGain,
        quittingPureTimeDeviationPayoff] at hgain ⊢
      unfold quittingTerminalSemanticDebt quittingTerminalSemanticPair at hgain
      linarith
    have hregretEq :
        quittingContinuationBestResponseValue reward endpoint observer -
            quittingPureTimeDeviationPayoff reward endpoint observer
              passport.quitTime = endpointDebt := by
      dsimp only [endpointDebt, endpointResponse,
        quittingPureTimeDeviationPayoff, response]
      unfold quittingTerminalSemanticDebt quittingTerminalSemanticPair
      rw [quittingContinuationBestResponseValue_update_self]
    have hregret : switchCharge + 2 * switchEta ≤
        quittingContinuationBestResponseValue reward endpoint observer -
          quittingPureTimeDeviationPayoff reward endpoint observer
            passport.quitTime := by
      rw [hregretEq]
      exact (lt_of_not_ge hsmall).le
    exact exists_quittingPureTimeWitnessSwitchCertificate_of_sourceWitness
      reward profile endpoint observer passport.quitTime switchCharge switchEta
      hswitchCharge hswitchEta hsourceApprox hregret

end GameTheory
