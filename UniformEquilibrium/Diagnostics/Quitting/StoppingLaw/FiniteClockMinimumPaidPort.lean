/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.ProbabilityMassFunction.BoundedSupportAverage
import UniformEquilibrium.Diagnostics.Quitting.StoppingLaw.FiniteClockCanonicalization
import UniformEquilibrium.Diagnostics.Quitting.StoppingLaw.FiniteClockMinimumPurification

/-!
# Finite-clock minimum reduction to paid ports

A supplied finite-clock positive global minimum admits a bounded exact-cap
purification chain.  Its strict exit supplies a paid response, or its canonical
pure-time endpoint admits the constructed deadline descent and paid response.

This is conditional on the supplied finite-clock global minimum. It is not a
source producer, chronological construction, renewal theorem, or uniform
equilibrium consumer.
-/

noncomputable section

namespace GameTheory

open _root_.Math.Probability _root_.Math.Probability.DiscreteHazard
open _root_.Math.ProbabilityMassFunction

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Complete paid-port data at one deadline-bounded strict target. -/
structure QuittingDeadlineBoundedExactPaidPort
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (minimumDebt : ℝ) where
  profile : (quittingGame reward).BehaviorProfile
  deadline : ℕ
  deadlineBounded : QuittingDeadlineBounded reward profile deadline
  offMinimum : minimumDebt < quittingTerminalSemanticDebtSum
    (quittingTerminalSemanticPair reward profile)
  responder : ι
  choice : Option ℕ
  sourceWitness : Option ℕ
  cap : quittingPureTimeDeviationPayoff reward profile responder choice =
    quittingContinuationBestResponseValue reward profile responder
  sourceSupport : sourceWitness ∈
    (quittingBehaviorStoppingLaw reward (profile responder)).support
  gain_eq_semanticDebt :
    quittingPureTimeDeviationPayoff reward profile responder choice -
        quittingTerminalPayoff reward profile responder =
      quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward profile) responder
  averageGain :
    quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward profile) / Fintype.card ι ≤
      quittingPureTimeDeviationPayoff reward profile responder choice -
        quittingTerminalPayoff reward profile responder
  sourcePaid :
    minimumDebt / Fintype.card ι <
      quittingPureTimeDeviationPayoff reward profile responder choice -
        quittingPureTimeDeviationPayoff reward profile responder sourceWitness
  row : QuittingPaidFirstDisagreementRow reward profile responder
    (minimumDebt / Fintype.card ι)
  row_source : row.sourceWitness = sourceWitness
  row_receiving : row.receivingWitness = choice

private theorem exists_deadlineBoundedExactPaidPort
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (minimumDebt : ℝ) (hminimumPositive : 0 < minimumDebt)
    (profile : (quittingGame reward).BehaviorProfile) (deadline : ℕ)
    (hbound : QuittingDeadlineBounded reward profile deadline)
    (hoff : minimumDebt < quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPair reward profile)) :
    ∃ port : QuittingDeadlineBoundedExactPaidPort reward minimumDebt,
      port.profile = profile ∧ port.deadline = deadline := by
  let pair := quittingTerminalSemanticPair reward profile
  have hpositive : 0 < quittingTerminalSemanticDebtSum pair :=
    hminimumPositive.trans (by simpa only [pair] using hoff)
  obtain ⟨responder, haverage⟩ :=
    exists_quittingTerminalSemanticDebt_ge_average pair hpositive
  obtain ⟨choice, hcap, _⟩ :=
    exists_quittingDeadlineBounded_pureTime_eq_cap
      reward profile responder hbound
  let value := quittingPureTimeDeviationPayoff reward profile responder
  have hvalueBound : ∀ response,
      |value response| ≤ quittingRewardBound reward := by
    intro response
    exact abs_quittingTerminalPayoff_le_quittingRewardBound reward _ responder
  obtain ⟨sourceWitness, hsourceSupport, hsourceLe⟩ :=
    exists_mem_support_le_expect
      (quittingBehaviorStoppingLaw reward (profile responder))
      value hvalueBound
  have hprescribed : quittingTerminalPayoff reward profile responder =
      Math.Probability.expect
        (quittingBehaviorStoppingLaw reward (profile responder)) value := by
    have hmix := quittingTerminalPayoff_update_eq_expect_stoppingLaw_pureTime
      reward profile responder (profile responder)
    rw [Function.update_eq_self] at hmix
    exact hmix
  have hgainEq :
      quittingPureTimeDeviationPayoff reward profile responder choice -
          quittingTerminalPayoff reward profile responder =
        quittingTerminalSemanticDebt pair responder := by
    unfold quittingTerminalSemanticDebt
    dsimp only [pair, quittingTerminalSemanticPair]
    rw [hcap]
  have hcard : (0 : ℝ) < Fintype.card ι := by
    exact_mod_cast Fintype.card_pos
  have hminimumAverage : minimumDebt / Fintype.card ι <
      quittingTerminalSemanticDebtSum pair / Fintype.card ι :=
    div_lt_div_of_pos_right (by simpa only [pair] using hoff) hcard
  have hpurePaid : minimumDebt / Fintype.card ι <
      quittingPureTimeDeviationPayoff reward profile responder choice -
        quittingPureTimeDeviationPayoff reward profile responder sourceWitness := by
    calc
      minimumDebt / Fintype.card ι <
          quittingTerminalSemanticDebtSum pair / Fintype.card ι := hminimumAverage
      _ ≤ quittingTerminalSemanticDebt pair responder := haverage
      _ = quittingPureTimeDeviationPayoff reward profile responder choice -
          quittingTerminalPayoff reward profile responder := hgainEq.symm
      _ ≤ quittingPureTimeDeviationPayoff reward profile responder choice -
          quittingPureTimeDeviationPayoff reward profile responder sourceWitness := by
        rw [hprescribed]
        exact sub_le_sub_left hsourceLe _
  have hgamma : 0 < minimumDebt / Fintype.card ι :=
    div_pos hminimumPositive hcard
  obtain ⟨row, hsource, hreceiving⟩ :=
    exists_quittingPaidFirstDisagreementRow_of_pureTimePayoff_sub
      reward profile responder sourceWitness choice
        (minimumDebt / Fintype.card ι) hgamma hpurePaid.le
  let port : QuittingDeadlineBoundedExactPaidPort reward minimumDebt :=
    { profile := profile
      deadline := deadline
      deadlineBounded := hbound
      offMinimum := hoff
      responder := responder
      choice := choice
      sourceWitness := sourceWitness
      cap := hcap
      sourceSupport := hsourceSupport
      gain_eq_semanticDebt := hgainEq
      averageGain := by rw [hgainEq]; exact haverage
      sourcePaid := hpurePaid
      row := row
      row_source := hsource
      row_receiving := hreceiving }
  exact ⟨port, rfl, rfl⟩

/-- The canonical pure-time branch retains the literal ancestry constructed
by deadline-rank descent and its resulting exact paid response. -/
structure QuittingPureTimeDescentPaidPort
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (minimumDebt : ℝ) (source : QuittingPureTimeProfile ι) where
  target : QuittingPureTimeProfile ι
  ancestry : IsQuittingPureTimeReplacementAncestry source target
  offMinimum : minimumDebt < quittingTerminalSemanticDebtSum
    (quittingTerminalSemanticPair reward
      (quittingPureTimeProfileBehavior reward target))
  responder : ι
  response : Option ℕ
  cap : quittingTerminalPayoff reward
      (quittingPureTimeProfileBehavior reward
        (Function.update target responder response)) responder =
    quittingContinuationBestResponseValue reward
      (quittingPureTimeProfileBehavior reward target) responder
  gain_eq_semanticDebt :
    quittingTerminalPayoff reward
          (quittingPureTimeProfileBehavior reward
            (Function.update target responder response)) responder -
        quittingTerminalPayoff reward
          (quittingPureTimeProfileBehavior reward target) responder =
      quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (quittingPureTimeProfileBehavior reward target)) responder
  averageGain :
    quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward
            (quittingPureTimeProfileBehavior reward target)) /
          Fintype.card ι ≤
      quittingTerminalPayoff reward
          (quittingPureTimeProfileBehavior reward
            (Function.update target responder response)) responder -
        quittingTerminalPayoff reward
          (quittingPureTimeProfileBehavior reward target) responder
  sourcePaid : minimumDebt / Fintype.card ι <
    quittingTerminalPayoff reward
        (quittingPureTimeProfileBehavior reward
          (Function.update target responder response)) responder -
      quittingTerminalPayoff reward
        (quittingPureTimeProfileBehavior reward target) responder
  row : QuittingPaidFirstDisagreementRow reward
    (quittingPureTimeProfileBehavior reward target) responder
      (minimumDebt / Fintype.card ι)
  row_source : row.sourceWitness = target responder
  row_receiving : row.receivingWitness = response

private theorem exists_pureTimeDescentPaidPort
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (minimumDebt : ℝ)
    (hlower : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      minimumDebt ≤ quittingTerminalSemanticDebtSum candidate)
    (hpositive : 0 < minimumDebt) (times : QuittingPureTimeProfile ι)
    (hminimum : quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPair reward
        (quittingPureTimeProfileBehavior reward times)) = minimumDebt) :
    Nonempty (QuittingPureTimeDescentPaidPort reward minimumDebt times) := by
  obtain ⟨target, hancestry, responder, response, hoff, hcap,
      haverage, hpaid, row, hrowSource, hrowReceiving⟩ :=
    pureTimeMinimum_exists_offMinimumPaidPort reward minimumDebt hlower
      hpositive times hminimum
  have hgainEq :
      quittingTerminalPayoff reward
            (quittingPureTimeProfileBehavior reward
              (Function.update target responder response)) responder -
          quittingTerminalPayoff reward
            (quittingPureTimeProfileBehavior reward target) responder =
        quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            (quittingPureTimeProfileBehavior reward target)) responder := by
    unfold quittingTerminalSemanticDebt
    dsimp only [quittingTerminalSemanticPair]
    rw [hcap]
  exact ⟨
    { target := target
      ancestry := hancestry
      offMinimum := hoff
      responder := responder
      response := response
      cap := hcap
      gain_eq_semanticDebt := hgainEq
      averageGain := haverage
      sourcePaid := hpaid
      row := row
      row_source := hrowSource
      row_receiving := hrowReceiving }⟩

/-- The two literal exits of bounded exact-cap purification. -/
inductive QuittingFiniteClockMinimumPaidPortReduction
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (canonical : (quittingGame reward).BehaviorProfile)
    (minimumDebt : ℝ) (stepBound : ℕ) : Prop
  | purificationExit
      (port : QuittingDeadlineBoundedExactPaidPort reward minimumDebt)
      (steps : ℕ)
      (steps_le : steps ≤ stepBound)
      (chain : QuittingPureTimeCapReplacementStepsOnDebtFiber minimumDebt
        steps canonical port.profile) :
      QuittingFiniteClockMinimumPaidPortReduction reward canonical
        minimumDebt stepBound
  | canonicalDescent
      (times : QuittingPureTimeProfile ι)
      (steps : ℕ)
      (steps_le : steps ≤ stepBound)
      (chain : QuittingPureTimeCapReplacementStepsOnDebtFiber minimumDebt
        steps canonical (quittingPureTimeProfileBehavior reward times))
      (onMinimum : quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward
            (quittingPureTimeProfileBehavior reward times)) = minimumDebt)
      (globalMinimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
        minimumDebt ≤ quittingTerminalSemanticDebtSum candidate)
      (port : QuittingPureTimeDescentPaidPort reward minimumDebt times) :
      QuittingFiniteClockMinimumPaidPortReduction reward canonical
        minimumDebt stepBound

/-- A supplied finite-clock positive global minimum has a canonicalized source
with identical semantics and a fibre-recorded exact-cap chain of length at most
the number of players.  Its first strict exit has a deadline-bounded paid row;
otherwise the canonical pure-time endpoint has the literal ancestry and paid
row produced by deadline descent. -/
theorem finiteClockMinimum_exactCapPurification_or_pureTimeDescentPaidPort
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (hclock : IsQuittingFiniteClockProfile reward profile)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward profile) ≤
        quittingTerminalSemanticDebtSum candidate)
    (hpositive : 0 < quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPair reward profile)) :
    ∃ clockBound,
      HasQuittingFiniteClockBound reward profile clockBound ∧
      QuittingDeadlineBounded reward
        (quittingStoppingLawCanonicalizeOn reward profile Finset.univ)
        clockBound ∧
      quittingTerminalSemanticPair reward
          (quittingStoppingLawCanonicalizeOn reward profile Finset.univ) =
        quittingTerminalSemanticPair reward profile ∧
      QuittingFiniteClockMinimumPaidPortReduction reward
        (quittingStoppingLawCanonicalizeOn reward profile Finset.univ)
        (quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward profile))
        (Fintype.card ι) := by
  obtain ⟨clockBound, hclock⟩ := hclock
  let canonical :=
    quittingStoppingLawCanonicalizeOn reward profile Finset.univ
  obtain ⟨hbound, hsemantic⟩ :=
    finiteClock_canonicalized_deadlineBounded_and_semantic_eq
      reward profile clockBound hclock
  let minimumDebt := quittingTerminalSemanticDebtSum
    (quittingTerminalSemanticPair reward profile)
  have hminimumCanonical : ∀ candidate ∈
      quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward canonical) ≤
        quittingTerminalSemanticDebtSum candidate := by
    intro candidate hcandidate
    rw [hsemantic]
    exact hminimum candidate hcandidate
  have hpositiveCanonical : 0 < quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPair reward canonical) := by
    rw [hsemantic]
    exact hpositive
  have hpositiveMinimum : 0 < minimumDebt := hpositive
  rcases deadlineBoundedMinimum_purify_or_offMinimum_with_step_bound
      reward canonical clockBound hbound hminimumCanonical hpositiveCanonical with
    ⟨times, steps, hsteps, hchain, hdebt, hminimumTimes⟩ |
      ⟨target, targetBound, steps, hsteps, hchain, htargetBound, hoff⟩
  · have hdebtMinimum : quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward
          (quittingPureTimeProfileBehavior reward times)) = minimumDebt := by
      rw [hdebt, hsemantic]
    have hlower : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
        minimumDebt ≤ quittingTerminalSemanticDebtSum candidate := by
      intro candidate hcandidate
      exact hminimum candidate hcandidate
    let port := Classical.choice
      (exists_pureTimeDescentPaidPort reward minimumDebt hlower
        hpositiveMinimum times hdebtMinimum)
    refine ⟨clockBound, hclock, hbound, hsemantic, ?_⟩
    exact QuittingFiniteClockMinimumPaidPortReduction.canonicalDescent
      times steps hsteps (by
        simpa only [minimumDebt, canonical, hsemantic] using hchain)
      hdebtMinimum hlower port
  · have hoffMinimum : minimumDebt < quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward target) := by
      simpa only [minimumDebt, canonical, hsemantic] using hoff
    obtain ⟨port, hportProfile, hportDeadline⟩ :=
      exists_deadlineBoundedExactPaidPort reward minimumDebt hpositiveMinimum
        target targetBound htargetBound hoffMinimum
    subst hportProfile
    subst hportDeadline
    refine ⟨clockBound, hclock, hbound, hsemantic, ?_⟩
    exact QuittingFiniteClockMinimumPaidPortReduction.purificationExit
      port steps hsteps (by
        simpa only [minimumDebt, canonical, hsemantic] using hchain)


end GameTheory
