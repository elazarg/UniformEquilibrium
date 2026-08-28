/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors.
-/

import UniformEquilibrium.Diagnostics.Quitting.StoppingLaw.TerminalSemanticStoppingLawMinimumFiberAffine
import UniformEquilibrium.Diagnostics.Quitting.StoppingLaw.PositiveMinimumDebtTangentFamily
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticBoundedSelfReset
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticResetIncidenceCapReturn
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticResetIncidenceRatio
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticSelfTailClosure

/-!
# Minimum response chords in the joint terminal-law carrier

This file isolates the source-independent part of the response-chord construction.
It proves the exact finite-date law screen, the executable one-player chord
identities, and the minimum-fibre debt/support geometry of every joint cluster.

The inputs are actual profiles and literal subsequences.  No source regeneration,
rank iteration, or uniform-equilibrium conclusion is asserted here.
-/

noncomputable section

namespace GameTheory

open Filter Set
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## A complete-law prefix screen -/

/-- Updating the same player by the same pure-time strategy preserves live-root
agreement at every date where the underlying profiles agree. -/
theorem quittingProfileLiveRoot_update_pureTime_eq_of_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (first second : (quittingGame reward).BehaviorProfile)
    (who : ι) (choice : Option ℕ) (time : ℕ)
    (hroot : quittingProfileLiveRoot reward first time =
      quittingProfileLiveRoot reward second time) :
    quittingProfileLiveRoot reward
        (Function.update first who
          (quittingPureTimeBehaviorStrategy reward who choice)) time =
      quittingProfileLiveRoot reward
        (Function.update second who
          (quittingPureTimeBehaviorStrategy reward who choice)) time := by
  rw [quittingProfileLiveRoot_update_eq_rootSequenceUpdate,
    quittingProfileLiveRoot_update_eq_rootSequenceUpdate]
  unfold quittingRootSequenceUpdate
  rw [hroot]

/-- If two profiles have the same live roots strictly before a cutoff, then a
common pure response strictly before that cutoff makes their complete terminal
laws equal.  This includes the `Never` coordinate. -/
theorem quittingTerminalOutcomeMass_update_pureTime_eq_of_liveRoot_eq_before
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (first second : (quittingGame reward).BehaviorProfile)
    (who : ι) (stop cutoff : ℕ) (hstop : stop < cutoff)
    (hroot : ∀ time < cutoff,
      quittingProfileLiveRoot reward first time =
        quittingProfileLiveRoot reward second time) :
    quittingTerminalOutcomeMass reward
        (Function.update first who
          (quittingPureTimeBehaviorStrategy reward who (some stop))) =
      quittingTerminalOutcomeMass reward
        (Function.update second who
          (quittingPureTimeBehaviorStrategy reward who (some stop))) := by
  funext outcome
  cases outcome with
  | none =>
      rw [quittingTerminalOutcomeMass_none_eq_zero_of_pureTimePlayer
          reward _ who stop (by simp),
        quittingTerminalOutcomeMass_none_eq_zero_of_pureTimePlayer
          reward _ who stop (by simp)]
  | some terminal =>
      by_cases hmem : who ∈ terminal.val
      · rw [quittingTerminalOutcomeMass_update_pureTime_some_mem_eq_at
            reward first who stop terminal hmem,
          quittingTerminalOutcomeMass_update_pureTime_some_mem_eq_at
            reward second who stop terminal hmem]
        apply quittingStageCoalitionMass_eq_of_liveRoot_eq_of_le
        intro time htime
        apply quittingProfileLiveRoot_update_pureTime_eq_of_eq
        exact hroot time (htime.trans_lt hstop)
      · rw [quittingTerminalOutcomeMass_update_pureTime_some_notMem_eq_before
            reward first who stop terminal hmem,
          quittingTerminalOutcomeMass_update_pureTime_some_notMem_eq_before
            reward second who stop terminal hmem]
        apply Finset.sum_congr rfl
        intro time htime
        apply quittingStageCoalitionMass_eq_of_liveRoot_eq_of_le
        intro date hdate
        apply quittingProfileLiveRoot_update_pureTime_eq_of_eq
        exact hroot date (hdate.trans_lt (Finset.mem_range.mp htime) |>.trans hstop)

/-- A nonzero complete-law rectangle atom excludes a finite response strictly
before the unique marked disagreement. -/
theorem responseAtom_pos_imp_pureTime_ge_mark
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source endpoint : (quittingGame reward).BehaviorProfile)
    (observer : ι) (choice : Option ℕ) (mark : ℕ)
    (atom : {S : Finset ι // S.Nonempty}) (eta : ℝ)
    (heta : 0 < eta)
    (hroot : ∀ time < mark,
      quittingProfileLiveRoot reward source time =
        quittingProfileLiveRoot reward endpoint time)
    (hatom : eta ≤
      (quittingTerminalOutcomeMass reward
          (Function.update endpoint observer
            (quittingPureTimeBehaviorStrategy reward observer choice))
          (some atom) -
        quittingTerminalOutcomeMass reward
          (Function.update source observer
            (quittingPureTimeBehaviorStrategy reward observer choice))
          (some atom)) * reward atom observer) :
    ∀ stop, choice = some stop → mark ≤ stop := by
  intro stop hchoice
  subst choice
  by_contra hnot
  have hlt : stop < mark := Nat.lt_of_not_ge hnot
  have hlaw := congrFun
    (quittingTerminalOutcomeMass_update_pureTime_eq_of_liveRoot_eq_before
      reward source endpoint observer stop mark hlt hroot) (some atom)
  rw [hlaw, sub_self, zero_mul] at hatom
  exact (not_lt_of_ge hatom) heta

/-! ## No-loss routing at an at-or-after-mark pure response -/

/-- Up to a finite pure stopping time, or for the `Never` response, replacing
one player by the pure-time strategy removes that player's factors from the
live-mass product.  Thus the new live mass is exactly the opponents' survival
weight. -/
theorem quittingLiveMass_update_pureTime_eq_opponentSurvivalWeight_of_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (who : ι) (choice : Option ℕ) (stage : ℕ)
    (hchoice : ∀ stop, choice = some stop → stage ≤ stop) :
    quittingLiveMass reward
        (Function.update profile who
          (quittingPureTimeBehaviorStrategy reward who choice)) stage =
      quittingOpponentSurvivalWeight
        (quittingProfileLiveRoot reward profile) who 0 stage := by
  rw [quittingLiveMass_eq_jointSurvivalWeight_profileLiveRoot,
    quittingJointSurvivalWeight_eq_prod]
  unfold quittingOpponentSurvivalWeight
  simp only [Nat.zero_add]
  apply Finset.prod_congr rfl
  intro offset hoffset
  have hoffsetLt : offset < stage := Finset.mem_range.mp hoffset
  change quittingStationaryContinueMass
      (quittingProfileLiveRoot reward
        (Function.update profile who
          (quittingPureTimeBehaviorStrategy reward who choice)) offset) =
    quittingFixedOpponentsContinueMass
      (quittingProfileLiveRoot reward profile) who offset
  rw [quittingProfileLiveRoot_update_eq_rootSequenceUpdate,
    quittingBehaviorLiveHazard_pureTimeBehaviorStrategy]
  unfold quittingRootSequenceUpdate quittingFixedOpponentsContinueMass
  cases choice with
  | none => rw [quittingPureTimeHazard_none]
  | some stop =>
      rw [quittingPureTimeHazard_some_of_ne
        (ne_of_lt (hoffsetLt.trans_le (hchoice stop rfl)))]

/-- The pure-time hazard at a displayed row is the pure Boolean mode saying
whether the finite stopping time is exactly that row. -/
theorem quittingPureTimeHazard_eq_pure_responseMode
    (choice : Option ℕ) (stage : ℕ) :
    quittingPureTimeHazard choice stage = PMF.pure
      (match choice with
      | some stop => decide (stop = stage)
      | none => false) := by
  cases choice with
  | none => simp
  | some stop =>
      by_cases hstop : stop = stage
      · subst stop
        simp
      · rw [quittingPureTimeHazard_some_of_ne (Ne.symm hstop)]
        simp [hstop]

/-- A pure-time response at or after the marked row cannot lose the marked
coalition's unconditional mass: the selected player's earlier survival factor
is removed, and its marked action routes the old coalition cylinder to the
matching pure cylinder. -/
theorem quittingStageCoalitionMass_le_update_pureTime_routed
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (who : ι) (choice : Option ℕ) (stage : ℕ)
    (terminal : {S : Finset ι // S.Nonempty}) (action : Bool)
    (hchoice : ∀ stop, choice = some stop → stage ≤ stop)
    (haction : quittingPureTimeHazard choice stage = PMF.pure action)
    (hrouted :
      (quittingPureEndpointRoutedCoalition terminal.val who action).Nonempty) :
    quittingStageCoalitionMass reward profile stage terminal ≤
      quittingStageCoalitionMass reward
        (Function.update profile who
          (quittingPureTimeBehaviorStrategy reward who choice)) stage
        ⟨quittingPureEndpointRoutedCoalition terminal.val who action,
          hrouted⟩ := by
  rw [quittingStageCoalitionMass_eq_liveMass_mul_rootCoalitionMass,
    quittingStageCoalitionMass_eq_liveMass_mul_rootCoalitionMass]
  have hlive : quittingLiveMass reward profile stage ≤
      quittingLiveMass reward
        (Function.update profile who
          (quittingPureTimeBehaviorStrategy reward who choice)) stage := by
    rw [quittingLiveMass_update_pureTime_eq_opponentSurvivalWeight_of_le
      reward profile who choice stage hchoice,
      quittingLiveMass_eq_jointSurvivalWeight_profileLiveRoot]
    exact quittingJointSurvivalWeight_le_quittingOpponentSurvivalWeight
      (quittingProfileLiveRoot reward profile) who 0 stage
  have hroot : quittingProfileLiveRoot reward
      (Function.update profile who
        (quittingPureTimeBehaviorStrategy reward who choice)) stage =
      Function.update (quittingProfileLiveRoot reward profile stage) who
        (PMF.pure action) := by
    rw [quittingProfileLiveRoot_update_eq_rootSequenceUpdate]
    unfold quittingRootSequenceUpdate
    rw [quittingBehaviorLiveHazard_pureTimeBehaviorStrategy, haction]
  rw [hroot]
  exact mul_le_mul hlive
    (quittingRootCoalitionMass_le_pureEndpointRouted
      (quittingProfileLiveRoot reward profile stage) terminal.val who action)
    (MarkedAbsorptionCylinder.quittingRootCoalitionMass_nonneg _ _)
    (quittingLiveMass_nonneg reward _ _)

/-! ## Executable one-player response chords -/

/-- Mix only `observer`'s complete stopping laws between two actual profiles. -/
def quittingResponseChordProfile
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (endpoint response : (quittingGame reward).BehaviorProfile)
    (observer : ι) (theta : ℝ) (htheta0 : 0 ≤ theta) (htheta1 : theta ≤ 1) :
    (quittingGame reward).BehaviorProfile :=
  Function.update endpoint observer
    (quittingStoppingLawMixtureBehaviorStrategy reward observer
      (endpoint observer) (response observer) theta htheta0 htheta1)

/-- If the response changes only `observer`, the response endpoint is exactly
the full endpoint of the stopping-law chord. -/
theorem update_endpoint_with_response_observer_eq_response
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (endpoint response : (quittingGame reward).BehaviorProfile)
    (observer : ι)
    (hopponents : ∀ other, other ≠ observer →
      response other = endpoint other) :
    Function.update endpoint observer (response observer) = response := by
  funext other
  by_cases hother : other = observer
  · subst other
    simp
  · rw [Function.update_of_ne hother]
    exact (hopponents other hother).symm

/-- The complete terminal law of the executable response chord is exactly
the affine chord of the two endpoint laws. -/
theorem quittingTerminalOutcomeMass_responseChord_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (endpoint response : (quittingGame reward).BehaviorProfile)
    (observer : ι) (theta : ℝ) (htheta0 : 0 ≤ theta) (htheta1 : theta ≤ 1)
    (hopponents : ∀ other, other ≠ observer →
      response other = endpoint other) (outcome : QuittingTerminalOutcome ι) :
    quittingTerminalOutcomeMass reward
        (quittingResponseChordProfile reward endpoint response observer theta
          htheta0 htheta1) outcome =
      (1 - theta) * quittingTerminalOutcomeMass reward endpoint outcome +
        theta * quittingTerminalOutcomeMass reward response outcome := by
  have haffine := quittingTerminalOutcomeMass_stoppingLawMixture_eq
    reward endpoint observer (endpoint observer) (response observer)
      theta htheta0 htheta1 outcome
  rw [Function.update_eq_self,
    update_endpoint_with_response_observer_eq_response reward endpoint response
      observer hopponents] at haffine
  exact haffine

/-- Every debt coordinate of an executable response chord lies below the
corresponding endpoint chord. -/
theorem quittingTerminalSemanticDebt_responseChord_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (endpoint response : (quittingGame reward).BehaviorProfile)
    (observer who : ι) (theta : ℝ)
    (htheta0 : 0 ≤ theta) (htheta1 : theta ≤ 1)
    (hopponents : ∀ other, other ≠ observer →
      response other = endpoint other) :
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (quittingResponseChordProfile reward endpoint response observer theta
            htheta0 htheta1)) who ≤
      (1 - theta) * quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward endpoint) who +
        theta * quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward response) who := by
  have hconvex := quittingTerminalSemanticDebt_stoppingLawMixture_le
    reward endpoint observer who (endpoint observer) (response observer)
      theta htheta0 htheta1
  rw [Function.update_eq_self,
    update_endpoint_with_response_observer_eq_response reward endpoint response
      observer hopponents] at hconvex
  exact hconvex

/-- Every prescribed payoff coordinate is exactly affine along the executable
response chord. -/
theorem quittingTerminalPayoff_responseChord_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (endpoint response : (quittingGame reward).BehaviorProfile)
    (observer who : ι) (theta : ℝ)
    (htheta0 : 0 ≤ theta) (htheta1 : theta ≤ 1)
    (hopponents : ∀ other, other ≠ observer →
      response other = endpoint other) :
    quittingTerminalPayoff reward
        (quittingResponseChordProfile reward endpoint response observer theta
          htheta0 htheta1) who =
      (1 - theta) * quittingTerminalPayoff reward endpoint who +
        theta * quittingTerminalPayoff reward response who := by
  have haffine := quittingTerminalPayoff_stoppingLawMixture_eq
    reward endpoint observer who (endpoint observer) (response observer)
      theta htheta0 htheta1
  rw [Function.update_eq_self,
    update_endpoint_with_response_observer_eq_response reward endpoint response
      observer hopponents] at haffine
  exact haffine

/-- Moving from a proper response chord to its full response endpoint retains
exactly the factor `1 - theta` of the original response gain. -/
theorem quittingResponseChord_fullResponseGain_eq_scale
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (endpoint response : (quittingGame reward).BehaviorProfile)
    (observer who : ι) (theta : ℝ)
    (htheta0 : 0 ≤ theta) (htheta1 : theta ≤ 1)
    (hopponents : ∀ other, other ≠ observer →
      response other = endpoint other) :
    quittingTerminalPayoff reward response who -
        quittingTerminalPayoff reward
          (quittingResponseChordProfile reward endpoint response observer theta
            htheta0 htheta1) who =
      (1 - theta) *
        (quittingTerminalPayoff reward response who -
          quittingTerminalPayoff reward endpoint who) := by
  rw [quittingTerminalPayoff_responseChord_eq reward endpoint response]
  · ring
  · exact hopponents

/-- Mixing the two vertical edges of a response rectangle scales its signed
cross-difference by exactly `1 - theta`. -/
theorem quittingResponseChord_crossDifference_eq_scale
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source endpoint sourceResponse endpointResponse :
      (quittingGame reward).BehaviorProfile)
    (observer : ι) (theta : ℝ)
    (htheta0 : 0 ≤ theta) (htheta1 : theta ≤ 1)
    (hsourceOpponents : ∀ other, other ≠ observer →
      sourceResponse other = source other)
    (hendpointOpponents : ∀ other, other ≠ observer →
      endpointResponse other = endpoint other) :
    (quittingTerminalPayoff reward endpointResponse observer -
        quittingTerminalPayoff reward
          (quittingResponseChordProfile reward endpoint endpointResponse
            observer theta htheta0 htheta1) observer) -
      (quittingTerminalPayoff reward sourceResponse observer -
        quittingTerminalPayoff reward
          (quittingResponseChordProfile reward source sourceResponse
            observer theta htheta0 htheta1) observer) =
      (1 - theta) *
        ((quittingTerminalPayoff reward endpointResponse observer -
            quittingTerminalPayoff reward endpoint observer) -
          (quittingTerminalPayoff reward sourceResponse observer -
            quittingTerminalPayoff reward source observer)) := by
  rw [quittingTerminalPayoff_responseChord_eq reward endpoint endpointResponse,
    quittingTerminalPayoff_responseChord_eq reward source sourceResponse]
  · ring
  · exact hsourceOpponents
  · exact hendpointOpponents

/-- The horizontal mover gain on a response chord is exactly the affine
combination of the two horizontal endpoint gains. -/
theorem quittingResponseChord_moverGain_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source endpoint sourceResponse endpointResponse :
      (quittingGame reward).BehaviorProfile)
    (observer mover : ι) (theta : ℝ)
    (htheta0 : 0 ≤ theta) (htheta1 : theta ≤ 1)
    (hsourceOpponents : ∀ other, other ≠ observer →
      sourceResponse other = source other)
    (hendpointOpponents : ∀ other, other ≠ observer →
      endpointResponse other = endpoint other) :
    quittingTerminalPayoff reward
        (quittingResponseChordProfile reward endpoint endpointResponse observer
          theta htheta0 htheta1) mover -
      quittingTerminalPayoff reward
        (quittingResponseChordProfile reward source sourceResponse observer
          theta htheta0 htheta1) mover =
      (1 - theta) *
          (quittingTerminalPayoff reward endpoint mover -
            quittingTerminalPayoff reward source mover) +
        theta *
          (quittingTerminalPayoff reward endpointResponse mover -
            quittingTerminalPayoff reward sourceResponse mover) := by
  rw [quittingTerminalPayoff_responseChord_eq reward endpoint endpointResponse,
    quittingTerminalPayoff_responseChord_eq reward source sourceResponse]
  · ring
  · exact hsourceOpponents
  · exact hendpointOpponents

omit [DecidableEq ι] in
/-- A uniformly paid horizontal edge retains half its gain on every sufficiently
short proper response chord. -/
theorem quittingResponseChord_moverGain_ge_half
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source endpoint sourceResponse endpointResponse :
      (quittingGame reward).BehaviorProfile)
    (mover : ι) (theta gap bound : ℝ)
    (htheta0 : 0 ≤ theta)
    (hgap : gap ≤ quittingTerminalPayoff reward endpoint mover -
      quittingTerminalPayoff reward source mover)
    (hgapPos : 0 < gap) (hbound0 : 0 ≤ bound)
    (hsourceResponse : |quittingTerminalPayoff reward sourceResponse mover| ≤ bound)
    (hendpointResponse :
      |quittingTerminalPayoff reward endpointResponse mover| ≤ bound)
    (htheta : theta ≤ gap / (2 * (gap + 2 * bound))) :
    gap / 2 ≤
      (1 - theta) *
          (quittingTerminalPayoff reward endpoint mover -
            quittingTerminalPayoff reward source mover) +
        theta *
          (quittingTerminalPayoff reward endpointResponse mover -
            quittingTerminalPayoff reward sourceResponse mover) := by
  have hdenom : 0 < 2 * (gap + 2 * bound) := by positivity
  have hthetaBound : theta * (gap + 2 * bound) ≤ gap / 2 := by
    have := (le_div_iff₀ hdenom).mp htheta
    nlinarith
  have hresponseLower : -2 * bound ≤
      quittingTerminalPayoff reward endpointResponse mover -
        quittingTerminalPayoff reward sourceResponse mover := by
    have hsourceLower := (neg_le_of_abs_le hsourceResponse)
    have hendpointLower := (neg_le_of_abs_le hendpointResponse)
    have hsourceUpper := (le_of_abs_le hsourceResponse)
    linarith
  have htheta1 : theta ≤ 1 := by
    apply htheta.trans
    apply (div_le_one hdenom).2
    nlinarith
  calc
    gap / 2 ≤ gap - theta * (gap + 2 * bound) := by linarith
    _ = (1 - theta) * gap + theta * (-2 * bound) := by ring
    _ ≤ (1 - theta) *
          (quittingTerminalPayoff reward endpoint mover -
            quittingTerminalPayoff reward source mover) +
        theta *
          (quittingTerminalPayoff reward endpointResponse mover -
            quittingTerminalPayoff reward sourceResponse mover) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left hgap (sub_nonneg.mpr htheta1))
        (mul_le_mul_of_nonneg_left hresponseLower htheta0)

/-! ## Minimum joint-law chord geometry -/

/-- Abstract joint-law geometry supplied by a cluster of executable response
chords.  The only analytic input retained here is the coordinatewise convex
upper bound; all equality and support conclusions are derived from minimum
total debt. -/
structure QuittingMinimumResponseChordLaw
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) where
  endpoint : QuittingTerminalSemanticLawPoint ι
  response : QuittingTerminalSemanticLawPoint ι
  chord : QuittingTerminalSemanticLawPoint ι
  theta : ℝ
  theta_pos : 0 < theta
  theta_lt_one : theta < 1
  endpoint_mem : endpoint ∈ quittingTerminalSemanticLawCarrier reward
  response_mem : response ∈ quittingTerminalSemanticLawCarrier reward
  chord_mem : chord ∈ quittingTerminalSemanticLawCarrier reward
  endpoint_minimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
    quittingTerminalSemanticDebtSum endpoint.1 ≤
      quittingTerminalSemanticDebtSum candidate
  response_debtSum_eq_endpoint :
    quittingTerminalSemanticDebtSum response.1 =
      quittingTerminalSemanticDebtSum endpoint.1
  chord_debt_le_affine : ∀ who,
    quittingTerminalSemanticDebt chord.1 who ≤
      (1 - theta) * quittingTerminalSemanticDebt endpoint.1 who +
        theta * quittingTerminalSemanticDebt response.1 who
  chord_law_eq_affine : ∀ outcome,
    chord.2 outcome = (1 - theta) * endpoint.2 outcome +
      theta * response.2 outcome

/-- The endpoint has maximum positive-debt-support cardinality among actual
minimum joint-law points carrying at least one positive finite atom.  This is
an explicit property of the displayed endpoint, not of an incoming source. -/
def IsMaximumSupportMinimumAtomEndpoint
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (endpoint : QuittingTerminalSemanticLawPoint ι) : Prop :=
  ∀ candidate : QuittingTerminalSemanticLawPoint ι,
    candidate ∈ quittingTerminalSemanticLawCarrier reward →
    quittingTerminalSemanticDebtSum candidate.1 =
      quittingTerminalSemanticDebtSum endpoint.1 →
    (∃ terminal : {S : Finset ι // S.Nonempty},
      0 < candidate.2 (some terminal)) →
    (quittingPositiveDebtSupport candidate.1).card ≤
      (quittingPositiveDebtSupport endpoint.1).card

namespace QuittingMinimumResponseChordLaw

variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- The chord remains on the same global minimum total-debt fibre. -/
theorem chord_debtSum_eq_endpoint
    (law : QuittingMinimumResponseChordLaw reward) :
    quittingTerminalSemanticDebtSum law.chord.1 =
      quittingTerminalSemanticDebtSum law.endpoint.1 := by
  have hchordCarrier :=
    terminalSemanticLawCarrier_fst_mem_carrier law.chord law.chord_mem
  have hlower := law.endpoint_minimum law.chord.1 hchordCarrier
  have hupper : quittingTerminalSemanticDebtSum law.chord.1 ≤
      (1 - law.theta) *
          quittingTerminalSemanticDebtSum law.endpoint.1 +
        law.theta * quittingTerminalSemanticDebtSum law.response.1 := by
    unfold quittingTerminalSemanticDebtSum
    calc
      ∑ who, quittingTerminalSemanticDebt law.chord.1 who ≤
          ∑ who, ((1 - law.theta) *
              quittingTerminalSemanticDebt law.endpoint.1 who +
            law.theta * quittingTerminalSemanticDebt law.response.1 who) :=
        Finset.sum_le_sum fun who _ => law.chord_debt_le_affine who
      _ = (1 - law.theta) *
            ∑ who, quittingTerminalSemanticDebt law.endpoint.1 who +
          law.theta *
            ∑ who, quittingTerminalSemanticDebt law.response.1 who := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  rw [law.response_debtSum_eq_endpoint] at hupper
  nlinarith

/-- Every debt coordinate is exactly affine on a proper minimum chord. -/
theorem chord_debt_eq_affine
    (law : QuittingMinimumResponseChordLaw reward) (who : ι) :
    quittingTerminalSemanticDebt law.chord.1 who =
      (1 - law.theta) * quittingTerminalSemanticDebt law.endpoint.1 who +
        law.theta * quittingTerminalSemanticDebt law.response.1 who := by
  let gap : ι → ℝ := fun player =>
    (1 - law.theta) * quittingTerminalSemanticDebt law.endpoint.1 player +
      law.theta * quittingTerminalSemanticDebt law.response.1 player -
        quittingTerminalSemanticDebt law.chord.1 player
  have hgapNonneg : ∀ player, 0 ≤ gap player := fun player =>
    sub_nonneg.mpr (law.chord_debt_le_affine player)
  have hgapSum : (∑ player, gap player) = 0 := by
    dsimp only [gap]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum]
    change (1 - law.theta) *
          quittingTerminalSemanticDebtSum law.endpoint.1 +
        law.theta * quittingTerminalSemanticDebtSum law.response.1 -
          quittingTerminalSemanticDebtSum law.chord.1 = 0
    rw [law.response_debtSum_eq_endpoint, law.chord_debtSum_eq_endpoint]
    ring
  have hrest : 0 ≤ ∑ player ∈ Finset.univ.erase who, gap player :=
    Finset.sum_nonneg fun player _ => hgapNonneg player
  have hsplit := Finset.sum_erase_add Finset.univ gap (Finset.mem_univ who)
  rw [hgapSum] at hsplit
  have hzero : gap who = 0 := by linarith [hgapNonneg who, hrest]
  dsimp only [gap] at hzero
  linarith

/-- Positive debt support on a proper minimum chord is exactly the union of
the endpoint supports. -/
theorem chord_support_eq_union
    (law : QuittingMinimumResponseChordLaw reward) :
    quittingPositiveDebtSupport law.chord.1 =
      quittingPositiveDebtSupport law.endpoint.1 ∪
        quittingPositiveDebtSupport law.response.1 := by
  ext who
  simp only [quittingPositiveDebtSupport, Finset.mem_filter,
    Finset.mem_univ, true_and, Finset.mem_union]
  rw [law.chord_debt_eq_affine who]
  have hendpointCarrier := terminalSemanticLawCarrier_fst_mem_carrier
    law.endpoint law.endpoint_mem
  have hresponseCarrier := terminalSemanticLawCarrier_fst_mem_carrier
    law.response law.response_mem
  have hendpointNonneg := quittingTerminalSemanticDebt_nonneg_of_mem_carrier
    reward hendpointCarrier who
  have hresponseNonneg := quittingTerminalSemanticDebt_nonneg_of_mem_carrier
    reward hresponseCarrier who
  have honeMinusPos : 0 < 1 - law.theta := sub_pos.mpr law.theta_lt_one
  constructor
  · intro hpositive
    by_contra hnone
    push Not at hnone
    rcases hnone with ⟨hendpointNot, hresponseNot⟩
    nlinarith
  · rintro (hendpointPositive | hresponsePositive)
    · exact add_pos_of_pos_of_nonneg
        (mul_pos honeMinusPos hendpointPositive)
        (mul_nonneg law.theta_pos.le hresponseNonneg)
    · exact add_pos_of_nonneg_of_pos
        (mul_nonneg honeMinusPos.le hendpointNonneg)
        (mul_pos law.theta_pos hresponsePositive)

/-- A response-law atom of mass `lambda` survives in the proper chord with
mass at least `theta * lambda`. -/
theorem theta_mul_le_chord_terminalMass
    (law : QuittingMinimumResponseChordLaw reward)
    (terminal : {S : Finset ι // S.Nonempty}) (lambda : ℝ)
    (hlambda : lambda ≤ law.response.2 (some terminal)) :
    law.theta * lambda ≤ law.chord.2 (some terminal) := by
  rw [law.chord_law_eq_affine]
  have hendpointSimplex := terminalSemanticLawCarrier_mass_mem_stdSimplex
    law.endpoint law.endpoint_mem
  have hendpointNonneg := hendpointSimplex.1 (some terminal)
  have hweightNonneg : 0 ≤ 1 - law.theta := sub_nonneg.mpr law.theta_lt_one.le
  nlinarith [mul_nonneg hweightNonneg hendpointNonneg,
    mul_le_mul_of_nonneg_left hlambda law.theta_pos.le]

/-- If the response endpoint kills a debt coordinate which is positive at
the other endpoint, its support is strictly smaller than the chord support. -/
theorem response_support_ssubset_chord_of_killed
    (law : QuittingMinimumResponseChordLaw reward) (who : ι)
    (hendpoint : 0 < quittingTerminalSemanticDebt law.endpoint.1 who)
    (hresponse : quittingTerminalSemanticDebt law.response.1 who = 0) :
    quittingPositiveDebtSupport law.response.1 ⊂
      quittingPositiveDebtSupport law.chord.1 := by
  apply Finset.ssubset_iff_subset_ne.mpr
  constructor
  · rw [law.chord_support_eq_union]
    exact Finset.subset_union_right
  · intro heq
    have hchordMem : who ∈ quittingPositiveDebtSupport law.chord.1 := by
      rw [law.chord_support_eq_union]
      exact Finset.mem_union_left _
        ((mem_quittingPositiveDebtSupport_iff law.endpoint.1 who).2 hendpoint)
    have hresponseMem : who ∈ quittingPositiveDebtSupport law.response.1 := by
      rw [heq]
      exact hchordMem
    have hpositive :=
      (mem_quittingPositiveDebtSupport_iff law.response.1 who).1 hresponseMem
    rw [hresponse] at hpositive
    exact (lt_irrefl 0) hpositive

/-- Orientation back to the other endpoint requires actual maximality of that
endpoint in the positive-atom minimum class.  Without this hypothesis the
unconditional conclusion is only `support(response) ⊊ support(chord)`. -/
theorem response_support_ssubset_endpoint_of_endpoint_maximal
    (law : QuittingMinimumResponseChordLaw reward)
    (terminal : {S : Finset ι // S.Nonempty})
    (hchordMass : 0 < law.chord.2 (some terminal))
    (hmaximal : IsMaximumSupportMinimumAtomEndpoint reward law.endpoint)
    (who : ι)
    (hendpoint : 0 < quittingTerminalSemanticDebt law.endpoint.1 who)
    (hresponse : quittingTerminalSemanticDebt law.response.1 who = 0) :
    quittingPositiveDebtSupport law.response.1 ⊂
      quittingPositiveDebtSupport law.endpoint.1 := by
  have hcard := hmaximal law.chord law.chord_mem law.chord_debtSum_eq_endpoint
    ⟨terminal, hchordMass⟩
  have hendpointSubset : quittingPositiveDebtSupport law.endpoint.1 ⊆
      quittingPositiveDebtSupport law.chord.1 := by
    rw [law.chord_support_eq_union]
    exact Finset.subset_union_left
  have hsupportEq : quittingPositiveDebtSupport law.chord.1 =
      quittingPositiveDebtSupport law.endpoint.1 := by
    exact (Finset.eq_of_subset_of_card_le hendpointSubset hcard).symm
  have hstrict := law.response_support_ssubset_chord_of_killed who
    hendpoint hresponse
  rwa [hsupportEq] at hstrict

end QuittingMinimumResponseChordLaw

end GameTheory
