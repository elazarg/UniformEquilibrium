/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.Topology.CompactExecutableTraceGrammar
import UniformEquilibrium.Diagnostics.Quitting.PureTimeScreenedMenu
import UniformEquilibrium.Quitting.Paths.FiniteStoppingLawMixture
import UniformEquilibrium.Quitting.Punishment.SingletonCapBindingCollision

/-!
# A constrained maximal-root selector with nonclosed graph

An explicit rational four-player quitting table is paired with a compact
one-parameter family of literal stopping-law sources and their checked
unrestricted continuation caps.  On the face where only
player `a` may quit, at rate at most `1 / 2`, exact root Nash is equivalent to
`q * t = 0`.  The greatest admissible rate is therefore zero for positive `t`
and `1 / 2` at `t = 0`.  Its graph is not closed, although the full exact-root
relation is closed.

The final theorems exclude exact trace-visible realization of this selector
by compact-witness, uniformly summable decoder, bounded ranked, and arbitrary
finite compositions of those constructors. They do not exclude a pointwise
choice made after one source is reconstructed, or an approximate selector.
The finite obstruction uses the literal source profile throughout: its payoff
and its cap over all behavioral deviations are both proved here before the
root and topological no-go are invoked.
-/

noncomputable section

namespace GameTheory
namespace ConstrainedMaximalRootNoGo

open Filter Set
open Math.ProbabilityMassFunction
open Math.Topology
open scoped Topology

/-- The four players in the rational obstruction. -/
inductive Player
  | a
  | b
  | c
  | d
  deriving DecidableEq, Fintype

/-- The rational terminal reward table from the obstruction. -/
def reward : {coalition : Finset Player // coalition.Nonempty} → Payoff Player :=
  fun coalition player ↦
    match player with
    | .a => if .b ∈ coalition.1 ∧ .a ∉ coalition.1 then 1 else 0
    | .b => if .b ∈ coalition.1 then -1 else if .a ∈ coalition.1 then 1 else 0
    | .c => if .c ∈ coalition.1 then -1 else 0
    | .d => if .d ∈ coalition.1 then -1 else 0

/-- The unrestricted continuation-cap vector of the source indexed by `t`.
Its equality with the literal profile's all-behavior best-response envelope is
proved below. -/
def sourceCap (t : ℝ) : Payoff Player
  | .a => t
  | .b => 0
  | .c => 0
  | .d => 0

/-- The prescribed payoff vector of the stopping-law source from the packet.
Its equality with the literal profile's terminal payoff is proved below. -/
def sourcePayoff (t : ℝ) : Payoff Player
  | .a => t
  | .b => -t
  | .c => 0
  | .d => 0

/-- The literal source profile: only `b` has a nontrivial stopping law, with
mass `t` at date one and the remaining mass at `Never`. -/
def sourceProfile (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (quittingGame reward).BehaviorProfile :=
  Function.update (quittingAlwaysContinueProfile reward) .b
    (quittingStoppingLawMixtureBehaviorStrategy reward .b
      (quittingPureTimeBehaviorStrategy reward .b none)
      (quittingPureTimeBehaviorStrategy reward .b (some 1)) t ht0 ht1)

/-- The whole compact source family is obtained from the one fixed
all-Continue source by one displayed unilateral stopping-law replacement. -/
theorem sourceProfile_eq_elementaryReplacement
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    sourceProfile t ht0 ht1 =
      Function.update (quittingAlwaysContinueProfile reward) .b
        (quittingStoppingLawMixtureBehaviorStrategy reward .b
          (quittingPureTimeBehaviorStrategy reward .b none)
          (quittingPureTimeBehaviorStrategy reward .b (some 1)) t ht0 ht1) :=
  rfl

/-- Player `b`'s complete induced stopping law is the displayed mixture of
Never and the deterministic date-one law. -/
theorem sourceProfile_b_stoppingLaw
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    quittingBehaviorStoppingLaw reward (sourceProfile t ht0 ht1 .b) =
      (Math.Probability.DiscreteHazard.mixtureCoin t ht0 ht1).bind
        (fun choose => if choose
        then quittingBehaviorStoppingLaw reward
          (quittingPureTimeBehaviorStrategy reward .b (some 1))
        else quittingBehaviorStoppingLaw reward
          (quittingPureTimeBehaviorStrategy reward .b none)) := by
  rw [sourceProfile]
  simp only [Function.update_self]
  exact quittingBehaviorStoppingLaw_stoppingLawMixture reward .b
    (quittingPureTimeBehaviorStrategy reward .b none)
    (quittingPureTimeBehaviorStrategy reward .b (some 1)) t ht0 ht1

/-- At parameter zero, the source is the fixed all-Continue profile. -/
theorem sourceProfile_zero :
    sourceProfile 0 (by norm_num) (by norm_num) =
      quittingAlwaysContinueProfile reward := by
  funext player time history
  cases player with
  | a => rfl
  | b =>
      change Math.Probability.DiscreteHazard.BooleanHazard.convexMix
          (quittingPureTimeHazard none) (quittingPureTimeHazard (some 1))
          0 (by norm_num) (by norm_num) time = PMF.pure false
      simp [Math.Probability.DiscreteHazard.BooleanHazard.convexMix,
        Math.Probability.DiscreteHazard.ScalarHazard.convexMix,
        Math.Probability.DiscreteHazard.ScalarHazard.mixedStopMass,
        Math.Probability.DiscreteHazard.ScalarHazard.mixedSurvival,
        Math.Probability.DiscreteHazard.ScalarHazard.toBoolean,
        Math.Probability.DiscreteHazard.BooleanHazard.toScalar,
        Math.Probability.DiscreteHazard.ScalarHazard.stopMass,
        Math.Probability.DiscreteHazard.ScalarHazard.survival,
        Math.Probability.DiscreteHazard.stopProbability,
        Math.survivalProduct,
        Math.Probability.DiscreteHazard.booleanCoin]
      apply PMF.ext
      intro stop
      cases stop <;> simp [PMF.ofFintype_apply]
  | c => rfl
  | d => rfl

/-- Deterministic endpoint of the source mixture: only `b` quits, at date one. -/
def bDeadlineTimes : QuittingPureTimeProfile Player
  | .b => some 1
  | _ => none

/-- The deterministic `b`-deadline endpoint as a behavior profile. -/
def bDeadlineProfile : (quittingGame reward).BehaviorProfile :=
  quittingPureTimeProfileBehavior reward bDeadlineTimes

private theorem bDeadlineProfile_eq_update_alwaysContinue :
    bDeadlineProfile =
      Function.update (quittingAlwaysContinueProfile reward) .b
        (quittingPureTimeBehaviorStrategy reward .b (some 1)) := by
  funext player time history
  cases player <;> rfl

private theorem bDeadline_opponentCoalition_zero (who : Player) :
    quittingPureTimeOpponentCoalitionAt bDeadlineTimes who 0 = ∅ := by
  ext player
  cases player <;>
    simp [bDeadlineTimes, quittingPureTimeOpponentCoalitionAt,
      quittingPureTimeCoalitionAt]

private theorem bDeadline_opponentCoalition_one_of_ne_b
    {who : Player} (hwho : who ≠ .b) :
    quittingPureTimeOpponentCoalitionAt bDeadlineTimes who 1 = {.b} := by
  ext player
  cases player <;>
    simp [bDeadlineTimes, quittingPureTimeOpponentCoalitionAt,
      quittingPureTimeCoalitionAt]

private theorem terminalPayoff_update_alwaysContinue_b_some_one
    (observer : Player) :
    quittingTerminalPayoff reward
        (Function.update (quittingAlwaysContinueProfile reward) .b
          (quittingPureTimeBehaviorStrategy reward .b (some 1))) observer =
      reward (quittingSingletonTerminal .b) observer := by
  rw [← quittingTerminalPayoff_observerReward reward _ observer .b]
  change quittingTerminalPayoff (quittingObserverReward reward observer)
      (Function.update
        (quittingAlwaysContinueProfile (quittingObserverReward reward observer)) .b
        (quittingPureTimeBehaviorStrategy
          (quittingObserverReward reward observer) .b (some 1))) .b = _
  rw [quittingTerminalPayoff_update_pureTimeBehaviorStrategy]
  have hroots : quittingProfileLiveRoot
      (quittingObserverReward reward observer)
      (quittingAlwaysContinueProfile (quittingObserverReward reward observer)) =
        fun _ => quittingAllContinueRoot := by
    funext time player
    rfl
  rw [hroots]
  rw [quittingRootSequencePureTimeTerminalValue_some_eq]
  have hupdate (hazard : PMF Bool) :
      Function.update quittingAllContinueRoot Player.b hazard =
        quittingSoloStationaryRoot Player.b hazard := by
    funext player
    by_cases hplayer : player = Player.b
    · subst player
      simp [quittingSoloStationaryRoot]
    · simp [quittingAllContinueRoot, quittingSoloStationaryRoot,
        hplayer]
  simp [quittingLiveLedgerAccum, quittingOpponentSurvivalWeight,
    quittingFixedOpponentsContinueReward,
    quittingFixedOpponentsContinueMass,
    quittingFixedOpponentsQuitValue, hupdate,
    quittingRootAbsorbingContribution_solo,
    quittingStationaryContinueMass_solo,
    quittingSoloReward, quittingObserverReward,
    quittingSingletonTerminal]

private theorem update_alwaysContinue_b_none :
    Function.update (quittingAlwaysContinueProfile reward) .b
        (quittingPureTimeBehaviorStrategy reward .b none) =
      quittingAlwaysContinueProfile reward := by
  funext player time history
  by_cases hplayer : player = Player.b
  · subst player
    rfl
  · simp [Function.update_of_ne hplayer]

/-- The literal source profile has prescribed payoff `(t,-t,0,0)`. -/
theorem sourceProfile_terminalPayoff_eq_sourcePayoff
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    quittingTerminalPayoff reward (sourceProfile t ht0 ht1) =
      sourcePayoff t := by
  funext observer
  rw [sourceProfile,
    quittingTerminalPayoff_update_stoppingLawMixture_observer_eq]
  rw [update_alwaysContinue_b_none,
    quittingTerminalPayoff_quittingAlwaysContinue,
    terminalPayoff_update_alwaysContinue_b_some_one]
  cases observer <;>
    simp [reward, sourcePayoff, quittingSingletonTerminal]

private theorem bDeadlineProfile_cap
    (who : Player) :
    quittingContinuationBestResponseValue reward bDeadlineProfile who =
      match who with
      | .a => 1
      | .b => 0
      | .c => 0
      | .d => 0 := by
  cases who with
  | b =>
      rw [bDeadlineProfile_eq_update_alwaysContinue,
        quittingContinuationBestResponseValue_update_self,
        quittingContinuationBestResponseValue_quittingAlwaysContinueProfile]
      norm_num [reward, quittingSingletonTerminal]
  | a =>
      rw [bDeadlineProfile,
        quittingContinuationBestResponseValue_pureTimeProfile_eq_max_three
          reward bDeadlineTimes .a 1 (by norm_num)]
      · simp +decide [bDeadline_opponentCoalition_one_of_ne_b, reward]
      · intro time htime
        interval_cases time
        exact bDeadline_opponentCoalition_zero .a
      · rw [bDeadline_opponentCoalition_one_of_ne_b (by decide)]
        simp

  | c =>
      rw [bDeadlineProfile,
        quittingContinuationBestResponseValue_pureTimeProfile_eq_max_three
          reward bDeadlineTimes .c 1 (by norm_num)]
      · simp +decide [bDeadline_opponentCoalition_one_of_ne_b, reward]
      · intro time htime
        interval_cases time
        exact bDeadline_opponentCoalition_zero .c
      · rw [bDeadline_opponentCoalition_one_of_ne_b (by decide)]
        simp

  | d =>
      rw [bDeadlineProfile,
        quittingContinuationBestResponseValue_pureTimeProfile_eq_max_three
          reward bDeadlineTimes .d 1 (by norm_num)]
      · simp +decide [bDeadline_opponentCoalition_one_of_ne_b, reward]
      · intro time htime
        interval_cases time
        exact bDeadline_opponentCoalition_zero .d
      · rw [bDeadline_opponentCoalition_one_of_ne_b (by decide)]
        simp

private theorem terminalPayoff_update_sourceProfile_eq_mix
    {who : Player} (hwho : who ≠ .b)
    (deviation : (quittingGame reward).BehaviorStrategy who)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    quittingTerminalPayoff reward
        (Function.update (sourceProfile t ht0 ht1) who deviation) who =
      (1 - t) * quittingTerminalPayoff reward
          (Function.update (quittingAlwaysContinueProfile reward) who deviation)
          who +
        t * quittingTerminalPayoff reward
          (Function.update bDeadlineProfile who deviation) who := by
  let mixed := quittingStoppingLawMixtureBehaviorStrategy reward Player.b
    (quittingPureTimeBehaviorStrategy reward .b none)
    (quittingPureTimeBehaviorStrategy reward .b (some 1)) t ht0 ht1
  have haffine :=
    quittingTerminalPayoff_update_stoppingLawMixture_observer_eq reward
      (Function.update (quittingAlwaysContinueProfile reward) who deviation)
      .b who (quittingPureTimeBehaviorStrategy reward .b none)
      (quittingPureTimeBehaviorStrategy reward .b (some 1)) t ht0 ht1
  have hcommuteMixed :
      Function.update
          (Function.update (quittingAlwaysContinueProfile reward) who deviation)
          .b mixed =
        Function.update (sourceProfile t ht0 ht1) who deviation := by
    simpa only [mixed, sourceProfile] using
      Function.update_comm hwho deviation mixed
        (quittingAlwaysContinueProfile reward)
  have hcommuteNever :
      Function.update
          (Function.update (quittingAlwaysContinueProfile reward) who deviation)
          .b (quittingPureTimeBehaviorStrategy reward .b none) =
        Function.update (quittingAlwaysContinueProfile reward) who deviation := by
    rw [Function.update_comm hwho, update_alwaysContinue_b_none]
  have hcommuteDeadline :
      Function.update
          (Function.update (quittingAlwaysContinueProfile reward) who deviation)
          .b (quittingPureTimeBehaviorStrategy reward .b (some 1)) =
        Function.update bDeadlineProfile who deviation := by
    rw [Function.update_comm hwho, bDeadlineProfile_eq_update_alwaysContinue]
  change quittingTerminalPayoff reward
      (Function.update
        (Function.update (quittingAlwaysContinueProfile reward) who deviation)
        .b mixed) who = _ at haffine
  rwa [hcommuteMixed, hcommuteNever, hcommuteDeadline] at haffine

/-- The literal stopping-law source has unrestricted behavioral best-response
cap `(t, 0, 0, 0)`.  The supremum ranges over every behavioral deviation. -/
theorem sourceProfile_continuationBestResponseValue_eq_sourceCap
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    quittingContinuationBestResponseValue reward (sourceProfile t ht0 ht1) =
      sourceCap t := by
  funext who
  cases who with
  | b =>
      rw [sourceProfile,
        quittingContinuationBestResponseValue_update_self,
        quittingContinuationBestResponseValue_quittingAlwaysContinueProfile]
      norm_num [reward, sourceCap, quittingSingletonTerminal]
  | a =>
      apply le_antisymm
      · unfold quittingContinuationBestResponseValue
        apply csSup_le
        · exact Set.range_nonempty _
        · rintro value ⟨deviation, rfl⟩
          change quittingTerminalPayoff reward
              (Function.update (sourceProfile t ht0 ht1) .a deviation) .a ≤ _
          rw [terminalPayoff_update_sourceProfile_eq_mix
            (who := .a) (by decide)]
          have hnever :=
            quittingTerminalPayoff_update_le_continuationBestResponseValue
              reward (quittingAlwaysContinueProfile reward) .a deviation
          rw [quittingContinuationBestResponseValue_quittingAlwaysContinueProfile]
            at hnever
          norm_num [reward, quittingSingletonTerminal] at hnever
          have hdeadline :=
            quittingTerminalPayoff_update_le_continuationBestResponseValue
              reward bDeadlineProfile .a deviation
          rw [bDeadlineProfile_cap] at hdeadline
          change (1 - t) * _ + t * _ ≤ t
          nlinarith
      · have hlower :=
          quittingTerminalPayoff_update_le_continuationBestResponseValue
            reward (sourceProfile t ht0 ht1) .a (sourceProfile t ht0 ht1 .a)
        rw [Function.update_eq_self,
          congrFun (sourceProfile_terminalPayoff_eq_sourcePayoff t ht0 ht1) .a]
          at hlower
        simpa [sourcePayoff, sourceCap] using hlower
  | c =>
      apply le_antisymm
      · unfold quittingContinuationBestResponseValue
        apply csSup_le
        · exact Set.range_nonempty _
        · rintro value ⟨deviation, rfl⟩
          change quittingTerminalPayoff reward
              (Function.update (sourceProfile t ht0 ht1) .c deviation) .c ≤ _
          rw [terminalPayoff_update_sourceProfile_eq_mix
            (who := .c) (by decide)]
          have hnever :=
            quittingTerminalPayoff_update_le_continuationBestResponseValue
              reward (quittingAlwaysContinueProfile reward) .c deviation
          rw [quittingContinuationBestResponseValue_quittingAlwaysContinueProfile]
            at hnever
          norm_num [reward, quittingSingletonTerminal] at hnever
          have hdeadline :=
            quittingTerminalPayoff_update_le_continuationBestResponseValue
              reward bDeadlineProfile .c deviation
          rw [bDeadlineProfile_cap] at hdeadline
          change (1 - t) * _ + t * _ ≤ 0
          nlinarith
      · have hlower :=
          quittingTerminalPayoff_update_le_continuationBestResponseValue
            reward (sourceProfile t ht0 ht1) .c (sourceProfile t ht0 ht1 .c)
        rw [Function.update_eq_self,
          congrFun (sourceProfile_terminalPayoff_eq_sourcePayoff t ht0 ht1) .c]
          at hlower
        simpa [sourcePayoff, sourceCap] using hlower
  | d =>
      apply le_antisymm
      · unfold quittingContinuationBestResponseValue
        apply csSup_le
        · exact Set.range_nonempty _
        · rintro value ⟨deviation, rfl⟩
          change quittingTerminalPayoff reward
              (Function.update (sourceProfile t ht0 ht1) .d deviation) .d ≤ _
          rw [terminalPayoff_update_sourceProfile_eq_mix
            (who := .d) (by decide)]
          have hnever :=
            quittingTerminalPayoff_update_le_continuationBestResponseValue
              reward (quittingAlwaysContinueProfile reward) .d deviation
          rw [quittingContinuationBestResponseValue_quittingAlwaysContinueProfile]
            at hnever
          norm_num [reward, quittingSingletonTerminal] at hnever
          have hdeadline :=
            quittingTerminalPayoff_update_le_continuationBestResponseValue
              reward bDeadlineProfile .d deviation
          rw [bDeadlineProfile_cap] at hdeadline
          change (1 - t) * _ + t * _ ≤ 0
          nlinarith
      · have hlower :=
          quittingTerminalPayoff_update_le_continuationBestResponseValue
            reward (sourceProfile t ht0 ht1) .d (sourceProfile t ht0 ht1 .d)
        rw [Function.update_eq_self,
          congrFun (sourceProfile_terminalPayoff_eq_sourcePayoff t ht0 ht1) .d]
          at hlower
        simpa [sourcePayoff, sourceCap] using hlower

/-- The fixed constrained face: only `a` may quit, with rate `q`. -/
def faceRoot (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) : Player → PMF Bool :=
  quittingSoloStationaryRoot .a (bernoulliBool q hq0 hq1)

/-- The actual child profile obtained by prefixing the literal source by the
displayed constrained root. -/
def prefixedSourceProfile
    (t q : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    (quittingGame reward).BehaviorProfile :=
  quittingRootThenContinuationProfile reward (faceRoot q hq0 hq1)
    (sourceProfile t ht0 ht1)

/-- The actual child retains the literal source as its declared continuation;
there is no source switch hidden in the finite semantic calculation. -/
theorem prefixedSourceProfile_eq_rootThenLiteralSource
    (t q : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    prefixedSourceProfile t q ht0 ht1 hq0 hq1 =
      quittingRootThenContinuationProfile reward (faceRoot q hq0 hq1)
        (sourceProfile t ht0 ht1) :=
  rfl

/-- The constrained face continues to the literal source with mass `1 - q`. -/
theorem faceRoot_continueMass_eq
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    quittingStationaryContinueMass (faceRoot q hq0 hq1) = 1 - q := by
  rw [faceRoot, quittingStationaryContinueMass_solo,
    bernoulliBool_false_toReal]

/-- Every root on the constrained half-face has continuation reach at least
`1 / 2`; the selector discontinuity is not a vanishing-reach effect. -/
theorem faceRoot_continueMass_ge_half
    (q : ℝ) (hq0 : 0 ≤ q) (hqHalf : q ≤ 1 / 2) :
    1 / 2 ≤ quittingStationaryContinueMass
      (faceRoot q hq0 (hqHalf.trans (by norm_num))) := by
  rw [faceRoot_continueMass_eq]
  linarith

/-- Player `b`'s prescribed one-root continuation trace is
`q - (1 - q) * t`. -/
theorem faceRoot_successor_sourcePayoff_b
    (t q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    quittingRootSuccessorPayoff reward (sourcePayoff t)
        (faceRoot q hq0 hq1) .b = q - (1 - q) * t := by
  rw [faceRoot, quittingRootSuccessorPayoff_solo]
  simp [sourcePayoff, reward, quittingSoloReward,
    bernoulliBool_true_toReal, bernoulliBool_false_toReal]
  ring

/-- Player `b`'s one-root continuation trace against the checked unrestricted
source cap is exactly `q`. -/
theorem faceRoot_successor_sourceCap_b
    (t q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    quittingRootSuccessorPayoff reward (sourceCap t)
        (faceRoot q hq0 hq1) .b = q := by
  rw [faceRoot, quittingRootSuccessorPayoff_solo]
  simp [sourceCap, reward, quittingSoloReward,
    bernoulliBool_true_toReal, bernoulliBool_false_toReal]

/-- The actual prefixed child has player `b`'s prescribed trace
`q - (1 - q) * t`. -/
theorem prefixedSourceProfile_terminalPayoff_b
    (t q : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    quittingTerminalPayoff reward
        (prefixedSourceProfile t q ht0 ht1 hq0 hq1) .b =
      q - (1 - q) * t := by
  rw [prefixedSourceProfile,
    quittingTerminalPayoff_rootThenContinuation_eq]
  change quittingRootSuccessorPayoff reward
      (quittingTerminalPayoff reward (sourceProfile t ht0 ht1))
      (faceRoot q hq0 hq1) .b = _
  rw [sourceProfile_terminalPayoff_eq_sourcePayoff,
    faceRoot_successor_sourcePayoff_b]

/-- The actual prefixed child's unrestricted behavioral cap for player `b`
is exactly `q`. -/
theorem prefixedSourceProfile_continuationBestResponseValue_b
    (t q : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    quittingContinuationBestResponseValue reward
        (prefixedSourceProfile t q ht0 ht1 hq0 hq1) .b = q := by
  rw [prefixedSourceProfile,
    quittingContinuationBestResponseValue_rootThenContinuation_eq_max,
    sourceProfile_terminalPayoff_eq_sourcePayoff,
    sourceProfile_continuationBestResponseValue_eq_sourceCap]
  have htail : Function.update (sourcePayoff t) .b (sourceCap t .b) =
      sourceCap t := by
    funext player
    cases player <;> simp [sourcePayoff, sourceCap]
  rw [htail]
  have hquit : quittingRootQuitPayoff reward (sourcePayoff t)
      (faceRoot q hq0 hq1) .b = -1 := by
    rw [faceRoot,
      quittingRootQuitPayoff_soloStationaryRoot_other reward
        (by decide : Player.b ≠ Player.a)]
    simp [reward, quittingSoloReward, quittingSingletonCollisionReward,
      bernoulliBool_true_toReal, bernoulliBool_false_toReal]
    ring
  have hcontinue : quittingRootContinuePayoff reward (sourceCap t)
      (faceRoot q hq0 hq1) .b = q := by
    rw [faceRoot,
      quittingRootContinuePayoff_soloStationaryRoot_other reward
        (by decide : Player.b ≠ Player.a)]
    simp [reward, sourceCap, quittingSoloReward,
      bernoulliBool_true_toReal, bernoulliBool_false_toReal]
  rw [hquit, hcontinue, max_eq_right]
  linarith

/-- The selected child at the limiting source and half root is literally
different from the zero-root child. -/
theorem prefixedSourceProfile_zero_half_ne_zero :
    prefixedSourceProfile 0 (1 / 2) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) ≠
      prefixedSourceProfile 0 0 (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) := by
  intro heq
  have hpayoff := congrArg
    (fun profile => quittingTerminalPayoff reward profile .b) heq
  rw [prefixedSourceProfile_terminalPayoff_b,
    prefixedSourceProfile_terminalPayoff_b] at hpayoff
  norm_num at hpayoff

private theorem singletonCapDefect_a (t : ℝ) :
    quittingSingletonCapDefect reward (sourceCap t) .a = t := by
  simp [quittingSingletonCapDefect, quittingSingletonTerminal, reward, sourceCap]

private theorem endpointDifference_a
    (t q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    quittingRootEndpointDifference reward (sourceCap t)
        (faceRoot q hq0 hq1) .a = -t := by
  rw [faceRoot, quittingRootEndpointDifference_soloStationaryRoot_owner_cap,
    singletonCapDefect_a]

private theorem endpointDifference_b
    (t q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    quittingRootEndpointDifference reward (sourceCap t)
        (faceRoot q hq0 hq1) .b = -q - 1 := by
  rw [faceRoot, quittingRootEndpointDifference_soloStationaryRoot_other_cap
    reward (sourceCap t) (by decide : Player.b ≠ Player.a)]
  norm_num [quittingSingletonCollisionGain, quittingSingletonCapDefect,
    quittingSingletonCollisionReward, quittingSoloReward,
    quittingSingletonTerminal, reward, sourceCap,
    show Player.b ≠ Player.a by decide]
  ring

private theorem endpointDifference_c
    (t q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    quittingRootEndpointDifference reward (sourceCap t)
        (faceRoot q hq0 hq1) .c = -1 := by
  rw [faceRoot, quittingRootEndpointDifference_soloStationaryRoot_other_cap
    reward (sourceCap t) (by decide : Player.c ≠ Player.a)]
  norm_num [quittingSingletonCollisionGain, quittingSingletonCapDefect,
    quittingSingletonCollisionReward, quittingSoloReward,
    quittingSingletonTerminal, reward, sourceCap,
    show Player.c ≠ Player.a by decide]
  ring

private theorem endpointDifference_d
    (t q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    quittingRootEndpointDifference reward (sourceCap t)
        (faceRoot q hq0 hq1) .d = -1 := by
  rw [faceRoot, quittingRootEndpointDifference_soloStationaryRoot_other_cap
    reward (sourceCap t) (by decide : Player.d ≠ Player.a)]
  norm_num [quittingSingletonCollisionGain, quittingSingletonCapDefect,
    quittingSingletonCollisionReward, quittingSoloReward,
    quittingSingletonTerminal, reward, sourceCap,
    show Player.d ≠ Player.a by decide]
  ring

/-- On the displayed nonnegative face, exact root Nash is exactly `q * t = 0`.
This is a literal finite root theorem against the actual source's checked
unrestricted cap. -/
theorem faceRoot_isZeroNash_iff_mul_eq_zero
    {t q : ℝ} (ht0 : 0 ≤ t) (hq0 : 0 ≤ q) (hqHalf : q ≤ 1 / 2) :
    IsεQuittingRootNash reward (sourceCap t) 0
        (faceRoot q hq0 (hqHalf.trans (by norm_num))) ↔
      q * t = 0 := by
  rw [← isεQuittingRootEndpointNash_iff_isεQuittingRootNash]
  constructor
  · intro hnash
    have ha := (hnash .a).2
    rw [endpointDifference_a] at ha
    simp [faceRoot, bernoulliBool_true_toReal] at ha
    nlinarith [mul_nonneg hq0 ht0]
  · intro hmul player
    cases player with
    | a =>
        rw [endpointDifference_a]
        simp [faceRoot, bernoulliBool_true_toReal,
          bernoulliBool_false_toReal]
        constructor
        · exact mul_nonneg (sub_nonneg.mpr <| by linarith) ht0
        · nlinarith
    | b =>
        rw [endpointDifference_b]
        simp [faceRoot, quittingSoloStationaryRoot,
          show Player.b ≠ Player.a by decide]
        nlinarith
    | c =>
        rw [endpointDifference_c]
        simp [faceRoot, quittingSoloStationaryRoot,
          show Player.c ≠ Player.a by decide]
    | d =>
        rw [endpointDifference_d]
        simp [faceRoot, quittingSoloStationaryRoot,
          show Player.d ≠ Player.a by decide]

/-- The exact constrained root relation against the literal source family. -/
def exactRootRelation : Set (ℝ × ℝ) :=
  {point | point.1 ∈ Icc (0 : ℝ) 1 ∧
    point.2 ∈ Icc (0 : ℝ) (1 / 2) ∧ point.2 * point.1 = 0}

/-- On the displayed compact rectangle, membership in `exactRootRelation` is
literally the checked exact root-Nash condition against `sourceCap`. -/
theorem mem_exactRootRelation_iff_isZeroNash
    {t q : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hq0 : 0 ≤ q) (hqHalf : q ≤ 1 / 2) :
    (t, q) ∈ exactRootRelation ↔
      IsεQuittingRootNash reward (sourceCap t) 0
        (faceRoot q hq0 (hqHalf.trans (by norm_num))) := by
  rw [faceRoot_isZeroNash_iff_mul_eq_zero ht0 hq0 hqHalf]
  simp only [exactRootRelation, mem_setOf_eq, mem_Icc, ht0, ht1, hq0,
    hqHalf, and_self, true_and]

/-- The full exact-root relation is closed. -/
theorem exactRootRelation_isClosed : IsClosed exactRootRelation := by
  have hfirst : IsClosed
      {point : ℝ × ℝ | point.1 ∈ Icc (0 : ℝ) 1} :=
    isClosed_Icc.preimage continuous_fst
  have hsecond : IsClosed
      {point : ℝ × ℝ | point.2 ∈ Icc (0 : ℝ) (1 / 2)} :=
    isClosed_Icc.preimage continuous_snd
  have hzero : IsClosed
      {point : ℝ × ℝ | point.2 * point.1 = 0} :=
    isClosed_eq (continuous_snd.mul continuous_fst) continuous_const
  exact hfirst.inter (hsecond.inter hzero)

/-- The greatest exact root on the fixed face. -/
def greatestFaceRoot (t : ℝ) : ℝ :=
  if t = 0 then 1 / 2 else 0

/-- The selected graph, including its compact source interval. -/
def greatestFaceRootGraph : Set (ℝ × ℝ) :=
  {point | point.1 ∈ Icc (0 : ℝ) 1 ∧ point.2 = greatestFaceRoot point.1}

theorem greatestFaceRoot_mem_exactRootRelation
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (t, greatestFaceRoot t) ∈ exactRootRelation := by
  by_cases hzero : t = 0
  · subst t
    norm_num [exactRootRelation, greatestFaceRoot]
  · refine ⟨ht, ?_, ?_⟩
    · simp [greatestFaceRoot, hzero]
    · simp [greatestFaceRoot, hzero]

theorem exactRootRelation_le_greatestFaceRoot
    {t q : ℝ} (hroot : (t, q) ∈ exactRootRelation) :
    q ≤ greatestFaceRoot t := by
  by_cases hzero : t = 0
  · simpa [greatestFaceRoot, hzero] using hroot.2.1.2
  · have hq : q = 0 := (mul_eq_zero.mp hroot.2.2).resolve_right hzero
    simp [greatestFaceRoot, hzero, hq]

/-- `greatestFaceRoot` really is the unique greatest member of every fiber. -/
theorem greatestFaceRoot_isGreatest
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    IsGreatest {q | (t, q) ∈ exactRootRelation} (greatestFaceRoot t) := by
  exact ⟨greatestFaceRoot_mem_exactRootRelation ht,
    fun _ hroot ↦ exactRootRelation_le_greatestFaceRoot hroot⟩

private def positiveSourceSequence (n : ℕ) : ℝ :=
  1 / ((n : ℝ) + 1)

private theorem positiveSourceSequence_pos (n : ℕ) :
    0 < positiveSourceSequence n := by
  dsimp [positiveSourceSequence]
  exact one_div_pos.mpr (by positivity)

private theorem positiveSourceSequence_le_one (n : ℕ) :
    positiveSourceSequence n ≤ 1 := by
  dsimp [positiveSourceSequence]
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < n + 1)]
  norm_num

private theorem positiveSourceSequence_tendsto_zero :
    Tendsto positiveSourceSequence atTop (nhds 0) := by
  unfold positiveSourceSequence
  simpa only [one_div] using
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

/-- The exact maximal-root graph is not closed: the selected roots along
`t = 1 / (n + 1)` converge to zero, while the selected root at zero is
`1 / 2`. -/
theorem greatestFaceRootGraph_not_isClosed :
    ¬IsClosed greatestFaceRootGraph := by
  intro hclosed
  have hmem : ∀ n,
      (positiveSourceSequence n, (0 : ℝ)) ∈ greatestFaceRootGraph := by
    intro n
    have hne : positiveSourceSequence n ≠ 0 :=
      ne_of_gt (positiveSourceSequence_pos n)
    exact ⟨⟨(positiveSourceSequence_pos n).le,
      positiveSourceSequence_le_one n⟩, by simp [greatestFaceRoot, hne]⟩
  have htendsto : Tendsto
      (fun n ↦ (positiveSourceSequence n, (0 : ℝ))) atTop
      (nhds ((0 : ℝ), (0 : ℝ))) :=
    positiveSourceSequence_tendsto_zero.prodMk_nhds tendsto_const_nhds
  have hlimit := hclosed.mem_of_tendsto htendsto (Eventually.of_forall hmem)
  norm_num [greatestFaceRootGraph, greatestFaceRoot] at hlimit

/-- A compact carrier with a continuous visible pair cannot have exactly the
nonclosed selected-root graph as its visible image. -/
theorem no_compact_continuous_exact_greatestFaceRootGraph
    {Code : Type*} [TopologicalSpace Code]
    (codeSet : Set Code) (hcompact : IsCompact codeSet)
    (visible : Code → ℝ × ℝ) (hvisible : ContinuousOn visible codeSet) :
    visible '' codeSet ≠ greatestFaceRootGraph := by
  intro heq
  apply greatestFaceRootGraph_not_isClosed
  rw [← heq]
  exact (hcompact.image_of_continuousOn hvisible).isClosed

/-- No compact proof-relevant adapter can expose exactly the maximal-root
graph, even after retaining and then forgetting an arbitrary compact witness. -/
theorem no_compactWitnessAdapter_exact_greatestFaceRootGraph
    {Witness Label Child : Type*}
    [TopologicalSpace Witness] [TopologicalSpace Label] [TopologicalSpace Child]
    (adapter : CompactProofRelevantAdapter ℝ Witness Label Child)
    (readRoot : Label → ℝ) (hreadRoot : Continuous readRoot) :
    (fun output ↦ (output.1, readRoot output.2.1)) '' adapter.visibleSet ≠
      greatestFaceRootGraph := by
  apply no_compact_continuous_exact_greatestFaceRootGraph
    adapter.visibleSet adapter.isCompact_visibleSet
  exact continuous_fst.prodMk
    (hreadRoot.comp (continuous_fst.comp continuous_snd)) |>.continuousOn

/-- No uniformly summable decoder can expose exactly the maximal-root graph
through its decoded state and decoded visible coordinate. -/
theorem no_summableDecoder_exact_greatestFaceRootGraph
    {Code Certificate : Type*}
    [TopologicalSpace Code] [TopologicalSpace Certificate]
    (decoder : SummableExecutableDecoder Code ℝ ℝ Certificate) :
    Set.range (fun code : decoder.CodePoint ↦
      (decoder.decodedState code, decoder.decodedVisible code)) ≠
        greatestFaceRootGraph := by
  letI : CompactSpace decoder.CodePoint :=
    isCompact_iff_compactSpace.mp decoder.code_compact
  intro heq
  apply greatestFaceRootGraph_not_isClosed
  rw [← heq]
  exact (isCompact_range <|
    decoder.continuous_decodedState.prodMk
      decoder.continuous_decodedVisible).isClosed

/-- No bounded trace-visible ranked adapter can expose exactly the selected
graph as its complete bounded outcome relation. -/
theorem no_boundedRankAdapter_exact_greatestFaceRootGraph
    {TerminalCertificate SuccessorCertificate : Type*}
    [TopologicalSpace TerminalCertificate]
    [TopologicalSpace SuccessorCertificate]
    (adapter : CompactRankedOutcomeAdapter ℝ TerminalCertificate
      SuccessorCertificate ℝ) :
    adapter.outcomeUpTo adapter.rankBound ≠ greatestFaceRootGraph := by
  intro heq
  apply greatestFaceRootGraph_not_isClosed
  rw [← heq]
  exact adapter.isClosed_outcomeUpTo adapter.rankBound

/-- No execution of the complete interpreted grammar can expose exactly the
maximal-root graph through a continuous visible map. This single theorem
covers compact witnesses, summable decoders, finite closed cases, bounded
ranks, and every finite composition of those constructors. -/
theorem no_executableTrace_exact_greatestFaceRootGraph
    (trace : ExecutableTrace ℝ)
    (visible : trace.evaluate.Execution → ℝ × ℝ)
    (hvisible : @Continuous trace.evaluate.Execution (ℝ × ℝ)
      trace.evaluate.executionTopology inferInstance visible) :
    Set.range visible ≠ greatestFaceRootGraph := by
  letI : TopologicalSpace trace.evaluate.Execution :=
    trace.evaluate.executionTopology
  letI : CompactSpace trace.evaluate.Execution :=
    trace.evaluate.executionCompact
  intro heq
  apply greatestFaceRootGraph_not_isClosed
  rw [← heq]
  exact (isCompact_range hvisible).isClosed

end ConstrainedMaximalRootNoGo
end GameTheory
