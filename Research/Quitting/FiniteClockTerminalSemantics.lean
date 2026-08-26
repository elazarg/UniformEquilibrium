/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Classification.Existence.StationarilyGeneratedSemanticCarrier
import UniformEquilibrium.Quitting.Paths.SureExitSet
import UniformEquilibrium.Quitting.Root.TerminalSemanticPrefixMetric
import UniformEquilibrium.Quitting.Root.TerminalSemanticEqualityStratum
import UniformEquilibrium.Quitting.Terminal.OpponentTightTerminalSemanticRealization
import UniformEquilibrium.Quitting.Terminal.StrategicallyPrecompactWatchdogProperBoundary

/-!
# Literal finite-clock terminal semantics

This module owns exact independent stopping-law reconstruction for quitting
games, its finite-word presentation, deterministic terminal-payoff formulas,
and the compact set of literal finite-clock semantic pairs. The Never atom is
retained literally, and every cap coordinate remains the unrestricted
behavioral envelope from quittingTerminalSemanticPair.
-/

noncomputable section

namespace GameTheory

open Filter Set Math.Probability Math.ProbabilityMassFunction Math.PMFProduct Math.Topology
open QuittingBoundaryHolonomy
open QuittingSureSetOwnerRepair
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A complete stopping law supported on the first `clockBound` finite dates,
with `none` retained as an additional exact atom. -/
def IsFiniteClockStoppingLaw (clockBound : ℕ)
    (law : PMF (Option ℕ)) : Prop :=
  ∀ choice, law choice ≠ 0 →
    choice = none ∨ ∃ time < clockBound, choice = some time

/-- Literal profile reconstructed independently from one complete stopping law
per player. -/
def quittingStoppingLawProfile
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (laws : ι → PMF (Option ℕ)) :
    (quittingGame reward).BehaviorProfile :=
  fun who => quittingStoppingLawBehaviorStrategy reward who (laws who)

omit [DecidableEq ι] in
@[simp] theorem quittingBehaviorStoppingLaw_stoppingLawProfile
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (laws : ι → PMF (Option ℕ)) (who : ι) :
    quittingBehaviorStoppingLaw reward
        (quittingStoppingLawProfile reward laws who) = laws who := by
  exact quittingBehaviorStoppingLaw_stoppingLawBehaviorStrategy
    reward who (laws who)

/-- Semantic pairs realized by independent finite-clock stopping laws.  Their
second coordinate remains the literal supremum over all behavioral
deviations. -/
def quittingFiniteClockSemanticReachable
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (clockBound : ℕ) : Set (QuittingTerminalSemanticPair ι) :=
  {pair | ∃ laws : ι → PMF (Option ℕ),
    (∀ who, IsFiniteClockStoppingLaw clockBound (laws who)) ∧
    pair = quittingTerminalSemanticPair reward
      (quittingStoppingLawProfile reward laws)}

theorem isFiniteClockStoppingLaw_mono
    {first second : ℕ} (hbound : first ≤ second)
    {law : PMF (Option ℕ)}
    (hlaw : IsFiniteClockStoppingLaw first law) :
    IsFiniteClockStoppingLaw second law := by
  intro choice hchoice
  rcases hlaw choice hchoice with hnever | ⟨time, htime, rfl⟩
  · exact Or.inl hnever
  · exact Or.inr ⟨time, htime.trans_le hbound, rfl⟩

theorem quittingFiniteClockSemanticReachable_mono
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {first second : ℕ} (hbound : first ≤ second) :
    quittingFiniteClockSemanticReachable reward first ⊆
      quittingFiniteClockSemanticReachable reward second := by
  rintro pair ⟨laws, hlaws, rfl⟩
  exact ⟨laws, fun who =>
    isFiniteClockStoppingLaw_mono hbound (hlaws who), rfl⟩

theorem isFiniteClockStoppingLaw_pure_never (clockBound : ℕ) :
    IsFiniteClockStoppingLaw clockBound (PMF.pure none) := by
  intro choice hchoice
  by_cases hnever : choice = none
  · exact Or.inl hnever
  · exfalso
    simp [PMF.pure_apply, hnever] at hchoice

theorem quittingFiniteClockSemanticReachable_nonempty
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (clockBound : ℕ) :
    (quittingFiniteClockSemanticReachable reward clockBound).Nonempty := by
  let laws : ι → PMF (Option ℕ) := fun _ => PMF.pure none
  exact ⟨quittingTerminalSemanticPair reward
      (quittingStoppingLawProfile reward laws),
    laws, fun _ => isFiniteClockStoppingLaw_pure_never clockBound, rfl⟩

theorem quittingFiniteClockSemanticReachable_subset_attainable
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (clockBound : ℕ) :
    quittingFiniteClockSemanticReachable reward clockBound ⊆
      quittingAttainableTerminalSemanticPairs reward := by
  rintro pair ⟨laws, -, rfl⟩
  exact ⟨quittingStoppingLawProfile reward laws, rfl⟩

theorem quittingFiniteClockSemanticReachable_subset_carrier
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (clockBound : ℕ) :
    quittingFiniteClockSemanticReachable reward clockBound ⊆
      quittingTerminalSemanticCarrier reward :=
  (quittingFiniteClockSemanticReachable_subset_attainable
    reward clockBound).trans subset_closure

/-! ## Compact finite-word presentation -/

/-- Product-root word of length `clockBound`, followed literally by
all-Continue. -/
def quittingFiniteClockRoots (clockBound : ℕ)
    (word : Fin clockBound → QuittingRootSimplex ι) :
    ℕ → ι → PMF Bool :=
  fun time => if htime : time < clockBound then
    quittingRootOfSimplex (word ⟨time, htime⟩)
  else quittingAllContinueRoot

/-- Literal profile generated by a finite product-root word and an exact
all-Continue suffix. -/
def quittingFiniteClockWordProfile
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (clockBound : ℕ) (word : Fin clockBound → QuittingRootSimplex ι) :
    (quittingGame reward).BehaviorProfile :=
  quittingRootSequenceProfile reward
    (quittingFiniteClockRoots clockBound word) 0

/-- Recursive semantic fold of a finite product-root word, starting from the
literal all-Continue terminal semantic pair. -/
def quittingFiniteClockSemanticFold
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    (clockBound : ℕ) →
      (Fin clockBound → QuittingRootSimplex ι) →
      QuittingTerminalSemanticPair ι
  | 0, _ => quittingTerminalSemanticPair reward
      (quittingAlwaysContinueProfile reward)
  | clockBound + 1, word =>
      quittingTerminalSemanticPrefixSimplex reward
        (word 0, quittingFiniteClockSemanticFold reward clockBound
          (fun time => word time.succ))

omit [DecidableEq ι] in
@[simp] theorem quittingFiniteClockRoots_zero
    (word : Fin 0 → QuittingRootSimplex ι) :
    quittingFiniteClockRoots 0 word =
      fun _ => (quittingAllContinueRoot : ι → PMF Bool) := by
  funext time
  simp [quittingFiniteClockRoots]

omit [DecidableEq ι] in
theorem quittingFiniteClockRoots_succ_shift
    (clockBound : ℕ)
    (word : Fin (clockBound + 1) → QuittingRootSimplex ι) (time : ℕ) :
    quittingFiniteClockRoots (clockBound + 1) word (time + 1) =
      quittingFiniteClockRoots clockBound (fun index => word index.succ) time := by
  by_cases htime : time < clockBound
  · simp only [quittingFiniteClockRoots,
      dif_pos (Nat.succ_lt_succ htime), dif_pos htime]
    congr 2
  · have hsucc : ¬time + 1 < clockBound + 1 := by omega
    simp [quittingFiniteClockRoots, htime, hsucc]

omit [DecidableEq ι] in
theorem quittingRootSequenceProfile_finiteClockRoots_succ_tail
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (clockBound : ℕ)
    (word : Fin (clockBound + 1) → QuittingRootSimplex ι) :
    quittingRootSequenceProfile reward
        (quittingFiniteClockRoots (clockBound + 1) word) 1 =
      quittingFiniteClockWordProfile reward clockBound
        (fun time => word time.succ) := by
  funext player time history
  change quittingFiniteClockRoots (clockBound + 1) word (1 + time) player =
    quittingFiniteClockRoots clockBound (fun index => word index.succ)
      (0 + time) player
  simp only [Nat.zero_add]
  rw [show 1 + time = time + 1 by omega,
    quittingFiniteClockRoots_succ_shift]

theorem quittingTerminalSemanticPair_finiteClockWordProfile_eq_fold
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    ∀ (clockBound : ℕ)
      (word : Fin clockBound → QuittingRootSimplex ι),
      quittingTerminalSemanticPair reward
          (quittingFiniteClockWordProfile reward clockBound word) =
        quittingFiniteClockSemanticFold reward clockBound word := by
  intro clockBound
  induction clockBound with
  | zero =>
      intro word
      have hprofile : quittingFiniteClockWordProfile reward 0 word =
          quittingAlwaysContinueProfile reward := by
        funext player time history
        simp [quittingFiniteClockWordProfile, quittingRootSequenceProfile,
          quittingFiniteClockRoots, quittingAlwaysContinueProfile,
          quittingAllContinueRoot, StochasticGame.stationaryBehaviorProfile]
        rfl
      simp [quittingFiniteClockSemanticFold, hprofile]
  | succ clockBound ih =>
      intro word
      rw [quittingFiniteClockWordProfile,
        quittingRootSequenceProfile_eq_rootThenContinuation,
        quittingTerminalSemanticPair_rootThenContinuation]
      rw [quittingRootSequenceProfile_finiteClockRoots_succ_tail,
        ih]
      rfl

theorem continuous_quittingFiniteClockSemanticFold
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    ∀ clockBound,
      Continuous (quittingFiniteClockSemanticFold reward clockBound) := by
  intro clockBound
  induction clockBound with
  | zero => exact continuous_const
  | succ clockBound ih =>
      have hhead : Continuous (fun word :
          Fin (clockBound + 1) → QuittingRootSimplex ι => word 0) :=
        continuous_apply 0
      have htailWord : Continuous (fun word :
          Fin (clockBound + 1) → QuittingRootSimplex ι =>
            fun time : Fin clockBound => word time.succ) := by
        apply continuous_pi
        intro time
        exact continuous_apply time.succ
      exact (continuous_quittingTerminalSemanticPrefixSimplex reward).comp
        (hhead.prodMk (ih.comp htailWord))

omit [DecidableEq ι] in
theorem quittingFiniteClockRoots_eq_allContinue_of_le
    (clockBound : ℕ) (word : Fin clockBound → QuittingRootSimplex ι)
    {time : ℕ} (htime : clockBound ≤ time) :
    quittingFiniteClockRoots clockBound word time = quittingAllContinueRoot := by
  simp [quittingFiniteClockRoots, Nat.not_lt.mpr htime]

omit [DecidableEq ι] in
theorem quittingFiniteClockWordProfile_stoppingLaw_isFinite
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (clockBound : ℕ) (word : Fin clockBound → QuittingRootSimplex ι)
    (who : ι) :
    IsFiniteClockStoppingLaw clockBound
      (quittingBehaviorStoppingLaw reward
        (quittingFiniteClockWordProfile reward clockBound word who)) := by
  intro choice hchoice
  cases choice with
  | none => exact Or.inl rfl
  | some time =>
      by_cases htime : time < clockBound
      · exact Or.inr ⟨time, htime, rfl⟩
      · exfalso
        have hroot : quittingBehaviorLiveHazard reward
            (quittingFiniteClockWordProfile reward clockBound word who) time =
            PMF.pure false := by
          change (quittingProfileLiveRoot reward
            (quittingFiniteClockWordProfile reward clockBound word) time) who = _
          rw [quittingFiniteClockWordProfile,
            quittingProfileLiveRoot_quittingRootSequenceProfile_zero]
          rw [quittingFiniteClockRoots_eq_allContinue_of_le
            clockBound word (Nat.le_of_not_gt htime)]
          rfl
        have hreal : (quittingBehaviorStoppingLaw reward
            (quittingFiniteClockWordProfile reward clockBound word who)
            (some time)).toReal = 0 := by
          rw [quittingBehaviorStoppingLaw_some_toReal,
            quittingHazardStopMass_eq_survival_mul_stop, hroot]
          simp
        rcases (ENNReal.toReal_eq_zero_iff _).mp hreal with hzero | htop
        · exact hchoice hzero
        · exact (PMF.apply_ne_top _ _ htop).elim

/-- Canonical reconstruction from a profile's complete stopping laws leaves
its terminal semantic pair unchanged. -/
theorem quittingTerminalSemanticPair_eq_stoppingLawProfile
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) :
    quittingTerminalSemanticPair reward profile =
      quittingTerminalSemanticPair reward
        (quittingStoppingLawProfile reward fun who =>
          quittingBehaviorStoppingLaw reward (profile who)) := by
  have hprofiles :
      quittingCompactStoppingLawProfile reward
          (quittingCompactStoppingLawsOfProfile reward profile) =
        quittingStoppingLawProfile reward (fun who =>
          quittingBehaviorStoppingLaw reward (profile who)) := by
    funext who
    simp [quittingCompactStoppingLawProfile,
      quittingCompactStoppingLawsOfProfile, quittingStoppingLawProfile]
  rw [← hprofiles]
  exact quittingTerminalSemanticPair_eq_compactStoppingLawsOfProfile
    reward profile

/-- Every deterministic deviation payoff is unchanged by canonical
reconstruction of all opponent stopping laws. -/
theorem quittingTerminalPayoff_update_pureTime_eq_stoppingLawProfile
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (who : ι) (choice : Option ℕ) :
    quittingTerminalPayoff reward
        (Function.update profile who
          (quittingPureTimeBehaviorStrategy reward who choice)) who =
      quittingTerminalPayoff reward
        (Function.update
          (quittingStoppingLawProfile reward fun player =>
            quittingBehaviorStoppingLaw reward (profile player)) who
          (quittingPureTimeBehaviorStrategy reward who choice)) who := by
  have hprofile : quittingCompactStoppingLawProfile reward
        (quittingCompactStoppingLawsOfProfile reward profile) =
      quittingStoppingLawProfile reward (fun player =>
        quittingBehaviorStoppingLaw reward (profile player)) := by
    funext player
    simp [quittingCompactStoppingLawProfile,
      quittingCompactStoppingLawsOfProfile, quittingStoppingLawProfile]
  rw [← hprofile]
  exact quittingTerminalPayoff_update_pureTime_eq_compactStoppingLawsOfProfile
    reward profile who choice

/-- A profile reconstructed from discrete complete stopping laws has the same
payoff as the independent expectation over deterministic stopping-time
profiles. -/
theorem quittingTerminalPayoff_stoppingLawProfile_eq_expect
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (laws : ι → PMF (Option ℕ)) (observer : ι) :
    quittingTerminalPayoff reward
        (quittingStoppingLawProfile reward laws) observer =
      Math.Probability.expect (pmfPi laws) fun choices =>
        quittingTerminalPayoff reward
          (quittingPureStoppingTimeProfile reward choices) observer := by
  have hprofile : quittingCompactStoppingLawProfile reward
      (fun who => Math.Probability.CompactStoppingLaw.ofPMF (laws who)) =
      quittingStoppingLawProfile reward laws := by
    funext who
    simp [quittingCompactStoppingLawProfile, quittingStoppingLawProfile]
  rw [← hprofile]
  convert quittingTerminalPayoff_compactStoppingLawProfile_eq_expect
    reward (fun who => Math.Probability.CompactStoppingLaw.ofPMF (laws who))
    observer using 1
  apply congrArg (fun joint => Math.Probability.expect joint fun choices =>
    quittingTerminalPayoff reward
      (quittingPureStoppingTimeProfile reward choices) observer)
  apply congrArg pmfPi
  funext who
  simp

/-- Replace one discrete complete stopping law by a deterministic finite date
or Never. -/
def quittingPureDeviationStoppingLaws
    (laws : ι → PMF (Option ℕ)) (who : ι) (choice : Option ℕ) :
    ι → PMF (Option ℕ) :=
  fun player => if player = who then PMF.pure choice else laws player

/-- A pure-time deviation against a discrete stopping-law reconstruction is
the independent expectation with that player's clock fixed. -/
theorem quittingTerminalPayoff_update_stoppingLawProfile_pureTime_eq_expect
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (laws : ι → PMF (Option ℕ)) (who : ι) (choice : Option ℕ)
    (observer : ι) :
    quittingTerminalPayoff reward
        (Function.update (quittingStoppingLawProfile reward laws) who
          (quittingPureTimeBehaviorStrategy reward who choice)) observer =
      Math.Probability.expect
        (pmfPi (quittingPureDeviationStoppingLaws laws who choice))
        (fun choices => quittingTerminalPayoff reward
          (quittingPureStoppingTimeProfile reward choices) observer) := by
  let compactLaws := fun player =>
    Math.Probability.CompactStoppingLaw.ofPMF (laws player)
  have hprofile : quittingCompactStoppingLawProfile reward compactLaws =
      quittingStoppingLawProfile reward laws := by
    funext player
    simp [compactLaws, quittingCompactStoppingLawProfile,
      quittingStoppingLawProfile]
  rw [← hprofile]
  convert
    quittingTerminalPayoff_update_compactStoppingLawProfile_pureTime_eq_expect
      reward compactLaws who choice observer using 1
  apply congrArg (fun joint => Math.Probability.expect joint fun choices =>
    quittingTerminalPayoff reward
      (quittingPureStoppingTimeProfile reward choices) observer)
  apply congrArg pmfPi
  funext player
  by_cases hplayer : player = who
  · subst player
    simp [quittingPureDeviationStoppingLaws,
      quittingPureDeviationCompactLaws, compactLaws]
    rfl
  · simp [quittingPureDeviationStoppingLaws,
      quittingPureDeviationCompactLaws, compactLaws, hplayer]

/-- A root sequence that first reaches a nonempty pure quitting set at one
specified date pays exactly that set's terminal reward. -/
theorem quittingRootSequenceTerminalValue_eq_setReward_of_first_pureSet
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (coalition : Finset ι) (hcoalition : coalition.Nonempty)
    (first : ℕ)
    (hbefore : ∀ time < first,
      roots time = (quittingAllContinueRoot : ι → PMF Bool))
    (hfirst : roots first = quittingPureSetRoot coalition) :
    quittingRootSequenceTerminalValue reward roots who 0 =
      quittingSetReward reward coalition who := by
  induction first generalizing roots with
  | zero =>
      rw [quittingRootSequenceTerminalValue_eq_rootSuccessorPayoff,
        hfirst, quittingRootSuccessorPayoff,
        quittingRootExpectedPayoff_eq_absorbingContribution_add,
        quittingRootAbsorbingContribution_pureSetRoot,
        stationaryContinueMass_pureSetRoot_of_nonempty hcoalition,
        zero_mul, add_zero]
  | succ first ih =>
      have hroot : roots 0 =
          (quittingAllContinueRoot : ι → PMF Bool) :=
        hbefore 0 (Nat.zero_lt_succ first)
      rw [quittingRootSequenceTerminalValue_eq_rootSuccessorPayoff, hroot,
        quittingRootSuccessorPayoff_allContinueRoot_eq,
        quittingRootSequenceTerminalValue_eq_shift]
      apply ih (fun time => roots (1 + time))
      · intro time htime
        apply hbefore
        omega
      · simpa only [Nat.add_comm] using hfirst

/-- At each date, a deterministic stopping-time profile is the pure root
formed by the players whose clocks equal that date. -/
theorem quittingPureStoppingTimeProfile_root_eq_pureSetRoot
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (choices : ι → Option ℕ) (time : ℕ) :
    quittingProfileLiveRoot reward
        (quittingPureStoppingTimeProfile reward choices) time =
      quittingPureSetRoot
        (Finset.univ.filter fun who => choices who = some time) := by
  funext who
  simp only [quittingProfileLiveRoot_pureStoppingTimeProfile]
  cases hchoice : choices who with
  | none => simp [quittingPureSetRoot, quittingSetAction,
      quittingPureTimeHazard, hchoice]
  | some quitTime =>
      by_cases heq : time = quitTime
      · subst quitTime
        simp [quittingPureSetRoot, quittingSetAction,
          quittingPureTimeHazard, hchoice]
      · have hne : quitTime ≠ time := Ne.symm heq
        simp [quittingPureSetRoot, quittingSetAction,
          quittingPureTimeHazard, hchoice, heq, hne]

/-- A deterministic stopping-time profile with earliest finite date `first`
pays the reward of the coalition tied at that date. -/
theorem quittingTerminalPayoff_pureStoppingTimeProfile_eq_firstCoalition
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (choices : ι → Option ℕ) (observer : ι) (first : ℕ)
    (hfirst : (Finset.univ.filter fun who =>
      choices who = some first).Nonempty)
    (hbefore : ∀ time < first, ∀ who, choices who ≠ some time) :
    quittingTerminalPayoff reward
        (quittingPureStoppingTimeProfile reward choices) observer =
      quittingSetReward reward
        (Finset.univ.filter fun who => choices who = some first) observer := by
  rw [quittingTerminalPayoff_eq_rootSequence_profileLiveRoot]
  apply quittingRootSequenceTerminalValue_eq_setReward_of_first_pureSet
    reward _ observer _ hfirst first
  · intro time htime
    rw [quittingPureStoppingTimeProfile_root_eq_pureSetRoot]
    have hempty : (Finset.univ.filter fun who =>
        choices who = some time) = ∅ := by
      ext who
      simp [hbefore time htime who]
    rw [hempty, quittingPureSetRoot_empty]
    rfl
  · exact quittingPureStoppingTimeProfile_root_eq_pureSetRoot
      reward choices first

omit [DecidableEq ι] in
/-- Literal all-Never deterministic clocks give the all-Continue payoff. -/
theorem quittingTerminalPayoff_pureStoppingTimeProfile_eq_zero_of_allNever
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (choices : ι → Option ℕ) (hallNever : ∀ who, choices who = none)
    (observer : ι) :
    quittingTerminalPayoff reward
        (quittingPureStoppingTimeProfile reward choices) observer = 0 := by
  have hprofile : quittingPureStoppingTimeProfile reward choices =
      quittingAlwaysContinueProfile reward := by
    funext who time history
    change quittingPureTimeHazard (choices who) time = PMF.pure false
    rw [hallNever who, quittingPureTimeHazard_none]
  rw [hprofile, quittingTerminalPayoff_quittingAlwaysContinue]

theorem quittingFiniteClockSemanticFold_mem_reachable
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (clockBound : ℕ) (word : Fin clockBound → QuittingRootSimplex ι) :
    quittingFiniteClockSemanticFold reward clockBound word ∈
      quittingFiniteClockSemanticReachable reward clockBound := by
  let profile := quittingFiniteClockWordProfile reward clockBound word
  let laws : ι → PMF (Option ℕ) := fun who =>
    quittingBehaviorStoppingLaw reward (profile who)
  refine ⟨laws, ?_, ?_⟩
  · intro who
    exact quittingFiniteClockWordProfile_stoppingLaw_isFinite
      reward clockBound word who
  · rw [← quittingTerminalSemanticPair_eq_stoppingLawProfile reward profile,
      quittingTerminalSemanticPair_finiteClockWordProfile_eq_fold]

omit [DecidableEq ι] in
theorem quittingStoppingLawProfile_liveHazard_eq_allContinue_of_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (clockBound : ℕ) (laws : ι → PMF (Option ℕ))
    (hlaws : ∀ who, IsFiniteClockStoppingLaw clockBound (laws who))
    {time : ℕ} (htime : clockBound ≤ time) :
    quittingProfileLiveRoot reward (quittingStoppingLawProfile reward laws) time =
      quittingAllContinueRoot := by
  funext who
  have hfinite : Math.Probability.DiscreteHazard.StoppingLaw.finiteMass
      (laws who) time = 0 := by
    unfold Math.Probability.DiscreteHazard.StoppingLaw.finiteMass
    have hzero : laws who (some time) = 0 := by
      by_contra hne
      rcases hlaws who (some time) hne with hnever | ⟨other, hother, heq⟩
      · cases hnever
      · simp only [Option.some.injEq] at heq
        subst other
        omega
    rw [hzero]
    rfl
  change (Math.Probability.DiscreteHazard.StoppingLaw.toScalarHazard
    (laws who)).toBoolean time = PMF.pure false
  apply eq_pure_false_of_true_toReal_eq_zero
  simp [Math.Probability.DiscreteHazard.ScalarHazard.toBoolean,
    Math.Probability.DiscreteHazard.StoppingLaw.toScalarHazard, hfinite]

theorem quittingFiniteClockSemanticReachable_subset_range_fold
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (clockBound : ℕ) :
    quittingFiniteClockSemanticReachable reward clockBound ⊆
      Set.range (quittingFiniteClockSemanticFold reward clockBound) := by
  rintro pair ⟨laws, hlaws, rfl⟩
  let profile := quittingStoppingLawProfile reward laws
  let word : Fin clockBound → QuittingRootSimplex ι := fun time who =>
    stdSimplexEquiv (quittingProfileLiveRoot reward profile time.val who)
  refine ⟨word, ?_⟩
  rw [← quittingTerminalSemanticPair_finiteClockWordProfile_eq_fold]
  congr 2
  funext who time history
  unfold quittingFiniteClockWordProfile quittingRootSequenceProfile
    quittingStoppingLawProfile
  simp only [Nat.zero_add]
  change (quittingFiniteClockRoots clockBound word time) who =
    quittingStoppingLawBehaviorStrategy reward who (laws who) time history
  by_cases htime : time < clockBound
  · rw [quittingFiniteClockRoots, dif_pos htime]
    simp [word, profile, quittingRootOfSimplex, quittingProfileLiveRoot,
      quittingStoppingLawProfile, quittingStoppingLawBehaviorStrategy]
  · rw [quittingFiniteClockRoots, dif_neg htime,
      ← quittingStoppingLawProfile_liveHazard_eq_allContinue_of_le
        reward clockBound laws hlaws (Nat.le_of_not_gt htime)]
    rfl

theorem quittingFiniteClockSemanticReachable_eq_range_fold
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (clockBound : ℕ) :
    quittingFiniteClockSemanticReachable reward clockBound =
      Set.range (quittingFiniteClockSemanticFold reward clockBound) := by
  apply Set.Subset.antisymm
  · exact quittingFiniteClockSemanticReachable_subset_range_fold
      reward clockBound
  · rintro pair ⟨word, rfl⟩
    exact quittingFiniteClockSemanticFold_mem_reachable
      reward clockBound word

theorem quittingFiniteClockSemanticReachable_isCompact
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (clockBound : ℕ) :
    IsCompact (quittingFiniteClockSemanticReachable reward clockBound) := by
  rw [quittingFiniteClockSemanticReachable_eq_range_fold]
  simpa only [Set.image_univ] using isCompact_univ.image
    (continuous_quittingFiniteClockSemanticFold reward clockBound)

/-- Literal compact finite-clock center used by the topological hierarchy. -/
def quittingFiniteClockSemanticCenter
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (clockBound : ℕ) : Set (QuittingTerminalSemanticPair ι) :=
  quittingFiniteClockSemanticReachable reward clockBound

theorem quittingFiniteClockSemanticCenter_nonempty
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (clockBound : ℕ) :
    (quittingFiniteClockSemanticCenter reward clockBound).Nonempty :=
  quittingFiniteClockSemanticReachable_nonempty reward clockBound

theorem quittingFiniteClockSemanticCenter_subset_carrier
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (clockBound : ℕ) :
    quittingFiniteClockSemanticCenter reward clockBound ⊆
      quittingTerminalSemanticCarrier reward := by
  exact quittingFiniteClockSemanticReachable_subset_carrier reward clockBound

theorem quittingFiniteClockSemanticCenter_isCompact
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (clockBound : ℕ) :
    IsCompact (quittingFiniteClockSemanticCenter reward clockBound) := by
  exact quittingFiniteClockSemanticReachable_isCompact reward clockBound

end GameTheory
