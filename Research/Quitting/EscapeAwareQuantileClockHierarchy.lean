/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.Topology.NestedOuterApproximation
import MathUE.Probability.QuantileClock
import Research.Quitting.EscapeAwareQuantileClockCollision
import UniformEquilibrium.Quitting.Classification.Existence.StationarilyGeneratedSemanticCarrier
import UniformEquilibrium.Quitting.Paths.SureExitSet
import UniformEquilibrium.Quitting.Root.TerminalSemanticPrefixMetric
import UniformEquilibrium.Quitting.Root.TerminalSemanticEqualityStratum
import UniformEquilibrium.Quitting.Terminal.OpponentTightTerminalSemanticRealization
import UniformEquilibrium.Quitting.Terminal.StrategicallyPrecompactWatchdogProperBoundary

/-!
# Escape-aware finite-clock outer hierarchy

This file formalizes the topological and semantic portion of the quantile-clock
hierarchy.  Finite-clock centers are literal profiles reconstructed from
independent stopping laws on `Option Nat`; the `none` (`Never`) atom is retained
exactly, and their cap coordinate is the unrestricted behavioral envelope in
`quittingTerminalSemanticPair`.

The localized transport property is
`HasEscapeAwareQuantileClockPayoffTransport`; its semantic wrapper is
`HasEscapeAwareQuantileClockCompression`.  Both are proved under the packet's
explicit reward normalization.  The carrier hierarchy and quantitative
lower/upper bracket follow from the wrapper.  This file does not encode a
semialgebraic/real-closed-field presentation of the finite centers.
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

/-- Replacing one source law by a pure clock commutes exactly with the
coordinatewise active-cell quotient. -/
theorem pmfPi_pureDeviationActiveCompressedLaws_eq_map
    (laws : ι → PMF (Option ℕ)) (marks : Finset ℕ)
    (who : ι) (choice : Option ℕ) :
    pmfPi (quittingPureDeviationStoppingLaws
        (fun player => Math.Probability.finiteClockActiveCompressedLaw
          (laws player) marks)
        who (Math.Probability.finiteClockActiveQuotient marks choice)) =
      (pmfPi (quittingPureDeviationStoppingLaws laws who choice)).map
        (fun choices player =>
          Math.Probability.finiteClockActiveQuotient marks
            (choices player)) := by
  rw [show quittingPureDeviationStoppingLaws
      (fun player => Math.Probability.finiteClockActiveCompressedLaw
        (laws player) marks)
      who (Math.Probability.finiteClockActiveQuotient marks choice) =
      fun player =>
        (quittingPureDeviationStoppingLaws laws who choice player).map
          (Math.Probability.finiteClockActiveQuotient marks) by
    funext player
    by_cases hplayer : player = who
    · subst player
      simp [quittingPureDeviationStoppingLaws]
      exact (PMF.pure_map
        (Math.Probability.finiteClockActiveQuotient marks) choice).symm
    · simp [quittingPureDeviationStoppingLaws,
        Math.Probability.finiteClockActiveCompressedLaw, hplayer]]
  exact (pmfPi_push_coordwise
    (quittingPureDeviationStoppingLaws laws who choice)
    (fun _ => Math.Probability.finiteClockActiveQuotient marks)).symm

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

/-- Number of finite clock cells in the finite-player common-quantile packet. -/
def quantileClockSupport (ι : Type) [Fintype ι]
    (level : ℕ) : ℕ :=
  2 * Fintype.card ι * level + 1

/-- Coordinatewise semantic error in the finite-player common-quantile
packet. -/
def quantileClockRadius (ι : Type) [Fintype ι]
    (level : ℕ) : ℝ :=
  ((Fintype.card ι * (Fintype.card ι - 1) : ℕ) : ℝ) / (level : ℝ)

/-- Quantile-clock semantic radius for terminal rewards bounded in absolute
value by `bound`. -/
def quantileClockScaledRadius (ι : Type) [Fintype ι]
    (bound : ℝ) (level : ℕ) : ℝ :=
  bound * quantileClockRadius ι level

/-- Union-bound budget for pair collisions in common unmarked cells. -/
def quantileClockCollisionBudget (ι : Type) [Fintype ι]
    (level : ℕ) : ℝ :=
  ((Fintype.card ι * (Fintype.card ι - 1) : ℕ) : ℝ) /
    (2 * (level : ℝ))

theorem two_mul_quantileClockCollisionBudget
    (ι : Type) [Fintype ι] {level : ℕ} (hlevel : 0 < level) :
    2 * quantileClockCollisionBudget ι level =
      quantileClockRadius ι level := by
  have hlevelNe : (level : ℝ) ≠ 0 := by exact_mod_cast hlevel.ne'
  unfold quantileClockCollisionBudget quantileClockRadius
  field_simp

theorem quantileClockRadius_nonneg (ι : Type) [Fintype ι]
    (level : ℕ) : 0 ≤ quantileClockRadius ι level := by
  exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem quantileClockRadius_tendsto_zero (ι : Type) [Fintype ι] :
    Tendsto (quantileClockRadius ι) atTop (𝓝 0) := by
  exact tendsto_const_div_atTop_nhds_zero_nat
    ((Fintype.card ι * (Fintype.card ι - 1) : ℕ) : ℝ)

theorem quantileClockScaledRadius_nonneg (ι : Type) [Fintype ι]
    {bound : ℝ} (hbound : 0 ≤ bound) (level : ℕ) :
    0 ≤ quantileClockScaledRadius ι bound level := by
  exact mul_nonneg hbound (quantileClockRadius_nonneg ι level)

theorem quantileClockScaledRadius_tendsto_zero (ι : Type) [Fintype ι]
    (bound : ℝ) :
    Tendsto (quantileClockScaledRadius ι bound) atTop (𝓝 0) := by
  change Tendsto (fun level => bound * quantileClockRadius ι level)
    atTop (𝓝 0)
  simpa using
    (quantileClockRadius_tendsto_zero ι).const_mul bound

/-! ## Canonical common-quantile compression -/

/-- Complete stopping laws extracted from the live spine of a source profile. -/
def quittingQuantileClockSourceLaws
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) :
    ι → PMF (Option ℕ) :=
  fun who => quittingBehaviorStoppingLaw reward (profile who)

/-- The common union of every player's positive-grid first-crossing dates. -/
def quittingQuantileClockMarks
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (level : ℕ) : Finset ℕ :=
  Math.Probability.commonStoppingLawQuantileMarks
    (quittingQuantileClockSourceLaws reward profile) level

/-- Push each stopping law separately through the same ordered finite-cell
quotient.  This preserves independence and retains Never exactly. -/
def quittingQuantileClockCompressedLaws
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (level : ℕ) :
    ι → PMF (Option ℕ) :=
  fun who => Math.Probability.finiteClockActiveCompressedLaw
    (quittingQuantileClockSourceLaws reward profile who)
    (quittingQuantileClockMarks reward profile level)

/-- Literal independent behavioral reconstruction of the compressed laws. -/
def quittingQuantileClockCompressedProfile
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (level : ℕ) :
    (quittingGame reward).BehaviorProfile :=
  quittingStoppingLawProfile reward
    (quittingQuantileClockCompressedLaws reward profile level)

/-- Coordinatewise quotient applied to one joint vector of independently
sampled source clocks. -/
def quittingQuantileClockJointQuotient
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (level : ℕ)
    (choices : ι → Option ℕ) : ι → Option ℕ :=
  fun who => Math.Probability.finiteClockActiveQuotient
    (quittingQuantileClockMarks reward profile level) (choices who)

/-- Raw alternating cell tags used only to identify common unmarked-gap
collisions.  Unlike the executable joint quotient, these tags may contain
unattained holes and are not used as target clock dates. -/
def quittingQuantileClockRawJointQuotient
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (level : ℕ)
    (choices : ι → Option ℕ) : ι → Option ℕ :=
  fun who => Math.Probability.finiteClockQuotient
    (quittingQuantileClockMarks reward profile level) (choices who)

/-- Removing unattained raw cells preserves every deterministic terminal
payoff off the event that two players occupy one common unmarked gap.  Ties
at marked dates are retained exactly, and the all-Never branch stays zero. -/
theorem quittingTerminalPayoff_pureStoppingTimeProfile_eq_activeQuotient_of_no_rawCollision
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (marks : Finset ℕ) (choices : ι → Option ℕ) (observer : ι)
    (hnoCollision : ¬hasEvenSomeCollision (fun who =>
      Math.Probability.finiteClockQuotient marks (choices who))) :
    quittingTerminalPayoff reward
        (quittingPureStoppingTimeProfile reward choices) observer =
      quittingTerminalPayoff reward
        (quittingPureStoppingTimeProfile reward fun who =>
          Math.Probability.finiteClockActiveQuotient marks
            (choices who)) observer := by
  by_cases hfinite : ∃ time, ∃ who, choices who = some time
  · let first := Nat.find hfinite
    have hfirstWitness : ∃ who, choices who = some first :=
      Nat.find_spec hfinite
    have hsourceFirst : (Finset.univ.filter fun who =>
        choices who = some first).Nonempty := by
      obtain ⟨who, hwho⟩ := hfirstWitness
      exact ⟨who, by simp [hwho]⟩
    have hsourceBefore : ∀ time < first, ∀ who,
        choices who ≠ some time := by
      intro time htime who hwho
      exact (Nat.not_le_of_lt htime)
        (Nat.find_min' hfinite ⟨who, hwho⟩)
    let target : ι → Option ℕ := fun who =>
      Math.Probability.finiteClockActiveQuotient marks (choices who)
    let targetFirst :=
      Math.Probability.finiteClockActiveCellIndex marks first
    have hcoalition : (Finset.univ.filter fun who =>
        target who = some targetFirst) =
        Finset.univ.filter fun who => choices who = some first := by
      ext who
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro htarget
        cases hchoice : choices who with
        | none => simp [target, hchoice] at htarget
        | some time =>
            have hactive :
                Math.Probability.finiteClockActiveCellIndex marks time =
                  Math.Probability.finiteClockActiveCellIndex marks first := by
              simpa [target, targetFirst, hchoice] using htarget
            have hraw :=
              (Math.Probability.finiteClockActiveCellIndex_eq_iff
                marks time first).mp hactive
            by_cases heqTime : time = first
            · subst time
              rfl
            · exfalso
              have heven :=
                (Math.Probability.finiteClockCellIndex_eq_implies_eq_or_even
                  marks hraw).resolve_left heqTime
              obtain ⟨anchor, hanchorMem⟩ := hsourceFirst
              have hanchor : choices anchor = some first := by
                simpa using hanchorMem
              have hne : who ≠ anchor := by
                intro heqWho
                subst anchor
                rw [hanchor] at hchoice
                cases hchoice
                exact (heqTime rfl).elim
              apply hnoCollision
              refine ⟨who, anchor, hne,
                Math.Probability.finiteClockCellIndex marks time,
                heven, ?_, ?_⟩
              · simp [hchoice, Math.Probability.finiteClockQuotient]
              · rw [hraw]
                simp [hanchor, Math.Probability.finiteClockQuotient]
      · intro hsource
        simp [target, targetFirst, hsource]
    have htargetFirst : (Finset.univ.filter fun who =>
        target who = some targetFirst).Nonempty := by
      rw [hcoalition]
      exact hsourceFirst
    have htargetBefore : ∀ time < targetFirst, ∀ who,
        target who ≠ some time := by
      intro time htime who htarget
      cases hchoice : choices who with
      | none => simp [target, hchoice] at htarget
      | some sourceTime =>
          have hactive :
              Math.Probability.finiteClockActiveCellIndex marks sourceTime =
                time := by
            simpa [target, hchoice] using htarget
          have hsourceLe : first ≤ sourceTime := by
            by_contra hnotLe
            exact hsourceBefore sourceTime (Nat.lt_of_not_ge hnotLe)
              who hchoice
          have hmono :=
            Math.Probability.finiteClockActiveCellIndex_mono marks hsourceLe
          rw [hactive] at hmono
          exact (Nat.not_le_of_lt htime) hmono
    rw [quittingTerminalPayoff_pureStoppingTimeProfile_eq_firstCoalition
      reward choices observer first hsourceFirst hsourceBefore]
    rw [quittingTerminalPayoff_pureStoppingTimeProfile_eq_firstCoalition
      reward target observer targetFirst htargetFirst htargetBefore]
    rw [hcoalition]
  · have hallNever : ∀ who, choices who = none := by
      intro who
      cases hchoice : choices who with
      | none => rfl
      | some time => exact (hfinite ⟨time, who, hchoice⟩).elim
    rw [quittingTerminalPayoff_pureStoppingTimeProfile_eq_zero_of_allNever
      reward choices hallNever observer]
    apply Eq.symm
    apply quittingTerminalPayoff_pureStoppingTimeProfile_eq_zero_of_allNever
    intro who
    simp [hallNever who]

/-- Moving one deterministic deviator later preserves terminal payoff when
every opponent either stops strictly before the old date or Never stops. -/
theorem quittingTerminalPayoff_pureStoppingTimeProfile_update_some_eq_of_others_lt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (choices : ι → Option ℕ) (who observer : ι)
    {first second : ℕ} (hlt : first < second)
    (hothers : ∀ player, player ≠ who →
      choices player = none ∨
        ∃ time < first, choices player = some time) :
    quittingTerminalPayoff reward
        (quittingPureStoppingTimeProfile reward
          (Function.update choices who (some first))) observer =
      quittingTerminalPayoff reward
        (quittingPureStoppingTimeProfile reward
          (Function.update choices who (some second))) observer := by
  let source := Function.update choices who (some first)
  let target := Function.update choices who (some second)
  change quittingTerminalPayoff reward
      (quittingPureStoppingTimeProfile reward source) observer =
    quittingTerminalPayoff reward
      (quittingPureStoppingTimeProfile reward target) observer
  by_cases hopponent : ∃ time, ∃ player, player ≠ who ∧
      choices player = some time
  · let earliest := Nat.find hopponent
    obtain ⟨anchor, hanchorNe, hanchor⟩ := Nat.find_spec hopponent
    have hearliestLt : earliest < first := by
      rcases hothers anchor hanchorNe with hnever | ⟨time, htime, heq⟩
      · rw [hnever] at hanchor
        cases hanchor
      · rw [heq] at hanchor
        cases hanchor
        exact htime
    have hsourceBefore : ∀ time < earliest, ∀ player,
        source player ≠ some time := by
      intro time htime player
      by_cases hplayer : player = who
      · subst player
        simp [source]
        omega
      · simp [source, hplayer]
        intro heq
        exact (Nat.not_le_of_lt htime)
          (Nat.find_min' hopponent ⟨player, hplayer, heq⟩)
    have htargetBefore : ∀ time < earliest, ∀ player,
        target player ≠ some time := by
      intro time htime player
      by_cases hplayer : player = who
      · subst player
        simp [target]
        omega
      · simp [target, hplayer]
        intro heq
        exact (Nat.not_le_of_lt htime)
          (Nat.find_min' hopponent ⟨player, hplayer, heq⟩)
    have hcoalition : (Finset.univ.filter fun player =>
        source player = some earliest) =
        Finset.univ.filter fun player => target player = some earliest := by
      ext player
      by_cases hplayer : player = who
      · subst player
        simp [source, target]
        omega
      · simp [source, target, Function.update, hplayer]
    have hsourceFirst : (Finset.univ.filter fun player =>
        source player = some earliest).Nonempty := by
      refine ⟨anchor, ?_⟩
      simp [source, hanchorNe]
      exact hanchor
    have htargetFirst : (Finset.univ.filter fun player =>
        target player = some earliest).Nonempty := by
      rw [← hcoalition]
      exact hsourceFirst
    rw [quittingTerminalPayoff_pureStoppingTimeProfile_eq_firstCoalition
      reward source observer earliest hsourceFirst hsourceBefore]
    rw [quittingTerminalPayoff_pureStoppingTimeProfile_eq_firstCoalition
      reward target observer earliest htargetFirst htargetBefore]
    rw [hcoalition]
  · push Not at hopponent
    have hallNever : ∀ player, player ≠ who → choices player = none := by
      intro player hplayer
      cases hchoice : choices player with
      | none => rfl
      | some time => exact (hopponent time player hplayer hchoice).elim
    have hsourceFirst : (Finset.univ.filter fun player =>
        source player = some first).Nonempty := by
      refine ⟨who, ?_⟩
      simp [source]
    have htargetFirst : (Finset.univ.filter fun player =>
        target player = some second).Nonempty := by
      refine ⟨who, ?_⟩
      simp [target]
    have hsourceBefore : ∀ time < first, ∀ player,
        source player ≠ some time := by
      intro time htime player
      by_cases hplayer : player = who
      · subst player
        simp [source]
        omega
      · simp [source, hplayer, hallNever player hplayer]
    have htargetBefore : ∀ time < second, ∀ player,
        target player ≠ some time := by
      intro time htime player
      by_cases hplayer : player = who
      · subst player
        simp [target]
        omega
      · simp [target, hplayer, hallNever player hplayer]
    have hcoalition : (Finset.univ.filter fun player =>
        source player = some first) =
        Finset.univ.filter fun player => target player = some second := by
      ext player
      by_cases hplayer : player = who
      · subst player
        simp [source, target]
      · simp [source, target, Function.update, hplayer,
          hallNever player hplayer]
    rw [quittingTerminalPayoff_pureStoppingTimeProfile_eq_firstCoalition
      reward source observer first hsourceFirst hsourceBefore]
    rw [quittingTerminalPayoff_pureStoppingTimeProfile_eq_firstCoalition
      reward target observer second htargetFirst htargetBefore]
    rw [hcoalition]

/-- A representative of the last active cell can be moved to any padded
target date.  Off raw terminal-gap collisions, all opponents are strictly
earlier or Never, so the deterministic terminal payoff is unchanged. -/
theorem quittingTerminalPayoff_pureStoppingTimeProfile_eq_paddedActiveTarget_of_no_rawCollision
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (marks : Finset ℕ) (choices : ι → Option ℕ) (who observer : ι)
    (sourceTime targetTime : ℕ)
    (hsourceLast :
      Math.Probability.finiteClockActiveCellIndex marks sourceTime =
        Math.Probability.finiteClockActiveCellCount marks - 1)
    (htarget : Math.Probability.finiteClockActiveCellCount marks ≤ targetTime)
    (hsourceWho : choices who = some sourceTime)
    (hnoCollision : ¬hasEvenSomeCollision (fun player =>
      Math.Probability.finiteClockQuotient marks (choices player))) :
    quittingTerminalPayoff reward
        (quittingPureStoppingTimeProfile reward choices) observer =
      quittingTerminalPayoff reward
        (quittingPureStoppingTimeProfile reward
          (Function.update
            (fun player => Math.Probability.finiteClockActiveQuotient
              marks (choices player))
            who (some targetTime))) observer := by
  let active : ι → Option ℕ := fun player =>
    Math.Probability.finiteClockActiveQuotient marks (choices player)
  let last := Math.Probability.finiteClockActiveCellCount marks - 1
  have hcount : 0 < Math.Probability.finiteClockActiveCellCount marks :=
    Math.Probability.finiteClockActiveCellCount_pos marks
  have hlastLt : last < targetTime := by
    dsimp [last]
    omega
  have hsourceActive : active who = some last := by
    simp [active, hsourceWho, hsourceLast, last]
  have hothers : ∀ player, player ≠ who →
      active player = none ∨ ∃ time < last, active player = some time := by
    intro player hplayer
    cases hchoice : choices player with
    | none => exact Or.inl (by simp [active, hchoice])
    | some time =>
        right
        let cell := Math.Probability.finiteClockActiveCellIndex marks time
        refine ⟨cell, ?_, by simp [active, hchoice, cell]⟩
        have hcellCount :=
          Math.Probability.finiteClockActiveCellIndex_lt_count marks time
        have hneLast : cell ≠ last := by
          intro heq
          have hactiveEq :
              Math.Probability.finiteClockActiveCellIndex marks time =
                Math.Probability.finiteClockActiveCellIndex
                  marks sourceTime := by
            rw [hsourceLast]
            exact heq
          have hrawEq :=
            (Math.Probability.finiteClockActiveCellIndex_eq_iff
              marks time sourceTime).mp hactiveEq
          have heven :=
            Math.Probability.finiteClockCellIndex_even_of_activeCellIndex_eq_last
              marks hsourceLast
          apply hnoCollision
          refine ⟨player, who, hplayer,
            Math.Probability.finiteClockCellIndex marks sourceTime,
            heven, ?_, ?_⟩
          · simp [hchoice, Math.Probability.finiteClockQuotient, hrawEq]
          · simp [hsourceWho, Math.Probability.finiteClockQuotient]
        dsimp [cell, last] at hcellCount hneLast ⊢
        omega
  calc
    _ = quittingTerminalPayoff reward
        (quittingPureStoppingTimeProfile reward active) observer :=
      quittingTerminalPayoff_pureStoppingTimeProfile_eq_activeQuotient_of_no_rawCollision
        reward marks choices observer hnoCollision
    _ = quittingTerminalPayoff reward
        (quittingPureStoppingTimeProfile reward
          (Function.update active who (some last))) observer := by
      have hclock : active = Function.update active who (some last) := by
        symm
        rw [← hsourceActive]
        exact Function.update_eq_self who active
      exact congrArg (fun clock => quittingTerminalPayoff reward
        (quittingPureStoppingTimeProfile reward clock) observer) hclock
    _ = _ :=
      quittingTerminalPayoff_pureStoppingTimeProfile_update_some_eq_of_others_lt
        reward active who observer hlastLt hothers

/-- Reverse coupling coordinate.  On the deterministic source atom of the
deviator it emits the requested target date; outside that null mismatch it
falls back to the ordinary active quotient. -/
def quittingQuantileClockReverseCoordinate
    (marks : Finset ℕ) (who : ι) (source target : Option ℕ)
    (player : ι) (choice : Option ℕ) : Option ℕ :=
  if player = who then
    if choice = source then target
    else Math.Probability.finiteClockActiveQuotient marks choice
  else Math.Probability.finiteClockActiveQuotient marks choice

/-- The fixed-source reverse coupling pushes the independently modified
source product exactly to the independently modified active target product. -/
theorem pmfPi_pureDeviationActiveCompressedLaws_eq_reverseMap
    (laws : ι → PMF (Option ℕ)) (marks : Finset ℕ) (who : ι)
    (source target : Option ℕ) :
    pmfPi (quittingPureDeviationStoppingLaws
        (fun player => Math.Probability.finiteClockActiveCompressedLaw
          (laws player) marks)
        who target) =
      (pmfPi (quittingPureDeviationStoppingLaws laws who source)).map
        (fun choices player =>
          quittingQuantileClockReverseCoordinate
            marks who source target player (choices player)) := by
  rw [show quittingPureDeviationStoppingLaws
      (fun player => Math.Probability.finiteClockActiveCompressedLaw
        (laws player) marks)
      who target = fun player =>
        (quittingPureDeviationStoppingLaws laws who source player).map
          (quittingQuantileClockReverseCoordinate
            marks who source target player) by
    funext player
    by_cases hplayer : player = who
    · subst player
      simp only [quittingPureDeviationStoppingLaws, if_pos]
      rw [PMF.pure_map]
      congr 1
      simp [quittingQuantileClockReverseCoordinate]
    · simp only [quittingPureDeviationStoppingLaws, if_neg hplayer]
      change (laws player).map
          (Math.Probability.finiteClockActiveQuotient marks) =
        (laws player).map
          (quittingQuantileClockReverseCoordinate
            marks who source target player)
      congr 1
      funext choice
      simp [quittingQuantileClockReverseCoordinate, hplayer]]
  exact (pmfPi_push_coordwise
    (quittingPureDeviationStoppingLaws laws who source)
    (quittingQuantileClockReverseCoordinate marks who source target)).symm

/-- Pointwise reverse coupling equality off raw gap collisions.  Internal
active target dates are represented exactly; padded dates use the final-cell
move-later lemma. -/
theorem quittingTerminalPayoff_pureStoppingTimeProfile_eq_reverseActiveCoupling_of_no_rawCollision
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (marks : Finset ℕ) (choices : ι → Option ℕ) (who observer : ι)
    (source target : Option ℕ)
    (hcase : Math.Probability.finiteClockActiveQuotient marks source = target ∨
      ∃ sourceTime targetTime,
        source = some sourceTime ∧ target = some targetTime ∧
        Math.Probability.finiteClockActiveCellIndex marks sourceTime =
          Math.Probability.finiteClockActiveCellCount marks - 1 ∧
        Math.Probability.finiteClockActiveCellCount marks ≤ targetTime)
    (hnoCollision : ¬hasEvenSomeCollision (fun player =>
      Math.Probability.finiteClockQuotient marks (choices player))) :
    quittingTerminalPayoff reward
        (quittingPureStoppingTimeProfile reward choices) observer =
      quittingTerminalPayoff reward
        (quittingPureStoppingTimeProfile reward fun player =>
          quittingQuantileClockReverseCoordinate
            marks who source target player (choices player)) observer := by
  let active : ι → Option ℕ := fun player =>
    Math.Probability.finiteClockActiveQuotient marks (choices player)
  by_cases hmatch : choices who = source
  · rcases hcase with hquotient | ⟨sourceTime, targetTime,
        hsource, htarget, hlast, hpadded⟩
    · have hmap : (fun player =>
          quittingQuantileClockReverseCoordinate
            marks who source target player (choices player)) = active := by
        funext player
        by_cases hplayer : player = who
        · subst player
          simp [quittingQuantileClockReverseCoordinate,
            active, hmatch, hquotient]
        · simp [quittingQuantileClockReverseCoordinate, active, hplayer]
      rw [hmap]
      exact
        quittingTerminalPayoff_pureStoppingTimeProfile_eq_activeQuotient_of_no_rawCollision
          reward marks choices observer hnoCollision
    · rcases hsource with rfl
      rcases htarget with rfl
      have hmap : (fun player =>
          quittingQuantileClockReverseCoordinate
            marks who (some sourceTime) (some targetTime)
              player (choices player)) =
          Function.update active who (some targetTime) := by
        funext player
        by_cases hplayer : player = who
        · subst player
          simp [quittingQuantileClockReverseCoordinate, active, hmatch]
        · simp [quittingQuantileClockReverseCoordinate, active, hplayer]
      rw [hmap]
      exact
        quittingTerminalPayoff_pureStoppingTimeProfile_eq_paddedActiveTarget_of_no_rawCollision
          reward marks choices who observer sourceTime targetTime hlast
          hpadded hmatch hnoCollision
  · have hmap : (fun player =>
        quittingQuantileClockReverseCoordinate
          marks who source target player (choices player)) = active := by
      funext player
      by_cases hplayer : player = who
      · subst player
        simp [quittingQuantileClockReverseCoordinate, active, hmatch]
      · simp [quittingQuantileClockReverseCoordinate, active, hplayer]
    rw [hmap]
    exact
      quittingTerminalPayoff_pureStoppingTimeProfile_eq_activeQuotient_of_no_rawCollision
        reward marks choices observer hnoCollision

/-- Every target clock has a source representative suitable for the reverse
coupling.  Active dates are represented exactly, `Never` is literal, and all
padding dates are represented by the last genuine finite cell. -/
theorem exists_finiteClockReverseRepresentative
    (marks : Finset ℕ) (target : Option ℕ) :
    ∃ source,
      Math.Probability.finiteClockActiveQuotient marks source = target ∨
        ∃ sourceTime targetTime,
          source = some sourceTime ∧ target = some targetTime ∧
          Math.Probability.finiteClockActiveCellIndex marks sourceTime =
            Math.Probability.finiteClockActiveCellCount marks - 1 ∧
          Math.Probability.finiteClockActiveCellCount marks ≤ targetTime := by
  cases target with
  | none =>
      exact ⟨none, Or.inl rfl⟩
  | some targetTime =>
      by_cases hactive : targetTime <
          Math.Probability.finiteClockActiveCellCount marks
      · obtain ⟨sourceTime, hsource⟩ :=
          Math.Probability.exists_finiteClockActiveCellIndex_eq marks hactive
        refine ⟨some sourceTime, Or.inl ?_⟩
        simp [hsource]
      · have hpadded :
            Math.Probability.finiteClockActiveCellCount marks ≤ targetTime :=
          Nat.le_of_not_gt hactive
        have hcount :=
          Math.Probability.finiteClockActiveCellCount_pos marks
        obtain ⟨sourceTime, hsource⟩ :=
          Math.Probability.exists_finiteClockActiveCellIndex_eq marks
            (show Math.Probability.finiteClockActiveCellCount marks - 1 <
              Math.Probability.finiteClockActiveCellCount marks by omega)
        exact ⟨some sourceTime, Or.inr
          ⟨sourceTime, targetTime, rfl, rfl, hsource, hpadded⟩⟩

omit [DecidableEq ι] in
/-- The product of the compressed marginals is exactly the pushforward of the
original independent product law through the coordinatewise common quotient. -/
theorem pmfPi_quittingQuantileClockCompressedLaws_eq_map
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (level : ℕ) :
    pmfPi (quittingQuantileClockCompressedLaws reward profile level) =
      (pmfPi (quittingQuantileClockSourceLaws reward profile)).map
        (quittingQuantileClockJointQuotient reward profile level) := by
  change pmfPi (fun who =>
      (quittingQuantileClockSourceLaws reward profile who).map
        (Math.Probability.finiteClockActiveQuotient
          (quittingQuantileClockMarks reward profile level))) =
    (pmfPi (quittingQuantileClockSourceLaws reward profile)).map
      (fun choices who => Math.Probability.finiteClockActiveQuotient
        (quittingQuantileClockMarks reward profile level) (choices who))
  exact (pmfPi_push_coordwise
    (quittingQuantileClockSourceLaws reward profile)
    (fun _ => Math.Probability.finiteClockActiveQuotient
      (quittingQuantileClockMarks reward profile level))).symm

omit [DecidableEq ι] in
@[simp] theorem quittingQuantileClockCompressedLaws_none
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (level : ℕ) (who : ι) :
    quittingQuantileClockCompressedLaws reward profile level who none =
      quittingQuantileClockSourceLaws reward profile who none := by
  simp [quittingQuantileClockCompressedLaws,
    quittingQuantileClockMarks]

omit [DecidableEq ι] in
theorem quittingQuantileClockCompressedLaws_isFiniteClock
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (level : ℕ) (who : ι) :
    IsFiniteClockStoppingLaw (quantileClockSupport ι level)
      (quittingQuantileClockCompressedLaws reward profile level who) := by
  intro choice hchoice
  exact Math.Probability.finiteClockActiveCompressedLaw_support_commonQuantile
    (quittingQuantileClockSourceLaws reward profile) level who hchoice

/-- The canonical compressed semantic pair belongs to the literal
finite-clock reachable set with the sharp support count. -/
theorem quittingQuantileClockCompressed_semanticPair_mem_reachable
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (level : ℕ) :
    quittingTerminalSemanticPair reward
        (quittingQuantileClockCompressedProfile reward profile level) ∈
      quittingFiniteClockSemanticReachable reward
        (quantileClockSupport ι level) := by
  refine ⟨quittingQuantileClockCompressedLaws reward profile level,
    fun who => quittingQuantileClockCompressedLaws_isFiniteClock
      reward profile level who, rfl⟩

omit [Fintype ι] [DecidableEq ι] in
/-- Coupled bounded observables differ in expectation by at most twice their
common absolute bound times the probability of the bad event. -/
theorem abs_expect_sub_expect_map_le_of_eq_off_event
    {Source Target : Type*} (law : PMF Source) (quotient : Source → Target)
    (sourceValue : Source → ℝ) (targetValue : Target → ℝ)
    (event : Set Source) {bound : ℝ}
    (hsource : ∀ sample, |sourceValue sample| ≤ bound)
    (htarget : ∀ sample, |targetValue sample| ≤ bound)
    (heq : ∀ sample, sample ∉ event →
      sourceValue sample = targetValue (quotient sample)) :
    |Math.Probability.expect law sourceValue -
        Math.Probability.expect (law.map quotient) targetValue| ≤
      2 * bound *
        (Math.ProbabilityMassFunction.pmfMass law
          fun sample => sample ∈ event).toReal := by
  have hmap : Math.Probability.expect (law.map quotient) targetValue =
      Math.Probability.expect law
        (fun sample => targetValue (quotient sample)) := by
    simpa [Math.ProbabilityMassFunction.pushforward] using
      Math.ProbabilityMassFunction.expect_pushforward_of_bounded
        law quotient targetValue htarget
  rw [hmap]
  apply Math.ProbabilityMassFunction.abs_expect_sub_le_mul_pmfMass
    law sourceValue (fun sample => targetValue (quotient sample)) event
    (bound := 2 * bound) (observableBound := bound)
    hsource (fun sample => htarget (quotient sample))
  intro sample
  by_cases hevent : sample ∈ event
  · rw [Set.indicator_of_mem hevent]
    simp only [mul_one]
    calc
      |sourceValue sample - targetValue (quotient sample)| ≤
          |sourceValue sample| + |targetValue (quotient sample)| :=
        abs_sub _ _
      _ ≤ bound + bound := add_le_add (hsource sample)
        (htarget (quotient sample))
      _ = 2 * bound := by ring
  · rw [Set.indicator_of_notMem hevent, mul_zero, heq sample hevent,
      sub_self, abs_zero]

/-- The prescribed-payoff part of quantile compression follows from an
explicit bad-event coupling and the sharp pair-collision budget. -/
theorem abs_quittingTerminalPayoff_sub_compressed_le_of_collisionEvent
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {bound : ℝ} (hbound : 0 ≤ bound)
    (hreward : ∀ terminal player, |reward terminal player| ≤ bound)
    (profile : (quittingGame reward).BehaviorProfile)
    {level : ℕ} (observer : ι)
    (event : Set (ι → Option ℕ))
    (heq : ∀ choices, choices ∉ event →
      quittingTerminalPayoff reward
          (quittingPureStoppingTimeProfile reward choices) observer =
        quittingTerminalPayoff reward
          (quittingPureStoppingTimeProfile reward
            (quittingQuantileClockJointQuotient
              reward profile level choices)) observer)
    (hmass : (Math.ProbabilityMassFunction.pmfMass
        (pmfPi (quittingQuantileClockSourceLaws reward profile))
        fun choices => choices ∈ event).toReal ≤
      quantileClockCollisionBudget ι level) :
    |quittingTerminalPayoff reward profile observer -
        quittingTerminalPayoff reward
          (quittingQuantileClockCompressedProfile reward profile level)
          observer| ≤ 2 * bound * quantileClockCollisionBudget ι level := by
  have hsourceCanonical := congrFun (congrArg Prod.fst
    (quittingTerminalSemanticPair_eq_stoppingLawProfile reward profile)) observer
  change quittingTerminalPayoff reward profile observer =
    quittingTerminalPayoff reward
      (quittingStoppingLawProfile reward
        (quittingQuantileClockSourceLaws reward profile)) observer at hsourceCanonical
  rw [hsourceCanonical, quittingQuantileClockCompressedProfile,
    quittingTerminalPayoff_stoppingLawProfile_eq_expect,
    quittingTerminalPayoff_stoppingLawProfile_eq_expect,
    pmfPi_quittingQuantileClockCompressedLaws_eq_map]
  have hcoupling := abs_expect_sub_expect_map_le_of_eq_off_event
    (pmfPi (quittingQuantileClockSourceLaws reward profile))
    (quittingQuantileClockJointQuotient reward profile level)
    (fun choices => quittingTerminalPayoff reward
      (quittingPureStoppingTimeProfile reward choices) observer)
    (fun choices => quittingTerminalPayoff reward
      (quittingPureStoppingTimeProfile reward choices) observer)
    event
    (bound := bound)
    (fun choices => abs_quittingTerminalPayoff_le reward _ observer hreward)
    (fun choices => abs_quittingTerminalPayoff_le reward _ observer hreward)
    heq
  calc
    _ ≤ 2 * bound *
        (Math.ProbabilityMassFunction.pmfMass
          (pmfPi (quittingQuantileClockSourceLaws reward profile))
          fun choices => choices ∈ event).toReal := hcoupling
    _ ≤ 2 * bound * quantileClockCollisionBudget ι level := by
      exact mul_le_mul_of_nonneg_left hmass (mul_nonneg (by norm_num) hbound)

/-- The canonical active-cell compression preserves every prescribed payoff
within the reward bound times the quantile radius.  The only bad event is a
pair sharing one raw unmarked gap; the consecutive target indexing itself
introduces no hole. -/
theorem abs_quittingTerminalPayoff_sub_quantileClockCompressed_le_of_bound
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {bound : ℝ} (hbound : 0 ≤ bound)
    (hreward : ∀ terminal player, |reward terminal player| ≤ bound)
    (profile : (quittingGame reward).BehaviorProfile)
    {level : ℕ} (hlevel : 0 < level) (observer : ι) :
    |quittingTerminalPayoff reward profile observer -
        quittingTerminalPayoff reward
          (quittingQuantileClockCompressedProfile reward profile level)
          observer| ≤ bound * quantileClockRadius ι level := by
  let event : Set (ι → Option ℕ) := {choices |
    hasEvenSomeCollision
      (quittingQuantileClockRawJointQuotient
        reward profile level choices)}
  rw [show bound * quantileClockRadius ι level =
      2 * bound * quantileClockCollisionBudget ι level by
    rw [← two_mul_quantileClockCollisionBudget ι hlevel]
    ring]
  apply abs_quittingTerminalPayoff_sub_compressed_le_of_collisionEvent
    reward hbound hreward profile observer event
  · intro choices hchoices
    exact
      quittingTerminalPayoff_pureStoppingTimeProfile_eq_activeQuotient_of_no_rawCollision
        reward (quittingQuantileClockMarks reward profile level)
        choices observer hchoices
  · have hmass :=
      Math.Probability.pmfMass_commonQuantileQuotient_hasEvenSomeCollision_toReal_le
        (quittingQuantileClockSourceLaws reward profile) hlevel
    change (Math.ProbabilityMassFunction.pmfMass
      (pmfPi (quittingQuantileClockSourceLaws reward profile))
      (fun choices => hasEvenSomeCollision (fun who =>
        Math.Probability.finiteClockQuotient
          (Math.Probability.commonStoppingLawQuantileMarks
            (quittingQuantileClockSourceLaws reward profile) level)
          (choices who)))).toReal ≤ quantileClockCollisionBudget ι level
    simpa only [quantileClockCollisionBudget] using hmass

/-- Unit-bounded specialization of the prescribed-payoff compression bound. -/
theorem abs_quittingTerminalPayoff_sub_quantileClockCompressed_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hreward : ∀ terminal player, |reward terminal player| ≤ 1)
    (profile : (quittingGame reward).BehaviorProfile)
    {level : ℕ} (hlevel : 0 < level) (observer : ι) :
    |quittingTerminalPayoff reward profile observer -
        quittingTerminalPayoff reward
          (quittingQuantileClockCompressedProfile reward profile level)
          observer| ≤ quantileClockRadius ι level := by
  simpa using
    abs_quittingTerminalPayoff_sub_quantileClockCompressed_le_of_bound
      reward (bound := 1) (by norm_num) hreward profile hlevel observer

/-- The fixed-original-marks collision budget remains valid after replacing
one source marginal by an arbitrary deterministic finite date or `Never`. -/
theorem pmfMass_quittingQuantileClock_update_pure_collision_toReal_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    {level : ℕ} (hlevel : 0 < level) (who : ι) (choice : Option ℕ) :
    (Math.ProbabilityMassFunction.pmfMass
      (pmfPi (quittingPureDeviationStoppingLaws
        (quittingQuantileClockSourceLaws reward profile) who choice))
      (fun choices => hasEvenSomeCollision (fun player =>
        Math.Probability.finiteClockQuotient
          (quittingQuantileClockMarks reward profile level)
          (choices player)))).toReal ≤
      quantileClockCollisionBudget ι level := by
  let laws := quittingQuantileClockSourceLaws reward profile
  let marks := quittingQuantileClockMarks reward profile level
  let sourceModified := quittingPureDeviationStoppingLaws laws who choice
  have hmass :=
    Math.Probability.pmfMass_commonQuantileQuotient_update_pure_collision_toReal_le
      laws hlevel who choice
  have hmodifiedClassical : sourceModified =
      @Function.update ι (fun _ => PMF (Option ℕ))
        (fun first second => Classical.propDecidable (first = second))
        laws who (PMF.pure choice) := by
    funext player
    by_cases hplayer : player = who
    · subst player
      simp [sourceModified, quittingPureDeviationStoppingLaws]
    · simp [sourceModified, quittingPureDeviationStoppingLaws, hplayer,
        Function.update]
  have hmassBase : (Math.ProbabilityMassFunction.pmfMass
      (pmfPi sourceModified)
      (fun choices => hasEvenSomeCollision (fun player =>
        Math.Probability.finiteClockQuotient marks
          (choices player)))).toReal ≤
      ((Fintype.card ι).choose 2 : ℝ) / (level : ℝ) := by
    rw [hmodifiedClassical]
    simpa [marks, laws, quittingQuantileClockMarks] using hmass
  rw [Math.Probability.natCast_choose_two_eq_mul_sub_div_two] at hmassBase
  change (Math.ProbabilityMassFunction.pmfMass
      (pmfPi sourceModified)
      (fun choices => hasEvenSomeCollision (fun player =>
        Math.Probability.finiteClockQuotient marks
          (choices player)))).toReal ≤ _
  calc
    _ ≤ (((Fintype.card ι * (Fintype.card ι - 1) : ℕ) : ℝ) / 2) /
        (level : ℝ) := hmassBase
    _ = quantileClockCollisionBudget ι level := by
      unfold quantileClockCollisionBudget
      ring

/-- Every source pure-time deviation has an active-cell target deviation with
payoff error at most the reward bound times the quantile radius. -/
theorem abs_quittingTerminalPayoff_update_pureTime_sub_compressed_mapped_le_of_bound
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {bound : ℝ} (hbound : 0 ≤ bound)
    (hreward : ∀ terminal player, |reward terminal player| ≤ bound)
    (profile : (quittingGame reward).BehaviorProfile)
    {level : ℕ} (hlevel : 0 < level) (who : ι)
    (choice : Option ℕ) :
    |quittingTerminalPayoff reward
          (Function.update profile who
            (quittingPureTimeBehaviorStrategy reward who choice)) who -
        quittingTerminalPayoff reward
          (Function.update
            (quittingQuantileClockCompressedProfile reward profile level) who
            (quittingPureTimeBehaviorStrategy reward who
              (Math.Probability.finiteClockActiveQuotient
                (quittingQuantileClockMarks reward profile level)
                choice))) who| ≤ bound * quantileClockRadius ι level := by
  let laws := quittingQuantileClockSourceLaws reward profile
  let marks := quittingQuantileClockMarks reward profile level
  let targetChoice :=
    Math.Probability.finiteClockActiveQuotient marks choice
  let sourceModified :=
    quittingPureDeviationStoppingLaws laws who choice
  let targetModified := quittingPureDeviationStoppingLaws
    (quittingQuantileClockCompressedLaws reward profile level)
    who targetChoice
  let event : Set (ι → Option ℕ) := {choices |
    hasEvenSomeCollision (fun player =>
      Math.Probability.finiteClockQuotient marks (choices player))}
  rw [quittingTerminalPayoff_update_pureTime_eq_stoppingLawProfile]
  change |quittingTerminalPayoff reward
          (Function.update (quittingStoppingLawProfile reward laws) who
            (quittingPureTimeBehaviorStrategy reward who choice)) who - _| ≤ _
  rw [quittingQuantileClockCompressedProfile]
  rw [quittingTerminalPayoff_update_stoppingLawProfile_pureTime_eq_expect,
    quittingTerminalPayoff_update_stoppingLawProfile_pureTime_eq_expect]
  change |Math.Probability.expect (pmfPi sourceModified) (fun choices =>
      quittingTerminalPayoff reward
        (quittingPureStoppingTimeProfile reward choices) who) -
    Math.Probability.expect (pmfPi targetModified) (fun choices =>
      quittingTerminalPayoff reward
        (quittingPureStoppingTimeProfile reward choices) who)| ≤ _
  have htargetLaw : pmfPi targetModified =
      (pmfPi sourceModified).map (fun choices player =>
        Math.Probability.finiteClockActiveQuotient marks
          (choices player)) := by
    exact pmfPi_pureDeviationActiveCompressedLaws_eq_map
      laws marks who choice
  rw [htargetLaw]
  have hcoupling := abs_expect_sub_expect_map_le_of_eq_off_event
    (pmfPi sourceModified)
    (fun choices player =>
      Math.Probability.finiteClockActiveQuotient marks (choices player))
    (fun choices => quittingTerminalPayoff reward
      (quittingPureStoppingTimeProfile reward choices) who)
    (fun choices => quittingTerminalPayoff reward
      (quittingPureStoppingTimeProfile reward choices) who)
    event (bound := bound)
    (fun choices => abs_quittingTerminalPayoff_le reward _ who hreward)
    (fun choices => abs_quittingTerminalPayoff_le reward _ who hreward)
    (fun choices hchoices =>
      quittingTerminalPayoff_pureStoppingTimeProfile_eq_activeQuotient_of_no_rawCollision
        reward marks choices who hchoices)
  have hmass :=
    Math.Probability.pmfMass_commonQuantileQuotient_update_pure_collision_toReal_le
      laws hlevel who choice
  have hmass' : (Math.ProbabilityMassFunction.pmfMass
      (pmfPi sourceModified)
      (fun choices => choices ∈ event)).toReal ≤
      quantileClockCollisionBudget ι level := by
    have hmodifiedClassical : sourceModified =
        @Function.update ι (fun _ => PMF (Option ℕ))
          (fun first second => Classical.propDecidable (first = second))
          laws who (PMF.pure choice) := by
      funext player
      by_cases hplayer : player = who
      · subst player
        simp [sourceModified, quittingPureDeviationStoppingLaws]
      · simp [sourceModified, quittingPureDeviationStoppingLaws, hplayer,
          Function.update]
    have hmassBase : (Math.ProbabilityMassFunction.pmfMass
        (pmfPi sourceModified)
        (fun choices => choices ∈ event)).toReal ≤
        ((Fintype.card ι).choose 2 : ℝ) / (level : ℝ) := by
      rw [hmodifiedClassical]
      simpa [event, marks, laws, quittingQuantileClockMarks] using hmass
    rw [Math.Probability.natCast_choose_two_eq_mul_sub_div_two] at hmassBase
    calc
      _ ≤ (((Fintype.card ι * (Fintype.card ι - 1) : ℕ) : ℝ) / 2) /
          (level : ℝ) := hmassBase
      _ = quantileClockCollisionBudget ι level := by
        unfold quantileClockCollisionBudget
        ring
  calc
    _ ≤ 2 * bound * (Math.ProbabilityMassFunction.pmfMass
        (pmfPi sourceModified)
        (fun choices => choices ∈ event)).toReal := hcoupling
    _ ≤ 2 * bound * quantileClockCollisionBudget ι level := by
      exact mul_le_mul_of_nonneg_left hmass'
        (mul_nonneg (by norm_num) hbound)
    _ = bound * quantileClockRadius ι level := by
      rw [← two_mul_quantileClockCollisionBudget ι hlevel]
      ring

/-- Unit-bounded forward pure-time transport. -/
theorem abs_quittingTerminalPayoff_update_pureTime_sub_compressed_mapped_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hreward : ∀ terminal player, |reward terminal player| ≤ 1)
    (profile : (quittingGame reward).BehaviorProfile)
    {level : ℕ} (hlevel : 0 < level) (who : ι)
    (choice : Option ℕ) :
    |quittingTerminalPayoff reward
          (Function.update profile who
            (quittingPureTimeBehaviorStrategy reward who choice)) who -
        quittingTerminalPayoff reward
          (Function.update
            (quittingQuantileClockCompressedProfile reward profile level) who
            (quittingPureTimeBehaviorStrategy reward who
              (Math.Probability.finiteClockActiveQuotient
                (quittingQuantileClockMarks reward profile level)
                choice))) who| ≤ quantileClockRadius ι level := by
  simpa using
    abs_quittingTerminalPayoff_update_pureTime_sub_compressed_mapped_le_of_bound
      reward (bound := 1) (by norm_num) hreward profile hlevel who choice

/-- Every target pure-time deviation, including padding dates and `Never`,
has a source pure-time representative with payoff error at most the reward
bound times the quantile radius. -/
theorem exists_abs_quittingTerminalPayoff_compressed_pureTime_sub_update_le_of_bound
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {bound : ℝ} (hbound : 0 ≤ bound)
    (hreward : ∀ terminal player, |reward terminal player| ≤ bound)
    (profile : (quittingGame reward).BehaviorProfile)
    {level : ℕ} (hlevel : 0 < level) (who : ι)
    (target : Option ℕ) :
    ∃ source,
      |quittingTerminalPayoff reward
          (Function.update
            (quittingQuantileClockCompressedProfile reward profile level) who
            (quittingPureTimeBehaviorStrategy reward who target)) who -
        quittingTerminalPayoff reward
          (Function.update profile who
            (quittingPureTimeBehaviorStrategy reward who source)) who| ≤
        bound * quantileClockRadius ι level := by
  let laws := quittingQuantileClockSourceLaws reward profile
  let marks := quittingQuantileClockMarks reward profile level
  obtain ⟨source, hcase⟩ :=
    exists_finiteClockReverseRepresentative marks target
  refine ⟨source, ?_⟩
  let sourceModified :=
    quittingPureDeviationStoppingLaws laws who source
  let targetModified := quittingPureDeviationStoppingLaws
    (quittingQuantileClockCompressedLaws reward profile level) who target
  let quotient : (ι → Option ℕ) → ι → Option ℕ := fun choices player =>
    quittingQuantileClockReverseCoordinate
      marks who source target player (choices player)
  let event : Set (ι → Option ℕ) := {choices |
    hasEvenSomeCollision (fun player =>
      Math.Probability.finiteClockQuotient marks (choices player))}
  have hsourceCanonical :=
    quittingTerminalPayoff_update_pureTime_eq_stoppingLawProfile
      reward profile who source
  rw [quittingQuantileClockCompressedProfile]
  rw [hsourceCanonical,
    quittingTerminalPayoff_update_stoppingLawProfile_pureTime_eq_expect,
    quittingTerminalPayoff_update_stoppingLawProfile_pureTime_eq_expect]
  change |Math.Probability.expect (pmfPi targetModified) (fun choices =>
      quittingTerminalPayoff reward
        (quittingPureStoppingTimeProfile reward choices) who) -
    Math.Probability.expect (pmfPi sourceModified) (fun choices =>
      quittingTerminalPayoff reward
        (quittingPureStoppingTimeProfile reward choices) who)| ≤ _
  have htargetLaw : pmfPi targetModified =
      (pmfPi sourceModified).map quotient := by
    exact pmfPi_pureDeviationActiveCompressedLaws_eq_reverseMap
      laws marks who source target
  rw [htargetLaw, abs_sub_comm]
  have hcoupling := abs_expect_sub_expect_map_le_of_eq_off_event
    (pmfPi sourceModified) quotient
    (fun choices => quittingTerminalPayoff reward
      (quittingPureStoppingTimeProfile reward choices) who)
    (fun choices => quittingTerminalPayoff reward
      (quittingPureStoppingTimeProfile reward choices) who)
    event (bound := bound)
    (fun choices => abs_quittingTerminalPayoff_le reward _ who hreward)
    (fun choices => abs_quittingTerminalPayoff_le reward _ who hreward)
    (fun choices hchoices =>
      quittingTerminalPayoff_pureStoppingTimeProfile_eq_reverseActiveCoupling_of_no_rawCollision
        reward marks choices who who source target hcase hchoices)
  have hmass : (Math.ProbabilityMassFunction.pmfMass
      (pmfPi sourceModified)
      (fun choices => choices ∈ event)).toReal ≤
      quantileClockCollisionBudget ι level := by
    exact pmfMass_quittingQuantileClock_update_pure_collision_toReal_le
      reward profile hlevel who source
  calc
    _ ≤ 2 * bound * (Math.ProbabilityMassFunction.pmfMass
        (pmfPi sourceModified)
        (fun choices => choices ∈ event)).toReal := hcoupling
    _ ≤ 2 * bound * quantileClockCollisionBudget ι level := by
      exact mul_le_mul_of_nonneg_left hmass
        (mul_nonneg (by norm_num) hbound)
    _ = bound * quantileClockRadius ι level := by
      rw [← two_mul_quantileClockCollisionBudget ι hlevel]
      ring

/-- Unit-bounded reverse pure-time transport. -/
theorem exists_abs_quittingTerminalPayoff_compressed_pureTime_sub_update_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hreward : ∀ terminal player, |reward terminal player| ≤ 1)
    (profile : (quittingGame reward).BehaviorProfile)
    {level : ℕ} (hlevel : 0 < level) (who : ι)
    (target : Option ℕ) :
    ∃ source,
      |quittingTerminalPayoff reward
          (Function.update
            (quittingQuantileClockCompressedProfile reward profile level) who
            (quittingPureTimeBehaviorStrategy reward who target)) who -
        quittingTerminalPayoff reward
          (Function.update profile who
            (quittingPureTimeBehaviorStrategy reward who source)) who| ≤
        quantileClockRadius ι level := by
  simpa using
    exists_abs_quittingTerminalPayoff_compressed_pureTime_sub_update_le_of_bound
      reward (bound := 1) (by norm_num) hreward profile hlevel who target

omit [Fintype ι] [DecidableEq ι] in
/-- Mutual pointwise approximation of two families controls the difference
of their suprema.  This is the order-theoretic final step in unrestricted-cap
compression. -/
theorem abs_sSup_range_sub_sSup_range_le_of_mutual_approx
    {Source Target : Type*} [Nonempty Source] [Nonempty Target]
    (source : Source → ℝ) (target : Target → ℝ)
    (hsource : BddAbove (Set.range source))
    (htarget : BddAbove (Set.range target)) {error : ℝ}
    (hforward : ∀ choice, ∃ mapped,
      |source choice - target mapped| ≤ error)
    (hbackward : ∀ choice, ∃ mapped,
      |target choice - source mapped| ≤ error) :
    |sSup (Set.range source) - sSup (Set.range target)| ≤ error := by
  have hsourceTarget : sSup (Set.range source) ≤
      sSup (Set.range target) + error := by
    apply csSup_le (Set.range_nonempty source)
    rintro value ⟨choice, rfl⟩
    obtain ⟨mapped, hmapped⟩ := hforward choice
    have hle : target mapped ≤ sSup (Set.range target) :=
      le_csSup htarget (Set.mem_range_self mapped)
    have hsigned : source choice - target mapped ≤ error :=
      (le_abs_self _).trans hmapped
    linarith
  have htargetSource : sSup (Set.range target) ≤
      sSup (Set.range source) + error := by
    apply csSup_le (Set.range_nonempty target)
    rintro value ⟨choice, rfl⟩
    obtain ⟨mapped, hmapped⟩ := hbackward choice
    have hle : source mapped ≤ sSup (Set.range source) :=
      le_csSup hsource (Set.mem_range_self mapped)
    have hsigned : target choice - source mapped ≤ error :=
      (le_abs_self _).trans hmapped
    linarith
  rw [abs_le]
  constructor <;> linarith

/-- Mutual comparison of every deterministic quit time, including Never,
controls the literal unrestricted behavioral best-response caps. -/
theorem abs_quittingContinuationBestResponseValue_sub_le_of_mutual_pureTime
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source target : (quittingGame reward).BehaviorProfile) (who : ι)
    {error : ℝ}
    (hforward : ∀ choice : Option ℕ, ∃ mapped : Option ℕ,
      |quittingTerminalPayoff reward
          (Function.update source who
            (quittingPureTimeBehaviorStrategy reward who choice)) who -
        quittingTerminalPayoff reward
          (Function.update target who
            (quittingPureTimeBehaviorStrategy reward who mapped)) who| ≤ error)
    (hbackward : ∀ choice : Option ℕ, ∃ mapped : Option ℕ,
      |quittingTerminalPayoff reward
          (Function.update target who
            (quittingPureTimeBehaviorStrategy reward who choice)) who -
        quittingTerminalPayoff reward
          (Function.update source who
            (quittingPureTimeBehaviorStrategy reward who mapped)) who| ≤ error) :
    |quittingContinuationBestResponseValue reward source who -
        quittingContinuationBestResponseValue reward target who| ≤ error := by
  let sourceValue : Option ℕ → ℝ := fun choice =>
    quittingTerminalPayoff reward
      (Function.update source who
        (quittingPureTimeBehaviorStrategy reward who choice)) who
  let targetValue : Option ℕ → ℝ := fun choice =>
    quittingTerminalPayoff reward
      (Function.update target who
        (quittingPureTimeBehaviorStrategy reward who choice)) who
  have hsourceBdd : BddAbove (Set.range sourceValue) := by
    refine ⟨quittingRewardBound reward, ?_⟩
    rintro value ⟨choice, rfl⟩
    exact (le_abs_self _).trans
      (abs_quittingTerminalPayoff_le_quittingRewardBound reward _ who)
  have htargetBdd : BddAbove (Set.range targetValue) := by
    refine ⟨quittingRewardBound reward, ?_⟩
    rintro value ⟨choice, rfl⟩
    exact (le_abs_self _).trans
      (abs_quittingTerminalPayoff_le_quittingRewardBound reward _ who)
  unfold quittingContinuationBestResponseValue
  rw [sSup_range_quittingTerminalPayoff_update_eq_pureTime,
    sSup_range_quittingTerminalPayoff_update_eq_pureTime]
  exact abs_sSup_range_sub_sSup_range_le_of_mutual_approx
    sourceValue targetValue hsourceBdd htargetBdd hforward hbackward

/-- Two-sided payoff transport at the radius appropriate for an explicit
absolute terminal-reward bound.  The last two clauses include every finite
quit time and Never. -/
def HasEscapeAwareQuantileClockPayoffTransportAtBound
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (bound : ℝ) : Prop :=
  ∀ profile : (quittingGame reward).BehaviorProfile,
    ∀ level, 0 < level →
      (∀ observer,
        |quittingTerminalPayoff reward profile observer -
          quittingTerminalPayoff reward
            (quittingQuantileClockCompressedProfile reward profile level)
            observer| ≤ quantileClockScaledRadius ι bound level) ∧
      (∀ who choice, ∃ mapped,
        |quittingTerminalPayoff reward
            (Function.update profile who
              (quittingPureTimeBehaviorStrategy reward who choice)) who -
          quittingTerminalPayoff reward
            (Function.update
              (quittingQuantileClockCompressedProfile reward profile level) who
              (quittingPureTimeBehaviorStrategy reward who mapped)) who| ≤
            quantileClockScaledRadius ι bound level) ∧
      (∀ who choice, ∃ mapped,
        |quittingTerminalPayoff reward
            (Function.update
              (quittingQuantileClockCompressedProfile reward profile level) who
              (quittingPureTimeBehaviorStrategy reward who choice)) who -
          quittingTerminalPayoff reward
            (Function.update profile who
              (quittingPureTimeBehaviorStrategy reward who mapped)) who| ≤
            quantileClockScaledRadius ι bound level)

/-- The active-cell common-quantile construction satisfies full two-sided
payoff transport for every explicit absolute reward bound. -/
theorem hasEscapeAwareQuantileClockPayoffTransportAtBound
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {bound : ℝ} (hbound : 0 ≤ bound)
    (hreward : ∀ terminal player, |reward terminal player| ≤ bound) :
    HasEscapeAwareQuantileClockPayoffTransportAtBound reward bound := by
  intro profile level hlevel
  refine ⟨?_, ?_, ?_⟩
  · simpa [quantileClockScaledRadius] using
      abs_quittingTerminalPayoff_sub_quantileClockCompressed_le_of_bound
        reward hbound hreward profile hlevel
  · intro who choice
    refine ⟨Math.Probability.finiteClockActiveQuotient
        (quittingQuantileClockMarks reward profile level) choice, ?_⟩
    simpa [quantileClockScaledRadius] using
      abs_quittingTerminalPayoff_update_pureTime_sub_compressed_mapped_le_of_bound
        reward hbound hreward profile hlevel who choice
  · intro who choice
    simpa [quantileClockScaledRadius] using
      exists_abs_quittingTerminalPayoff_compressed_pureTime_sub_update_le_of_bound
        reward hbound hreward profile hlevel who choice

/-- Exact probabilistic transport property for the canonical common-quantile
quotient.  The last two clauses include all deterministic finite quit times
and Never in both directions. -/
def HasEscapeAwareQuantileClockPayoffTransport
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) : Prop :=
  ∀ profile : (quittingGame reward).BehaviorProfile,
    ∀ level, 0 < level →
      (∀ observer,
        |quittingTerminalPayoff reward profile observer -
          quittingTerminalPayoff reward
            (quittingQuantileClockCompressedProfile reward profile level)
            observer| ≤ quantileClockRadius ι level) ∧
      (∀ who choice, ∃ mapped,
        |quittingTerminalPayoff reward
            (Function.update profile who
              (quittingPureTimeBehaviorStrategy reward who choice)) who -
          quittingTerminalPayoff reward
            (Function.update
              (quittingQuantileClockCompressedProfile reward profile level) who
              (quittingPureTimeBehaviorStrategy reward who mapped)) who| ≤
            quantileClockRadius ι level) ∧
      (∀ who choice, ∃ mapped,
        |quittingTerminalPayoff reward
            (Function.update
              (quittingQuantileClockCompressedProfile reward profile level) who
              (quittingPureTimeBehaviorStrategy reward who choice)) who -
          quittingTerminalPayoff reward
            (Function.update profile who
              (quittingPureTimeBehaviorStrategy reward who mapped)) who| ≤
            quantileClockRadius ι level)

/-- The active-cell common-quantile construction satisfies full two-sided
payoff transport at the sharp normalized radius. -/
theorem hasEscapeAwareQuantileClockPayoffTransport_of_normalized
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hreward : ∀ terminal player, |reward terminal player| ≤ 1) :
    HasEscapeAwareQuantileClockPayoffTransport reward := by
  intro profile level hlevel
  refine ⟨abs_quittingTerminalPayoff_sub_quantileClockCompressed_le
      reward hreward profile hlevel, ?_, ?_⟩
  · intro who choice
    exact ⟨Math.Probability.finiteClockActiveQuotient
        (quittingQuantileClockMarks reward profile level) choice,
      abs_quittingTerminalPayoff_update_pureTime_sub_compressed_mapped_le
        reward hreward profile hlevel who choice⟩
  · intro who choice
    exact
      exists_abs_quittingTerminalPayoff_compressed_pureTime_sub_update_le
        reward hreward profile hlevel who choice

/-- Every executable semantic pair admits a finite-clock representative at
the radius scaled by an explicit absolute reward bound. -/
def HasEscapeAwareQuantileClockCompressionAtBound
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (bound : ℝ) : Prop :=
  ∀ profile : (quittingGame reward).BehaviorProfile,
    ∀ level, 0 < level →
      semanticPairWithin (quantileClockScaledRadius ι bound level)
        (quittingTerminalSemanticPair reward profile)
        (quittingTerminalSemanticPair reward
          (quittingQuantileClockCompressedProfile reward profile level))

theorem hasEscapeAwareQuantileClockCompressionAtBound_of_payoffTransport
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (bound : ℝ)
    (htransport :
      HasEscapeAwareQuantileClockPayoffTransportAtBound reward bound) :
    HasEscapeAwareQuantileClockCompressionAtBound reward bound := by
  intro profile level hlevel
  obtain ⟨hpayoff, hforward, hbackward⟩ :=
    htransport profile level hlevel
  constructor
  · exact hpayoff
  · intro who
    exact abs_quittingContinuationBestResponseValue_sub_le_of_mutual_pureTime
      reward profile
      (quittingQuantileClockCompressedProfile reward profile level) who
      (hforward who) (hbackward who)

/-- Arbitrarily bounded terminal rewards have canonical finite-clock
semantic compression, with the literal unrestricted behavioral cap and exact
Never atom. -/
theorem hasEscapeAwareQuantileClockCompressionAtBound
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {bound : ℝ} (hbound : 0 ≤ bound)
    (hreward : ∀ terminal player, |reward terminal player| ≤ bound) :
    HasEscapeAwareQuantileClockCompressionAtBound reward bound :=
  hasEscapeAwareQuantileClockCompressionAtBound_of_payoffTransport reward bound
    (hasEscapeAwareQuantileClockPayoffTransportAtBound
      reward hbound hreward)

/-- The canonical game-specific reward bound always discharges the scaled
compression hypothesis. -/
theorem hasEscapeAwareQuantileClockCompressionAtRewardBound
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    HasEscapeAwareQuantileClockCompressionAtBound reward
      (quittingRewardBound reward) :=
  hasEscapeAwareQuantileClockCompressionAtBound reward
    (quittingRewardBound_nonneg reward)
    (abs_reward_le_quittingRewardBound reward)

/-- Every executable semantic pair admits a finite-clock representative at the
stated support and coordinatewise rate.
The envelope coordinate in `semanticPairWithin` is the unrestricted
behavioral cap, not a finite-horizon verifier. -/
def HasEscapeAwareQuantileClockCompression
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) : Prop :=
  ∀ profile : (quittingGame reward).BehaviorProfile,
    ∀ level, 0 < level →
      semanticPairWithin (quantileClockRadius ι level)
        (quittingTerminalSemanticPair reward profile)
        (quittingTerminalSemanticPair reward
          (quittingQuantileClockCompressedProfile reward profile level))

theorem hasEscapeAwareQuantileClockCompression_of_payoffTransport
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (htransport : HasEscapeAwareQuantileClockPayoffTransport reward) :
    HasEscapeAwareQuantileClockCompression reward := by
  intro profile level hlevel
  obtain ⟨hpayoff, hforward, hbackward⟩ :=
    htransport profile level hlevel
  constructor
  · exact hpayoff
  · intro who
    exact abs_quittingContinuationBestResponseValue_sub_le_of_mutual_pureTime
      reward profile
      (quittingQuantileClockCompressedProfile reward profile level) who
      (hforward who) (hbackward who)

/-- Normalized terminal rewards have the canonical finite-clock semantic
compression, with the literal unrestricted behavioral cap and exact Never
atom. -/
theorem hasEscapeAwareQuantileClockCompression_of_normalized
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hreward : ∀ terminal player, |reward terminal player| ≤ 1) :
    HasEscapeAwareQuantileClockCompression reward :=
  hasEscapeAwareQuantileClockCompression_of_payoffTransport reward
    (hasEscapeAwareQuantileClockPayoffTransport_of_normalized reward hreward)

omit [DecidableEq ι] in
theorem dist_le_of_semanticPairWithin
    {radius : ℝ} (hradius : 0 ≤ radius)
    {first second : QuittingTerminalSemanticPair ι}
    (hwithin : semanticPairWithin radius first second) :
    dist first second ≤ radius := by
  rw [Prod.dist_eq]
  apply max_le
  · rw [dist_pi_le_iff hradius]
    intro who
    simpa only [Real.dist_eq] using hwithin.1 who
  · rw [dist_pi_le_iff hradius]
    intro who
    simpa only [Real.dist_eq] using hwithin.2 who

omit [DecidableEq ι] in
theorem semanticPairWithin_dist
    (first second : QuittingTerminalSemanticPair ι) :
    semanticPairWithin (dist first second) first second := by
  constructor
  · intro who
    have hfirst : dist first.1 second.1 ≤ dist first second := by
      rw [Prod.dist_eq]
      exact le_max_left _ _
    rw [← Real.dist_eq]
    exact ((dist_pi_le_iff dist_nonneg).mp hfirst) who
  · intro who
    have hsecond : dist first.2 second.2 ≤ dist first second := by
      rw [Prod.dist_eq]
      exact le_max_right _ _
    rw [← Real.dist_eq]
    exact ((dist_pi_le_iff dist_nonneg).mp hsecond) who

/-! ## Literal finite-clock density -/

/-- Directed union of literal finite-clock semantic pairs along the canonical
cofinal support sequence.  Membership retains an actual independent stopping-
law profile; this is not a closure-defined set. -/
def quittingCofinalFiniteClockSemanticPairs
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    Set (QuittingTerminalSemanticPair ι) :=
  ⋃ level : ℕ, quittingFiniteClockSemanticReachable reward
    (quantileClockSupport ι (level + 1))

theorem quittingCofinalFiniteClockSemanticPairs_nonempty
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    (quittingCofinalFiniteClockSemanticPairs reward).Nonempty := by
  obtain ⟨pair, hpair⟩ := quittingFiniteClockSemanticReachable_nonempty
    reward (quantileClockSupport ι 1)
  exact ⟨pair, Set.mem_iUnion.mpr ⟨0, by simpa using hpair⟩⟩

theorem quittingCofinalFiniteClockSemanticPairs_subset_carrier
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    quittingCofinalFiniteClockSemanticPairs reward ⊆
      quittingTerminalSemanticCarrier reward := by
  rintro pair hpair
  obtain ⟨level, hpair⟩ := Set.mem_iUnion.mp hpair
  exact quittingFiniteClockSemanticReachable_subset_carrier
    reward (quantileClockSupport ι (level + 1)) hpair

/-- For one executable source profile, its canonical compressed semantic pairs
converge at the explicit cofinal clock levels. -/
theorem tendsto_quittingQuantileClockCompressed_semanticPair
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) :
    Tendsto (fun level => quittingTerminalSemanticPair reward
        (quittingQuantileClockCompressedProfile reward profile (level + 1)))
      atTop (nhds (quittingTerminalSemanticPair reward profile)) := by
  rw [Metric.tendsto_atTop]
  intro epsilon hepsilon
  have hradius := (quantileClockScaledRadius_tendsto_zero ι
    (quittingRewardBound reward)).comp (tendsto_add_atTop_nat 1)
  obtain ⟨threshold, hthreshold⟩ :=
    (Metric.tendsto_atTop.mp hradius) epsilon hepsilon
  refine ⟨threshold, fun level hlevel => ?_⟩
  rw [dist_comm]
  exact lt_of_le_of_lt
    (dist_le_of_semanticPairWithin
      (quantileClockScaledRadius_nonneg ι
        (quittingRewardBound_nonneg reward) (level + 1))
      (hasEscapeAwareQuantileClockCompressionAtRewardBound reward
        profile (level + 1) (Nat.zero_lt_succ level)))
    (by
      simpa [Real.dist_eq, abs_of_nonneg
        (quantileClockScaledRadius_nonneg ι
          (quittingRewardBound_nonneg reward) (level + 1))] using
        hthreshold level hlevel)

/-- Every carrier point is a sequential limit of literal finite-clock pairs,
with the `level`th pair realized at exactly the canonical cofinal support
`quantileClockSupport ι (level + 1)`.  The conclusion does not realize the
limit point itself by a profile. -/
theorem exists_cofinalFiniteClockSemanticPair_sequence_tendsto
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward) :
    ∃ approximants : ℕ → QuittingTerminalSemanticPair ι,
      (∀ level, approximants level ∈
        quittingFiniteClockSemanticReachable reward
          (quantileClockSupport ι (level + 1))) ∧
      Tendsto approximants atTop (nhds pair) := by
  obtain ⟨profiles, hprofiles⟩ :=
    exists_terminalProfile_sequence_tendsto_semanticPair reward pair hpair
  let approximants := fun level => quittingTerminalSemanticPair reward
    (quittingQuantileClockCompressedProfile reward
      (profiles level) (level + 1))
  refine ⟨approximants, ?_, ?_⟩
  · intro level
    exact quittingQuantileClockCompressed_semanticPair_mem_reachable
      reward (profiles level) (level + 1)
  · apply tendsto_iff_dist_tendsto_zero.mpr
    have hsourceDist : Tendsto
        (fun level => dist
          (quittingTerminalSemanticPair reward (profiles level)) pair)
        atTop (nhds 0) :=
      tendsto_iff_dist_tendsto_zero.mp hprofiles
    have hradius : Tendsto
        (fun level => quantileClockScaledRadius ι
          (quittingRewardBound reward) (level + 1))
        atTop (nhds 0) :=
      (quantileClockScaledRadius_tendsto_zero ι
        (quittingRewardBound reward)).comp (tendsto_add_atTop_nat 1)
    apply squeeze_zero'
      (g := fun level => quantileClockScaledRadius ι
        (quittingRewardBound reward) (level + 1) +
          dist (quittingTerminalSemanticPair reward (profiles level)) pair)
    · exact Eventually.of_forall fun _ => dist_nonneg
    · exact Eventually.of_forall fun level => by
        calc
          dist (approximants level) pair ≤
              dist (approximants level)
                  (quittingTerminalSemanticPair reward (profiles level)) +
                dist (quittingTerminalSemanticPair reward (profiles level))
                  pair := dist_triangle _ _ _
          _ ≤ quantileClockScaledRadius ι
                  (quittingRewardBound reward) (level + 1) +
                dist (quittingTerminalSemanticPair reward (profiles level))
                  pair := by
              gcongr
              rw [dist_comm]
              exact dist_le_of_semanticPairWithin
                (quantileClockScaledRadius_nonneg ι
                  (quittingRewardBound_nonneg reward) (level + 1))
                (hasEscapeAwareQuantileClockCompressionAtRewardBound reward
                  (profiles level) (level + 1) (Nat.zero_lt_succ level))
    · simpa using hradius.add hsourceDist

/-- Literal finite-clock semantic pairs are dense in the full compact carrier.
This equality is only a closure statement. -/
theorem closure_quittingCofinalFiniteClockSemanticPairs_eq_carrier
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    closure (quittingCofinalFiniteClockSemanticPairs reward) =
      quittingTerminalSemanticCarrier reward := by
  apply Set.Subset.antisymm
  · exact closure_minimal
      (quittingCofinalFiniteClockSemanticPairs_subset_carrier reward)
      (quittingTerminalSemanticCarrier_isCompact reward).isClosed
  · intro pair hpair
    obtain ⟨approximants, hlevels, htendsto⟩ :=
      exists_cofinalFiniteClockSemanticPair_sequence_tendsto
        reward pair hpair
    apply mem_closure_iff_seq_limit.mpr
    refine ⟨approximants, ?_, htendsto⟩
    intro level
    exact Set.mem_iUnion.mpr ⟨level, hlevels level⟩

omit [Fintype ι] [DecidableEq ι] in
/-- A continuous real score has the same lower bounds on a set and on any
containing set equal to its closure. -/
theorem lowerBounds_image_eq_of_subset_closure_eq
    {Point : Type*} [PseudoMetricSpace Point]
    {approximants carrier : Set Point}
    (hsubset : approximants ⊆ carrier)
    (hclosure : closure approximants = carrier)
    (score : Point → ℝ) (hscore : Continuous score) :
    lowerBounds (score '' approximants) = lowerBounds (score '' carrier) := by
  apply Set.Subset.antisymm
  · intro bound hbound value hvalue
    obtain ⟨point, hpoint, rfl⟩ := hvalue
    rw [← hclosure] at hpoint
    obtain ⟨sequence, hsequence, htendsto⟩ :=
      mem_closure_iff_seq_limit.mp hpoint
    apply ge_of_tendsto
      (hscore.continuousAt.tendsto.comp htendsto)
    exact Eventually.of_forall fun level => hbound
      ⟨sequence level, hsequence level, rfl⟩
  · intro bound hbound value hvalue
    obtain ⟨point, hpoint, rfl⟩ := hvalue
    exact hbound ⟨point, hsubset hpoint, rfl⟩

omit [Fintype ι] [DecidableEq ι] in
/-- A continuous real score has the same infimum on a nonempty set and on a
containing set equal to its closure. -/
theorem sInf_image_eq_of_subset_closure_eq
    {Point : Type*} [PseudoMetricSpace Point]
    {approximants carrier : Set Point}
    (happroximants : approximants.Nonempty)
    (hsubset : approximants ⊆ carrier)
    (hclosure : closure approximants = carrier)
    (score : Point → ℝ) (hscore : Continuous score)
    (hbounded : BddBelow (score '' carrier)) :
    sInf (score '' approximants) = sInf (score '' carrier) := by
  have hboundedApproximants : BddBelow (score '' approximants) :=
    hbounded.mono (Set.image_mono hsubset)
  have hbounds := lowerBounds_image_eq_of_subset_closure_eq
    hsubset hclosure score hscore
  have hglbApproximants := isGLB_csInf
    (happroximants.image score) hboundedApproximants
  have hglbCarrier := isGLB_csInf
    ((happroximants.mono hsubset).image score) hbounded
  apply hglbApproximants.unique
  constructor
  · rw [hbounds]
    exact hglbCarrier.1
  · intro bound hbound
    apply hglbCarrier.2
    rw [← hbounds]
    exact hbound

/-- Every continuous real score has the same infimum on the literal cofinal
finite-clock union and on the full compact semantic carrier. -/
theorem sInf_image_quittingCofinalFiniteClockSemanticPairs_eq_carrier
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (score : QuittingTerminalSemanticPair ι → ℝ)
    (hscore : Continuous score) :
    sInf (score '' quittingCofinalFiniteClockSemanticPairs reward) =
      sInf (score '' quittingTerminalSemanticCarrier reward) := by
  apply sInf_image_eq_of_subset_closure_eq
    (quittingCofinalFiniteClockSemanticPairs_nonempty reward)
    (quittingCofinalFiniteClockSemanticPairs_subset_carrier reward)
    (closure_quittingCofinalFiniteClockSemanticPairs_eq_carrier reward)
    score hscore
  exact (quittingTerminalSemanticCarrier_isCompact reward).image hscore
    |>.bddBelow

variable [Nonempty ι]

/-- Continuous terminal exploitability has the same infimum on literal
finite-clock profiles as on all behavioral profiles. -/
theorem sInf_image_quittingCofinalFiniteClockSemanticExploitability
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    sInf (quittingTerminalSemanticExploitability ''
        quittingCofinalFiniteClockSemanticPairs reward) =
      quittingTerminalExploitabilityInf reward := by
  rw [sInf_image_quittingCofinalFiniteClockSemanticPairs_eq_carrier
    reward quittingTerminalSemanticExploitability
    continuous_quittingTerminalSemanticExploitability]
  have hattainableNonempty :
      (quittingAttainableTerminalSemanticPairs reward).Nonempty := by
    exact ⟨quittingTerminalSemanticPair reward
        (quittingAlwaysContinueProfile reward),
      quittingAlwaysContinueProfile reward, rfl⟩
  have hcarrierInf :
      sInf (quittingTerminalSemanticExploitability ''
          quittingAttainableTerminalSemanticPairs reward) =
        sInf (quittingTerminalSemanticExploitability ''
          quittingTerminalSemanticCarrier reward) := by
    apply sInf_image_eq_of_subset_closure_eq
      hattainableNonempty subset_closure rfl
      quittingTerminalSemanticExploitability
      continuous_quittingTerminalSemanticExploitability
    exact (quittingTerminalSemanticCarrier_isCompact reward).image
      continuous_quittingTerminalSemanticExploitability |>.bddBelow
  rw [← hcarrierInf]
  unfold quittingTerminalExploitabilityInf
  congr 1
  ext value
  constructor
  · rintro ⟨pair, ⟨profile, rfl⟩, rfl⟩
    exact ⟨profile,
      quittingTerminalSemanticExploitability_pair reward profile⟩
  · rintro ⟨profile, rfl⟩
    exact ⟨quittingTerminalSemanticPair reward profile,
      ⟨profile, rfl⟩,
      quittingTerminalSemanticExploitability_pair reward profile⟩

omit [DecidableEq ι] in
theorem quittingTerminalSemanticExploitability_nonneg
    (pair : QuittingTerminalSemanticPair ι) :
    0 ≤ quittingTerminalSemanticExploitability pair := by
  let who : ι := Classical.choice inferInstance
  exact (le_max_left 0 _).trans
    (le_finitePlayerMax
      (fun player => max 0 (quittingTerminalSemanticDebt pair player)) who)

omit [DecidableEq ι] in
theorem abs_quittingTerminalSemanticExploitability_sub_le
    (first second : QuittingTerminalSemanticPair ι) :
    |quittingTerminalSemanticExploitability first -
        quittingTerminalSemanticExploitability second| ≤
      2 * dist first second := by
  let radius := dist first second
  have hradius : 0 ≤ radius := dist_nonneg
  have hwithin : semanticPairWithin radius first second :=
    semanticPairWithin_dist first second
  have hdebt : ∀ who,
      |quittingTerminalSemanticDebt first who -
          quittingTerminalSemanticDebt second who| ≤ 2 * radius := by
    intro who
    unfold quittingTerminalSemanticDebt
    rw [show (first.2 who - first.1 who) -
        (second.2 who - second.1 who) =
      (first.2 who - second.2 who) -
        (first.1 who - second.1 who) by ring]
    calc
      |(first.2 who - second.2 who) -
          (first.1 who - second.1 who)| ≤
          |first.2 who - second.2 who| +
            |first.1 who - second.1 who| := by
        exact abs_sub _ _
      _ ≤ radius + radius := add_le_add (hwithin.2 who) (hwithin.1 who)
      _ = 2 * radius := by ring
  have hforward : quittingTerminalSemanticExploitability first ≤
      quittingTerminalSemanticExploitability second + 2 * radius := by
    unfold quittingTerminalSemanticExploitability
    apply finitePlayerMax_le
    intro who
    calc
      max 0 (quittingTerminalSemanticDebt first who) ≤
          max 0 (quittingTerminalSemanticDebt second who) + 2 * radius := by
        have hmax := abs_max_sub_max_le_max
          0 (quittingTerminalSemanticDebt first who)
          0 (quittingTerminalSemanticDebt second who)
        have hsigned : max 0 (quittingTerminalSemanticDebt first who) -
            max 0 (quittingTerminalSemanticDebt second who) ≤
            2 * radius := by
          refine (le_abs_self _).trans (hmax.trans ?_)
          simpa using hdebt who
        linarith
      _ ≤ finitePlayerMax
          (fun player => max 0
            (quittingTerminalSemanticDebt second player)) + 2 * radius :=
        by
          simpa [add_comm] using add_le_add_right (le_finitePlayerMax
            (fun player => max 0
              (quittingTerminalSemanticDebt second player)) who) (2 * radius)
  have hbackward : quittingTerminalSemanticExploitability second ≤
      quittingTerminalSemanticExploitability first + 2 * radius := by
    unfold quittingTerminalSemanticExploitability
    apply finitePlayerMax_le
    intro who
    calc
      max 0 (quittingTerminalSemanticDebt second who) ≤
          max 0 (quittingTerminalSemanticDebt first who) + 2 * radius := by
        have hmax := abs_max_sub_max_le_max
          0 (quittingTerminalSemanticDebt second who)
          0 (quittingTerminalSemanticDebt first who)
        have hsigned : max 0 (quittingTerminalSemanticDebt second who) -
            max 0 (quittingTerminalSemanticDebt first who) ≤
            2 * radius := by
          refine (le_abs_self _).trans (hmax.trans ?_)
          simpa [abs_sub_comm] using hdebt who
        linarith
      _ ≤ finitePlayerMax
          (fun player => max 0
            (quittingTerminalSemanticDebt first player)) + 2 * radius :=
        by
          simpa [add_comm] using add_le_add_right (le_finitePlayerMax
            (fun player => max 0
              (quittingTerminalSemanticDebt first player)) who) (2 * radius)
  rw [abs_le]
  constructor <;> dsimp [radius] at * <;> linarith

/-- Topological hierarchy system generated by the exact finite-clock centers.
Its only non-structural input is the named common-quantile compression
proposition. -/
def escapeAwareQuantileClockSystem
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hcompression : HasEscapeAwareQuantileClockCompression reward) :
    NestedOuterApproximation (QuittingTerminalSemanticPair ι) where
  attainable := quittingAttainableTerminalSemanticPairs reward
  center level := quittingFiniteClockSemanticCenter reward
    (quantileClockSupport ι level)
  radius := quantileClockRadius ι
  attainable_nonempty := by
    exact ⟨quittingTerminalSemanticPair reward
        (quittingAlwaysContinueProfile reward),
      quittingAlwaysContinueProfile reward, rfl⟩
  center_nonempty level := quittingFiniteClockSemanticCenter_nonempty reward _
  center_compact level := quittingFiniteClockSemanticCenter_isCompact reward _
  center_subset_closure level := by
    simpa only [quittingTerminalSemanticCarrier] using
      quittingFiniteClockSemanticCenter_subset_carrier reward _
  radius_nonneg := quantileClockRadius_nonneg ι
  radius_tendsto_zero := quantileClockRadius_tendsto_zero ι
  attainable_infDist_le := by
    rintro pair ⟨profile, rfl⟩ level hlevel
    exact (Metric.infDist_le_dist_of_mem
      (quittingQuantileClockCompressed_semanticPair_mem_reachable
        reward profile level)).trans
      (dist_le_of_semanticPairWithin
        (quantileClockRadius_nonneg ι level)
        (hcompression profile level hlevel))

/-- Finite-clock outer-approximation system at an explicit absolute terminal
reward bound. -/
def escapeAwareQuantileClockSystemAtBound
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (bound : ℝ) (hbound : 0 ≤ bound)
    (hcompression : HasEscapeAwareQuantileClockCompressionAtBound
      reward bound) :
    NestedOuterApproximation (QuittingTerminalSemanticPair ι) where
  attainable := quittingAttainableTerminalSemanticPairs reward
  center level := quittingFiniteClockSemanticCenter reward
    (quantileClockSupport ι level)
  radius := quantileClockScaledRadius ι bound
  attainable_nonempty := by
    exact ⟨quittingTerminalSemanticPair reward
        (quittingAlwaysContinueProfile reward),
      quittingAlwaysContinueProfile reward, rfl⟩
  center_nonempty level := quittingFiniteClockSemanticCenter_nonempty reward _
  center_compact level := quittingFiniteClockSemanticCenter_isCompact reward _
  center_subset_closure level := by
    simpa only [quittingTerminalSemanticCarrier] using
      quittingFiniteClockSemanticCenter_subset_carrier reward _
  radius_nonneg := quantileClockScaledRadius_nonneg ι hbound
  radius_tendsto_zero := quantileClockScaledRadius_tendsto_zero ι bound
  attainable_infDist_le := by
    rintro pair ⟨profile, rfl⟩ level hlevel
    exact (Metric.infDist_le_dist_of_mem
      (quittingQuantileClockCompressed_semanticPair_mem_reachable
        reward profile level)).trans
      (dist_le_of_semanticPairWithin
        (quantileClockScaledRadius_nonneg ι hbound level)
        (hcompression profile level hlevel))

/-- Outer hierarchy at a finite level. -/
def escapeAwareQuantileClockOuter
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hcompression : HasEscapeAwareQuantileClockCompression reward)
    (level : ℕ) : Set (QuittingTerminalSemanticPair ι) :=
  (escapeAwareQuantileClockSystem reward hcompression).nestedOuter level

/-- Scaled outer hierarchy at a finite level. -/
def escapeAwareQuantileClockOuterAtBound
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (bound : ℝ) (hbound : 0 ≤ bound)
    (hcompression : HasEscapeAwareQuantileClockCompressionAtBound
      reward bound)
    (level : ℕ) : Set (QuittingTerminalSemanticPair ι) :=
  (escapeAwareQuantileClockSystemAtBound
    reward bound hbound hcompression).nestedOuter level

omit [Nonempty ι] in
/-- The nested hierarchy converges exactly to the terminal semantic carrier,
including carrier points not realized by one behavior profile. -/
theorem iInter_escapeAwareQuantileClockOuter_eq_carrier
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hcompression : HasEscapeAwareQuantileClockCompression reward) :
    (⋂ level, escapeAwareQuantileClockOuter reward hcompression level) =
      quittingTerminalSemanticCarrier reward := by
  simpa only [escapeAwareQuantileClockOuter,
    escapeAwareQuantileClockSystem, quittingTerminalSemanticCarrier] using
    (escapeAwareQuantileClockSystem reward hcompression).iInter_nestedOuter

omit [Nonempty ι] in
/-- Under normalized rewards, the canonical finite-clock outer hierarchy
unconditionally converges to the full terminal semantic carrier. -/
theorem iInter_escapeAwareQuantileClockOuter_normalized_eq_carrier
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hreward : ∀ terminal player, |reward terminal player| ≤ 1) :
    (⋂ level, escapeAwareQuantileClockOuter reward
      (hasEscapeAwareQuantileClockCompression_of_normalized reward hreward)
      level) = quittingTerminalSemanticCarrier reward :=
  iInter_escapeAwareQuantileClockOuter_eq_carrier reward
    (hasEscapeAwareQuantileClockCompression_of_normalized reward hreward)

omit [Nonempty ι] in
/-- At every nonnegative explicit reward bound, the scaled finite-clock outer
hierarchy converges exactly to the terminal semantic carrier. -/
theorem iInter_escapeAwareQuantileClockOuterAtBound_eq_carrier
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (bound : ℝ) (hbound : 0 ≤ bound)
    (hcompression : HasEscapeAwareQuantileClockCompressionAtBound
      reward bound) :
    (⋂ level, escapeAwareQuantileClockOuterAtBound reward bound hbound
      hcompression level) = quittingTerminalSemanticCarrier reward := by
  simpa only [escapeAwareQuantileClockOuterAtBound,
    escapeAwareQuantileClockSystemAtBound,
    quittingTerminalSemanticCarrier] using
    (escapeAwareQuantileClockSystemAtBound
      reward bound hbound hcompression).iInter_nestedOuter

omit [Nonempty ι] in
/-- The canonical reward bound gives an unconditional finite-clock outer
hierarchy for every finite quitting reward table. -/
theorem iInter_escapeAwareQuantileClockOuterAtRewardBound_eq_carrier
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    (⋂ level, escapeAwareQuantileClockOuterAtBound reward
      (quittingRewardBound reward) (quittingRewardBound_nonneg reward)
      (hasEscapeAwareQuantileClockCompressionAtRewardBound reward) level) =
        quittingTerminalSemanticCarrier reward :=
  iInter_escapeAwareQuantileClockOuterAtBound_eq_carrier reward
    (quittingRewardBound reward) (quittingRewardBound_nonneg reward)
    (hasEscapeAwareQuantileClockCompressionAtRewardBound reward)

/-- Certified lower objective over the finite outer hierarchy. -/
def escapeAwareQuantileClockLower
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hcompression : HasEscapeAwareQuantileClockCompression reward)
    (level : ℕ) : ℝ :=
  (escapeAwareQuantileClockSystem reward hcompression).lowerValue
    quittingTerminalSemanticExploitability level

/-- Upper objective over the closed finite-clock center. -/
def escapeAwareQuantileClockUpper
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hcompression : HasEscapeAwareQuantileClockCompression reward)
    (level : ℕ) : ℝ :=
  (escapeAwareQuantileClockSystem reward hcompression).upperValue
    quittingTerminalSemanticExploitability level

/-- Certified lower objective over the scaled finite outer hierarchy. -/
def escapeAwareQuantileClockLowerAtBound
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (bound : ℝ) (hbound : 0 ≤ bound)
    (hcompression : HasEscapeAwareQuantileClockCompressionAtBound
      reward bound)
    (level : ℕ) : ℝ :=
  (escapeAwareQuantileClockSystemAtBound
    reward bound hbound hcompression).lowerValue
      quittingTerminalSemanticExploitability level

/-- Upper objective over the finite-clock center, paired with the scaled
outer hierarchy. -/
def escapeAwareQuantileClockUpperAtBound
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (bound : ℝ) (hbound : 0 ≤ bound)
    (hcompression : HasEscapeAwareQuantileClockCompressionAtBound
      reward bound)
    (level : ℕ) : ℝ :=
  (escapeAwareQuantileClockSystemAtBound
    reward bound hbound hcompression).upperValue
      quittingTerminalSemanticExploitability level

theorem escapeAwareQuantileClockLowerAtBound_nonneg
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (bound : ℝ) (hbound : 0 ≤ bound)
    (hcompression : HasEscapeAwareQuantileClockCompressionAtBound
      reward bound)
    (level : ℕ) :
    0 ≤ escapeAwareQuantileClockLowerAtBound
      reward bound hbound hcompression level := by
  exact (escapeAwareQuantileClockSystemAtBound
    reward bound hbound hcompression).floor_le_lowerValue
      quittingTerminalSemanticExploitability
      quittingTerminalSemanticExploitability_nonneg level

/-- The scaled finite-clock upper value is attained by one literal product
stopping-law semantic pair. -/
theorem exists_finiteClockSemanticPair_exploitability_eq_upperAtBound
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (bound : ℝ) (hbound : 0 ≤ bound)
    (hcompression : HasEscapeAwareQuantileClockCompressionAtBound
      reward bound)
    (level : ℕ) :
    ∃ pair ∈ quittingFiniteClockSemanticReachable reward
        (quantileClockSupport ι level),
      quittingTerminalSemanticExploitability pair =
        escapeAwareQuantileClockUpperAtBound
          reward bound hbound hcompression level := by
  exact NestedOuterApproximation.exists_mem_center_score_eq_upperValue
    (escapeAwareQuantileClockSystemAtBound
      reward bound hbound hcompression)
    quittingTerminalSemanticExploitability
    continuous_quittingTerminalSemanticExploitability level

/-- Every finite outer lower bound is nonnegative. -/
theorem escapeAwareQuantileClockLower_nonneg
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hcompression : HasEscapeAwareQuantileClockCompression reward)
    (level : ℕ) :
    0 ≤ escapeAwareQuantileClockLower reward hcompression level := by
  exact (escapeAwareQuantileClockSystem reward hcompression).floor_le_lowerValue
    quittingTerminalSemanticExploitability
    quittingTerminalSemanticExploitability_nonneg level

/-- Every finite-clock upper value is nonnegative. -/
theorem escapeAwareQuantileClockUpper_nonneg
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hcompression : HasEscapeAwareQuantileClockCompression reward)
    (level : ℕ) :
    0 ≤ escapeAwareQuantileClockUpper reward hcompression level := by
  exact (escapeAwareQuantileClockSystem reward hcompression).floor_le_upperValue
    quittingTerminalSemanticExploitability
    quittingTerminalSemanticExploitability_nonneg level

/-- The finite-clock upper value is attained by one literal finite-clock
semantic pair, hence by an actual independent stopping-law profile retaining
its Never atoms. -/
theorem exists_finiteClockSemanticPair_exploitability_eq_upper
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hcompression : HasEscapeAwareQuantileClockCompression reward)
    (level : ℕ) :
    ∃ pair ∈ quittingFiniteClockSemanticReachable reward
        (quantileClockSupport ι level),
      quittingTerminalSemanticExploitability pair =
        escapeAwareQuantileClockUpper reward hcompression level := by
  exact NestedOuterApproximation.exists_mem_center_score_eq_upperValue
    (escapeAwareQuantileClockSystem reward hcompression)
    quittingTerminalSemanticExploitability
    continuous_quittingTerminalSemanticExploitability level

theorem escapeAwareQuantileClock_attainableInf_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hcompression : HasEscapeAwareQuantileClockCompression reward) :
    (escapeAwareQuantileClockSystem reward hcompression).attainableInf
        quittingTerminalSemanticExploitability =
      quittingTerminalExploitabilityInf reward := by
  unfold NestedOuterApproximation.attainableInf
    quittingTerminalExploitabilityInf
  congr 1
  ext value
  constructor
  · rintro ⟨pair, ⟨profile, rfl⟩, rfl⟩
    exact ⟨profile, quittingTerminalSemanticExploitability_pair reward profile⟩
  · rintro ⟨profile, rfl⟩
    exact ⟨quittingTerminalSemanticPair reward profile,
      ⟨profile, rfl⟩,
      quittingTerminalSemanticExploitability_pair reward profile⟩

theorem escapeAwareQuantileClockAtBound_attainableInf_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (bound : ℝ) (hbound : 0 ≤ bound)
    (hcompression : HasEscapeAwareQuantileClockCompressionAtBound
      reward bound) :
    NestedOuterApproximation.attainableInf
        (escapeAwareQuantileClockSystemAtBound
          reward bound hbound hcompression)
        quittingTerminalSemanticExploitability =
      quittingTerminalExploitabilityInf reward := by
  unfold NestedOuterApproximation.attainableInf
    quittingTerminalExploitabilityInf
  congr 1
  ext value
  constructor
  · rintro ⟨pair, ⟨profile, rfl⟩, rfl⟩
    exact ⟨profile, quittingTerminalSemanticExploitability_pair reward profile⟩
  · rintro ⟨profile, rfl⟩
    exact ⟨quittingTerminalSemanticPair reward profile,
      ⟨profile, rfl⟩,
      quittingTerminalSemanticExploitability_pair reward profile⟩

/-- Every outer lower value is below the true executable exploitability
infimum, including the unconstrained level zero. -/
theorem escapeAwareQuantileClockLower_le_exploitabilityInf
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hcompression : HasEscapeAwareQuantileClockCompression reward)
    (level : ℕ) :
    escapeAwareQuantileClockLower reward hcompression level ≤
      quittingTerminalExploitabilityInf reward := by
  have hle := NestedOuterApproximation.lowerValue_le_attainableInf
    (escapeAwareQuantileClockSystem reward hcompression)
    quittingTerminalSemanticExploitability
    quittingTerminalSemanticExploitability_nonneg level
  rwa [escapeAwareQuantileClock_attainableInf_eq reward hcompression] at hle

/-- Quantitative lower/upper bracket from the analytic compression input.
The factor `2` is the exact metric modulus of terminal exploitability. -/
theorem escapeAwareQuantileClock_quantitative_bracket
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hcompression : HasEscapeAwareQuantileClockCompression reward)
    {level : ℕ} (hlevel : 0 < level) :
    escapeAwareQuantileClockLower reward hcompression level ≤
        quittingTerminalExploitabilityInf reward ∧
      quittingTerminalExploitabilityInf reward ≤
        escapeAwareQuantileClockUpper reward hcompression level ∧
      escapeAwareQuantileClockUpper reward hcompression level -
          escapeAwareQuantileClockLower reward hcompression level ≤
        2 * quantileClockRadius ι level := by
  have hbracket :=
    (escapeAwareQuantileClockSystem reward hcompression).quantitative_bracket
      quittingTerminalSemanticExploitability
      (floor := 0) (modulus := 2)
      quittingTerminalSemanticExploitability_nonneg
      continuous_quittingTerminalSemanticExploitability
      (by norm_num)
      abs_quittingTerminalSemanticExploitability_sub_le hlevel
  rw [escapeAwareQuantileClock_attainableInf_eq reward hcompression] at hbracket
  change escapeAwareQuantileClockLower reward hcompression level ≤
        quittingTerminalExploitabilityInf reward ∧
      quittingTerminalExploitabilityInf reward ≤
        escapeAwareQuantileClockUpper reward hcompression level ∧
      escapeAwareQuantileClockUpper reward hcompression level -
          escapeAwareQuantileClockLower reward hcompression level ≤
        2 * quantileClockRadius ι level at hbracket
  exact hbracket

/-- The normalized common-quantile producer discharges the analytic premise
of the general finite-player lower/upper bracket. -/
theorem escapeAwareQuantileClock_normalized_quantitative_bracket
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hreward : ∀ terminal player, |reward terminal player| ≤ 1)
    {level : ℕ} (hlevel : 0 < level) :
    escapeAwareQuantileClockLower reward
          (hasEscapeAwareQuantileClockCompression_of_normalized reward hreward)
          level ≤ quittingTerminalExploitabilityInf reward ∧
      quittingTerminalExploitabilityInf reward ≤
        escapeAwareQuantileClockUpper reward
          (hasEscapeAwareQuantileClockCompression_of_normalized reward hreward)
          level ∧
      escapeAwareQuantileClockUpper reward
            (hasEscapeAwareQuantileClockCompression_of_normalized reward hreward)
            level -
          escapeAwareQuantileClockLower reward
            (hasEscapeAwareQuantileClockCompression_of_normalized reward hreward)
            level ≤
        2 * quantileClockRadius ι level :=
  escapeAwareQuantileClock_quantitative_bracket reward
    (hasEscapeAwareQuantileClockCompression_of_normalized reward hreward)
    hlevel

/-- Quantitative lower/upper bracket for an explicit terminal-reward bound.
The objective gap is twice the scaled semantic radius. -/
theorem escapeAwareQuantileClockAtBound_quantitative_bracket
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (bound : ℝ) (hbound : 0 ≤ bound)
    (hcompression : HasEscapeAwareQuantileClockCompressionAtBound
      reward bound)
    {level : ℕ} (hlevel : 0 < level) :
    escapeAwareQuantileClockLowerAtBound reward bound hbound hcompression
          level ≤ quittingTerminalExploitabilityInf reward ∧
      quittingTerminalExploitabilityInf reward ≤
        escapeAwareQuantileClockUpperAtBound reward bound hbound hcompression
          level ∧
      escapeAwareQuantileClockUpperAtBound reward bound hbound hcompression
            level -
          escapeAwareQuantileClockLowerAtBound reward bound hbound hcompression
            level ≤
        2 * quantileClockScaledRadius ι bound level := by
  have hbracket :=
    NestedOuterApproximation.quantitative_bracket
        (escapeAwareQuantileClockSystemAtBound
          reward bound hbound hcompression)
        quittingTerminalSemanticExploitability
        (floor := 0) (modulus := 2)
        quittingTerminalSemanticExploitability_nonneg
        continuous_quittingTerminalSemanticExploitability
        (by norm_num)
        abs_quittingTerminalSemanticExploitability_sub_le hlevel
  rw [escapeAwareQuantileClockAtBound_attainableInf_eq
    reward bound hbound hcompression] at hbracket
  change escapeAwareQuantileClockLowerAtBound reward bound hbound hcompression
          level ≤ quittingTerminalExploitabilityInf reward ∧
      quittingTerminalExploitabilityInf reward ≤
        escapeAwareQuantileClockUpperAtBound reward bound hbound hcompression
          level ∧
      escapeAwareQuantileClockUpperAtBound reward bound hbound hcompression
            level -
          escapeAwareQuantileClockLowerAtBound reward bound hbound hcompression
            level ≤
        2 * quantileClockScaledRadius ι bound level at hbracket
  exact hbracket

/-- Every finite quitting reward table has the scaled finite-clock bracket at
its canonical absolute reward bound. -/
theorem escapeAwareQuantileClockAtRewardBound_quantitative_bracket
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {level : ℕ} (hlevel : 0 < level) :
    escapeAwareQuantileClockLowerAtBound reward
          (quittingRewardBound reward) (quittingRewardBound_nonneg reward)
          (hasEscapeAwareQuantileClockCompressionAtRewardBound reward)
          level ≤ quittingTerminalExploitabilityInf reward ∧
      quittingTerminalExploitabilityInf reward ≤
        escapeAwareQuantileClockUpperAtBound reward
          (quittingRewardBound reward) (quittingRewardBound_nonneg reward)
          (hasEscapeAwareQuantileClockCompressionAtRewardBound reward)
          level ∧
      escapeAwareQuantileClockUpperAtBound reward
            (quittingRewardBound reward) (quittingRewardBound_nonneg reward)
            (hasEscapeAwareQuantileClockCompressionAtRewardBound reward)
            level -
          escapeAwareQuantileClockLowerAtBound reward
            (quittingRewardBound reward) (quittingRewardBound_nonneg reward)
            (hasEscapeAwareQuantileClockCompressionAtRewardBound reward)
            level ≤
        2 * quantileClockScaledRadius ι (quittingRewardBound reward) level :=
  escapeAwareQuantileClockAtBound_quantitative_bracket reward
    (quittingRewardBound reward) (quittingRewardBound_nonneg reward)
    (hasEscapeAwareQuantileClockCompressionAtRewardBound reward) hlevel

/-- On the zero-infimum branch, the scaled hierarchy supplies an actual
finite-clock product profile at the scaled objective rate. -/
theorem exists_finiteClockSemanticPair_exploitability_le_of_inf_eq_zeroAtBound
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (bound : ℝ) (hbound : 0 ≤ bound)
    (hcompression : HasEscapeAwareQuantileClockCompressionAtBound
      reward bound)
    {level : ℕ} (hlevel : 0 < level)
    (hinf : quittingTerminalExploitabilityInf reward = 0) :
    ∃ pair ∈ quittingFiniteClockSemanticReachable reward
        (quantileClockSupport ι level),
      quittingTerminalSemanticExploitability pair ≤
        2 * quantileClockScaledRadius ι bound level := by
  obtain ⟨pair, hpair, hpairValue⟩ :=
    exists_finiteClockSemanticPair_exploitability_eq_upperAtBound
      reward bound hbound hcompression level
  obtain ⟨hlower, -, hgap⟩ :=
    escapeAwareQuantileClockAtBound_quantitative_bracket
      reward bound hbound hcompression hlevel
  have hlowerNonneg := escapeAwareQuantileClockLowerAtBound_nonneg
    reward bound hbound hcompression level
  refine ⟨pair, hpair, ?_⟩
  rw [hpairValue]
  linarith

/-- The certified interval has nonnegative width at every positive level. -/
theorem escapeAwareQuantileClock_gap_nonneg
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hcompression : HasEscapeAwareQuantileClockCompression reward)
    {level : ℕ} (hlevel : 0 < level) :
    0 ≤ escapeAwareQuantileClockUpper reward hcompression level -
      escapeAwareQuantileClockLower reward hcompression level := by
  obtain ⟨hlower, hupper, -⟩ :=
    escapeAwareQuantileClock_quantitative_bracket reward hcompression hlevel
  linarith

/-- The finite-clock upper certificate converges from above at the same
explicit rate. -/
theorem escapeAwareQuantileClockUpper_sub_exploitabilityInf
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hcompression : HasEscapeAwareQuantileClockCompression reward)
    {level : ℕ} (hlevel : 0 < level) :
    0 ≤ escapeAwareQuantileClockUpper reward hcompression level -
        quittingTerminalExploitabilityInf reward ∧
      escapeAwareQuantileClockUpper reward hcompression level -
          quittingTerminalExploitabilityInf reward ≤
        2 * quantileClockRadius ι level := by
  obtain ⟨hlower, hupper, hgap⟩ :=
    escapeAwareQuantileClock_quantitative_bracket reward hcompression hlevel
  constructor <;> linarith

/-- On the zero-infimum branch, an actual finite-clock product profile attains
the advertised quantitative exploitability upper bound. -/
theorem exists_finiteClockSemanticPair_exploitability_le_of_inf_eq_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hcompression : HasEscapeAwareQuantileClockCompression reward)
    {level : ℕ} (hlevel : 0 < level)
    (hinf : quittingTerminalExploitabilityInf reward = 0) :
    ∃ pair ∈ quittingFiniteClockSemanticReachable reward
        (quantileClockSupport ι level),
      quittingTerminalSemanticExploitability pair ≤
        2 * quantileClockRadius ι level := by
  obtain ⟨pair, hpair, hpairValue⟩ :=
    exists_finiteClockSemanticPair_exploitability_eq_upper
      reward hcompression level
  refine ⟨pair, hpair, ?_⟩
  rw [hpairValue]
  obtain ⟨-, hupper⟩ :=
    escapeAwareQuantileClockUpper_sub_exploitabilityInf
      reward hcompression hlevel
  linarith

/-- The lower certificates converge to the exact executable exploitability
infimum at the quantitative compression rate. -/
theorem tendsto_escapeAwareQuantileClockLower
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hcompression : HasEscapeAwareQuantileClockCompression reward) :
    Tendsto (escapeAwareQuantileClockLower reward hcompression) atTop
      (𝓝 (quittingTerminalExploitabilityInf reward)) := by
  have herror : Tendsto (fun level =>
      quittingTerminalExploitabilityInf reward -
        escapeAwareQuantileClockLower reward hcompression level)
      atTop (𝓝 0) := by
    apply squeeze_zero' (g := fun level => 2 * quantileClockRadius ι level)
    · exact Eventually.of_forall fun level => sub_nonneg.mpr
        (escapeAwareQuantileClockLower_le_exploitabilityInf
          reward hcompression level)
    · filter_upwards [eventually_gt_atTop 0] with level hlevel
      obtain ⟨-, hupper, hgap⟩ :=
        escapeAwareQuantileClock_quantitative_bracket
          reward hcompression hlevel
      linarith
    · simpa only [mul_zero] using
        (quantileClockRadius_tendsto_zero ι).const_mul 2
  have hconstant : Tendsto
      (fun _ : ℕ => quittingTerminalExploitabilityInf reward) atTop
      (𝓝 (quittingTerminalExploitabilityInf reward)) :=
    tendsto_const_nhds
  simpa only [sub_sub_cancel, sub_zero] using hconstant.sub herror

/-- The supremum of all finite lower certificates is the exact executable
exploitability infimum. -/
theorem sSup_range_escapeAwareQuantileClockLower
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hcompression : HasEscapeAwareQuantileClockCompression reward) :
    sSup (Set.range (escapeAwareQuantileClockLower reward hcompression)) =
      quittingTerminalExploitabilityInf reward := by
  have hle : ∀ level, escapeAwareQuantileClockLower reward hcompression level ≤
      quittingTerminalExploitabilityInf reward :=
    escapeAwareQuantileClockLower_le_exploitabilityInf reward hcompression
  have hbdd : BddAbove
      (Set.range (escapeAwareQuantileClockLower reward hcompression)) :=
    ⟨quittingTerminalExploitabilityInf reward, by
      rintro value ⟨level, rfl⟩
      exact hle level⟩
  apply le_antisymm
  · exact csSup_le (Set.range_nonempty _) (by
      rintro value ⟨level, rfl⟩
      exact hle level)
  · apply le_of_tendsto'
      (tendsto_escapeAwareQuantileClockLower reward hcompression)
    intro level
    exact le_csSup hbdd (Set.mem_range_self level)

/-- The support and radius constants specialize literally to the Fin4 packet. -/
theorem quantileClockSupport_fin4 (level : ℕ) :
    quantileClockSupport (Fin 4) level = 8 * level + 1 := by
  simp [quantileClockSupport]

theorem quantileClockRadius_fin4 (level : ℕ) :
    quantileClockRadius (Fin 4) level = 12 / (level : ℝ) := by
  simp [quantileClockRadius]

theorem quantileClockScaledRadius_fin4 (bound : ℝ) (level : ℕ) :
    quantileClockScaledRadius (Fin 4) bound level =
      12 * bound / (level : ℝ) := by
  rw [quantileClockScaledRadius, quantileClockRadius_fin4]
  ring

/-- Fin4 bracket with the advertised `24 / level` gap. -/
theorem escapeAwareQuantileClock_fin4_quantitative_bracket
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hcompression : HasEscapeAwareQuantileClockCompression reward)
    {level : ℕ} (hlevel : 0 < level) :
    escapeAwareQuantileClockLower reward hcompression level ≤
        quittingTerminalExploitabilityInf reward ∧
      quittingTerminalExploitabilityInf reward ≤
        escapeAwareQuantileClockUpper reward hcompression level ∧
      escapeAwareQuantileClockUpper reward hcompression level -
          escapeAwareQuantileClockLower reward hcompression level ≤
        24 / (level : ℝ) := by
  obtain ⟨hlower, hupper, hgap⟩ :=
    escapeAwareQuantileClock_quantitative_bracket reward hcompression hlevel
  refine ⟨hlower, hupper, hgap.trans_eq ?_⟩
  rw [quantileClockRadius_fin4]
  ring

/-- Unconditional normalized Fin4 bracket with support `8 * level + 1`,
semantic radius `12 / level`, and objective gap `24 / level`. -/
theorem escapeAwareQuantileClock_fin4_normalized_quantitative_bracket
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hreward : ∀ terminal player, |reward terminal player| ≤ 1)
    {level : ℕ} (hlevel : 0 < level) :
    escapeAwareQuantileClockLower reward
          (hasEscapeAwareQuantileClockCompression_of_normalized reward hreward)
          level ≤ quittingTerminalExploitabilityInf reward ∧
      quittingTerminalExploitabilityInf reward ≤
        escapeAwareQuantileClockUpper reward
          (hasEscapeAwareQuantileClockCompression_of_normalized reward hreward)
          level ∧
      escapeAwareQuantileClockUpper reward
            (hasEscapeAwareQuantileClockCompression_of_normalized reward hreward)
            level -
          escapeAwareQuantileClockLower reward
            (hasEscapeAwareQuantileClockCompression_of_normalized reward hreward)
            level ≤
        24 / (level : ℝ) :=
  escapeAwareQuantileClock_fin4_quantitative_bracket reward
    (hasEscapeAwareQuantileClockCompression_of_normalized reward hreward)
    hlevel

/-- Fin4 bracket for an arbitrary explicit absolute reward bound. -/
theorem escapeAwareQuantileClock_fin4AtBound_quantitative_bracket
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (bound : ℝ) (hbound : 0 ≤ bound)
    (hcompression : HasEscapeAwareQuantileClockCompressionAtBound
      reward bound)
    {level : ℕ} (hlevel : 0 < level) :
    escapeAwareQuantileClockLowerAtBound reward bound hbound hcompression
          level ≤ quittingTerminalExploitabilityInf reward ∧
      quittingTerminalExploitabilityInf reward ≤
        escapeAwareQuantileClockUpperAtBound reward bound hbound hcompression
          level ∧
      escapeAwareQuantileClockUpperAtBound reward bound hbound hcompression
            level -
          escapeAwareQuantileClockLowerAtBound reward bound hbound hcompression
            level ≤
        24 * bound / (level : ℝ) := by
  obtain ⟨hlower, hupper, hgap⟩ :=
    escapeAwareQuantileClockAtBound_quantitative_bracket
      reward bound hbound hcompression hlevel
  refine ⟨hlower, hupper, hgap.trans_eq ?_⟩
  rw [quantileClockScaledRadius_fin4]
  ring

/-- Every Fin4 reward table has the finite-clock bracket with its canonical
absolute reward bound. -/
theorem escapeAwareQuantileClock_fin4AtRewardBound_quantitative_bracket
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    {level : ℕ} (hlevel : 0 < level) :
    escapeAwareQuantileClockLowerAtBound reward
          (quittingRewardBound reward) (quittingRewardBound_nonneg reward)
          (hasEscapeAwareQuantileClockCompressionAtRewardBound reward)
          level ≤ quittingTerminalExploitabilityInf reward ∧
      quittingTerminalExploitabilityInf reward ≤
        escapeAwareQuantileClockUpperAtBound reward
          (quittingRewardBound reward) (quittingRewardBound_nonneg reward)
          (hasEscapeAwareQuantileClockCompressionAtRewardBound reward)
          level ∧
      escapeAwareQuantileClockUpperAtBound reward
            (quittingRewardBound reward) (quittingRewardBound_nonneg reward)
            (hasEscapeAwareQuantileClockCompressionAtRewardBound reward)
            level -
          escapeAwareQuantileClockLowerAtBound reward
            (quittingRewardBound reward) (quittingRewardBound_nonneg reward)
            (hasEscapeAwareQuantileClockCompressionAtRewardBound reward)
            level ≤
        24 * quittingRewardBound reward / (level : ℝ) :=
  escapeAwareQuantileClock_fin4AtBound_quantitative_bracket reward
    (quittingRewardBound reward) (quittingRewardBound_nonneg reward)
    (hasEscapeAwareQuantileClockCompressionAtRewardBound reward) hlevel

/-- Fin4 zero-infimum branch: an actual finite-clock product profile has the
advertised `24 / level` exploitability bound. -/
theorem exists_fin4_finiteClockSemanticPair_exploitability_le_of_inf_eq_zero
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hcompression : HasEscapeAwareQuantileClockCompression reward)
    {level : ℕ} (hlevel : 0 < level)
    (hinf : quittingTerminalExploitabilityInf reward = 0) :
    ∃ pair ∈ quittingFiniteClockSemanticReachable reward (8 * level + 1),
      quittingTerminalSemanticExploitability pair ≤ 24 / (level : ℝ) := by
  obtain ⟨pair, hpair, hbound⟩ :=
    exists_finiteClockSemanticPair_exploitability_le_of_inf_eq_zero
      reward hcompression hlevel hinf
  rw [quantileClockSupport_fin4] at hpair
  refine ⟨pair, hpair, hbound.trans_eq ?_⟩
  rw [quantileClockRadius_fin4]
  ring

/-- On the normalized Fin4 zero-infimum branch, the finite-clock upper witness
is an actual product stopping-law semantic pair with the advertised rate. -/
theorem exists_fin4_finiteClockSemanticPair_exploitability_le_of_normalized_inf_eq_zero
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hreward : ∀ terminal player, |reward terminal player| ≤ 1)
    {level : ℕ} (hlevel : 0 < level)
    (hinf : quittingTerminalExploitabilityInf reward = 0) :
    ∃ pair ∈ quittingFiniteClockSemanticReachable reward (8 * level + 1),
      quittingTerminalSemanticExploitability pair ≤ 24 / (level : ℝ) :=
  exists_fin4_finiteClockSemanticPair_exploitability_le_of_inf_eq_zero
    reward
    (hasEscapeAwareQuantileClockCompression_of_normalized reward hreward)
    hlevel hinf

end GameTheory
