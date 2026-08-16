/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegime.StoppingLaw.SelfOrientedAtomSequence
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegime.StoppingLaw.ObserverAbsent.ForcedOwnerDispatch
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegime.StoppingLaw.ReachedRowDebtLocalization

/-!
# Generic pure-time consumers for a signed terminal atom

A pure-time carrier with persistent terminal mass feeds three literal
consumers: an observer-absent forced-owner wall, a negative source-row atomic
dispatch, or a positive reached-row localization with vanishing marked debt.
-/

noncomputable section

namespace GameTheory

open Filter Set StochasticGame Math.Probability
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]
/-! ## Generic pure-time observer-absent wall -/

/-- A sequence of profiles obtained by installing one pure-time strategy. -/
def quittingPureTimeCarrierProfile
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (base : ℕ → (quittingGame reward).BehaviorProfile)
    (observer : ι) (quitTime : ℕ → Option ℕ) (n : ℕ) :
    (quittingGame reward).BehaviorProfile :=
  quittingPureTimeUpdatedProfile reward (base n) observer (quitTime n)

/-- One fixed member of a nonempty terminal label. -/
def quittingPureTimeObserverAbsentOwner
    (terminal : {S : Finset ι // S.Nonempty}) : ι :=
  terminal.property.choose

/-- The fixed forced owner belongs to the terminal label. -/
theorem quittingPureTimeObserverAbsentOwner_mem
    (terminal : {S : Finset ι // S.Nonempty}) :
    quittingPureTimeObserverAbsentOwner terminal ∈ terminal.val :=
  terminal.property.choose_spec

/-- Force the fixed terminal owner to Quit at one row of a pure-time carrier.
-/
def quittingPureTimeObserverAbsentForcedOwnerProfile
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (base : ℕ → (quittingGame reward).BehaviorProfile)
    (observer : ι) (quitTime : ℕ → Option ℕ)
    (terminal : {S : Finset ι // S.Nonempty}) (n time : ℕ) :
    (quittingGame reward).BehaviorProfile :=
  let profile := quittingPureTimeCarrierProfile reward base observer quitTime n
  let owner := quittingPureTimeObserverAbsentOwner terminal
  Function.update profile owner
    (quittingStagePureEndpointBehaviorDeviation reward profile owner time true)

/-- The atomic blocker wall at one row of a pure-time carrier. -/
def quittingPureTimeObserverAbsentRowBarrier
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (base : ℕ → (quittingGame reward).BehaviorProfile)
    (observer : ι) (quitTime : ℕ → Option ℕ)
    (terminal : {S : Finset ι // S.Nonempty}) (n time : ℕ) : ℝ :=
  let profile := quittingPureTimeCarrierProfile reward base observer quitTime n
  let owner := quittingPureTimeObserverAbsentOwner terminal
  let root := Function.update (quittingProfileLiveRoot reward profile time)
    owner (PMF.pure true)
  max (quittingForcedOwnerOutsiderDefect reward root owner)
    (max 0 (-quittingAtomicBlockerBalance reward root owner))

/-- Game-facing forced-owner wall for a pure-time observer absent from the
fixed terminal label. -/
def HasQuittingPureTimeObserverAbsentForcedOwnerDispatch
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {regime : QuittingCounterexampleRegime reward}
    (base : ℕ → (quittingGame reward).BehaviorProfile)
    (observer : ι) (quitTime : ℕ → Option ℕ)
    (terminal : {S : Finset ι // S.Nonempty}) (lower : ℝ) : Prop :=
  let owner := quittingPureTimeObserverAbsentOwner terminal
  let profile := quittingPureTimeCarrierProfile reward base observer quitTime
  owner ∈ terminal.val ∧ owner ≠ observer ∧ 0 < lower ∧
    (∀ n, lower ≤
      quittingTerminalOutcomeMass reward (profile n) (some terminal)) ∧
    (∀ n, lower * regime.terminalGap ≤
      quittingTerminalOutcomeMass reward (profile n) (some terminal) *
        regime.terminalGap) ∧
    (∀ n,
      quittingTerminalOutcomeMass reward (profile n) (some terminal) =
        match quitTime n with
        | some stop => ∑ time ∈ Finset.range stop,
            quittingStageCoalitionMass reward (profile n) time terminal
        | none => ∑' time,
            quittingStageCoalitionMass reward (profile n) time terminal) ∧
    ∀ n time,
      (match quitTime n with
        | some stop => time < stop
        | none => True) →
      let actualRoot := quittingProfileLiveRoot reward (profile n) time
      let forcedRoot := Function.update actualRoot owner (PMF.pure true)
      let forcedProfile := quittingPureTimeObserverAbsentForcedOwnerProfile
        reward base observer quitTime terminal n time
      let tail := quittingTerminalSemanticPair reward
        (quittingAllContinueProfileSpine reward (profile n) (time + 1))
      let mass := quittingStageCoalitionMass reward (profile n) time terminal
      actualRoot observer = PMF.pure false ∧
        quittingProfileLiveRoot reward forcedProfile time = forcedRoot ∧
        mass ≤ quittingLiveMass reward (profile n) time *
          quittingRootCoalitionMass forcedRoot terminal.val ∧
        regime.terminalGap ≤
          quittingPureTimeObserverAbsentRowBarrier reward base observer
            quitTime terminal n time ∧
        mass * regime.terminalGap ≤
          mass * quittingPureTimeObserverAbsentRowBarrier reward base observer
            quitTime terminal n time ∧
        ((∃ who, who ≠ owner ∧
            regime.terminalGap ≤
              quittingRootCoordinateNashDefect reward tail.1 forcedRoot who ∧
            mass * regime.terminalGap ≤
              mass * quittingRootCoordinateNashDefect reward tail.1
                forcedRoot who) ∨
          (regime.terminalGap ≤
              max 0 (-quittingAtomicBlockerBalance reward forcedRoot owner) ∧
            mass * regime.terminalGap ≤
              mass * max 0
                (-quittingAtomicBlockerBalance reward forcedRoot owner)))

/-- Exact pre-observer-stop accounting for a pure-time carrier. -/
theorem quittingPureTimeCarrier_mass_eq_clock
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (base : ℕ → (quittingGame reward).BehaviorProfile)
    (observer : ι) (quitTime : ℕ → Option ℕ)
    (terminal : {S : Finset ι // S.Nonempty})
    (habsent : observer ∉ terminal.val) (n : ℕ) :
    quittingTerminalOutcomeMass reward
        (quittingPureTimeCarrierProfile reward base observer quitTime n)
        (some terminal) =
      match quitTime n with
      | some stop => ∑ time ∈ Finset.range stop,
          quittingStageCoalitionMass reward
            (quittingPureTimeCarrierProfile reward base observer quitTime n)
            time terminal
      | none => ∑' time,
          quittingStageCoalitionMass reward
            (quittingPureTimeCarrierProfile reward base observer quitTime n)
            time terminal := by
  cases htime : quitTime n with
  | none =>
      simpa only using quittingTerminalOutcomeMass_eq_timeDisintegration reward
        (quittingPureTimeCarrierProfile reward base observer quitTime n)
        (some terminal)
  | some stop =>
      unfold quittingPureTimeCarrierProfile quittingPureTimeUpdatedProfile
      simpa only [htime] using
        quittingTerminalOutcomeMass_update_pureTime_some_notMem_eq_before
          reward (base n) observer stop terminal habsent

/-- Before its selected stopping date, the observer literally Continues. -/
theorem quittingPureTimeCarrier_root_observer
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (base : ℕ → (quittingGame reward).BehaviorProfile)
    (observer : ι) (quitTime : ℕ → Option ℕ) (n time : ℕ)
    (hbefore : match quitTime n with
      | some stop => time < stop
      | none => True) :
    quittingProfileLiveRoot reward
        (quittingPureTimeCarrierProfile reward base observer quitTime n) time
        observer = PMF.pure false := by
  cases htime : quitTime n with
  | none =>
      unfold quittingPureTimeCarrierProfile quittingPureTimeUpdatedProfile
      rw [quittingProfileLiveRoot_update_pureTime_self, htime,
        quittingPureTimeHazard_none]
  | some stop =>
      have hlt : time < stop := by simpa only [htime] using hbefore
      unfold quittingPureTimeCarrierProfile quittingPureTimeUpdatedProfile
      simpa only [htime] using
        quittingProfileLiveRoot_update_pureTime_some_eq_pureContinue_of_lt
          reward (base n) observer hlt

/-- The forced profile has exactly the advertised product root. -/
theorem quittingProfileLiveRoot_pureTimeObserverAbsentForcedOwnerProfile
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (base : ℕ → (quittingGame reward).BehaviorProfile)
    (observer : ι) (quitTime : ℕ → Option ℕ)
    (terminal : {S : Finset ι // S.Nonempty}) (n time : ℕ) :
    quittingProfileLiveRoot reward
        (quittingPureTimeObserverAbsentForcedOwnerProfile reward base observer
          quitTime terminal n time) time =
      Function.update
        (quittingProfileLiveRoot reward
          (quittingPureTimeCarrierProfile reward base observer quitTime n) time)
        (quittingPureTimeObserverAbsentOwner terminal) (PMF.pure true) := by
  funext player
  unfold quittingPureTimeObserverAbsentForcedOwnerProfile
    quittingProfileLiveRoot
  by_cases hplayer : player = quittingPureTimeObserverAbsentOwner terminal
  · subst player
    simp [quittingStagePureEndpointBehaviorDeviation,
      quittingStageDeviationHazard_self]
  · simp [Function.update_of_ne hplayer]

/-- Forcing a terminal member to Quit cannot decrease the displayed
coalition cylinder. -/
theorem quittingPureTimeCarrier_stageMass_le_forcedOwnerCylinder
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (base : ℕ → (quittingGame reward).BehaviorProfile)
    (observer : ι) (quitTime : ℕ → Option ℕ)
    (terminal : {S : Finset ι // S.Nonempty}) (n time : ℕ) :
    quittingStageCoalitionMass reward
        (quittingPureTimeCarrierProfile reward base observer quitTime n) time
        terminal ≤
      quittingLiveMass reward
          (quittingPureTimeCarrierProfile reward base observer quitTime n) time *
        quittingRootCoalitionMass
          (Function.update
            (quittingProfileLiveRoot reward
              (quittingPureTimeCarrierProfile reward base observer quitTime n)
              time)
            (quittingPureTimeObserverAbsentOwner terminal) (PMF.pure true))
          terminal.val := by
  rw [quittingStageCoalitionMass_eq_liveMass_mul_rootCoalitionMass]
  apply mul_le_mul_of_nonneg_left
  · simpa [quittingPureEndpointRoutedCoalition,
      quittingPureTimeObserverAbsentOwner_mem terminal] using
      quittingRootCoalitionMass_le_pureEndpointRouted
        (quittingProfileLiveRoot reward
          (quittingPureTimeCarrierProfile reward base observer quitTime n) time)
        terminal.val (quittingPureTimeObserverAbsentOwner terminal) true
  · exact quittingLiveMass_nonneg reward
      (quittingPureTimeCarrierProfile reward base observer quitTime n) time

/-- A persistent observer-absent terminal mass produces the generic
pure-time forced-owner wall. -/
theorem pureTimeObserverAbsent_forcedOwnerDispatch
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {regime : QuittingCounterexampleRegime reward}
    (base : ℕ → (quittingGame reward).BehaviorProfile)
    (observer : ι) (quitTime : ℕ → Option ℕ)
    (terminal : {S : Finset ι // S.Nonempty}) (lower : ℝ)
    (habsent : observer ∉ terminal.val) (hlower : 0 < lower)
    (hmassLower : ∀ n, lower ≤
      quittingTerminalOutcomeMass reward
        (quittingPureTimeCarrierProfile reward base observer quitTime n)
        (some terminal)) :
    HasQuittingPureTimeObserverAbsentForcedOwnerDispatch
      (regime := regime) base observer quitTime terminal lower := by
  classical
  let owner := quittingPureTimeObserverAbsentOwner terminal
  let profile := quittingPureTimeCarrierProfile reward base observer quitTime
  have hownerMem : owner ∈ terminal.val :=
    quittingPureTimeObserverAbsentOwner_mem terminal
  have hownerNe : owner ≠ observer := by
    intro heq
    exact habsent (heq ▸ hownerMem)
  have hmassWeighted : ∀ n,
      lower * regime.terminalGap ≤
        quittingTerminalOutcomeMass reward (profile n) (some terminal) *
          regime.terminalGap := by
    intro n
    exact mul_le_mul_of_nonneg_right (hmassLower n)
      regime.terminalGap_pos.le
  refine ⟨hownerMem, hownerNe, hlower, ?_, hmassWeighted, ?_, ?_⟩
  · intro n
    simpa only [profile] using hmassLower n
  · intro n
    simpa only [profile] using
      quittingPureTimeCarrier_mass_eq_clock reward base observer quitTime
        terminal habsent n
  · intro n time hbefore
    let actualRoot := quittingProfileLiveRoot reward (profile n) time
    let forcedRoot := Function.update actualRoot owner (PMF.pure true)
    let forcedProfile := quittingPureTimeObserverAbsentForcedOwnerProfile
      reward base observer quitTime terminal n time
    let tail := quittingTerminalSemanticPair reward
      (quittingAllContinueProfileSpine reward (profile n) (time + 1))
    let mass := quittingStageCoalitionMass reward (profile n) time terminal
    have hobserver : actualRoot observer = PMF.pure false := by
      simpa only [actualRoot, profile] using
        quittingPureTimeCarrier_root_observer reward base observer quitTime
          n time hbefore
    have hforcedProfile : quittingProfileLiveRoot reward forcedProfile time =
        forcedRoot := by
      simpa only [forcedProfile, forcedRoot, actualRoot, profile] using
        quittingProfileLiveRoot_pureTimeObserverAbsentForcedOwnerProfile
          reward base observer quitTime terminal n time
    have hmass : mass ≤ quittingLiveMass reward (profile n) time *
        quittingRootCoalitionMass forcedRoot terminal.val := by
      simpa only [mass, forcedRoot, actualRoot, profile] using
        quittingPureTimeCarrier_stageMass_le_forcedOwnerCylinder
          reward base observer quitTime terminal n time
    have hownerForced : forcedRoot owner = PMF.pure true := by
      simp [forcedRoot]
    have hbarrier : regime.terminalGap ≤
        quittingPureTimeObserverAbsentRowBarrier reward base observer
          quitTime terminal n time := by
      simpa only [quittingPureTimeObserverAbsentRowBarrier, forcedRoot,
        actualRoot, owner, profile] using
        regime.terminalGap_le_atomicBlockerBarrier hownerForced
    have hmassNonneg : 0 ≤ mass :=
      quittingStageCoalitionMass_nonneg reward (profile n) time terminal
    have hweightedBarrier : mass * regime.terminalGap ≤
        mass * quittingPureTimeObserverAbsentRowBarrier reward base observer
          quitTime terminal n time :=
      mul_le_mul_of_nonneg_left hbarrier hmassNonneg
    have halternative :
        (∃ who, who ≠ owner ∧
            regime.terminalGap ≤
              quittingRootCoordinateNashDefect reward tail.1 forcedRoot who ∧
            mass * regime.terminalGap ≤
              mass * quittingRootCoordinateNashDefect reward tail.1
                forcedRoot who) ∨
          (regime.terminalGap ≤
              max 0 (-quittingAtomicBlockerBalance reward forcedRoot owner) ∧
            mass * regime.terminalGap ≤
              mass * max 0
                (-quittingAtomicBlockerBalance reward forcedRoot owner)) := by
      have hraw : regime.terminalGap ≤
          max (quittingForcedOwnerOutsiderDefect reward forcedRoot owner)
            (max 0 (-quittingAtomicBlockerBalance reward forcedRoot owner)) := by
        simpa only [quittingPureTimeObserverAbsentRowBarrier, forcedRoot,
          actualRoot, owner, profile] using hbarrier
      rcases (le_max_iff.mp hraw) with hdefect | hrefusal
      · left
        obtain ⟨who, hwho, hcoordinate⟩ :=
          exists_outsider_coordinateNashDefect_ge_of_forcedOwnerDefect_ge
            reward tail.1 forcedRoot owner hownerForced regime.terminalGap_pos
              hdefect
        exact ⟨who, hwho, hcoordinate,
          mul_le_mul_of_nonneg_left hcoordinate hmassNonneg⟩
      · exact Or.inr ⟨hrefusal,
          mul_le_mul_of_nonneg_left hrefusal hmassNonneg⟩
    exact ⟨hobserver, hforcedProfile, hmass, hbarrier, hweightedBarrier,
      halternative⟩

/-! ## Generic pure-time negative source-row dispatch -/

/-- Actual-source atomic dispatch for a pure-time owner contained in the
fixed terminal label. -/
def HasQuittingPureTimeNegativeTargetAtomicDispatch
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {regime : QuittingCounterexampleRegime reward}
    (base : ℕ → (quittingGame reward).BehaviorProfile)
    (owner : ι) (quitTime : ℕ → Option ℕ)
    (terminal : {S : Finset ι // S.Nonempty}) (lower : ℝ) : Prop :=
  ∃ stop : ℕ → ℕ,
    (∀ n, quitTime n = some (stop n)) ∧
    ∀ n,
      let profile := quittingPureTimeCarrierProfile reward base owner quitTime n
      let root := quittingProfileLiveRoot reward profile (stop n)
      let tail := quittingTerminalSemanticPair reward
        (quittingAllContinueProfileSpine reward profile (stop n + 1))
      lower ≤ quittingStageCoalitionMass reward profile (stop n) terminal ∧
        root owner = PMF.pure true ∧
        ((∃ who, who ≠ owner ∧
            regime.terminalGap ≤
              quittingRootCoordinateNashDefect reward tail.1 root who ∧
            lower * regime.terminalGap ≤
              quittingStageCoalitionMass reward profile (stop n) terminal *
                quittingRootCoordinateNashDefect reward tail.1 root who) ∨
          (regime.terminalGap ≤
              max 0 (-quittingAtomicBlockerBalance reward root owner) ∧
            lower * regime.terminalGap ≤
              quittingStageCoalitionMass reward profile (stop n) terminal *
                max 0 (-quittingAtomicBlockerBalance reward root owner)))

/-- Persistent mass on a pure-time source containing its owner reaches one
literal sure-Quit row and the atomic blocker alternative there. -/
theorem pureTimeNegativeTarget_atomicDispatch
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {regime : QuittingCounterexampleRegime reward}
    (base : ℕ → (quittingGame reward).BehaviorProfile)
    (owner : ι) (quitTime : ℕ → Option ℕ)
    (terminal : {S : Finset ι // S.Nonempty}) (lower : ℝ)
    (howner : owner ∈ terminal.val) (hlower : 0 < lower)
    (hmassLower : ∀ n, lower ≤
      quittingTerminalOutcomeMass reward
        (quittingPureTimeCarrierProfile reward base owner quitTime n)
        (some terminal)) :
    HasQuittingPureTimeNegativeTargetAtomicDispatch
      (regime := regime) base owner quitTime terminal lower := by
  classical
  have hfinite : ∀ n, ∃ stop, quitTime n = some stop := by
    intro n
    cases htime : quitTime n with
    | none =>
        have hzero :=
          quittingTerminalOutcomeMass_update_pureTime_none_mem_eq_zero
            reward (base n) owner terminal howner
        have hlowerN := hmassLower n
        unfold quittingPureTimeCarrierProfile quittingPureTimeUpdatedProfile
          at hlowerN
        rw [htime, hzero] at hlowerN
        exact False.elim ((not_lt_of_ge hlowerN) hlower)
    | some stop => exact ⟨stop, rfl⟩
  choose stop hstop using hfinite
  have hstage : ∀ n, lower ≤
      quittingStageCoalitionMass reward
        (quittingPureTimeCarrierProfile reward base owner quitTime n)
        (stop n) terminal := by
    intro n
    have hlowerN := hmassLower n
    unfold quittingPureTimeCarrierProfile quittingPureTimeUpdatedProfile
      at hlowerN ⊢
    rw [hstop n,
      quittingTerminalOutcomeMass_update_pureTime_some_mem_eq_at
        reward (base n) owner (stop n) terminal howner] at hlowerN
    simpa only [hstop n] using hlowerN
  refine ⟨stop, hstop, ?_⟩
  intro n
  let profile := quittingPureTimeCarrierProfile reward base owner quitTime n
  let root := quittingProfileLiveRoot reward profile (stop n)
  let tail := quittingTerminalSemanticPair reward
    (quittingAllContinueProfileSpine reward profile (stop n + 1))
  have hownerSure : root owner = PMF.pure true := by
    dsimp only [root, profile, quittingPureTimeCarrierProfile,
      quittingPureTimeUpdatedProfile]
    rw [quittingProfileLiveRoot_update_pureTime_self, hstop n,
      quittingPureTimeHazard_some_self]
  have hbarrier := regime.terminalGap_le_atomicBlockerBarrier hownerSure
  have hstageN : lower ≤
      quittingStageCoalitionMass reward profile (stop n) terminal := by
    simpa only [profile] using hstage n
  refine ⟨hstageN, hownerSure, ?_⟩
  by_cases hdefect : regime.terminalGap ≤
      quittingForcedOwnerOutsiderDefect reward root owner
  · left
    obtain ⟨who, hwho, hcoordinate⟩ :=
      exists_outsider_coordinateNashDefect_ge_of_forcedOwnerDefect_ge
        reward tail.1 root owner hownerSure regime.terminalGap_pos hdefect
    refine ⟨who, hwho, hcoordinate, ?_⟩
    exact mul_le_mul hstageN hcoordinate regime.terminalGap_pos.le
      (quittingStageCoalitionMass_nonneg reward profile (stop n) terminal)
  · right
    have hrefusal : regime.terminalGap ≤
        max 0 (-quittingAtomicBlockerBalance reward root owner) := by
      have hdefectLt :
          quittingForcedOwnerOutsiderDefect reward root owner <
            regime.terminalGap := lt_of_not_ge hdefect
      by_contra hnot
      have hrefusalLt :
          max 0 (-quittingAtomicBlockerBalance reward root owner) <
            regime.terminalGap := lt_of_not_ge hnot
      exact (not_lt_of_ge hbarrier) (max_lt hdefectLt hrefusalLt)
    refine ⟨hrefusal, ?_⟩
    exact mul_le_mul hstageN hrefusal regime.terminalGap_pos.le
      (quittingStageCoalitionMass_nonneg reward profile (stop n) terminal)

/-! ## Generic pure-time positive reached-row localization -/

/-- Canonical legal best-endpoint gain at a selected pure-time target row. -/
def quittingPureTimePositiveTargetReachedRowGain
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (base : ℕ → (quittingGame reward).BehaviorProfile)
    (owner : ι) (quitTime : ℕ → Option ℕ)
    (stop : ℕ → ℕ) (other : ι) (rank : ℕ) : ℝ :=
  let profile := quittingPureTimeCarrierProfile reward base owner quitTime rank
  let stage := stop rank
  let tail := quittingTerminalSemanticPair reward
    (quittingAllContinueProfileSpine reward profile (stage + 1))
  let root := quittingProfileLiveRoot reward profile stage
  let action := quittingRootBestEndpointAction reward tail.1 root other
  let deviation := quittingStagePureEndpointBehaviorDeviation
    reward profile other stage action
  quittingTerminalPayoff reward
        (Function.update profile other deviation) other -
      quittingTerminalPayoff reward profile other

/-- Explicit positive gain floor at a uniformly reached pure-time row. -/
def quittingPureTimePositiveTargetReachedRowGainFloor
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {regime : QuittingCounterexampleRegime reward}
    (frontier : QuittingCounterexampleStoppingLawFrontier regime)
    (owner : ι) (lower : ℝ) : ℝ :=
  lower * quittingTerminalSemanticDebtSum frontier.base /
    (2 * ((Finset.univ.erase owner).card : ℝ))

/-- Quantitative positive-target localization for a generic pure-time carrier.
-/
def HasQuittingPureTimePositiveTargetReachedRowLocalization
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {regime : QuittingCounterexampleRegime reward}
    (frontier : QuittingCounterexampleStoppingLawFrontier regime)
    (base : ℕ → (quittingGame reward).BehaviorProfile)
    (owner : ι) (quitTime : ℕ → Option ℕ)
    (terminal : {S : Finset ι // S.Nonempty}) (lower : ℝ) : Prop :=
  0 < lower ∧
    ∃ (stop : ℕ → ℕ) (subseq : ℕ → ℕ) (other : ι),
      StrictMono subseq ∧ other ≠ owner ∧
      (∀ rank, quitTime (subseq rank) = some (stop (subseq rank))) ∧
      (∀ rank, lower ≤ quittingStageCoalitionMass reward
        (quittingPureTimeCarrierProfile reward base owner quitTime
          (subseq rank)) (stop (subseq rank)) terminal) ∧
      ∀ rank,
        quittingPureTimePositiveTargetReachedRowGainFloor frontier owner lower ≤
          quittingPureTimePositiveTargetReachedRowGain reward base owner
            quitTime stop other (subseq rank)

/-- Eventual finite target times and persistent stage mass produce the generic
positive reached-row localization. -/
theorem pureTimePositiveTargetReachedRowLocalization_of_eventually_stop_mass
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {regime : QuittingCounterexampleRegime reward}
    (frontier : QuittingCounterexampleStoppingLawFrontier regime)
    (base : ℕ → (quittingGame reward).BehaviorProfile)
    (owner : ι) (quitTime : ℕ → Option ℕ)
    (terminal : {S : Finset ι // S.Nonempty})
    {lower : ℝ} (hlower : 0 < lower) (stop baseSubseq : ℕ → ℕ)
    (hbaseSubseq : StrictMono baseSubseq)
    (hfinite : ∀ᶠ rank in atTop,
      quitTime (baseSubseq rank) = some (stop (baseSubseq rank)))
    (hmass : ∀ᶠ rank in atTop, lower ≤
      quittingStageCoalitionMass reward
        (quittingPureTimeCarrierProfile reward base owner quitTime
          (baseSubseq rank)) (stop (baseSubseq rank)) terminal)
    (hdebt : Tendsto (fun rank =>
      quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (quittingPureTimeCarrierProfile reward base owner quitTime rank))
        owner) atTop (nhds 0)) :
    HasQuittingPureTimePositiveTargetReachedRowLocalization
      frontier base owner quitTime terminal lower := by
  unfold HasQuittingPureTimePositiveTargetReachedRowLocalization
  have hready := hfinite.and hmass
  obtain ⟨start, hstart⟩ := eventually_atTop.1 hready
  let shifted : ℕ → ℕ := fun n => start + n
  have hshifted : StrictMono shifted := fun _ _ hlt =>
    Nat.add_lt_add_left hlt start
  let subseq : ℕ → ℕ := fun n => baseSubseq (shifted n)
  have hsubseq : StrictMono subseq := hbaseSubseq.comp hshifted
  let profile : ℕ → (quittingGame reward).BehaviorProfile := fun n =>
    quittingPureTimeCarrierProfile reward base owner quitTime (subseq n)
  let stage : ℕ → ℕ := fun n => stop (subseq n)
  have htime : ∀ n, quitTime (subseq n) = some (stage n) := by
    intro n
    exact (hstart (shifted n) (Nat.le_add_right start n)).1
  have hstageMass : ∀ n, lower ≤
      quittingStageCoalitionMass reward (profile n) (stage n) terminal := by
    intro n
    exact (hstart (shifted n) (Nat.le_add_right start n)).2
  have hsure : ∀ n,
      quittingProfileLiveRoot reward (profile n) (stage n) owner =
        PMF.pure true := by
    intro n
    dsimp only [profile, quittingPureTimeCarrierProfile,
      quittingPureTimeUpdatedProfile]
    rw [quittingProfileLiveRoot_update_pureTime_self, htime n,
      quittingPureTimeHazard_some_self]
  have hdebtSubseq : Tendsto (fun n =>
      quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward (profile n)) owner)
      atTop (nhds 0) := by
    have hcomp := hdebt.comp hsubseq.tendsto_atTop
    simpa only [profile, subseq, Function.comp_def] using hcomp
  have hminimum : ∀ n, quittingTerminalSemanticDebtSum frontier.base ≤
      quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward
          (quittingAllContinueProfileSpine reward (profile n) (stage n))) := by
    intro n
    exact frontier.base_minimum _
      (quittingTerminalSemanticPair_mem_carrier reward _)
  have hreach : ∀ n, lower ≤
      quittingLiveMass reward (profile n) (stage n) := by
    intro n
    exact (hstageMass n).trans
      (quittingStageCoalitionMass_le_liveMass reward (profile n) (stage n)
        terminal)
  obtain ⟨other, gainSubseq, hother, hgainSubseq, hgain⟩ :=
    exists_fixed_other_reachedRowGain_subsequence reward
      (quittingTerminalSemanticDebtSum frontier.base) frontier.base_positive
      profile stage owner lower hminimum hlower hreach hsure hdebtSubseq
  let finalSubseq : ℕ → ℕ := fun n => subseq (gainSubseq n)
  have hfinalSubseq : StrictMono finalSubseq :=
    hsubseq.comp hgainSubseq
  refine ⟨hlower, stop, finalSubseq, other, hfinalSubseq, hother, ?_, ?_, ?_⟩
  · intro rank
    simpa only [finalSubseq, stage] using htime (gainSubseq rank)
  · intro rank
    simpa only [finalSubseq, profile, stage] using
      hstageMass (gainSubseq rank)
  · intro rank
    simpa only [quittingPureTimePositiveTargetReachedRowGainFloor,
      quittingPureTimePositiveTargetReachedRowGain, finalSubseq, profile,
      stage] using hgain rank


end GameTheory
