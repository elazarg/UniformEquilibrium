/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Research.Semantics.SurvivalWeightedReachedHistoryAccount
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeNegativeCollisionAtomicDispatch
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPlateauLocalizedOtherDefect
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticResetReprojectionWindow

/-!
# Thin quitting adapters for reached-history localization

The game-free account in `Research.Semantics.SurvivalWeightedReachedHistoryAccount`
does not identify a defect with a legal game deviation.  This file checks the
two actual-row interfaces proposed in an earlier design note against the
current negative- and positive-collision predicates.

* The negative-collision outsider arm is already globally executable: the
  existing better-endpoint deviation has exact gain `live mass * defect`.
  The adapter below retains the literal source profile, stop, coalition mass,
  sure-quitting observer, outsider, and deviation.
* At a positive marked row, a sure-quitting observer kills continuation for
  every other player.  Their current-suffix semantic debts are therefore
  exactly their actual coordinate defects.  Global minimality and the
  observer's survival-weighted debt bound sharpen the other-player sum to
  `minimum debt - initial observer debt / lower`, with no minimum-tail/escape
  case split.

The observer-refusal half of the negative leaf is deliberately not converted
to a deviation here: the leaf supplies a positive atomic blocker balance, not
a positive expected refusal gain.  The cancellation claim in Collapse1 needs
extra signed-distribution hypotheses absent from the current leaf.
-/

noncomputable section

namespace GameTheory

open Filter StochasticGame Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## Forced-owner debt identity -/

/-- If `owner` quits surely, every other player has zero opponent Continue
mass. -/
theorem quittingRootOpponentContinueMass_eq_zero_of_other_pureQuit
    (root : ι → PMF Bool) {owner other : ι}
    (hne : other ≠ owner) (howner : root owner = PMF.pure true) :
    quittingRootOpponentContinueMass root other = 0 := by
  let forced := Function.update root other (PMF.pure false)
  have hsure : QuittingRootHasSureQuitter forced := by
    refine ⟨owner, ?_⟩
    dsimp only [forced]
    rw [Function.update_of_ne (Ne.symm hne), howner]
  have hzero :=
    (quittingRootHasSureQuitter_iff_allContinue_mass_zero forced).mp hsure
  unfold quittingRootOpponentContinueMass quittingStationaryContinueMass
  rw [show quittingAllContinueAction = (fun _ : ι => false) by rfl, hzero]
  norm_num

/-- On a row with a distinct sure quitter, another player's current-suffix
semantic debt is exactly its actual one-row coordinate defect. -/
theorem terminalSemanticDebt_prefix_eq_coordinateNashDefect_of_other_pureQuit
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : QuittingTerminalSemanticPair ι) (root : ι → PMF Bool)
    {owner other : ι} (hne : other ≠ owner)
    (howner : root owner = PMF.pure true)
    (htailDebt : 0 ≤ quittingTerminalSemanticDebt tail other) :
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPrefix reward root tail) other =
      quittingRootCoordinateNashDefect reward tail.1 root other := by
  have hlower := quittingRootCoordinateNashDefect_le_terminalSemanticDebt_prefix
    reward tail root other htailDebt
  have hupper := quittingTerminalSemanticDebt_prefix_le_nashDefect_add_transport
    reward tail root other htailDebt
  rw [quittingRootOpponentContinueMass_eq_zero_of_other_pureQuit
    root hne howner, zero_mul, add_zero] at hupper
  exact le_antisymm hupper hlower

/-! ## Common surely-absorbing reached-row localization -/

/-- Pointwise marked-row sharpening.  At an actual row reached with event
mass at least `lower`, a distinct sure quitter makes all other current-suffix
debts equal their row defects.  Global minimality then puts all but the
observer's survival-affordable debt on those defects. -/
theorem sureQuitterReachedRow_minimumDebt_localization_of_reach
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (minimum : QuittingTerminalSemanticPair ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (observer : ι) (stage : ℕ) {lower M : ℝ}
    (hlower : 0 < lower) (hM : 0 ≤ M)
    (hreward : ∀ outcome player, |reward outcome player| ≤ M)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (hreach : lower ≤ quittingLiveMass reward profile stage)
    (hobserver : quittingProfileLiveRoot reward profile stage observer =
      PMF.pure true) :
    quittingTerminalSemanticDebtSum minimum -
        quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward profile) observer / lower ≤
      ∑ other ∈ Finset.univ.erase observer,
        quittingRootCoordinateNashDefect reward
          (quittingTerminalSemanticPair reward
            (quittingAllContinueProfileSpine reward profile (stage + 1))).1
          (quittingProfileLiveRoot reward profile stage) other := by
  let current := quittingTerminalSemanticPair reward
    (quittingAllContinueProfileSpine reward profile stage)
  let tail := quittingTerminalSemanticPair reward
    (quittingAllContinueProfileSpine reward profile (stage + 1))
  let root := quittingProfileLiveRoot reward profile stage
  have hcurrentCarrier : current ∈ quittingTerminalSemanticCarrier reward :=
    quittingTerminalSemanticPair_mem_carrier reward _
  have htailCarrier : tail ∈ quittingTerminalSemanticCarrier reward :=
    quittingTerminalSemanticPair_mem_carrier reward _
  have hcurrentNonneg : ∀ who, 0 ≤ quittingTerminalSemanticDebt current who :=
    quittingTerminalSemanticDebt_nonneg_of_mem_carrier
      reward hM hreward hcurrentCarrier
  have htailNonneg : ∀ who, 0 ≤ quittingTerminalSemanticDebt tail who :=
    quittingTerminalSemanticDebt_nonneg_of_mem_carrier
      reward hM hreward htailCarrier
  have hprefix : current = quittingTerminalSemanticPrefix reward root tail := by
    dsimp only [current, root, tail]
    exact quittingTerminalSemanticPair_spine_eq_prefix
      reward profile stage hM hreward
  have hotherEq : ∀ other ∈ Finset.univ.erase observer,
      quittingTerminalSemanticDebt current other =
        quittingRootCoordinateNashDefect reward tail.1 root other := by
    intro other hother
    rw [hprefix]
    exact terminalSemanticDebt_prefix_eq_coordinateNashDefect_of_other_pureQuit
      reward tail root (Finset.mem_erase.mp hother).1
        (by simpa only [root] using hobserver) (htailNonneg other)
  have hsumCurrent : quittingTerminalSemanticDebtSum current =
      quittingTerminalSemanticDebt current observer +
        ∑ other ∈ Finset.univ.erase observer,
          quittingRootCoordinateNashDefect reward tail.1 root other := by
    unfold quittingTerminalSemanticDebtSum
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ observer)]
    rw [add_comm]
    congr 1
    apply Finset.sum_congr rfl
    exact hotherEq
  have hminimumCurrent : quittingTerminalSemanticDebtSum minimum ≤
      quittingTerminalSemanticDebtSum current :=
    hminimum current hcurrentCarrier
  have hobserverWeighted : quittingLiveMass reward profile stage *
      quittingTerminalSemanticDebt current observer ≤
        quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward profile) observer := by
    simpa only [current] using
      (quittingLiveMass_mul_spineDebt_le_initialDebt
        (reward := reward) profile observer hM hreward stage)
  have hlowerWeighted : lower *
      quittingTerminalSemanticDebt current observer ≤
        quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward profile) observer := by
    exact (mul_le_mul_of_nonneg_right hreach
      (hcurrentNonneg observer)).trans hobserverWeighted
  have hobserverDiv : quittingTerminalSemanticDebt current observer ≤
      quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward profile) observer / lower := by
    exact (le_div_iff₀ hlower).2 (by simpa [mul_comm] using hlowerWeighted)
  rw [hsumCurrent] at hminimumCurrent
  have hresult : quittingTerminalSemanticDebtSum minimum -
        quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward profile) observer / lower ≤
      ∑ other ∈ Finset.univ.erase observer,
        quittingRootCoordinateNashDefect reward tail.1 root other := by
    linarith
  simpa only [tail, root] using hresult

/-- A named coalition is one way to certify reach of the surely absorbing
row.  It plays no further role in the debt localization. -/
theorem sureQuitterReachedRow_minimumDebt_localization
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (minimum : QuittingTerminalSemanticPair ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (observer : ι) (stage : ℕ)
    (terminal : {S : Finset ι // S.Nonempty}) {lower M : ℝ}
    (hlower : 0 < lower) (hM : 0 ≤ M)
    (hreward : ∀ outcome player, |reward outcome player| ≤ M)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (hmass : lower ≤
      quittingStageCoalitionMass reward profile stage terminal)
    (hobserver : quittingProfileLiveRoot reward profile stage observer =
      PMF.pure true) :
    quittingTerminalSemanticDebtSum minimum -
        quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward profile) observer / lower ≤
      ∑ other ∈ Finset.univ.erase observer,
        quittingRootCoordinateNashDefect reward
          (quittingTerminalSemanticPair reward
            (quittingAllContinueProfileSpine reward profile (stage + 1))).1
          (quittingProfileLiveRoot reward profile stage) other := by
  apply sureQuitterReachedRow_minimumDebt_localization_of_reach
    reward minimum profile observer stage hlower hM hreward hminimum
  · exact hmass.trans (quittingStageCoalitionMass_le_liveMass
      reward profile stage terminal)
  · exact hobserver

/-- If the displayed root has zero joint Continue mass, some sure quitter
can be selected and used in the reached-row localization.  The conclusion is
existential because zero joint survival does not identify a prescribed
observer. -/
theorem surelyAbsorbingReachedRow_minimumDebt_localization
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (minimum : QuittingTerminalSemanticPair ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (stage : ℕ) {lower M : ℝ}
    (hlower : 0 < lower) (hM : 0 ≤ M)
    (hreward : ∀ outcome player, |reward outcome player| ≤ M)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (hreach : lower ≤ quittingLiveMass reward profile stage)
    (habsorbing : quittingStationaryContinueMass
      (quittingProfileLiveRoot reward profile stage) = 0) :
    ∃ observer,
      quittingProfileLiveRoot reward profile stage observer = PMF.pure true ∧
      quittingTerminalSemanticDebtSum minimum -
          quittingTerminalSemanticDebt
            (quittingTerminalSemanticPair reward profile) observer / lower ≤
        ∑ other ∈ Finset.univ.erase observer,
          quittingRootCoordinateNashDefect reward
            (quittingTerminalSemanticPair reward
              (quittingAllContinueProfileSpine reward profile
                (stage + 1))).1
            (quittingProfileLiveRoot reward profile stage) other := by
  let root := quittingProfileLiveRoot reward profile stage
  have hzero : (pmfPi root) (fun _ : ι => false) = 0 := by
    have hzeroOrTop :=
      (ENNReal.toReal_eq_zero_iff ((pmfPi root) (fun _ : ι => false))).mp
        (by simpa [root, quittingStationaryContinueMass,
          quittingAllContinueAction] using habsorbing)
    exact hzeroOrTop.resolve_right (PMF.apply_ne_top _ _)
  obtain ⟨observer, hobserver⟩ :=
    (quittingRootHasSureQuitter_iff_allContinue_mass_zero root).mpr hzero
  refine ⟨observer, by simpa only [root] using hobserver, ?_⟩
  exact sureQuitterReachedRow_minimumDebt_localization_of_reach
    reward minimum profile observer stage hlower hM hreward hminimum hreach
      (by simpa only [root] using hobserver)

/-- **Common reached surely-absorbing row.**  Reach and zero joint Continue
mass alone select a sure quitter and put the minimum-debt localization and
every nonquitter's legal endpoint deviation on the same literal row and tail.
A named terminal coalition is not part of this statement. -/
theorem surelyAbsorbingReachedRow_localization_and_legalDeviations
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (minimum : QuittingTerminalSemanticPair ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (stage : ℕ) {lower M : ℝ}
    (hlower : 0 < lower) (hM : 0 ≤ M)
    (hreward : ∀ outcome player, |reward outcome player| ≤ M)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (hreach : lower ≤ quittingLiveMass reward profile stage)
    (habsorbing : quittingStationaryContinueMass
      (quittingProfileLiveRoot reward profile stage) = 0) :
    ∃ observer,
      quittingProfileLiveRoot reward profile stage observer = PMF.pure true ∧
      let tail := quittingTerminalSemanticPair reward
        (quittingAllContinueProfileSpine reward profile (stage + 1))
      let root := quittingProfileLiveRoot reward profile stage
      quittingTerminalSemanticDebtSum minimum -
            quittingTerminalSemanticDebt
              (quittingTerminalSemanticPair reward profile) observer / lower ≤
          ∑ other ∈ Finset.univ.erase observer,
            quittingRootCoordinateNashDefect reward tail.1 root other ∧
        ∀ other, other ≠ observer →
          let action :=
            quittingRootBestEndpointAction reward tail.1 root other
          let deviation := quittingStagePureEndpointBehaviorDeviation
            reward profile other stage action
          quittingTerminalPayoff reward
                (Function.update profile other deviation) other -
              quittingTerminalPayoff reward profile other =
            quittingLiveMass reward profile stage *
              quittingRootCoordinateNashDefect reward tail.1 root other := by
  obtain ⟨observer, hobserver, hlocal⟩ :=
    surelyAbsorbingReachedRow_minimumDebt_localization reward minimum profile
      stage hlower hM hreward hminimum hreach habsorbing
  refine ⟨observer, hobserver, ?_⟩
  dsimp only
  refine ⟨hlocal, ?_⟩
  intro other _hne
  exact
    quittingTerminalPayoff_stageBestEndpointDeviation_sub_eq_liveMass_mul_defect
      reward profile other stage

/-- **Common surely-absorbing reached-row packet.**  The minimum-debt
localization and the legal-deviation interpretation of every nonowner defect
hold on the same literal profile, row, event, root, and tail. -/
theorem sureQuitterReachedRow_localization_and_legalDeviations
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (minimum : QuittingTerminalSemanticPair ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (observer : ι) (stage : ℕ)
    (terminal : {S : Finset ι // S.Nonempty}) {lower M : ℝ}
    (hlower : 0 < lower) (hM : 0 ≤ M)
    (hreward : ∀ outcome player, |reward outcome player| ≤ M)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (hmass : lower ≤
      quittingStageCoalitionMass reward profile stage terminal)
    (hobserver : quittingProfileLiveRoot reward profile stage observer =
      PMF.pure true) :
    let tail := quittingTerminalSemanticPair reward
      (quittingAllContinueProfileSpine reward profile (stage + 1))
    let root := quittingProfileLiveRoot reward profile stage
    quittingTerminalSemanticDebtSum minimum -
          quittingTerminalSemanticDebt
            (quittingTerminalSemanticPair reward profile) observer / lower ≤
        ∑ other ∈ Finset.univ.erase observer,
          quittingRootCoordinateNashDefect reward tail.1 root other ∧
      ∀ other, other ≠ observer →
        let action :=
          quittingRootBestEndpointAction reward tail.1 root other
        let deviation := quittingStagePureEndpointBehaviorDeviation
          reward profile other stage action
        quittingTerminalPayoff reward
              (Function.update profile other deviation) other -
            quittingTerminalPayoff reward profile other =
          quittingLiveMass reward profile stage *
            quittingRootCoordinateNashDefect reward tail.1 root other := by
  dsimp only
  refine ⟨sureQuitterReachedRow_minimumDebt_localization reward minimum
    profile observer stage terminal hlower hM hreward hminimum hmass
      hobserver, ?_⟩
  intro other _hne
  exact
    quittingTerminalPayoff_stageBestEndpointDeviation_sub_eq_liveMass_mul_defect
      reward profile other stage

/-! ## L4 actual-source outsider adapter -/

/-- The outsider-defect half of the current negative-collision leaf is one
legal behavioral deviation on its literal source profile.  The common
sure-quitter localization also identifies the exact obstruction to the L5
average-defect argument: the source observer's initial debt occurs divided by
the reached-mass lower bound and is not known to vanish.  The refusal half is
returned unchanged because the leaf does not imply a collectible expected
refusal. -/
theorem negativeCollisionAtomicDispatch_outsider_isLegalDeviation
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {regime : QuittingCounterexampleRegime reward}
    {frontier : QuittingCounterexampleStoppingLawFrontier regime}
    (packet : QuittingStoppingLawVanishingDebtRectangleSequence frontier)
    {lower : ℝ}
    (hlower : 0 < lower)
    (dispatch : HasQuittingStoppingLawNegativeCollisionAtomicDispatch
      packet lower) (n : ℕ) :
    ∃ stop : ℕ,
      packet.quitTime n = some stop ∧
      let profile := quittingStoppingLawRectangleSourceProfile packet n
      let root := quittingProfileLiveRoot reward profile stop
      let tail := quittingTerminalSemanticPair reward
        (quittingAllContinueProfileSpine reward profile (stop + 1))
      lower ≤ quittingStageCoalitionMass reward profile stop packet.terminal ∧
      root packet.observer = PMF.pure true ∧
      quittingTerminalSemanticDebtSum frontier.base -
          quittingTerminalSemanticDebt
            (quittingTerminalSemanticPair reward profile) packet.observer /
            lower ≤
        ∑ other ∈ Finset.univ.erase packet.observer,
          quittingRootCoordinateNashDefect reward tail.1 root other ∧
      ((∃ who, who ≠ packet.observer ∧
          regime.terminalGap ≤
            quittingRootCoordinateNashDefect reward tail.1 root who ∧
          let action := quittingRootBestEndpointAction reward tail.1 root who
          let deviation := quittingStagePureEndpointBehaviorDeviation
            reward profile who stop action
          quittingTerminalPayoff reward
                (Function.update profile who deviation) who -
              quittingTerminalPayoff reward profile who =
            quittingLiveMass reward profile stop *
              quittingRootCoordinateNashDefect reward tail.1 root who ∧
          lower * regime.terminalGap ≤
            quittingTerminalPayoff reward
                (Function.update profile who deviation) who -
              quittingTerminalPayoff reward profile who) ∨
        (regime.terminalGap ≤
            max 0 (-quittingAtomicBlockerBalance reward root packet.observer) ∧
          lower * regime.terminalGap ≤
            quittingStageCoalitionMass reward profile stop packet.terminal *
              max 0
                (-quittingAtomicBlockerBalance reward root packet.observer))) := by
  obtain ⟨stops, hstop, hrows⟩ := dispatch
  refine ⟨stops n, hstop n, ?_⟩
  dsimp only
  obtain ⟨hmass, howner, halt⟩ := hrows n
  have hcommon := sureQuitterReachedRow_localization_and_legalDeviations
      reward frontier.base
        (quittingStoppingLawRectangleSourceProfile packet n)
        packet.observer (stops n) packet.terminal hlower
        (quittingRewardBound_nonneg reward)
        (abs_reward_le_quittingRewardBound reward) frontier.base_minimum
        hmass howner
  refine ⟨hmass, howner, hcommon.1, ?_⟩
  rcases halt with houtsider | hrefusal
  · left
    obtain ⟨who, hwho, hdefect, hweighted⟩ := houtsider
    refine ⟨who, hwho, hdefect, ?_, ?_⟩
    · exact hcommon.2 who hwho
    · rw [quittingTerminalPayoff_stageBestEndpointDeviation_sub_eq_liveMass_mul_defect]
      have hmassLe := quittingStageCoalitionMass_le_liveMass reward
        (quittingStoppingLawRectangleSourceProfile packet n) (stops n)
          packet.terminal
      have hdefectNonneg := quittingRootCoordinateNashDefect_nonneg reward
        (quittingTerminalSemanticPair reward
          (quittingAllContinueProfileSpine reward
            (quittingStoppingLawRectangleSourceProfile packet n)
            (stops n + 1))).1
        (quittingProfileLiveRoot reward
          (quittingStoppingLawRectangleSourceProfile packet n) (stops n)) who
      exact hweighted.trans
        (mul_le_mul_of_nonneg_right hmassLe hdefectNonneg)
  · exact Or.inr hrefusal

/-- The negative-collision rowwise alternative can be frozen without
creating another residual predicate.  Along a strict subsequence either one
fixed outsider has the full defect and a legal source-row deviation at every
selected row, or the observer's refusal certificate occurs at every selected
row. -/
theorem negativeCollisionAtomicDispatch_fixedSubsequence
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {regime : QuittingCounterexampleRegime reward}
    {frontier : QuittingCounterexampleStoppingLawFrontier regime}
    (packet : QuittingStoppingLawVanishingDebtRectangleSequence frontier)
    {lower : ℝ}
    (dispatch : HasQuittingStoppingLawNegativeCollisionAtomicDispatch
      packet lower) :
    ∃ (stop : ℕ → ℕ) (subseq : ℕ → ℕ),
      StrictMono subseq ∧
      (∀ rank, packet.quitTime (subseq rank) = some (stop (subseq rank))) ∧
      ((∃ who, who ≠ packet.observer ∧ ∀ rank,
          let profile := quittingStoppingLawRectangleSourceProfile packet
            (subseq rank)
          let root := quittingProfileLiveRoot reward profile
            (stop (subseq rank))
          let tail := quittingTerminalSemanticPair reward
            (quittingAllContinueProfileSpine reward profile
              (stop (subseq rank) + 1))
          let action := quittingRootBestEndpointAction reward tail.1 root who
          let deviation := quittingStagePureEndpointBehaviorDeviation
            reward profile who (stop (subseq rank)) action
          lower ≤ quittingStageCoalitionMass reward profile
              (stop (subseq rank)) packet.terminal ∧
            root packet.observer = PMF.pure true ∧
            regime.terminalGap ≤
              quittingRootCoordinateNashDefect reward tail.1 root who ∧
            quittingTerminalPayoff reward
                  (Function.update profile who deviation) who -
                quittingTerminalPayoff reward profile who =
              quittingLiveMass reward profile (stop (subseq rank)) *
                quittingRootCoordinateNashDefect reward tail.1 root who ∧
            lower * regime.terminalGap ≤
              quittingTerminalPayoff reward
                  (Function.update profile who deviation) who -
                quittingTerminalPayoff reward profile who) ∨
        (∀ rank,
          let profile := quittingStoppingLawRectangleSourceProfile packet
            (subseq rank)
          let root := quittingProfileLiveRoot reward profile
            (stop (subseq rank))
          lower ≤ quittingStageCoalitionMass reward profile
              (stop (subseq rank)) packet.terminal ∧
            root packet.observer = PMF.pure true ∧
            regime.terminalGap ≤
              max 0 (-quittingAtomicBlockerBalance reward root
                packet.observer) ∧
            lower * regime.terminalGap ≤
              quittingStageCoalitionMass reward profile
                (stop (subseq rank)) packet.terminal *
                max 0 (-quittingAtomicBlockerBalance reward root
                  packet.observer))) := by
  classical
  obtain ⟨stop, hstop, hrows⟩ := dispatch
  let outsider : ℕ → ι → Prop := fun n who =>
    let profile := quittingStoppingLawRectangleSourceProfile packet n
    let root := quittingProfileLiveRoot reward profile (stop n)
    let tail := quittingTerminalSemanticPair reward
      (quittingAllContinueProfileSpine reward profile (stop n + 1))
    who ≠ packet.observer ∧
      regime.terminalGap ≤
        quittingRootCoordinateNashDefect reward tail.1 root who ∧
      lower * regime.terminalGap ≤
        quittingStageCoalitionMass reward profile (stop n) packet.terminal *
          quittingRootCoordinateNashDefect reward tail.1 root who
  by_cases hfrequent : ∃ᶠ n in atTop, ∃ who, outsider n who
  · rw [Filter.frequently_exists] at hfrequent
    obtain ⟨who, hwhoFrequent⟩ := hfrequent
    obtain ⟨subseq, hsubseq, hwho⟩ :=
      extraction_of_frequently_atTop hwhoFrequent
    refine ⟨stop, subseq, hsubseq, fun rank => hstop (subseq rank),
      Or.inl ⟨who, (hwho 0).1, ?_⟩⟩
    intro rank
    dsimp only
    let profile := quittingStoppingLawRectangleSourceProfile packet
      (subseq rank)
    let root := quittingProfileLiveRoot reward profile (stop (subseq rank))
    let tail := quittingTerminalSemanticPair reward
      (quittingAllContinueProfileSpine reward profile
        (stop (subseq rank) + 1))
    obtain ⟨hmass, howner, _⟩ := hrows (subseq rank)
    have hfixed := hwho rank
    dsimp only [outsider] at hfixed
    have hgain :=
      quittingTerminalPayoff_stageBestEndpointDeviation_sub_eq_liveMass_mul_defect
        reward profile who (stop (subseq rank))
    have hlive : quittingStageCoalitionMass reward profile
        (stop (subseq rank)) packet.terminal ≤
        quittingLiveMass reward profile (stop (subseq rank)) :=
      quittingStageCoalitionMass_le_liveMass reward profile
        (stop (subseq rank)) packet.terminal
    have hdefectNonneg : 0 ≤ quittingRootCoordinateNashDefect reward
        tail.1 root who :=
      quittingRootCoordinateNashDefect_nonneg reward tail.1 root who
    have hweighted : lower * regime.terminalGap ≤
        quittingLiveMass reward profile (stop (subseq rank)) *
          quittingRootCoordinateNashDefect reward tail.1 root who :=
      hfixed.2.2.trans
        (mul_le_mul_of_nonneg_right hlive hdefectNonneg)
    refine ⟨hmass, howner, hfixed.2.1, ?_, ?_⟩
    · simpa only [profile, tail, root] using hgain
    · rw [hgain]
      simpa only [profile, tail, root] using hweighted
  · have hnoOutsider : ∀ᶠ n in atTop, ¬ ∃ who, outsider n who :=
      not_frequently.mp hfrequent
    obtain ⟨start, hstart⟩ := eventually_atTop.1 hnoOutsider
    let subseq : ℕ → ℕ := fun rank => start + rank
    have hsubseq : StrictMono subseq := fun _ _ hlt =>
      Nat.add_lt_add_left hlt start
    refine ⟨stop, subseq, hsubseq, fun rank => hstop (subseq rank),
      Or.inr ?_⟩
    intro rank
    dsimp only
    let profile := quittingStoppingLawRectangleSourceProfile packet
      (subseq rank)
    let root := quittingProfileLiveRoot reward profile (stop (subseq rank))
    obtain ⟨hmass, howner, halt⟩ := hrows (subseq rank)
    have hnone : ¬ ∃ who, outsider (subseq rank) who :=
      hstart (subseq rank) (Nat.le_add_right start rank)
    have hrefusal : regime.terminalGap ≤
          max 0 (-quittingAtomicBlockerBalance reward root packet.observer) ∧
        lower * regime.terminalGap ≤
          quittingStageCoalitionMass reward profile (stop (subseq rank))
            packet.terminal *
            max 0 (-quittingAtomicBlockerBalance reward root
              packet.observer) := by
      rcases halt with houtsider | hrefusal
      · exfalso
        apply hnone
        obtain ⟨who, hwho⟩ := houtsider
        exact ⟨who, by simpa only [outsider, profile, root] using hwho⟩
      · simpa only [profile, root] using hrefusal
    exact ⟨hmass, howner, hrefusal⟩

/-! ## L5 marked-row sharpening -/

/-- The current positive-collision leaf predicate supplies all hypotheses of
the pointwise sharpening.  Thus every eventually marked actual target row,
independently of the stored cluster's escape/fiber alternative, satisfies the
strong other-player defect lower bound. -/
theorem positiveCollisionMarkedTailDispatch_strongOtherDefectLocalization
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {regime : QuittingCounterexampleRegime reward}
    {frontier : QuittingCounterexampleStoppingLawFrontier regime}
    (packet : QuittingStoppingLawVanishingDebtRectangleSequence frontier)
    {lower : ℝ} (hlower : 0 < lower)
    (dispatch : HasQuittingStoppingLawPositiveCollisionMarkedTailDispatch
      packet lower) :
    ∃ (stop : ℕ → ℕ) (subseq : ℕ → ℕ),
      StrictMono subseq ∧
      (∀ᶠ rank in atTop,
        packet.quitTime (subseq rank) = some (stop (subseq rank))) ∧
      Tendsto (fun rank =>
        let profile := Function.update
          (quittingStoppingLawRectangleTargetProfile packet (subseq rank))
          packet.observer
          (quittingPureTimeBehaviorStrategy reward packet.observer
            (packet.quitTime (subseq rank)))
        quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward profile) packet.observer)
        atTop (nhds 0) ∧
      (∀ᶠ rank in atTop,
        let profile := Function.update
          (quittingStoppingLawRectangleTargetProfile packet (subseq rank))
          packet.observer
          (quittingPureTimeBehaviorStrategy reward packet.observer
            (packet.quitTime (subseq rank)))
        lower ≤ quittingStageCoalitionMass reward profile
          (stop (subseq rank)) packet.terminal ∧
        quittingTerminalSemanticDebtSum frontier.base -
            quittingTerminalSemanticDebt
              (quittingTerminalSemanticPair reward profile) packet.observer /
              lower ≤
          ∑ other ∈ Finset.univ.erase packet.observer,
            quittingRootCoordinateNashDefect reward
              (quittingTerminalSemanticPair reward
                (quittingAllContinueProfileSpine reward profile
                  (stop (subseq rank) + 1))).1
              (quittingProfileLiveRoot reward profile
                (stop (subseq rank))) other) := by
  obtain ⟨stop, _cluster, subseq, _hcluster, hsubseq, hfinite, hmass,
    _htail, _hmarked, _hdispatch⟩ := dispatch
  have hdebt := packet.observer_debt_tendsto_zero.comp hsubseq.tendsto_atTop
  have hdebt' : Tendsto (fun rank =>
      let profile := Function.update
        (quittingStoppingLawRectangleTargetProfile packet (subseq rank))
        packet.observer
        (quittingPureTimeBehaviorStrategy reward packet.observer
          (packet.quitTime (subseq rank)))
      quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward profile) packet.observer)
      atTop (nhds 0) := by
    simpa only [quittingStoppingLawRectangleTargetProfile,
      Function.comp_def] using hdebt
  refine ⟨stop, subseq, hsubseq, hfinite, hdebt', ?_⟩
  filter_upwards [hfinite, hmass] with rank htime hstage
  let profile := Function.update
    (quittingStoppingLawRectangleTargetProfile packet (subseq rank))
    packet.observer
    (quittingPureTimeBehaviorStrategy reward packet.observer
      (packet.quitTime (subseq rank)))
  have howner : quittingProfileLiveRoot reward profile
      (stop (subseq rank)) packet.observer = PMF.pure true := by
    dsimp only [profile]
    rw [quittingProfileLiveRoot_update_pureTime_self, htime,
      quittingPureTimeHazard_some_self]
  refine ⟨hstage, ?_⟩
  exact (sureQuitterReachedRow_localization_and_legalDeviations
    reward frontier.base profile packet.observer (stop (subseq rank))
      packet.terminal hlower (quittingRewardBound_nonneg reward)
      (abs_reward_le_quittingRewardBound reward) frontier.base_minimum
      hstage howner).1

/-- The marked-row sharpening selects one fixed non-observer along a further
strict subsequence.  Its literal one-row best-endpoint deviation is a genuine
behavioral deviation from the same target profile, and its global payoff gain
has a uniform division-free lower bound. -/
theorem positiveCollisionMarkedTailDispatch_fixedOtherLegalDeviation
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {regime : QuittingCounterexampleRegime reward}
    {frontier : QuittingCounterexampleStoppingLawFrontier regime}
    (packet : QuittingStoppingLawVanishingDebtRectangleSequence frontier)
    {lower : ℝ} (hlower : 0 < lower)
    (dispatch : HasQuittingStoppingLawPositiveCollisionMarkedTailDispatch
      packet lower) :
    ∃ (stop : ℕ → ℕ) (subseq : ℕ → ℕ) (other : ι),
      StrictMono subseq ∧
      other ≠ packet.observer ∧
      Tendsto (fun rank =>
        let profile := Function.update
          (quittingStoppingLawRectangleTargetProfile packet (subseq rank))
          packet.observer
          (quittingPureTimeBehaviorStrategy reward packet.observer
            (packet.quitTime (subseq rank)))
        quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward profile) packet.observer)
        atTop (nhds 0) ∧
      ∀ rank,
        packet.quitTime (subseq rank) = some (stop (subseq rank)) ∧
        let profile := Function.update
          (quittingStoppingLawRectangleTargetProfile packet (subseq rank))
          packet.observer
          (quittingPureTimeBehaviorStrategy reward packet.observer
            (packet.quitTime (subseq rank)))
        let tail := quittingTerminalSemanticPair reward
          (quittingAllContinueProfileSpine reward profile
            (stop (subseq rank) + 1))
        let root := quittingProfileLiveRoot reward profile
          (stop (subseq rank))
        let action := quittingRootBestEndpointAction reward tail.1 root other
        let deviation := quittingStagePureEndpointBehaviorDeviation
          reward profile other (stop (subseq rank)) action
        lower ≤ quittingStageCoalitionMass reward profile
            (stop (subseq rank)) packet.terminal ∧
          quittingTerminalPayoff reward
                (Function.update profile other deviation) other -
              quittingTerminalPayoff reward profile other =
            quittingLiveMass reward profile (stop (subseq rank)) *
              quittingRootCoordinateNashDefect reward tail.1 root other ∧
          lower * quittingTerminalSemanticDebtSum frontier.base / 2 ≤
            ((Finset.univ.erase packet.observer).card : ℝ) *
              (quittingTerminalPayoff reward
                  (Function.update profile other deviation) other -
                quittingTerminalPayoff reward profile other) := by
  obtain ⟨stop, baseSubseq, hbaseSubseq, hfinite, hdebt, hrows⟩ :=
    positiveCollisionMarkedTailDispatch_strongOtherDefectLocalization
      packet hlower dispatch
  let debt : ℕ → ℝ := fun rank =>
    let profile := Function.update
      (quittingStoppingLawRectangleTargetProfile packet (baseSubseq rank))
      packet.observer
      (quittingPureTimeBehaviorStrategy reward packet.observer
        (packet.quitTime (baseSubseq rank)))
    quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward profile) packet.observer
  have hscaledDebt : Tendsto (fun rank => debt rank / lower)
      atTop (nhds 0) := by
    have hdiv := hdebt.div_const lower
    simpa only [debt, zero_div] using hdiv
  have hsmall : ∀ᶠ rank in atTop,
      debt rank / lower <
        quittingTerminalSemanticDebtSum frontier.base / 2 :=
    hscaledDebt.eventually (Iio_mem_nhds (by
      linarith [frontier.base_positive]))
  have hready := hfinite.and (hrows.and hsmall)
  obtain ⟨start, hstart⟩ := eventually_atTop.1 hready
  let shifted : ℕ → ℕ := fun n => start + n
  have hshifted : StrictMono shifted := fun _ _ hlt =>
    Nat.add_lt_add_left hlt start
  let profile : ℕ → (quittingGame reward).BehaviorProfile := fun n =>
    Function.update
      (quittingStoppingLawRectangleTargetProfile packet
        (baseSubseq (shifted n)))
      packet.observer
      (quittingPureTimeBehaviorStrategy reward packet.observer
        (packet.quitTime (baseSubseq (shifted n))))
  let tail : ℕ → QuittingTerminalSemanticPair ι := fun n =>
    quittingTerminalSemanticPair reward
      (quittingAllContinueProfileSpine reward (profile n)
        (stop (baseSubseq (shifted n)) + 1))
  let root : ℕ → ι → PMF Bool := fun n =>
    quittingProfileLiveRoot reward (profile n)
      (stop (baseSubseq (shifted n)))
  let defect : ℕ → ι → ℝ := fun n who =>
    quittingRootCoordinateNashDefect reward (tail n).1 (root n) who
  let players : Finset ι := Finset.univ.erase packet.observer
  have hreadyAt : ∀ n,
      packet.quitTime (baseSubseq (shifted n)) =
          some (stop (baseSubseq (shifted n))) ∧
        lower ≤ quittingStageCoalitionMass reward (profile n)
          (stop (baseSubseq (shifted n))) packet.terminal ∧
        quittingTerminalSemanticDebtSum frontier.base / 2 ≤
          ∑ other ∈ players, defect n other := by
    intro n
    obtain ⟨htime, hrow, hdebtSmall⟩ :=
      hstart (shifted n) (Nat.le_add_right start n)
    refine ⟨htime, ?_, ?_⟩
    · simpa only [profile] using hrow.1
    dsimp only [debt] at hdebtSmall
    dsimp only at hrow
    dsimp only [profile, tail, root, defect, players]
    linarith [hrow.2]
  have hplayers : players.Nonempty := by
    by_contra hempty
    have hsum := (hreadyAt 0).2.2
    rw [Finset.not_nonempty_iff_eq_empty.mp hempty] at hsum
    simp only [Finset.sum_empty] at hsum
    linarith [frontier.base_positive]
  have hwitness : ∀ n, ∃ who ∈ players,
      quittingTerminalSemanticDebtSum frontier.base / 2 ≤
        (players.card : ℝ) * defect n who := by
    intro n
    obtain ⟨who, hwho, havg⟩ :=
      QuittingMarkedFencePacket.exists_sum_le_card_mul
        players hplayers (defect n)
    exact ⟨who, hwho, (hreadyAt n).2.2.trans havg⟩
  have hfrequent : ∃ who ∈ players,
      ∃ᶠ n in atTop,
        quittingTerminalSemanticDebtSum frontier.base / 2 ≤
          (players.card : ℝ) * defect n who := by
    by_contra hnot
    push Not at hnot
    have hallSmall : ∀ᶠ n in atTop, ∀ who ∈ players,
        (players.card : ℝ) * defect n who <
          quittingTerminalSemanticDebtSum frontier.base / 2 := by
      rw [eventually_all]
      intro who
      by_cases hwho : who ∈ players
      · filter_upwards [hnot who hwho] with n hn
        intro _hmem
        exact hn
      · exact Filter.Eventually.of_forall fun _ => fun hmem =>
          (hwho hmem).elim
    obtain ⟨n, hn⟩ := hallSmall.exists
    obtain ⟨who, hwho, hwitnessWho⟩ := hwitness n
    exact (not_lt_of_ge hwitnessWho) (hn who hwho)
  obtain ⟨other, hotherMem, hotherFrequent⟩ := hfrequent
  obtain ⟨playerSubseq, hplayerSubseq, hplayerLower⟩ :=
    extraction_of_frequently_atTop hotherFrequent
  let subseq : ℕ → ℕ := fun rank =>
    baseSubseq (shifted (playerSubseq rank))
  have hsubseq : StrictMono subseq :=
    hbaseSubseq.comp (hshifted.comp hplayerSubseq)
  have hotherNe : other ≠ packet.observer :=
    (Finset.mem_erase.mp hotherMem).1
  have hdebtFinal : Tendsto (fun rank =>
      let actual := Function.update
        (quittingStoppingLawRectangleTargetProfile packet (subseq rank))
        packet.observer
        (quittingPureTimeBehaviorStrategy reward packet.observer
          (packet.quitTime (subseq rank)))
      quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward actual) packet.observer)
      atTop (nhds 0) := by
    exact hdebt.comp (hshifted.comp hplayerSubseq).tendsto_atTop
  refine ⟨stop, subseq, other, hsubseq, hotherNe, hdebtFinal, ?_⟩
  intro rank
  have hdata := hreadyAt (playerSubseq rank)
  refine ⟨by simpa only [subseq] using hdata.1, ?_⟩
  dsimp only
  let actual := profile (playerSubseq rank)
  have hprofile : actual = Function.update
      (quittingStoppingLawRectangleTargetProfile packet (subseq rank))
      packet.observer
      (quittingPureTimeBehaviorStrategy reward packet.observer
        (packet.quitTime (subseq rank))) := by
    rfl
  have hgain :=
    quittingTerminalPayoff_stageBestEndpointDeviation_sub_eq_liveMass_mul_defect
      reward actual other (stop (subseq rank))
  have hlive : lower ≤ quittingLiveMass reward actual
      (stop (subseq rank)) :=
    hdata.2.1.trans (quittingStageCoalitionMass_le_liveMass reward actual
      (stop (subseq rank)) packet.terminal)
  have hdefectNonneg : 0 ≤ defect (playerSubseq rank) other :=
    quittingRootCoordinateNashDefect_nonneg reward _ _ other
  have hscaledLive : lower *
        ((players.card : ℝ) * defect (playerSubseq rank) other) ≤
      (players.card : ℝ) *
        (quittingLiveMass reward actual (stop (subseq rank)) *
          defect (playerSubseq rank) other) := by
    have hcardNonneg : 0 ≤ (players.card : ℝ) := by positivity
    have hcoefficient : 0 ≤
        (players.card : ℝ) * defect (playerSubseq rank) other :=
      mul_nonneg hcardNonneg hdefectNonneg
    calc
      lower * ((players.card : ℝ) * defect (playerSubseq rank) other) ≤
          quittingLiveMass reward actual (stop (subseq rank)) *
            ((players.card : ℝ) * defect (playerSubseq rank) other) :=
        mul_le_mul_of_nonneg_right hlive hcoefficient
      _ = (players.card : ℝ) *
          (quittingLiveMass reward actual (stop (subseq rank)) *
            defect (playerSubseq rank) other) := by ring
  have hfloor : lower *
        (quittingTerminalSemanticDebtSum frontier.base / 2) ≤
      lower * ((players.card : ℝ) *
        defect (playerSubseq rank) other) :=
    mul_le_mul_of_nonneg_left (hplayerLower rank) hlower.le
  have hmassFinal : lower ≤ quittingStageCoalitionMass reward
      (Function.update
        (quittingStoppingLawRectangleTargetProfile packet (subseq rank))
        packet.observer
        (quittingPureTimeBehaviorStrategy reward packet.observer
          (packet.quitTime (subseq rank))))
      (stop (subseq rank)) packet.terminal := by
    simpa only [actual, profile, subseq] using hdata.2.1
  have hgainFinal := hgain
  rw [hprofile] at hgainFinal
  refine ⟨hmassFinal, hgainFinal, ?_⟩
  rw [hgainFinal]
  change lower * quittingTerminalSemanticDebtSum frontier.base / 2 ≤
    (players.card : ℝ) *
      (quittingLiveMass reward actual (stop (subseq rank)) *
        defect (playerSubseq rank) other)
  rw [mul_div_assoc]
  exact hfloor.trans hscaledLive

end GameTheory
