/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Research.Quitting.PureTimeRectangleSequenceNormalForm
import UniformEquilibrium.Diagnostics.Quitting.StoppingLaw.VanishingDebtAtomAlternative
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPositiveSlopeCausalRegression

/-!
# The legal target gain and the two-deviation state-match obstruction

The vanishing-error rectangle decoder retains a stronger fact than its
current packet records.  Its pure-time observer response gains a fixed amount
over the literal *mover-reset target*: the endpoint observer debt is at least
the off-diagonal charge, while the selected response misses the endpoint cap
by at most `error`.

This does not give an observer deviation from the original source.  The
rectangle compares the same observer response before and after a different
player's strategy is changed.  Exact-prefix Continue access preserves that
distinction: the target is a mover deviation, and the pure-time response is a
subsequent observer deviation.

The final regression makes the obstruction sharp.  Along an escaping
pure-time sequence there is a fixed positive terminal atom, zero target
observer debt, reached positive endpoint gap, and a uniform legal observer
gain at the target.  Nevertheless *every* observer deviation from the source
has nonpositive gain.  Elementary compression cannot repair this label
mismatch because it preserves/approximates a supplied continuation; it does
not perform the mover update on behalf of the observer.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The exact semantic premise missing from a two-deviation rectangle: the
observer response must be profitable against the source whose prefix is being
tested, not only against the mover-reset target. -/
def HasQuittingSourceMatchedObserverGain
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source : (quittingGame reward).BehaviorProfile)
    (observer : ι) (lower : ℝ) : Prop :=
  ∃ deviation : (quittingGame reward).BehaviorStrategy observer,
    lower ≤ quittingTerminalPayoff reward
        (Function.update source observer deviation) observer -
      quittingTerminalPayoff reward source observer

/-- The decoder alternative with the cutoff-independent legal gain retained
on its rectangle side. -/
def HasQuittingStoppingLawVanishingDebtGainAtomAlternative
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (mover observer : ι)
    (target : (quittingGame reward).BehaviorStrategy mover)
    (charge error : ℝ) : Prop :=
  (∃ terminal : {S : Finset ι // S.Nonempty},
    charge / 2 ≤
      (Fintype.card (QuittingTerminalOutcome ι) : ℝ) *
        quittingTerminalPayoffDifferenceAtom reward profile
          (Function.update profile mover target) observer (some terminal)) ∨
  ∃ quitTime : Option ℕ, ∃ terminal : {S : Finset ι // S.Nonempty},
    charge / 4 ≤
      (Fintype.card (QuittingTerminalOutcome ι) : ℝ) *
        quittingTerminalPayoffDifferenceAtom reward
          (Function.update (Function.update profile mover target) observer
            (quittingPureTimeBehaviorStrategy reward observer quitTime))
          (Function.update (Function.update profile mover (profile mover)) observer
            (quittingPureTimeBehaviorStrategy reward observer quitTime))
          observer (some terminal) ∧
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (Function.update (Function.update profile mover target) observer
            (quittingPureTimeBehaviorStrategy reward observer quitTime)))
        observer ≤ error ∧
    charge - error ≤
      quittingTerminalPayoff reward
          (Function.update (Function.update profile mover target) observer
            (quittingPureTimeBehaviorStrategy reward observer quitTime)) observer -
        quittingTerminalPayoff reward
          (Function.update profile mover target) observer

/-- **The missing gain was already present at the target.**  Under the same
slope hypotheses as the atom decoder, its rectangle response gains at least
`charge - error` over the mover-reset endpoint. -/
theorem exists_prescribedAtom_or_pureTimeRectangleAtom_with_debtBound_and_targetGain
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (mover observer : ι)
    (target : (quittingGame reward).BehaviorStrategy mover)
    (lambda charge error : ℝ) (hlambda0 : 0 < lambda)
    (hlambda1 : lambda ≤ 1) (hcharge : 0 < charge)
    (herror : 0 < error) (herrorLe : error ≤ charge / 8)
    (hslope : lambda * charge ≤
      quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            (Function.update profile mover
              (quittingStoppingLawMixtureBehaviorStrategy reward mover
                (profile mover) target lambda hlambda0.le hlambda1))) observer -
        quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward profile) observer) :
    HasQuittingStoppingLawVanishingDebtGainAtomAlternative reward profile
      mover observer target charge error := by
  let endpoint := Function.update profile mover target
  let mixed := Function.update profile mover
    (quittingStoppingLawMixtureBehaviorStrategy reward mover
      (profile mover) target lambda hlambda0.le hlambda1)
  let sourcePair := quittingTerminalSemanticPair reward profile
  let endpointPair := quittingTerminalSemanticPair reward endpoint
  let mixedPair := quittingTerminalSemanticPair reward mixed
  have hchord := quittingTerminalSemanticDebt_stoppingLawMixture_le
    reward profile mover observer (profile mover) target lambda hlambda0.le
      hlambda1
  rw [Function.update_eq_self] at hchord
  change quittingTerminalSemanticDebt mixedPair observer ≤
      (1 - lambda) * quittingTerminalSemanticDebt sourcePair observer +
        lambda * quittingTerminalSemanticDebt endpointPair observer at hchord
  have hendpointSlope : charge ≤
      quittingTerminalSemanticDebt endpointPair observer -
        quittingTerminalSemanticDebt sourcePair observer := by
    change lambda * charge ≤
      quittingTerminalSemanticDebt mixedPair observer -
        quittingTerminalSemanticDebt sourcePair observer at hslope
    have hscaled : lambda * charge ≤ lambda *
        (quittingTerminalSemanticDebt endpointPair observer -
          quittingTerminalSemanticDebt sourcePair observer) := by
      nlinarith
    nlinarith
  have hsourceDebtNonneg : 0 ≤
      quittingTerminalSemanticDebt sourcePair observer := by
    exact quittingTerminalDeviationDebt_nonneg reward profile observer
  have hendpointDebt : charge ≤
      quittingTerminalSemanticDebt endpointPair observer := by
    linarith
  rcases exists_prescribedAtom_or_pureTimeRectangleAtom_with_debtBound
      reward profile mover observer target lambda charge error hlambda0
      hlambda1 hcharge herror herrorLe hslope with
    hprescribed | ⟨quitTime, terminal, hatom, hdebt⟩
  · exact Or.inl hprescribed
  · right
    refine ⟨quitTime, terminal, hatom, hdebt, ?_⟩
    let response := quittingPureTimeBehaviorStrategy reward observer quitTime
    have hdebt' :
        quittingContinuationBestResponseValue reward endpoint observer -
          quittingTerminalPayoff reward
            (Function.update endpoint observer response) observer ≤ error := by
      unfold quittingTerminalSemanticDebt quittingTerminalSemanticPair at hdebt
      change quittingContinuationBestResponseValue reward
          (Function.update endpoint observer response) observer -
        quittingTerminalPayoff reward
          (Function.update endpoint observer response) observer ≤ error at hdebt
      rw [quittingContinuationBestResponseValue_update_self] at hdebt
      exact hdebt
    change charge ≤
      quittingContinuationBestResponseValue reward endpoint observer -
        quittingTerminalPayoff reward endpoint observer at hendpointDebt
    simpa only [endpoint, response] using (show charge - error ≤
        quittingTerminalPayoff reward
            (Function.update endpoint observer response) observer -
          quittingTerminalPayoff reward endpoint observer by linarith)

/-! ## A sharp escaping regression -/

namespace PureTimeRectangleTargetSourceNoGo

open PositiveSlopeCausalRegression
open QuittingSureSetOwnerRepair

/-- The escaping observer response. -/
def response (n : ℕ) : (quittingGame reward).BehaviorStrategy observer :=
  quittingPureTimeBehaviorStrategy reward observer (some (n + 1))

/-- Apply that response after the mover has reset to `Never`. -/
def targetResponse (n : ℕ) : (quittingGame reward).BehaviorProfile :=
  Function.update endpoint observer (response n)

/-- Apply the identical response before the mover reset. -/
def sourceResponse (n : ℕ) : (quittingGame reward).BehaviorProfile :=
  Function.update source observer (response n)

def terminal : {S : Finset Bool // S.Nonempty} :=
  quittingSingletonTerminal observer

theorem targetRoots_eq_allContinue :
    quittingProfileLiveRoot reward endpoint =
      fun _ _ => PMF.pure false := by
  funext time who
  cases who <;>
    simp [endpoint, quittingProfileLiveRoot, quittingStationaryProfile,
      StochasticGame.stationaryBehaviorProfile, quittingPureSetRoot,
      quittingSetAction]

theorem targetResponse_payoff_eq_two (n : ℕ) :
    quittingTerminalPayoff reward (targetResponse n) observer = 2 := by
  change quittingTerminalPayoff reward
    (Function.update endpoint observer
      (quittingPureTimeBehaviorStrategy reward observer (some (n + 1))))
    observer = 2
  rw [quittingTerminalPayoff_update_pureTimeBehaviorStrategy,
    targetRoots_eq_allContinue]
  have hgeneral : ∀ start fuel : ℕ,
      quittingRootSequencePureTimeTerminalValue reward
        (fun _ _ => PMF.pure false) observer (some (start + fuel)) start = 2 := by
    intro start fuel
    induction fuel generalizing start with
    | zero =>
        rw [Nat.add_zero,
          quittingRootSequencePureTimeTerminalValue_some_self_eq_fixedOpponents]
        change quittingStationaryFixedOpponentsQuitValue reward
          (quittingPureSetRoot (∅ : Finset Bool)) observer = 2
        rw [quittingStationaryFixedOpponentsQuitValue_pureSetRoot]
        norm_num [quittingSetReward, reward, observer, mover]
    | succ fuel ih =>
        unfold quittingRootSequencePureTimeTerminalValue
        rw [quittingRootSequenceHazardTerminalValue_eq_hazardBellman]
        have hne : start ≠ start + (fuel + 1) := by omega
        rw [quittingPureTimeHazard_some_of_ne hne]
        simp only [PMF.pure_apply,
          if_neg (by decide : (true : Bool) ≠ false), ENNReal.toReal_zero,
          if_true, ENNReal.toReal_one, zero_mul, one_mul, zero_add]
        have htime : start + (fuel + 1) = (start + 1) + fuel := by omega
        change quittingFixedOpponentsContinueReward reward
              (fun _ _ => PMF.pure false) observer start +
            quittingFixedOpponentsContinueMass
                (fun _ _ => PMF.pure false) observer start *
              quittingRootSequencePureTimeTerminalValue reward
                (fun _ _ => PMF.pure false) observer
                (some (start + (fuel + 1))) (start + 1) = 2
        rw [htime, ih (start + 1)]
        change quittingStationaryFixedOpponentsContinueReward reward
              (quittingPureSetRoot (∅ : Finset Bool)) observer +
            quittingStationaryFixedOpponentsContinueMass
              (quittingPureSetRoot (∅ : Finset Bool)) observer * 2 = 2
        rw [quittingStationaryFixedOpponentsContinueReward_pureSetRoot,
          quittingStationaryFixedOpponentsContinueMass_pureSetRoot_of_erase_empty
            (by simp)]
        norm_num [quittingSetReward]
  simpa using hgeneral 0 (n + 1)

theorem source_payoff_eq_zero :
    quittingTerminalPayoff reward source observer = 0 := by
  unfold source
  rw [quittingTerminalPayoff_pureSetRoot]
  norm_num [quittingSetReward, reward, observer, mover]

/-- The source has no profitable observer deviation at all. -/
theorem source_observer_deviation_nonpos
    (deviation : (quittingGame reward).BehaviorStrategy observer) :
    quittingTerminalPayoff reward
        (Function.update source observer deviation) observer -
      quittingTerminalPayoff reward source observer ≤ 0 := by
  have hupper := quittingTerminalPayoff_update_pureSetRoot_le reward
    ({mover} : Finset Bool) observer deviation
  change quittingTerminalPayoff reward
      (Function.update source observer deviation) observer ≤ _ at hupper
  rw [source_payoff_eq_zero]
  have hjoint : ({observer, mover} : Finset Bool) ≠ {observer} := by decide
  simpa [quittingSetReward, reward, observer, mover, Fin.ext_iff,
    hjoint] using hupper

theorem endpoint_payoff_observer_eq_zero :
    quittingTerminalPayoff reward endpoint observer = 0 := by
  unfold endpoint
  rw [quittingTerminalPayoff_pureSetRoot]
  simp [quittingSetReward]

theorem endpoint_cap_observer_eq_two :
    quittingContinuationBestResponseValue reward endpoint observer = 2 := by
  have hdebt := endpoint_debt_observer
  unfold quittingTerminalSemanticDebt quittingTerminalSemanticPair at hdebt
  change quittingContinuationBestResponseValue reward endpoint observer -
      quittingTerminalPayoff reward endpoint observer = 2 at hdebt
  rw [endpoint_payoff_observer_eq_zero] at hdebt
  linarith

theorem targetResponse_debt_eq_zero (n : ℕ) :
    quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward (targetResponse n)) observer = 0 := by
  unfold quittingTerminalSemanticDebt quittingTerminalSemanticPair
  change quittingContinuationBestResponseValue reward
      (Function.update endpoint observer (response n)) observer -
    quittingTerminalPayoff reward (targetResponse n) observer = 0
  rw [quittingContinuationBestResponseValue_update_self,
    endpoint_cap_observer_eq_two, targetResponse_payoff_eq_two]
  ring

theorem targetResponse_legalGain_eq_two (n : ℕ) :
    quittingTerminalPayoff reward (targetResponse n) observer -
      quittingTerminalPayoff reward endpoint observer = 2 := by
  rw [targetResponse_payoff_eq_two, endpoint_payoff_observer_eq_zero]
  ring

theorem allContinue_never_payoff_eq_zero (start : ℕ) :
    quittingRootSequencePureTimeTerminalValue reward
      (fun _ _ => PMF.pure false) observer none start = 0 := by
  unfold quittingRootSequencePureTimeTerminalValue
    quittingRootSequenceHazardTerminalValue
    quittingRootSequenceTerminalValue
  have hupdate : quittingRootSequenceUpdate
      (fun _ : ℕ => fun _ : Bool => PMF.pure false) observer
      (quittingPureTimeHazard none) = fun _ _ => PMF.pure false := by
    funext time who
    by_cases hwho : who = observer
    · subst who
      simp [quittingRootSequenceUpdate]
    · simp [quittingRootSequenceUpdate, Function.update_of_ne hwho]
  rw [hupdate]
  have hprofile : quittingRootSequenceProfile reward
      (fun _ _ => PMF.pure false) start =
      quittingAlwaysContinueProfile reward := by
    rfl
  rw [hprofile, quittingTerminalPayoff_quittingAlwaysContinue]

theorem target_lateEndpointGap_eq_two (n : ℕ) :
    quittingRootEndpointDifference reward
      (fun _ => quittingRootSequencePureTimeTerminalValue reward
        (quittingProfileLiveRoot reward endpoint) observer none (n + 2))
      (quittingProfileLiveRoot reward endpoint (n + 1)) observer = 2 := by
  rw [targetRoots_eq_allContinue]
  have htail := allContinue_never_payoff_eq_zero (n + 2)
  change quittingRootEndpointDifference reward
    (fun _ => quittingRootSequencePureTimeTerminalValue reward
      (fun _ _ => PMF.pure false) observer none (n + 2))
    (quittingAllContinueRoot : Bool → PMF Bool) observer = 2
  rw [quittingRootEndpointDifference_allContinueRoot]
  change reward (quittingSingletonTerminal observer) observer -
      quittingRootSequencePureTimeTerminalValue reward
        (fun _ _ => PMF.pure false) observer none (n + 2) = 2
  rw [htail]
  norm_num [reward, observer, mover, quittingSingletonTerminal]

theorem target_reaches_lateEndpoint (n : ℕ) :
    quittingOpponentSurvivalWeight
      (quittingProfileLiveRoot reward endpoint) observer 0 (n + 1) = 1 := by
  rw [targetRoots_eq_allContinue]
  simp [quittingOpponentSurvivalWeight,
    quittingFixedOpponentsContinueMass,
    quittingStationaryContinueMass, quittingAllContinueAction]

theorem targetResponse_roots (n time : ℕ) (who : Bool) :
    quittingProfileLiveRoot reward (targetResponse n) time who =
      if who = observer ∧ time = n + 1 then PMF.pure true
      else PMF.pure false := by
  change quittingProfileLiveRoot reward
    (Function.update endpoint observer (response n)) time who = _
  rw [quittingProfileLiveRoot_update_eq_rootSequenceUpdate,
    targetRoots_eq_allContinue]
  unfold quittingRootSequenceUpdate response
  by_cases hwho : who = observer
  · subst who
    simp [quittingBehaviorLiveHazard,
      quittingPureTimeBehaviorStrategy, quittingPureTimeHazard]
  · simp [hwho]

theorem target_singleton_mass_eq_one (n : ℕ) :
    quittingTerminalOutcomeMass reward (targetResponse n) (some terminal) = 1 := by
  change quittingTerminalOutcomeMass reward
    (Function.update endpoint observer
      (quittingPureTimeBehaviorStrategy reward observer (some (n + 1))))
    (some terminal) = 1
  rw [quittingTerminalOutcomeMass_update_pureTime_some_mem_eq_at reward endpoint
      observer (n + 1) terminal (by
        change observer ∈ ({observer} : Finset Bool)
        simp)]
  rw [quittingStageCoalitionMass_eq_liveMass_mul_rootCoalitionMass,
    quittingLiveMass_eq_jointSurvivalWeight_profileLiveRoot]
  let roots := quittingProfileLiveRoot reward (targetResponse n)
  have hsurvival : quittingJointSurvivalWeight roots 0 (n + 1) = 1 := by
    calc
      quittingJointSurvivalWeight roots 0 (n + 1) =
          quittingJointSurvivalWeight
            (fun _ : ℕ => fun _ : Bool => PMF.pure false) 0 (n + 1) := by
        apply quittingJointSurvivalWeight_congr
        intro offset hoffset
        funext who
        dsimp only [roots]
        rw [targetResponse_roots]
        simp only [Nat.zero_add]
        rw [if_neg]
        intro h
        omega
      _ = 1 := by
        rw [quittingJointSurvivalWeight_eq_prod]
        simp [quittingStationaryContinueMass,
          quittingAllContinueAction]
  have hroot : roots (n + 1) = fun who =>
      if who = observer then PMF.pure true else PMF.pure false := by
    funext who
    dsimp only [roots]
    rw [targetResponse_roots]
    simp
  change quittingJointSurvivalWeight roots 0 (n + 1) *
      quittingRootCoalitionMass (roots (n + 1)) terminal.val = 1
  rw [hsurvival, hroot, one_mul]
  unfold quittingRootCoalitionMass
  change Math.PMFProduct.coalitionMass
      (fun who => ((if who = observer then PMF.pure true
        else PMF.pure false) true).toReal) ({observer} : Finset Bool) = 1
  unfold Math.PMFProduct.coalitionMass
  rw [show ({observer} : Finset Bool)ᶜ = {mover} by decide]
  simp [observer, mover]

theorem source_singleton_mass_eq_zero (n : ℕ) :
    quittingTerminalOutcomeMass reward (sourceResponse n) (some terminal) = 0 := by
  change quittingTerminalOutcomeMass reward
    (Function.update source observer
      (quittingPureTimeBehaviorStrategy reward observer (some (n + 1))))
    (some terminal) = 0
  rw [quittingTerminalOutcomeMass_update_pureTime_some_mem_eq_at reward source
      observer (n + 1) terminal (by
        change observer ∈ ({observer} : Finset Bool)
        simp)]
  rw [quittingStageCoalitionMass_eq_liveMass_mul_rootCoalitionMass]
  have hlive : quittingLiveMass reward
      (Function.update source observer
        (quittingPureTimeBehaviorStrategy reward observer (some (n + 1))))
      (n + 1) = 0 := by
    let deviated := Function.update source observer
      (quittingPureTimeBehaviorStrategy reward observer (some (n + 1)))
    have hliveOne : quittingLiveMass reward deviated 1 = 0 := by
      rw [show 1 = 0 + 1 by omega, quittingLiveMass_succ]
      have hcontinue : quittingJointContinueMass reward deviated 0 = 0 := by
        rw [quittingJointContinueMass_eq_product]
        rw [Fintype.prod_bool]
        have hmoverContinue :
            ((deviated mover 0 (quittingLiveHist reward 0)) false).toReal = 0 := by
          dsimp only [deviated]
          rw [Function.update_of_ne (by decide : mover ≠ observer)]
          change ((quittingPureSetRoot ({mover} : Finset Bool) mover) false).toReal = 0
          simp [quittingPureSetRoot, quittingSetAction, mover]
        rw [hmoverContinue, mul_zero]
      rw [hcontinue, mul_zero]
    have hle := quittingLiveMass_antitone reward deviated
      (show 1 ≤ n + 1 by omega)
    have hnonneg := quittingLiveMass_nonneg reward deviated (n + 1)
    change quittingLiveMass reward deviated (n + 1) = 0
    linarith
  rw [hlive, zero_mul]

theorem fixed_positive_terminalAtom (n : ℕ) :
    quittingTerminalPayoffDifferenceAtom reward (targetResponse n)
      (sourceResponse n) observer (some terminal) = 2 := by
  unfold quittingTerminalPayoffDifferenceAtom
  rw [target_singleton_mass_eq_one, source_singleton_mass_eq_zero]
  norm_num [quittingTerminalOutcomeReward, terminal, reward, observer, mover,
    quittingSingletonTerminal]

theorem escaping_time_tendsto :
    Tendsto (fun n : ℕ => n + 1) atTop atTop := by
  refine tendsto_atTop.2 fun bound => ?_
  exact eventually_atTop.2 ⟨bound, fun n hn => by omega⟩

/-- **Sharp two-deviation no-go.**  All of the temporal/semantic data on the
target coexist with the complete absence of a profitable observer deviation
from the source. -/
theorem escaping_positiveAtom_zeroDebt_lateGap_but_no_sourceObserverGain :
    Tendsto (fun n : ℕ => n + 1) atTop atTop ∧
      (∀ n, quittingTerminalPayoffDifferenceAtom reward (targetResponse n)
        (sourceResponse n) observer (some terminal) = 2) ∧
      (∀ n, quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward (targetResponse n)) observer = 0) ∧
      (∀ n, quittingTerminalPayoff reward (targetResponse n) observer -
        quittingTerminalPayoff reward endpoint observer = 2) ∧
      (∀ n, quittingRootEndpointDifference reward
        (fun _ => quittingRootSequencePureTimeTerminalValue reward
          (quittingProfileLiveRoot reward endpoint) observer none (n + 2))
        (quittingProfileLiveRoot reward endpoint (n + 1)) observer = 2 ∧
        quittingOpponentSurvivalWeight
          (quittingProfileLiveRoot reward endpoint) observer 0 (n + 1) = 1) ∧
      ∀ deviation : (quittingGame reward).BehaviorStrategy observer,
        quittingTerminalPayoff reward
            (Function.update source observer deviation) observer -
          quittingTerminalPayoff reward source observer ≤ 0 := by
  exact ⟨escaping_time_tendsto, fixed_positive_terminalAtom,
    targetResponse_debt_eq_zero, targetResponse_legalGain_eq_two,
    fun n => ⟨target_lateEndpointGap_eq_two n,
      target_reaches_lateEndpoint n⟩, source_observer_deviation_nonpos⟩

/-- No positive source-matched gain can be recovered from the regression's
target data.  This is the minimal missing premise before any exact-prefix
transport: it already fails with the empty exact prefix. -/
theorem not_hasQuittingSourceMatchedObserverGain_source
    {lower : ℝ} (hlower : 0 < lower) :
    ¬HasQuittingSourceMatchedObserverGain reward source observer lower := by
  rintro ⟨deviation, hgain⟩
  have hnonpos := source_observer_deviation_nonpos deviation
  linarith

end PureTimeRectangleTargetSourceNoGo

end GameTheory
