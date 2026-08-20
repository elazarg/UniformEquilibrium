/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import GameTheory.Stochastic.Kuhn
import MathUE.Probability.FinDistIntegral
import UniformEquilibrium.ProofView.Concepts.Stochastic.Equilibrium.Discounted
import UniformEquilibrium.ProofView.Native.History

/-!
# Exact execution semantics for the native bridge

The compiled law below is a proof view of GameTheory's sole Protocol runner:
it unfolds one ordinary simultaneous-action draw and one native transition,
then recurses under the translated continuation profile. The main theorem
identifies this recursion exactly with GameTheory's public-history law.
-/

noncomputable section

namespace GameTheory

open _root_.Math.Probability
open GameTheory.Math.Probability
open GameTheory.Protocol

namespace StochasticGame.NativeBridge

variable {ι : Type} (G : StochasticGame ι) [Fintype ι]
  [Finite G.State] [∀ i, Finite (G.Act i)] [∀ i, Nonempty (G.Act i)]

/-- The native public-history law written in the indexed PMF proof view's
one-stage continuation coordinates. -/
def compiledPublicHistoryLaw (profile : G.BehaviorProfile) :
    (initial : G.State) → (horizon : ℕ) → FinDist G.toNative.PublicHistory
  | _, 0 => FinDist.pure []
  | initial, horizon + 1 =>
      (FinDist.pi fun i => finDistOfPMF
        (profile i 0 (G.emptyHist initial))).bind fun actions =>
        (G.toNative.transition initial actions).bindOnSupport fun target _ =>
          FinDist.map
            (fun continuation => continuation ++
              [{ source := initial, joint := actions, target := target }])
            (compiledPublicHistoryLaw
              (G.shiftProfile profile (initial, actions)) target horizon)

omit [∀ i, Nonempty (G.Act i)] in
@[simp]
theorem compiledPublicHistoryLaw_zero (profile : G.BehaviorProfile)
    (initial : G.State) :
    compiledPublicHistoryLaw G profile initial 0 = FinDist.pure [] :=
  rfl

omit [∀ i, Nonempty (G.Act i)] in
theorem compiledPublicHistoryLaw_succ (profile : G.BehaviorProfile)
    (initial : G.State) (horizon : ℕ) :
    compiledPublicHistoryLaw G profile initial (horizon + 1) =
      (FinDist.pi fun i => finDistOfPMF
        (profile i 0 (G.emptyHist initial))).bind fun actions =>
        (G.toNative.transition initial actions).bindOnSupport fun target _ =>
          FinDist.map
            (fun continuation => continuation ++
              [{ source := initial, joint := actions, target := target }])
            (compiledPublicHistoryLaw G
              (G.shiftProfile profile (initial, actions)) target horizon) :=
  rfl

/-- GameTheory's canonical Protocol execution has exactly the compiled
proof-view public-history law. -/
theorem native_publicHistoryLaw_eq_compiled
    (profile : G.BehaviorProfile) (initial : G.State) :
    ∀ horizon,
      G.toNative.publicHistoryLaw initial
          (toNativeBehaviorProfile G initial profile) horizon =
        compiledPublicHistoryLaw G profile initial horizon := by
  intro horizon
  induction horizon generalizing profile initial with
  | zero =>
      change G.toNative.restartHistoryLaw
          (toNativeBehaviorProfile G initial profile) [] initial 0 = _
      rw [Stochastic.Game.restartHistoryLaw_zero]
      rfl
  | succ horizon ih =>
      let publicProfile := toNativePublicProfile G initial profile
      have hstep := G.toNative.restartHistoryLaw_succ_toPublicProfile
        publicProfile [] initial horizon
      change G.toNative.publicHistoryLaw initial
          (G.toNative.toBehaviorProfile initial publicProfile) (horizon + 1) = _
      rw [← show G.toNative.restartHistoryLaw
          (G.toNative.toBehaviorProfile initial publicProfile) [] initial
            (horizon + 1) =
          G.toNative.publicHistoryLaw initial
            (G.toNative.toBehaviorProfile initial publicProfile)
              (horizon + 1) by
        simp [Stochastic.Game.restartHistoryLaw]]
      rw [hstep, compiledPublicHistoryLaw_succ]
      apply FinDist.bind_congr
      intro actions _
      apply FinDist.bindOnSupport_congr
      intro target realized
      let record : G.toNative.StageRecord :=
        { source := initial, joint := actions, target := target }
      have hpublic :
          Stochastic.Game.PublicProfile.after publicProfile [record] =
            toNativePublicProfile G target
              (G.shiftProfile profile (initial, actions)) :=
        toNativePublicProfile_after_record G initial profile record
      have hbehavior :
          G.toNative.afterPublicHistory
              (G.toNative.toBehaviorProfile initial publicProfile) [record] =
            G.toNative.toBehaviorProfile target
              (toNativePublicProfile G target
                (G.shiftProfile profile (initial, actions))) := by
        rw [← G.toNative.toBehaviorProfile_after publicProfile [record],
          hpublic]
      unfold Stochastic.Game.restartHistoryLaw
      rw [hbehavior]
      apply congrArg (FinDist.map
        (fun continuation => continuation ++ [record]))
      simpa only [toNativeBehaviorProfile] using
        ih (G.shiftProfile profile (initial, actions)) target

/-- Predraw the translated proof-view profile at every counterfactual public
history through `horizon`. Unlike a bare existence result, this is the explicit
mixed public-policy witness supplied by bounded stochastic Kuhn correspondence.
-/
def toNativeMixedPublicProfile (profile : G.BehaviorProfile)
    (initial : G.State) (horizon : ℕ) : G.toNative.MixedPublicProfile := by
  letI (i : ι) : Fintype (G.Act i) := Fintype.ofFinite (G.Act i)
  exact fun i =>
    Stochastic.Game.PublicPolicy.toMixed G.toNative initial horizon
      (toNativePublicProfile G initial profile i)

/-- The explicit bounded mixed public profile has exactly the translated
proof-view behavioral history law. -/
theorem nativeMixedPublicProfile_play_eq_toNativeBehaviorProfile
    (profile : G.BehaviorProfile) (initial : G.State) (horizon : ℕ) :
    ((G.toNative.pureHorizonForm initial horizon).mixed).play
        (toNativeMixedPublicProfile G profile initial horizon) =
      (G.toNative.perfectMonitoring initial).runBehavioral
        (toNativeBehaviorProfile G initial profile) horizon := by
  letI (i : ι) : Fintype (G.Act i) := Fintype.ofFinite (G.Act i)
  unfold toNativeMixedPublicProfile
  rw [G.toNative.kuhn_behavioral_to_mixed initial
    (toNativePublicProfile G initial profile) horizon]
  exact G.toNative.publicHorizonForm_play initial horizon
    (toNativePublicProfile G initial profile)

/-- Relabel the explicit mixed public profile as Protocol's certified mixed
policies, without changing its induced bounded law. -/
def toNativeMixedProfile (profile : G.BehaviorProfile)
    (initial : G.State) (horizon : ℕ) :
    (i : ι) → (G.toNative.perfectMonitoring initial).MixedPolicy i :=
  fun i => FinDist.map (G.toNative.purePolicyEquiv initial i).symm
    (toNativeMixedPublicProfile G profile initial horizon i)

/-- The explicit certified mixed profile has exactly the translated
proof-view behavioral history law. -/
theorem nativeMixed_runMixed_eq_toNativeBehaviorProfile
    (profile : G.BehaviorProfile) (initial : G.State) (horizon : ℕ) :
    (G.toNative.perfectMonitoring initial).runMixed
        (toNativeMixedProfile G profile initial horizon) horizon =
      (G.toNative.perfectMonitoring initial).runBehavioral
        (toNativeBehaviorProfile G initial profile) horizon := by
  letI (i : ι) : Fintype (G.Act i) := Fintype.ofFinite (G.Act i)
  calc
    (G.toNative.perfectMonitoring initial).runMixed
          (toNativeMixedProfile G profile initial horizon) horizon =
        ((G.toNative.pureHorizonForm initial horizon).mixed).play
          (toNativeMixedPublicProfile G profile initial horizon) := by
      exact (GameTheory.mixed_relabelStrategies_play
        ((G.toNative.perfectMonitoring initial).toGameForm horizon)
        (G.toNative.purePolicyEquiv initial)
        (toNativeMixedPublicProfile G profile initial horizon)).symm
    _ = _ := nativeMixedPublicProfile_play_eq_toNativeBehaviorProfile
      G profile initial horizon

/-- Every bounded proof-view behavioral run has an exactly equivalent native
mixed contingent-policy run. The mixed witness is profile- and horizon-local;
this does not supply one mixed profile valid at all large horizons. -/
theorem exists_nativeMixed_runMixed_eq_toNativeBehaviorProfile
    (profile : G.BehaviorProfile) (initial : G.State) (horizon : ℕ) :
    ∃ mixed : (i : ι) →
        (G.toNative.perfectMonitoring initial).MixedPolicy i,
      (G.toNative.perfectMonitoring initial).runMixed mixed horizon =
        (G.toNative.perfectMonitoring initial).runBehavioral
          (toNativeBehaviorProfile G initial profile) horizon := by
  exact ⟨toNativeMixedProfile G profile initial horizon,
    nativeMixed_runMixed_eq_toNativeBehaviorProfile
      G profile initial horizon⟩

/-- Projecting the explicit bounded mixed witness to public histories recovers
the proof view's compiled public-history law exactly. -/
theorem nativeMixed_publicHistoryLaw_eq_compiled
    (profile : G.BehaviorProfile) (initial : G.State) (horizon : ℕ) :
    FinDist.map
        (fun history => G.toNative.publicHistoryOfTrace initial history.trace)
        ((G.toNative.perfectMonitoring initial).runMixed
          (toNativeMixedProfile G profile initial horizon) horizon) =
      compiledPublicHistoryLaw G profile initial horizon := by
  rw [nativeMixed_runMixed_eq_toNativeBehaviorProfile]
  exact native_publicHistoryLaw_eq_compiled G profile initial horizon

/-- The bounded mixed witness also realizes the proof view's compiled public
history law exactly. -/
theorem exists_nativeMixed_publicHistoryLaw_eq_compiled
    (profile : G.BehaviorProfile) (initial : G.State) (horizon : ℕ) :
    ∃ mixed : (i : ι) →
        (G.toNative.perfectMonitoring initial).MixedPolicy i,
      FinDist.map
          (fun history =>
            G.toNative.publicHistoryOfTrace initial history.trace)
          ((G.toNative.perfectMonitoring initial).runMixed mixed horizon) =
        compiledPublicHistoryLaw G profile initial horizon := by
  exact ⟨toNativeMixedProfile G profile initial horizon,
    nativeMixed_publicHistoryLaw_eq_compiled G profile initial horizon⟩

/-- Total proof-view payoff read from a native public history. -/
def publicHistoryTotalPayoff (history : G.toNative.PublicHistory)
    (who : ι) : ℝ :=
  (history.map fun record =>
    G.stagePayoff record.source record.joint who).sum

omit [Fintype ι] [∀ i, Finite (G.Act i)] [∀ i, Nonempty (G.Act i)] in
@[simp]
theorem publicHistoryTotalPayoff_nil (who : ι) :
    publicHistoryTotalPayoff G [] who = 0 :=
  rfl

omit [Fintype ι] [∀ i, Finite (G.Act i)] [∀ i, Nonempty (G.Act i)] in
@[simp]
theorem publicHistoryTotalPayoff_append_singleton
    (history : G.toNative.PublicHistory) (record : G.toNative.StageRecord)
    (who : ι) :
    publicHistoryTotalPayoff G (history ++ [record]) who =
      publicHistoryTotalPayoff G history who +
        G.stagePayoff record.source record.joint who := by
  simp [publicHistoryTotalPayoff]

omit [∀ i, Nonempty (G.Act i)] in
/-- The compiled native law and the indexed PMF law have identical expected
total payoffs at every horizon. -/
theorem expect_compiledPublicHistoryLaw_totalPayoff_eq
    (profile : G.BehaviorProfile) (initial : G.State) (who : ι) :
    ∀ horizon,
      FinDist.expect (compiledPublicHistoryLaw G profile initial horizon)
          (fun history => publicHistoryTotalPayoff G history who) =
        _root_.Math.Probability.expect (G.histDist profile initial horizon)
          (fun history => G.totalPayoff who history) := by
  intro horizon
  induction horizon generalizing profile initial with
  | zero =>
      simp [compiledPublicHistoryLaw, G.histDist_zero,
        publicHistoryTotalPayoff]
  | succ horizon ih =>
      rw [compiledPublicHistoryLaw_succ]
      simp only [FinDist.bindOnSupport_eq_bind]
      rw [FinDist.expect_bind]
      simp only [FinDist.expect_bind, FinDist.expect_map,
        publicHistoryTotalPayoff_append_singleton]
      rw [G.histDist_succ_shift profile initial horizon]
      rw [_root_.Math.Probability.expect_bind]
      change _root_.Math.Probability.expect
          (G.stageActionDist profile (G.emptyHist initial)) _ =
        _root_.Math.Probability.expect
          (G.stageActionDist profile (G.emptyHist initial)) _
      apply congrArg (_root_.Math.Probability.expect
        (G.stageActionDist profile (G.emptyHist initial)))
      funext actions
      rw [_root_.Math.Probability.expect_bind]
      change _root_.Math.Probability.expect (G.transition initial actions) _ =
        _root_.Math.Probability.expect (G.transition initial actions) _
      apply congrArg (_root_.Math.Probability.expect
        (G.transition initial actions))
      funext target
      rw [_root_.Math.Probability.expect_map]
      simp_rw [G.totalPayoff_consHist]
      rw [FinDist.expect_add, FinDist.expect_const, ih,
        _root_.Math.Probability.expect_add,
        _root_.Math.Probability.expect_const]
      ac_rfl

/-- The payoff of the latest stage in a reverse-chronological native public
history.  The empty branch only totalizes the observable off support. -/
def publicHistoryLatestPayoff (history : G.toNative.PublicHistory)
    (who : ι) : ℝ :=
  match history with
  | [] => 0
  | record :: _ => G.stagePayoff record.source record.joint who

omit [Fintype ι] [∀ i, Finite (G.Act i)]
  [∀ i, Nonempty (G.Act i)] in
@[simp]
theorem publicHistoryLatestPayoff_nil (who : ι) :
    publicHistoryLatestPayoff G [] who = 0 :=
  rfl

omit [Fintype ι] [∀ i, Finite (G.Act i)]
  [∀ i, Nonempty (G.Act i)] in
@[simp]
theorem publicHistoryLatestPayoff_singleton
    (record : G.toNative.StageRecord) (who : ι) :
    publicHistoryLatestPayoff G [record] who =
      G.stagePayoff record.source record.joint who :=
  rfl

omit [Fintype ι] [∀ i, Finite (G.Act i)]
  [∀ i, Nonempty (G.Act i)] in
theorem publicHistoryLatestPayoff_append_singleton_of_ne_nil
    (history : G.toNative.PublicHistory) (record : G.toNative.StageRecord)
    (who : ι) (hhistory : history ≠ []) :
    publicHistoryLatestPayoff G (history ++ [record]) who =
      publicHistoryLatestPayoff G history who := by
  cases history with
  | nil => exact (hhistory rfl).elim
  | cons head tail => rfl

/-- The latest-stage observable on the compiled native prefix is exactly the
proof view's expected payoff at that stage. -/
theorem expect_compiledPublicHistoryLaw_latestPayoff_eq
    (profile : G.BehaviorProfile) (initial : G.State) (who : ι) :
    ∀ time,
      FinDist.expect (compiledPublicHistoryLaw G profile initial (time + 1))
          (fun history => publicHistoryLatestPayoff G history who) =
        G.expectedStagePayoff profile initial time who := by
  intro time
  induction time generalizing profile initial with
  | zero =>
      rw [compiledPublicHistoryLaw_succ]
      simp only [FinDist.bindOnSupport_eq_bind, FinDist.expect_bind,
        FinDist.expect_map, compiledPublicHistoryLaw_zero,
        FinDist.expect_pure, List.nil_append,
        publicHistoryLatestPayoff_singleton,
        _root_.Math.Probability.expect_finDistOfPMF,
        _root_.Math.Probability.expect_const]
      rw [G.expectedStagePayoff_zero]
      rfl
  | succ time ih =>
      rw [compiledPublicHistoryLaw_succ]
      simp only [FinDist.bindOnSupport_eq_bind, FinDist.expect_bind,
        FinDist.expect_map]
      rw [G.expectedStagePayoff_succ_shift]
      change _root_.Math.Probability.expect
          (G.stageActionDist profile (G.emptyHist initial)) _ =
        _root_.Math.Probability.expect
          (G.stageActionDist profile (G.emptyHist initial)) _
      apply congrArg (_root_.Math.Probability.expect
        (G.stageActionDist profile (G.emptyHist initial)))
      funext actions
      rw [_root_.Math.Probability.expect_finDistOfPMF]
      apply congrArg (_root_.Math.Probability.expect
        (G.transition initial actions))
      funext target
      let continuation := compiledPublicHistoryLaw G
        (G.shiftProfile profile (initial, actions)) target (time + 1)
      have hpointwise : ∀ history ∈ continuation.support,
          publicHistoryLatestPayoff G
              (history ++ [{
                source := initial
                joint := actions
                target := target }]) who =
            publicHistoryLatestPayoff G history who := by
        intro history hhistory
        apply publicHistoryLatestPayoff_append_singleton_of_ne_nil
        intro hempty
        subst history
        have hnative := native_publicHistoryLaw_eq_compiled G
          (G.shiftProfile profile (initial, actions)) target (time + 1)
        have hmem : [] ∈ (G.toNative.publicHistoryLaw target
            (G.toNative.toBehaviorProfile target
              (toNativePublicProfile G target
                (G.shiftProfile profile (initial, actions))))
            (time + 1)).support := by
          change [] ∈ (G.toNative.publicHistoryLaw target
            (toNativeBehaviorProfile G target
              (G.shiftProfile profile (initial, actions)))
            (time + 1)).support
          rw [hnative]
          exact hhistory
        have hlength := G.toNative.length_eq_of_mem_support_publicHistoryLaw
          target
          (G.toNative.toBehaviorProfile target
            (toNativePublicProfile G target
              (G.shiftProfile profile (initial, actions))))
          (time + 1) hmem
        simp at hlength
      rw [FinDist.expect_congr hpointwise]
      exact ih (G.shiftProfile profile (initial, actions)) target

/-- Native finite-prefix stage expectation is exactly the proof-view expected
stage payoff under compilation. -/
theorem native_behavioralStageExpectation_eq
    (profile : G.BehaviorProfile) (initial : G.State)
    [MeasurableSpace (G.toNative.toExecution initial).History]
    [DiscreteMeasurableSpace (G.toNative.toExecution initial).History]
    [MeasurableSingletonClass (G.toNative.toExecution initial).History]
    (who : ι) (time : ℕ) :
    G.toNative.behavioralStageExpectation initial
        (toNativePublicProfile G initial profile) who time =
      G.expectedStagePayoff profile initial time who := by
  classical
  let run := (G.toNative.perfectMonitoring initial).runBehavioral
    (toNativeBehaviorProfile G initial profile) (time + 1)
  obtain ⟨bound, hbound⟩ :=
    _root_.Math.Probability.exists_abs_bound_of_finite
      (fun x : G.State × G.JointAct =>
        G.stagePayoff x.1 x.2 who)
  have hlatest : ∀ history : (G.toNative.toExecution initial).History,
      ‖G.toNative.latestStageUtility initial who history‖ ≤ bound := by
    intro history
    rw [Real.norm_eq_abs]
    apply G.toNative.abs_latestStageUtility_le initial who bound
    intro state actions
    exact hbound (state, actions)
  unfold Stochastic.Game.behavioralStageExpectation
    Protocol.InformationModel.behavioralPrefixExpectation
  change (∫ history,
      G.toNative.latestStageUtility initial who history ∂run.toMeasure) = _
  rw [FinDist.integral_toMeasure_eq_expect_of_bound run _ hlatest]
  have hobservable : G.toNative.latestStageUtility initial who =
      fun history => publicHistoryLatestPayoff G
        (G.toNative.publicHistoryOfTrace initial history.trace) who := by
    funext history
    unfold Stochastic.Game.latestStageUtility publicHistoryLatestPayoff
    generalize hhistory :
      G.toNative.publicHistoryOfTrace initial history.trace = publicHistory
    cases publicHistory with
    | nil => rfl
    | cons record tail =>
        unfold Stochastic.Game.stageRecordUtility
        rfl
  rw [hobservable]
  change run.expect (fun history =>
      publicHistoryLatestPayoff G
        (G.toNative.publicHistoryOfTrace initial history.trace) who) = _
  rw [← FinDist.expect_map
    (f := fun history =>
      G.toNative.publicHistoryOfTrace initial history.trace)
    (μ := run)
    (u := fun history => publicHistoryLatestPayoff G history who)]
  change (G.toNative.publicHistoryLaw initial
      (toNativeBehaviorProfile G initial profile) (time + 1)).expect
        (fun history => publicHistoryLatestPayoff G history who) = _
  rw [native_publicHistoryLaw_eq_compiled]
  exact expect_compiledPublicHistoryLaw_latestPayoff_eq
    G profile initial who time

/-- Native and proof-view normalized discounted payoffs agree exactly under
compilation. -/
theorem native_behavioralDiscountedPayoff_eq
    (profile : G.BehaviorProfile) (initial : G.State)
    [MeasurableSpace (G.toNative.toExecution initial).History]
    [DiscreteMeasurableSpace (G.toNative.toExecution initial).History]
    [MeasurableSingletonClass (G.toNative.toExecution initial).History]
    (discount : ℝ) (who : ι) :
    G.toNative.behavioralDiscountedPayoff initial discount
        (toNativePublicProfile G initial profile) who =
      G.discountedPayoff discount profile initial who := by
  unfold Stochastic.Game.behavioralDiscountedPayoff
    StochasticGame.discountedPayoff
    GameTheory.Math.normalizedDiscountedSum
  congr 2
  funext time
  rw [native_behavioralStageExpectation_eq]

/-- Finite-average payoff is preserved exactly by compilation to
GameTheory's canonical behavioral runner. -/
theorem native_finiteAveragePayoff_eq
    (profile : G.BehaviorProfile) (initial : G.State)
    (horizon : ℕ) (who : ι) :
    G.toNative.finiteAveragePayoff initial horizon
        (toNativeBehaviorProfile G initial profile) who =
      G.finiteAveragePayoff initial horizon profile who := by
  rw [← G.toNative.publicFiniteAveragePayoff_eq_finiteAveragePayoff]
  unfold Stochastic.Game.publicFiniteAveragePayoff expectedUtility
  rw [native_publicHistoryLaw_eq_compiled]
  change FinDist.expect (compiledPublicHistoryLaw G profile initial horizon)
      (fun history => (horizon : ℝ)⁻¹ *
        publicHistoryTotalPayoff G history who) = _
  have hcommute :
      (fun history : G.toNative.PublicHistory =>
          (horizon : ℝ)⁻¹ * publicHistoryTotalPayoff G history who) =
        fun history =>
          publicHistoryTotalPayoff G history who * (horizon : ℝ)⁻¹ := by
    funext history
    ring
  rw [hcommute, FinDist.expect_mul_const,
    expect_compiledPublicHistoryLaw_totalPayoff_eq]
  unfold StochasticGame.finiteAveragePayoff
  ring

/-- Agreement on the public histories actually exposed by one bounded
proof-view run is enough for exact agreement of the canonical Protocol laws.
No agreement is required at unsupported counterfactual histories. -/
theorem native_runBehavioral_eq_of_support_agreement
    (initial : G.State) (proofProfile : G.BehaviorProfile)
    (nativeProfile : G.toNative.PublicProfile initial)
    (horizon : ℕ)
    (hagree : ∀ elapsed, elapsed ≤ horizon → ∀ later,
      later ∈ ((G.toNative.perfectMonitoring initial).runBehavioralFrom
        (toNativeBehaviorProfile G initial proofProfile) elapsed
        (G.toNative.toExecution initial).initHistory).support →
      ∀ i,
        toNativePublicProfile G initial proofProfile i
            (G.toNative.publicHistoryOfTrace initial later.trace) =
          nativeProfile i
            (G.toNative.publicHistoryOfTrace initial later.trace)) :
    (G.toNative.perfectMonitoring initial).runBehavioral
        (toNativeBehaviorProfile G initial proofProfile) horizon =
      (G.toNative.perfectMonitoring initial).runBehavioral
        (G.toNative.toBehaviorProfile initial nativeProfile) horizon := by
  unfold InformationModel.runBehavioral
  apply InformationModel.runBehavioralFrom_congr_on_support
  intro elapsed helapsed history hhistory _ i
  rw [G.toNative.perfectMonitoring_infoOf_eq_publicHistoryOfTrace]
  unfold toNativeBehaviorProfile Stochastic.Game.toBehaviorProfile
    Stochastic.Game.toBehavioralPolicy
  apply congrArg (FinDist.map
    (G.toNative.actionChoiceEquiv initial i
      (G.toNative.publicHistoryOfTrace initial history.trace)))
  exact hagree elapsed helapsed history hhistory i

/-- Coherent-history agreement with a proof-view profile is enough for exact
agreement of the canonical Protocol laws. -/
theorem native_runBehavioral_eq_of_coherent
    (initial : G.State) (proofProfile : G.BehaviorProfile)
    (nativeProfile : G.toNative.PublicProfile initial)
    (horizon : ℕ)
    (hagree : ∀ i history, IsCoherentPublicHistory G initial history →
      toNativePublicProfile G initial proofProfile i history =
        nativeProfile i history) :
    (G.toNative.perfectMonitoring initial).runBehavioral
        (toNativeBehaviorProfile G initial proofProfile) horizon =
      (G.toNative.perfectMonitoring initial).runBehavioral
        (G.toNative.toBehaviorProfile initial nativeProfile) horizon := by
  apply native_runBehavioral_eq_of_support_agreement
  intro _ _ history _ i
  exact hagree i _
    (isCoherentPublicHistory_publicHistoryOfTrace G initial history.trace)

/-- A native public profile and its proof-view round trip induce the same
canonical Protocol history law. -/
theorem native_runBehavioral_roundtrip
    (initial : G.State) (profile : G.toNative.PublicProfile initial)
    (horizon : ℕ) :
    (G.toNative.perfectMonitoring initial).runBehavioral
        (toNativeBehaviorProfile G initial
          (ofNativePublicProfile G initial profile)) horizon =
      (G.toNative.perfectMonitoring initial).runBehavioral
        (G.toNative.toBehaviorProfile initial profile) horizon := by
  apply native_runBehavioral_eq_of_coherent
  exact fun i history hcoherent =>
    toNativePublicProfile_ofNativePublicProfile_of_coherent
      G initial profile i history hcoherent

/-- Every native public profile has the same finite-prefix stage expectation
as its decoded proof-view profile. -/
theorem native_behavioralStageExpectation_eq_of_publicProfile
    (initial : G.State) (profile : G.toNative.PublicProfile initial)
    [MeasurableSpace (G.toNative.toExecution initial).History]
    [DiscreteMeasurableSpace (G.toNative.toExecution initial).History]
    [MeasurableSingletonClass (G.toNative.toExecution initial).History]
    (who : ι) (time : ℕ) :
    G.toNative.behavioralStageExpectation initial profile who time =
      G.expectedStagePayoff
        (ofNativePublicProfile G initial profile) initial time who := by
  rw [← native_behavioralStageExpectation_eq G
    (ofNativePublicProfile G initial profile) initial who time]
  unfold Stochastic.Game.behavioralStageExpectation
    Protocol.InformationModel.behavioralPrefixExpectation
  rw [← native_runBehavioral_roundtrip G initial profile (time + 1)]
  rfl

/-- Every native public profile has exactly the discounted payoff of its
decoded proof-view profile. -/
theorem native_behavioralDiscountedPayoff_eq_of_publicProfile
    (initial : G.State) (profile : G.toNative.PublicProfile initial)
    [MeasurableSpace (G.toNative.toExecution initial).History]
    [DiscreteMeasurableSpace (G.toNative.toExecution initial).History]
    [MeasurableSingletonClass (G.toNative.toExecution initial).History]
    (discount : ℝ) (who : ι) :
    G.toNative.behavioralDiscountedPayoff initial discount profile who =
      G.discountedPayoff discount
        (ofNativePublicProfile G initial profile) initial who := by
  unfold Stochastic.Game.behavioralDiscountedPayoff
    StochasticGame.discountedPayoff
    GameTheory.Math.normalizedDiscountedSum
  congr 2
  funext time
  rw [native_behavioralStageExpectation_eq_of_publicProfile]

/-- A native public profile and a proof-view profile that agree on coherent
histories have exactly the same normalized discounted payoff. -/
theorem native_behavioralDiscountedPayoff_eq_of_coherent
    (initial : G.State) (proofProfile : G.BehaviorProfile)
    (nativeProfile : G.toNative.PublicProfile initial)
    (hagree : ∀ i history, IsCoherentPublicHistory G initial history →
      toNativePublicProfile G initial proofProfile i history =
        nativeProfile i history)
    [MeasurableSpace (G.toNative.toExecution initial).History]
    [DiscreteMeasurableSpace (G.toNative.toExecution initial).History]
    [MeasurableSingletonClass (G.toNative.toExecution initial).History]
    (discount : ℝ) (who : ι) :
    G.toNative.behavioralDiscountedPayoff initial discount nativeProfile who =
      G.discountedPayoff discount proofProfile initial who := by
  rw [← native_behavioralDiscountedPayoff_eq G proofProfile initial
    discount who]
  unfold Stochastic.Game.behavioralDiscountedPayoff
    GameTheory.Math.normalizedDiscountedSum
  congr 2
  funext time
  unfold Stochastic.Game.behavioralStageExpectation
    Protocol.InformationModel.behavioralPrefixExpectation
  rw [← native_runBehavioral_eq_of_coherent G initial proofProfile
    nativeProfile (time + 1) hagree]
  rfl

/-- A native public profile and a proof-view profile that agree on coherent
histories have exactly the same finite-average payoff. -/
theorem native_finiteAveragePayoff_eq_of_coherent
    (initial : G.State) (proofProfile : G.BehaviorProfile)
    (nativeProfile : G.toNative.PublicProfile initial)
    (hagree : ∀ i history, IsCoherentPublicHistory G initial history →
      toNativePublicProfile G initial proofProfile i history =
        nativeProfile i history)
    (horizon : ℕ) (who : ι) :
    G.toNative.finiteAveragePayoff initial horizon
        (G.toNative.toBehaviorProfile initial nativeProfile) who =
      G.finiteAveragePayoff initial horizon proofProfile who := by
  rw [← native_finiteAveragePayoff_eq G proofProfile initial horizon who]
  unfold Stochastic.Game.finiteAveragePayoff
  rw [G.toNative.horizonForm_play, G.toNative.horizonForm_play]
  rw [native_runBehavioral_eq_of_coherent G initial proofProfile
    nativeProfile horizon hagree]

/-- Every native public profile has exactly the finite-average payoff of its
decoded PMF proof-view profile. -/
theorem native_finiteAveragePayoff_eq_of_publicProfile
    (initial : G.State) (profile : G.toNative.PublicProfile initial)
    (horizon : ℕ) (who : ι) :
    G.toNative.finiteAveragePayoff initial horizon
        (G.toNative.toBehaviorProfile initial profile) who =
      G.finiteAveragePayoff initial horizon
        (ofNativePublicProfile G initial profile) who := by
  rw [← native_finiteAveragePayoff_eq G
    (ofNativePublicProfile G initial profile) initial horizon who]
  unfold Stochastic.Game.finiteAveragePayoff
  rw [G.toNative.horizonForm_play, G.toNative.horizonForm_play]
  rw [native_runBehavioral_roundtrip]

end StochasticGame.NativeBridge

end GameTheory
