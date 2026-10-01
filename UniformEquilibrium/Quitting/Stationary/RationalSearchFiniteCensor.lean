import UniformEquilibrium.Quitting.Stationary.RationalGridSearch
import UniformEquilibrium.Quitting.Stationary.FiniteCensorCutoff
import UniformEquilibrium.Quitting.Stationary.GuardedCrossedResponseHalfCeilingProducer

/-! # Actual finite laws from accuracy-only rational stationary search

The selector uses half the requested rational regret tolerance. Its actual
contracting root supplies the deleted-opponent survival rate; a logarithmic
cutoff makes censoring consume at most the other half. Delivery is to the
selected stationary profile's actual payoff, which may change with accuracy.
No prescribed fixed target, executable logarithmic cutoff, search complexity
bound, or game-wide equilibrium-existence test is asserted.
-/

noncomputable section

namespace GameTheory

variable {n : ℕ}

/-- Censoring budget, truncated only to meet the scalar cutoff's unit-tolerance premise. -/
def rationalQuittingSearchCensorTolerance (accuracy : ℚ) (M : ℝ) : ℝ :=
  min ((accuracy : ℝ) / 2) (3 * M)

/-- The derived date count uses the actual root returned by the rational search. -/
def rationalQuittingSearchCensorDeadline (reward : RationalQuittingReward n)
    (accuracy : ℚ) (M : ℝ)
    (hsuccess : ∃ budget,
      (rationalQuittingStationaryBoundedSearch? reward (accuracy / 2) budget).isSome = true) :
    ℕ :=
  Math.powerLogCutoff
    (quittingStationaryDeletedSurvivalMax
      (rationalQuittingStationarySearchSelector reward (accuracy / 2) hsuccess).toPMF)
    (rationalQuittingSearchCensorTolerance accuracy M / (3 * M))

/-- One independently mixed date/Never law per player, with the actual censored
geometric atoms, semantic pair, requested whole-behavioral regret, selected-value
delivery, and signed finite-horizon estimates. The successful search is named
only to identify exactly which source root and value the laws implement. -/
def RationalQuittingSearchFiniteCensorGuarantee (reward : RationalQuittingReward n)
    (accuracy : ℚ) (M : ℝ)
    (hsuccess : ∃ budget,
      (rationalQuittingStationaryBoundedSearch? reward (accuracy / 2) budget).isSome = true) :
    Prop :=
  let realReward := rationalQuittingRewardToReal reward
  let selected := rationalQuittingStationarySearchSelector reward (accuracy / 2) hsuccess
  let deadline := rationalQuittingSearchCensorDeadline reward accuracy M hsuccess
  0 < deadline ∧
    (deadline : ℝ) ≤ 1 +
      Math.survivalLogScale (quittingStationaryDeletedSurvivalMax selected.toPMF) *
        Real.log (3 * M / rationalQuittingSearchCensorTolerance accuracy M) ∧
    ∃ mixed : Fin n → PMF (QuittingFiniteDeadlineTimingAction deadline),
      (∀ who, (quittingFiniteDeadlineTimingLaw (mixed who)).toPMF =
        _root_.Math.Probability.censorLateFiniteStoppingLaw
          (quittingBehaviorStoppingLaw realReward
            (quittingStationaryProfile realReward selected.toPMF who)) (deadline - 1)) ∧
      quittingTerminalSemanticPair realReward
          (quittingFiniteDeadlineTimingProfile realReward deadline mixed) =
        quittingTerminalSemanticPair realReward
          (quittingStationaryFiniteCensorProfile realReward selected.toPMF deadline) ∧
      (∀ who time, time < deadline →
        ((quittingFiniteDeadlineTimingLaw (mixed who)).toPMF (some time)).toReal =
          (selected.toPMF who true).toReal * (selected.toPMF who false).toReal ^ time) ∧
      (∀ who, (mixed who none).toReal = (selected.toPMF who false).toReal ^ deadline) ∧
      (∀ who, quittingTerminalPayoff realReward
          (quittingFiniteDeadlineTimingProfile realReward deadline mixed) who =
        (1 - quittingStationaryContinueMass selected.toPMF ^ deadline) *
          quittingTerminalPayoff realReward
            (quittingStationaryProfile realReward selected.toPMF) who) ∧
      (quittingGame realReward).IsεAsymptoticNash (quittingTerminalPayoff realReward)
        (accuracy : ℝ) (quittingFiniteDeadlineTimingProfile realReward deadline mixed) ∧
      (∀ who, |quittingTerminalPayoff realReward
          (quittingFiniteDeadlineTimingProfile realReward deadline mixed) who -
        quittingTerminalPayoff realReward
          (quittingStationaryProfile realReward selected.toPMF) who| ≤ (accuracy : ℝ) / 6) ∧
      ∀ horizon, 0 < horizon →
        (quittingGame realReward).IsεHorizonNash none horizon
          ((accuracy : ℝ) + 2 * M * (deadline + 1) / horizon)
          (quittingFiniteDeadlineTimingProfile realReward deadline mixed) ∧
        ∀ who, |(quittingGame realReward).finiteAveragePayoff none horizon
            (quittingFiniteDeadlineTimingProfile realReward deadline mixed) who -
          quittingTerminalPayoff realReward
            (quittingStationaryProfile realReward selected.toPMF) who| ≤
              (accuracy : ℝ) / 6 + M * (deadline + 1) / horizon

/-- Accepted rational search and the canonical approximate-Nash censor compose
without supplying a real root, a unilateral-cap certificate, or a target value. -/
theorem rationalQuittingSearchFiniteCensorGuarantee_of_success
    (reward : RationalQuittingReward n) (accuracy : ℚ) (haccuracy : 0 < accuracy)
    {M : ℝ} (hM : 0 < M)
    (hreward : ∀ terminal who, |rationalQuittingRewardToReal reward terminal who| ≤ M)
    (hsuccess : ∃ budget,
      (rationalQuittingStationaryBoundedSearch? reward (accuracy / 2) budget).isSome = true) :
    RationalQuittingSearchFiniteCensorGuarantee reward accuracy M hsuccess := by
  let selected := rationalQuittingStationarySearchSelector reward (accuracy / 2) hsuccess
  let tolerance := rationalQuittingSearchCensorTolerance accuracy M
  let deadline := rationalQuittingSearchCensorDeadline reward accuracy M hsuccess
  have haccuracyReal : 0 < (accuracy : ℝ) := by exact_mod_cast haccuracy
  have htolerance : 0 < tolerance := lt_min (by positivity) (by positivity)
  have htoleranceSmall : tolerance ≤ 3 * M := min_le_right _ _
  have htoleranceHalf : tolerance ≤ (accuracy : ℝ) / 2 := min_le_left _ _
  have hhalf : ((accuracy / 2 : ℚ) : ℝ) = (accuracy : ℝ) / 2 := by norm_num
  obtain ⟨hcontracts, hnash⟩ := rationalQuittingStationarySearchSelector_spec
    reward (accuracy / 2) hsuccess
  obtain ⟨hdeadline, hregret, hdelivery, hlength⟩ :=
    stationaryFiniteCensor_logCutoff_bounds selected.toPMF hcontracts
      htolerance htoleranceSmall
  change 0 < deadline at hdeadline
  change 3 * M * quittingStationaryDeletedSurvivalMax selected.toPMF ^ deadline ≤
    tolerance at hregret
  change M * quittingStationaryDeletedSurvivalMax selected.toPMF ^ deadline ≤
    tolerance / 3 at hdelivery
  change (deadline : ℝ) ≤ 1 +
    Math.survivalLogScale (quittingStationaryDeletedSurvivalMax selected.toPMF) *
      Real.log (3 * M / tolerance) at hlength
  obtain ⟨_, mixed, hlaws, hpair, hatoms, hnever, hpay, hterminal, htarget, hhorizon⟩ :=
    exists_stationaryFiniteCensorTimingProfile_of_approximateNash
      (rationalQuittingRewardToReal reward) selected.toPMF deadline hdeadline
      hreward hnash hcontracts
  have htotal : ((accuracy / 2 : ℚ) : ℝ) +
      3 * M * quittingStationaryDeletedSurvivalMax selected.toPMF ^ deadline ≤
        (accuracy : ℝ) := by
    rw [hhalf]
    linarith
  have htargetBound : M * quittingStationaryDeletedSurvivalMax selected.toPMF ^ deadline ≤
      (accuracy : ℝ) / 6 := by
    linarith
  refine ⟨hdeadline, hlength, mixed, hlaws, hpair, hatoms, hnever, hpay, ?_, ?_, ?_⟩
  · intro who deviation
    exact (hterminal who deviation).trans (_root_.add_le_add le_rfl htotal)
  · intro who
    exact (htarget who).trans htargetBound
  · intro horizon hpositive
    obtain ⟨hnashH, htargetH⟩ := hhorizon horizon hpositive
    constructor
    · intro who deviation
      exact (hnashH who deviation).trans
        (_root_.add_le_add le_rfl (_root_.add_le_add htotal le_rfl))
    · intro who
      exact (htargetH who).trans (_root_.add_le_add htargetBound le_rfl)

/-- Theorem A's actual guarded source supplies success internally. The real height
is auxiliary; no selected equilibrium root or favorable degree equality is supplied. -/
theorem exists_rationalQuittingSearchFiniteCensor_of_sourceGuards
    (reward : RationalQuittingReward n) (first second : Fin n) (hdistinct : first ≠ second)
    (height : ℝ) (hheight : 0 < height) (hheightOne : height ≤ 1)
    (hguard : QuittingCrossedSourceGuards
      (rationalQuittingRewardToReal reward) first second height)
    (hreciprocalFirst : 0 < QuittingLCPClassification.quittingSingletonMatrix
      (rationalQuittingRewardToReal reward) first second)
    (hreciprocalSecond : 0 < QuittingLCPClassification.quittingSingletonMatrix
      (rationalQuittingRewardToReal reward) second first)
    (hR0 : Math.LinearProgramming.IsR0Matrix (quittingCrossedSingletonMatrix
      (rationalQuittingRewardToReal reward) first second))
    (hdegree : Math.LinearProgramming.r0Degree (quittingCrossedSingletonMatrix
      (rationalQuittingRewardToReal reward) first second) hR0 ≠ 1)
    (accuracy : ℚ) (haccuracy : 0 < accuracy) {M : ℝ} (hM : 0 < M)
    (hreward : ∀ terminal who, |rationalQuittingRewardToReal reward terminal who| ≤ M) :
    ∃ hsuccess : ∃ budget,
      (rationalQuittingStationaryBoundedSearch? reward (accuracy / 2) budget).isSome = true,
      RationalQuittingSearchFiniteCensorGuarantee reward accuracy M hsuccess := by
  obtain ⟨threshold, hthreshold⟩ :=
    rationalQuittingStationaryBoundedSearch_eventually_succeeds_of_sourceGuards
      reward first second hdistinct height hheight hheightOne hguard
      hreciprocalFirst hreciprocalSecond hR0 hdegree (accuracy / 2) (by positivity)
  let hsuccess : ∃ budget,
      (rationalQuittingStationaryBoundedSearch? reward (accuracy / 2) budget).isSome = true :=
    ⟨threshold, hthreshold threshold le_rfl⟩
  exact ⟨hsuccess, rationalQuittingSearchFiniteCensorGuarantee_of_success
    reward accuracy haccuracy hM hreward hsuccess⟩

/-- The unit raw-table producer derives the needed real root and degree escape;
the finite laws implement the rational selector, not that auxiliary real root. -/
theorem exists_rationalQuittingSearchFiniteCensor_of_strictRawUnit
    (reward : RationalQuittingReward n) (first second : Fin n) (hdistinct : first ≠ second)
    (hdet : 0 < (QuittingLCPClassification.quittingSingletonMatrix
      (rationalQuittingRewardToReal reward)).det)
    (hinverse : ∀ row column, 0 < (QuittingLCPClassification.quittingSingletonMatrix
      (rationalQuittingRewardToReal reward))⁻¹ row column)
    (hraw : QuittingCrossedStrictRawUnitGuards
      (rationalQuittingRewardToReal reward) first second)
    (accuracy : ℚ) (haccuracy : 0 < accuracy) {M : ℝ} (hM : 0 < M)
    (hreward : ∀ terminal who, |rationalQuittingRewardToReal reward terminal who| ≤ M) :
    ∃ hsuccess : ∃ budget,
      (rationalQuittingStationaryBoundedSearch? reward (accuracy / 2) budget).isSome = true,
      RationalQuittingSearchFiniteCensorGuarantee reward accuracy M hsuccess := by
  obtain ⟨root, _, _, _, _, _, _, _, hcontracts, hnash, _⟩ :=
    exists_guardedCrossed_stationaryTerminalNash_uniformPayoff_of_strictRawUnit
      (rationalQuittingRewardToReal reward) first second hdistinct hdet hinverse hraw
  obtain ⟨threshold, hthreshold⟩ :=
    rationalQuittingStationaryBoundedSearch_eventually_succeeds_of_stationaryNash
      reward root hcontracts hnash (accuracy / 2) (by positivity)
  let hsuccess : ∃ budget,
      (rationalQuittingStationaryBoundedSearch? reward (accuracy / 2) budget).isSome = true :=
    ⟨threshold, hthreshold threshold le_rfl⟩
  exact ⟨hsuccess, rationalQuittingSearchFiniteCensorGuarantee_of_success
    reward accuracy haccuracy hM hreward hsuccess⟩

/-- The four-player half raw-table tests likewise supply search termination,
followed by the same actual finite-law compiler and requested regret bound. -/
theorem exists_rationalQuittingSearchFiniteCensor_of_halfStrictRaw
    (reward : RationalQuittingReward 4)
    (hdet : 0 < (QuittingLCPClassification.quittingSingletonMatrix
      (rationalQuittingRewardToReal reward)).det)
    (hinverse : ∀ row column, 0 < (QuittingLCPClassification.quittingSingletonMatrix
      (rationalQuittingRewardToReal reward))⁻¹ row column)
    (hraw : QuittingHalfStrictRawGuards (rationalQuittingRewardToReal reward))
    (accuracy : ℚ) (haccuracy : 0 < accuracy) {M : ℝ} (hM : 0 < M)
    (hreward : ∀ terminal who, |rationalQuittingRewardToReal reward terminal who| ≤ M) :
    ∃ hsuccess : ∃ budget,
      (rationalQuittingStationaryBoundedSearch? reward (accuracy / 2) budget).isSome = true,
      RationalQuittingSearchFiniteCensorGuarantee reward accuracy M hsuccess := by
  obtain ⟨root, _, _, _, _, _, _, _, hcontracts, hnash, _⟩ :=
    exists_guardedCrossed_stationaryTerminalNash_uniformPayoff_of_halfStrictRaw
      (rationalQuittingRewardToReal reward) hdet hinverse hraw
  obtain ⟨threshold, hthreshold⟩ :=
    rationalQuittingStationaryBoundedSearch_eventually_succeeds_of_stationaryNash
      reward root hcontracts hnash (accuracy / 2) (by positivity)
  let hsuccess : ∃ budget,
      (rationalQuittingStationaryBoundedSearch? reward (accuracy / 2) budget).isSome = true :=
    ⟨threshold, hthreshold threshold le_rfl⟩
  exact ⟨hsuccess, rationalQuittingSearchFiniteCensorGuarantee_of_success
    reward accuracy haccuracy hM hreward hsuccess⟩

end GameTheory
