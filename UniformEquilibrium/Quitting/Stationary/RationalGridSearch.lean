import MathUE.Interval.RationalCubeGrid
import UniformEquilibrium.Quitting.Stationary.RationalPayoffCap
import UniformEquilibrium.Quitting.Stationary.GuardedCrossedResponseStrategic
import Mathlib.Data.Nat.Find

/-! # Terminating accuracy-only rational stationary search

At each budget the executable search checks all common-denominator grids up to
that budget, using the exact rational full behavioral-cap test. A supplied actual
contracting stationary Nash root proves eventual success; guarded crossed source
data provide that root. The returned root need not approximate a prescribed real
payoff target. No complexity bound or equilibrium-existence test is asserted.
-/

namespace GameTheory

open GameTheory.Finite Filter
open scoped Topology

variable {n : ℕ}

/-- A point in the existing executable finite Boolean grid, as an actual rational root. -/
def rationalQuittingGridRoot (resolution : ℕ)
    (point : Fin n → Fin (resolution + 2)) : RationalQuittingRoot n where
  probability := rationalBooleanGridProbability resolution point
  nonnegative := fun who => (rationalBooleanGridProbability_mem_unitInterval
    resolution point who).1
  le_one := fun who => (rationalBooleanGridProbability_mem_unitInterval
    resolution point who).2

@[simp]
theorem hazardOfRoot_rationalQuittingGridRoot (resolution : ℕ)
    (point : Fin n → Fin (resolution + 2)) :
    hazardOfRoot (rationalQuittingGridRoot resolution point).toPMF =
      fun who => (rationalBooleanGridProbability resolution point who : ℝ) := by
  funext who
  simp [hazardOfRoot, rationalQuittingGridRoot]

/-- Literal finite enumeration, using the existing executable grid list. -/
def rationalQuittingStationaryGridCandidates (budget : ℕ) : List (RationalQuittingRoot n) :=
  (List.range (budget + 1)).flatMap fun resolution =>
    (rationalBooleanGridPoints n resolution).map (rationalQuittingGridRoot resolution)

/-- Exact accuracy-only search through all denominators at most `budget + 1`. -/
def rationalQuittingStationaryBoundedSearch? (reward : RationalQuittingReward n)
    (accuracy : ℚ) (budget : ℕ) : Option (RationalQuittingRoot n) :=
  (rationalQuittingStationaryGridCandidates budget).find?
    (fun root => rationalQuittingStationaryRegretAccepts reward root accuracy)

theorem mem_rationalQuittingStationaryGridCandidates (resolution budget : ℕ)
    (hbudget : resolution ≤ budget) (point : Fin n → Fin (resolution + 2)) :
    rationalQuittingGridRoot resolution point ∈
      rationalQuittingStationaryGridCandidates budget := by
  apply List.mem_flatMap.mpr
  refine ⟨resolution, List.mem_range.mpr (Nat.lt_succ_of_le hbudget), ?_⟩
  exact List.mem_map.mpr ⟨point, mem_rationalBooleanGridPoints resolution point, rfl⟩

/-- Small positive regret tolerance holds near any zero-regret contracting root.
Only denominator positivity is used; boundary hazards and degenerate roots remain allowed. -/
theorem eventually_stationaryHazard_regret_lt
    (reward : {S : Finset (Fin n) // S.Nonempty} → Payoff (Fin n))
    (hazard : Fin n → ℝ) (hmem : hazard ∈ quittingStationaryContractingHazardCube)
    (hregret : ∀ who, quittingStationaryHazardCap reward hazard who ≤
      quittingStationaryHazardPayoff reward hazard who)
    (accuracy : ℝ) (haccuracy : 0 < accuracy) :
    ∀ᶠ candidate in 𝓝 hazard,
      (∀ who, continueMassExcl candidate who < 1) ∧
      ∀ who, quittingStationaryHazardCap reward candidate who <
        quittingStationaryHazardPayoff reward candidate who + accuracy := by
  have hcontracts : ∀ᶠ candidate in 𝓝 hazard,
      ∀ who, continueMassExcl candidate who < 1 :=
    isOpen_setOf_continueMassExcl_lt_one.mem_nhds hmem.2
  have hsmall : ∀ᶠ candidate in 𝓝 hazard,
      ∀ who, quittingStationaryHazardCap reward candidate who <
        quittingStationaryHazardPayoff reward candidate who + accuracy := by
    apply Filter.eventually_all.mpr
    intro who
    have hpayoff : ContinuousAt
        (fun candidate => quittingStationaryHazardPayoff reward candidate who) hazard := by
      apply ContinuousAt.div
        (((continuous_apply who).continuousAt.mul
          (continuous_sigmaValue (weightOfReward reward) who).continuousAt).add
          ((continuous_const.sub (continuous_apply who)).continuousAt.mul
            (continuous_excludedValue (weightOfReward reward) who).continuousAt))
        (continuous_const.sub ((continuous_const.sub (continuous_apply who)).mul
          (continuous_continueMassExcl who))).continuousAt
      exact ne_of_gt (quittingStationaryHazardPayoff_denominator_pos hazard hmem who)
    have hcap : ContinuousAt
        (fun candidate => quittingStationaryHazardCap reward candidate who) hazard := by
      exact (continuous_sigmaValue (weightOfReward reward) who).continuousAt.sup
        ((continuous_excludedValue (weightOfReward reward) who).continuousAt.div
          (continuous_const.sub (continuous_continueMassExcl who)).continuousAt
          (ne_of_gt (sub_pos.mpr (hmem.2 who))))
    exact hcap.eventually_lt (hpayoff.add continuousAt_const)
      (lt_of_le_of_lt (hregret who) (lt_add_of_pos_right _ haccuracy))
  exact hcontracts.and hsmall

/-- Rational cube density plus actual cap continuity produces an accepted grid root. -/
theorem exists_rationalQuittingGridRoot_accepts_of_stationaryNash
    (reward : RationalQuittingReward n) (root : Fin n → PMF Bool)
    (hcontracts : ∀ who, quittingStationaryFixedOpponentsContinueMass root who < 1)
    (hnash : (quittingGame (rationalQuittingRewardToReal reward)).IsεAsymptoticNash
      (quittingTerminalPayoff (rationalQuittingRewardToReal reward)) 0
      (quittingStationaryProfile (rationalQuittingRewardToReal reward) root))
    (accuracy : ℚ) (haccuracy : 0 < accuracy) :
    ∃ resolution : ℕ, ∃ point : Fin n → Fin (resolution + 2),
      rationalQuittingStationaryRegretAccepts reward
        (rationalQuittingGridRoot resolution point) accuracy = true := by
  let realReward := rationalQuittingRewardToReal reward
  let hazard := hazardOfRoot root
  have hmem : hazard ∈ quittingStationaryContractingHazardCube := by
    refine ⟨fun who => ⟨hazardOfRoot_nonneg root who, hazardOfRoot_le_one root who⟩, ?_⟩
    intro who
    rw [← quittingStationaryFixedOpponentsContinueMass_eq_continueMassExcl]
    exact hcontracts who
  have hregret (who : Fin n) : quittingStationaryHazardCap realReward hazard who ≤
      quittingStationaryHazardPayoff realReward hazard who := by
    have h := (isεAsymptoticNash_stationary_iff_fullRateUnilateralCap_le
      realReward root 0).mp hnash who
    simpa only [quittingStationaryFullRateUnilateralCap_eq_hazardCap
      realReward root who (hcontracts who),
      quittingTerminalPayoff_stationary_eq_hazardPayoff realReward root who (hcontracts who),
      add_zero] using h
  have hgood := eventually_stationaryHazard_regret_lt realReward hazard hmem hregret
    (accuracy : ℝ) (by exact_mod_cast haccuracy)
  obtain ⟨radius, hradius, hball⟩ := Metric.mem_nhds_iff.mp hgood
  obtain ⟨resolution, point, hdist⟩ := Math.RationalCubeGrid.exists_point_dist_lt
    hazard (fun who => (hmem.1 who).1) (fun who => (hmem.1 who).2) radius hradius
  let candidate := rationalQuittingGridRoot resolution point
  have hnear : hazardOfRoot candidate.toPMF ∈ Metric.ball hazard radius := by
    rw [Metric.mem_ball]
    simpa only [candidate, hazardOfRoot_rationalQuittingGridRoot,
      rationalBooleanGridProbability] using hdist
  have hchosen := hball hnear
  have hcandidateContracts (who : Fin n) :
      quittingStationaryFixedOpponentsContinueMass candidate.toPMF who < 1 := by
    rw [quittingStationaryFixedOpponentsContinueMass_eq_continueMassExcl]
    exact hchosen.1 who
  refine ⟨resolution, point, (rationalQuittingStationaryRegretAccepts_eq_true_iff
    reward candidate accuracy).mpr ⟨hcandidateContracts, ?_⟩⟩
  apply (isεAsymptoticNash_stationary_iff_fullRateUnilateralCap_le
    realReward candidate.toPMF (accuracy : ℝ)).mpr
  intro who
  rw [quittingStationaryFullRateUnilateralCap_eq_hazardCap
    realReward candidate.toPMF who (hcandidateContracts who),
    quittingTerminalPayoff_stationary_eq_hazardPayoff
      realReward candidate.toPMF who (hcandidateContracts who)]
  exact (hchosen.2 who).le

/-- Increasing finite search budgets eventually succeed for every positive accuracy. -/
theorem rationalQuittingStationaryBoundedSearch_eventually_succeeds_of_stationaryNash
    (reward : RationalQuittingReward n) (root : Fin n → PMF Bool)
    (hcontracts : ∀ who, quittingStationaryFixedOpponentsContinueMass root who < 1)
    (hnash : (quittingGame (rationalQuittingRewardToReal reward)).IsεAsymptoticNash
      (quittingTerminalPayoff (rationalQuittingRewardToReal reward)) 0
      (quittingStationaryProfile (rationalQuittingRewardToReal reward) root))
    (accuracy : ℚ) (haccuracy : 0 < accuracy) :
    ∃ threshold : ℕ, ∀ budget, threshold ≤ budget →
      (rationalQuittingStationaryBoundedSearch? reward accuracy budget).isSome = true := by
  obtain ⟨resolution, point, haccepts⟩ :=
    exists_rationalQuittingGridRoot_accepts_of_stationaryNash
      reward root hcontracts hnash accuracy haccuracy
  refine ⟨resolution, fun budget hbudget => ?_⟩
  exact List.find?_isSome.mpr ⟨rationalQuittingGridRoot resolution point,
    mem_rationalQuittingStationaryGridCandidates resolution budget hbudget point, haccepts⟩

/-- The first successful finite budget, with termination justified by a success proof.
The proof is erased; the selector tests budgets with exact rational arithmetic. -/
def rationalQuittingStationarySearchSelector (reward : RationalQuittingReward n)
    (accuracy : ℚ)
    (hsuccess : ∃ budget,
      (rationalQuittingStationaryBoundedSearch? reward accuracy budget).isSome = true) :
    RationalQuittingRoot n :=
  (rationalQuittingStationaryBoundedSearch? reward accuracy (Nat.find hsuccess)).get
    (Nat.find_spec hsuccess)

theorem rationalQuittingStationarySearchSelector_accepts (reward : RationalQuittingReward n)
    (accuracy : ℚ)
    (hsuccess : ∃ budget,
      (rationalQuittingStationaryBoundedSearch? reward accuracy budget).isSome = true) :
    rationalQuittingStationaryRegretAccepts reward
      (rationalQuittingStationarySearchSelector reward accuracy hsuccess) accuracy = true := by
  let search := rationalQuittingStationaryBoundedSearch? reward accuracy (Nat.find hsuccess)
  have hsome : search = some (search.get (Nat.find_spec hsuccess)) :=
    (Option.some_get _).symm
  exact List.find?_some
    (p := fun candidate : RationalQuittingRoot n =>
      rationalQuittingStationaryRegretAccepts reward candidate accuracy) hsome

/-- The returned rational root satisfies the actual whole-behavioral-class guarantee. -/
theorem rationalQuittingStationarySearchSelector_spec (reward : RationalQuittingReward n)
    (accuracy : ℚ)
    (hsuccess : ∃ budget,
      (rationalQuittingStationaryBoundedSearch? reward accuracy budget).isSome = true) :
    let selected := rationalQuittingStationarySearchSelector reward accuracy hsuccess
    (∀ who, quittingStationaryFixedOpponentsContinueMass selected.toPMF who < 1) ∧
    (quittingGame (rationalQuittingRewardToReal reward)).IsεAsymptoticNash
      (quittingTerminalPayoff (rationalQuittingRewardToReal reward)) (accuracy : ℝ)
      (quittingStationaryProfile (rationalQuittingRewardToReal reward) selected.toPMF) := by
  exact (rationalQuittingStationaryRegretAccepts_eq_true_iff reward _ accuracy).mp
    (rationalQuittingStationarySearchSelector_accepts reward accuracy hsuccess)

/-- The literal guarded crossed source hypotheses supply termination; no real
equilibrium root or target-payoff oracle is passed to the enumeration. -/
theorem rationalQuittingStationaryBoundedSearch_eventually_succeeds_of_sourceGuards
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
    (accuracy : ℚ) (haccuracy : 0 < accuracy) :
    ∃ threshold : ℕ, ∀ budget, threshold ≤ budget →
      (rationalQuittingStationaryBoundedSearch? reward accuracy budget).isSome = true := by
  obtain ⟨root, _, _, _, _, _, _, _, hcontracts, hnash, _⟩ :=
    exists_guardedCrossed_stationaryTerminalNash_uniformPayoff_of_sourceGuards
      (rationalQuittingRewardToReal reward) first second hdistinct height
      hheight hheightOne hguard hreciprocalFirst hreciprocalSecond hR0 hdegree
  exact rationalQuittingStationaryBoundedSearch_eventually_succeeds_of_stationaryNash
    reward root hcontracts hnash accuracy haccuracy

end GameTheory
