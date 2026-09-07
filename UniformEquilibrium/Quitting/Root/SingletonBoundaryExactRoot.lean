import UniformEquilibrium.Quitting.Stationary.SingletonStationaryRoot

/-! # An absorbing exact root at a uniquely binding singleton face -/

noncomputable section

namespace GameTheory

open Filter Topology Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A continuation with exactly one coordinate on its singleton floor has
an absorbing exact Nash root. Only that player's marginal is changed from
all Continue; no nonnegative-premium condition is needed for this lemma. -/
theorem exists_absorbing_exactRoot_of_unique_singleton_binding
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (point : Payoff ι) (owner : ι)
    (howner : point owner = reward (quittingSingletonTerminal owner) owner)
    (hother : ∀ other, other ≠ owner →
      reward (quittingSingletonTerminal other) other < point other) :
    ∃ root : ι → PMF Bool,
      IsεQuittingRootNash reward point 0 root ∧ 0 < quittingRootAbsorptionMass root := by
  let gap : ι → ℝ → ℝ := fun other rate =>
    rate * quittingSoloReward reward owner other + (1 - rate) * point other -
      ((1 - rate) * quittingSoloReward reward other other +
        rate * quittingSingletonCollisionReward reward owner other)
  have hgap : ∀ᶠ rate : ℝ in 𝓝[>] 0, ∀ other, other ≠ owner → 0 < gap other rate := by
    apply Filter.eventually_all.mpr
    intro other
    by_cases hne : other ≠ owner
    · have hcont : Continuous (gap other) := by unfold gap; fun_prop
      have hpos : 0 < gap other 0 := by
        simpa [gap, quittingSoloReward, quittingSingletonTerminal] using hother other hne
      have hpositive : ∀ᶠ rate : ℝ in 𝓝[>] 0, 0 < gap other rate :=
        nhdsWithin_le_nhds (hcont.continuousAt.eventually (lt_mem_nhds hpos))
      exact hpositive.mono fun rate hrate _ => hrate
    · exact Filter.Eventually.of_forall fun _ hneq => (hne hneq).elim
  have hone : ∀ᶠ rate : ℝ in 𝓝[>] 0, rate < 1 :=
    nhdsWithin_le_nhds (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  have hchoose : ∀ᶠ rate : ℝ in 𝓝[>] 0,
      0 < rate ∧ rate < 1 ∧ ∀ other, other ≠ owner → 0 < gap other rate := by
    filter_upwards [self_mem_nhdsWithin, hone, hgap] with rate hrate hupper hgap
    exact ⟨hrate, hupper, hgap⟩
  obtain ⟨rate, hrate, hone, hgap⟩ := hchoose.exists
  let hazard := quittingHazardCoin rate hrate.le hone.le
  let root := quittingSoloStationaryRoot owner hazard
  have hquit : ∀ player, quittingRootQuitPayoff reward point root player =
      quittingStationaryFixedOpponentsQuitValue reward root player := by
    intro player
    exact quittingRootQuitPayoff_eq_fixedOpponentsQuitValue reward (fun _ => root) player point 0
  have hcontinue : ∀ player, quittingRootContinuePayoff reward point root player =
      quittingStationaryFixedOpponentsContinueReward reward root player +
        quittingStationaryFixedOpponentsContinueMass root player * point player := by
    intro player
    exact quittingRootContinuePayoff_eq_fixedOpponents reward (fun _ => root) player point 0
  have hend : IsεQuittingRootEndpointNash reward point 0 root := by
    intro player
    by_cases heq : player = owner
    · subst player
      have hzero : quittingRootEndpointDifference reward point root owner = 0 := by
        rw [quittingRootEndpointDifference, hquit, hcontinue]
        simp [root, howner, quittingSoloReward, quittingSingletonTerminal]
      simp [hzero]
    · have hnonpos : quittingRootEndpointDifference reward point root player ≤ 0 := by
        rw [quittingRootEndpointDifference, hquit, hcontinue]
        rw [quittingStationaryFixedOpponentsQuitValue_solo_other_eq_mix reward heq hazard,
          quittingStationaryFixedOpponentsContinueReward_solo_other reward heq hazard,
          quittingStationaryFixedOpponentsContinueMass_solo_other heq hazard]
        have hpos := hgap player heq
        simp only [hazard, quittingHazardCoin_true_toReal,
          quittingHazardCoin_false_toReal]
        dsimp only [gap] at hpos
        linarith
      constructor
      · exact mul_nonpos_of_nonneg_of_nonpos ENNReal.toReal_nonneg hnonpos
      · simp [root, quittingSoloStationaryRoot, heq]
  refine ⟨root, (isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash
    reward point root).mp hend, ?_⟩
  simpa [root, quittingRootAbsorptionMass, quittingStationaryContinueMass_solo,
    hazard] using hrate

end GameTheory
