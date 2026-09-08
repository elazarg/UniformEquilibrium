import UniformEquilibrium.Quitting.Bellman.Discounted.SpecifiedEndpoint
import UniformEquilibrium.Quitting.RewardBound
import Mathlib.Topology.Compactness.Compact

/-!

# Completing a supplied discounted hazard cluster

The uniform bound for actual quotient values provides a compact value cube.
Two filter refinements retain the supplied hazard cluster and select only a
compatible value cluster. The complete assignment and its analytic germ use
the same reward table and the same supplied limiting root.
-/

noncomputable section

namespace GameTheory

open Filter Set Topology StochasticGame

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A supplied hazard cluster of actual discounted fixed points admits a full
value/assignment endpoint along a nontrivial refinement of the same source. -/
theorem exists_analyticBellmanGerm_at_discountedFixedPoint_hazardCluster
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {κ : Type*} {sourceFilter : Filter κ}
    (discountComplement : κ → ℝ) (root : κ → ι → PMF Bool)
    (rootLimit : ι → PMF Bool)
    (hdiscount : Tendsto discountComplement sourceFilter (𝓝 0))
    (hcluster : MapClusterPt (hazardOfRoot rootLimit) sourceFilter
      (fun index => hazardOfRoot (root index)))
    (hsource : ∀ᶠ index in sourceFilter,
      0 < discountComplement index ∧ discountComplement index ≤ 1 ∧
        quittingDiscountedClippedMap reward (discountComplement index)
          (hazardOfRoot (root index)) = hazardOfRoot (root index)) :
    ∃ (valueLimit : Payoff ι) (refinement : Filter κ),
      refinement.NeBot ∧ refinement ≤ sourceFilter ∧
      (∀ who, |valueLimit who| ≤ quittingRewardBound reward) ∧
      Tendsto (fun index => hazardOfRoot (root index)) refinement
        (𝓝 (hazardOfRoot rootLimit)) ∧
      Tendsto (fun index => quittingDiscountedLiveValue reward
        (discountComplement index) (root index)) refinement (𝓝 valueLimit) ∧
      ∃ germ : (quittingGame reward).AnalyticBellmanGerm,
        germ.endpoint = quittingDiscountedBellmanAssignment reward 0 rootLimit valueLimit := by
  let hazard := fun index => hazardOfRoot (root index)
  let value := fun index => quittingDiscountedLiveValue reward
    (discountComplement index) (root index)
  let hazardFilter := comap hazard (𝓝 (hazardOfRoot rootLimit)) ⊓ sourceFilter
  haveI : hazardFilter.NeBot := neBot_inf_comap_iff_map'.mpr hcluster
  have hroot : Tendsto hazard hazardFilter (𝓝 (hazardOfRoot rootLimit)) :=
    tendsto_iff_comap.mpr inf_le_left
  have hsourceHazard := hsource.filter_mono
    (show hazardFilter ≤ sourceFilter from inf_le_right)
  let valueCube : Set (Payoff ι) :=
    Icc (fun _ => -quittingRewardBound reward) (fun _ => quittingRewardBound reward)
  have hmem : ∀ᶠ index in hazardFilter, value index ∈ valueCube := by
    filter_upwards [hsourceHazard] with index hindex
    have hbound : ∀ who, |value index who| ≤ quittingRewardBound reward :=
      fun who => abs_quittingDiscountedLiveValue_le reward hindex.1 hindex.2.1
        (abs_reward_le_quittingRewardBound reward) (root index) who
    exact ⟨fun who => (abs_le.mp (hbound who)).1,
      fun who => (abs_le.mp (hbound who)).2⟩
  obtain ⟨valueLimit, hvalueLimit, hvalueCluster⟩ :=
    (show IsCompact valueCube from isCompact_Icc).exists_mapClusterPt_of_frequently hmem.frequently
  let refinement := comap value (𝓝 valueLimit) ⊓ hazardFilter
  haveI : refinement.NeBot := neBot_inf_comap_iff_map'.mpr hvalueCluster
  have hle : refinement ≤ sourceFilter := inf_le_right.trans inf_le_right
  have hrootRefined := hroot.mono_left (show refinement ≤ hazardFilter from inf_le_right)
  have hvalue : Tendsto value refinement (𝓝 valueLimit) :=
    tendsto_iff_comap.mpr inf_le_left
  refine ⟨valueLimit, refinement, inferInstance, hle, ?_, hrootRefined, hvalue, ?_⟩
  · intro who
    exact abs_le.mpr ⟨hvalueLimit.1 who, hvalueLimit.2 who⟩
  · apply exists_analyticBellmanGerm_at_quittingDiscountedFixedPoint_limit
      reward discountComplement root value rootLimit valueLimit
      (hdiscount.mono_left hle) hrootRefined hvalue
    filter_upwards [hsource.filter_mono hle] with index hindex
    exact ⟨hindex.1, hindex.2.1, rfl, hindex.2.2⟩

end GameTheory
