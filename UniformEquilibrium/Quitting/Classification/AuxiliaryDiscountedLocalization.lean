import UniformEquilibrium.Quitting.Bellman.Discounted.ClusterCompletion
import UniformEquilibrium.Quitting.Classification.ThreePlayer.AuxiliaryShift

/-!

# Localization of all auxiliary discounted fixed points

A nonzero hazard cluster is completed using the actual bounded quotient values.
Its specified-endpoint germ feeds the existing punishment-completed original-game
consumer, including its signed sole-owner branch. Hence, under no original uniform
equilibrium, every actual auxiliary discounted fixed-point family tends to zero.
The final statement is uniform over the entire fixed-point set, not a selection.
-/

noncomputable section

namespace GameTheory

open Filter Set Topology StochasticGame

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Identifying the complete endpoint identifies the full decoded live product law. -/
theorem quittingGerm_endpointProfile_eq_of_discountedAssignment
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (germ : (quittingGame reward).AnalyticBellmanGerm)
    (rootLimit : ι → PMF Bool) (valueLimit : Payoff ι)
    (hendpoint : germ.endpoint =
      quittingDiscountedBellmanAssignment reward 0 rootLimit valueLimit) :
    germ.endpointProfile none = rootLimit := by
  funext who
  apply Math.ProbabilityMassFunction.toVector_injective
  funext action
  change ((germ.endpointProfile none who) action).toReal = (rootLimit who action).toReal
  rw [AnalyticBellmanGerm.endpointProfile,
    (quittingGame reward).bellmanDecodeProfile_apply_toReal, hendpoint]
  rfl

/-- The same complete endpoint retains the live value, without translation or reselection. -/
theorem quittingGermValue_zero_eq_of_discountedAssignment
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (germ : (quittingGame reward).AnalyticBellmanGerm)
    (rootLimit : ι → PMF Bool) (valueLimit : Payoff ι)
    (hendpoint : germ.endpoint =
      quittingDiscountedBellmanAssignment reward 0 rootLimit valueLimit) :
    quittingGermValue germ 0 = valueLimit := by
  funext who
  change germ.endpoint (.val none who) = valueLimit who
  rw [hendpoint]
  rfl

/-- A supplied absorbing hazard cluster of the canonical auxiliary table yields
an actual original-game uniform payoff at the translated compatible value limit. -/
theorem exists_uniformEquilibriumPayoff_of_auxiliaryDiscounted_hazardCluster
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {κ : Type*} {sourceFilter : Filter κ}
    (discountComplement : κ → ℝ) (root : κ → ι → PMF Bool)
    (rootLimit : ι → PMF Bool)
    (hdiscount : Tendsto discountComplement sourceFilter (𝓝 0))
    (hcluster : MapClusterPt (hazardOfRoot rootLimit) sourceFilter
      (fun index => hazardOfRoot (root index)))
    (hsource : ∀ᶠ index in sourceFilter,
      0 < discountComplement index ∧ discountComplement index ≤ 1 ∧
        quittingDiscountedClippedMap (quittingAuxiliaryReward reward) (discountComplement index)
          (hazardOfRoot (root index)) = hazardOfRoot (root index))
    (habsorbs : quittingStationaryContinueMass rootLimit < 1) :
    ∃ valueLimit : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none
        (quittingAuxiliaryTarget reward valueLimit) ∧
      ∃ germ : (quittingGame (quittingAuxiliaryReward reward)).AnalyticBellmanGerm,
        germ.endpoint = quittingDiscountedBellmanAssignment
          (quittingAuxiliaryReward reward) 0 rootLimit valueLimit := by
  obtain ⟨valueLimit, refinement, _, _, _, _, _, germ, hendpoint⟩ :=
    exists_analyticBellmanGerm_at_discountedFixedPoint_hazardCluster
      (quittingAuxiliaryReward reward) discountComplement root rootLimit
      hdiscount hcluster hsource
  have hprofile := quittingGerm_endpointProfile_eq_of_discountedAssignment
    (quittingAuxiliaryReward reward) germ rootLimit valueLimit hendpoint
  have hvalue := quittingGermValue_zero_eq_of_discountedAssignment
    (quittingAuxiliaryReward reward) germ rootLimit valueLimit hendpoint
  have hue := isUniformEquilibriumPayoff_of_auxiliaryGerm_absorbingEndpoint reward germ
    (by simpa only [hprofile] using habsorbs)
  rw [hvalue] at hue
  exact ⟨valueLimit, hue, germ, hendpoint⟩

/-- No original uniform payoff forces every supplied auxiliary discounted
fixed-point family to have hazards tending to zero. No fixed point is selected. -/
theorem tendsto_hazard_zero_of_no_uniformEquilibriumPayoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hno : ¬ ∃ payoff, (quittingGame reward).IsUniformEquilibriumPayoff none payoff)
    {κ : Type*} {sourceFilter : Filter κ}
    (discountComplement : κ → ℝ) (root : κ → ι → PMF Bool)
    (hdiscount : Tendsto discountComplement sourceFilter (𝓝 0))
    (hsource : ∀ᶠ index in sourceFilter,
      0 < discountComplement index ∧ discountComplement index ≤ 1 ∧
        quittingDiscountedClippedMap (quittingAuxiliaryReward reward) (discountComplement index)
          (hazardOfRoot (root index)) = hazardOfRoot (root index)) :
    Tendsto (fun index => hazardOfRoot (root index)) sourceFilter (𝓝 (0 : ι → ℝ)) := by
  have hcompact : IsCompact (Icc (0 : ι → ℝ) 1) := isCompact_Icc
  apply hcompact.tendsto_nhds_of_unique_mapClusterPt
    (Eventually.of_forall fun index =>
      ⟨hazardOfRoot_nonneg (root index), hazardOfRoot_le_one (root index)⟩)
  intro hazardLimit hcube hcluster
  by_contra hnonzero
  let rootLimit := rootOfHazard hazardLimit hcube.1 hcube.2
  have hrootLimit : hazardOfRoot rootLimit = hazardLimit :=
    hazardOfRoot_rootOfHazard hazardLimit hcube.1 hcube.2
  have habsorbs : quittingStationaryContinueMass rootLimit < 1 := by
    apply lt_of_le_of_ne (quittingStationaryContinueMass_le_one rootLimit)
    intro hone
    have hzero : hazardOfRoot rootLimit = 0 := by
      funext who
      change (rootLimit who true).toReal = 0
      rw [eq_pure_false_of_quittingStationaryContinueMass_eq_one hone who]
      simp
    exact hnonzero (hrootLimit.symm.trans hzero)
  obtain ⟨valueLimit, hue, _⟩ :=
    exists_uniformEquilibriumPayoff_of_auxiliaryDiscounted_hazardCluster reward
      discountComplement root rootLimit hdiscount (by simpa only [hrootLimit] using hcluster)
      hsource habsorbs
  exact hno ⟨quittingAuxiliaryTarget reward valueLimit, hue⟩

/-- Uniform localization over ALL actual cube fixed points of the canonical
auxiliary table: the small-discount threshold precedes both discount and root. -/
theorem auxiliaryDiscounted_fixedPoint_sum_lt_of_no_uniformEquilibriumPayoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hno : ¬ ∃ payoff, (quittingGame reward).IsUniformEquilibriumPayoff none payoff)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (discountComplement : ℝ),
      0 < discountComplement → discountComplement ≤ min δ 1 →
      ∀ hazard : ι → ℝ, (∀ who, 0 ≤ hazard who) → (∀ who, hazard who ≤ 1) →
        quittingDiscountedClippedMap (quittingAuxiliaryReward reward)
          discountComplement hazard = hazard → ∑ who, hazard who < ε := by
  let Source := {point : ℝ × (ι → ℝ) //
    0 < point.1 ∧ point.1 ≤ 1 ∧ (∀ who, 0 ≤ point.2 who) ∧
      (∀ who, point.2 who ≤ 1) ∧
      quittingDiscountedClippedMap (quittingAuxiliaryReward reward) point.1 point.2 = point.2}
  let discount : Source → ℝ := fun point => point.1.1
  let root : Source → ι → PMF Bool := fun point =>
    rootOfHazard point.1.2 point.2.2.2.1 point.2.2.2.2.1
  let sourceFilter := comap discount (𝓝[>] (0 : ℝ))
  have hdiscount : Tendsto discount sourceFilter (𝓝 (0 : ℝ)) :=
    tendsto_comap.mono_right nhdsWithin_le_nhds
  have hsource : ∀ᶠ point in sourceFilter,
      0 < discount point ∧ discount point ≤ 1 ∧
        quittingDiscountedClippedMap (quittingAuxiliaryReward reward) (discount point)
          (hazardOfRoot (root point)) = hazardOfRoot (root point) := by
    apply Eventually.of_forall
    intro point
    refine ⟨point.2.1, point.2.2.1, ?_⟩
    simpa [root, discount] using point.2.2.2.2.2
  have hlimit := tendsto_hazard_zero_of_no_uniformEquilibriumPayoff
    reward hno discount root hdiscount hsource
  have hsum : Tendsto (fun point => ∑ who, hazardOfRoot (root point) who)
      sourceFilter (𝓝 (0 : ℝ)) := by
    simpa only [Finset.sum_const_zero, Pi.zero_apply] using
      tendsto_finsetSum Finset.univ (fun who _ => (tendsto_pi_nhds.mp hlimit) who)
  have hsmall : ∀ᶠ point in sourceFilter, ∑ who, hazardOfRoot (root point) who < ε :=
    hsum.eventually (Iio_mem_nhds hε)
  obtain ⟨δ, hδ, hthreshold⟩ := ((nhdsGT_basis_Ioc (0 : ℝ)).comap discount).mem_iff.mp hsmall
  refine ⟨δ, hδ, ?_⟩
  intro discountComplement hpositive hbound hazard hzero hone hfixed
  let point : Source := ⟨(discountComplement, hazard), hpositive,
    hbound.trans (min_le_right _ _), hzero, hone, hfixed⟩
  have hpoint := hthreshold (show point ∈ discount ⁻¹' Ioc 0 δ from
    ⟨hpositive, hbound.trans (min_le_left _ _)⟩)
  simpa [root, point] using hpoint

end GameTheory
