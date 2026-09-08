import UniformEquilibrium.Quitting.Classification.SimonFiniteOrbit.NormalizedMotionStationaryPrefixProducer
import UniformEquilibrium.Quitting.Circulation.MultiOwnerFaceCirculationCompactPath
import UniformEquilibrium.Quitting.Root.NashDefectContinuity

/-!
# Uniform motion and survival bounds on compact continuation sets

This module combines the already checked normalized-motion contrapositive with
the compact separation of admissible product roots from the sure-quitter
boundary.  It is stated in production quitting-game semantics; paper-specific
notation is handled by a separate adapter.
-/

noncomputable section

namespace GameTheory

open Set StochasticGame Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Rationality at a fixed error is a closed condition on continuation
payoffs. -/
theorem isClosed_quittingSimonRationalPayoffAt
    (reward : {coalition : Finset ι // coalition.Nonempty} → Payoff ι)
    (error : ℝ) :
    IsClosed {tail : Payoff ι |
      QuittingSimonRationalPayoffAt reward error tail} := by
  rw [show {tail : Payoff ι |
      QuittingSimonRationalPayoffAt reward error tail} =
      ⋂ who : ι,
        {tail | quittingPunishmentValue reward who - error ≤ tail who} by
    ext tail
    simp [QuittingSimonRationalPayoffAt]]
  exact isClosed_iInter fun who =>
    isClosed_le continuous_const (continuous_apply who)

/-- Closed admissible continuation/root pairs over a displayed carrier. -/
def QuittingCompactContinuationAdmissiblePairs
    (reward : {coalition : Finset ι // coalition.Nonempty} → Payoff ι)
    (carrier : Set (Payoff ι)) (error : ℝ) :
    Set (Payoff ι × QuittingRootSimplex ι) :=
  {pair | pair.1 ∈ carrier ∧
    QuittingSimonRationalPayoffAt reward error pair.1 ∧
    IsQuittingSimplexRootSupportApproxNash reward pair.1 error pair.2}

/-- The admissible continuation/root pairs over a compact carrier form a
compact set. -/
theorem isCompact_quittingCompactContinuationAdmissiblePairs
    (reward : {coalition : Finset ι // coalition.Nonempty} → Payoff ι)
    {carrier : Set (Payoff ι)} (hcarrier : IsCompact carrier)
    (error : ℝ) :
    IsCompact (QuittingCompactContinuationAdmissiblePairs reward carrier error) := by
  have hambient : IsCompact
      (carrier ×ˢ (Set.univ : Set (QuittingRootSimplex ι))) :=
    hcarrier.prod isCompact_univ
  apply hambient.of_isClosed_subset
  · have hclosed := ((hcarrier.isClosed.preimage continuous_fst).inter
      ((isClosed_quittingSimonRationalPayoffAt reward error).preimage
        continuous_fst)).inter
      (isClosed_isQuittingSimplexRootSupportApproxNash reward error)
    rw [show QuittingCompactContinuationAdmissiblePairs reward carrier error =
        (Prod.fst ⁻¹' carrier ∩
          Prod.fst ⁻¹' {tail |
            QuittingSimonRationalPayoffAt reward error tail}) ∩
          {point |
            IsQuittingSimplexRootSupportApproxNash
              reward point.1 error point.2} by
      ext pair
      simp only [QuittingCompactContinuationAdmissiblePairs, Set.mem_setOf_eq,
        Set.mem_inter_iff, Set.mem_preimage]
      tauto]
    exact hclosed
  · intro pair hpair
    exact ⟨hpair.1, Set.mem_univ pair.2⟩

/-- If admissible roots over a compact continuation carrier have no sure
quitter, their all-Continue masses have one uniform positive lower bound. -/
theorem exists_pos_uniformContinueMass_on_compact_of_noSure
    [Nonempty ι]
    (reward : {coalition : Finset ι // coalition.Nonempty} → Payoff ι)
    {carrier : Set (Payoff ι)} (hcarrier : IsCompact carrier)
    {error : ℝ}
    (hnoSure : SuppliedQuittingSimonNoSureQuitterAt reward error) :
    ∃ lower : ℝ, 0 < lower ∧
      ∀ tail ∈ carrier, ∀ root,
        QuittingSimonRationalPayoffAt reward error tail →
        IsQuittingRootSupportApproxNash reward tail error root →
        lower ≤ quittingStationaryContinueMass root := by
  let admissible := QuittingCompactContinuationAdmissiblePairs reward carrier error
  have hcompact : IsCompact admissible :=
    isCompact_quittingCompactContinuationAdmissiblePairs reward hcarrier error
  by_cases hnonempty : admissible.Nonempty
  · let continueMass : Payoff ι × QuittingRootSimplex ι → ℝ :=
      fun pair => quittingStationaryContinueMass
        (quittingRootOfSimplex pair.2)
    have hcontinuous : Continuous continueMass := by
      have hsub : Continuous
          (fun pair : Payoff ι × QuittingRootSimplex ι =>
            1 - quittingRootAbsorptionMass
              (quittingRootOfSimplex pair.2)) :=
        continuous_const.sub
          ((continuous_quittingRootAbsorptionMass_simplex (ι := ι)).comp
            continuous_snd)
      simpa only [continueMass, quittingRootAbsorptionMass,
        sub_sub_cancel] using hsub
    obtain ⟨minimum, hminimumMem, hminimum⟩ :=
      hcompact.exists_isMinOn hnonempty hcontinuous.continuousOn
    have hminimumPos : 0 < continueMass minimum := by
      have hnotSure : ¬QuittingRootHasSureQuitter
          (quittingRootOfSimplex minimum.2) := by
        apply hnoSure minimum.1
        · exact hminimumMem.2.1
        · exact (isQuittingSimplexRootSupportApproxNash_iff
            reward minimum.1 error minimum.2).mp hminimumMem.2.2
      have hnonneg : 0 ≤ continueMass minimum := by
        exact quittingStationaryContinueMass_nonneg _
      refine lt_of_le_of_ne hnonneg fun hzero => ?_
      have hfactor : ∃ who : ι,
          (quittingRootOfSimplex minimum.2 who false).toReal = 0 := by
        have hprod : ∏ who : ι,
            (quittingRootOfSimplex minimum.2 who false).toReal = 0 := by
          simpa only [continueMass,
            quittingStationaryContinueMass_eq_prod_continueProbability]
            using hzero.symm
        simpa only [Finset.prod_eq_zero_iff, Finset.mem_univ, true_and]
          using hprod
      obtain ⟨who, hfalse⟩ := hfactor
      apply hnotSure
      exact ⟨who, (pmf_eq_pure_true_iff_apply_false_eq_zero _).mpr
        ((ENNReal.toReal_eq_zero_iff _).mp hfalse |>.resolve_right
          (PMF.apply_ne_top _ _))⟩
    refine ⟨continueMass minimum, hminimumPos, ?_⟩
    intro tail htail root hrational hsupport
    let simplexRoot := quittingSimplexOfRoot root
    have hroot : quittingRootOfSimplex simplexRoot = root :=
      quittingRootOfSimplex_simplexOfRoot root
    have hmem : (tail, simplexRoot) ∈ admissible := by
      refine ⟨htail, hrational, ?_⟩
      apply (isQuittingSimplexRootSupportApproxNash_iff
        reward tail error simplexRoot).mpr
      rw [hroot]
      exact hsupport
    have hmin := hminimum hmem
    change continueMass minimum ≤
      quittingStationaryContinueMass (quittingRootOfSimplex simplexRoot) at hmin
    rw [hroot] at hmin
    exact hmin
  · refine ⟨1, zero_lt_one, ?_⟩
    intro tail htail root hrational hsupport
    exfalso
    apply hnonempty
    let simplexRoot := quittingSimplexOfRoot root
    refine ⟨(tail, simplexRoot), htail, hrational, ?_⟩
    apply (isQuittingSimplexRootSupportApproxNash_iff
      reward tail error simplexRoot).mpr
    rw [quittingRootOfSimplex_simplexOfRoot]
    exact hsupport

/-- Uniform motion and survival bounds over a compact continuation carrier. -/
def HasQuittingCompactContinuationMotionAt
    (reward : {coalition : Finset ι // coalition.Nonempty} → Payoff ι)
    (carrier : Set (Payoff ι)) (rate : ℝ) : Prop :=
  0 < rate ∧ rate < 1 ∧
    ∀ tail ∈ carrier, ∀ root,
      QuittingSimonRationalPayoffAt reward rate tail →
      IsQuittingRootSupportApproxNash reward tail rate root →
      (∃ who,
        rate * quittingRootAbsorptionMass root ≤
          |quittingRootSuccessorPayoff reward tail root who - tail who|) ∧
      rate ≤ quittingStationaryContinueMass root

/-- Failure of the instant and stationarily generated branches gives the
corrected motion and survival bounds uniformly on every fixed compact
continuation carrier. -/
theorem exists_compactContinuationMotion_of_not_branches
    [Nonempty ι]
    (reward : {coalition : Finset ι // coalition.Nonempty} → Payoff ι)
    (hinstant : ¬QuittingInstantPunishmentεEquilibriumExistence reward)
    (hgenerated : ¬QuittingStationarilyGeneratedApproximateEquilibria reward)
    {carrier : Set (Payoff ι)} (hcarrier : IsCompact carrier) :
    ∃ rate : ℝ,
      HasQuittingCompactContinuationMotionAt reward carrier rate := by
  obtain ⟨motionRate, hmotionRate, hmotionRateOne, hmotion⟩ :=
    exists_normalizedMotionLowerBound_of_not_branches
      reward hinstant hgenerated
  obtain ⟨sureRate, hsureRate, hnoSure⟩ :=
    exists_pos_noSure_support_scale_of_not_instant reward hinstant
  obtain ⟨massRate, hmassRate, hmass⟩ :=
    exists_pos_uniformContinueMass_on_compact_of_noSure
      reward hcarrier hnoSure
  let rate := min (min motionRate sureRate) massRate
  have hrate : 0 < rate := lt_min (lt_min hmotionRate hsureRate) hmassRate
  have hrateMotion : rate ≤ motionRate :=
    (min_le_left (min motionRate sureRate) massRate).trans
      (min_le_left motionRate sureRate)
  have hrateSure : rate ≤ sureRate :=
    (min_le_left (min motionRate sureRate) massRate).trans
      (min_le_right motionRate sureRate)
  have hrateMass : rate ≤ massRate := min_le_right _ _
  refine ⟨rate, hrate, hrateMotion.trans_lt hmotionRateOne, ?_⟩
  intro tail htail root hrational hsupport
  have hrationalMotion := hrational.mono hrateMotion
  have hsupportMotion := hsupport.mono hrateMotion
  obtain ⟨who, hwho⟩ := hmotion tail root hrationalMotion hsupportMotion
  have habsorption : 0 ≤ quittingRootAbsorptionMass root :=
    quittingRootAbsorptionMass_nonneg root
  have hmotionFinal : rate * quittingRootAbsorptionMass root ≤
      |quittingRootSuccessorPayoff reward tail root who - tail who| :=
    (mul_le_mul_of_nonneg_right hrateMotion habsorption).trans hwho
  have hrationalSure := hrational.mono hrateSure
  have hsupportSure := hsupport.mono hrateSure
  exact ⟨⟨who, hmotionFinal⟩,
    hrateMass.trans (hmass tail htail root hrationalSure hsupportSure)⟩

end GameTheory
