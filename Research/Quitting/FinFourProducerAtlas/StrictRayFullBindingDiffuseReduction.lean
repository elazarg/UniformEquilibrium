/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Research.Quitting.FinFourProducerAtlas.StrictRayTailNormalizedCapFlow

/-!
# Compact full-binding reduction for a strict Fin4 ray

Every positive-hazard strict ray has a jointly convergent subsequence of its
current hazard direction, remaining-tail hazard barycenter, and renewal
ratio.  If the limiting binding face is full and the renewal-ratio limit is
zero, a full-support current limit would force the tail limit to solve the
homogeneous singleton LCP.  The hard residual excludes that possibility.

Thus one actual compact cluster is either ballistic (positive renewal-ratio
limit) or has current-limit positive support of cardinality at most three.
The conclusion retains the same ray, packet, and minimum source.  It does not
consume either surviving branch or produce a return, rank drop, or uniform
equilibrium payoff.
-/

noncomputable section

namespace GameTheory

open Filter Math Math.LinearProgramming Set

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

namespace QuittingForwardExactCapTail

/-- Every coordinate of the remaining-hazard barycenter is nonnegative. -/
theorem tailAverage_nonneg
    (ray : QuittingForwardExactCapTail reward) (start : ℕ) (who : ι) :
    0 ≤ ray.tailAverage start who := by
  apply div_nonneg
  · unfold tailFlow
    exact tsum_nonneg fun offset ↦
      mul_nonneg (ray.totalHazard_nonneg _)
        (ray.currentHazard_nonneg _ who)
  · exact (ray.tailMass_pos start).le

/-- The remaining-hazard barycenter has total mass one. -/
theorem sum_tailAverage
    (ray : QuittingForwardExactCapTail reward) (start : ℕ) :
    ∑ who, ray.tailAverage start who = 1 := by
  have hsum : ∑ who, ray.tailFlow start who = ray.tailMass start := by
    unfold tailFlow tailMass
    rw [← Summable.tsum_finsetSum (fun who _ ↦
      ray.weightedCurrentHazard_summable start who)]
    apply tsum_congr
    intro offset
    rw [← Finset.mul_sum, ray.sum_currentHazard, mul_one]
  unfold tailAverage
  rw [← Finset.sum_div, hsum]
  exact div_self (ray.tailMass_pos start).ne'

/-- Current marginal hazards as a literal standard-simplex point. -/
def currentHazardSimplex
    (ray : QuittingForwardExactCapTail reward) (time : ℕ) :
    stdSimplex ℝ ι :=
  ⟨ray.currentHazard time, ray.currentHazard_nonneg time,
    ray.sum_currentHazard time⟩

/-- The remaining-tail hazard barycenter as a literal simplex point. -/
def tailAverageSimplex
    (ray : QuittingForwardExactCapTail reward) (time : ℕ) :
    stdSimplex ℝ ι :=
  ⟨ray.tailAverage time, ray.tailAverage_nonneg time,
    ray.sum_tailAverage time⟩

/-- The renewal ratio as a point of the compact unit interval. -/
def renewalRatioPoint
    (ray : QuittingForwardExactCapTail reward) (time : ℕ) :
    Set.Icc (0 : ℝ) 1 :=
  ⟨ray.renewalRatio time,
    ray.renewalRatio_nonneg time, ray.renewalRatio_le_one time⟩

/-- Compact state carrying the three normalized quantities used by the
strict-ray first-order limit. -/
abbrev CompactHazardState :=
  stdSimplex ℝ ι × stdSimplex ℝ ι × Set.Icc (0 : ℝ) 1

/-- The normalized compact state at one actual ray date. -/
def compactHazardState
    (ray : QuittingForwardExactCapTail reward) (time : ℕ) :
    CompactHazardState (ι := ι) :=
  (ray.currentHazardSimplex time, ray.tailAverageSimplex time,
    ray.renewalRatioPoint time)

/-- One jointly convergent strict subsequence of all three normalized ray
quantities.  The cluster is dependent on the same actual ray. -/
structure CompactHazardCluster
    (ray : QuittingForwardExactCapTail reward) where
  subseq : ℕ → ℕ
  subseq_strictMono : StrictMono subseq
  limit : CompactHazardState (ι := ι)
  state_tendsto : Tendsto (fun rank ↦ ray.compactHazardState (subseq rank))
    atTop (nhds limit)

namespace CompactHazardCluster

variable {ray : QuittingForwardExactCapTail reward}

/-- Limiting current marginal-hazard direction. -/
def currentLimit (cluster : CompactHazardCluster ray) : ι → ℝ :=
  cluster.limit.1.val

/-- Limiting remaining-tail hazard barycenter. -/
def tailLimit (cluster : CompactHazardCluster ray) : ι → ℝ :=
  cluster.limit.2.1.val

/-- Limiting renewal ratio. -/
def ratioLimit (cluster : CompactHazardCluster ray) : ℝ :=
  cluster.limit.2.2.val

theorem current_tendsto
    (cluster : CompactHazardCluster ray) (who : ι) :
    Tendsto (fun rank ↦ ray.currentHazard (cluster.subseq rank) who)
      atTop (nhds (cluster.currentLimit who)) := by
  have hcontinuous : Continuous
      (fun state : CompactHazardState (ι := ι) ↦ state.1.val who) :=
    ((continuous_apply who).comp continuous_subtype_val).comp continuous_fst
  simpa [compactHazardState, currentHazardSimplex, currentLimit,
    Function.comp_def] using
      hcontinuous.continuousAt.tendsto.comp cluster.state_tendsto

theorem tail_tendsto
    (cluster : CompactHazardCluster ray) (who : ι) :
    Tendsto (fun rank ↦ ray.tailAverage (cluster.subseq rank) who)
      atTop (nhds (cluster.tailLimit who)) := by
  have hcontinuous : Continuous
      (fun state : CompactHazardState (ι := ι) ↦ state.2.1.val who) :=
    ((continuous_apply who).comp continuous_subtype_val).comp
      (continuous_fst.comp continuous_snd)
  simpa [compactHazardState, tailAverageSimplex, tailLimit,
    Function.comp_def] using
      hcontinuous.continuousAt.tendsto.comp cluster.state_tendsto

theorem ratio_tendsto (cluster : CompactHazardCluster ray) :
    Tendsto (fun rank ↦ ray.renewalRatio (cluster.subseq rank))
      atTop (nhds cluster.ratioLimit) := by
  have hcontinuous : Continuous
      (fun state : CompactHazardState (ι := ι) ↦ (state.2.2 : ℝ)) :=
    continuous_subtype_val.comp (continuous_snd.comp continuous_snd)
  simpa [compactHazardState, renewalRatioPoint, ratioLimit,
    Function.comp_def] using
      hcontinuous.continuousAt.tendsto.comp cluster.state_tendsto

theorem currentLimit_nonneg
    (cluster : CompactHazardCluster ray) (who : ι) :
    0 ≤ cluster.currentLimit who :=
  cluster.limit.1.property.1 who

theorem currentLimit_sum (cluster : CompactHazardCluster ray) :
    ∑ who, cluster.currentLimit who = 1 :=
  cluster.limit.1.property.2

theorem tailLimit_nonneg
    (cluster : CompactHazardCluster ray) (who : ι) :
    0 ≤ cluster.tailLimit who :=
  cluster.limit.2.1.property.1 who

theorem tailLimit_sum (cluster : CompactHazardCluster ray) :
    ∑ who, cluster.tailLimit who = 1 :=
  cluster.limit.2.1.property.2

theorem ratioLimit_nonneg (cluster : CompactHazardCluster ray) :
    0 ≤ cluster.ratioLimit :=
  cluster.limit.2.2.property.1

theorem ratioLimit_le_one (cluster : CompactHazardCluster ray) :
    cluster.ratioLimit ≤ 1 :=
  cluster.limit.2.2.property.2

end CompactHazardCluster

/-- Compactness produces a joint cluster without any supplied subsequence or
limit data. -/
theorem nonempty_compactHazardCluster
    (ray : QuittingForwardExactCapTail reward) :
    Nonempty (CompactHazardCluster ray) := by
  obtain ⟨limit, subseq, hsubseq, htendsto⟩ :=
    CompactSpace.tendsto_subseq ray.compactHazardState
  exact ⟨{
    subseq := subseq
    subseq_strictMono := hsubseq
    limit := limit
    state_tendsto := htendsto
  }⟩

end QuittingForwardExactCapTail

variable {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
variable {bound : ℝ}
variable {source : FinFourMinimumAtomProducer reward bound}
variable {returnSource : FinFourOwnerCompressedMinimumReturnForcedPairSource source}
variable {lambda : ℝ}

namespace FinFourMinimumAtomProducer

private def fullCoreEquiv
    (source : FinFourMinimumAtomProducer reward bound) :
    QuittingLCPClassification.normalCore
        (QuittingLCPClassification.normalizedSoloMatrix reward) ≃ Fin 4 where
  toFun player := player.1
  invFun who := ⟨who, by
    rw [source.residual.normalCore_eq_univ]
    exact Finset.mem_univ who⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := rfl

private theorem reindex_normalPlayerMatrix_eq_full
    (source : FinFourMinimumAtomProducer reward bound) :
    reindexMatrix source.fullCoreEquiv
        (QuittingLCPClassification.normalPlayerMatrix
          (QuittingLCPClassification.normalizedSoloMatrix reward)) =
      QuittingLCPClassification.normalizedSoloMatrix reward := by
  funext receiver owner
  rfl

/-- The full-core hard residual excludes a homogeneous solution of the full
normalized solo matrix, not only of its definitionally reindexed normal
principal matrix. -/
theorem not_hasHomogeneous_fullNormalizedSoloMatrix
    (source : FinFourMinimumAtomProducer reward bound) :
    ¬QuittingLCPClassification.HasHomogeneousSimplexSolution
      (QuittingLCPClassification.normalizedSoloMatrix reward) := by
  intro hfull
  apply source.residual.residualHardClass.no_homogeneous
  have hreindexed : SingletonLCPFeasible
      (reindexMatrix source.fullCoreEquiv
        (QuittingLCPClassification.normalPlayerMatrix
          (QuittingLCPClassification.normalizedSoloMatrix reward))) := by
    rw [source.reindex_normalPlayerMatrix_eq_full]
    exact hfull
  exact (singletonLCPFeasible_reindexMatrix_iff source.fullCoreEquiv
    (QuittingLCPClassification.normalPlayerMatrix
      (QuittingLCPClassification.normalizedSoloMatrix reward))).1 hreindexed

end FinFourMinimumAtomProducer

namespace FinFourOwnerCompressedMinimumReturnForcedPairPacket

variable {packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
  returnSource lambda}
variable {flow : FinFourStrictRayForwardExactCapTail packet}

/-- Positive support of the limiting current marginal-hazard direction. -/
def FinFourStrictRayCompactCurrentSupport
    (cluster : QuittingForwardExactCapTail.CompactHazardCluster flow.forward) :
    Finset (Fin 4) :=
  Finset.univ.filter fun who ↦ 0 < cluster.currentLimit who

/-- The current-limit positive support is nonempty because its coordinates
are nonnegative and sum to one. -/
theorem compactCurrentSupport_nonempty
    (cluster : QuittingForwardExactCapTail.CompactHazardCluster flow.forward) :
    (FinFourStrictRayCompactCurrentSupport cluster).Nonempty := by
  by_contra hnonempty
  have hempty : FinFourStrictRayCompactCurrentSupport cluster = ∅ :=
    Finset.not_nonempty_iff_eq_empty.mp hnonempty
  have hzero : ∀ who : Fin 4, cluster.currentLimit who = 0 := by
    intro who
    apply le_antisymm
    · apply le_of_not_gt
      intro hpos
      have hmem : who ∈ FinFourStrictRayCompactCurrentSupport cluster := by
        simp [FinFourStrictRayCompactCurrentSupport, hpos]
      rw [hempty] at hmem
      simp at hmem
    · exact cluster.currentLimit_nonneg who
  have hsum := cluster.currentLimit_sum
  simp only [hzero, Finset.sum_const_zero] at hsum
  norm_num at hsum

/-- On the full limiting binding face, no diffuse cluster can also have a
strictly positive current-limit coordinate at every player. -/
theorem not_ratioLimit_eq_zero_and_all_currentLimit_pos_of_fullBinding
    (cluster : QuittingForwardExactCapTail.CompactHazardCluster flow.forward)
    (hbinding : flow.forward.bindingFinset = Finset.univ) :
    ¬(cluster.ratioLimit = 0 ∧
      ∀ who : Fin 4, 0 < cluster.currentLimit who) := by
  rintro ⟨hratio, hcurrentPos⟩
  let analysis := flow.analysis
  have hrow : ∀ who : Fin 4,
      ∑ owner,
          QuittingLCPClassification.normalizedSoloMatrix reward who owner *
            cluster.tailLimit owner = 0 := by
    intro who
    have hbindingWho : who ∈ flow.forward.bindingFinset := by
      rw [hbinding]
      exact Finset.mem_univ who
    have hzero := analysis.normalized.subseq_diffuse_positiveCurrent_solo_eq_zero
      cluster.subseq cluster.subseq_strictMono cluster.currentLimit
        cluster.tailLimit cluster.ratioLimit cluster.current_tendsto
        cluster.tail_tendsto cluster.ratio_tendsto hratio who hbindingWho
        (hcurrentPos who)
    simpa only [analysis.soloMatrix_eq] using hzero
  apply source.not_hasHomogeneous_fullNormalizedSoloMatrix
  refine ⟨cluster.limit.2.1, ?_, ?_⟩
  · intro who
    have hzero := hrow who
    change 0 ≤ ∑ owner, cluster.tailLimit owner *
      QuittingLCPClassification.normalizedSoloMatrix reward who owner
    have hzero' : (∑ owner, cluster.tailLimit owner *
        QuittingLCPClassification.normalizedSoloMatrix reward who owner) = 0 := by
      simpa [mul_comm] using hzero
    rw [hzero']
  · intro who
    have hzero := hrow who
    have hzero' : (∑ owner, cluster.tailLimit owner *
        QuittingLCPClassification.normalizedSoloMatrix reward who owner) = 0 := by
      simpa [mul_comm] using hzero
    change cluster.tailLimit who * (∑ owner, cluster.tailLimit owner *
      QuittingLCPClassification.normalizedSoloMatrix reward who owner) = 0
    rw [hzero', mul_zero]

/-- In the diffuse full-binding case, the positive support of the limiting
current hazard has cardinality at most three. -/
theorem currentSupport_card_le_three_of_ratioLimit_eq_zero_of_fullBinding
    (cluster : QuittingForwardExactCapTail.CompactHazardCluster flow.forward)
    (hbinding : flow.forward.bindingFinset = Finset.univ)
    (hratio : cluster.ratioLimit = 0) :
    (FinFourStrictRayCompactCurrentSupport cluster).card ≤ 3 := by
  have hnotAll : ¬∀ who : Fin 4, 0 < cluster.currentLimit who := by
    intro hall
    exact not_ratioLimit_eq_zero_and_all_currentLimit_pos_of_fullBinding
      (flow := flow) cluster hbinding ⟨hratio, hall⟩
  push Not at hnotAll
  obtain ⟨missing, hmissing⟩ := hnotAll
  have hzero : cluster.currentLimit missing = 0 :=
    le_antisymm hmissing (cluster.currentLimit_nonneg missing)
  have hproper : FinFourStrictRayCompactCurrentSupport cluster ⊂
      (Finset.univ : Finset (Fin 4)) := by
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨Finset.filter_subset _ _, ?_⟩
    intro heq
    have hmem : missing ∈ FinFourStrictRayCompactCurrentSupport cluster := by
      rw [heq]
      exact Finset.mem_univ missing
    simp [FinFourStrictRayCompactCurrentSupport, hzero] at hmem
  have hcard := Finset.card_lt_card hproper
  have hcard' : (FinFourStrictRayCompactCurrentSupport cluster).card < 4 := by
    simpa using hcard
  omega

/-- Actual source-retaining compact reduction of the full-binding ray.  The
same flow has a jointly convergent cluster which is either ballistic or has
effective current support of cardinality at most three. -/
theorem nonempty_compactCluster_ratioLimit_pos_or_currentSupport_card_le_three
    (flow : FinFourStrictRayForwardExactCapTail packet)
    (hbinding : flow.forward.bindingFinset = Finset.univ) :
    ∃ cluster : QuittingForwardExactCapTail.CompactHazardCluster flow.forward,
      0 < cluster.ratioLimit ∨
        (FinFourStrictRayCompactCurrentSupport cluster).Nonempty ∧
          (FinFourStrictRayCompactCurrentSupport cluster).card ≤ 3 := by
  obtain ⟨cluster⟩ := flow.forward.nonempty_compactHazardCluster
  refine ⟨cluster, ?_⟩
  by_cases hratio : cluster.ratioLimit = 0
  · exact Or.inr ⟨compactCurrentSupport_nonempty (flow := flow) cluster,
      currentSupport_card_le_three_of_ratioLimit_eq_zero_of_fullBinding
        (flow := flow) cluster hbinding hratio⟩
  · exact Or.inl (lt_of_le_of_ne cluster.ratioLimit_nonneg (Ne.symm hratio))

end FinFourOwnerCompressedMinimumReturnForcedPairPacket

end GameTheory
