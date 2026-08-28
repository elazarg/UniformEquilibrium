/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import Research.Quitting.FinFourProducerAtlas.StrictRayFullBindingDiffuseReduction
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticFinFourOffMinimumChargedBlockerGate

/-!
# Full finite support forces ballistic renewal on a full-binding Fin4 ray

Exact finite complementarity is stronger than limiting complementarity.  If
one current normalized hazard coordinate is positive eventually along a
selected subsequence, its finite endpoint slack is literally zero eventually,
even when the coordinate converges to zero.  In the diffuse ratio branch this
forces the corresponding homogeneous solo-flow equation.

For a source-attached strict Fin4 ray, eventual positivity at every finite
coordinate and full limiting binding therefore exclude every zero-ratio
cluster.  Compactness upgrades the cluster statement to one eventual positive
lower bound on the actual renewal-ratio sequence.

No lower bound on an individual current coordinate is assumed.  The theorem
does not consume the surviving ballistic branch, the partial finite-support
branch, or produce a terminal profile or uniform equilibrium.
-/

noncomputable section

namespace GameTheory

open Filter Math Math.LinearProgramming Set

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

namespace QuittingTailNormalizedCapFlow

variable {ray : QuittingForwardExactCapTail reward}

/-- Limit of the finite scaled endpoint slacks along one jointly convergent
hazard subsequence.  This is the unmultiplied precursor of limiting
complementarity. -/
theorem subseq_scaledEndpointSlack_tendsto
    (flow : QuittingTailNormalizedCapFlow reward ray)
    (subseq : ℕ → ℕ) (hsubseq : StrictMono subseq)
    (currentLimit tailLimit : ι → ℝ) (ratioLimit : ℝ)
    (hcurrent : ∀ who, Tendsto (fun rank ↦
      ray.currentHazard (subseq rank) who) atTop (nhds (currentLimit who)))
    (htail : ∀ who, Tendsto (fun rank ↦
      ray.tailAverage (subseq rank) who) atTop (nhds (tailLimit who)))
    (hratio : Tendsto (fun rank ↦ ray.renewalRatio (subseq rank))
      atTop (nhds ratioLimit))
    (who : ι) (hbinding : who ∈ ray.bindingFinset) :
    Tendsto (fun rank ↦
      ray.renewalRatio (subseq rank) *
        flow.endpointSlack (subseq rank) who) atTop
      (nhds (-(∑ owner, flow.soloMatrix who owner * tailLimit owner) -
        ratioLimit *
          ∑ owner, flow.collisionMatrix who owner * currentLimit owner)) := by
  have hcap : Tendsto (fun rank ↦
      (ray.capLimit who - (ray.pair (subseq rank)).2 who) /
          ray.tailMass (subseq rank) -
        ∑ owner, flow.soloMatrix who owner *
          ray.tailAverage (subseq rank) owner) atTop (nhds 0) := by
    simpa [Function.comp_def] using
      (flow.tailNormalized_capFlow who hbinding).comp hsubseq.tendsto_atTop
  have hmatrix : Tendsto (fun rank ↦
      ∑ owner, flow.soloMatrix who owner *
        ray.tailAverage (subseq rank) owner) atTop
      (nhds (∑ owner, flow.soloMatrix who owner * tailLimit owner)) := by
    apply tendsto_finsetSum
    intro owner _
    exact (tendsto_const_nhds : Tendsto
      (fun _rank : ℕ ↦ flow.soloMatrix who owner) atTop
        (nhds (flow.soloMatrix who owner))).mul (htail owner)
  have hcapLimit : Tendsto (fun rank ↦
      (ray.capLimit who - (ray.pair (subseq rank)).2 who) /
        ray.tailMass (subseq rank)) atTop
      (nhds (∑ owner, flow.soloMatrix who owner * tailLimit owner)) := by
    convert hcap.add hmatrix using 1 <;> simp
  have hcollision : Tendsto (fun rank ↦
      ∑ owner, flow.collisionMatrix who owner *
        ray.currentHazard (subseq rank) owner) atTop
      (nhds (∑ owner,
        flow.collisionMatrix who owner * currentLimit owner)) := by
    apply tendsto_finsetSum
    intro owner _
    exact (tendsto_const_nhds : Tendsto
      (fun _rank : ℕ ↦ flow.collisionMatrix who owner) atTop
        (nhds (flow.collisionMatrix who owner))).mul (hcurrent owner)
  have herror := (flow.collisionError_tendsto_zero who hbinding).comp
    hsubseq.tendsto_atTop
  have hright := hcapLimit.neg.sub (hratio.mul hcollision) |>.add herror
  simpa only [Function.comp_apply, add_zero] using hright.congr'
    (Eventually.of_forall fun rank ↦
      (flow.endpoint_decomposition (subseq rank) who).symm)

/-- Diffuse renewal plus eventual positivity of the finite current coordinate
forces the homogeneous solo-flow equation, even if its limiting current
coordinate is zero. -/
theorem subseq_diffuse_eventually_currentHazard_pos_solo_eq_zero
    (flow : QuittingTailNormalizedCapFlow reward ray)
    (subseq : ℕ → ℕ) (hsubseq : StrictMono subseq)
    (currentLimit tailLimit : ι → ℝ) (ratioLimit : ℝ)
    (hcurrent : ∀ who, Tendsto (fun rank ↦
      ray.currentHazard (subseq rank) who) atTop (nhds (currentLimit who)))
    (htail : ∀ who, Tendsto (fun rank ↦
      ray.tailAverage (subseq rank) who) atTop (nhds (tailLimit who)))
    (hratio : Tendsto (fun rank ↦ ray.renewalRatio (subseq rank))
      atTop (nhds ratioLimit))
    (hratioZero : ratioLimit = 0)
    (who : ι) (hbinding : who ∈ ray.bindingFinset)
    (hpositive : ∀ᶠ rank in atTop,
      0 < ray.currentHazard (subseq rank) who) :
    ∑ owner, flow.soloMatrix who owner * tailLimit owner = 0 := by
  have hlimit := flow.subseq_scaledEndpointSlack_tendsto subseq hsubseq
    currentLimit tailLimit ratioLimit hcurrent htail hratio who hbinding
  have hslackZero : ∀ᶠ rank in atTop,
      flow.endpointSlack (subseq rank) who = 0 := by
    filter_upwards [hpositive] with rank hpos
    exact (mul_eq_zero.mp
      (flow.current_complementarity (subseq rank) who)).resolve_left hpos.ne'
  have hzero : Tendsto (fun rank ↦
      ray.renewalRatio (subseq rank) *
        flow.endpointSlack (subseq rank) who) atTop (nhds 0) := by
    exact tendsto_const_nhds.congr' <| hslackZero.mono fun rank hslack ↦ by
      simp [hslack]
  have hunique := tendsto_nhds_unique hlimit hzero
  rw [hratioZero, zero_mul, sub_zero] at hunique
  linarith

end QuittingTailNormalizedCapFlow

variable {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
variable {bound : ℝ}
variable {source : FinFourMinimumAtomProducer reward bound}
variable {returnSource :
  FinFourOwnerCompressedMinimumReturnForcedPairSource source}
variable {lambda : ℝ}

namespace FinFourOwnerCompressedMinimumReturnForcedPairPacket

variable {packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
  returnSource lambda}
variable {flow : FinFourStrictRayForwardExactCapTail packet}

/-- On the full binding face, eventual finite full support along one actual
compact cluster forces its renewal-ratio limit to be positive. -/
theorem compactCluster_ratioLimit_pos_of_eventually_all_currentHazard_pos
    (cluster :
      QuittingForwardExactCapTail.CompactHazardCluster flow.forward)
    (hbinding : flow.forward.bindingFinset = Finset.univ)
    (hpositive : ∀ᶠ rank in atTop, ∀ who : Fin 4,
      0 < flow.forward.currentHazard (cluster.subseq rank) who) :
    0 < cluster.ratioLimit := by
  have hratioNe : cluster.ratioLimit ≠ 0 := by
    intro hratioZero
    let analysis := flow.analysis
    have hrow : ∀ who : Fin 4,
        ∑ owner,
            QuittingLCPClassification.normalizedSoloMatrix reward who owner *
              cluster.tailLimit owner = 0 := by
      intro who
      have hbindingWho : who ∈ flow.forward.bindingFinset := by
        rw [hbinding]
        exact Finset.mem_univ who
      have hpositiveWho : ∀ᶠ rank in atTop,
          0 < flow.forward.currentHazard (cluster.subseq rank) who :=
        hpositive.mono fun _ hall ↦ hall who
      have hzero :=
        analysis.normalized.subseq_diffuse_eventually_currentHazard_pos_solo_eq_zero
          cluster.subseq cluster.subseq_strictMono cluster.currentLimit
            cluster.tailLimit cluster.ratioLimit cluster.current_tendsto
            cluster.tail_tendsto cluster.ratio_tendsto hratioZero who
            hbindingWho hpositiveWho
      simpa only [analysis.soloMatrix_eq] using hzero
    apply source.not_hasHomogeneous_fullNormalizedSoloMatrix
    refine ⟨cluster.limit.2.1, ?_, ?_⟩
    · intro who
      change 0 ≤ ∑ owner, cluster.tailLimit owner *
        QuittingLCPClassification.normalizedSoloMatrix reward who owner
      have hzero : (∑ owner, cluster.tailLimit owner *
          QuittingLCPClassification.normalizedSoloMatrix reward who owner) =
          0 := by
        simpa [mul_comm] using hrow who
      rw [hzero]
    · intro who
      have hzero : (∑ owner, cluster.tailLimit owner *
          QuittingLCPClassification.normalizedSoloMatrix reward who owner) =
          0 := by
        simpa [mul_comm] using hrow who
      change cluster.tailLimit who * (∑ owner, cluster.tailLimit owner *
        QuittingLCPClassification.normalizedSoloMatrix reward who owner) = 0
      rw [hzero, mul_zero]
  exact lt_of_le_of_ne cluster.ratioLimit_nonneg (Ne.symm hratioNe)

/-- Actual source-retaining ballistic conclusion.  Eventual positivity of all
four finite current hazards and full limiting binding produce one uniform
eventual lower bound for the renewal ratio of the same strict ray. -/
theorem eventually_renewalRatio_ge_pos_of_fullBinding_of_eventually_all_currentHazard_pos
    (flow : FinFourStrictRayForwardExactCapTail packet)
    (hbinding : flow.forward.bindingFinset = Finset.univ)
    (hpositive : ∀ᶠ time in atTop, ∀ who : Fin 4,
      0 < flow.forward.currentHazard time who) :
    ∃ eta, 0 < eta ∧ ∀ᶠ time in atTop,
      eta ≤ flow.forward.renewalRatio time := by
  rcases exists_eventually_pos_or_strictMono_tendsto_zero
      flow.forward.renewalRatio flow.forward.renewalRatio_nonneg with
    hballistic | ⟨subseq, hsubseq, hratioZero⟩
  · exact hballistic
  · obtain ⟨limit, refinement, hrefinement, hstate⟩ :=
      CompactSpace.tendsto_subseq
        (fun rank ↦ flow.forward.compactHazardState (subseq rank))
    let cluster :
        QuittingForwardExactCapTail.CompactHazardCluster flow.forward := {
      subseq := subseq ∘ refinement
      subseq_strictMono := hsubseq.comp hrefinement
      limit := limit
      state_tendsto := by
        simpa [Function.comp_def] using hstate
    }
    have hratioCluster : cluster.ratioLimit = 0 := by
      apply tendsto_nhds_unique cluster.ratio_tendsto
      simpa [cluster, Function.comp_def] using
        hratioZero.comp hrefinement.tendsto_atTop
    have hpositiveCluster : ∀ᶠ rank in atTop, ∀ who : Fin 4,
        0 < flow.forward.currentHazard (cluster.subseq rank) who := by
      exact (hsubseq.comp hrefinement).tendsto_atTop.eventually hpositive
    have hratioPos :=
      compactCluster_ratioLimit_pos_of_eventually_all_currentHazard_pos
        (flow := flow) cluster hbinding hpositiveCluster
    exact False.elim ((ne_of_gt hratioPos) hratioCluster)

/-- Source-level full-binding dispatch.  The same actual strict ray is either
uniformly ballistic or one fixed player is absent from infinitely many finite
current roots.  The second branch is retained, not consumed. -/
theorem eventually_renewalRatio_ge_pos_or_exists_frequently_currentHazard_eq_zero
    (flow : FinFourStrictRayForwardExactCapTail packet)
    (hbinding : flow.forward.bindingFinset = Finset.univ) :
    (∃ eta, 0 < eta ∧ ∀ᶠ time in atTop,
      eta ≤ flow.forward.renewalRatio time) ∨
      ∃ who : Fin 4, ∃ᶠ time in atTop,
        flow.forward.currentHazard time who = 0 := by
  by_cases hpositive : ∀ᶠ time in atTop, ∀ who : Fin 4,
      0 < flow.forward.currentHazard time who
  · exact Or.inl
      (eventually_renewalRatio_ge_pos_of_fullBinding_of_eventually_all_currentHazard_pos
        flow hbinding hpositive)
  · right
    by_contra hnone
    have hnonzero : ∀ who : Fin 4, ∀ᶠ time in atTop,
        flow.forward.currentHazard time who ≠ 0 := by
      intro who
      rw [← not_frequently]
      intro hfrequent
      exact hnone ⟨who, hfrequent⟩
    apply hpositive
    filter_upwards [(eventually_all_finite Set.finite_univ).2
      (fun who _ ↦ hnonzero who)] with time htime who
    exact lt_of_le_of_ne (flow.forward.currentHazard_nonneg time who)
      (Ne.symm (htime who (Set.mem_univ who)))

end FinFourOwnerCompressedMinimumReturnForcedPairPacket

end GameTheory
