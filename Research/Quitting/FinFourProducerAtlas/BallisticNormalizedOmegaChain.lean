/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors.
-/

import MathUE.Topology.SourceOmegaChain
import Research.Quitting.FinFourProducerAtlas.FullBindingPointwiseSupportBallistic

/-!
# Source-compatible omega chain of a ballistic normalized Fin4 ray

An eventually positive renewal-ratio floor places the actual normalized
hazard states in one compact box.  A common compact extraction then produces
a bi-infinite path whose every finite window is approached by complete
windows of the same actual strict ray.  Exact renewal passes directly to the
limit; the checked tail-normalized collision theorems give the limiting
inequality and complementarity at every integer node.

The output contains normalized current hazards, normalized tail hazards, and
renewal ratios only.  It contains no absolute root hazard, payoff vector,
stationary realization, periodic Bellman seam, or terminal consumer.
-/

noncomputable section

namespace GameTheory

open Filter Math Math.Probability Set

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

/-- Compact normalized state with a literal positive renewal-ratio floor. -/
abbrev FinFourBallisticNormalizedState (eta : ℝ) :=
  stdSimplex ℝ (Fin 4) × stdSimplex ℝ (Fin 4) × Set.Icc eta 1

/-- Same-ray data placing every retained tail date in one ballistic compact
box.  The finite cutoff is retained rather than silently deleted. -/
structure FinFourUniformlyBallisticNormalizedSource
    (flow : FinFourStrictRayForwardExactCapTail packet) where
  fullBinding : flow.forward.bindingFinset = Finset.univ
  eta : ℝ
  eta_pos : 0 < eta
  cutoff : ℕ
  renewalRatio_ge : ∀ time,
    eta ≤ flow.forward.renewalRatio (cutoff + time)

namespace FinFourUniformlyBallisticNormalizedSource

variable (data : FinFourUniformlyBallisticNormalizedSource flow)

/-- The complete normalized state at one retained actual ray date. -/
def stateAt (time : ℕ) : FinFourBallisticNormalizedState data.eta :=
  (flow.forward.currentHazardSimplex (data.cutoff + time),
    flow.forward.tailAverageSimplex (data.cutoff + time),
    ⟨flow.forward.renewalRatio (data.cutoff + time),
      data.renewalRatio_ge time,
      flow.forward.renewalRatio_le_one (data.cutoff + time)⟩)

/-- The source date represented by a retained normalized index. -/
def actualDate (time : ℕ) : ℕ := data.cutoff + time

@[simp] theorem stateAt_current (time : ℕ) (who : Fin 4) :
    (data.stateAt time).1.val who =
      flow.forward.currentHazard (data.actualDate time) who := rfl

@[simp] theorem stateAt_tail (time : ℕ) (who : Fin 4) :
    (data.stateAt time).2.1.val who =
      flow.forward.tailAverage (data.actualDate time) who := rfl

@[simp] theorem stateAt_ratio (time : ℕ) :
    ((data.stateAt time).2.2 : ℝ) =
      flow.forward.renewalRatio (data.actualDate time) := rfl

/-- Exact renewal relation on normalized states. -/
def IsRenewalEdge
    (current next : FinFourBallisticNormalizedState data.eta) : Prop :=
  ∀ who, current.2.1.val who =
    (current.2.2 : ℝ) * current.1.val who +
      (1 - (current.2.2 : ℝ)) * next.2.1.val who

theorem isClosed_renewalEdgeGraph :
    IsClosed {edge : FinFourBallisticNormalizedState data.eta ×
        FinFourBallisticNormalizedState data.eta |
      data.IsRenewalEdge edge.1 edge.2} := by
  have heq : {edge : FinFourBallisticNormalizedState data.eta ×
        FinFourBallisticNormalizedState data.eta |
      data.IsRenewalEdge edge.1 edge.2} =
      ⋂ who, {edge : FinFourBallisticNormalizedState data.eta ×
          FinFourBallisticNormalizedState data.eta |
        edge.1.2.1.val who =
          (edge.1.2.2 : ℝ) * edge.1.1.val who +
            (1 - (edge.1.2.2 : ℝ)) * edge.2.2.1.val who} := by
    ext edge
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    rfl
  rw [heq]
  apply isClosed_iInter
  intro who
  have hcurrent : Continuous (fun edge :
      FinFourBallisticNormalizedState data.eta ×
        FinFourBallisticNormalizedState data.eta ↦
      edge.1.1.val who) :=
    ((continuous_apply who).comp continuous_subtype_val).comp
      (continuous_fst.comp continuous_fst)
  have htail : Continuous (fun edge :
      FinFourBallisticNormalizedState data.eta ×
        FinFourBallisticNormalizedState data.eta ↦
      edge.1.2.1.val who) :=
    ((continuous_apply who).comp continuous_subtype_val).comp
      ((continuous_fst.comp continuous_snd).comp continuous_fst)
  have hratio : Continuous (fun edge :
      FinFourBallisticNormalizedState data.eta ×
        FinFourBallisticNormalizedState data.eta ↦
      (edge.1.2.2 : ℝ)) :=
    continuous_subtype_val.comp
      ((continuous_snd.comp continuous_snd).comp continuous_fst)
  have hnextTail : Continuous (fun edge :
      FinFourBallisticNormalizedState data.eta ×
        FinFourBallisticNormalizedState data.eta ↦
      edge.2.2.1.val who) :=
    ((continuous_apply who).comp continuous_subtype_val).comp
      ((continuous_fst.comp continuous_snd).comp continuous_snd)
  exact isClosed_eq htail
    ((hratio.mul hcurrent).add
      (continuous_const.sub hratio |>.mul hnextTail))

theorem stateAt_renewal (time : ℕ) :
    data.IsRenewalEdge (data.stateAt time) (data.stateAt (time + 1)) := by
  intro who
  simpa [actualDate, Nat.add_assoc] using
    flow.forward.tailAverage_renewal (data.cutoff + time) who

/-- Limiting singleton-plus-collision work at one normalized state. -/
def work
    (state : FinFourBallisticNormalizedState data.eta) (who : Fin 4) : ℝ :=
  (∑ owner, flow.analysis.normalized.soloMatrix who owner *
      state.2.1.val owner) +
    (state.2.2 : ℝ) *
      ∑ owner, flow.analysis.normalized.collisionMatrix who owner *
        state.1.val owner

/-- The closed normalized ballistic relation. -/
def IsBallisticEdge
    (current next : FinFourBallisticNormalizedState data.eta) : Prop :=
  data.IsRenewalEdge current next ∧
    (∀ who, data.work current who ≤ 0) ∧
      ∀ who, current.1.val who * data.work current who = 0

end FinFourUniformlyBallisticNormalizedSource

/-- A source-compatible bi-infinite normalized chain.  `extraction` stores
the one common center subsequence needed for all finite-window provenance. -/
structure FinFourBallisticNormalizedOmegaChain
    (data : FinFourUniformlyBallisticNormalizedSource flow) where
  extraction : Math.Topology.SourceOmegaChain data.stateAt
  edge : ∀ offset,
    data.IsBallisticEdge (extraction.path offset)
      (extraction.path (offset + 1))

namespace FinFourBallisticNormalizedOmegaChain

variable {data : FinFourUniformlyBallisticNormalizedSource flow}
variable (omega : FinFourBallisticNormalizedOmegaChain data)

def state (offset : ℤ) : FinFourBallisticNormalizedState data.eta :=
  omega.extraction.path offset

def sourceIndex (offset : ℤ) (rank : ℕ) : ℕ :=
  omega.extraction.sourceIndex offset rank

def actualDate (offset : ℤ) (rank : ℕ) : ℕ :=
  data.actualDate (omega.sourceIndex offset rank)

theorem sourceIndex_strictMono (offset : ℤ) :
    StrictMono (omega.sourceIndex offset) :=
  omega.extraction.sourceIndex_strictMono offset

theorem actualDate_strictMono (offset : ℤ) :
    StrictMono (omega.actualDate offset) := by
  intro first second hlt
  exact Nat.add_lt_add_left (omega.sourceIndex_strictMono offset hlt)
    data.cutoff

/-- Every omega coordinate is the limit of strict actual dates from the same
source ray. -/
theorem source_state_tendsto (offset : ℤ) :
    Tendsto (fun rank ↦ data.stateAt (omega.sourceIndex offset rank))
      atTop (nhds (omega.state offset)) :=
  omega.extraction.source_coordinate_tendsto offset

theorem source_current_tendsto (offset : ℤ) (who : Fin 4) :
    Tendsto (fun rank ↦ flow.forward.currentHazard
      (omega.actualDate offset rank) who) atTop
      (nhds ((omega.state offset).1.val who)) := by
  have hcontinuous : Continuous
      (fun state : FinFourBallisticNormalizedState data.eta ↦
        state.1.val who) :=
    ((continuous_apply who).comp continuous_subtype_val).comp continuous_fst
  have hlimit := hcontinuous.continuousAt.tendsto.comp
    (omega.source_state_tendsto offset)
  change Tendsto (fun rank ↦
    (data.stateAt (omega.sourceIndex offset rank)).1.val who) atTop
      (nhds ((omega.state offset).1.val who)) at hlimit
  simpa only [FinFourUniformlyBallisticNormalizedSource.stateAt_current,
    actualDate] using hlimit

theorem source_tail_tendsto (offset : ℤ) (who : Fin 4) :
    Tendsto (fun rank ↦ flow.forward.tailAverage
      (omega.actualDate offset rank) who) atTop
      (nhds ((omega.state offset).2.1.val who)) := by
  have hcontinuous : Continuous
      (fun state : FinFourBallisticNormalizedState data.eta ↦
        state.2.1.val who) :=
    ((continuous_apply who).comp continuous_subtype_val).comp
      (continuous_fst.comp continuous_snd)
  have hlimit := hcontinuous.continuousAt.tendsto.comp
    (omega.source_state_tendsto offset)
  change Tendsto (fun rank ↦
    (data.stateAt (omega.sourceIndex offset rank)).2.1.val who) atTop
      (nhds ((omega.state offset).2.1.val who)) at hlimit
  simpa only [FinFourUniformlyBallisticNormalizedSource.stateAt_tail,
    actualDate] using hlimit

theorem source_ratio_tendsto (offset : ℤ) :
    Tendsto (fun rank ↦ flow.forward.renewalRatio
      (omega.actualDate offset rank)) atTop
      (nhds ((omega.state offset).2.2 : ℝ)) := by
  have hcontinuous : Continuous
      (fun state : FinFourBallisticNormalizedState data.eta ↦
        (state.2.2 : ℝ)) :=
    continuous_subtype_val.comp (continuous_snd.comp continuous_snd)
  have hlimit := hcontinuous.continuousAt.tendsto.comp
    (omega.source_state_tendsto offset)
  change Tendsto (fun rank ↦
    ((data.stateAt (omega.sourceIndex offset rank)).2.2 : ℝ)) atTop
      (nhds ((omega.state offset).2.2 : ℝ)) at hlimit
  simpa only [FinFourUniformlyBallisticNormalizedSource.stateAt_ratio,
    actualDate] using hlimit

/-- Every complete finite normalized window has the same-source convergence
provided by the common center extraction. -/
theorem finiteWindow_tendsto (radius : ℕ) :
    Tendsto
      (fun rank ↦ Math.Topology.SourceOmegaChain.finiteWindow radius
        (Math.Topology.centeredSequence data.stateAt
          (omega.extraction.centers rank)))
      atTop
      (nhds (Math.Topology.SourceOmegaChain.finiteWindow radius
        omega.extraction.path)) :=
  omega.extraction.finiteWindow_tendsto radius

/-- Literal consecutive windows of retained actual normalized states converge
to the omega window.  Thus the finite-window provenance is stronger than a
collection of independently selected coordinate subsequences. -/
theorem sourceFiniteWindow_tendsto (radius : ℕ) :
    Tendsto
      (fun rank ↦ Math.Topology.SourceOmegaChain.sourceFiniteWindow
        data.stateAt radius (omega.extraction.centers rank))
      atTop
      (nhds (Math.Topology.SourceOmegaChain.finiteWindow radius
        omega.extraction.path)) :=
  omega.extraction.sourceFiniteWindow_tendsto radius

/-- The literal ray date at one slot of a complete source window. -/
def sourceWindowDate (radius : ℕ) (rank : ℕ)
    (slot : Fin (2 * radius + 1)) : ℕ :=
  data.actualDate (omega.extraction.centers rank - radius + slot)

@[simp] theorem sourceWindowDate_eq (radius : ℕ) (rank : ℕ)
    (slot : Fin (2 * radius + 1)) :
    omega.sourceWindowDate radius rank slot =
      data.cutoff + (omega.extraction.centers rank - radius + slot) := rfl

theorem renewal (offset : ℤ) :
    data.IsRenewalEdge (omega.state offset) (omega.state (offset + 1)) :=
  (omega.edge offset).1

theorem work_nonpos (offset : ℤ) (who : Fin 4) :
    data.work (omega.state offset) who ≤ 0 :=
  (omega.edge offset).2.1 who

theorem current_work_eq_zero (offset : ℤ) (who : Fin 4) :
    (omega.state offset).1.val who * data.work (omega.state offset) who = 0 :=
  (omega.edge offset).2.2 who

/-- The path stores normalized data only.  This name-only predicate makes the
missing absolute lift explicit and is not a consumer. -/
def HasAbsoluteNashBellmanLift : Prop :=
  ∃ (payoff : ℤ → Payoff (Fin 4)) (root : ℤ → Fin 4 → PMF Bool),
    ∀ offset,
      IsεQuittingRootNash reward (payoff offset) 0 (root offset) ∧
        payoff (offset + 1) =
          quittingRootSuccessorPayoff reward (payoff offset) (root offset)

end FinFourBallisticNormalizedOmegaChain

namespace FinFourUniformlyBallisticNormalizedSource

variable (data : FinFourUniformlyBallisticNormalizedSource flow)

/-- Compact extraction plus the checked limiting collision identities produce
the source-compatible ballistic omega chain. -/
theorem nonempty_omegaChain :
    Nonempty (FinFourBallisticNormalizedOmegaChain data) := by
  obtain ⟨extraction⟩ := Math.Topology.nonempty_sourceOmegaChain data.stateAt
  refine ⟨{ extraction := extraction, edge := ?_ }⟩
  intro offset
  have hrenewal : data.IsRenewalEdge
      (extraction.path offset) (extraction.path (offset + 1)) :=
    extraction.relation data.IsRenewalEdge data.isClosed_renewalEdgeGraph
      data.stateAt_renewal offset
  let subseq : ℕ → ℕ := fun rank ↦
    data.actualDate (extraction.sourceIndex offset rank)
  have hsubseq : StrictMono subseq := by
    intro first second hlt
    exact Nat.add_lt_add_left
      (extraction.sourceIndex_strictMono offset hlt) data.cutoff
  have hstate := extraction.source_coordinate_tendsto offset
  have hcurrent : ∀ who, Tendsto (fun rank ↦
      flow.forward.currentHazard (subseq rank) who) atTop
      (nhds ((extraction.path offset).1.val who)) := by
    intro who
    have hcontinuous : Continuous
        (fun state : FinFourBallisticNormalizedState data.eta ↦
          state.1.val who) :=
      ((continuous_apply who).comp continuous_subtype_val).comp continuous_fst
    have hlimit := hcontinuous.continuousAt.tendsto.comp hstate
    change Tendsto (fun rank ↦
      (data.stateAt (extraction.sourceIndex offset rank)).1.val who) atTop
        (nhds ((extraction.path offset).1.val who)) at hlimit
    simpa only [stateAt_current, subseq, actualDate] using hlimit
  have htail : ∀ who, Tendsto (fun rank ↦
      flow.forward.tailAverage (subseq rank) who) atTop
      (nhds ((extraction.path offset).2.1.val who)) := by
    intro who
    have hcontinuous : Continuous
        (fun state : FinFourBallisticNormalizedState data.eta ↦
          state.2.1.val who) :=
      ((continuous_apply who).comp continuous_subtype_val).comp
        (continuous_fst.comp continuous_snd)
    have hlimit := hcontinuous.continuousAt.tendsto.comp hstate
    change Tendsto (fun rank ↦
      (data.stateAt (extraction.sourceIndex offset rank)).2.1.val who) atTop
        (nhds ((extraction.path offset).2.1.val who)) at hlimit
    simpa only [stateAt_tail, subseq, actualDate] using hlimit
  have hratio : Tendsto (fun rank ↦
      flow.forward.renewalRatio (subseq rank)) atTop
      (nhds ((extraction.path offset).2.2 : ℝ)) := by
    have hcontinuous : Continuous
        (fun state : FinFourBallisticNormalizedState data.eta ↦
          (state.2.2 : ℝ)) :=
      continuous_subtype_val.comp (continuous_snd.comp continuous_snd)
    have hlimit := hcontinuous.continuousAt.tendsto.comp hstate
    change Tendsto (fun rank ↦
      ((data.stateAt (extraction.sourceIndex offset rank)).2.2 : ℝ)) atTop
        (nhds ((extraction.path offset).2.2 : ℝ)) at hlimit
    simpa only [stateAt_ratio, subseq, actualDate] using hlimit
  refine ⟨hrenewal, ?_, ?_⟩
  · intro who
    have hbinding : who ∈ flow.forward.bindingFinset := by
      rw [data.fullBinding]
      exact Finset.mem_univ who
    have hnonpos := flow.analysis.normalized.subseq_collision_nonpos
      subseq hsubseq (extraction.path offset).1.val
        (extraction.path offset).2.1.val
        (extraction.path offset).2.2 hcurrent htail hratio who hbinding
    unfold work
    linarith
  · intro who
    have hbinding : who ∈ flow.forward.bindingFinset := by
      rw [data.fullBinding]
      exact Finset.mem_univ who
    exact flow.analysis.normalized.subseq_collision_complementarity
      subseq hsubseq (extraction.path offset).1.val
        (extraction.path offset).2.1.val
        (extraction.path offset).2.2 hcurrent htail hratio who hbinding

end FinFourUniformlyBallisticNormalizedSource

/-- Eventual ballisticity gives a literal cutoff-indexed source record. -/
theorem nonempty_uniformlyBallisticNormalizedSource_of_eventually
    (flow : FinFourStrictRayForwardExactCapTail packet)
    (hbinding : flow.forward.bindingFinset = Finset.univ)
    {eta : ℝ} (heta : 0 < eta)
    (hballistic : ∀ᶠ time in atTop,
      eta ≤ flow.forward.renewalRatio time) :
    Nonempty (FinFourUniformlyBallisticNormalizedSource flow) := by
  obtain ⟨cutoff, hcutoff⟩ := eventually_atTop.1 hballistic
  exact ⟨{
    fullBinding := hbinding
    eta := eta
    eta_pos := heta
    cutoff := cutoff
    renewalRatio_ge := fun time ↦ hcutoff (cutoff + time) (Nat.le_add_right _ _)
  }⟩

/-- Actual full finite support and full limiting binding produce the same-ray
source-compatible omega chain without a supplied normalized certificate. -/
theorem nonempty_ballisticNormalizedOmegaChain_of_fullBinding_of_eventually_all_currentHazard_pos
    (flow : FinFourStrictRayForwardExactCapTail packet)
    (hbinding : flow.forward.bindingFinset = Finset.univ)
    (hpositive : ∀ᶠ time in atTop, ∀ who : Fin 4,
      0 < flow.forward.currentHazard time who) :
    ∃ data : FinFourUniformlyBallisticNormalizedSource flow,
      Nonempty (FinFourBallisticNormalizedOmegaChain data) := by
  obtain ⟨eta, heta, hballistic⟩ :=
    eventually_renewalRatio_ge_pos_of_fullBinding_of_eventually_all_currentHazard_pos
      flow hbinding hpositive
  obtain ⟨data⟩ :=
    nonempty_uniformlyBallisticNormalizedSource_of_eventually
      flow hbinding heta hballistic
  exact ⟨data, data.nonempty_omegaChain⟩

end FinFourOwnerCompressedMinimumReturnForcedPairPacket

end GameTheory
