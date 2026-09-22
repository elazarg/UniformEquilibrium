/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors.
-/

import MathUE.Topology.CompactOrbitOccupation
import Research.Quitting.FinFourProducerAtlas.BallisticNormalizedOmegaChain

/-!
# Balanced occupation law of a ballistic normalized Fin4 omega chain

The nonnegative half of the source-compatible omega chain has a weak
empirical edge limit.  Its two state marginals agree and its support lies in
the exact closed ballistic relation.  The law remains a law of normalized
states; it is not a stationary quitting profile or a Bellman consumer.
-/

noncomputable section

namespace GameTheory

open Filter _root_.Math _root_.Math.Probability MeasureTheory Set

variable {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
variable {bound : ℝ}
variable {source : FinFourMinimumAtomProducer reward bound}
variable {returnSource :
  FinFourOwnerCompressedMinimumReturnForcedPairSource source}
variable {lambda : ℝ}

local instance : MeasurableSpace (Convexity.StdSimplex ℝ (Fin 4)) :=
  borel _

local instance : BorelSpace (Convexity.StdSimplex ℝ (Fin 4)) :=
  ⟨rfl⟩

namespace FinFourOwnerCompressedMinimumReturnForcedPairPacket

variable {packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
  returnSource lambda}
variable {flow : FinFourStrictRayForwardExactCapTail packet}
variable {data : FinFourUniformlyBallisticNormalizedSource flow}

namespace FinFourUniformlyBallisticNormalizedSource

variable (data : FinFourUniformlyBallisticNormalizedSource flow)

theorem continuous_work (who : Fin 4) :
    Continuous (fun state : FinFourBallisticNormalizedState data.eta ↦
      data.work state who) := by
  have htail (owner : Fin 4) : Continuous
      (fun state : FinFourBallisticNormalizedState data.eta ↦
        state.2.1.weights owner) :=
    (Convexity.StdSimplex.continuous_weights_apply ℝ owner).comp
      (continuous_fst.comp continuous_snd)
  have hcurrent (owner : Fin 4) : Continuous
      (fun state : FinFourBallisticNormalizedState data.eta ↦
        state.1.weights owner) :=
    (Convexity.StdSimplex.continuous_weights_apply ℝ owner).comp continuous_fst
  have hratio : Continuous
      (fun state : FinFourBallisticNormalizedState data.eta ↦
        (state.2.2 : ℝ)) :=
    continuous_subtype_val.comp (continuous_snd.comp continuous_snd)
  unfold work
  apply Continuous.add
  · apply continuous_finsetSum
    intro owner _
    exact continuous_const.mul (htail owner)
  · apply Continuous.mul hratio
    apply continuous_finsetSum
    intro owner _
    exact continuous_const.mul (hcurrent owner)

theorem isClosed_ballisticEdgeGraph :
    IsClosed {edge : FinFourBallisticNormalizedState data.eta ×
        FinFourBallisticNormalizedState data.eta |
      data.IsBallisticEdge edge.1 edge.2} := by
  let renewal : Set (FinFourBallisticNormalizedState data.eta ×
      FinFourBallisticNormalizedState data.eta) :=
    {edge | data.IsRenewalEdge edge.1 edge.2}
  let feasible : Set (FinFourBallisticNormalizedState data.eta ×
      FinFourBallisticNormalizedState data.eta) :=
    {edge | ∀ who, data.work edge.1 who ≤ 0}
  let complementary : Set (FinFourBallisticNormalizedState data.eta ×
      FinFourBallisticNormalizedState data.eta) :=
    {edge | ∀ who, edge.1.1.weights who * data.work edge.1 who = 0}
  have hrenewal : IsClosed renewal := data.isClosed_renewalEdgeGraph
  have hfeasible : IsClosed feasible := by
    rw [show feasible = ⋂ who, {edge :
        FinFourBallisticNormalizedState data.eta ×
          FinFourBallisticNormalizedState data.eta |
        data.work edge.1 who ≤ 0} by
      ext edge
      simp [feasible]]
    apply isClosed_iInter
    intro who
    exact isClosed_le ((data.continuous_work who).comp continuous_fst)
      continuous_const
  have hcomplementary : IsClosed complementary := by
    rw [show complementary = ⋂ who,
        {edge : FinFourBallisticNormalizedState data.eta ×
            FinFourBallisticNormalizedState data.eta |
          edge.1.1.weights who * data.work edge.1 who = 0} by
      ext edge
      simp [complementary]]
    apply isClosed_iInter
    intro who
    have hcurrent : Continuous (fun edge :
        FinFourBallisticNormalizedState data.eta ×
          FinFourBallisticNormalizedState data.eta ↦
        edge.1.1.weights who) :=
      (Convexity.StdSimplex.continuous_weights_apply ℝ who).comp
        (continuous_fst.comp continuous_fst)
    exact isClosed_eq
      (hcurrent.mul ((data.continuous_work who).comp continuous_fst))
      continuous_const
  have heq : {edge : FinFourBallisticNormalizedState data.eta ×
        FinFourBallisticNormalizedState data.eta |
      data.IsBallisticEdge edge.1 edge.2} =
      renewal ∩ feasible ∩ complementary := by
    ext edge
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, renewal, feasible,
      complementary, IsBallisticEdge]
    aesop
  rw [heq]
  exact (hrenewal.inter hfeasible).inter hcomplementary

end FinFourUniformlyBallisticNormalizedSource

namespace FinFourBallisticNormalizedOmegaChain

variable (omega : FinFourBallisticNormalizedOmegaChain data)

/-- The nonnegative half of the bi-infinite omega chain. -/
def forwardState (time : ℕ) : FinFourBallisticNormalizedState data.eta :=
  omega.state (Int.ofNat time)

theorem forwardState_edge (time : ℕ) :
    data.IsBallisticEdge (omega.forwardState time)
      (omega.forwardState (time + 1)) := by
  have hsuccessor : Int.ofNat time + 1 = Int.ofNat (time + 1) := by
    norm_num
  simpa only [forwardState, state, hsuccessor] using
    omega.edge (Int.ofNat time)

/-- Balanced empirical edge occupation retained from this exact omega chain. -/
structure FinFourBallisticNormalizedOccupation where
  occupation : Math.Topology.CompactForwardOccupation omega.forwardState

namespace FinFourBallisticNormalizedOccupation

variable {omega : FinFourBallisticNormalizedOmegaChain data}
variable (occupation : FinFourBallisticNormalizedOccupation omega)

def law : ProbabilityMeasure
    (FinFourBallisticNormalizedState data.eta ×
      FinFourBallisticNormalizedState data.eta) :=
  occupation.occupation.law

def horizons : ℕ → ℕ := occupation.occupation.horizons

theorem horizons_strictMono : StrictMono occupation.horizons :=
  occupation.occupation.horizons_strictMono

theorem empirical_tendsto :
    Tendsto (fun rank ↦ Math.Topology.empiricalEdgeLaw omega.forwardState
      (occupation.horizons rank)) atTop (nhds occupation.law) :=
  occupation.occupation.empirical_tendsto

/-- Exact stationarity of the normalized state marginal. -/
theorem marginals_eq :
    occupation.law.map Prod.fst = occupation.law.map Prod.snd :=
  occupation.occupation.marginals_eq

/-- The occupation law is supported on the exact ballistic relation. -/
theorem support_subset_ballisticEdgeGraph :
    (occupation.law : Measure
      (FinFourBallisticNormalizedState data.eta ×
        FinFourBallisticNormalizedState data.eta)).support ⊆
      {edge | data.IsBallisticEdge edge.1 edge.2} :=
  occupation.occupation.support_subset_edgeGraph data.IsBallisticEdge
    data.isClosed_ballisticEdgeGraph omega.forwardState_edge

end FinFourBallisticNormalizedOccupation

/-- Every source-compatible omega chain has a balanced normalized
occupation law. -/
theorem nonempty_normalizedOccupation :
    Nonempty (FinFourBallisticNormalizedOccupation omega) := by
  obtain ⟨occupation⟩ :=
    Math.Topology.CompactForwardOccupation.nonempty_compactForwardOccupation
      omega.forwardState
  exact ⟨⟨occupation⟩⟩

end FinFourBallisticNormalizedOmegaChain

end FinFourOwnerCompressedMinimumReturnForcedPairPacket

end GameTheory
