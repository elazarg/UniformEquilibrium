import MathUE.ChargedPathBudget
import UniformEquilibrium.Quitting.Root.NashDefectContinuity

/-! # Floor-free robust charged relation

The state is only a boxed payoff vector. A relation edge stores its source,
one product-root simplex point, and its target. Its defining conditions are
exactly absorption-relative Bellman residual and ordinary Nash regret bounds.
There is no punishment floor or support restriction.
-/

noncomputable section

namespace GameTheory

open Math.ChargedPathBudget Math.Probability Math.PMFProduct Set

variable {player : Type} [Fintype player] [DecidableEq player]
variable {bound : ℝ}

/-- A bare payoff vector in the coordinate box of radius `bound`. -/
abbrev QuittingRobustChargedState (player : Type) (bound : ℝ) :=
  {value : Payoff player // ∀ who, |value who| ≤ bound}

omit [Fintype player] [DecidableEq player] in
theorem isCompact_quittingRobustChargedState (bound : ℝ) :
    IsCompact {value : Payoff player | ∀ who, |value who| ≤ bound} := by
  have hcompact := isCompact_univ_pi (ι := player) (fun _ ↦
    (isCompact_Icc : IsCompact (Set.Icc (-bound) bound : Set ℝ)))
  convert hcompact using 1
  ext value
  simp only [Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, Set.mem_Icc,
    true_implies, abs_le]

instance (bound : ℝ) : CompactSpace (QuittingRobustChargedState player bound) :=
  isCompact_iff_compactSpace.mp (isCompact_quittingRobustChargedState bound)

/-- Raw source/root/target data before imposing the two robust inequalities. -/
abbrev QuittingRobustChargedEdgeData (player : Type) [Fintype player]
    (bound : ℝ) :=
  (QuittingRobustChargedState player bound × QuittingRootSimplex player) ×
    QuittingRobustChargedState player bound

def quittingRobustChargedEdgeAbsorption
    (data : QuittingRobustChargedEdgeData player bound) : ℝ :=
  quittingRootAbsorptionMass (quittingRootOfSimplex data.1.2)

def quittingRobustChargedEdgeResidual
    (reward : {S : Finset player // S.Nonempty} → Payoff player)
    (data : QuittingRobustChargedEdgeData player bound) (who : player) : ℝ :=
  |data.2.1 who - quittingRootSuccessorPayoff reward data.1.1.1
    (quittingRootOfSimplex data.1.2) who|

def quittingRobustChargedEdgeRegret
    (reward : {S : Finset player // S.Nonempty} → Payoff player)
    (data : QuittingRobustChargedEdgeData player bound) (who : player) : ℝ :=
  quittingRootCoordinateNashDefect reward data.1.1.1
    (quittingRootOfSimplex data.1.2) who

/-- One floor-free robust edge. Both endpoints lie in the state box, while
the root is stored on the edge rather than in either state. -/
def IsQuittingFloorFreeRobustEdge
    (reward : {S : Finset player // S.Nonempty} → Payoff player)
    (tolerance bound : ℝ)
    (source : QuittingRobustChargedState player bound)
    (root : QuittingRootSimplex player)
    (target : QuittingRobustChargedState player bound) : Prop :=
  let data : QuittingRobustChargedEdgeData player bound :=
    ((source, root), target)
  ∀ who,
    quittingRobustChargedEdgeResidual reward data who ≤
        tolerance * quittingRobustChargedEdgeAbsorption data ∧
      quittingRobustChargedEdgeRegret reward data who ≤
        tolerance * quittingRobustChargedEdgeAbsorption data

/-- The full edge space, containing every boxed source/root/target triple
that satisfies the robust inequalities. -/
def QuittingRobustChargedEdge
    (reward : {S : Finset player // S.Nonempty} → Payoff player)
    (tolerance bound : ℝ) :=
  {data : QuittingRobustChargedEdgeData player bound |
    IsQuittingFloorFreeRobustEdge reward tolerance bound
      data.1.1 data.1.2 data.2}

private def quittingRobustChargedEdgeSourceRoot
    (data : QuittingRobustChargedEdgeData player bound) :
    Payoff player × QuittingRootSimplex player :=
  (data.1.1.1, data.1.2)

omit [DecidableEq player] in
private theorem continuous_quittingRobustChargedEdgeSourceRoot
    (bound : ℝ) :
    Continuous (quittingRobustChargedEdgeSourceRoot
      (player := player) (bound := bound)) :=
  (continuous_subtype_val.comp
      (continuous_fst.comp continuous_fst)).prodMk
    (continuous_snd.comp continuous_fst)

omit [DecidableEq player] in
private theorem continuous_quittingRobustChargedEdgeSuccessor
    (reward : {S : Finset player // S.Nonempty} → Payoff player)
    (bound : ℝ) :
    Continuous (fun data : QuittingRobustChargedEdgeData player bound ↦
      quittingRootSuccessorPayoff reward data.1.1.1
        (quittingRootOfSimplex data.1.2)) :=
  by
    change Continuous ((fun point : Payoff player × QuittingRootSimplex player ↦
      quittingRootSuccessorPayoff reward point.1
        (quittingRootOfSimplex point.2)) ∘
          quittingRobustChargedEdgeSourceRoot)
    exact (continuous_quittingRootSuccessorPayoff_simplex reward).comp
      (continuous_quittingRobustChargedEdgeSourceRoot bound)

omit [DecidableEq player] in
private theorem continuous_quittingRobustChargedEdgeTarget
    (bound : ℝ) (who : player) :
    Continuous (fun data : QuittingRobustChargedEdgeData player bound ↦
      data.2.1 who) :=
  (continuous_apply who).comp (continuous_subtype_val.comp continuous_snd)

omit [DecidableEq player] in
private theorem continuous_quittingRobustChargedEdgeAbsorption
    (bound : ℝ) :
    Continuous (quittingRobustChargedEdgeAbsorption
      (player := player) (bound := bound)) :=
  continuous_quittingRootAbsorptionMass_simplex.comp
    (continuous_snd.comp continuous_fst)

omit [DecidableEq player] in
private theorem continuous_quittingRobustChargedEdgeResidual
    (reward : {S : Finset player // S.Nonempty} → Payoff player)
    (bound : ℝ) (who : player) :
    Continuous (fun data : QuittingRobustChargedEdgeData player bound ↦
      quittingRobustChargedEdgeResidual reward data who) := by
  unfold quittingRobustChargedEdgeResidual
  exact ((continuous_quittingRobustChargedEdgeTarget bound who).sub
    ((continuous_apply who).comp
      (continuous_quittingRobustChargedEdgeSuccessor reward bound))).abs

private theorem continuous_quittingRobustChargedEdgeRegret
    (reward : {S : Finset player // S.Nonempty} → Payoff player)
    (bound : ℝ) (who : player) :
    Continuous (fun data : QuittingRobustChargedEdgeData player bound ↦
      quittingRobustChargedEdgeRegret reward data who) := by
  unfold quittingRobustChargedEdgeRegret
  change Continuous ((fun point : Payoff player × QuittingRootSimplex player ↦
    quittingRootCoordinateNashDefect reward point.1
      (quittingRootOfSimplex point.2) who) ∘
        quittingRobustChargedEdgeSourceRoot)
  exact (continuous_quittingRootCoordinateNashDefect_simplex reward who).comp
    (continuous_quittingRobustChargedEdgeSourceRoot bound)

private theorem isClosed_quittingFloorFreeRobustEdgeAt
    (reward : {S : Finset player // S.Nonempty} → Payoff player)
    (tolerance bound : ℝ) (who : player) :
    IsClosed ({data : QuittingRobustChargedEdgeData player bound |
      quittingRobustChargedEdgeResidual reward data who ≤
        tolerance * quittingRobustChargedEdgeAbsorption data} ∩
      {data | quittingRobustChargedEdgeRegret reward data who ≤
        tolerance * quittingRobustChargedEdgeAbsorption data}) := by
  have habsorption := continuous_quittingRobustChargedEdgeAbsorption
    (player := player) bound
  exact (isClosed_le
      (continuous_quittingRobustChargedEdgeResidual reward bound who)
      (continuous_const.mul habsorption)).inter
    (isClosed_le (continuous_quittingRobustChargedEdgeRegret reward bound who)
      (continuous_const.mul habsorption))

theorem isClosed_isQuittingFloorFreeRobustEdge
    (reward : {S : Finset player // S.Nonempty} → Payoff player)
    (tolerance bound : ℝ) :
    IsClosed {data : QuittingRobustChargedEdgeData player bound |
      IsQuittingFloorFreeRobustEdge reward tolerance bound
        data.1.1 data.1.2 data.2} := by
  rw [show {data : QuittingRobustChargedEdgeData player bound |
      IsQuittingFloorFreeRobustEdge reward tolerance bound
        data.1.1 data.1.2 data.2} =
      ⋂ who, {data |
        quittingRobustChargedEdgeResidual reward data who ≤
          tolerance * quittingRobustChargedEdgeAbsorption data} ∩
        {data | quittingRobustChargedEdgeRegret reward data who ≤
          tolerance * quittingRobustChargedEdgeAbsorption data} by
    ext data
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_inter_iff]
    simp only [IsQuittingFloorFreeRobustEdge]]
  apply isClosed_iInter
  intro who
  exact isClosed_quittingFloorFreeRobustEdgeAt reward tolerance bound who

instance (reward : {S : Finset player // S.Nonempty} → Payoff player)
    (tolerance bound : ℝ) :
    CompactSpace (QuittingRobustChargedEdge reward tolerance bound) :=
  isCompact_iff_compactSpace.mp
    (isClosed_isQuittingFloorFreeRobustEdge reward tolerance bound).isCompact

/-- The floor-free robust relation, charged by one-step absorption mass. -/
def quittingFloorFreeRobustChargedRelation
    (reward : {S : Finset player // S.Nonempty} → Payoff player)
    (tolerance bound : ℝ) :
    ChargedRelation (QuittingRobustChargedState player bound)
      (QuittingRobustChargedEdge reward tolerance bound) where
  src edge := edge.1.1.1
  tgt edge := edge.1.2
  charge edge := quittingRootAbsorptionMass
    (quittingRootOfSimplex edge.1.1.2)
  charge_nonneg edge := quittingRootAbsorptionMass_nonneg
    (quittingRootOfSimplex edge.1.1.2)

theorem continuous_quittingFloorFreeRobustChargedRelation_src
    (reward : {S : Finset player // S.Nonempty} → Payoff player)
    (tolerance bound : ℝ) :
    Continuous (quittingFloorFreeRobustChargedRelation
      reward tolerance bound).src :=
  continuous_fst.comp (continuous_fst.comp continuous_subtype_val)

theorem continuous_quittingFloorFreeRobustChargedRelation_tgt
    (reward : {S : Finset player // S.Nonempty} → Payoff player)
    (tolerance bound : ℝ) :
    Continuous (quittingFloorFreeRobustChargedRelation
      reward tolerance bound).tgt :=
  continuous_snd.comp continuous_subtype_val

theorem continuous_quittingFloorFreeRobustChargedRelation_charge
    (reward : {S : Finset player // S.Nonempty} → Payoff player)
    (tolerance bound : ℝ) :
    Continuous (quittingFloorFreeRobustChargedRelation
      reward tolerance bound).charge :=
  continuous_quittingRootAbsorptionMass_simplex.comp
    (continuous_snd.comp (continuous_fst.comp continuous_subtype_val))

end GameTheory
