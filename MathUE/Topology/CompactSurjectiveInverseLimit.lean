/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.Topology.SummableExecutableDecoder
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Separation.Hausdorff

/-!
# Compact inverse limits of surjective finite-code towers

A sequence of compact finite code spaces with continuous surjective
restrictions has a nonempty compact space of complete compatible codes.  A
summable finite-macro tower on those codes then produces the complete-code
decoder required by `SummableExecutableDecoder`; the inverse-limit code is
constructed here rather than postulated by the decoder.
-/

noncomputable section

namespace Math
namespace Topology

variable {Stage : ℕ → Type*}
  [∀ depth, TopologicalSpace (Stage depth)]

/-- Compact finite code spaces with continuous surjective adjacent
restrictions. -/
structure CompactSurjectiveTower
    (Stage : ℕ → Type*) [∀ depth, TopologicalSpace (Stage depth)] where
  stageSet : ∀ depth, Set (Stage depth)
  stage_compact : ∀ depth, IsCompact (stageSet depth)
  initial_nonempty : (stageSet 0).Nonempty
  restriction : ∀ depth, Stage (depth + 1) → Stage depth
  restriction_continuous : ∀ depth, Continuous (restriction depth)
  restriction_mem : ∀ depth point,
    point ∈ stageSet (depth + 1) →
      restriction depth point ∈ stageSet depth
  restriction_surjective : ∀ depth point,
    point ∈ stageSet depth →
      ∃ next, next ∈ stageSet (depth + 1) ∧
        restriction depth next = point

namespace CompactSurjectiveTower

variable (tower : CompactSurjectiveTower Stage)

/-- Complete codes stay in every finite code space and commute with every
adjacent restriction. -/
def completeCodeSet : Set (∀ depth, Stage depth) :=
  {code |
    (∀ depth, code depth ∈ tower.stageSet depth) ∧
      ∀ depth, tower.restriction depth (code (depth + 1)) = code depth}

/-- The unrestricted product of the finite code carriers is compact. -/
theorem isCompact_codeBox :
    IsCompact {code : ∀ depth, Stage depth |
      ∀ depth, code depth ∈ tower.stageSet depth} := by
  exact isCompact_pi_infinite tower.stage_compact

/-- Compatibility with all adjacent restrictions is a closed condition. -/
theorem isClosed_compatibleCodeSet
    [∀ depth, T2Space (Stage depth)] :
    IsClosed {code : ∀ depth, Stage depth |
      ∀ depth, tower.restriction depth (code (depth + 1)) = code depth} := by
  rw [show {code : ∀ depth, Stage depth |
      ∀ depth, tower.restriction depth (code (depth + 1)) = code depth} =
      ⋂ depth, {code : ∀ current, Stage current |
        tower.restriction depth (code (depth + 1)) = code depth} by
    ext code
    simp only [Set.mem_setOf_eq, Set.mem_iInter]]
  exact isClosed_iInter fun depth ↦
    isClosed_eq
      ((tower.restriction_continuous depth).comp
        (continuous_apply (depth + 1)))
      (continuous_apply depth)

/-- The complete inverse-limit code space is compact. -/
theorem isCompact_completeCodeSet
    [∀ depth, T2Space (Stage depth)] :
    IsCompact tower.completeCodeSet := by
  have heq : tower.completeCodeSet =
      {code : ∀ depth, Stage depth |
        ∀ depth, code depth ∈ tower.stageSet depth} ∩
      {code : ∀ depth, Stage depth |
        ∀ depth, tower.restriction depth (code (depth + 1)) = code depth} := by
    ext code
    rfl
  rw [heq]
  exact tower.isCompact_codeBox.inter_right
    tower.isClosed_compatibleCodeSet

/-- A chosen point in the initial finite code space. -/
def initialPoint : tower.stageSet 0 :=
  ⟨Classical.choose tower.initial_nonempty,
    Classical.choose_spec tower.initial_nonempty⟩

/-- A chosen compatible lift of one certified finite code. -/
def liftPoint (depth : ℕ) (point : tower.stageSet depth) :
    tower.stageSet (depth + 1) :=
  ⟨Classical.choose
      (tower.restriction_surjective depth point point.property),
    (Classical.choose_spec
      (tower.restriction_surjective depth point point.property)).1⟩

@[simp] theorem restriction_liftPoint
    (depth : ℕ) (point : tower.stageSet depth) :
    tower.restriction depth (tower.liftPoint depth point) = point := by
  exact (Classical.choose_spec
    (tower.restriction_surjective depth point point.property)).2

/-- One canonical compatible code, obtained by recursively lifting the
initial code. -/
def canonicalCodePoint : ∀ depth, tower.stageSet depth
  | 0 => tower.initialPoint
  | depth + 1 => tower.liftPoint depth (canonicalCodePoint depth)

/-- The underlying dependent sequence of the canonical compatible code. -/
def canonicalCode (depth : ℕ) : Stage depth :=
  tower.canonicalCodePoint depth

@[simp] theorem canonicalCode_mem (depth : ℕ) :
    tower.canonicalCode depth ∈ tower.stageSet depth :=
  (tower.canonicalCodePoint depth).property

@[simp] theorem restriction_canonicalCode (depth : ℕ) :
    tower.restriction depth (tower.canonicalCode (depth + 1)) =
      tower.canonicalCode depth := by
  simp only [canonicalCode, canonicalCodePoint]
  exact tower.restriction_liftPoint depth (tower.canonicalCodePoint depth)

/-- Surjectivity makes the complete inverse-limit code space nonempty. -/
theorem completeCodeSet_nonempty : tower.completeCodeSet.Nonempty := by
  exact ⟨tower.canonicalCode,
    ⟨tower.canonicalCode_mem, tower.restriction_canonicalCode⟩⟩

/-- Coordinate projection from a complete code is continuous. -/
theorem continuous_completeCodeProjection (depth : ℕ) :
    Continuous fun code : tower.completeCodeSet ↦ code.1 depth :=
  (continuous_apply depth).comp continuous_subtype_val

end CompactSurjectiveTower

variable {State Visible Certificate : Type*}
  [MetricSpace State] [CompleteSpace State]
  [MetricSpace Visible] [CompleteSpace Visible]
  [TopologicalSpace Certificate]

/-- Finite continuous approximants and literal legal macro certificates on a
compact surjective code tower.  All endpoint equalities are stated on the
finite extension which actually carries the macro. -/
structure SummableFiniteMacroTower
    (Stage : ℕ → Type*) (State Visible Certificate : Type*)
    [∀ depth, TopologicalSpace (Stage depth)]
    [MetricSpace State] [CompleteSpace State]
    [MetricSpace Visible] [CompleteSpace Visible]
    [TopologicalSpace Certificate]
    extends CompactSurjectiveTower Stage where
  state : ∀ depth, Stage depth → State
  state_continuousOn : ∀ depth,
    ContinuousOn (state depth) (stageSet depth)
  stateError : ℕ → ℝ
  stateError_nonneg : ∀ depth, 0 ≤ stateError depth
  stateError_summable : Summable stateError
  state_step : ∀ depth next, next ∈ stageSet (depth + 1) →
    dist (state depth (restriction depth next))
      (state (depth + 1) next) ≤ stateError depth
  visible : ∀ depth, Stage depth → Visible
  visible_continuousOn : ∀ depth,
    ContinuousOn (visible depth) (stageSet depth)
  visibleCarrier : Set Visible
  visibleCarrier_compact : IsCompact visibleCarrier
  visible_mem : ∀ depth point, point ∈ stageSet depth →
    visible depth point ∈ visibleCarrier
  visibleError : ℕ → ℝ
  visibleError_nonneg : ∀ depth, 0 ≤ visibleError depth
  visibleError_summable : Summable visibleError
  visible_step : ∀ depth next, next ∈ stageSet (depth + 1) →
    dist (visible depth (restriction depth next))
      (visible (depth + 1) next) ≤ visibleError depth
  certificate : ∀ depth, Stage (depth + 1) → Certificate
  certificate_continuousOn : ∀ depth,
    ContinuousOn (certificate depth) (stageSet (depth + 1))
  certificateCarrier : Set Certificate
  certificateCarrier_compact : IsCompact certificateCarrier
  certificate_mem : ∀ depth point, point ∈ stageSet (depth + 1) →
    certificate depth point ∈ certificateCarrier
  certificateSource : Certificate → State
  certificateTarget : Certificate → State
  legalMacro : Certificate → Prop
  certificate_legal : ∀ depth point, point ∈ stageSet (depth + 1) →
    legalMacro (certificate depth point)
  certificate_source_eq : ∀ depth point,
    point ∈ stageSet (depth + 1) →
      certificateSource (certificate depth point) =
        state depth (restriction depth point)
  certificate_target_eq : ∀ depth point,
    point ∈ stageSet (depth + 1) →
      certificateTarget (certificate depth point) =
        state (depth + 1) point

namespace SummableFiniteMacroTower

variable [∀ depth, T2Space (Stage depth)]
  (tower : SummableFiniteMacroTower Stage State Visible Certificate)

/-- The complete-code decoder constructed from the declared finite compact
surjective tower. -/
def toSummableExecutableDecoder :
    SummableExecutableDecoder
      (∀ depth, Stage depth) State Visible Certificate where
  codeSet := tower.toCompactSurjectiveTower.completeCodeSet
  code_compact := tower.toCompactSurjectiveTower.isCompact_completeCodeSet
  state := fun depth code ↦ tower.state depth (code depth)
  state_continuousOn := by
    intro depth
    exact (tower.state_continuousOn depth).comp
      (continuous_apply depth).continuousOn
      (fun code hcode ↦ hcode.1 depth)
  stateError := tower.stateError
  stateError_nonneg := tower.stateError_nonneg
  stateError_summable := tower.stateError_summable
  state_step := by
    intro code hcode depth
    rw [← hcode.2 depth]
    exact tower.state_step depth (code (depth + 1))
      (hcode.1 (depth + 1))
  visible := fun depth code ↦ tower.visible depth (code depth)
  visible_continuousOn := by
    intro depth
    exact (tower.visible_continuousOn depth).comp
      (continuous_apply depth).continuousOn
      (fun code hcode ↦ hcode.1 depth)
  visibleCarrier := tower.visibleCarrier
  visibleCarrier_compact := tower.visibleCarrier_compact
  visible_mem := by
    intro code hcode depth
    exact tower.visible_mem depth (code depth) (hcode.1 depth)
  visibleError := tower.visibleError
  visibleError_nonneg := tower.visibleError_nonneg
  visibleError_summable := tower.visibleError_summable
  visible_step := by
    intro code hcode depth
    rw [← hcode.2 depth]
    exact tower.visible_step depth (code (depth + 1))
      (hcode.1 (depth + 1))
  certificate := fun depth code ↦ tower.certificate depth (code (depth + 1))
  certificate_continuousOn := by
    intro depth
    exact (tower.certificate_continuousOn depth).comp
      (continuous_apply (depth + 1)).continuousOn
      (fun code hcode ↦ hcode.1 (depth + 1))
  certificateCarrier := tower.certificateCarrier
  certificateCarrier_compact := tower.certificateCarrier_compact
  certificate_mem := by
    intro code hcode depth
    exact tower.certificate_mem depth (code (depth + 1))
      (hcode.1 (depth + 1))
  certificateSource := tower.certificateSource
  certificateTarget := tower.certificateTarget
  legalMacro := tower.legalMacro
  certificate_legal := by
    intro code hcode depth
    exact tower.certificate_legal depth (code (depth + 1))
      (hcode.1 (depth + 1))
  certificate_source_eq := by
    intro code hcode depth
    rw [tower.certificate_source_eq depth (code (depth + 1))
      (hcode.1 (depth + 1)), hcode.2 depth]
  certificate_target_eq := by
    intro code hcode depth
    exact tower.certificate_target_eq depth (code (depth + 1))
      (hcode.1 (depth + 1))

/-- The tower therefore supplies a nonempty compact complete-code carrier,
not merely separate finite codes. -/
theorem completeCode_nonempty :
    (tower.toSummableExecutableDecoder.codeSet).Nonempty :=
  tower.toCompactSurjectiveTower.completeCodeSet_nonempty

end SummableFiniteMacroTower

end Topology
end Math
