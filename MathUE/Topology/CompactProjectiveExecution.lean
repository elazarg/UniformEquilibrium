/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Sequences

/-!
# Compact projective execution systems

One cofinal sequence of proof-relevant executions is restricted to every
fixed named finite diagram.  Compactness of the countable product selects one
common subsequence, and continuity plus literal functoriality of restriction
makes its coordinate limits compatible.  Different depths cannot choose
unrelated input sequences.
-/

noncomputable section

namespace Math
namespace Topology

open Filter

variable {Execution : ℕ → Type*}
  [∀ depth, TopologicalSpace (Execution depth)]
  [∀ depth, FirstCountableTopology (Execution depth)]
  [∀ depth, T2Space (Execution depth)]

/-- A projective system of compact proof-relevant finite execution spaces.
The restriction laws are literal data of one named diagram system. -/
structure CompactProjectiveExecutionSystem
    (Execution : ℕ → Type*)
    [∀ depth, TopologicalSpace (Execution depth)] where
  executionSet : ∀ depth, Set (Execution depth)
  execution_compact : ∀ depth, IsCompact (executionSet depth)
  restriction : ∀ smaller larger, smaller ≤ larger →
    Execution larger → Execution smaller
  restriction_continuous : ∀ smaller larger (hle : smaller ≤ larger),
    Continuous (restriction smaller larger hle)
  restriction_mem : ∀ smaller larger (hle : smaller ≤ larger) point,
    point ∈ executionSet larger →
      restriction smaller larger hle point ∈ executionSet smaller
  restriction_id : ∀ depth point,
    restriction depth depth le_rfl point = point
  restriction_trans : ∀ first second third
      (hfirst : first ≤ second) (hsecond : second ≤ third) point,
    restriction first third (hfirst.trans hsecond) point =
      restriction first second hfirst
        (restriction second third hsecond point)

namespace CompactProjectiveExecutionSystem

variable
  (system : CompactProjectiveExecutionSystem Execution)

/-- A certified point of one finite execution space. -/
abbrev ExecutionPoint (depth : ℕ) := system.executionSet depth

/-- Restriction on certified execution points. -/
def pointRestriction
    (smaller larger : ℕ) (hle : smaller ≤ larger) :
    system.ExecutionPoint larger → system.ExecutionPoint smaller :=
  fun point ↦
    ⟨system.restriction smaller larger hle point,
      system.restriction_mem smaller larger hle point point.property⟩

omit [∀ depth, FirstCountableTopology (Execution depth)]
  [∀ depth, T2Space (Execution depth)] in
theorem continuous_pointRestriction
    (smaller larger : ℕ) (hle : smaller ≤ larger) :
    Continuous (system.pointRestriction smaller larger hle) := by
  exact ((system.restriction_continuous smaller larger hle).comp
    continuous_subtype_val).subtype_mk _

/-- One sequence of executions on cofinally growing named diagrams. -/
structure CofinalExecutionSequence where
  depth : ℕ → ℕ
  depth_tendsto_atTop : Tendsto depth atTop atTop
  execution : ∀ index, Execution (depth index)
  execution_mem : ∀ index, execution index ∈ system.executionSet (depth index)

namespace CofinalExecutionSequence

variable (sequence : system.CofinalExecutionSequence)
include sequence

omit [∀ depth, FirstCountableTopology (Execution depth)]
  [∀ depth, T2Space (Execution depth)] in
theorem nonempty_executionSet (depth : ℕ) :
    (system.executionSet depth).Nonempty := by
  have hevent : ∀ᶠ index in atTop,
      depth ≤ CofinalExecutionSequence.depth sequence index :=
    (tendsto_atTop.1
      (CofinalExecutionSequence.depth_tendsto_atTop sequence)) depth
  obtain ⟨cutoff, hcutoff⟩ := eventually_atTop.1 hevent
  let hle : depth ≤ CofinalExecutionSequence.depth sequence cutoff :=
    hcutoff cutoff le_rfl
  exact ⟨system.restriction depth
      (CofinalExecutionSequence.depth sequence cutoff) hle
      (CofinalExecutionSequence.execution sequence cutoff),
    system.restriction_mem depth
      (CofinalExecutionSequence.depth sequence cutoff) hle
      (CofinalExecutionSequence.execution sequence cutoff)
      (CofinalExecutionSequence.execution_mem sequence cutoff)⟩

/-- A harmless compact-carrier filler used only before a sampled diagram has
reached the requested depth. -/
def basePoint (depth : ℕ) : system.ExecutionPoint depth :=
  ⟨Classical.choose (nonempty_executionSet system sequence depth),
    Classical.choose_spec (nonempty_executionSet system sequence depth)⟩

/-- Restrict the sampled execution to a fixed depth once available; before
that finite time use the carrier filler. -/
def restrictedPoint (index depth : ℕ) : system.ExecutionPoint depth :=
  if hle : depth ≤ CofinalExecutionSequence.depth sequence index then
    ⟨system.restriction depth
        (CofinalExecutionSequence.depth sequence index) hle
        (CofinalExecutionSequence.execution sequence index),
      system.restriction_mem depth
        (CofinalExecutionSequence.depth sequence index) hle
        (CofinalExecutionSequence.execution sequence index)
        (CofinalExecutionSequence.execution_mem sequence index)⟩
  else basePoint system sequence depth

omit [∀ depth, FirstCountableTopology (Execution depth)]
  [∀ depth, T2Space (Execution depth)] in
theorem restrictedPoint_of_le
    (index depth : ℕ)
    (hle : depth ≤ CofinalExecutionSequence.depth sequence index) :
    restrictedPoint system sequence index depth =
      ⟨system.restriction depth
          (CofinalExecutionSequence.depth sequence index) hle
          (CofinalExecutionSequence.execution sequence index),
        system.restriction_mem depth
          (CofinalExecutionSequence.depth sequence index) hle
          (CofinalExecutionSequence.execution sequence index)
          (CofinalExecutionSequence.execution_mem sequence index)⟩ := by
  simp only [restrictedPoint, dif_pos hle]

omit [∀ depth, FirstCountableTopology (Execution depth)]
  [∀ depth, T2Space (Execution depth)] in
theorem pointRestriction_restrictedPoint
    (index smaller larger : ℕ) (hsmaller : smaller ≤ larger)
    (hlarge : larger ≤ CofinalExecutionSequence.depth sequence index) :
    system.pointRestriction smaller larger hsmaller
        (restrictedPoint system sequence index larger) =
      restrictedPoint system sequence index smaller := by
  apply Subtype.ext
  rw [restrictedPoint_of_le system sequence index larger hlarge]
  rw [restrictedPoint_of_le system sequence index smaller
    (hsmaller.trans hlarge)]
  exact (system.restriction_trans smaller larger
    (CofinalExecutionSequence.depth sequence index)
    hsmaller hlarge
    (CofinalExecutionSequence.execution sequence index)).symm

end CofinalExecutionSequence

/-- One compatible inverse-limit family of named finite executions. -/
structure CompatibleExecution where
  point : ∀ depth, system.ExecutionPoint depth
  compatible : ∀ smaller larger (hle : smaller ≤ larger),
    system.pointRestriction smaller larger hle (point larger) = point smaller

/-- A cofinal execution sequence has one common subsequence converging at
every named depth to one compatible projective family. -/
structure ProjectiveSubsequenceLimit
    (sequence : system.CofinalExecutionSequence) where
  subsequence : ℕ → ℕ
  subsequence_strictMono : StrictMono subsequence
  limit : system.CompatibleExecution
  depth_eventually_available : ∀ depth,
    ∀ᶠ rank in atTop,
      depth ≤ CofinalExecutionSequence.depth sequence (subsequence rank)
  restriction_tendsto : ∀ depth,
    Tendsto (fun rank ↦
      CofinalExecutionSequence.restrictedPoint system sequence
        (subsequence rank) depth)
      atTop (nhds (limit.point depth))

/-- Projective realization by diagonal compactness of one countable product.
The same `subsequence` occurs in every coordinate conclusion. -/
theorem exists_projectiveSubsequenceLimit
    (sequence : system.CofinalExecutionSequence) :
    Nonempty (system.ProjectiveSubsequenceLimit sequence) := by
  letI (depth : ℕ) : CompactSpace (system.ExecutionPoint depth) :=
    isCompact_iff_compactSpace.mp (system.execution_compact depth)
  obtain ⟨limitPoint, subsequence, hmono, htendsto⟩ :=
    CompactSpace.tendsto_subseq
      (fun index depth ↦
        CofinalExecutionSequence.restrictedPoint system sequence index depth)
  have hdepth : Tendsto
      (CofinalExecutionSequence.depth sequence ∘ subsequence)
      atTop atTop :=
    (CofinalExecutionSequence.depth_tendsto_atTop sequence).comp
      hmono.tendsto_atTop
  have havailable : ∀ depth,
      ∀ᶠ rank in atTop,
        depth ≤ CofinalExecutionSequence.depth sequence
          (subsequence rank) :=
    fun depth ↦ (tendsto_atTop.1 hdepth) depth
  have hcoordinate : ∀ depth,
      Tendsto (fun rank ↦
        CofinalExecutionSequence.restrictedPoint system sequence
          (subsequence rank) depth)
        atTop (nhds (limitPoint depth)) :=
    fun depth ↦ tendsto_pi_nhds.mp htendsto depth
  have hcompatible : ∀ smaller larger (hle : smaller ≤ larger),
      system.pointRestriction smaller larger hle (limitPoint larger) =
        limitPoint smaller := by
    intro smaller larger hle
    have hmapped : Tendsto
        (fun rank ↦ system.pointRestriction smaller larger hle
          (CofinalExecutionSequence.restrictedPoint system sequence
            (subsequence rank) larger))
        atTop
        (nhds (system.pointRestriction smaller larger hle
          (limitPoint larger))) :=
      (system.continuous_pointRestriction smaller larger hle).continuousAt.tendsto.comp
        (hcoordinate larger)
    have heq : ∀ᶠ rank in atTop,
        system.pointRestriction smaller larger hle
            (CofinalExecutionSequence.restrictedPoint system sequence
              (subsequence rank) larger) =
          CofinalExecutionSequence.restrictedPoint system sequence
            (subsequence rank) smaller := by
      filter_upwards [havailable larger] with rank hrank
      exact CofinalExecutionSequence.pointRestriction_restrictedPoint
        system sequence
        (subsequence rank) smaller larger hle hrank
    exact tendsto_nhds_unique (hmapped.congr' heq) (hcoordinate smaller)
  exact ⟨{
    subsequence := subsequence
    subsequence_strictMono := hmono
    limit := {
      point := limitPoint
      compatible := hcompatible }
    depth_eventually_available := havailable
    restriction_tendsto := hcoordinate }⟩

/-- A literally nested family already is a compatible projective execution;
no subsequence or compactness extraction is needed. -/
def compatibleExecutionOfNested
    (point : ∀ depth, system.ExecutionPoint depth)
    (nested : ∀ depth,
      system.pointRestriction depth (depth + 1) (Nat.le_succ depth)
        (point (depth + 1)) = point depth) :
    system.CompatibleExecution where
  point := point
  compatible := by
    intro smaller larger hle
    induction larger, hle using Nat.le_induction with
    | base =>
        apply Subtype.ext
        exact system.restriction_id smaller (point smaller)
    | succ larger hle ih =>
        rw [show system.pointRestriction smaller (larger + 1)
            (Nat.le.step hle) (point (larger + 1)) =
              system.pointRestriction smaller larger hle
                (system.pointRestriction larger (larger + 1)
                  (Nat.le_succ larger) (point (larger + 1))) by
          apply Subtype.ext
          exact system.restriction_trans smaller larger (larger + 1)
            hle (Nat.le_succ larger) (point (larger + 1))]
        rw [nested larger, ih]

end CompactProjectiveExecutionSystem

end Topology
end Math
