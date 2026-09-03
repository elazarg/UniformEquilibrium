/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.UniformSpace.UniformConvergence
import Mathlib.Topology.UniformSpace.UniformApproximation

/-!
# Source-anchored summable executable decoders

Uniform summable successive-displacement budgets turn continuous finite
approximants on a compact code space into one continuous actual decoder.  The
first approximant is the named source.  Every finite macro certificate remains
in the proof-relevant ancestry record with literal source and target endpoints.

Visible numerical annotations use their own summable budget.  Consequently a
LawMin error or another visible quantity cannot be smuggled in through an
unbounded initial value: its code range is explicitly contained in one compact
carrier.
-/

noncomputable section

namespace Math
namespace Topology

open Filter

variable {Code State Visible Certificate : Type*}
  [TopologicalSpace Code]
  [MetricSpace State] [CompleteSpace State]
  [MetricSpace Visible] [CompleteSpace Visible]
  [TopologicalSpace Certificate]

/-- A compact complete-code decoder with separate actual-state and visible
annotation budgets.  The code may itself be an inverse-limit subtype built by
another module; this structure does not silently choose unrelated codes at
different depths. -/
structure SummableExecutableDecoder
    (Code State Visible Certificate : Type*)
    [TopologicalSpace Code]
    [MetricSpace State] [CompleteSpace State]
    [MetricSpace Visible] [CompleteSpace Visible]
    [TopologicalSpace Certificate] where
  codeSet : Set Code
  code_compact : IsCompact codeSet
  state : ℕ → Code → State
  state_continuousOn : ∀ depth, ContinuousOn (state depth) codeSet
  stateError : ℕ → ℝ
  stateError_nonneg : ∀ depth, 0 ≤ stateError depth
  stateError_summable : Summable stateError
  state_step : ∀ code, code ∈ codeSet → ∀ depth,
    dist (state depth code) (state (depth + 1) code) ≤ stateError depth
  visible : ℕ → Code → Visible
  visible_continuousOn : ∀ depth, ContinuousOn (visible depth) codeSet
  visibleCarrier : Set Visible
  visibleCarrier_compact : IsCompact visibleCarrier
  visible_mem : ∀ code, code ∈ codeSet → ∀ depth,
    visible depth code ∈ visibleCarrier
  visibleError : ℕ → ℝ
  visibleError_nonneg : ∀ depth, 0 ≤ visibleError depth
  visibleError_summable : Summable visibleError
  visible_step : ∀ code, code ∈ codeSet → ∀ depth,
    dist (visible depth code) (visible (depth + 1) code) ≤ visibleError depth
  certificate : ℕ → Code → Certificate
  certificate_continuousOn : ∀ depth,
    ContinuousOn (certificate depth) codeSet
  certificateCarrier : Set Certificate
  certificateCarrier_compact : IsCompact certificateCarrier
  certificate_mem : ∀ code, code ∈ codeSet → ∀ depth,
    certificate depth code ∈ certificateCarrier
  certificateSource : Certificate → State
  certificateTarget : Certificate → State
  legalMacro : Certificate → Prop
  certificate_legal : ∀ code, code ∈ codeSet → ∀ depth,
    legalMacro (certificate depth code)
  certificate_source_eq : ∀ code, code ∈ codeSet → ∀ depth,
    certificateSource (certificate depth code) = state depth code
  certificate_target_eq : ∀ code, code ∈ codeSet → ∀ depth,
    certificateTarget (certificate depth code) = state (depth + 1) code

namespace SummableExecutableDecoder

/-- A complete code, carrying its certified compact-membership proof. -/
abbrev CodePoint
    (decoder : SummableExecutableDecoder Code State Visible Certificate) :=
  decoder.codeSet

/-- The finite actual-state track at one complete code. -/
def stateTrack
    (decoder : SummableExecutableDecoder Code State Visible Certificate)
    (code : decoder.CodePoint) (depth : ℕ) : State :=
  decoder.state depth code

/-- The finite visible-annotation track at one complete code. -/
def visibleTrack
    (decoder : SummableExecutableDecoder Code State Visible Certificate)
    (code : decoder.CodePoint) (depth : ℕ) : Visible :=
  decoder.visible depth code

theorem cauchySeq_stateTrack
    (decoder : SummableExecutableDecoder Code State Visible Certificate)
    (code : decoder.CodePoint) :
    CauchySeq (decoder.stateTrack code) := by
  apply cauchySeq_of_dist_le_of_summable decoder.stateError
  · intro depth
    exact decoder.state_step code code.property depth
  · exact decoder.stateError_summable

theorem cauchySeq_visibleTrack
    (decoder : SummableExecutableDecoder Code State Visible Certificate)
    (code : decoder.CodePoint) :
    CauchySeq (decoder.visibleTrack code) := by
  apply cauchySeq_of_dist_le_of_summable decoder.visibleError
  · intro depth
    exact decoder.visible_step code code.property depth
  · exact decoder.visibleError_summable

/-- The actual decoded state, derived from completeness and the uniform
summable finite-macro budget. -/
def decodedState
    (decoder : SummableExecutableDecoder Code State Visible Certificate)
    (code : decoder.CodePoint) : State :=
  Classical.choose
    (cauchySeq_tendsto_of_complete (decoder.cauchySeq_stateTrack code))

/-- The decoded visible annotation. -/
def decodedVisible
    (decoder : SummableExecutableDecoder Code State Visible Certificate)
    (code : decoder.CodePoint) : Visible :=
  Classical.choose
    (cauchySeq_tendsto_of_complete (decoder.cauchySeq_visibleTrack code))

theorem tendsto_stateTrack
    (decoder : SummableExecutableDecoder Code State Visible Certificate)
    (code : decoder.CodePoint) :
    Tendsto (decoder.stateTrack code) atTop
      (nhds (decoder.decodedState code)) :=
  Classical.choose_spec
    (cauchySeq_tendsto_of_complete (decoder.cauchySeq_stateTrack code))

theorem tendsto_visibleTrack
    (decoder : SummableExecutableDecoder Code State Visible Certificate)
    (code : decoder.CodePoint) :
    Tendsto (decoder.visibleTrack code) atTop
      (nhds (decoder.decodedVisible code)) :=
  Classical.choose_spec
    (cauchySeq_tendsto_of_complete (decoder.cauchySeq_visibleTrack code))

/-- Quantitative actual-state tail bound. -/
theorem dist_state_decodedState_le_tail
    (decoder : SummableExecutableDecoder Code State Visible Certificate)
    (code : decoder.CodePoint) (depth : ℕ) :
    dist (decoder.stateTrack code depth) (decoder.decodedState code) ≤
      ∑' offset, decoder.stateError (depth + offset) := by
  exact dist_le_tsum_of_dist_le_of_tendsto decoder.stateError
    (fun n ↦ decoder.state_step code code.property n)
    decoder.stateError_summable (decoder.tendsto_stateTrack code) depth

/-- Quantitative visible-annotation tail bound. -/
theorem dist_visible_decodedVisible_le_tail
    (decoder : SummableExecutableDecoder Code State Visible Certificate)
    (code : decoder.CodePoint) (depth : ℕ) :
    dist (decoder.visibleTrack code depth) (decoder.decodedVisible code) ≤
      ∑' offset, decoder.visibleError (depth + offset) := by
  exact dist_le_tsum_of_dist_le_of_tendsto decoder.visibleError
    (fun n ↦ decoder.visible_step code code.property n)
    decoder.visibleError_summable (decoder.tendsto_visibleTrack code) depth

theorem continuous_stateTrack
    (decoder : SummableExecutableDecoder Code State Visible Certificate)
    (depth : ℕ) :
    Continuous fun code : decoder.CodePoint ↦ decoder.stateTrack code depth :=
  (decoder.state_continuousOn depth).restrict

theorem continuous_visibleTrack
    (decoder : SummableExecutableDecoder Code State Visible Certificate)
    (depth : ℕ) :
    Continuous fun code : decoder.CodePoint ↦ decoder.visibleTrack code depth :=
  (decoder.visible_continuousOn depth).restrict

theorem tendstoUniformly_stateTrack
    (decoder : SummableExecutableDecoder Code State Visible Certificate) :
    TendstoUniformly (fun depth code ↦ decoder.stateTrack code depth)
      decoder.decodedState atTop := by
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  have htail : Tendsto
      (fun depth ↦ ∑' offset, decoder.stateError (offset + depth))
      atTop (nhds 0) := tendsto_sum_nat_add decoder.stateError
  obtain ⟨cutoff, hcutoff⟩ := Metric.tendsto_atTop.1 htail ε hε
  filter_upwards [eventually_atTop.2 ⟨cutoff, hcutoff⟩] with depth hdepth code
  calc
    dist (decoder.decodedState code) (decoder.stateTrack code depth) =
        dist (decoder.stateTrack code depth) (decoder.decodedState code) :=
      dist_comm _ _
    _ ≤ ∑' offset, decoder.stateError (depth + offset) :=
      decoder.dist_state_decodedState_le_tail code depth
    _ = ∑' offset, decoder.stateError (offset + depth) := by
      congr 1
      funext offset
      rw [Nat.add_comm]
    _ < ε := (le_abs_self _).trans_lt <| by
      simpa [Real.dist_eq] using hdepth

theorem tendstoUniformly_visibleTrack
    (decoder : SummableExecutableDecoder Code State Visible Certificate) :
    TendstoUniformly (fun depth code ↦ decoder.visibleTrack code depth)
      decoder.decodedVisible atTop := by
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  have htail : Tendsto
      (fun depth ↦ ∑' offset, decoder.visibleError (offset + depth))
      atTop (nhds 0) := tendsto_sum_nat_add decoder.visibleError
  obtain ⟨cutoff, hcutoff⟩ := Metric.tendsto_atTop.1 htail ε hε
  filter_upwards [eventually_atTop.2 ⟨cutoff, hcutoff⟩] with depth hdepth code
  calc
    dist (decoder.decodedVisible code) (decoder.visibleTrack code depth) =
        dist (decoder.visibleTrack code depth) (decoder.decodedVisible code) :=
      dist_comm _ _
    _ ≤ ∑' offset, decoder.visibleError (depth + offset) :=
      decoder.dist_visible_decodedVisible_le_tail code depth
    _ = ∑' offset, decoder.visibleError (offset + depth) := by
      congr 1
      funext offset
      rw [Nat.add_comm]
    _ < ε := (le_abs_self _).trans_lt <| by
      simpa [Real.dist_eq] using hdepth

/-- Uniform summability makes the actual decoder continuous. -/
theorem continuous_decodedState
    (decoder : SummableExecutableDecoder Code State Visible Certificate) :
    Continuous decoder.decodedState :=
  decoder.tendstoUniformly_stateTrack.continuous
    (Frequently.of_forall decoder.continuous_stateTrack)

/-- Uniform summability makes the decoded visible annotation continuous. -/
theorem continuous_decodedVisible
    (decoder : SummableExecutableDecoder Code State Visible Certificate) :
    Continuous decoder.decodedVisible :=
  decoder.tendstoUniformly_visibleTrack.continuous
    (Frequently.of_forall decoder.continuous_visibleTrack)

/-- The exact named source of a decoder code is its depth-zero actual state. -/
def initialSource
    (decoder : SummableExecutableDecoder Code State Visible Certificate)
    (code : decoder.CodePoint) : State :=
  decoder.stateTrack code 0

/-- The full source-faithful proof-relevant ancestry record. -/
def ancestryRecord
    (decoder : SummableExecutableDecoder Code State Visible Certificate)
    (code : decoder.CodePoint) :
    State × (ℕ → State) × (ℕ → Certificate) × State :=
  (decoder.initialSource code, decoder.stateTrack code,
    fun depth ↦ decoder.certificate depth code, decoder.decodedState code)

theorem continuous_ancestryRecord
    (decoder : SummableExecutableDecoder Code State Visible Certificate) :
    Continuous decoder.ancestryRecord := by
  unfold ancestryRecord initialSource
  apply Continuous.prodMk
  · exact decoder.continuous_stateTrack 0
  apply Continuous.prodMk
  · exact continuous_pi fun depth ↦ decoder.continuous_stateTrack depth
  apply Continuous.prodMk
  · exact continuous_pi fun depth ↦
      (decoder.certificate_continuousOn depth).restrict
  · exact decoder.continuous_decodedState

/-- Compact inverse-limit code produces a compact full ancestry relation,
including every finite certificate coordinate. -/
theorem isCompact_range_ancestryRecord
    (decoder : SummableExecutableDecoder Code State Visible Certificate) :
    IsCompact (Set.range decoder.ancestryRecord) := by
  letI : CompactSpace decoder.CodePoint :=
    isCompact_iff_compactSpace.mp decoder.code_compact
  exact isCompact_range decoder.continuous_ancestryRecord

/-- The full ancestry relation is closed in Hausdorff state and certificate
spaces. -/
theorem isClosed_range_ancestryRecord
    [T2Space Certificate]
    (decoder : SummableExecutableDecoder Code State Visible Certificate) :
    IsClosed (Set.range decoder.ancestryRecord) :=
  decoder.isCompact_range_ancestryRecord.isClosed

/-- Every retained certificate starts at the displayed finite state. -/
theorem certificate_starts_at_stateTrack
    (decoder : SummableExecutableDecoder Code State Visible Certificate)
    (code : decoder.CodePoint) (depth : ℕ) :
    decoder.certificateSource (decoder.certificate depth code) =
      decoder.stateTrack code depth :=
  decoder.certificate_source_eq code code.property depth

/-- Every retained certificate ends at the next displayed finite state. -/
theorem certificate_ends_at_next_stateTrack
    (decoder : SummableExecutableDecoder Code State Visible Certificate)
    (code : decoder.CodePoint) (depth : ℕ) :
    decoder.certificateTarget (decoder.certificate depth code) =
      decoder.stateTrack code (depth + 1) :=
  decoder.certificate_target_eq code code.property depth

/-- Every retained coordinate is a certified legal finite macro. -/
theorem certificate_isLegalMacro
    (decoder : SummableExecutableDecoder Code State Visible Certificate)
    (code : decoder.CodePoint) (depth : ℕ) :
    decoder.legalMacro (decoder.certificate depth code) :=
  decoder.certificate_legal code code.property depth

/-- A Lipschitz reach floor survives decoding when it exceeds the remaining
summable actual-state error. -/
theorem decodedReach_pos_of_tail_lt
    (decoder : SummableExecutableDecoder Code State Visible Certificate)
    (reach : State → ℝ) (lipschitz : ℝ)
    (hlipschitz : 0 ≤ lipschitz)
    (hreach : ∀ first second,
      |reach first - reach second| ≤ lipschitz * dist first second)
    (code : decoder.CodePoint) (depth : ℕ) (floor : ℝ)
    (hfloor : floor ≤ reach (decoder.stateTrack code depth))
    (htail : lipschitz *
      (∑' offset, decoder.stateError (depth + offset)) < floor) :
    0 < reach (decoder.decodedState code) := by
  have hdist := decoder.dist_state_decodedState_le_tail code depth
  have hvariation := hreach
    (decoder.stateTrack code depth) (decoder.decodedState code)
  have hbound :
      |reach (decoder.stateTrack code depth) -
          reach (decoder.decodedState code)| ≤
        lipschitz * (∑' offset, decoder.stateError (depth + offset)) :=
    hvariation.trans <| mul_le_mul_of_nonneg_left hdist hlipschitz
  have hlower := le_of_abs_le hbound
  linarith

/-- Exact minimization may be read at the limit only from a visible error
track which tends to zero along this same complete code. -/
theorem decodedVisible_eq_zero_of_track_tendsto_zero
    [Zero Visible]
    (decoder : SummableExecutableDecoder Code State Visible Certificate)
    (code : decoder.CodePoint)
    (hzero : Tendsto (decoder.visibleTrack code) atTop (nhds 0)) :
    decoder.decodedVisible code = 0 := by
  exact tendsto_nhds_unique (decoder.tendsto_visibleTrack code) hzero

end SummableExecutableDecoder

end Topology
end Math
