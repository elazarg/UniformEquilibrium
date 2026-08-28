/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors.
-/

import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Tactic

/-!
# Source-compatible omega chains in compact spaces

A one-sided sequence in a compact space has a two-sided limiting path after
centering farther and farther along the source.  This module retains one
common center subsequence, not independently selected limits at each integer
offset.  Consequently every finite window of the limiting path is approached
by complete windows of the original source.

This is only a compact dynamical statement.  It does not turn a normalized
state into an underlying game state, payoff, or stationary realization.
-/

noncomputable section

namespace Math
namespace Topology

open Filter Set

variable {Point : Type*} [TopologicalSpace Point]

/-- A one-sided source recentered at `center`, padded by its initial point
only beyond the unavailable negative end.  Every fixed offset is unpadded
eventually as the center tends to infinity. -/
def centeredSequence
    (source : ℕ → Point) (center : ℕ) : ℤ → Point
  | .ofNat offset => source (center + offset)
  | .negSucc offset => source (center - (offset + 1))

/-- One common compact extraction of every integer offset of a one-sided
source sequence. -/
structure SourceOmegaChain (source : ℕ → Point) where
  path : ℤ → Point
  centers : ℕ → ℕ
  centers_strictMono : StrictMono centers
  centered_tendsto :
    Tendsto (fun rank ↦ centeredSequence source (centers rank))
      atTop (nhds path)

namespace SourceOmegaChain

variable {source : ℕ → Point}

theorem centers_tendsto_atTop (chain : SourceOmegaChain source) :
    Tendsto chain.centers atTop atTop :=
  chain.centers_strictMono.tendsto_atTop

/-- Every fixed centered source coordinate converges to the corresponding
integer coordinate of the common limiting path. -/
theorem centered_coordinate_tendsto
    (chain : SourceOmegaChain source) (offset : ℤ) :
    Tendsto
      (fun rank ↦ centeredSequence source (chain.centers rank) offset)
      atTop (nhds (chain.path offset)) := by
  exact ((continuous_apply offset).tendsto chain.path).comp
    chain.centered_tendsto

/-- A globally strict source-date sequence converging to one omega
coordinate.  Negative offsets discard a sufficiently long prefix before
subtracting, so no truncated date is retained. -/
def sourceIndex (chain : SourceOmegaChain source) : ℤ → ℕ → ℕ
  | .ofNat offset => fun rank ↦ chain.centers rank + offset
  | .negSucc offset => fun rank ↦
      chain.centers (rank + offset + 1) - (offset + 1)

theorem sourceIndex_strictMono
    (chain : SourceOmegaChain source) (offset : ℤ) :
    StrictMono (chain.sourceIndex offset) := by
  cases offset with
  | ofNat offset =>
      intro first second hlt
      exact Nat.add_lt_add_right (chain.centers_strictMono hlt) offset
  | negSucc offset =>
      intro first second hlt
      have harguments : first + offset + 1 < second + offset + 1 := by
        omega
      have hcenters := chain.centers_strictMono harguments
      have hfirst := chain.centers_strictMono.id_le (first + offset + 1)
      have hbound : offset + 1 ≤
          chain.centers (first + offset + 1) := by
        exact (Nat.le_add_left (offset + 1) first).trans hfirst
      dsimp only [sourceIndex]
      exact Nat.sub_lt_sub_right hbound hcenters

/-- The strict source dates selected for an integer coordinate converge to
that coordinate of the same common omega path. -/
theorem source_coordinate_tendsto
    (chain : SourceOmegaChain source) (offset : ℤ) :
    Tendsto (fun rank ↦ source (chain.sourceIndex offset rank))
      atTop (nhds (chain.path offset)) := by
  cases offset with
  | ofNat offset =>
      simpa [sourceIndex, centeredSequence] using
        chain.centered_coordinate_tendsto (Int.ofNat offset)
  | negSucc offset =>
      have hshift :=
        (chain.centered_coordinate_tendsto (Int.negSucc offset)).comp
          (tendsto_add_atTop_nat (offset + 1))
      change Tendsto (fun rank ↦ source
        (chain.centers (rank + (offset + 1)) - (offset + 1)))
          atTop (nhds (chain.path (Int.negSucc offset))) at hshift
      simpa [sourceIndex, Nat.add_assoc] using hshift

/-- The radius-`radius` centered window of an integer path. -/
def finiteWindow (radius : ℕ) (path : ℤ → Point) :
    Fin (2 * radius + 1) → Point :=
  fun slot ↦ path (((slot : ℕ) : ℤ) - (radius : ℤ))

/-- The literal contiguous source window of radius `radius` centered at an
actual source index.  The caller supplies a center at least `radius`, so the
left endpoint is not truncated. -/
def sourceFiniteWindow (source : ℕ → Point) (radius center : ℕ) :
    Fin (2 * radius + 1) → Point :=
  fun slot ↦ source (center - radius + slot)

omit [TopologicalSpace Point] in
/-- Once the center is past the radius, the abstract integer-centered window
is literally the contiguous source window with dates
`center - radius, ..., center + radius`. -/
theorem finiteWindow_centeredSequence_eq_sourceFiniteWindow
    (source : ℕ → Point) (radius center : ℕ) (hcenter : radius ≤ center) :
    finiteWindow radius (centeredSequence source center) =
      sourceFiniteWindow source radius center := by
  funext slot
  simp only [finiteWindow, sourceFiniteWindow]
  by_cases hslot : (slot : ℕ) < radius
  · have hoffset : (((slot : ℕ) : ℤ) - (radius : ℤ)) =
        Int.negSucc (radius - slot - 1) := by
      omega
    rw [hoffset]
    simp only [centeredSequence]
    congr 1
    omega
  · have hradius : radius ≤ (slot : ℕ) := Nat.le_of_not_gt hslot
    have hoffset : (((slot : ℕ) : ℤ) - (radius : ℤ)) =
        Int.ofNat ((slot : ℕ) - radius) := by
      exact (Int.ofNat_sub hradius).symm
    rw [hoffset]
    simp only [centeredSequence]
    congr 1
    omega

/-- Complete centered source windows converge jointly to the corresponding
finite limiting window.  The same center subsequence is used at every radius
and every slot. -/
theorem finiteWindow_tendsto
    (chain : SourceOmegaChain source) (radius : ℕ) :
    Tendsto
      (fun rank ↦ finiteWindow radius
        (centeredSequence source (chain.centers rank)))
      atTop (nhds (finiteWindow radius chain.path)) := by
  rw [tendsto_pi_nhds]
  intro slot
  exact chain.centered_coordinate_tendsto
    (((slot : ℕ) : ℤ) - (radius : ℤ))

/-- Literal complete windows from the original one-sided source converge to
the finite window of the omega path.  This is the source-faithful form: one
common center is used for every slot, and the selected dates in a window are
consecutive. -/
theorem sourceFiniteWindow_tendsto
    (chain : SourceOmegaChain source) (radius : ℕ) :
    Tendsto
      (fun rank ↦ sourceFiniteWindow source radius (chain.centers rank))
      atTop (nhds (finiteWindow radius chain.path)) := by
  apply (chain.finiteWindow_tendsto radius).congr'
  filter_upwards [chain.centers_tendsto_atTop.eventually
    (eventually_ge_atTop radius)] with rank hcenter
  exact finiteWindow_centeredSequence_eq_sourceFiniteWindow
    source radius (chain.centers rank) hcenter

/-- A closed relation satisfied at every actual source edge is inherited by
every edge of the common omega path. -/
theorem relation
    (chain : SourceOmegaChain source)
    (edge : Point → Point → Prop)
    (hclosed : IsClosed {pair : Point × Point | edge pair.1 pair.2})
    (hsource : ∀ time, edge (source time) (source (time + 1)))
    (offset : ℤ) :
    edge (chain.path offset) (chain.path (offset + 1)) := by
  have hleft := chain.centered_coordinate_tendsto offset
  have hright := chain.centered_coordinate_tendsto (offset + 1)
  apply hclosed.mem_of_tendsto (hleft.prodMk_nhds hright)
  cases offset with
  | ofNat offset =>
      exact Eventually.of_forall fun rank ↦ by
        have hsuccessor : Int.ofNat offset + 1 =
            Int.ofNat (offset + 1) := by
          norm_num
        rw [hsuccessor]
        simpa [centeredSequence, Nat.add_assoc] using
          hsource (chain.centers rank + offset)
  | negSucc offset =>
      filter_upwards [chain.centers_tendsto_atTop.eventually
        (eventually_ge_atTop (offset + 2))] with rank hcenter
      rcases offset with _ | offset
      · change 2 ≤ chain.centers rank at hcenter
        change edge (source (chain.centers rank - 1))
          (source (chain.centers rank))
        have hdate : chain.centers rank - 1 + 1 =
            chain.centers rank := by
          omega
        simpa only [hdate] using hsource (chain.centers rank - 1)
      · have hsuccessor : Int.negSucc (offset + 1) + 1 =
            Int.negSucc offset := by
          simp [Int.negSucc_eq]
        change offset + 3 ≤ chain.centers rank at hcenter
        rw [hsuccessor]
        simp only [centeredSequence]
        have hdate : chain.centers rank - (offset + 2) + 1 =
            chain.centers rank - (offset + 1) := by
          omega
        simpa only [hdate] using
          hsource (chain.centers rank - (offset + 2))

end SourceOmegaChain

/-- Compact first-countable spaces produce a source-compatible omega
extraction. -/
theorem nonempty_sourceOmegaChain [CompactSpace Point]
    [FirstCountableTopology Point]
    (source : ℕ → Point) :
    Nonempty (SourceOmegaChain source) := by
  obtain ⟨path, centers, hcenters, htendsto⟩ :=
    CompactSpace.tendsto_subseq (fun center ↦ centeredSequence source center)
  exact ⟨{
    path := path
    centers := centers
    centers_strictMono := hcenters
    centered_tendsto := htendsto
  }⟩

end Topology
end Math
