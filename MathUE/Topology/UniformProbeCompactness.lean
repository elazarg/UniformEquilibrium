/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Topology.MetricSpace.Sequences

/-!
# Compactness obstructions from one common probe modulus

A labelled family of observables may separate a sequence even when every
individual observable is harmless.  If all labels share one epsilon--delta
modulus through a metric state map, that observable separation becomes metric
separation of the state images.  Such a family cannot lie in a sequentially
compact set and cannot admit one finite approximation net at the resulting
resolution.

The modulus below is common to every label.  Nothing here obstructs continuity
at one fixed label or a modulus chosen after restricting to finitely many
labels.
-/

namespace Math

open Filter

variable {Source State Label Observation : Type*}
variable [PseudoMetricSpace State] [PseudoMetricSpace Observation]

/-- One epsilon--delta modulus controls every labelled probe through the same
metric state map. -/
def HasCommonProbeModulus
    (probe : Label → Source → Observation) (state : Source → State) : Prop :=
  ∀ ε, 0 < ε → ∃ δ, 0 < δ ∧
    ∀ first second, dist (state first) (state second) < δ →
      ∀ label, dist (probe label first) (probe label second) < ε

/-- A common probe modulus transfers a uniform observable separation to a
uniform separation of the corresponding state images. -/
theorem exists_uniform_stateSeparation_of_commonProbeModulus
    (probe : ℕ → Source → Observation) (state : Source → State)
    (source : ℕ → Source) {gap : ℝ} (hgap : 0 < gap)
    (hprobe : ∀ {first second : ℕ}, first ≠ second →
      gap ≤ dist (probe first (source first)) (probe first (source second)))
    (hmodulus : HasCommonProbeModulus probe state) :
    ∃ δ, 0 < δ ∧ ∀ {first second : ℕ}, first ≠ second →
      δ ≤ dist (state (source first)) (state (source second)) := by
  obtain ⟨δ, hδ, hcontrol⟩ := hmodulus gap hgap
  refine ⟨δ, hδ, ?_⟩
  intro first second hne
  by_contra hnot
  have hstate : dist (state (source first)) (state (source second)) < δ :=
    lt_of_not_ge hnot
  exact (not_lt_of_ge (hprobe hne))
    (hcontrol (source first) (source second) hstate first)

/-- An infinite uniformly separated sequence cannot be contained in a
sequentially compact metric set. -/
theorem not_isSeqCompact_of_uniform_stateSeparation
    (point : ℕ → State) {carrier : Set State} {gap : ℝ} (hgap : 0 < gap)
    (hpoint : ∀ index, point index ∈ carrier)
    (hseparated : ∀ {first second : ℕ}, first ≠ second →
      gap ≤ dist (point first) (point second)) :
    ¬IsSeqCompact carrier := by
  intro hcompact
  have hfrequent : ∃ᶠ index in atTop, point index ∈ carrier :=
    (Eventually.of_forall hpoint).frequently
  obtain ⟨limit, -, subsequence, hsubsequence, hlimit⟩ :=
    hcompact.subseq_of_frequently_in hfrequent
  obtain ⟨start, hstart⟩ :=
    (Metric.tendsto_atTop.mp hlimit) (gap / 2) (half_pos hgap)
  have hfirst := hstart start le_rfl
  have hsecond := hstart (start + 1) (Nat.le_add_right start 1)
  have hindices : subsequence start ≠ subsequence (start + 1) := by
    exact ne_of_lt (hsubsequence (Nat.lt_succ_self start))
  have htriangle :
      dist (point (subsequence start)) (point (subsequence (start + 1))) < gap := by
    calc
      dist (point (subsequence start)) (point (subsequence (start + 1))) ≤
          dist (point (subsequence start)) limit +
            dist limit (point (subsequence (start + 1))) := dist_triangle _ _ _
      _ = dist (point (subsequence start)) limit +
            dist (point (subsequence (start + 1))) limit := by
          rw [dist_comm limit]
      _ < gap / 2 + gap / 2 := add_lt_add hfirst hsecond
      _ = gap := by ring
  exact (not_lt_of_ge (hseparated hindices)) htriangle

/-- No finite family of centers covers an infinite uniformly separated
sequence by open balls of radius strictly below half the separation. -/
theorem not_exists_finite_net_of_uniform_stateSeparation
    (point : ℕ → State) {gap radius : ℝ} (hradius : 2 * radius < gap)
    (hseparated : ∀ {first second : ℕ}, first ≠ second →
      gap ≤ dist (point first) (point second)) :
    ¬∃ centers : Set State, centers.Finite ∧
      ∀ index, ∃ center ∈ centers, dist (point index) center < radius := by
  rintro ⟨centers, hcenters, hcover⟩
  choose center hcenterMem hcenterDist using hcover
  have hcenterInjective : Function.Injective center := by
    intro first second heq
    by_contra hne
    have htriangle : dist (point first) (point second) < 2 * radius := by
      calc
        dist (point first) (point second) ≤
            dist (point first) (center first) +
              dist (center first) (point second) := dist_triangle _ _ _
        _ = dist (point first) (center first) +
              dist (point second) (center second) := by
            rw [heq, dist_comm (center second)]
        _ < radius + radius := add_lt_add (hcenterDist first) (hcenterDist second)
        _ = 2 * radius := by ring
    exact (not_lt_of_ge (hseparated hne)) (htriangle.trans hradius)
  have hinfinite : (Set.range center).Infinite :=
    Set.infinite_range_of_injective hcenterInjective
  exact hinfinite (hcenters.subset fun value hvalue => by
    obtain ⟨index, rfl⟩ := hvalue
    exact hcenterMem index)

/-- Common-modulus capstone: a uniformly separated probe family cannot map
into one sequentially compact carrier. -/
theorem not_isSeqCompact_of_commonProbeModulus
    (probe : ℕ → Source → Observation) (state : Source → State)
    (source : ℕ → Source) {carrier : Set State} {gap : ℝ} (hgap : 0 < gap)
    (hsource : ∀ index, state (source index) ∈ carrier)
    (hprobe : ∀ {first second : ℕ}, first ≠ second →
      gap ≤ dist (probe first (source first)) (probe first (source second)))
    (hmodulus : HasCommonProbeModulus probe state) :
    ¬IsSeqCompact carrier := by
  obtain ⟨δ, hδ, hseparated⟩ :=
    exists_uniform_stateSeparation_of_commonProbeModulus
      probe state source hgap hprobe hmodulus
  exact not_isSeqCompact_of_uniform_stateSeparation
    (fun index => state (source index)) hδ hsource hseparated

/-- Common-modulus finite-net capstone.  The radius is produced from the
common modulus and is independent of the probe label. -/
theorem exists_no_finite_net_of_commonProbeModulus
    (probe : ℕ → Source → Observation) (state : Source → State)
    (source : ℕ → Source) {gap : ℝ} (hgap : 0 < gap)
    (hprobe : ∀ {first second : ℕ}, first ≠ second →
      gap ≤ dist (probe first (source first)) (probe first (source second)))
    (hmodulus : HasCommonProbeModulus probe state) :
    ∃ radius, 0 < radius ∧
      ¬∃ centers : Set State, centers.Finite ∧
        ∀ index, ∃ center ∈ centers,
          dist (state (source index)) center < radius := by
  obtain ⟨δ, hδ, hseparated⟩ :=
    exists_uniform_stateSeparation_of_commonProbeModulus
      probe state source hgap hprobe hmodulus
  refine ⟨δ / 3, by positivity, ?_⟩
  exact not_exists_finite_net_of_uniform_stateSeparation
    (point := fun index => state (source index)) (gap := δ) (radius := δ / 3)
      (by linarith) hseparated

end Math
