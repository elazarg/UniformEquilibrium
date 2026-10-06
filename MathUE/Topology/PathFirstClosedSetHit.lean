import Mathlib.Topology.Connected.PathConnected
import Mathlib.Topology.Order.Compact

/-! # Clipping a path at its first encounter with a closed set

The clipped path stays in the original path image and in the starting
complement component until it reaches the closed set. This is the path-clipping
step used in selected-component filling arguments. The target requires only a
topology; no metric or separation axiom and no finite component family is used.
-/

noncomputable section

namespace Math.Topology

open Set

variable {X : Type*} [TopologicalSpace X] {first last : X}

/-- Constant-extension truncation with its literal initial and moving endpoint. -/
def pathInitialSegment (path : Path first last) (time : unitInterval) :
    Path first (path time) :=
  (path.truncateOfLE (t₀ := 0) (t₁ := time.val) time.property.1).cast
    path.extend_zero.symm (path.extend_extends' time).symm

theorem pathInitialSegment_apply (path : Path first last) (time parameter : unitInterval) :
    pathInitialSegment path time parameter =
      path ⟨min parameter.val time.val,
        ⟨le_min parameter.property.1 time.property.1,
          (min_le_left _ _).trans parameter.property.2⟩⟩ := by
  change path.extend (min (max parameter.val 0) time.val) = _
  rw [max_eq_left parameter.property.1]
  exact path.extend_extends' ⟨min parameter.val time.val,
    ⟨le_min parameter.property.1 time.property.1,
      (min_le_left _ _).trans parameter.property.2⟩⟩

/-- The first hitting time exists by compactness of the closed time preimage. -/
theorem exists_first_closedSet_hit (path : Path first last) {closed : Set X}
    (hclosed : IsClosed closed) (hlast : last ∈ closed) :
    ∃ time : unitInterval, path time ∈ closed ∧
      ∀ earlier : unitInterval, earlier < time → path earlier ∉ closed := by
  have hnonempty : (path ⁻¹' closed).Nonempty :=
    ⟨1, by simpa only [mem_preimage, path.target] using hlast⟩
  obtain ⟨time, htime, hleast⟩ :=
    (hclosed.preimage path.continuous).isCompact.exists_isLeast hnonempty
  refine ⟨time, htime, ?_⟩
  intro earlier hearlier hmem
  exact (not_le_of_gt hearlier) (hleast hmem)

/-- Before a first hit, every visited point lies in the starting path component
of the complement. The proof uses an actual clipped path, not connectedness alone. -/
theorem mem_pathComponentIn_before_first_hit (path : Path first last) {closed : Set X}
    {hit : unitInterval}
    (hbefore : ∀ earlier : unitInterval, earlier < hit → path earlier ∉ closed)
    {time : unitInterval} (htime : time < hit) :
    path time ∈ pathComponentIn closedᶜ first := by
  refine ⟨pathInitialSegment path time, ?_⟩
  intro parameter
  rw [pathInitialSegment_apply]
  apply hbefore
  change min parameter.val time.val < hit.val
  exact lt_of_le_of_lt (min_le_right _ _) htime

/-- Clip at the first hit of a closed set. The whole resulting path is still
inside the original image and inside the starting complement component or the
closed set. This retains any additional neighborhood constraint on the input path. -/
theorem exists_path_to_first_closedSet_hit (path : Path first last) {closed : Set X}
    (hclosed : IsClosed closed) (hlast : last ∈ closed) :
    ∃ time : unitInterval, path time ∈ closed ∧
      (∀ earlier : unitInterval, earlier < time → path earlier ∉ closed) ∧
      ∃ clipped : Path first (path time),
        Set.range clipped ⊆ Set.range path ∩ (closed ∪ pathComponentIn closedᶜ first) := by
  obtain ⟨time, htime, hbefore⟩ := exists_first_closedSet_hit path hclosed hlast
  refine ⟨time, htime, hbefore, pathInitialSegment path time, ?_⟩
  rintro point ⟨parameter, rfl⟩
  rw [pathInitialSegment_apply]
  let clippedTime : unitInterval := ⟨min parameter.val time.val,
    ⟨le_min parameter.property.1 time.property.1,
      (min_le_left _ _).trans parameter.property.2⟩⟩
  change path clippedTime ∈ Set.range path ∩ (closed ∪ pathComponentIn closedᶜ first)
  refine ⟨⟨clippedTime, rfl⟩, ?_⟩
  have hle : clippedTime ≤ time := min_le_right parameter.val time.val
  rcases lt_or_eq_of_le hle with hlt | heq
  · exact Or.inr (mem_pathComponentIn_before_first_hit path hbefore hlt)
  · exact Or.inl (heq.symm ▸ htime)

end Math.Topology
