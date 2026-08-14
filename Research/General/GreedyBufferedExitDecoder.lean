/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib

/-!
# Greedy buffered paths: first exits certify failed buffered seriality

Companion to `BufferedOneSeamReturnOrExit.lean`, which checks the CG7
pigeonhole dichotomy along an *arbitrary* serial orbit.  There the exit
branch is weak: an arbitrary orbit may leave the buffer even though a
different successor choice would have stayed inside.

This experiment machine-checks the greedy construction actually described
in `ideas/CycleGeometryResolution.md` §8: while possible, choose a
successor inside the buffer; only when none exists take an outside
successor.  The payoff is a strong exit branch, the hook required by the
CG8 descent decoder:

- the exit time is the **first** exit, so the whole prefix is buffered
  and chronologically attached to the start;
- the pre-exit state provably has **no** admissible successor in the
  buffer — buffered seriality fails there, it was not a bad choice; and
- the potential drop at the exit exceeds `a − b` exactly.

Seriality is assumed only on the ambient set `K`, and every transition of
the constructed path is an exact relation edge.  No anchor preservation,
edge decoding, or optimized-debt conclusion is claimed (those are CG8).
-/


noncomputable section

namespace GameTheory

variable {Point : Type*}

open Classical in
/-- Greedy buffered successor: stay in `K ∩ buffer` if possible, else stay
in `K`, else stand still (never taken from a serial point of `K`). -/
noncomputable def greedyBufferedStep
    (relation : Point → Point → Prop) (K buffer : Set Point)
    (point : Point) : Point :=
  if h : ∃ next, next ∈ K ∧ relation point next ∧ next ∈ buffer then
    h.choose
  else if h' : ∃ next, next ∈ K ∧ relation point next then h'.choose
  else point

/-- The greedy buffered path. -/
noncomputable def greedyBufferedPath
    (relation : Point → Point → Prop) (K buffer : Set Point)
    (entry : Point) : ℕ → Point :=
  fun time ↦ (greedyBufferedStep relation K buffer)^[time] entry

theorem greedyBufferedPath_zero
    (relation : Point → Point → Prop) (K buffer : Set Point)
    (entry : Point) :
    greedyBufferedPath relation K buffer entry 0 = entry := rfl

theorem greedyBufferedPath_succ
    (relation : Point → Point → Prop) (K buffer : Set Point)
    (entry : Point) (time : ℕ) :
    greedyBufferedPath relation K buffer entry (time + 1) =
      greedyBufferedStep relation K buffer
        (greedyBufferedPath relation K buffer entry time) :=
  Function.iterate_succ_apply' _ time entry

/-- From a serial point of `K` the greedy step stays in `K` and is a
genuine relation edge. -/
theorem greedyBufferedStep_mem_and_rel
    (relation : Point → Point → Prop) (K buffer : Set Point)
    (hserial : ∀ point ∈ K, ∃ next ∈ K, relation point next)
    {point : Point} (hpoint : point ∈ K) :
    greedyBufferedStep relation K buffer point ∈ K ∧
      relation point (greedyBufferedStep relation K buffer point) := by
  unfold greedyBufferedStep
  by_cases h : ∃ next, next ∈ K ∧ relation point next ∧ next ∈ buffer
  · rw [dif_pos h]
    exact ⟨h.choose_spec.1, h.choose_spec.2.1⟩
  · rw [dif_neg h]
    have h' : ∃ next, next ∈ K ∧ relation point next := by
      obtain ⟨next, hnextK, hnextR⟩ := hserial point hpoint
      exact ⟨next, hnextK, hnextR⟩
    rw [dif_pos h']
    exact ⟨h'.choose_spec.1, h'.choose_spec.2⟩

/-- Buffer preference: if some admissible successor stays in the buffer,
the greedy step does. -/
theorem greedyBufferedStep_mem_buffer
    (relation : Point → Point → Prop) (K buffer : Set Point)
    {point : Point}
    (h : ∃ next, next ∈ K ∧ relation point next ∧ next ∈ buffer) :
    greedyBufferedStep relation K buffer point ∈ buffer := by
  unfold greedyBufferedStep
  rw [dif_pos h]
  exact h.choose_spec.2.2

/-- **Exit decoder hook.**  If the greedy step leaves the buffer, then no
admissible successor inside `K` is in the buffer: buffered seriality
genuinely fails at the pre-exit state. -/
theorem forall_not_mem_buffer_of_greedyStep_exit
    (relation : Point → Point → Prop) (K buffer : Set Point)
    {point : Point}
    (hstep : greedyBufferedStep relation K buffer point ∉ buffer) :
    ∀ next ∈ K, relation point next → next ∉ buffer := by
  intro next hnextK hnextR hnextBuffer
  exact hstep (greedyBufferedStep_mem_buffer relation K buffer
    ⟨next, hnextK, hnextR, hnextBuffer⟩)

theorem greedyBufferedPath_mem
    (relation : Point → Point → Prop) (K buffer : Set Point)
    (hserial : ∀ point ∈ K, ∃ next ∈ K, relation point next)
    {entry : Point} (hentry : entry ∈ K) :
    ∀ time, greedyBufferedPath relation K buffer entry time ∈ K := by
  intro time
  induction time with
  | zero => exact hentry
  | succ time ih =>
      rw [greedyBufferedPath_succ]
      exact (greedyBufferedStep_mem_and_rel relation K buffer hserial ih).1

theorem greedyBufferedPath_rel
    (relation : Point → Point → Prop) (K buffer : Set Point)
    (hserial : ∀ point ∈ K, ∃ next ∈ K, relation point next)
    {entry : Point} (hentry : entry ∈ K) (time : ℕ) :
    relation (greedyBufferedPath relation K buffer entry time)
      (greedyBufferedPath relation K buffer entry (time + 1)) := by
  rw [greedyBufferedPath_succ]
  exact (greedyBufferedStep_mem_and_rel relation K buffer hserial
    (greedyBufferedPath_mem relation K buffer hserial hentry time)).2

/-- **Greedy buffered return-or-exit with a certified exit.**  From a
start in `K` with potential at least `a ≥ b`, within the covering number
of exact steps, either two buffered path states share one covering cell,
or there is a **first** exit time `N`: the prefix is entirely buffered,
the potential drop exceeds `a − b`, and the pre-exit state has no
admissible successor in the buffer at all. -/
theorem greedyBufferedPath_return_or_certified_exit
    {Cell : Type*} [Fintype Cell]
    (relation : Point → Point → Prop) (K : Set Point)
    (Φ : Point → ℝ) {a b : ℝ} (hab : b ≤ a)
    (hserial : ∀ point ∈ K, ∃ next ∈ K, relation point next)
    (cell : Point → Cell)
    {entry : Point} (hentry : entry ∈ K) (hentryΦ : a ≤ Φ entry) :
    ∃ path : ℕ → Point,
      path 0 = entry ∧
      (∀ time, relation (path time) (path (time + 1))) ∧
      (∀ time, path time ∈ K) ∧
      ((∃ first last : ℕ, first < last ∧ last ≤ Fintype.card Cell ∧
          (∀ time, time ≤ Fintype.card Cell → b ≤ Φ (path time)) ∧
          cell (path first) = cell (path last)) ∨
        (∃ N : ℕ, 0 < N ∧ N ≤ Fintype.card Cell ∧
          Φ (path N) < b ∧
          (∀ time, time < N → b ≤ Φ (path time)) ∧
          a - b < Φ entry - Φ (path N) ∧
          ∀ next ∈ K, relation (path (N - 1)) next → Φ next < b)) := by
  classical
  set buffer : Set Point := {point | b ≤ Φ point} with hbufferdef
  set path : ℕ → Point := greedyBufferedPath relation K buffer entry
    with hpathdef
  refine ⟨path, rfl,
    fun time ↦ greedyBufferedPath_rel relation K buffer hserial hentry time,
    fun time ↦ greedyBufferedPath_mem relation K buffer hserial hentry time,
    ?_⟩
  by_cases hall : ∀ time, time ≤ Fintype.card Cell → path time ∈ buffer
  · left
    have hcard : Fintype.card Cell <
        Fintype.card (Fin (Fintype.card Cell + 1)) := by simp
    obtain ⟨first, last, hne, hsame⟩ :=
      Fintype.exists_ne_map_eq_of_card_lt
        (fun time : Fin (Fintype.card Cell + 1) ↦ cell (path time.val)) hcard
    have hmem : ∀ time, time ≤ Fintype.card Cell → b ≤ Φ (path time) :=
      fun time htime ↦ hall time htime
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact ⟨first.val, last.val, hlt, Nat.lt_succ_iff.mp last.isLt,
        hmem, hsame⟩
    · exact ⟨last.val, first.val, hgt, Nat.lt_succ_iff.mp first.isLt,
        hmem, hsame.symm⟩
  · right
    push Not at hall
    obtain ⟨exitWitness, hwitnessLe, hwitnessOut⟩ := hall
    have hexists : ∃ N, path N ∉ buffer := ⟨exitWitness, hwitnessOut⟩
    set N := Nat.find hexists with hNdef
    have hNout : path N ∉ buffer := Nat.find_spec hexists
    have hNleast : ∀ time, time < N → path time ∈ buffer := by
      intro time htime
      by_contra hnot
      exact Nat.find_min hexists htime hnot
    have hNle : N ≤ exitWitness := Nat.find_min' hexists hwitnessOut
    have hNn : N ≤ Fintype.card Cell := le_trans hNle hwitnessLe
    have hentryBuffer : path 0 ∈ buffer := by
      change b ≤ Φ entry
      linarith
    have hNpos : 0 < N := by
      rcases Nat.eq_zero_or_pos N with hzero | hpos
      · rw [hzero] at hNout
        exact absurd hentryBuffer hNout
      · exact hpos
    have hNΦ : Φ (path N) < b := lt_of_not_ge hNout
    refine ⟨N, hNpos, hNn, hNΦ,
      fun time htime ↦ hNleast time htime, by linarith, ?_⟩
    have hstep : path N =
        greedyBufferedStep relation K buffer (path (N - 1)) := by
      rw [show N = (N - 1) + 1 by omega]
      exact greedyBufferedPath_succ relation K buffer entry (N - 1)
    intro next hnextK hnextR
    have hnot := forall_not_mem_buffer_of_greedyStep_exit relation K buffer
      (point := path (N - 1)) (by rw [← hstep]; exact hNout)
      next hnextK hnextR
    exact lt_of_not_ge hnot

/-! ## Dead-end-aware trichotomy (no seriality assumed) -/

/-- No admissible successor inside `K`. -/
def RelationDeadEnd (relation : Point → Point → Prop) (K : Set Point)
    (point : Point) : Prop :=
  ¬∃ next, next ∈ K ∧ relation point next

/-- Away from a dead end, the greedy step stays in `K` and is a genuine
relation edge (no seriality hypothesis). -/
theorem greedyBufferedStep_mem_and_rel_of_not_deadEnd
    (relation : Point → Point → Prop) (K buffer : Set Point)
    {point : Point} (hnot : ¬RelationDeadEnd relation K point) :
    greedyBufferedStep relation K buffer point ∈ K ∧
      relation point (greedyBufferedStep relation K buffer point) := by
  rw [RelationDeadEnd, not_not] at hnot
  unfold greedyBufferedStep
  by_cases h : ∃ next, next ∈ K ∧ relation point next ∧ next ∈ buffer
  · rw [dif_pos h]
    exact ⟨h.choose_spec.1, h.choose_spec.2.1⟩
  · rw [dif_neg h, dif_pos hnot]
    exact ⟨hnot.choose_spec.1, hnot.choose_spec.2⟩

/-- Membership along a prefix with no dead end. -/
theorem greedyBufferedPath_mem_of_no_deadEnd
    (relation : Point → Point → Prop) (K buffer : Set Point)
    {entry : Point} (hentry : entry ∈ K) (horizon : ℕ)
    (hnodead : ∀ t, t < horizon →
      ¬RelationDeadEnd relation K
        (greedyBufferedPath relation K buffer entry t)) :
    ∀ t, t ≤ horizon →
      greedyBufferedPath relation K buffer entry t ∈ K := by
  intro t
  induction t with
  | zero => intro _; exact hentry
  | succ t _ih =>
      intro ht
      rw [greedyBufferedPath_succ]
      exact (greedyBufferedStep_mem_and_rel_of_not_deadEnd relation K buffer
        (hnodead t (by omega))).1

/-- Away from a dead end the path takes a genuine relation edge; no
membership of the current state is needed. -/
theorem greedyBufferedPath_rel_of_not_deadEnd
    (relation : Point → Point → Prop) (K buffer : Set Point)
    (entry : Point) (time : ℕ)
    (hnot : ¬RelationDeadEnd relation K
      (greedyBufferedPath relation K buffer entry time)) :
    relation (greedyBufferedPath relation K buffer entry time)
      (greedyBufferedPath relation K buffer entry (time + 1)) := by
  rw [greedyBufferedPath_succ]
  exact (greedyBufferedStep_mem_and_rel_of_not_deadEnd relation K buffer
    hnot).2

/-- **Greedy trichotomy without seriality.**  From a buffered start in `K`,
within the covering number of steps: a one-seam return with the whole
displayed horizon buffered, or a certified first exit (prefix buffered,
potential drop above `a − b`, no buffered successor at the pre-exit state),
or a typed dead end: an exact buffered prefix ending at a state of `K`
with no admissible successor at all. -/
theorem greedyBufferedPath_return_or_certified_exit_or_deadEnd
    {Cell : Type*} [Fintype Cell]
    (relation : Point → Point → Prop) (K : Set Point)
    (Φ : Point → ℝ) {a b : ℝ} (hab : b ≤ a)
    (cell : Point → Cell)
    {entry : Point} (hentry : entry ∈ K) (hentryΦ : a ≤ Φ entry) :
    ∃ path : ℕ → Point,
      path 0 = entry ∧
      ((∃ first last : ℕ, first < last ∧ last ≤ Fintype.card Cell ∧
          (∀ time, time < Fintype.card Cell →
            relation (path time) (path (time + 1))) ∧
          (∀ time, time ≤ Fintype.card Cell →
            path time ∈ K ∧ b ≤ Φ (path time)) ∧
          cell (path first) = cell (path last)) ∨
        (∃ N : ℕ, 0 < N ∧ N ≤ Fintype.card Cell ∧
          (∀ time, time < N → relation (path time) (path (time + 1))) ∧
          (∀ time, time < N → path time ∈ K ∧ b ≤ Φ (path time)) ∧
          path N ∈ K ∧ Φ (path N) < b ∧
          a - b < Φ entry - Φ (path N) ∧
          (∀ next ∈ K, relation (path (N - 1)) next → Φ next < b)) ∨
        (∃ D : ℕ, D ≤ Fintype.card Cell ∧
          (∀ time, time < D → relation (path time) (path (time + 1))) ∧
          (∀ time, time ≤ D → path time ∈ K) ∧
          RelationDeadEnd relation K (path D))) := by
  classical
  set buffer : Set Point := {point | b ≤ Φ point} with hbufferdef
  set path : ℕ → Point := greedyBufferedPath relation K buffer entry
    with hpathdef
  refine ⟨path, rfl, ?_⟩
  by_cases hdead :
      ∃ D ≤ Fintype.card Cell, RelationDeadEnd relation K (path D)
  · right; right
    obtain ⟨witness, hwitnessLe, hwitnessDead⟩ := hdead
    have hexists : ∃ D, RelationDeadEnd relation K (path D) :=
      ⟨witness, hwitnessDead⟩
    set D := Nat.find hexists with hDdef
    have hDspec : RelationDeadEnd relation K (path D) := Nat.find_spec hexists
    have hDle : D ≤ Fintype.card Cell :=
      le_trans (Nat.find_min' hexists hwitnessDead) hwitnessLe
    have hDmin : ∀ t, t < D → ¬RelationDeadEnd relation K (path t) :=
      fun t ht ↦ Nat.find_min hexists ht
    exact ⟨D, hDle,
      fun time htime ↦ greedyBufferedPath_rel_of_not_deadEnd relation K buffer
        entry time (hDmin time htime),
      greedyBufferedPath_mem_of_no_deadEnd relation K buffer hentry D hDmin,
      hDspec⟩
  · push Not at hdead
    have hmemK : ∀ t, t ≤ Fintype.card Cell → path t ∈ K :=
      greedyBufferedPath_mem_of_no_deadEnd relation K buffer hentry
        (Fintype.card Cell) (fun t ht ↦ hdead t ht.le)
    have hrelAll : ∀ t, t < Fintype.card Cell →
        relation (path t) (path (t + 1)) :=
      fun t ht ↦ greedyBufferedPath_rel_of_not_deadEnd relation K buffer entry t
        (hdead t ht.le)
    by_cases hall : ∀ time, time ≤ Fintype.card Cell → path time ∈ buffer
    · left
      have hcard : Fintype.card Cell <
          Fintype.card (Fin (Fintype.card Cell + 1)) := by simp
      obtain ⟨first, last, hne, hsame⟩ :=
        Fintype.exists_ne_map_eq_of_card_lt
          (fun time : Fin (Fintype.card Cell + 1) ↦ cell (path time.val)) hcard
      have hstates : ∀ time, time ≤ Fintype.card Cell →
          path time ∈ K ∧ b ≤ Φ (path time) :=
        fun time htime ↦ ⟨hmemK time htime, hall time htime⟩
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · exact ⟨first.val, last.val, hlt, Nat.lt_succ_iff.mp last.isLt,
          hrelAll, hstates, hsame⟩
      · exact ⟨last.val, first.val, hgt, Nat.lt_succ_iff.mp first.isLt,
          hrelAll, hstates, hsame.symm⟩
    · right; left
      push Not at hall
      obtain ⟨exitWitness, hwitnessLe, hwitnessOut⟩ := hall
      have hexists : ∃ N, path N ∉ buffer := ⟨exitWitness, hwitnessOut⟩
      set N := Nat.find hexists with hNdef
      have hNout : path N ∉ buffer := Nat.find_spec hexists
      have hNleast : ∀ time, time < N → path time ∈ buffer := by
        intro time htime
        by_contra hnot
        exact Nat.find_min hexists htime hnot
      have hNn : N ≤ Fintype.card Cell :=
        le_trans (Nat.find_min' hexists hwitnessOut) hwitnessLe
      have hentryBuffer : path 0 ∈ buffer := by
        change b ≤ Φ entry
        linarith
      have hNpos : 0 < N := by
        rcases Nat.eq_zero_or_pos N with hzero | hpos
        · rw [hzero] at hNout
          exact absurd hentryBuffer hNout
        · exact hpos
      have hNΦ : Φ (path N) < b := lt_of_not_ge hNout
      refine ⟨N, hNpos, hNn,
        fun time htime ↦ hrelAll time (lt_of_lt_of_le htime hNn),
        fun time htime ↦ ⟨hmemK time (le_of_lt (lt_of_lt_of_le htime hNn)),
          hNleast time htime⟩,
        hmemK N hNn, hNΦ, by linarith, ?_⟩
      have hstep : path N =
          greedyBufferedStep relation K buffer (path (N - 1)) := by
        rw [show N = (N - 1) + 1 by omega]
        exact greedyBufferedPath_succ relation K buffer entry (N - 1)
      intro next hnextK hnextR
      have hnot := forall_not_mem_buffer_of_greedyStep_exit relation K buffer
        (point := path (N - 1)) (by rw [← hstep]; exact hNout)
        next hnextK hnextR
      exact lt_of_not_ge hnot


end GameTheory
