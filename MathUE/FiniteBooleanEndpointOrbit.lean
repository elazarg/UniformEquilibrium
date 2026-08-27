/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Data.Fintype.Powerset
import Mathlib.Tactic

/-!
# Bounded finite orbits and Boolean coalition counts

This file contains the game-independent finite combinatorics used by
same-stage endpoint arguments.  An orbit in a finite type has a repeated
vertex before the cardinality bound, and hence a closed segment of bounded
positive period.  It also records the number of non-singleton coalitions.

No semantic or strategy assumptions are made here.  A game-facing argument
must supply the orbit and prove that it remains in the finite subtype it
chooses as its state space.
-/

namespace MathUE.FiniteBooleanEndpointOrbit

universe u

variable {State : Type u} [Fintype State]

/-- A bounded repetition in a natural-number orbit. -/
structure BoundedRepeat (orbit : ℕ → State) where
  /-- The beginning of the repeated segment. -/
  first : ℕ
  /-- The first endpoint after the beginning of the repeated segment. -/
  second : ℕ
  /-- The repeated endpoint is strictly later. -/
  first_lt_second : first < second
  /-- The orbit has the same state at both endpoints. -/
  closes_at : orbit first = orbit second
  /-- The endpoint occurs within the finite pigeonhole window. -/
  second_le_card : second ≤ Fintype.card State

/-- Every orbit in a finite type has a bounded positive repetition. -/
theorem exists_boundedRepeat (orbit : ℕ → State) :
    Nonempty (BoundedRepeat orbit) := by
  let sampled : Fin (Fintype.card State + 1) → State := fun time => orbit time
  have hnot_injective : ¬Function.Injective sampled := by
    intro hinjective
    have hcard : Fintype.card (Fin (Fintype.card State + 1)) ≤
        Fintype.card State :=
      Fintype.card_le_of_injective sampled hinjective
    simp only [Fintype.card_fin] at hcard
    omega
  have hcollision : ∃ first second, first ≠ second ∧
      sampled first = sampled second := by
    by_contra hno
    apply hnot_injective
    intro first second hfirst_second
    by_contra hne
    exact hno ⟨first, second, hne, hfirst_second⟩
  obtain ⟨first, second, hne, hrepeat⟩ := hcollision
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · refine ⟨{
      first := first
      second := second
      first_lt_second := hlt
      closes_at := hrepeat
      second_le_card := by omega
    }⟩
  · refine ⟨{
      first := second
      second := first
      first_lt_second := hgt
      closes_at := hrepeat.symm
      second_le_card := by omega
    }⟩

/-- A closed positive-period segment of an orbit. -/
structure ClosedSegment (orbit : ℕ → State) where
  /-- The segment's starting time. -/
  start : ℕ
  /-- Its positive period. -/
  period : ℕ
  /-- The period is positive. -/
  period_pos : 0 < period
  /-- The period is bounded by the state-space cardinality. -/
  period_le_card : period ≤ Fintype.card State
  /-- The endpoint of the segment is within the same cardinality window. -/
  end_le_card : start + period ≤ Fintype.card State
  /-- The segment closes at its endpoints. -/
  closes : orbit (start + period) = orbit start

/-- A bounded repetition gives a bounded closed positive-period segment. -/
theorem exists_boundedClosedSegment (orbit : ℕ → State) :
    Nonempty (ClosedSegment orbit) := by
  obtain ⟨bounded⟩ := exists_boundedRepeat orbit
  let period := bounded.second - bounded.first
  have hlt := bounded.first_lt_second
  have hsecond := bounded.second_le_card
  have hperiod_pos : 0 < period := by
    dsimp only [period]
    omega
  have hsum : bounded.first + period = bounded.second := by
    dsimp only [period]
    omega
  refine ⟨{
    start := bounded.first
    period := period
    period_pos := hperiod_pos
    period_le_card := by
      dsimp only [period]
      omega
    end_le_card := by
      rw [hsum]
      exact bounded.second_le_card
    closes := by
      rw [hsum]
      exact bounded.closes_at.symm
  }⟩

/-- A closed segment whose offsets before one period are pairwise distinct. -/
structure MinimalClosedSegment (orbit : ℕ → State) where
  /-- The underlying bounded closed segment. -/
  segment : ClosedSegment orbit
  /-- Distinct offsets give distinct states before the closing endpoint. -/
  offset_injective : Function.Injective (fun offset : Fin segment.period =>
    orbit (segment.start + offset))

/-- Every finite orbit has a bounded closed segment with a simple period. -/
theorem exists_minimalClosedSegment (orbit : ℕ → State) :
    Nonempty (MinimalClosedSegment orbit) := by
  classical
  let hasRepeat : ℕ → Prop := fun endpoint =>
    ∃ first, first < endpoint ∧ orbit first = orbit endpoint
  obtain ⟨bounded⟩ := exists_boundedRepeat orbit
  have hexists : ∃ endpoint, hasRepeat endpoint := by
    refine ⟨bounded.second, bounded.first, bounded.first_lt_second, ?_⟩
    exact bounded.closes_at
  let endpoint := Nat.find hexists
  have hendpoint : hasRepeat endpoint := Nat.find_spec hexists
  have hminimal : ∀ candidate, hasRepeat candidate → endpoint ≤ candidate := by
    intro candidate hcandidate
    exact Nat.find_min' hexists hcandidate
  obtain ⟨first, hfirst, hclose⟩ := hendpoint
  have hendpoint_card : endpoint ≤ Fintype.card State := by
    apply (hminimal bounded.second ?_).trans bounded.second_le_card
    exact ⟨bounded.first, bounded.first_lt_second, bounded.closes_at⟩
  let period := endpoint - first
  have hperiod_pos : 0 < period := by
    dsimp only [period]
    omega
  have hsum : first + period = endpoint := by
    dsimp only [period]
    omega
  have hperiod_card : period ≤ Fintype.card State := by
    dsimp only [period]
    omega
  have hend_le_card : first + period ≤ Fintype.card State := by
    rw [hsum]
    exact hendpoint_card
  have hoffsets : Function.Injective (fun offset : Fin period =>
      orbit (first + offset)) := by
    intro left right heq
    by_contra hne
    rcases lt_or_gt_of_ne hne with hleft | hright
    · have hcandidate : hasRepeat (first + right) := by
        refine ⟨first + left, ?_, ?_⟩
        · omega
        · exact heq
      have hbound := hminimal (first + right) hcandidate
      omega
    · have hcandidate : hasRepeat (first + left) := by
        refine ⟨first + right, ?_, ?_⟩
        · omega
        · exact heq.symm
      have hbound := hminimal (first + left) hcandidate
      omega
  refine ⟨{
    segment := {
      start := first
      period := period
      period_pos := hperiod_pos
      period_le_card := hperiod_card
      end_le_card := hend_le_card
      closes := by
        rw [hsum]
        exact hclose.symm
    }
    offset_injective := by
      exact hoffsets
  }⟩

/-- A bounded orbit stopped at its first terminal vertex.

The edge relation is part of the data: every step strictly before
`terminal_time` is certified.  No edge is asserted from the terminal vertex.
The explicit first-terminal field lets game-facing consumers recover the
whole finite dispatched path without reconstructing the choice function used
by the existence theorem. -/
structure DispatchedOrbit (terminal : State → Prop)
    (edge : State → State → Prop) (start : State) where
  /-- The orbit chosen from the local dispatch rule. -/
  orbit : ℕ → State
  /-- The orbit starts at the supplied state. -/
  orbit_zero : orbit 0 = start
  /-- A terminal vertex occurs in the bounded prefix. -/
  terminal_time : Fin (Fintype.card State + 1)
  /-- No earlier vertex is terminal. -/
  not_terminal_before : ∀ time : ℕ, time < terminal_time →
    ¬terminal (orbit time)
  /-- Every step before the first terminal vertex is a dispatched edge. -/
  edge_before : ∀ time : ℕ, time < terminal_time →
    edge (orbit time) (orbit (time + 1))
  terminal_at : terminal (orbit terminal_time)

namespace DispatchedOrbit

/-- Forget some edge data while retaining the identical stopped orbit. -/
def mapEdge
    {terminal : State → Prop} {edge edge' : State → State → Prop}
    {start : State} (trace : DispatchedOrbit terminal edge start)
    (map : ∀ source target, edge source target → edge' source target) :
    DispatchedOrbit terminal edge' start where
  orbit := trace.orbit
  orbit_zero := trace.orbit_zero
  terminal_time := trace.terminal_time
  not_terminal_before := trace.not_terminal_before
  edge_before := fun time htime =>
    map _ _ (trace.edge_before time htime)
  terminal_at := trace.terminal_at

end DispatchedOrbit

/-- A closed segment of an orbit whose in-period steps are dispatched edges. -/
structure DispatchedClosedSegment (terminal : State → Prop)
    (edge : State → State → Prop) (start : State) where
  /-- The total orbit used by the segment. -/
  orbit : ℕ → State
  /-- The bounded simple closed segment. -/
  segment : MinimalClosedSegment orbit
  /-- The orbit starts at the supplied state. -/
  orbit_zero : orbit 0 = start
  /-- No vertex in the period is terminal. -/
  offset_not_terminal : ∀ offset : Fin segment.segment.period,
    ¬terminal (orbit (segment.segment.start + offset))
  /-- Every in-period successor is an edge of the supplied relation. -/
  offset_edge : ∀ offset : Fin segment.segment.period,
    edge (orbit (segment.segment.start + offset))
      (orbit (segment.segment.start + offset + 1))

namespace DispatchedClosedSegment

/-- Forget some edge data while retaining the identical closed segment. -/
def mapEdge
    {terminal : State → Prop} {edge edge' : State → State → Prop}
    {start : State} (trace : DispatchedClosedSegment terminal edge start)
    (map : ∀ source target, edge source target → edge' source target) :
    DispatchedClosedSegment terminal edge' start where
  orbit := trace.orbit
  segment := trace.segment
  orbit_zero := trace.orbit_zero
  offset_not_terminal := trace.offset_not_terminal
  offset_edge := fun offset => map _ _ (trace.offset_edge offset)

end DispatchedClosedSegment

/-- Local dispatch gives either a bounded terminal occurrence or a bounded
simple closed segment.  No edge is asserted after a terminal vertex. -/
theorem exists_dispatchedOrbit_terminal_or_closedSegment
    (terminal : State → Prop) (edge : State → State → Prop)
    (dispatch : ∀ state, terminal state ∨ ∃ next, edge state next)
    (start : State) :
    Nonempty (DispatchedOrbit terminal edge start) ∨
      Nonempty (DispatchedClosedSegment terminal edge start) := by
  classical
  let successor : State → State := fun state =>
    if hterminal : terminal state then state else
      Classical.choose ((dispatch state).resolve_left hterminal)
  have hsuccessor : ∀ state, ¬terminal state → edge state (successor state) := by
    intro state hterminal
    dsimp only [successor]
    rw [dif_neg hterminal]
    exact Classical.choose_spec ((dispatch state).resolve_left hterminal)
  let orbit : ℕ → State := fun time => (successor^[time]) start
  have horbit_zero : orbit 0 = start := by
    simp only [orbit, Function.iterate_zero_apply]
  have horbit_succ : ∀ time, orbit (time + 1) = successor (orbit time) := by
    intro time
    dsimp only [orbit]
    rw [Function.iterate_succ_apply']
  by_cases hterminal : ∃ time : Fin (Fintype.card State + 1),
      terminal (orbit time)
  · left
    have hterminalNat : ∃ time : ℕ,
        time < Fintype.card State + 1 ∧ terminal (orbit time) := by
      obtain ⟨time, htime⟩ := hterminal
      exact ⟨time, time.isLt, htime⟩
    let firstTerminal : ℕ := Nat.find hterminalNat
    have hfirstTerminal := Nat.find_spec hterminalNat
    have hfirstTerminal_lt : firstTerminal < Fintype.card State + 1 :=
      hfirstTerminal.1
    let time : Fin (Fintype.card State + 1) :=
      ⟨firstTerminal, hfirstTerminal_lt⟩
    have hnotTerminalBefore : ∀ candidate : ℕ, candidate < firstTerminal →
        ¬terminal (orbit candidate) := by
      intro candidate hcandidate hbad
      have hcandidateBound : candidate < Fintype.card State + 1 :=
        hcandidate.trans hfirstTerminal_lt
      have hminimal := Nat.find_min' hterminalNat
        (show candidate < Fintype.card State + 1 ∧ terminal (orbit candidate) from
          ⟨hcandidateBound, hbad⟩)
      omega
    exact ⟨{
      orbit := orbit
      orbit_zero := horbit_zero
      terminal_time := time
      not_terminal_before := by
        intro candidate hcandidate
        exact hnotTerminalBefore candidate hcandidate
      edge_before := by
        intro candidate hcandidate
        rw [horbit_succ]
        exact hsuccessor _ (hnotTerminalBefore candidate hcandidate)
      terminal_at := hfirstTerminal.2
    }⟩
  · right
    have hno_terminal : ∀ time : Fin (Fintype.card State + 1),
        ¬terminal (orbit time) := by
      simpa only [not_exists] using hterminal
    obtain ⟨minimal⟩ := exists_minimalClosedSegment orbit
    have hoffset_not_terminal : ∀ offset : Fin minimal.segment.period,
        ¬terminal (orbit (minimal.segment.start + offset)) := by
      intro offset hbad
      have hindex : minimal.segment.start + offset ≤
          Fintype.card State := by
        have hoffset := offset.isLt
        have hend := minimal.segment.end_le_card
        omega
      exact hno_terminal ⟨minimal.segment.start + offset, by omega⟩ hbad
    have hoffset_edge : ∀ offset : Fin minimal.segment.period,
        edge (orbit (minimal.segment.start + offset))
          (orbit (minimal.segment.start + offset + 1)) := by
      intro offset
      rw [horbit_succ]
      exact hsuccessor _ (hoffset_not_terminal offset)
    exact ⟨{
      orbit := orbit
      segment := minimal
      orbit_zero := horbit_zero
      offset_not_terminal := hoffset_not_terminal
      offset_edge := hoffset_edge
    }⟩

/-- The finite state space may itself be a predicate subtype. -/
theorem exists_boundedClosedSegment_subtype {Base : Type*} [Fintype Base]
    (predicate : Base → Prop) [DecidablePred predicate]
    (orbit : ℕ → {base : Base // predicate base}) :
    Nonempty (ClosedSegment orbit) :=
  exists_boundedClosedSegment orbit

/-- The finite type of nonempty, nonsingleton finite coalitions. -/
def NonsingletonCoalition (Player : Type*) [DecidableEq Player] :=
  {coalition : Finset Player // 1 < coalition.card}

instance nonsingletonCoalitionFintype {Player : Type*} [Fintype Player]
    [DecidableEq Player] : Fintype (NonsingletonCoalition Player) :=
  by
    classical
    exact Fintype.subtype (Finset.univ.filter fun coalition =>
      1 < coalition.card) (by simp)

/-- A nonsingleton coalition is nonempty. -/
theorem NonsingletonCoalition.nonempty
    {Player : Type*} [DecidableEq Player]
    {coalition : NonsingletonCoalition Player} :
    (coalition.1 : Finset Player).Nonempty := by
  exact Finset.nonempty_of_ne_empty (by
    intro hempty
    have hcard := coalition.property
    simp [hempty] at hcard)

namespace DispatchedOrbit

/-- A stopped nonsingleton-coalition orbit inside at most four effective
players reaches its terminal predicate within three dispatched steps.

This statement is purely combinatorial.  Nonterminal coalitions have size at
least three, each edge changes coalition cardinality by one, and immediate
edge reversal is forbidden.  Thus sizes alternate between three and four.
Among four effective players, four consecutive nonterminal vertices would
force the two size-four vertices at distance two to coincide, producing an
immediate reverse. -/
theorem terminal_time_le_three_of_effectiveSupport_card_le_four
    {Player : Type*} [Fintype Player] [DecidableEq Player]
    {terminal : NonsingletonCoalition Player → Prop}
    {edge : NonsingletonCoalition Player →
      NonsingletonCoalition Player → Prop}
    {start : NonsingletonCoalition Player}
    (trace : DispatchedOrbit terminal edge start)
    (support : Finset Player)
    (hcontained : ∀ time : ℕ, time ≤ trace.terminal_time →
      (trace.orbit time).1 ⊆ support)
    (hcardTwoTerminal : ∀ state : NonsingletonCoalition Player,
      state.1.card = 2 → terminal state)
    (hedgeCard : ∀ {source target}, edge source target →
      target.1.card + 1 = source.1.card ∨
        source.1.card + 1 = target.1.card)
    (hnoReverse : ∀ {source target}, edge source target →
      edge target source → False)
    (hsupport : support.card ≤ 4) :
    trace.terminal_time.val ≤ 3 := by
  by_contra hnot
  have hthree : 3 < trace.terminal_time.val := by omega
  have hbefore : ∀ time : ℕ, time ≤ 3 →
      ¬terminal (trace.orbit time) := by
    intro time htime
    exact trace.not_terminal_before time (by omega)
  have hcardBounds : ∀ time : ℕ, time ≤ 3 →
      3 ≤ (trace.orbit time).1.card ∧
        (trace.orbit time).1.card ≤ 4 := by
    intro time htime
    have hnonsingleton := (trace.orbit time).2
    have hneTwo : (trace.orbit time).1.card ≠ 2 := by
      intro hcard
      exact hbefore time htime (hcardTwoTerminal _ hcard)
    have hsubset := hcontained time (by omega)
    exact ⟨by omega, (Finset.card_le_card hsubset).trans hsupport⟩
  have hedge : ∀ time : ℕ, time ≤ 2 →
      edge (trace.orbit time) (trace.orbit (time + 1)) := by
    intro time htime
    exact trace.edge_before time (by omega)
  have hstep : ∀ time : ℕ, time ≤ 2 →
      ((trace.orbit time).1.card = 3 ∧
          (trace.orbit (time + 1)).1.card = 4) ∨
        ((trace.orbit time).1.card = 4 ∧
          (trace.orbit (time + 1)).1.card = 3) := by
    intro time htime
    have hsource := hcardBounds time (by omega)
    have htarget := hcardBounds (time + 1) (by omega)
    rcases hedgeCard (hedge time htime) with hdrop | hjoin
    · exact Or.inr ⟨by omega, by omega⟩
    · exact Or.inl ⟨by omega, by omega⟩
  by_cases hzero : (trace.orbit 0).1.card = 4
  · have hone : (trace.orbit 1).1.card = 3 :=
      ((hstep 0 (by omega)).resolve_left (fun h => by omega)).2
    have htwo : (trace.orbit 2).1.card = 4 :=
      ((hstep 1 (by omega)).resolve_right (fun h => by omega)).2
    have hzeroSupport : (trace.orbit 0).1 = support := by
      apply Finset.eq_of_subset_of_card_le (hcontained 0 (by omega))
      omega
    have htwoSupport : (trace.orbit 2).1 = support := by
      apply Finset.eq_of_subset_of_card_le (hcontained 2 (by omega))
      omega
    have horbit : trace.orbit 2 = trace.orbit 0 := by
      apply Subtype.ext
      rw [hzeroSupport, htwoSupport]
    have hforward := hedge 0 (by omega)
    have hbackward := hedge 1 (by omega)
    rw [horbit] at hbackward
    exact hnoReverse hforward hbackward
  · have hzeroThree : (trace.orbit 0).1.card = 3 := by
      rcases hcardBounds 0 (by omega) with ⟨hlower, hupper⟩
      omega
    have hone : (trace.orbit 1).1.card = 4 :=
      ((hstep 0 (by omega)).resolve_right (fun h => by omega)).2
    have htwo : (trace.orbit 2).1.card = 3 :=
      ((hstep 1 (by omega)).resolve_left (fun h => by omega)).2
    have hthreeCard : (trace.orbit 3).1.card = 4 :=
      ((hstep 2 (by omega)).resolve_right (fun h => by omega)).2
    have honeSupport : (trace.orbit 1).1 = support := by
      apply Finset.eq_of_subset_of_card_le (hcontained 1 (by omega))
      omega
    have hthreeSupport : (trace.orbit 3).1 = support := by
      apply Finset.eq_of_subset_of_card_le (hcontained 3 (by omega))
      omega
    have horbit : trace.orbit 3 = trace.orbit 1 := by
      apply Subtype.ext
      rw [honeSupport, hthreeSupport]
    have hforward := hedge 1 (by omega)
    have hbackward := hedge 2 (by omega)
    rw [horbit] at hbackward
    exact hnoReverse hforward hbackward

end DispatchedOrbit

private def subtypeEquivOfIff {α : Type*} {p q : α → Prop}
    (h : ∀ value, p value ↔ q value) : {value // p value} ≃ {value // q value} :=
  {
    toFun := fun value => ⟨value.1, (h value.1).mp value.2⟩
    invFun := fun value => ⟨value.1, (h value.1).mpr value.2⟩
    left_inv := by intro value; rfl
    right_inv := by intro value; rfl
  }

/-- There are `2^n - n - 1` nonempty nonsingleton coalitions on `n` players. -/
theorem card_nonsingletonCoalition {Player : Type*} [Fintype Player]
    [DecidableEq Player] :
    Fintype.card (NonsingletonCoalition Player) =
      2 ^ Fintype.card Player - Fintype.card Player - 1 := by
  let zero : Finset Player → Prop := fun coalition => coalition.card = 0
  let one : Finset Player → Prop := fun coalition => coalition.card = 1
  have hdisjoint : Disjoint zero one := by
    refine Set.disjoint_left.2 ?_
    intro coalition hzero hone
    change coalition.card = 0 at hzero
    change coalition.card = 1 at hone
    omega
  have hor := Fintype.card_subtype_or_disjoint zero one hdisjoint
  have hzero : Fintype.card {coalition : Finset Player // zero coalition} = 1 := by
    simp [zero]
  have hone : Fintype.card {coalition : Finset Player // one coalition} =
      Fintype.card Player := by
    simp [one]
  have hor' : Fintype.card {coalition : Finset Player //
      zero coalition ∨ one coalition} = 1 + Fintype.card Player := by
    rw [hor, hzero, hone]
  let small : Finset Player → Prop := fun coalition =>
    coalition.card = 0 ∨ coalition.card = 1
  have hsmall : ∀ coalition, small coalition ↔
      zero coalition ∨ one coalition := by
    intro coalition
    rfl
  have hsmall_card : Fintype.card {coalition : Finset Player // small coalition} =
      1 + Fintype.card Player := by
    exact (Fintype.card_congr (subtypeEquivOfIff hsmall)).trans hor'
  have hcomplement := Fintype.card_subtype_compl small
  have hnot_small : ∀ coalition, ¬small coalition ↔
      1 < coalition.card := by
    intro coalition
    simp only [small, not_or]
    omega
  have hcoalition_card : Fintype.card (NonsingletonCoalition Player) =
      Fintype.card (Finset Player) - (1 + Fintype.card Player) := by
    calc
      Fintype.card (NonsingletonCoalition Player) =
          Fintype.card {coalition : Finset Player // ¬small coalition} :=
        Fintype.card_congr (subtypeEquivOfIff (fun coalition =>
          (hnot_small coalition).symm))
      _ = Fintype.card (Finset Player) -
          Fintype.card {coalition : Finset Player // small coalition} := hcomplement
      _ = Fintype.card (Finset Player) - (1 + Fintype.card Player) := by
        rw [hsmall_card]
  rw [hcoalition_card, Fintype.card_finset]
  omega

end MathUE.FiniteBooleanEndpointOrbit
