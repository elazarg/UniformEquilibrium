/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-!
# Cycles and short lassos in finite serial relations

Every serial relation on a nonempty finite type contains a positive-period
periodic cycle.  This general cycle extractor records the periodic orbit
directly and does not assume decidable equality or a chosen finite enumeration.

An irreflexive relation with one outgoing edge from a root and an outgoing
edge after every reached edge generates a rooted directed lasso.  On at most
four points, it has a simple lasso witness of one of six shapes: a rooted cycle of
length two, three, or four; one tail edge into a cycle of length two or three;
or two tail edges into a cycle of length two.

The theorem is purely relational.  Game-semantic applications supply the
relation and the seriality proof.
-/

namespace Math.FiniteSerialRelation

universe u

section PeriodicCycle

variable {State : Type u} (R : State → State → Prop)

/-- A positive-period periodic orbit in a binary relation. -/
structure PeriodicCycle where
  /-- Period of the selected orbit. -/
  period : ℕ
  /-- The period is nonzero. -/
  period_pos : 0 < period
  /-- Vertices of the periodic orbit. -/
  vertex : ℕ → State
  /-- Advancing by one period returns to the same vertex. -/
  vertex_periodic : ∀ time, vertex (time + period) = vertex time
  /-- Every consecutive pair is an edge of the relation. -/
  edge : ∀ time, R (vertex time) (vertex (time + 1))

namespace PeriodicCycle

variable {R}

/-- Map a periodic relational cycle through a relation-preserving function. -/
def map {Target : Type*} {S : Target → Target → Prop}
    (cycle : PeriodicCycle R) (f : State → Target)
    (hedge : ∀ {source target}, R source target → S (f source) (f target)) :
    PeriodicCycle S where
  period := cycle.period
  period_pos := cycle.period_pos
  vertex := fun time ↦ f (cycle.vertex time)
  vertex_periodic := fun time ↦ congrArg f (cycle.vertex_periodic time)
  edge := fun time ↦ hedge (cycle.edge time)

/-- An irreflexive relation has no period-one relational cycle. -/
theorem two_le_period_of_irreflexive
    (cycle : PeriodicCycle R) (hirreflexive : ∀ state, ¬R state state) :
    2 ≤ cycle.period := by
  by_contra hperiod
  have hpositive := cycle.period_pos
  have hone : cycle.period = 1 := by omega
  have hperiodic := cycle.vertex_periodic 0
  rw [hone] at hperiodic
  simp only [zero_add] at hperiodic
  have hedge := cycle.edge 0
  rw [hperiodic] at hedge
  exact hirreflexive (cycle.vertex 0) hedge

end PeriodicCycle

/-- Every serial relation on a nonempty finite type contains a periodic cycle.

The proof follows one chosen successor forever and closes the finite orbit at
the first supplied repetition.  No irreflexivity assumption is needed, so a
self-loop may produce period one. -/
theorem nonempty_periodicCycle_of_serial
    [Finite State] [Nonempty State]
    (hserial : ∀ state, ∃ next, R state next) :
    Nonempty (PeriodicCycle R) := by
  let successor : State → State := fun state ↦ Classical.choose (hserial state)
  have hsuccessor : ∀ state, R state (successor state) := fun state ↦
    Classical.choose_spec (hserial state)
  let seed : State := Classical.choice inferInstance
  let orbit : ℕ → State := fun time ↦ (successor^[time]) seed
  obtain ⟨left, right, hne, heq⟩ :=
    Finite.exists_ne_map_eq_of_infinite orbit
  have build : ∀ {start stop : ℕ}, start < stop → orbit start = orbit stop →
      Nonempty (PeriodicCycle R) := by
    intro start stop hlt hrepeat
    let period := stop - start
    have hperiodPos : 0 < period := by
      dsimp only [period]
      omega
    have hstartPeriod : start + period = stop := by
      dsimp only [period]
      omega
    let vertex : ℕ → State := fun time ↦ orbit (start + time)
    have hedge : ∀ time, R (vertex time) (vertex (time + 1)) := by
      intro time
      have hstep := hsuccessor (orbit (start + time))
      have horbitSucc : successor (orbit (start + time)) =
          orbit (start + (time + 1)) := by
        dsimp only [orbit]
        rw [show start + (time + 1) = (start + time).succ by omega,
          Function.iterate_succ_apply']
      change R (orbit (start + time)) (orbit (start + (time + 1)))
      rw [← horbitSucc]
      exact hstep
    have hreturn : (successor^[period]) (orbit start) = orbit start := by
      change (successor^[period]) ((successor^[start]) seed) =
        (successor^[start]) seed
      rw [← Function.iterate_add_apply]
      rw [Nat.add_comm, hstartPeriod]
      exact hrepeat.symm
    have hperiodic : ∀ time, vertex (time + period) = vertex time := by
      intro time
      change orbit (start + (time + period)) = orbit (start + time)
      change (successor^[start + (time + period)]) seed =
        (successor^[start + time]) seed
      rw [show start + (time + period) = time + period + start by omega,
        Function.iterate_add_apply]
      rw [show start + time = time + start by omega,
        Function.iterate_add_apply]
      rw [Function.iterate_add_apply, hreturn]
    exact ⟨{
      period := period
      period_pos := hperiodPos
      vertex := vertex
      vertex_periodic := hperiodic
      edge := hedge
    }⟩
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact build hlt heq
  · exact build hgt heq.symm

end PeriodicCycle

variable {State : Type} [Fintype State] [DecidableEq State]
variable (R : State → State → Prop) (root : State)

/-- A directed two-cycle containing the distinguished root. -/
structure RootedTwoCycle where
  next : State
  next_ne_root : next ≠ root
  forward : R root next
  backward : R next root

/-- A directed three-cycle containing the distinguished root. -/
structure RootedThreeCycle where
  first : State
  second : State
  first_ne_root : first ≠ root
  second_ne_root : second ≠ root
  second_ne_first : second ≠ first
  first_edge : R root first
  second_edge : R first second
  closing_edge : R second root

/-- A directed four-cycle containing the distinguished root. -/
structure RootedFourCycle where
  first : State
  second : State
  third : State
  first_ne_root : first ≠ root
  second_ne_root : second ≠ root
  second_ne_first : second ≠ first
  third_ne_root : third ≠ root
  third_ne_first : third ≠ first
  third_ne_second : third ≠ second
  first_edge : R root first
  second_edge : R first second
  third_edge : R second third
  closing_edge : R third root

/-- One tail edge from the root into a directed two-cycle. -/
structure OneStepToTwoCycle where
  entry : State
  other : State
  entry_ne_root : entry ≠ root
  other_ne_root : other ≠ root
  other_ne_entry : other ≠ entry
  tail_edge : R root entry
  cycle_forward : R entry other
  cycle_backward : R other entry

/-- One tail edge from the root into a directed three-cycle. -/
structure OneStepToThreeCycle where
  entry : State
  second : State
  third : State
  entry_ne_root : entry ≠ root
  second_ne_root : second ≠ root
  second_ne_entry : second ≠ entry
  third_ne_root : third ≠ root
  third_ne_entry : third ≠ entry
  third_ne_second : third ≠ second
  tail_edge : R root entry
  first_cycle_edge : R entry second
  second_cycle_edge : R second third
  closing_edge : R third entry

/-- Two tail edges from the root into a directed two-cycle. -/
structure TwoStepsToTwoCycle where
  first : State
  entry : State
  other : State
  first_ne_root : first ≠ root
  entry_ne_root : entry ≠ root
  entry_ne_first : entry ≠ first
  other_ne_root : other ≠ root
  other_ne_first : other ≠ first
  other_ne_entry : other ≠ entry
  first_tail_edge : R root first
  second_tail_edge : R first entry
  cycle_forward : R entry other
  cycle_backward : R other entry

/-- The six simple rooted lasso shapes available on at most four points. -/
def HasRootedLasso : Prop :=
  Nonempty (RootedTwoCycle R root) ∨
  Nonempty (RootedThreeCycle R root) ∨
  Nonempty (RootedFourCycle R root) ∨
  Nonempty (OneStepToTwoCycle R root) ∨
  Nonempty (OneStepToThreeCycle R root) ∨
  Nonempty (TwoStepsToTwoCycle R root)

/-- The position of a distinguished non-root marker relative to a simple
rooted lasso.  The constructors are the seventeen positions available on at
most four points: two over a rooted two-cycle, three over each of the other
five lasso shapes.  A four-vertex lasso has no outside position. -/
inductive MarkedRootedLasso (marker : State) where
  | rootedTwo_next (geometry : RootedTwoCycle R root)
      (marker_eq : marker = geometry.next)
  | rootedTwo_outside (geometry : RootedTwoCycle R root)
      (marker_outside : marker ∉ ({root, geometry.next} : Finset State))
  | rootedThree_first (geometry : RootedThreeCycle R root)
      (marker_eq : marker = geometry.first)
  | rootedThree_second (geometry : RootedThreeCycle R root)
      (marker_eq : marker = geometry.second)
  | rootedThree_outside (geometry : RootedThreeCycle R root)
      (marker_outside : marker ∉
        ({root, geometry.first, geometry.second} : Finset State))
  | rootedFour_first (geometry : RootedFourCycle R root)
      (marker_eq : marker = geometry.first)
  | rootedFour_second (geometry : RootedFourCycle R root)
      (marker_eq : marker = geometry.second)
  | rootedFour_third (geometry : RootedFourCycle R root)
      (marker_eq : marker = geometry.third)
  | oneToTwo_entry (geometry : OneStepToTwoCycle R root)
      (marker_eq : marker = geometry.entry)
  | oneToTwo_other (geometry : OneStepToTwoCycle R root)
      (marker_eq : marker = geometry.other)
  | oneToTwo_outside (geometry : OneStepToTwoCycle R root)
      (marker_outside : marker ∉
        ({root, geometry.entry, geometry.other} : Finset State))
  | oneToThree_entry (geometry : OneStepToThreeCycle R root)
      (marker_eq : marker = geometry.entry)
  | oneToThree_second (geometry : OneStepToThreeCycle R root)
      (marker_eq : marker = geometry.second)
  | oneToThree_third (geometry : OneStepToThreeCycle R root)
      (marker_eq : marker = geometry.third)
  | twoToTwo_first (geometry : TwoStepsToTwoCycle R root)
      (marker_eq : marker = geometry.first)
  | twoToTwo_entry (geometry : TwoStepsToTwoCycle R root)
      (marker_eq : marker = geometry.entry)
  | twoToTwo_other (geometry : TwoStepsToTwoCycle R root)
      (marker_eq : marker = geometry.other)

omit [Fintype State] in
/-- Forgetting the marker reduces the seventeen marked positions to the six
rooted lasso shapes. -/
theorem MarkedRootedLasso.hasRootedLasso
    {marker : State} (geometry : MarkedRootedLasso R root marker) :
    HasRootedLasso R root := by
  cases geometry with
  | rootedTwo_next geometry _ => exact Or.inl ⟨geometry⟩
  | rootedTwo_outside geometry _ => exact Or.inl ⟨geometry⟩
  | rootedThree_first geometry _ => exact Or.inr (Or.inl ⟨geometry⟩)
  | rootedThree_second geometry _ => exact Or.inr (Or.inl ⟨geometry⟩)
  | rootedThree_outside geometry _ => exact Or.inr (Or.inl ⟨geometry⟩)
  | rootedFour_first geometry _ =>
      exact Or.inr (Or.inr (Or.inl ⟨geometry⟩))
  | rootedFour_second geometry _ =>
      exact Or.inr (Or.inr (Or.inl ⟨geometry⟩))
  | rootedFour_third geometry _ =>
      exact Or.inr (Or.inr (Or.inl ⟨geometry⟩))
  | oneToTwo_entry geometry _ =>
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨geometry⟩)))
  | oneToTwo_other geometry _ =>
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨geometry⟩)))
  | oneToTwo_outside geometry _ =>
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨geometry⟩)))
  | oneToThree_entry geometry _ =>
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨geometry⟩))))
  | oneToThree_second geometry _ =>
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨geometry⟩))))
  | oneToThree_third geometry _ =>
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨geometry⟩))))
  | twoToTwo_first geometry _ =>
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨geometry⟩))))
  | twoToTwo_entry geometry _ =>
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨geometry⟩))))
  | twoToTwo_other geometry _ =>
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨geometry⟩))))

omit [DecidableEq State] in
/-- Five elements of a type of cardinality at most four cannot be pairwise
distinct. -/
theorem five_not_pairwise_distinct
    (hcard : Fintype.card State ≤ 4)
    {q a b c d : State}
    (haq : a ≠ q) (hbq : b ≠ q) (hba : b ≠ a)
    (hcq : c ≠ q) (hca : c ≠ a) (hcb : c ≠ b)
    (hdq : d ≠ q) (hda : d ≠ a) (hdb : d ≠ b) (hdc : d ≠ c) :
    False := by
  let vertices : Fin 5 → State := ![q, a, b, c, d]
  have hinjective : Function.Injective vertices := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [vertices]
  have hle : 5 ≤ Fintype.card State :=
    Fintype.card_le_of_injective vertices hinjective
  omega

/-- **Four-point serial-relation classification.**  Every irreflexive serial
walk rooted in a type of cardinality at most four has one of the six simple
lasso shapes in `HasRootedLasso`. -/
theorem hasRootedLasso_of_card_le_four
    (hcard : Fintype.card State ≤ 4)
    (hirreflexive : ∀ state, ¬ R state state)
    (hroot : ∃ next, R root next)
    (hserial : ∀ {previous current}, R previous current → ∃ next, R current next) :
    HasRootedLasso R root := by
  obtain ⟨a, hqa⟩ := hroot
  obtain ⟨b, hab⟩ := hserial hqa
  obtain ⟨c, hbc⟩ := hserial hab
  obtain ⟨d, hcd⟩ := hserial hbc
  have haq : a ≠ root := by
    intro h
    subst a
    exact hirreflexive root hqa
  have hba : b ≠ a := by
    intro h
    subst b
    exact hirreflexive a hab
  have hcb : c ≠ b := by
    intro h
    subst c
    exact hirreflexive b hbc
  have hdc : d ≠ c := by
    intro h
    subst d
    exact hirreflexive c hcd
  by_cases hbq : b = root
  · exact Or.inl ⟨{
      next := a
      next_ne_root := haq
      forward := hqa
      backward := by simpa [hbq] using hab
    }⟩
  have hbq' : b ≠ root := hbq
  by_cases hcq : c = root
  · exact Or.inr (Or.inl ⟨{
      first := a
      second := b
      first_ne_root := haq
      second_ne_root := hbq'
      second_ne_first := hba
      first_edge := hqa
      second_edge := hab
      closing_edge := by simpa [hcq] using hbc
    }⟩)
  have hcq' : c ≠ root := hcq
  by_cases hca : c = a
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨{
      entry := a
      other := b
      entry_ne_root := haq
      other_ne_root := hbq'
      other_ne_entry := hba
      tail_edge := hqa
      cycle_forward := hab
      cycle_backward := by simpa [hca] using hbc
    }⟩)))
  have hca' : c ≠ a := hca
  have hd_cases : d = root ∨ d = a ∨ d = b := by
    by_contra hnot
    push Not at hnot
    exact five_not_pairwise_distinct hcard haq hbq' hba hcq' hca' hcb
      hnot.1 hnot.2.1 hnot.2.2 hdc
  rcases hd_cases with hdq | hda | hdb
  · exact Or.inr (Or.inr (Or.inl ⟨{
      first := a
      second := b
      third := c
      first_ne_root := haq
      second_ne_root := hbq'
      second_ne_first := hba
      third_ne_root := hcq'
      third_ne_first := hca'
      third_ne_second := hcb
      first_edge := hqa
      second_edge := hab
      third_edge := hbc
      closing_edge := by simpa [hdq] using hcd
    }⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨{
      entry := a
      second := b
      third := c
      entry_ne_root := haq
      second_ne_root := hbq'
      second_ne_entry := hba
      third_ne_root := hcq'
      third_ne_entry := hca'
      third_ne_second := hcb
      tail_edge := hqa
      first_cycle_edge := hab
      second_cycle_edge := hbc
      closing_edge := by simpa [hda] using hcd
    }⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨{
      first := a
      entry := b
      other := c
      first_ne_root := haq
      entry_ne_root := hbq'
      entry_ne_first := hba
      other_ne_root := hcq'
      other_ne_first := hca'
      other_ne_entry := hcb
      first_tail_edge := hqa
      second_tail_edge := hab
      cycle_forward := hbc
      cycle_backward := by simpa [hdb] using hcd
    }⟩))))

/-- **Marked four-point classification.**  A distinguished point other than
the root occupies one of the seventeen canonical positions relative to a
selected rooted lasso witness. -/
theorem markedRootedLasso_of_card_le_four
    (hcard : Fintype.card State ≤ 4)
    (hirreflexive : ∀ state, ¬ R state state)
    (hroot : ∃ next, R root next)
    (hserial : ∀ {previous current}, R previous current → ∃ next, R current next)
    {marker : State} (hmarker : marker ≠ root) :
    Nonempty (MarkedRootedLasso R root marker) := by
  rcases hasRootedLasso_of_card_le_four R root hcard hirreflexive hroot hserial with
    geometry | geometry | geometry | geometry | geometry | geometry
  · obtain ⟨geometry⟩ := geometry
    by_cases hnext : marker = geometry.next
    · exact ⟨MarkedRootedLasso.rootedTwo_next geometry hnext⟩
    · exact ⟨MarkedRootedLasso.rootedTwo_outside geometry (by
        simp [hmarker, hnext])⟩
  · obtain ⟨geometry⟩ := geometry
    by_cases hfirst : marker = geometry.first
    · exact ⟨MarkedRootedLasso.rootedThree_first geometry hfirst⟩
    · by_cases hsecond : marker = geometry.second
      · exact ⟨MarkedRootedLasso.rootedThree_second geometry hsecond⟩
      · exact ⟨MarkedRootedLasso.rootedThree_outside geometry (by
          simp [hmarker, hfirst, hsecond])⟩
  · obtain ⟨geometry⟩ := geometry
    by_cases hfirst : marker = geometry.first
    · exact ⟨MarkedRootedLasso.rootedFour_first geometry hfirst⟩
    · by_cases hsecond : marker = geometry.second
      · exact ⟨MarkedRootedLasso.rootedFour_second geometry hsecond⟩
      · by_cases hthird : marker = geometry.third
        · exact ⟨MarkedRootedLasso.rootedFour_third geometry hthird⟩
        · exact (five_not_pairwise_distinct hcard
            geometry.first_ne_root geometry.second_ne_root
            geometry.second_ne_first geometry.third_ne_root
            geometry.third_ne_first geometry.third_ne_second hmarker
            hfirst hsecond hthird).elim
  · obtain ⟨geometry⟩ := geometry
    by_cases hentry : marker = geometry.entry
    · exact ⟨MarkedRootedLasso.oneToTwo_entry geometry hentry⟩
    · by_cases hother : marker = geometry.other
      · exact ⟨MarkedRootedLasso.oneToTwo_other geometry hother⟩
      · exact ⟨MarkedRootedLasso.oneToTwo_outside geometry (by
          simp [hmarker, hentry, hother])⟩
  · obtain ⟨geometry⟩ := geometry
    by_cases hentry : marker = geometry.entry
    · exact ⟨MarkedRootedLasso.oneToThree_entry geometry hentry⟩
    · by_cases hsecond : marker = geometry.second
      · exact ⟨MarkedRootedLasso.oneToThree_second geometry hsecond⟩
      · by_cases hthird : marker = geometry.third
        · exact ⟨MarkedRootedLasso.oneToThree_third geometry hthird⟩
        · exact (five_not_pairwise_distinct hcard
            geometry.entry_ne_root geometry.second_ne_root
            geometry.second_ne_entry geometry.third_ne_root
            geometry.third_ne_entry geometry.third_ne_second hmarker
            hentry hsecond hthird).elim
  · obtain ⟨geometry⟩ := geometry
    by_cases hfirst : marker = geometry.first
    · exact ⟨MarkedRootedLasso.twoToTwo_first geometry hfirst⟩
    · by_cases hentry : marker = geometry.entry
      · exact ⟨MarkedRootedLasso.twoToTwo_entry geometry hentry⟩
      · by_cases hother : marker = geometry.other
        · exact ⟨MarkedRootedLasso.twoToTwo_other geometry hother⟩
        · exact (five_not_pairwise_distinct hcard
            geometry.first_ne_root geometry.entry_ne_root
            geometry.entry_ne_first geometry.other_ne_root
            geometry.other_ne_first geometry.other_ne_entry hmarker
            hfirst hentry hother).elim

end Math.FiniteSerialRelation
