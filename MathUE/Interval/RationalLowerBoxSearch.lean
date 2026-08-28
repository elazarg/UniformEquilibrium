/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors.
-/

import MathUE.Interval.RationalLowerBoxTree
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.List.FinRange
import Mathlib.Topology.Sequences

/-!
# Fair exact search for rational lower-box certificates

This module separates an executable search from the semantic checker in
`RationalLowerBoxTree`.  At every node it first tries every exact leaf reason.
If none succeeds, it follows a fixed schedule of midpoint splits.  One round of
the schedule visits every coordinate, so increasing the number of rounds is a
fair refinement even when coordinate intervals have different scales.

The search never consults a real minimum or a classical choice.  Compactness is
used only in the completeness proof that some finite round succeeds under a
strict pointwise separation hypothesis.
-/

namespace Math
namespace Interval

namespace RationalLowerBoxProblem

variable {variableCount equalityCount inequalityCount : ℕ}

/-- The first exact leaf reason accepted by the rational checker. -/
def firstVerifiedLeaf
    (problem : RationalLowerBoxProblem variableCount equalityCount
      inequalityCount)
    (gamma : ℚ) (box : RationalBox variableCount) :
    Option (RationalLowerLeafReason equalityCount inequalityCount) :=
  match Fin.find? fun index ↦
      problem.verifyLeaf gamma box (.equalitySeparated index) with
  | some index => some (.equalitySeparated index)
  | none =>
      match Fin.find? fun index ↦
          problem.verifyLeaf gamma box (.nonnegativeSeparated index) with
      | some index => some (.nonnegativeSeparated index)
      | none =>
          if problem.verifyLeaf gamma box .objectiveLowerBound then
            some .objectiveLowerBound
          else
            none

/-- A leaf returned by `firstVerifiedLeaf` is accepted by the base checker. -/
theorem verifyLeaf_firstVerifiedLeaf
    (problem : RationalLowerBoxProblem variableCount equalityCount
      inequalityCount)
    (gamma : ℚ) (box : RationalBox variableCount)
    {reason : RationalLowerLeafReason equalityCount inequalityCount}
    (hreason : problem.firstVerifiedLeaf gamma box = some reason) :
    problem.verifyLeaf gamma box reason = true := by
  unfold firstVerifiedLeaf at hreason
  split at hreason
  next index hindex =>
    injection hreason with hreason
    subst reason
    exact Fin.eq_true_of_find?_eq_some hindex
  next hequality =>
    split at hreason
    next index hindex =>
      injection hreason with hreason
      subst reason
      exact Fin.eq_true_of_find?_eq_some hindex
    next hnonnegative =>
      split at hreason
      next hobjective =>
        injection hreason with hreason
        subst reason
        exact hobjective
      next hobjective => simp at hreason

/-- If any exact leaf reason succeeds, the deterministic selector finds one. -/
theorem isSome_firstVerifiedLeaf_of_verifyLeaf
    (problem : RationalLowerBoxProblem variableCount equalityCount
      inequalityCount)
    (gamma : ℚ) (box : RationalBox variableCount)
    (reason : RationalLowerLeafReason equalityCount inequalityCount)
    (hreason : problem.verifyLeaf gamma box reason = true) :
    (problem.firstVerifiedLeaf gamma box).isSome := by
  cases reason with
  | equalitySeparated index =>
      cases hequality : Fin.find? fun candidate ↦
          problem.verifyLeaf gamma box (.equalitySeparated candidate) with
      | none =>
          have hfalse := Fin.eq_false_of_find?_eq_none hequality index
          simp [hreason] at hfalse
      | some found => simp [firstVerifiedLeaf, hequality]
  | nonnegativeSeparated index =>
      cases hequality : Fin.find? fun candidate ↦
          problem.verifyLeaf gamma box (.equalitySeparated candidate) with
      | some found => simp [firstVerifiedLeaf, hequality]
      | none =>
          cases hnonnegative : Fin.find? fun candidate ↦
              problem.verifyLeaf gamma box (.nonnegativeSeparated candidate) with
          | none =>
              have hfalse := Fin.eq_false_of_find?_eq_none hnonnegative index
              simp [hreason] at hfalse
          | some found => simp [firstVerifiedLeaf, hequality, hnonnegative]
  | objectiveLowerBound =>
      cases hequality : Fin.find? fun candidate ↦
          problem.verifyLeaf gamma box (.equalitySeparated candidate) with
      | some found => simp [firstVerifiedLeaf, hequality]
      | none =>
          cases hnonnegative : Fin.find? fun candidate ↦
              problem.verifyLeaf gamma box (.nonnegativeSeparated candidate) with
          | some found => simp [firstVerifiedLeaf, hequality, hnonnegative]
          | none => simp [firstVerifiedLeaf, hequality, hnonnegative, hreason]

/-- Midpoint of one rational coordinate interval. -/
def midpoint (interval : RationalInterval) : ℚ :=
  (interval.lower + interval.upper) / 2

/-- The canonical full coordinate sweep. -/
def coordinateSweep (variableCount : ℕ) : List (Fin variableCount) :=
  List.ofFn id

/-- Repeat the full coordinate sweep a prescribed number of times. -/
def uniformDyadicSchedule (variableCount rounds : ℕ) :
    List (Fin variableCount) :=
  (List.replicate rounds (coordinateSweep variableCount)).flatten

@[simp] theorem count_coordinateSweep (coordinate : Fin variableCount) :
    (coordinateSweep variableCount).count coordinate = 1 := by
  apply List.count_eq_one_of_mem
  · exact List.nodup_ofFn_ofInjective Function.injective_id
  · simp [coordinateSweep, List.mem_ofFn']

@[simp] theorem count_uniformDyadicSchedule (rounds : ℕ)
    (coordinate : Fin variableCount) :
    (uniformDyadicSchedule variableCount rounds).count coordinate = rounds := by
  induction rounds with
  | zero => simp [uniformDyadicSchedule]
  | succ rounds hinduction =>
      have hinduction' :
          List.count coordinate
              (List.replicate rounds (coordinateSweep variableCount)).flatten =
            rounds := by
        simpa [uniformDyadicSchedule] using hinduction
      simp [uniformDyadicSchedule, List.replicate_succ, hinduction',
        Nat.add_comm]

/-- All terminal boxes produced by one finite schedule, without early leaf
classification.  This mathematical view is used only to audit fairness and
termination of the executable search. -/
def terminalBoxes : List (Fin variableCount) → RationalBox variableCount →
    List (RationalBox variableCount)
  | [], box => [box]
  | coordinate :: remaining, box =>
      if (box coordinate).lower < (box coordinate).upper then
        terminalBoxes remaining
            (box.left coordinate (midpoint (box coordinate))) ++
          terminalBoxes remaining
            (box.right coordinate (midpoint (box coordinate)))
      else
        terminalBoxes remaining box

/-- Coordinatewise validity of a rational box. -/
def RationalBox.Valid (box : RationalBox variableCount) : Prop :=
  ∀ coordinate, (box coordinate).Valid

/-- Exact rational width of one coordinate. -/
def RationalBox.width (box : RationalBox variableCount)
    (coordinate : Fin variableCount) : ℚ :=
  (box coordinate).upper - (box coordinate).lower

/-- The midpoint of every coordinate, regarded as a real point. -/
def RationalBox.center (box : RationalBox variableCount) :
    Fin variableCount → ℝ :=
  fun coordinate ↦ (midpoint (box coordinate) : ℝ)

/-- A valid box contains its coordinatewise midpoint. -/
theorem RationalBox.contains_center (box : RationalBox variableCount)
    (hbox : RationalBox.Valid box) :
    RationalBox.Contains box (RationalBox.center box) := by
  intro coordinate
  change ((box coordinate).lower : ℝ) ≤
      ((midpoint (box coordinate) : ℚ) : ℝ) ∧
    ((midpoint (box coordinate) : ℚ) : ℝ) ≤
      ((box coordinate).upper : ℝ)
  dsimp only [midpoint]
  constructor <;> exact_mod_cast (by
    have := hbox coordinate
    dsimp only [RationalInterval.Valid] at this
    linarith)

/-- Coordinatewise inclusion of rational boxes. -/
def RationalBox.Subbox (inner outer : RationalBox variableCount) : Prop :=
  ∀ coordinate,
    (outer coordinate).lower ≤ (inner coordinate).lower ∧
      (inner coordinate).upper ≤ (outer coordinate).upper

theorem RationalBox.subbox_refl (box : RationalBox variableCount) :
    RationalBox.Subbox box box := by
  intro coordinate
  exact ⟨le_rfl, le_rfl⟩

theorem RationalBox.Subbox.trans
    {first second third : RationalBox variableCount}
    (hfirst : RationalBox.Subbox first second)
    (hsecond : RationalBox.Subbox second third) :
    RationalBox.Subbox first third := by
  intro coordinate
  exact ⟨(hsecond coordinate).1.trans (hfirst coordinate).1,
    (hfirst coordinate).2.trans (hsecond coordinate).2⟩

theorem RationalBox.valid_left (box : RationalBox variableCount)
    (hbox : RationalBox.Valid box) (coordinate : Fin variableCount)
    (hwidth : (box coordinate).lower < (box coordinate).upper) :
    RationalBox.Valid (box.left coordinate (midpoint (box coordinate))) := by
  intro index
  by_cases hindex : index = coordinate
  · subst index
    rw [RationalBox.left, RationalBox.update, Function.update_self]
    simp only [RationalInterval.Valid, midpoint]
    linarith
  · simpa [RationalBox.left, RationalBox.update, hindex] using hbox index

theorem RationalBox.valid_right (box : RationalBox variableCount)
    (hbox : RationalBox.Valid box) (coordinate : Fin variableCount)
    (hwidth : (box coordinate).lower < (box coordinate).upper) :
    RationalBox.Valid (box.right coordinate (midpoint (box coordinate))) := by
  intro index
  by_cases hindex : index = coordinate
  · subst index
    rw [RationalBox.right, RationalBox.update, Function.update_self]
    simp only [RationalInterval.Valid, midpoint]
    linarith
  · simpa [RationalBox.right, RationalBox.update, hindex] using hbox index

theorem RationalBox.left_subbox (box : RationalBox variableCount)
    (coordinate : Fin variableCount)
    (hwidth : (box coordinate).lower < (box coordinate).upper) :
    RationalBox.Subbox
      (box.left coordinate (midpoint (box coordinate))) box := by
  intro index
  by_cases hindex : index = coordinate
  · subst index
    rw [RationalBox.left, RationalBox.update, Function.update_self]
    simp only [midpoint]
    constructor <;> linarith
  · simp [RationalBox.left, RationalBox.update, hindex]

theorem RationalBox.right_subbox (box : RationalBox variableCount)
    (coordinate : Fin variableCount)
    (hwidth : (box coordinate).lower < (box coordinate).upper) :
    RationalBox.Subbox
      (box.right coordinate (midpoint (box coordinate))) box := by
  intro index
  by_cases hindex : index = coordinate
  · subst index
    rw [RationalBox.right, RationalBox.update, Function.update_self]
    simp only [midpoint]
    constructor <;> linarith
  · simp [RationalBox.right, RationalBox.update, hindex]

/-- Every fully refined terminal box remains valid and lies in its input box. -/
theorem terminalBoxes_valid_subbox
    (schedule : List (Fin variableCount))
    (box terminal : RationalBox variableCount)
    (hbox : RationalBox.Valid box)
    (hterminal : terminal ∈ terminalBoxes schedule box) :
    RationalBox.Valid terminal ∧ RationalBox.Subbox terminal box := by
  induction schedule generalizing box with
  | nil =>
      simp only [terminalBoxes, List.mem_singleton] at hterminal
      subst terminal
      exact ⟨hbox, RationalBox.subbox_refl box⟩
  | cons coordinate remaining hinduction =>
      simp only [terminalBoxes] at hterminal
      split at hterminal
      next hwidth =>
        rw [List.mem_append] at hterminal
        rcases hterminal with hleft | hright
        · obtain ⟨hvalid, hsubbox⟩ := hinduction _
            (RationalBox.valid_left box hbox coordinate hwidth) hleft
          exact ⟨hvalid,
            hsubbox.trans (RationalBox.left_subbox box coordinate hwidth)⟩
        · obtain ⟨hvalid, hsubbox⟩ := hinduction _
            (RationalBox.valid_right box hbox coordinate hwidth) hright
          exact ⟨hvalid,
            hsubbox.trans (RationalBox.right_subbox box coordinate hwidth)⟩
      next hwidth => exact hinduction box hbox hterminal

/-- The midpoint of a terminal box is still a point of the input box. -/
theorem terminalBox_contains_center
    (schedule : List (Fin variableCount))
    (box terminal : RationalBox variableCount)
    (hbox : RationalBox.Valid box)
    (hterminal : terminal ∈ terminalBoxes schedule box) :
    box.Contains (RationalBox.center terminal) := by
  obtain ⟨hvalid, hsubbox⟩ :=
    terminalBoxes_valid_subbox schedule box terminal hbox hterminal
  have hcenter := RationalBox.contains_center terminal hvalid
  intro coordinate
  constructor
  · have hlower : ((box coordinate).lower : ℝ) ≤
        ((terminal coordinate).lower : ℝ) := by
      exact_mod_cast (hsubbox coordinate).1
    exact hlower.trans (hcenter coordinate).1
  · have hupper : ((terminal coordinate).upper : ℝ) ≤
        ((box coordinate).upper : ℝ) := by
      exact_mod_cast (hsubbox coordinate).2
    exact (hcenter coordinate).2.trans hupper

/-- Every scheduled visit halves the selected coordinate width.  A degenerate
coordinate stays at width zero, so the same exact formula covers skipped
splits. -/
theorem terminalBox_width_eq
    (schedule : List (Fin variableCount))
    (box terminal : RationalBox variableCount)
    (hbox : RationalBox.Valid box)
    (hterminal : terminal ∈ terminalBoxes schedule box)
    (coordinate : Fin variableCount) :
    RationalBox.width terminal coordinate =
      RationalBox.width box coordinate /
        (2 : ℚ) ^ schedule.count coordinate := by
  induction schedule generalizing box with
  | nil =>
      simp only [terminalBoxes, List.mem_singleton] at hterminal
      subst terminal
      simp
  | cons selected remaining hinduction =>
      simp only [terminalBoxes] at hterminal
      split at hterminal
      next hwidth =>
        rw [List.mem_append] at hterminal
        rcases hterminal with hleft | hright
        · rw [hinduction _
            (RationalBox.valid_left box hbox selected hwidth) hleft]
          by_cases heq : selected = coordinate
          · subst selected
            simp only [List.count_cons, beq_self_eq_true, ↓reduceIte]
            simp only [RationalBox.width, RationalBox.left,
              RationalBox.update, Function.update_self, midpoint]
            ring
          · have hne : coordinate ≠ selected := Ne.symm heq
            simp only [List.count_cons, beq_iff_eq, heq, ↓reduceIte]
            simp [RationalBox.width, RationalBox.left, RationalBox.update,
              hne]
        · rw [hinduction _
            (RationalBox.valid_right box hbox selected hwidth) hright]
          by_cases heq : selected = coordinate
          · subst selected
            simp only [List.count_cons, beq_self_eq_true, ↓reduceIte]
            simp only [RationalBox.width, RationalBox.right,
              RationalBox.update, Function.update_self, midpoint]
            ring
          · have hne : coordinate ≠ selected := Ne.symm heq
            simp only [List.count_cons, beq_iff_eq, heq, ↓reduceIte]
            simp [RationalBox.width, RationalBox.right, RationalBox.update,
              hne]
      next hwidth =>
        rw [hinduction box hbox hterminal]
        by_cases heq : selected = coordinate
        · subst selected
          have hzero : RationalBox.width box coordinate = 0 := by
            have hvalid := hbox coordinate
            unfold RationalInterval.Valid at hvalid
            unfold RationalBox.width
            linarith
          simp [hzero]
        · simp [heq]

/-- After `rounds` full sweeps, every coordinate has been bisected exactly
`rounds` times. -/
theorem uniformTerminalBox_width_eq
    (rounds : ℕ) (box terminal : RationalBox variableCount)
    (hbox : RationalBox.Valid box)
    (hterminal : terminal ∈
      terminalBoxes (uniformDyadicSchedule variableCount rounds) box)
    (coordinate : Fin variableCount) :
    RationalBox.width terminal coordinate =
      RationalBox.width box coordinate / (2 : ℚ) ^ rounds := by
  simpa using terminalBox_width_eq
    (uniformDyadicSchedule variableCount rounds) box terminal hbox hterminal
      coordinate

/-- Execute one finite split schedule below an arbitrary current box.

Degenerate coordinates are skipped.  A nondegenerate coordinate is bisected
at its exact rational midpoint, and both children must close using the rest of
the same schedule. -/
def searchAlong
    (problem : RationalLowerBoxProblem variableCount equalityCount
      inequalityCount)
    (gamma : ℚ) : List (Fin variableCount) → RationalBox variableCount →
      Option (RationalLowerBoxTree variableCount equalityCount inequalityCount)
  | schedule, box =>
      match problem.firstVerifiedLeaf gamma box with
      | some reason => some (.leaf reason)
      | none =>
          match schedule with
          | [] => none
          | coordinate :: remaining =>
              if (box coordinate).lower < (box coordinate).upper then
                let cut := midpoint (box coordinate)
                match problem.searchAlong gamma remaining
                    (box.left coordinate cut),
                    problem.searchAlong gamma remaining
                      (box.right coordinate cut) with
                | some left, some right =>
                    some (.split coordinate cut left right)
                | _, _ => none
              else
                problem.searchAlong gamma remaining box
termination_by schedule _box => schedule.length

/-- Search the root box using a fixed number of fair full-coordinate rounds. -/
def search
    (problem : RationalLowerBoxProblem variableCount equalityCount
      inequalityCount)
    (gamma : ℚ) (rounds : ℕ) :
    Option (RationalLowerBoxTree variableCount equalityCount inequalityCount) :=
  problem.searchAlong gamma (uniformDyadicSchedule variableCount rounds)
    problem.root

/-- Every tree returned below an arbitrary box passes the exact base checker. -/
theorem verifyTree_searchAlong
    (problem : RationalLowerBoxProblem variableCount equalityCount
      inequalityCount)
    (gamma : ℚ) (schedule : List (Fin variableCount))
    (box : RationalBox variableCount)
    {tree : RationalLowerBoxTree variableCount equalityCount inequalityCount}
    (htree : problem.searchAlong gamma schedule box = some tree) :
    problem.verifyTree gamma box tree = true := by
  induction schedule generalizing box tree with
  | nil =>
      simp only [searchAlong] at htree
      split at htree
      next reason hreason =>
        injection htree with htree
        subst tree
        exact problem.verifyLeaf_firstVerifiedLeaf gamma box hreason
      next hreason => simp at htree
  | cons coordinate remaining hinduction =>
      simp only [searchAlong] at htree
      split at htree
      next reason hreason =>
        injection htree with htree
        subst tree
        exact problem.verifyLeaf_firstVerifiedLeaf gamma box hreason
      next hreason =>
        split at htree
        next hwidth =>
          split at htree
          next left right hleft hright =>
            injection htree with htree
            subst tree
            simp only [verifyTree, Bool.and_eq_true, decide_eq_true_eq]
            refine ⟨⟨?_, hinduction _ hleft⟩, hinduction _ hright⟩
            dsimp only [midpoint]
            constructor <;> linarith
          next hresult => simp at htree
        next hwidth => exact hinduction box htree

/-- Public finite-stage soundness: a search result is a valid certificate. -/
theorem verifies_search
    (problem : RationalLowerBoxProblem variableCount equalityCount
      inequalityCount)
    (gamma : ℚ) (rounds : ℕ)
    {tree : RationalLowerBoxTree variableCount equalityCount inequalityCount}
    (htree : problem.search gamma rounds = some tree) :
    problem.verifies gamma tree = true := by
  exact problem.verifyTree_searchAlong gamma _ problem.root htree

/-- If a finite scheduled search has not closed, one fully refined terminal
box is still unclassified. -/
theorem exists_terminalBox_unclassified_of_searchAlong_eq_none
    (problem : RationalLowerBoxProblem variableCount equalityCount
      inequalityCount)
    (gamma : ℚ) (schedule : List (Fin variableCount))
    (box : RationalBox variableCount)
    (hsearch : problem.searchAlong gamma schedule box = none) :
    ∃ terminal ∈ terminalBoxes schedule box,
      problem.firstVerifiedLeaf gamma terminal = none := by
  induction schedule generalizing box with
  | nil =>
      simp only [searchAlong] at hsearch
      split at hsearch
      next reason hreason => simp at hsearch
      next hreason => exact ⟨box, by simp [terminalBoxes], hreason⟩
  | cons coordinate remaining hinduction =>
      simp only [searchAlong] at hsearch
      split at hsearch
      next reason hreason => simp at hsearch
      next hreason =>
        split at hsearch
        next hwidth =>
          cases hleft : problem.searchAlong gamma remaining
              (box.left coordinate (midpoint (box coordinate))) with
          | none =>
              obtain ⟨terminal, hterminal, hunclassified⟩ :=
                hinduction _ hleft
              refine ⟨terminal, ?_, hunclassified⟩
              simp [terminalBoxes, hwidth, hterminal]
          | some left =>
              cases hright : problem.searchAlong gamma remaining
                  (box.right coordinate (midpoint (box coordinate))) with
              | none =>
                  obtain ⟨terminal, hterminal, hunclassified⟩ :=
                    hinduction _ hright
                  refine ⟨terminal, ?_, hunclassified⟩
                  simp [terminalBoxes, hwidth, hterminal]
              | some right => simp [hleft, hright] at hsearch
        next hwidth =>
          obtain ⟨terminal, hterminal, hunclassified⟩ :=
            hinduction box hsearch
          exact ⟨terminal, by simp [terminalBoxes, hwidth, hterminal],
            hunclassified⟩

/-- Pointwise strict separation that makes exact interval subdivision close.

At each point of the root, either an equality is detectably nonzero, a
required-nonnegative expression is strictly negative, or the objective is
strictly above the requested lower bound. -/
def StrictlySeparated
    (problem : RationalLowerBoxProblem variableCount equalityCount
      inequalityCount)
    (gamma : ℚ) : Prop :=
  ∀ point : Fin variableCount → ℝ, problem.root.Contains point →
    (∃ index, RationalMaxExpression.evalReal point
        (problem.equality index) ≠ 0) ∨
      (∃ index, RationalMaxExpression.evalReal point
        (problem.nonnegative index) < 0) ∨
      (gamma : ℝ) < RationalMaxExpression.evalReal point problem.objective

/-- Along boxes whose rational endpoints converge coordinatewise to one
strictly separated point, exact interval classification eventually succeeds.
This is the local analytic input to the compact finite-stage theorem. -/
theorem eventually_isSome_firstVerifiedLeaf
    {Index : Type*} (filter : Filter Index)
    (problem : RationalLowerBoxProblem variableCount equalityCount
      inequalityCount)
    (gamma : ℚ) (box : Index → RationalBox variableCount)
    (point : Fin variableCount → ℝ)
    (hlower : ∀ coordinate, Filter.Tendsto
      (fun index ↦ ((box index coordinate).lower : ℝ)) filter
      (nhds (point coordinate)))
    (hupper : ∀ coordinate, Filter.Tendsto
      (fun index ↦ ((box index coordinate).upper : ℝ)) filter
      (nhds (point coordinate)))
    (hstrict :
      (∃ index, RationalMaxExpression.evalReal point
          (problem.equality index) ≠ 0) ∨
        (∃ index, RationalMaxExpression.evalReal point
          (problem.nonnegative index) < 0) ∨
        (gamma : ℝ) < RationalMaxExpression.evalReal point
          problem.objective) :
    ∀ᶠ index in filter, (problem.firstVerifiedLeaf gamma (box index)).isSome := by
  rcases hstrict with ⟨coordinate, hcoordinate⟩ |
      ⟨coordinate, hcoordinate⟩ | hobjective
  · have htendsto := RationalMaxExpression.evalInterval_tendsto_point
      filter (problem.equality coordinate) box point hlower hupper
    rcases lt_or_gt_of_ne hcoordinate with hnegative | hpositive
    · filter_upwards [htendsto.2.eventually_lt_const hnegative] with index hindex
      apply problem.isSome_firstVerifiedLeaf_of_verifyLeaf gamma (box index)
        (.equalitySeparated coordinate)
      simp only [verifyLeaf, decide_eq_true_eq]
      exact Or.inl (by exact_mod_cast hindex)
    · filter_upwards [htendsto.1.eventually_const_lt hpositive] with index hindex
      apply problem.isSome_firstVerifiedLeaf_of_verifyLeaf gamma (box index)
        (.equalitySeparated coordinate)
      simp only [verifyLeaf, decide_eq_true_eq]
      exact Or.inr (by exact_mod_cast hindex)
  · have htendsto := RationalMaxExpression.evalInterval_tendsto_point
      filter (problem.nonnegative coordinate) box point hlower hupper
    filter_upwards [htendsto.2.eventually_lt_const hcoordinate] with index hindex
    apply problem.isSome_firstVerifiedLeaf_of_verifyLeaf gamma (box index)
      (.nonnegativeSeparated coordinate)
    simp only [verifyLeaf, decide_eq_true_eq]
    exact_mod_cast hindex
  · have htendsto := RationalMaxExpression.evalInterval_tendsto_point
      filter problem.objective box point hlower hupper
    filter_upwards [htendsto.1.eventually_const_lt hobjective] with index hindex
    apply problem.isSome_firstVerifiedLeaf_of_verifyLeaf gamma (box index)
      .objectiveLowerBound
    simp only [verifyLeaf, decide_eq_true_eq]
    exact_mod_cast hindex.le

/-- Strict pointwise separation on a valid compact rational box makes the
executable uniform-dyadic search close after finitely many rounds.

The proof is classical only in selecting a convergent subsequence from a
hypothetical sequence of failed terminal boxes.  The returned stage and every
search step remain ordinary executable data. -/
theorem exists_search_of_strictlySeparated
    (problem : RationalLowerBoxProblem variableCount equalityCount
      inequalityCount)
    (gamma : ℚ) (hroot : RationalBox.Valid problem.root)
    (hstrict : problem.StrictlySeparated gamma) :
    ∃ rounds tree, problem.search gamma rounds = some tree := by
  classical
  by_contra hno
  push Not at hno
  have hsearchNone (rounds : ℕ) : problem.search gamma rounds = none := by
    cases hsearch : problem.search gamma rounds with
    | none => simp
    | some tree => exact False.elim (hno rounds tree hsearch)
  have hfailed (rounds : ℕ) :
      ∃ terminal ∈ terminalBoxes
          (uniformDyadicSchedule variableCount rounds) problem.root,
        problem.firstVerifiedLeaf gamma terminal = none :=
    problem.exists_terminalBox_unclassified_of_searchAlong_eq_none gamma _ _
      (hsearchNone rounds)
  choose terminal hterminal hunclassified using hfailed
  let lower : Fin variableCount → ℝ :=
    fun coordinate ↦ ((problem.root coordinate).lower : ℝ)
  let upper : Fin variableCount → ℝ :=
    fun coordinate ↦ ((problem.root coordinate).upper : ℝ)
  have hcenterMem (rounds : ℕ) :
      RationalBox.center (terminal rounds) ∈ Set.Icc lower upper := by
    have hcontains := terminalBox_contains_center
      (uniformDyadicSchedule variableCount rounds) problem.root
        (terminal rounds) hroot (hterminal rounds)
    exact ⟨fun coordinate ↦ (hcontains coordinate).1,
      fun coordinate ↦ (hcontains coordinate).2⟩
  obtain ⟨point, hpoint, subsequence, hsubsequence, hcenterTendsto⟩ :=
    (isCompact_Icc : IsCompact (Set.Icc lower upper)).tendsto_subseq hcenterMem
  have hsubsequenceAtTop : Filter.Tendsto subsequence Filter.atTop Filter.atTop :=
    hsubsequence.tendsto_atTop
  have hwidthTendsto (coordinate : Fin variableCount) :
      Filter.Tendsto
        (fun rank ↦
          (((terminal (subsequence rank) coordinate).upper -
              (terminal (subsequence rank) coordinate).lower : ℚ) : ℝ))
        Filter.atTop (nhds 0) := by
    have hpow : Filter.Tendsto
        (fun rank : ℕ ↦ (((1 / 2 : ℚ) : ℝ)) ^ rank)
        Filter.atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    have hscaled := (hpow.comp hsubsequenceAtTop).const_mul
      (((problem.root coordinate).upper -
        (problem.root coordinate).lower : ℚ) : ℝ)
    have hscaledZero : Filter.Tendsto
        (fun rank ↦
          (((problem.root coordinate).upper -
              (problem.root coordinate).lower : ℚ) : ℝ) *
            (((1 / 2 : ℚ) : ℝ)) ^ subsequence rank)
        Filter.atTop (nhds 0) := by
      simpa only [Function.comp_apply, mul_zero] using hscaled
    apply hscaledZero.congr'
    filter_upwards [] with rank
    have heq := uniformTerminalBox_width_eq (subsequence rank) problem.root
      (terminal (subsequence rank)) hroot (hterminal (subsequence rank))
      coordinate
    unfold RationalBox.width at heq
    rw [heq]
    push_cast
    have hpower : (1 / 2 : ℝ) ^ subsequence rank =
        (2 : ℝ)⁻¹ ^ subsequence rank := by
      congr 1
      norm_num
    calc
      (((problem.root coordinate).upper : ℝ) -
          ((problem.root coordinate).lower : ℝ)) *
          (1 / 2 : ℝ) ^ subsequence rank =
          (((problem.root coordinate).upper : ℝ) -
            ((problem.root coordinate).lower : ℝ)) *
            (2 : ℝ)⁻¹ ^ subsequence rank :=
        congrArg (fun factor : ℝ ↦
          (((problem.root coordinate).upper : ℝ) -
            ((problem.root coordinate).lower : ℝ)) * factor) hpower
      _ = (((problem.root coordinate).upper : ℝ) -
            ((problem.root coordinate).lower : ℝ)) /
          (2 : ℝ) ^ subsequence rank := by
        rw [div_eq_mul_inv, inv_pow]
  have hlowerTendsto (coordinate : Fin variableCount) :
      Filter.Tendsto
        (fun rank ↦ ((terminal (subsequence rank) coordinate).lower : ℝ))
        Filter.atTop (nhds (point coordinate)) := by
    have hcenterCoordinate :=
      (tendsto_pi_nhds.mp hcenterTendsto) coordinate
    have htarget := hcenterCoordinate.sub
      ((hwidthTendsto coordinate).div_const 2)
    have htarget' : Filter.Tendsto
        (fun rank ↦
          RationalBox.center (terminal (subsequence rank)) coordinate -
            (((terminal (subsequence rank) coordinate).upper -
                (terminal (subsequence rank) coordinate).lower : ℚ) : ℝ) / 2)
        Filter.atTop (nhds (point coordinate)) := by
      simpa only [Function.comp_apply, zero_div, sub_zero] using htarget
    apply htarget'.congr'
    filter_upwards [] with rank
    simp only [RationalBox.center, midpoint]
    push_cast
    ring
  have hupperTendsto (coordinate : Fin variableCount) :
      Filter.Tendsto
        (fun rank ↦ ((terminal (subsequence rank) coordinate).upper : ℝ))
        Filter.atTop (nhds (point coordinate)) := by
    have hcenterCoordinate :=
      (tendsto_pi_nhds.mp hcenterTendsto) coordinate
    have htarget := hcenterCoordinate.add
      ((hwidthTendsto coordinate).div_const 2)
    have htarget' : Filter.Tendsto
        (fun rank ↦
          RationalBox.center (terminal (subsequence rank)) coordinate +
            (((terminal (subsequence rank) coordinate).upper -
                (terminal (subsequence rank) coordinate).lower : ℚ) : ℝ) / 2)
        Filter.atTop (nhds (point coordinate)) := by
      simpa only [Function.comp_apply, zero_div, add_zero] using htarget
    apply htarget'.congr'
    filter_upwards [] with rank
    simp only [RationalBox.center, midpoint]
    push_cast
    ring
  have hpointRoot : problem.root.Contains point := by
    intro coordinate
    exact ⟨hpoint.1 coordinate, hpoint.2 coordinate⟩
  have heventually := problem.eventually_isSome_firstVerifiedLeaf
    Filter.atTop gamma (fun rank ↦ terminal (subsequence rank)) point
      hlowerTendsto hupperTendsto (hstrict point hpointRoot)
  obtain ⟨rank, hclassified⟩ := heventually.exists
  rw [hunclassified (subsequence rank)] at hclassified
  simp at hclassified

/-- The usual strict-minimum hypothesis implies pointwise separation: an
infeasible point violates an equality or a required inequality, while a
feasible point has objective strictly above `gamma`. -/
theorem strictlySeparated_of_feasible_objective_gt
    (problem : RationalLowerBoxProblem variableCount equalityCount
      inequalityCount)
    (gamma : ℚ)
    (hobjective : ∀ point, problem.Feasible point →
      (gamma : ℝ) < RationalMaxExpression.evalReal point problem.objective) :
    problem.StrictlySeparated gamma := by
  intro point hpoint
  by_cases hequality : ∀ index, RationalMaxExpression.evalReal point
      (problem.equality index) = 0
  · by_cases hnonnegative : ∀ index, 0 ≤ RationalMaxExpression.evalReal point
        (problem.nonnegative index)
    · exact Or.inr (Or.inr (hobjective point ⟨hpoint, hequality, hnonnegative⟩))
    · right
      left
      push Not at hnonnegative
      exact hnonnegative
  · left
    push Not at hequality
    exact hequality

/-- Strict objective separation on the feasible set yields a finite generated
certificate accepted by the exact checker. -/
theorem exists_search_verifies_of_feasible_objective_gt
    (problem : RationalLowerBoxProblem variableCount equalityCount
      inequalityCount)
    (gamma : ℚ) (hroot : RationalBox.Valid problem.root)
    (hobjective : ∀ point, problem.Feasible point →
      (gamma : ℝ) < RationalMaxExpression.evalReal point problem.objective) :
    ∃ rounds tree,
      problem.search gamma rounds = some tree ∧
        problem.verifies gamma tree = true := by
  obtain ⟨rounds, tree, htree⟩ := problem.exists_search_of_strictlySeparated
    gamma hroot (problem.strictlySeparated_of_feasible_objective_gt
      gamma hobjective)
  exact ⟨rounds, tree, htree,
    problem.verifies_search gamma rounds htree⟩

end RationalLowerBoxProblem

end Interval
end Math
