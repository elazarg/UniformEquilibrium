/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Powerset
import Mathlib.Tactic
import MathUE.FiniteBooleanEndpointOrbit

/-!
# Simple one-coordinate cycles on four players

This file gives a finite, game-independent interface for the Boolean-cube
calculation used by finite-player endpoint iteration.  `CoalitionCode` is an
explicit enumeration of the eleven subsets of `Fin 4` having cardinality at
least two.  A cycle support is represented by two bit masks selecting a
finite set of these vertices, together with the assertion that every selected
vertex has exactly two selected one-coordinate neighbours.

The support interface forgets connectedness, and is convenient for later
cycle-support arguments: the support of every chord-free ordinary simple graph
cycle satisfies it.  It excludes length-two
closed walks which traverse one undirected edge twice; those are not simple
cycles in a simple graph.  The finite results below are checked by the
ordinary kernel reducer (`decide`), not by `native_decide`.
-/

namespace MathUE.FinFourCoalitionCycle

abbrev Player := Fin 4

/-- The eleven coalitions of at least two players, in a fixed enumeration. -/
abbrev CoalitionCode := Fin 11

abbrev LowMask := Fin 32
abbrev HighMask := Fin 64

def coalitionSet (c : CoalitionCode) : Finset Player :=
  ![
    {0, 1}, {0, 2}, {0, 3}, {1, 2}, {1, 3}, {2, 3},
    {0, 1, 2}, {0, 1, 3}, {0, 2, 3}, {1, 2, 3},
    {0, 1, 2, 3}
  ] c

theorem coalitionSet_card_ge_two (c : CoalitionCode) :
    2 ≤ (coalitionSet c).card := by
  revert c
  decide

theorem coalitionSet_injective : Function.Injective coalitionSet := by
  decide

abbrev NonsingletonCoalition :=
  MathUE.FiniteBooleanEndpointOrbit.NonsingletonCoalition Player

noncomputable instance : DecidableEq NonsingletonCoalition := Classical.decEq _

/-- A code viewed as the corresponding nonsingleton-coalition subtype. -/
def codeToCoalition (c : CoalitionCode) : NonsingletonCoalition :=
  ⟨coalitionSet c, by
    have h := coalitionSet_card_ge_two c
    omega⟩

theorem codeToCoalition_injective : Function.Injective codeToCoalition := by
  intro c d h
  apply coalitionSet_injective
  exact congrArg Subtype.val h

theorem card_nonsingletonCoalition_fin_four :
    Fintype.card NonsingletonCoalition = 11 := by
  rw [MathUE.FiniteBooleanEndpointOrbit.card_nonsingletonCoalition]
  norm_num [Fintype.card_fin]

/-- The fixed eleven-code enumeration is exactly the nonsingleton subtype. -/
noncomputable def coalitionCodeEquiv : CoalitionCode ≃ NonsingletonCoalition :=
  Equiv.ofBijective codeToCoalition <| by
    rw [Fintype.bijective_iff_injective_and_card]
    exact ⟨codeToCoalition_injective, by
      rw [Fintype.card_fin, card_nonsingletonCoalition_fin_four]⟩

/-- One-coordinate adjacency on the enumerated coalitions. -/
def oneCoordinateAdjacent (c d : CoalitionCode) : Prop :=
  (coalitionSet c \ coalitionSet d ∪ coalitionSet d \ coalitionSet c).card = 1

instance (c d : CoalitionCode) : Decidable (oneCoordinateAdjacent c d) := by
  unfold oneCoordinateAdjacent
  infer_instance

/-- Membership in the support selected by two masks.

The low mask selects codes `0` through `4`; the high mask selects codes `5`
through `10`.  Every subset of the eleven coalition codes has exactly one
such pair of masks, so this is an explicit finite support interface rather
than a bounded experimental enumeration.
-/
def memSupport (low : LowMask) (high : HighMask) (c : CoalitionCode) : Prop :=
  if c.val < 5 then
    low.val &&& (2 ^ c.val) ≠ 0
  else
    high.val &&& (2 ^ (c.val - 5)) ≠ 0

instance (low : LowMask) (high : HighMask) (c : CoalitionCode) :
    Decidable (memSupport low high c) := by
  unfold memSupport
  split <;> infer_instance

/-- The selected finite set of coalition vertices. -/
def support (low : LowMask) (high : HighMask) : Finset CoalitionCode :=
  Finset.univ.filter (memSupport low high)

/-- The selected low and high code positions, viewed as finite subsets. -/
def lowSelection (low : LowMask) : Finset (Fin 5) :=
  Finset.univ.filter (fun i => low.val &&& (2 ^ i.val) ≠ 0)

def highSelection (high : HighMask) : Finset (Fin 6) :=
  Finset.univ.filter (fun i => high.val &&& (2 ^ i.val) ≠ 0)

instance (low : LowMask) (i : Fin 5) :
    Decidable (low.val &&& (2 ^ i.val) ≠ 0) := inferInstance

instance (high : HighMask) (i : Fin 6) :
    Decidable (high.val &&& (2 ^ i.val) ≠ 0) := inferInstance

theorem lowSelection_injective : Function.Injective lowSelection := by
  decide

theorem lowSelection_bijective : Function.Bijective lowSelection := by
  rw [Fintype.bijective_iff_injective_and_card]
  exact ⟨lowSelection_injective, by
    simp [Fintype.card_finset, Fintype.card_fin]⟩

theorem highSelection_injective : Function.Injective highSelection := by
  decide

theorem highSelection_bijective : Function.Bijective highSelection := by
  rw [Fintype.bijective_iff_injective_and_card]
  exact ⟨highSelection_injective, by
    simp [Fintype.card_finset, Fintype.card_fin]⟩

/-- A support described by finite low and high position selections. -/
def selectionSupport (low : Finset (Fin 5)) (high : Finset (Fin 6)) :
    Finset CoalitionCode :=
  Finset.univ.filter fun c =>
    if h : c.val < 5 then
      (⟨c.val, h⟩ : Fin 5) ∈ low
    else
      (⟨c.val - 5, by omega⟩ : Fin 6) ∈ high

def lowIndices (s : Finset CoalitionCode) : Finset (Fin 5) :=
  Finset.univ.filter fun i =>
    (⟨i.val, by omega⟩ : CoalitionCode) ∈ s

def highIndices (s : Finset CoalitionCode) : Finset (Fin 6) :=
  Finset.univ.filter fun i =>
    (⟨i.val + 5, by omega⟩ : CoalitionCode) ∈ s

theorem selectionSupport_lowIndices_highIndices (s : Finset CoalitionCode) :
    selectionSupport (lowIndices s) (highIndices s) = s := by
  ext c
  fin_cases c <;> simp [selectionSupport, lowIndices, highIndices]

theorem support_eq_selectionSupport (low : LowMask) (high : HighMask) :
    support low high = selectionSupport (lowSelection low) (highSelection high) := by
  ext c
  fin_cases c <;> simp [support, memSupport, selectionSupport,
    lowSelection, highSelection]

theorem exists_mask_for_code_support (s : Finset CoalitionCode) :
    ∃ low : LowMask, ∃ high : HighMask, support low high = s := by
  obtain ⟨low, hlow⟩ := lowSelection_bijective.2 (lowIndices s)
  obtain ⟨high, hhigh⟩ := highSelection_bijective.2 (highIndices s)
  refine ⟨low, high, ?_⟩
  rw [support_eq_selectionSupport, hlow, hhigh]
  exact selectionSupport_lowIndices_highIndices s

/-- One-coordinate adjacency on the nonsingleton-coalition subtype. -/
def subtypeAdjacent (a b : NonsingletonCoalition) : Prop :=
  (a.1 \ b.1 ∪ b.1 \ a.1).card = 1

instance (a b : NonsingletonCoalition) : Decidable (subtypeAdjacent a b) := by
  unfold subtypeAdjacent
  infer_instance

def subtypeNeighbours (s : Finset NonsingletonCoalition)
    (a : NonsingletonCoalition) : Finset NonsingletonCoalition :=
  s.filter (subtypeAdjacent a)

def IsSubtypeCycleSupport (s : Finset NonsingletonCoalition) : Prop :=
  s.Nonempty ∧ ∀ a ∈ s, (subtypeNeighbours s a).card = 2

noncomputable instance (s : Finset NonsingletonCoalition) :
    Decidable (IsSubtypeCycleSupport s) := by
  unfold IsSubtypeCycleSupport
  infer_instance

def subtypeHasCommonPlayer (s : Finset NonsingletonCoalition) : Prop :=
  ∃ p : Player, ∀ a ∈ s, p ∈ a.1

noncomputable instance (s : Finset NonsingletonCoalition) :
    Decidable (subtypeHasCommonPlayer s) := by
  unfold subtypeHasCommonPlayer
  infer_instance

def subtypeHasComplementaryPairs (s : Finset NonsingletonCoalition) : Prop :=
  ∃ a ∈ s, ∃ b ∈ s,
    a.1.card = 2 ∧ b.1.card = 2 ∧ Disjoint a.1 b.1

instance (s : Finset NonsingletonCoalition) :
    Decidable (subtypeHasComplementaryPairs s) := by
  unfold subtypeHasComplementaryPairs
  infer_instance

theorem coalitionSet_equiv_symm (a : NonsingletonCoalition) :
    coalitionSet (coalitionCodeEquiv.symm a) = a.1 := by
  exact congrArg Subtype.val (coalitionCodeEquiv.apply_symm_apply a)

noncomputable def codeSupportOfSubtype
    (s : Finset NonsingletonCoalition) : Finset CoalitionCode :=
  s.image coalitionCodeEquiv.symm

theorem card_codeSupportOfSubtype
    (s : Finset NonsingletonCoalition) :
    (codeSupportOfSubtype s).card = s.card := by
  exact Finset.card_image_of_injective s coalitionCodeEquiv.symm.injective

theorem exists_mask_for_subtype_support
    (s : Finset NonsingletonCoalition) :
    ∃ low : LowMask, ∃ high : HighMask,
      (support low high).image codeToCoalition = s := by
  obtain ⟨low, high, hs⟩ := exists_mask_for_code_support
    (codeSupportOfSubtype s)
  refine ⟨low, high, ?_⟩
  ext a
  rw [Finset.mem_image]
  constructor
  · rintro ⟨c, hc, rfl⟩
    rw [hs] at hc
    simp [codeSupportOfSubtype] at hc
    obtain ⟨b, hb, hba⟩ := hc
    rw [← hba]
    change coalitionCodeEquiv (coalitionCodeEquiv.symm b) ∈ s
    rw [coalitionCodeEquiv.apply_symm_apply]
    exact hb
  · intro ha
    have : coalitionCodeEquiv.symm a ∈ codeSupportOfSubtype s := by
      simp [codeSupportOfSubtype, ha]
    rw [← hs] at this
    exact ⟨coalitionCodeEquiv.symm a, this,
      coalitionCodeEquiv.apply_symm_apply a⟩

def neighbours (low : LowMask) (high : HighMask) (c : CoalitionCode) :
    Finset CoalitionCode :=
  (support low high).filter (oneCoordinateAdjacent c)

theorem neighbours_image_code
    (s : Finset NonsingletonCoalition)
    (low : LowMask) (high : HighMask)
    (hs : (support low high).image codeToCoalition = s)
    (a : NonsingletonCoalition) :
    neighbours low high (coalitionCodeEquiv.symm a) =
      (subtypeNeighbours s a).image coalitionCodeEquiv.symm := by
  rw [← hs]
  ext c
  simp only [neighbours, subtypeNeighbours, Finset.mem_filter, Finset.mem_image]
  constructor
  · intro h
    refine ⟨codeToCoalition c, ⟨⟨c, h.1, rfl⟩, ?_⟩, ?_⟩
    · simpa [subtypeAdjacent, oneCoordinateAdjacent,
        coalitionSet_equiv_symm, codeToCoalition] using h.2
    · change coalitionCodeEquiv.symm (coalitionCodeEquiv c) = c
      exact coalitionCodeEquiv.left_inv c
  · rintro ⟨w, ⟨⟨d, hd, hdw⟩, hwa⟩, hwc⟩
    have heq : coalitionCodeEquiv.symm w = d := by
      rw [← hdw]
      change coalitionCodeEquiv.symm (coalitionCodeEquiv d) = d
      exact coalitionCodeEquiv.left_inv d
    have hcd : c = d := hwc.symm.trans heq
    constructor
    · rw [hcd]
      exact hd
    · rw [hcd]
      have hwa' : subtypeAdjacent a (codeToCoalition d) := by
        rw [hdw]
        exact hwa
      simpa [subtypeAdjacent, oneCoordinateAdjacent,
        coalitionSet_equiv_symm, codeToCoalition] using hwa'

/-- A nonempty support whose induced one-coordinate degree is two everywhere.

The support of a connected chord-free simple cycle has this property.
Connectivity is not needed for the two conclusions proved here, so omitting
it makes the interface stable under taking the support of a later walk proof.
-/
def IsCycleSupport (low : LowMask) (high : HighMask) : Prop :=
  (support low high).Nonempty ∧
    ∀ c ∈ support low high, (neighbours low high c).card = 2

instance (low : LowMask) (high : HighMask) :
    Decidable (IsCycleSupport low high) := by
  unfold IsCycleSupport
  infer_instance

/-- All selected coalitions contain one common player. -/
def HasCommonPlayer (low : LowMask) (high : HighMask) : Prop :=
  ∃ p : Player, ∀ c ∈ support low high, p ∈ coalitionSet c

instance (low : LowMask) (high : HighMask) :
    Decidable (HasCommonPlayer low high) := by
  unfold HasCommonPlayer
  infer_instance

/-- The support contains a complementary pair of pair coalitions. -/
def HasComplementaryPairs (low : LowMask) (high : HighMask) : Prop :=
  ∃ c ∈ support low high, ∃ d ∈ support low high,
    (coalitionSet c).card = 2 ∧
      (coalitionSet d).card = 2 ∧
        Disjoint (coalitionSet c) (coalitionSet d)

instance (low : LowMask) (high : HighMask) :
    Decidable (HasComplementaryPairs low high) := by
  unfold HasComplementaryPairs
  infer_instance

/-- A simple one-coordinate cycle on four players has at most eight vertices.

This is an exhaustive kernel check over the `32 × 64` mask interface; it is
the exact finite graph theorem, not a claim about an external computation.
-/
theorem cycleSupport_card_le_eight
    (low : LowMask) (high : HighMask)
    (hcycle : IsCycleSupport low high) :
    (support low high).card ≤ 8 := by
  revert high low
  decide

/-- Every simple one-coordinate cycle has a common player or complementary
pair vertices. -/
theorem cycleSupport_common_or_complementary
    (low : LowMask) (high : HighMask)
    (hcycle : IsCycleSupport low high) :
    HasCommonPlayer low high ∨ HasComplementaryPairs low high := by
  revert high low
  decide

theorem subtype_cycle_code_support
    (s : Finset NonsingletonCoalition)
    (low : LowMask) (high : HighMask)
    (hs : (support low high).image codeToCoalition = s)
    (hcycle : IsSubtypeCycleSupport s) :
    IsCycleSupport low high := by
  constructor
  · obtain ⟨a, ha⟩ := hcycle.1
    rw [← hs] at ha
    simp only [Finset.mem_image] at ha
    obtain ⟨c, hc, hca⟩ := ha
    refine ⟨c, hc⟩
  · intro c hc
    have hmem : codeToCoalition c ∈ s := by
      rw [← hs]
      simp only [Finset.mem_image]
      exact ⟨c, hc, rfl⟩
    have hdegree := hcycle.2 (codeToCoalition c) hmem
    have hneigh := neighbours_image_code s low high hs (codeToCoalition c)
    have heq : coalitionCodeEquiv.symm (codeToCoalition c) = c := by
      change coalitionCodeEquiv.symm (coalitionCodeEquiv c) = c
      exact coalitionCodeEquiv.left_inv c
    calc
      (neighbours low high c).card =
          (neighbours low high (coalitionCodeEquiv.symm
            (codeToCoalition c))).card := by rw [heq]
      _ = ((subtypeNeighbours s (codeToCoalition c)).image
          coalitionCodeEquiv.symm).card := congrArg Finset.card hneigh
      _ = (subtypeNeighbours s (codeToCoalition c)).card :=
        Finset.card_image_of_injective _ coalitionCodeEquiv.symm.injective
      _ = 2 := hdegree

theorem subtype_cycle_support_card_le_eight
    (s : Finset NonsingletonCoalition)
    (hcycle : IsSubtypeCycleSupport s) : s.card ≤ 8 := by
  obtain ⟨low, high, hs⟩ := exists_mask_for_subtype_support s
  have hcode := subtype_cycle_code_support s low high hs hcycle
  have hcard := cycleSupport_card_le_eight low high hcode
  calc
    s.card = ((support low high).image codeToCoalition).card := by rw [hs]
    _ = (support low high).card :=
      Finset.card_image_of_injective _ codeToCoalition_injective
    _ ≤ 8 := hcard

theorem subtype_cycle_support_common_or_complementary
    (s : Finset NonsingletonCoalition)
    (hcycle : IsSubtypeCycleSupport s) :
    subtypeHasCommonPlayer s ∨ subtypeHasComplementaryPairs s := by
  obtain ⟨low, high, hs⟩ := exists_mask_for_subtype_support s
  have hcode := subtype_cycle_code_support s low high hs hcycle
  rcases cycleSupport_common_or_complementary low high hcode with hcommon | hcomp
  · left
    obtain ⟨p, hp⟩ := hcommon
    refine ⟨p, ?_⟩
    intro a ha
    rw [← hs] at ha
    simp only [Finset.mem_image] at ha
    obtain ⟨c, hc, hca⟩ := ha
    rw [← hca]
    simpa [codeToCoalition] using hp c hc
  · right
    obtain ⟨c, hc, d, hd, hccard, hdcard, hdisjoint⟩ := hcomp
    refine ⟨codeToCoalition c, ?_, codeToCoalition d, ?_, ?_, ?_, ?_⟩
    · rw [← hs]
      simp only [Finset.mem_image]
      exact ⟨c, hc, rfl⟩
    · rw [← hs]
      simp only [Finset.mem_image]
      exact ⟨d, hd, rfl⟩
    · simpa [codeToCoalition] using hccard
    · simpa [codeToCoalition] using hdcard
    · simpa [codeToCoalition] using hdisjoint

theorem subtype_cycle_support_card_le_eight_and_geometry
    (s : Finset NonsingletonCoalition)
    (hcycle : IsSubtypeCycleSupport s) :
    s.card ≤ 8 ∧
      (subtypeHasCommonPlayer s ∨ subtypeHasComplementaryPairs s) := by
  exact ⟨subtype_cycle_support_card_le_eight s hcycle,
    subtype_cycle_support_common_or_complementary s hcycle⟩

/-- The sixteen undirected one-coordinate edges in the eleven-vertex cube. -/
abbrev EdgeCode := Fin 16

def edgeEndpoints (e : EdgeCode) : CoalitionCode × CoalitionCode :=
  ![
    (0, 6), (0, 7), (1, 6), (1, 8), (2, 7), (2, 8),
    (3, 6), (3, 9), (4, 7), (4, 9), (5, 8), (5, 9),
    (6, 10), (7, 10), (8, 10), (9, 10)
  ] e

abbrev EdgeNibble := Fin 16
abbrev EdgeLowMask := EdgeNibble × EdgeNibble
abbrev EdgeHighMask := EdgeNibble × EdgeNibble

def memEdgeSupportBool (low : EdgeLowMask) (high : EdgeHighMask) (e : EdgeCode) :
    Bool :=
  if e.val < 4 then
    decide (low.1.val &&& (2 ^ e.val) ≠ 0)
  else if e.val < 8 then
    decide (low.2.val &&& (2 ^ (e.val - 4)) ≠ 0)
  else if e.val < 12 then
    decide (high.1.val &&& (2 ^ (e.val - 8)) ≠ 0)
  else
    decide (high.2.val &&& (2 ^ (e.val - 12)) ≠ 0)

def memEdgeSupport (low : EdgeLowMask) (high : EdgeHighMask) (e : EdgeCode) :
    Prop := memEdgeSupportBool low high e = true

instance (low : EdgeLowMask) (high : EdgeHighMask) (e : EdgeCode) :
    Decidable (memEdgeSupport low high e) := by
  unfold memEdgeSupport
  infer_instance

def edgeSupport (low : EdgeLowMask) (high : EdgeHighMask) :
    Finset CoalitionCode :=
  (Finset.univ.filter (memEdgeSupport low high)).biUnion fun e =>
    { (edgeEndpoints e).1, (edgeEndpoints e).2 }

def selectedEdgeDegree (low : EdgeLowMask) (high : EdgeHighMask)
    (c : CoalitionCode) : Nat :=
  (Finset.univ.filter (fun e => memEdgeSupport low high e ∧
    ((edgeEndpoints e).1 = c ∨ (edgeEndpoints e).2 = c))).card

/-- A cycle described by its traversed edges, rather than all cube chords. -/
def IsSelectedEdgeCycle (low : EdgeLowMask) (high : EdgeHighMask) : Prop :=
  (edgeSupport low high).Nonempty ∧
    ∀ c ∈ edgeSupport low high, selectedEdgeDegree low high c = 2

instance (low : EdgeLowMask) (high : EdgeHighMask) :
    Decidable (IsSelectedEdgeCycle low high) := by
  unfold IsSelectedEdgeCycle
  infer_instance

def selectedEdgeHasCommonPlayer (low : EdgeLowMask) (high : EdgeHighMask) : Prop :=
  ∃ p : Player, ∀ c ∈ edgeSupport low high, p ∈ coalitionSet c

instance (low : EdgeLowMask) (high : EdgeHighMask) :
    Decidable (selectedEdgeHasCommonPlayer low high) := by
  unfold selectedEdgeHasCommonPlayer
  infer_instance

def selectedEdgeHasComplementaryPairs
    (low : EdgeLowMask) (high : EdgeHighMask) : Prop :=
  ∃ c ∈ edgeSupport low high, ∃ d ∈ edgeSupport low high,
    (coalitionSet c).card = 2 ∧
      (coalitionSet d).card = 2 ∧
        Disjoint (coalitionSet c) (coalitionSet d)

instance (low : EdgeLowMask) (high : EdgeHighMask) :
    Decidable (selectedEdgeHasComplementaryPairs low high) := by
  unfold selectedEdgeHasComplementaryPairs
  infer_instance

theorem adjacent_pair_has_common_player (c d : CoalitionCode)
    (h : oneCoordinateAdjacent c d) :
    ∃ p : Player, p ∈ coalitionSet c ∧ p ∈ coalitionSet d := by
  revert d c
  decide

def HasCommonPlayerOn (s : Finset CoalitionCode) : Prop :=
  ∃ p : Player, ∀ c ∈ s, p ∈ coalitionSet c

def HasComplementaryPairsOn (s : Finset CoalitionCode) : Prop :=
  ∃ c ∈ s, ∃ d ∈ s,
    (coalitionSet c).card = 2 ∧
      (coalitionSet d).card = 2 ∧
        Disjoint (coalitionSet c) (coalitionSet d)

instance (s : Finset CoalitionCode) : Decidable (HasCommonPlayerOn s) := by
  unfold HasCommonPlayerOn
  infer_instance

instance (s : Finset CoalitionCode) :
    Decidable (HasComplementaryPairsOn s) := by
  unfold HasComplementaryPairsOn
  infer_instance

theorem cycleSupport_card_le_eight_and_geometry
    (low : LowMask) (high : HighMask)
    (hcycle : IsCycleSupport low high) :
    (support low high).card ≤ 8 ∧
      (HasCommonPlayer low high ∨ HasComplementaryPairs low high) := by
  exact ⟨cycleSupport_card_le_eight low high hcycle,
    cycleSupport_common_or_complementary low high hcycle⟩

end MathUE.FinFourCoalitionCycle
