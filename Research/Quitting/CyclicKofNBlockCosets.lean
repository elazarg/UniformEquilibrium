/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Research.Quitting.CyclicKofNArithmetic

/-!
# Collapsed blocks are unions of stabilizer cosets

The arithmetic divisor `d` has a direct geometric meaning.  If `H` is the
translation stabilizer of a block `A`, then for every active player `a`, the
whole coset `H + a` is active.  Thus `A` is a union of disjoint `H`-orbits,
each of cardinality `|H|`.

This explains both divisibilities:

* `|H| ∣ |A|` because the active block is tiled by stabilizer cosets;
* `|H| ∣ |G|` because the whole population is tiled by those cosets.

It also shows what a collapsed `K/N` schedule really is: a primitive schedule
on quotient-sized packets, with each quotient player expanded into an equal
symmetry class.
-/

namespace GameTheory

namespace CyclicKofNBlockCosets

open CyclicKofNArithmetic
open scoped Pointwise

noncomputable section

variable {G : Type*} [AddGroup G] [Fintype G] [DecidableEq G]

/-- The translation stabilizer of a finite block. -/
abbrev blockStabilizer (A : Finset G) : AddSubgroup G :=
  AddAction.stabilizer G A

instance stabilizerOrbitFintype (A : Finset G) (a : G) :
    Fintype (AddAction.orbit (blockStabilizer A) a) :=
  Fintype.ofFinite _

omit [Fintype G] in
/-- The stabilizer orbit of an active player stays inside the active block. -/
theorem stabilizerOrbit_subset_block (A : Finset G) {a : G} (ha : a ∈ A) :
    AddAction.orbit (blockStabilizer A) a ⊆ (A : Set G) := by
  rintro x ⟨h, rfl⟩
  have hstable : (h : G) +ᵥ A = A := h.property
  have hmem : (h : G) + a ∈ (h : G) +ᵥ A :=
    (Finset.vadd_mem_vadd_finset_iff (s := A) (b := a) (h : G)).mpr ha
  rwa [hstable] at hmem

/-- Translation by a base point identifies the stabilizer with its orbit of
that point. -/
def stabilizerEquivOrbit (A : Finset G) (a : G) :
    blockStabilizer A ≃ AddAction.orbit (blockStabilizer A) a where
  toFun h := ⟨(h : G) + a, ⟨h, rfl⟩⟩
  invFun x :=
    ⟨x.1 - a, by
      obtain ⟨h, hx⟩ := x.2
      have hval : (h : G) = x.1 - a := by
        rw [← hx]
        change (h : G) = (h : G) + a - a
        rw [add_sub_cancel_right]
      simpa [hval] using h.property⟩
  left_inv h := by
    apply Subtype.ext
    simp
  right_inv x := by
    apply Subtype.ext
    simp

/-- Every stabilizer coset/orbit has exactly the stabilizer cardinality. -/
theorem card_stabilizerOrbit (A : Finset G) (a : G) :
    Fintype.card (AddAction.orbit (blockStabilizer A) a) =
      Fintype.card (blockStabilizer A) := by
  exact Fintype.card_congr (stabilizerEquivOrbit A a).symm

omit [Fintype G] in
/-- Two stabilizer orbits through active points are either identical or
disjoint; this is the coset partition property. -/
theorem stabilizerOrbit_eq_or_disjoint (A : Finset G) (a b : G) :
    AddAction.orbit (blockStabilizer A) a =
        AddAction.orbit (blockStabilizer A) b ∨
      Disjoint (AddAction.orbit (blockStabilizer A) a)
        (AddAction.orbit (blockStabilizer A) b) := by
  by_cases hinter :
      (AddAction.orbit (blockStabilizer A) a ∩
        AddAction.orbit (blockStabilizer A) b).Nonempty
  · left
    obtain ⟨x, hxa, hxb⟩ := hinter
    rw [AddAction.orbit_eq_iff]
    obtain ⟨ha, hha⟩ := hxa
    obtain ⟨hb, hhb⟩ := hxb
    refine ⟨-ha + hb, ?_⟩
    change ((-ha + hb : blockStabilizer A) : G) + b = a
    change -(ha : G) + (hb : G) + b = a
    have hxb : (hb : G) + b = x := hhb
    have hxa : (ha : G) + a = x := hha
    calc
      -(ha : G) + (hb : G) + b =
          -(ha : G) + ((hb : G) + b) := by rw [add_assoc]
      _ = -(ha : G) + x := by rw [hxb]
      _ = -(ha : G) + ((ha : G) + a) := by rw [hxa]
      _ = a := by simp
  · right
    rw [Set.disjoint_left]
    intro x hxa hxb
    exact hinter ⟨x, hxa, hxb⟩

omit [Fintype G] in
/-- Pointwise coset form: if `a` is active and `h` stabilizes the block, then
`h+a` is active. -/
theorem vadd_mem_block_of_mem_stabilizer
    (A : Finset G) {a : G} (ha : a ∈ A) (h : blockStabilizer A) :
    (h : G) + a ∈ A := by
  exact stabilizerOrbit_subset_block A ha ⟨h, rfl⟩

omit [Fintype G] in
/-- A block with nontrivial collapse cannot distinguish players inside one
stabilizer coset: membership is invariant under the entire stabilizer. -/
theorem mem_block_iff_vadd_stabilizer
    (A : Finset G) (a : G) (h : blockStabilizer A) :
    (h : G) + a ∈ A ↔ a ∈ A := by
  have hstable : (h : G) +ᵥ A = A := h.property
  have hiff := Finset.vadd_mem_vadd_finset_iff
    (a := (h : G)) (b := a) (s := A)
  simpa only [hstable, vadd_eq_add] using hiff

/-- The coset cardinality divides the active block cardinality, now exposed
through the geometric stabilizer-coset interpretation. -/
theorem stabilizerCosetCard_dvd_blockCard (A : Finset G) :
    Fintype.card (blockStabilizer A) ∣ A.card :=
  card_translationStabilizer_dvd_card_block A

/-- The quotient number of active packets is `K/d`. -/
theorem activePacketCount_eq_div_stabilizer (A : Finset G) :
    A.card / Fintype.card (blockStabilizer A) *
        Fintype.card (blockStabilizer A) = A.card := by
  exact Nat.div_mul_cancel (stabilizerCosetCard_dvd_blockCard A)

/-- Together with orbit-stabilizer, a collapsed block has a clean two-level
parameterization: `K/d` active packets among `N/d` population packets. -/
theorem quotientPacketParameters (A : Finset G) :
    let d := Fintype.card (blockStabilizer A)
    let activePackets := A.card / d
    let populationPackets := Fintype.card G / d
    activePackets * d = A.card ∧
      populationPackets * d = Fintype.card G ∧
      populationPackets = Fintype.card (TranslationPhase A) := by
  dsimp only
  constructor
  · exact Nat.div_mul_cancel (stabilizerCosetCard_dvd_blockCard A)
  constructor
  · have hdvd : Fintype.card (blockStabilizer A) ∣ Fintype.card G := by
      refine ⟨Fintype.card (TranslationPhase A), ?_⟩
      simpa [mul_comm] using (translationOrbit_mul_stabilizer A).symm
    exact Nat.div_mul_cancel hdvd
  · exact (card_translationPhase_eq_div_stabilizer A).symm

end

end CyclicKofNBlockCosets

end GameTheory
