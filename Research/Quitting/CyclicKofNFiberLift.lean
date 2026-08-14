/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Research.Quitting.CyclicKofNArithmetic

/-!
# Fiber lifts of cyclic `K/N` schedules

A block `A` in a finite additive group `G` can be replicated over every
point of a second finite additive group `H`:

`fiberLift A = A × H`.

Translation in the `H` coordinate is then invisible.  The lift multiplies
both the block size and population size by `|H|`, preserves the number of
distinct phases, and multiplies the translation stabilizer by `|H|`.

This is the basic construction behind controlled `K/N` collapse.  Starting
from a primitive base block, a fiber of size `d` realizes collapse factor
exactly `d`.
-/

namespace GameTheory

namespace CyclicKofNFiberLift

open CyclicKofNArithmetic
open scoped Pointwise

noncomputable section

variable {G H : Type*}
variable [AddGroup G] [Fintype G] [DecidableEq G]
variable [AddGroup H] [Fintype H] [DecidableEq H]

/-- Replicate a base block over the whole fiber group. -/
def fiberLift (A : Finset G) : Finset (G × H) :=
  A ×ˢ Finset.univ

omit [AddGroup G] [Fintype G] [DecidableEq G] [AddGroup H] [DecidableEq H] in
/-- Fiber lifting multiplies block size by the fiber cardinality. -/
theorem card_fiberLift (A : Finset G) :
    (fiberLift (H := H) A).card = A.card * Fintype.card H := by
  classical
  simp [fiberLift, Finset.card_product]

omit [AddGroup G] [Fintype G] [DecidableEq G] [AddGroup H] [DecidableEq H] in
/-- The fiber-lift operation is injective. -/
theorem fiberLift_injective [AddGroup H] :
    Function.Injective (fiberLift (G := G) (H := H)) := by
  classical
  intro A B hAB
  ext x
  have hpoint := Finset.ext_iff.mp hAB (x, (0 : H))
  simpa [fiberLift] using hpoint

omit [Fintype G] in
/-- Translation of a fiber lift depends only on the base coordinate. -/
theorem vadd_fiberLift (g : G) (h : H) (A : Finset G) :
    (g, h) +ᵥ fiberLift (H := H) A = fiberLift (H := H) (g +ᵥ A) := by
  ext z
  rw [← Finset.neg_vadd_mem_iff]
  change ((-g + z.1, -h + z.2) ∈ fiberLift (H := H) A) ↔
    z ∈ fiberLift (H := H) (g +ᵥ A)
  simp only [fiberLift, Finset.mem_product, Finset.mem_univ, and_true]
  rw [← Finset.neg_vadd_mem_iff]
  rfl

omit [Fintype G] in
/-- The orbit of a fiber lift is precisely the injective image of the base
translation orbit. -/
theorem orbit_fiberLift (A : Finset G) :
    AddAction.orbit (G × H) (fiberLift (H := H) A) =
      fiberLift (H := H) '' AddAction.orbit G A := by
  ext C
  constructor
  · rintro ⟨⟨g, h⟩, rfl⟩
    refine ⟨g +ᵥ A, ⟨g, rfl⟩, ?_⟩
    exact (vadd_fiberLift g h A).symm
  · rintro ⟨B, ⟨g, hg⟩, rfl⟩
    refine ⟨(g, (0 : H)), ?_⟩
    change (g, (0 : H)) +ᵥ fiberLift (H := H) A = fiberLift (H := H) B
    rw [vadd_fiberLift]
    exact congrArg (fiberLift (H := H)) hg

/-- **Phase preservation.**  Fiber lifting does not change the number of
distinct translated phases. -/
theorem card_translationPhase_fiberLift (A : Finset G) :
    Fintype.card (TranslationPhase (fiberLift (H := H) A)) =
      Fintype.card (TranslationPhase A) := by
  rw [Set.fintypeCard_eq_ncard, Set.fintypeCard_eq_ncard,
    orbit_fiberLift]
  exact Set.ncard_image_of_injective _ fiberLift_injective

omit [AddGroup G] [DecidableEq G] [AddGroup H] [DecidableEq H] in
/-- The ambient product population has the expected cardinality. -/
theorem card_product_population :
    Fintype.card (G × H) = Fintype.card G * Fintype.card H :=
  Fintype.card_prod G H

/-- The stabilizer of the lift has cardinality equal to the base stabilizer
times the fiber cardinality. -/
theorem card_stabilizer_fiberLift (A : Finset G) :
    Fintype.card (AddAction.stabilizer (G × H) (fiberLift (H := H) A)) =
      Fintype.card (AddAction.stabilizer G A) * Fintype.card H := by
  let L := Fintype.card (TranslationPhase A)
  let d := Fintype.card (AddAction.stabilizer G A)
  let dLift := Fintype.card
    (AddAction.stabilizer (G × H) (fiberLift (H := H) A))
  have hL : 0 < L := Fintype.card_pos_iff.mpr inferInstance
  have hbase : L * d = Fintype.card G :=
    translationOrbit_mul_stabilizer A
  have hlift : L * dLift = Fintype.card G * Fintype.card H := by
    calc
      L * dLift =
          Fintype.card (TranslationPhase (fiberLift (H := H) A)) * dLift := by
        rw [card_translationPhase_fiberLift]
      _ = Fintype.card (G × H) :=
        translationOrbit_mul_stabilizer (fiberLift (H := H) A)
      _ = Fintype.card G * Fintype.card H := card_product_population
  have hscaled : L * dLift = L * (d * Fintype.card H) := by
    calc
      L * dLift = Fintype.card G * Fintype.card H := hlift
      _ = (L * d) * Fintype.card H := by rw [hbase]
      _ = L * (d * Fintype.card H) := by rw [mul_assoc]
  exact Nat.mul_left_cancel hL hscaled

/-- A primitive base block (trivial stabilizer) lifted over a fiber of size
`d` has collapse factor exactly `d`. -/
theorem card_stabilizer_fiberLift_of_primitive
    (A : Finset G)
    (hprimitive : Fintype.card (AddAction.stabilizer G A) = 1) :
    Fintype.card
        (AddAction.stabilizer (G × H) (fiberLift (H := H) A)) =
      Fintype.card H := by
  rw [card_stabilizer_fiberLift, hprimitive, one_mul]

/-- Parameter summary for a primitive fiber lift: block and population are
both scaled by `d`, the period is unchanged, and the stabilizer is `d`. -/
theorem primitive_fiberLift_parameters
    (A : Finset G)
    (hprimitive : Fintype.card (AddAction.stabilizer G A) = 1) :
    (fiberLift (H := H) A).card = A.card * Fintype.card H ∧
    Fintype.card (G × H) = Fintype.card G * Fintype.card H ∧
    Fintype.card (TranslationPhase (fiberLift (H := H) A)) =
      Fintype.card (TranslationPhase A) ∧
    Fintype.card
        (AddAction.stabilizer (G × H) (fiberLift (H := H) A)) =
      Fintype.card H := by
  exact ⟨card_fiberLift A, card_product_population,
    card_translationPhase_fiberLift A,
    card_stabilizer_fiberLift_of_primitive A hprimitive⟩

end

end CyclicKofNFiberLift

end GameTheory
