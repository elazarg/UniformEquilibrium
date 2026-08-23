/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Examples.SolanVieilleBoundarySoloHazardLedger

/-!
# Quantitative algebra for the Solan--Vieille solo-hazard obstruction

This file isolates the finite algebra in the explicit solo-hazard
exploitability floor.  It contains no compactness or path regularity.

* `atomicTailCharge_eq_quadraticCharge` is the path-independent potential
  identity for every finite atom word.
* `quadraticCharge_lower_bound` is the exact four-mass polygon estimate.
* `explicitFloor_of_smallErrorData` and `explicitFloor_of_errorData` consume
  the accounting output and give `1 ≤ 14 * E ^ 2 + 67 * E`.
* `one_over_sixtyEight_lt_of_explicitFloor` extracts the convenient rational
  strict floor.

The literal infinite-calendar producer is kept in
`SolanVieilleBoundarySoloHazardSemantic`.  Keeping that adapter separate
leaves the algebra reusable and makes its hypotheses explicit.
-/

noncomputable section

namespace GameTheory
namespace SolanVieilleBoundary
namespace SoloHazardLedger

abbrev PairMass := Player → ℝ

/-- Mass of the first partner pair. -/
def firstPairMass (mass : PairMass) : ℝ := mass 0 + mass 1

/-- Mass of the second partner pair. -/
def secondPairMass (mass : PairMass) : ℝ := mass 2 + mass 3

/-- The quadratic charge exposed by summing all four atomic friction lower
bounds. -/
def quadraticCharge (mass : PairMass) : ℝ :=
  3 * mass 0 * mass 1 + 3 * mass 2 * mass 3 -
    firstPairMass mass * secondPairMass mass

/-- Tail coefficient read by an atom owned by `owner`. -/
def tailCoefficient (mass : PairMass) (owner : Player) : ℝ :=
  3 * mass (partner owner) - oppositeMass mass owner

/-- Sum of atomic mass times the coefficient of the remaining mass, including
the current atom. -/
def atomicTailCharge : List Atom → ℝ
  | [] => 0
  | atom :: atoms =>
      tailCoefficient (ownerMass (atom :: atoms)) atom.owner * atom.mass +
        atomicTailCharge atoms

/-- **Finite path-independent potential identity.**  Ordering and hazards
cancel: only the four total owner masses remain. -/
theorem atomicTailCharge_eq_quadraticCharge (atoms : List Atom) :
    atomicTailCharge atoms = quadraticCharge (ownerMass atoms) := by
  induction atoms with
  | nil =>
      simp [atomicTailCharge, quadraticCharge, firstPairMass,
        secondPairMass, ownerMass]
  | cons atom atoms ih =>
      rcases atom with ⟨owner, hazard, mass⟩
      rw [atomicTailCharge, ih]
      fin_cases owner <;>
        simp [tailCoefficient, oppositeMass, totalMass, partner,
          quadraticCharge, firstPairMass, secondPairMass, ownerMass_cons,
          Fin.sum_univ_four] <;> ring

/-! ## Atomic friction domination -/

/-- Total own-clock friction, accumulated chronologically across all owners. -/
def totalAtomicFriction : List Atom → (Player → ℝ) → ℝ
  | [], _ => 0
  | atom :: atoms, gap =>
      gap atom.owner * atom.hazard +
        totalAtomicFriction atoms (fun who ↦ gapStep who atom (gap who))

/-- Pointwise conditions needed by the atomic friction estimate.  The tail
coefficient is bounded by the current deflated gap at each atom, and the
condition is transported through the literal gap update. -/
def AtomicTailFrictionAdmissible : List Atom → (Player → ℝ) → Prop
  | [], _ => True
  | atom :: atoms, gap =>
      0 ≤ atom.mass ∧ 0 ≤ atom.hazard ∧ atom.mass ≤ atom.hazard ∧
      0 ≤ gap atom.owner ∧
      tailCoefficient (ownerMass (atom :: atoms)) atom.owner ≤
        gap atom.owner ∧
      AtomicTailFrictionAdmissible atoms
        (fun who ↦ gapStep who atom (gap who))

/-- One coefficient-mass charge is bounded by its own-clock friction. -/
private theorem tailCoefficient_mul_mass_le_friction
    {coefficient gap mass hazard : ℝ}
    (hmass0 : 0 ≤ mass) (hhazard0 : 0 ≤ hazard)
    (hmass : mass ≤ hazard) (hgap0 : 0 ≤ gap)
    (hcoefficient : coefficient ≤ gap) :
    coefficient * mass ≤ gap * hazard := by
  by_cases hcoefficient0 : 0 ≤ coefficient
  · calc
      coefficient * mass ≤ gap * mass :=
        mul_le_mul_of_nonneg_right hcoefficient hmass0
      _ ≤ gap * hazard := mul_le_mul_of_nonneg_left hmass hgap0
  · have : coefficient ≤ 0 := le_of_not_ge hcoefficient0
    exact (mul_nonpos_of_nonpos_of_nonneg this hmass0).trans
      (mul_nonneg hgap0 hhazard0)

/-- **Atomic friction floor.**  The sum of the four signed tail charges is
bounded by total own-clock friction for every admissible finite word. -/
theorem atomicTailCharge_le_totalAtomicFriction
    (atoms : List Atom) (gap : Player → ℝ)
    (hadmissible : AtomicTailFrictionAdmissible atoms gap) :
    atomicTailCharge atoms ≤ totalAtomicFriction atoms gap := by
  induction atoms generalizing gap with
  | nil => simp [atomicTailCharge, totalAtomicFriction]
  | cons atom atoms ih =>
      rcases hadmissible with
        ⟨hmass0, hhazard0, hmass, hgap0, hcoefficient, htail⟩
      have hhead := tailCoefficient_mul_mass_le_friction hmass0 hhazard0
        hmass hgap0 hcoefficient
      have hrest := ih (fun who ↦ gapStep who atom (gap who)) htail
      simp only [atomicTailCharge, totalAtomicFriction]
      linarith

/-- The chronological total is exactly the sum of the four playerwise
friction ledgers already defined in the finite-prefix module. -/
theorem totalAtomicFriction_eq_sum_friction
    (atoms : List Atom) (gap : Player → ℝ) :
    totalAtomicFriction atoms gap = ∑ who, friction who atoms (gap who) := by
  induction atoms generalizing gap with
  | nil => simp [totalAtomicFriction, friction]
  | cons atom atoms ih =>
      rcases atom with ⟨owner, hazard, mass⟩
      rw [totalAtomicFriction, Fin.sum_univ_four]
      simp only [friction]
      have hih := ih (fun who ↦
        gapStep who ⟨owner, hazard, mass⟩ (gap who))
      rw [Fin.sum_univ_four] at hih
      rw [hih]
      fin_cases owner <;>
        simp [frictionStep] <;> ring

/-- Finite ledger form of the friction floor, directly reusing the canonical
playerwise `friction` definition. -/
theorem quadraticCharge_ownerMass_le_sum_friction
    (atoms : List Atom) (gap : Player → ℝ)
    (hadmissible : AtomicTailFrictionAdmissible atoms gap) :
    quadraticCharge (ownerMass atoms) ≤
      ∑ who, friction who atoms (gap who) := by
  rw [← atomicTailCharge_eq_quadraticCharge,
    ← totalAtomicFriction_eq_sum_friction]
  exact atomicTailCharge_le_totalAtomicFriction atoms gap hadmissible

/-! ## The mass polygon -/

/-- The product bound for one partner pair is exactly the product of its two
singleton-floor slacks. -/
private theorem pair_product_lower_bound
    {x y sigma : ℝ}
    (hxy : sigma ≤ x + 4 * y) (hyx : sigma ≤ y + 4 * x) :
    (sigma - (x + y)) * (4 * (x + y) - sigma) ≤ 9 * x * y := by
  have hprod : 0 ≤ (x + 4 * y - sigma) * (y + 4 * x - sigma) :=
    mul_nonneg (sub_nonneg.mpr hxy) (sub_nonneg.mpr hyx)
  nlinarith

/-- **Mass polygon estimate.**  Four singleton floors and total mass at most
one force the explicit quadratic lower bound. -/
theorem quadraticCharge_lower_bound
    (mass : PairMass) (E : ℝ)
    (hE0 : 0 ≤ E) (hEsmall : E ≤ 2 / 7)
    (hmass : ∀ who, 0 ≤ mass who)
    (htotal : totalMass mass ≤ 1)
    (hfloor : ∀ who, 1 - E ≤ prescribedPayoff mass who) :
    1 / 15 - 7 / 15 * E - 14 / 15 * E ^ 2 ≤ quadraticCharge mass := by
  let sigma : ℝ := 1 - E
  let a : ℝ := firstPairMass mass
  let b : ℝ := secondPairMass mass
  let t : ℝ := a + b
  have hsigma0 : 0 ≤ sigma := by dsimp [sigma]; nlinarith
  have hsigma1 : sigma ≤ 1 := by dsimp [sigma]; linarith
  have hsigmaLower : 5 / 7 ≤ sigma := by dsimp [sigma]; linarith
  have ha0 : 0 ≤ a := by
    dsimp [a, firstPairMass]
    exact add_nonneg (hmass 0) (hmass 1)
  have hb0 : 0 ≤ b := by
    dsimp [b, secondPairMass]
    exact add_nonneg (hmass 2) (hmass 3)
  have ht : t ≤ 1 := by
    have := htotal
    simp only [totalMass, Fin.sum_univ_four] at this
    dsimp [t, a, b, firstPairMass, secondPairMass]
    linarith
  have hfloor0 := hfloor 0
  have hfloor1 := hfloor 1
  have hfloor2 := hfloor 2
  have hfloor3 := hfloor 3
  simp [prescribedPayoff, partner] at hfloor0 hfloor1 hfloor2 hfloor3
  have hfloor0' : sigma ≤ mass 0 + 4 * mass 1 := by
    dsimp [sigma]
    linarith
  have hfloor1' : sigma ≤ mass 1 + 4 * mass 0 := by
    dsimp [sigma]
    linarith
  have hfloor2' : sigma ≤ mass 2 + 4 * mass 3 := by
    dsimp [sigma]
    linarith
  have hfloor3' : sigma ≤ mass 3 + 4 * mass 2 := by
    dsimp [sigma]
    linarith
  have haLower : 2 * sigma / 5 ≤ a := by
    dsimp [sigma, a, firstPairMass]
    linarith
  have hbLower : 2 * sigma / 5 ≤ b := by
    dsimp [sigma, b, secondPairMass]
    linarith
  have hpairA := pair_product_lower_bound hfloor0' hfloor1'
  have hpairB := pair_product_lower_bound hfloor2' hfloor3'
  have hab : (2 * sigma / 5) * (t - 2 * sigma / 5) ≤ a * b := by
    have hprod : 0 ≤ (a - 2 * sigma / 5) * (b - 2 * sigma / 5) :=
      mul_nonneg (sub_nonneg.mpr haLower) (sub_nonneg.mpr hbLower)
    dsimp [t]
    nlinarith
  have htLower : 4 * sigma / 5 ≤ t := by
    dsimp [t]
    linarith
  have hlinear : 0 ≤ 20 * (1 + t) - 35 * sigma := by
    nlinarith
  have hfactor : 0 ≤ (1 - t) * (20 * (1 + t) - 35 * sigma) :=
    mul_nonneg (sub_nonneg.mpr ht) hlinear
  dsimp [quadraticCharge, firstPairMass, secondPairMass, sigma, a, b, t]
    at hpairA hpairB hab hfactor ⊢
  nlinarith

/-! ## Consumers -/

/-- The quantitative floor in the nontrivial small-error regime. -/
theorem explicitFloor_of_smallErrorData
    (mass : PairMass) (E : ℝ)
    (hE0 : 0 ≤ E) (hEsmall : E ≤ 2 / 7)
    (hmass : ∀ who, 0 ≤ mass who)
    (htotal : totalMass mass ≤ 1)
    (hfloor : ∀ who, 1 - E ≤ prescribedPayoff mass who)
    (hcharge : quadraticCharge mass ≤ 4 * E) :
    1 ≤ 14 * E ^ 2 + 67 * E := by
  have hpolygon := quadraticCharge_lower_bound mass E hE0 hEsmall
    hmass htotal hfloor
  nlinarith

/-- Global form: only the small-error branch must supply mass data.  For
`E > 2/7`, the conclusion follows from the linear term alone. -/
theorem explicitFloor_of_errorData
    (E : ℝ) (hE0 : 0 ≤ E)
    (hdata : E ≤ 2 / 7 → ∃ mass : PairMass,
      (∀ who, 0 ≤ mass who) ∧ totalMass mass ≤ 1 ∧
      (∀ who, 1 - E ≤ prescribedPayoff mass who) ∧
      quadraticCharge mass ≤ 4 * E) :
    1 ≤ 14 * E ^ 2 + 67 * E := by
  by_cases hsmall : E ≤ 2 / 7
  · obtain ⟨mass, hmass, htotal, hfloor, hcharge⟩ := hdata hsmall
    exact explicitFloor_of_smallErrorData mass E hE0 hsmall hmass htotal
      hfloor hcharge
  · have : 2 / 7 < E := lt_of_not_ge hsmall
    nlinarith [sq_nonneg E]

/-- The explicit quadratic floor is strictly larger than `1/68`. -/
theorem one_over_sixtyEight_lt_of_explicitFloor
    {E : ℝ} (hE0 : 0 ≤ E)
    (hfloor : 1 ≤ 14 * E ^ 2 + 67 * E) :
    1 / 68 < E := by
  by_contra hnot
  have hupper : E ≤ 1 / 68 := le_of_not_gt hnot
  have hsquare : E ^ 2 ≤ E * (1 / 68) := by
    rw [pow_two]
    exact mul_le_mul_of_nonneg_left hupper hE0
  nlinarith

/-- Rational architectural floor directly from supplied solo mass data. -/
theorem one_over_sixtyEight_lt_of_errorData
    (E : ℝ) (hE0 : 0 ≤ E)
    (hdata : E ≤ 2 / 7 → ∃ mass : PairMass,
      (∀ who, 0 ≤ mass who) ∧ totalMass mass ≤ 1 ∧
      (∀ who, 1 - E ≤ prescribedPayoff mass who) ∧
      quadraticCharge mass ≤ 4 * E) :
    1 / 68 < E :=
  one_over_sixtyEight_lt_of_explicitFloor hE0
    (explicitFloor_of_errorData E hE0 hdata)

end SoloHazardLedger
end SolanVieilleBoundary
end GameTheory
