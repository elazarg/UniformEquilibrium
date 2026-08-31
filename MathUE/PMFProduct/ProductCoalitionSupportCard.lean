/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.PMFProduct.CoalitionMass

/-!
# Cardinality of an independent coalition law

The positive exact-coalition support is a translate of the powerset of the
coordinates at which both actions have positive mass.
-/

noncomputable section

namespace Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Exact coalitions having nonzero product mass. -/
def productCoalitionSupport (rates : ι → ℝ) : Finset (Finset ι) :=
  Finset.univ.filter fun coalition => coalitionMass rates coalition ≠ 0

/-- Coordinates whose Quit and Continue factors are both nonzero. -/
def productCoalitionFlexibleCoordinates (rates : ι → ℝ) : Finset ι :=
  Finset.univ.filter fun who => rates who ≠ 0 ∧ 1 - rates who ≠ 0

/-- Coordinates that occur in every positive exact coalition. -/
def productCoalitionForcedCoordinates (rates : ι → ℝ) : Finset ι :=
  Finset.univ.filter fun who => 1 - rates who = 0

private theorem coalitionMass_ne_zero_iff
    (rates : ι → ℝ) (coalition : Finset ι) :
    coalitionMass rates coalition ≠ 0 ↔
      (∀ who ∈ coalition, rates who ≠ 0) ∧
      ∀ who ∈ coalitionᶜ, 1 - rates who ≠ 0 := by
  simp only [coalitionMass, mul_ne_zero_iff, Finset.prod_ne_zero_iff]

omit [DecidableEq ι] in
private theorem flexible_disjoint_forced (rates : ι → ℝ) :
    Disjoint (productCoalitionFlexibleCoordinates rates)
      (productCoalitionForcedCoordinates rates) := by
  rw [Finset.disjoint_left]
  intro who hflex hforced
  exact (Finset.mem_filter.mp hflex).2.2 (Finset.mem_filter.mp hforced).2

private theorem productCoalitionSupport_eq_image_powerset
    (rates : ι → ℝ) :
    productCoalitionSupport rates =
      (productCoalitionFlexibleCoordinates rates).powerset.image
        (fun optional => productCoalitionForcedCoordinates rates ∪ optional) := by
  ext coalition
  simp only [productCoalitionSupport, Finset.mem_filter, Finset.mem_univ,
    true_and, Finset.mem_image, Finset.mem_powerset]
  constructor
  · intro hmass
    rw [coalitionMass_ne_zero_iff] at hmass
    let optional := coalition \ productCoalitionForcedCoordinates rates
    refine ⟨optional, ?_, ?_⟩
    · intro who hwho
      have hcoalition : who ∈ coalition := (Finset.mem_sdiff.mp hwho).1
      have hnotForced : who ∉ productCoalitionForcedCoordinates rates :=
        (Finset.mem_sdiff.mp hwho).2
      simp only [productCoalitionFlexibleCoordinates, Finset.mem_filter,
        Finset.mem_univ, true_and]
      refine ⟨hmass.1 who hcoalition, ?_⟩
      simpa [productCoalitionForcedCoordinates] using hnotForced
    · apply Finset.ext
      intro who
      by_cases hforced : who ∈ productCoalitionForcedCoordinates rates
      · have hwho : who ∈ coalition := by
          by_contra hnot
          have hcomplement : who ∈ coalitionᶜ := by simpa using hnot
          exact (hmass.2 who hcomplement)
            ((Finset.mem_filter.mp hforced).2)
        simp [hforced, hwho]
      · simp [optional, hforced]
  · rintro ⟨optional, hoptional, rfl⟩
    rw [coalitionMass_ne_zero_iff]
    constructor
    · intro who hwho
      rcases Finset.mem_union.mp hwho with hforced | hflex
      · have hcontinue := (Finset.mem_filter.mp hforced).2
        linarith
      · exact (Finset.mem_filter.mp (hoptional hflex)).2.1
    · intro who hwho
      have hnotForced : who ∉ productCoalitionForcedCoordinates rates := by
        intro hforced
        have hnotUnion :
            who ∉ productCoalitionForcedCoordinates rates ∪ optional := by
          simpa using hwho
        exact hnotUnion (Finset.mem_union_left optional hforced)
      by_contra hcontinue
      exact hnotForced (by simp [productCoalitionForcedCoordinates, hcontinue])

/-- The number of positive exact coalitions is a power of two, with exponent
the number of coordinates at which both actions have nonzero mass. -/
theorem card_productCoalitionSupport
    (rates : ι → ℝ) :
    (productCoalitionSupport rates).card =
      2 ^ (productCoalitionFlexibleCoordinates rates).card := by
  rw [productCoalitionSupport_eq_image_powerset]
  have hinjective : Set.InjOn
      (fun optional : Finset ι =>
        productCoalitionForcedCoordinates rates ∪ optional)
      (productCoalitionFlexibleCoordinates rates).powerset := by
    intro left hleft right hright heq
    apply Finset.ext
    intro who
    have hleftSubset := Finset.mem_powerset.mp hleft
    have hrightSubset := Finset.mem_powerset.mp hright
    have hnotForced : who ∈ left ∨ who ∈ right →
        who ∉ productCoalitionForcedCoordinates rates := by
      intro hmem hforced
      have hflex : who ∈ productCoalitionFlexibleCoordinates rates :=
        hmem.elim (fun h => hleftSubset h) (fun h => hrightSubset h)
      exact Finset.disjoint_left.mp (flexible_disjoint_forced rates)
        hflex hforced
    constructor
    · intro hwho
      have hunion : who ∈ productCoalitionForcedCoordinates rates ∪ right := by
        change productCoalitionForcedCoordinates rates ∪ left =
          productCoalitionForcedCoordinates rates ∪ right at heq
        rw [← heq]
        exact Finset.mem_union_right _ hwho
      rcases Finset.mem_union.mp hunion with hforced | hrightMem
      · exact False.elim ((hnotForced (Or.inl hwho)) hforced)
      · exact hrightMem
    · intro hwho
      have hunion : who ∈ productCoalitionForcedCoordinates rates ∪ left := by
        change productCoalitionForcedCoordinates rates ∪ left =
          productCoalitionForcedCoordinates rates ∪ right at heq
        rw [heq]
        exact Finset.mem_union_right _ hwho
      rcases Finset.mem_union.mp hunion with hforced | hleftMem
      · exact False.elim ((hnotForced (Or.inr hwho)) hforced)
      · exact hleftMem
  rw [Finset.card_image_iff.mpr hinjective, Finset.card_powerset]

end Math.PMFProduct
