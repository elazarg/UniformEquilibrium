import UniformEquilibrium.Quitting.Stationary.GuardedCrossedResponseRawMatrix
import MathUE.Finset.PowersetBernoulliWeight

/-! # Bernoulli coalition sums at a literal partner face -/

noncomputable section

namespace GameTheory

open Math.Finset

variable {ι : Type*} [DecidableEq ι]

private theorem insert_sdiff_of_not_mem
    (carrier subset : Finset ι) (partner : ι)
    (hpartner : partner ∉ carrier) (hsubset : subset ⊆ carrier) :
    insert partner carrier \ subset = insert partner (carrier \ subset) := by
  ext coordinate
  simp only [Finset.mem_sdiff, Finset.mem_insert]
  constructor
  · rintro ⟨heither, hnot⟩
    rcases heither with hpartnerEq | hcarrier
    · exact Or.inl hpartnerEq
    · exact Or.inr ⟨hcarrier, hnot⟩
  · rintro (hpartnerEq | ⟨hcarrier, hnot⟩)
    · subst coordinate
      exact ⟨Or.inl rfl, fun hmem => hpartner (hsubset hmem)⟩
    · exact ⟨Or.inr hcarrier, hnot⟩

private theorem insert_sdiff_insert
    (carrier subset : Finset ι) (partner : ι)
    (hpartner : partner ∉ carrier) :
    insert partner carrier \ insert partner subset = carrier \ subset := by
  ext coordinate
  by_cases hcoordinate : coordinate = partner
  · subst coordinate
    simp [hpartner]
  · simp [hcoordinate]

/-- A zero-rate partner contributes no Bernoulli mass to any coalition. -/
theorem quittingCrossed_sum_bernoulliWeight_partner_zero
    (carrier : Finset ι) (partner : ι) (hpartner : partner ∉ carrier)
    (hazard : ι → ℝ) (hzero : hazard partner = 0) (f : Finset ι → ℝ) :
    (∑ subset ∈ (insert partner carrier).powerset,
      bernoulliWeight hazard (insert partner carrier) subset * f subset) =
      ∑ subset ∈ carrier.powerset, bernoulliWeight hazard carrier subset * f subset := by
  rw [Finset.sum_powerset_insert hpartner]
  have hpositivePart :
      (∑ subset ∈ carrier.powerset,
        bernoulliWeight hazard (insert partner carrier) (insert partner subset) *
          f (insert partner subset)) = 0 := by
    apply Finset.sum_eq_zero
    intro subset hsubset
    have hsubsetCarrier := Finset.mem_powerset.mp hsubset
    have hpartnerSubset : partner ∉ subset := fun hmem => hpartner (hsubsetCarrier hmem)
    rw [bernoulliWeight, Finset.prod_insert hpartnerSubset, hzero]
    ring
  rw [hpositivePart, add_zero]
  apply Finset.sum_congr rfl
  intro subset hsubset
  have hsubsetCarrier := Finset.mem_powerset.mp hsubset
  have hpartnerSubset : partner ∉ subset := fun hmem => hpartner (hsubsetCarrier hmem)
  rw [bernoulliWeight, bernoulliWeight,
    insert_sdiff_of_not_mem carrier subset partner hpartner hsubsetCarrier,
    Finset.prod_insert]
  · simp [hzero]
  · exact fun hmem => hpartner (Finset.mem_sdiff.mp hmem).1

/-- A unit-rate partner belongs to every coalition with positive mass. -/
theorem quittingCrossed_sum_bernoulliWeight_partner_one
    (carrier : Finset ι) (partner : ι) (hpartner : partner ∉ carrier)
    (hazard : ι → ℝ) (hone : hazard partner = 1) (f : Finset ι → ℝ) :
    (∑ subset ∈ (insert partner carrier).powerset,
      bernoulliWeight hazard (insert partner carrier) subset * f subset) =
      ∑ subset ∈ carrier.powerset,
        bernoulliWeight hazard carrier subset * f (insert partner subset) := by
  rw [Finset.sum_powerset_insert hpartner]
  have hzeroPart :
      (∑ subset ∈ carrier.powerset,
        bernoulliWeight hazard (insert partner carrier) subset * f subset) = 0 := by
    apply Finset.sum_eq_zero
    intro subset hsubset
    have hsubsetCarrier := Finset.mem_powerset.mp hsubset
    rw [bernoulliWeight,
      insert_sdiff_of_not_mem carrier subset partner hpartner hsubsetCarrier,
      Finset.prod_insert]
    · simp [hone]
    · exact fun hmem => hpartner (Finset.mem_sdiff.mp hmem).1
  rw [hzeroPart, zero_add]
  apply Finset.sum_congr rfl
  intro subset hsubset
  have hsubsetCarrier := Finset.mem_powerset.mp hsubset
  have hpartnerSubset : partner ∉ subset := fun hmem => hpartner (hsubsetCarrier hmem)
  rw [bernoulliWeight, bernoulliWeight, Finset.prod_insert hpartnerSubset,
    insert_sdiff_insert carrier subset partner hpartner, hone, one_mul]

end GameTheory
