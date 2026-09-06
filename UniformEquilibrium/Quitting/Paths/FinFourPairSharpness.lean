import MathUE.FinFourPairRelabel
import UniformEquilibrium.Quitting.Paths.FirstStoppingCoalitionRelabel
import UniformEquilibrium.Quitting.Paths.OverlappingPairSharpProfiles

/-! # Sharpness of every four-player pair-law projection -/


namespace GameTheory

open Math Math.Probability.DiscreteHazard.StoppingLaw
open OverlappingPairSharpProfiles

/-- Every ordered pair of distinct `K₄` edges has an actual behavioral
profile attaining the sharp boundary `(p²,(1-p)²)`. -/
theorem exists_actual_finFour_pairProjection_sharpProfile
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (first second : {C : Finset (Fin 4) // C.Nonempty})
    (hfirst : first.1.card = 2) (hsecond : second.1.card = 2)
    (hne : first ≠ second) (weight : ℝ)
    (hzero : 0 ≤ weight) (hone : weight ≤ 1) :
    ∃ profile : (quittingGame reward).BehaviorProfile,
      quittingBehaviorExactFiniteFirstCoalitionMass profile first = weight ^ 2 ∧
      quittingBehaviorExactFiniteFirstCoalitionMass profile second =
        (1 - weight) ^ 2 := by
  have hneVal : first.1 ≠ second.1 := by
    intro h
    exact hne (Subtype.ext h)
  obtain ⟨equiv, hadjacent | hdisjoint⟩ :=
    exists_finFour_pair_relabel first.1 second.1 hfirst hsecond hneVal
  · let laws := sameDateLaws weight hzero hone
    let profile := quittingStoppingLawProfile reward (fun who => laws (equiv.symm who))
    refine ⟨profile, ?_, ?_⟩
    · have hcoalition : relabelCoalition equiv firstPair = first :=
        Subtype.ext hadjacent.1
      rw [← hcoalition]
      rw [quittingBehaviorExactFiniteFirstCoalitionMass_relabel]
      rw [← firstPairMass_sameDateProfile reward weight hzero hone]
      simpa [laws, sameDateProfile, relabelCoalition] using
        (quittingBehaviorExactFiniteFirstCoalitionMass_relabel reward laws
          (Equiv.refl (Fin 4)) firstPair).symm
    · have hcoalition : relabelCoalition equiv secondPair = second :=
        Subtype.ext hadjacent.2
      rw [← hcoalition]
      rw [quittingBehaviorExactFiniteFirstCoalitionMass_relabel]
      rw [← secondPairMass_sameDateProfile reward weight hzero hone]
      simpa [laws, sameDateProfile, relabelCoalition] using
        (quittingBehaviorExactFiniteFirstCoalitionMass_relabel reward laws
          (Equiv.refl (Fin 4)) secondPair).symm
  · let laws := disjointPairLaws weight hzero hone
    let profile := quittingStoppingLawProfile reward (fun who => laws (equiv.symm who))
    refine ⟨profile, ?_, ?_⟩
    · have hcoalition : relabelCoalition equiv firstPair = first :=
        Subtype.ext hdisjoint.1
      rw [← hcoalition]
      rw [quittingBehaviorExactFiniteFirstCoalitionMass_relabel]
      rw [← firstPairMass_disjointPairProfile reward weight hzero hone]
      simpa [laws, disjointPairProfile, relabelCoalition] using
        (quittingBehaviorExactFiniteFirstCoalitionMass_relabel reward laws
          (Equiv.refl (Fin 4)) firstPair).symm
    · have hcoalition : relabelCoalition equiv thirdPair = second :=
        Subtype.ext hdisjoint.2
      rw [← hcoalition]
      rw [quittingBehaviorExactFiniteFirstCoalitionMass_relabel]
      rw [← thirdPairMass_disjointPairProfile reward weight hzero hone]
      simpa [laws, disjointPairProfile, relabelCoalition] using
        (quittingBehaviorExactFiniteFirstCoalitionMass_relabel reward laws
          (Equiv.refl (Fin 4)) thirdPair).symm

/-- Every one of the fifteen unordered edge projections, in either order, has an actual
behavioral profile attaining equality in the square-root law. -/
theorem exists_actual_finFour_pairProjection_sqrt_eq_one
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (first second : {C : Finset (Fin 4) // C.Nonempty})
    (hfirst : first.1.card = 2) (hsecond : second.1.card = 2)
    (hne : first ≠ second) (weight : ℝ)
    (hzero : 0 ≤ weight) (hone : weight ≤ 1) :
    ∃ profile : (quittingGame reward).BehaviorProfile,
      quittingBehaviorExactFiniteFirstCoalitionMass profile first = weight ^ 2 ∧
      quittingBehaviorExactFiniteFirstCoalitionMass profile second =
        (1 - weight) ^ 2 ∧
      Real.sqrt (quittingBehaviorExactFiniteFirstCoalitionMass profile first) +
        Real.sqrt (quittingBehaviorExactFiniteFirstCoalitionMass profile second) = 1 := by
  obtain ⟨profile, hfirstMass, hsecondMass⟩ :=
    exists_actual_finFour_pairProjection_sharpProfile reward first second
      hfirst hsecond hne weight hzero hone
  refine ⟨profile, hfirstMass, hsecondMass, ?_⟩
  rw [hfirstMass, hsecondMass]
  simp only [Real.sqrt_sq_eq_abs, abs_of_nonneg hzero,
    abs_of_nonneg (sub_nonneg.mpr hone)]
  ring

end GameTheory
