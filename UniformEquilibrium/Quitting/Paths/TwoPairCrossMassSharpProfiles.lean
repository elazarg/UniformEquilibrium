import UniformEquilibrium.Quitting.Paths.OverlappingPairSharpProfiles
import UniformEquilibrium.Quitting.Paths.TwoPairCrossMassDeterminant

/-! # Literal independent laws attaining the cross-mass determinant

Players 0 and 1 stop at date zero or Never. Players 2 and 3 stop surely at
date one. The exact same laws and their actual behavioral realization attain
both boundaries, including weights zero and one.
-/

noncomputable section

namespace GameTheory.TwoPairCrossMassSharpProfiles

open _root_.Math.Probability _root_.Math.Probability.DiscreteHazard.StoppingLaw
open OverlappingPairSharpProfiles

variable (weight : ℝ) (hzero : 0 ≤ weight) (hone : weight ≤ 1)

/-- These are the literal date-zero-or-Never laws, not date-zero-or-two laws. -/
def laws : Fin 4 → PMF (Option ℕ) :=
  ![stopOrNever 0 weight hzero hone, stopOrNever 0 weight hzero hone,
    PMF.pure (some 1), PMF.pure (some 1)]

theorem laws_date_zero (who : Fin 4) :
    (laws weight hzero hone who (some 0)).toReal =
      if who < 2 then weight else 0 := by
  fin_cases who <;> simp [laws, stopOrNever, PMF.map_apply]

theorem laws_date_one (who : Fin 4) :
    (laws weight hzero hone who (some 1)).toReal =
      if who < 2 then 0 else 1 := by
  fin_cases who <;> simp [laws, stopOrNever, PMF.map_apply]

theorem laws_never (who : Fin 4) :
    (laws weight hzero hone who none).toReal =
      if who < 2 then 1 - weight else 0 := by
  fin_cases who <;> simp [laws, stopOrNever, PMF.map_apply]

private theorem early_finiteMass_other (time : ℕ) (htime : time ≠ 0) :
    finiteMass (stopOrNever 0 weight hzero hone) time = 0 := by
  simp [finiteMass, stopOrNever, PMF.map_apply, htime]

private theorem early_survival_succ (time : ℕ) :
    survival (stopOrNever 0 weight hzero hone) (time + 1) = 1 - weight := by
  unfold survival
  have hsum : (∑ date ∈ Finset.range (time + 1),
      finiteMass (stopOrNever 0 weight hzero hone) date) = weight := by
    rw [Finset.sum_eq_single 0]
    · simp [finiteMass, stopOrNever, PMF.map_apply]
    · intro date _ hdate
      exact early_finiteMass_other weight hzero hone date hdate
    · simp
  rw [hsum]

theorem firstPair_mass :
    exactFiniteFirstStoppingCoalitionMass (laws weight hzero hone)
      ⟨{0, 1}, by simp⟩ = weight ^ 2 := by
  unfold exactFiniteFirstStoppingCoalitionMass
  rw [tsum_eq_single 0]
  · have hcomplement : ({0, 1} : Finset (Fin 4))ᶜ = {2, 3} := by decide
    rw [hcomplement]
    simp [laws, finiteMass, survival, stopOrNever, PMF.map_apply]
    ring
  · intro time htime
    simp [laws, finiteMass, stopOrNever, PMF.map_apply, htime]

theorem secondPair_mass :
    exactFiniteFirstStoppingCoalitionMass (laws weight hzero hone)
      ⟨{2, 3}, by simp⟩ = (1 - weight) ^ 2 := by
  unfold exactFiniteFirstStoppingCoalitionMass
  rw [tsum_eq_single 1]
  · have hcomplement : ({2, 3} : Finset (Fin 4))ᶜ = {0, 1} := by decide
    rw [hcomplement]
    simp [laws, finiteMass, early_survival_succ]
    ring
  · intro time htime
    simp [laws, finiteMass, htime]

theorem zeroSingleton_mass :
    exactFiniteFirstStoppingCoalitionMass (laws weight hzero hone)
      ⟨{0}, by simp⟩ = weight * (1 - weight) := by
  unfold exactFiniteFirstStoppingCoalitionMass
  rw [tsum_eq_single 0]
  · have hcomplement : ({0} : Finset (Fin 4))ᶜ = {1, 2, 3} := by decide
    rw [hcomplement]
    simp [laws, finiteMass, survival, stopOrNever, PMF.map_apply]
  · intro time htime
    simp [laws, finiteMass, stopOrNever, PMF.map_apply, htime]

theorem oneSingleton_mass :
    exactFiniteFirstStoppingCoalitionMass (laws weight hzero hone)
      ⟨{1}, by simp⟩ = weight * (1 - weight) := by
  unfold exactFiniteFirstStoppingCoalitionMass
  rw [tsum_eq_single 0]
  · have hcomplement : ({1} : Finset (Fin 4))ᶜ = {0, 2, 3} := by decide
    rw [hcomplement]
    simp [laws, finiteMass, survival, stopOrNever, PMF.map_apply]
  · intro time htime
    simp [laws, finiteMass, stopOrNever, PMF.map_apply, htime]

theorem twoSingleton_mass :
    exactFiniteFirstStoppingCoalitionMass (laws weight hzero hone)
      ⟨{2}, by simp⟩ = 0 := by
  unfold exactFiniteFirstStoppingCoalitionMass
  apply (tsum_congr ?_).trans (tsum_zero : (∑' _ : ℕ, (0 : ℝ)) = 0)
  intro time
  by_cases htime : time = 1
  · subst time
    have hcomplement : ({2} : Finset (Fin 4))ᶜ = {0, 1, 3} := by decide
    rw [hcomplement]
    norm_num [laws, finiteMass, survival, Finset.sum_range_succ]
  · simp [laws, finiteMass, htime]

theorem threeSingleton_mass :
    exactFiniteFirstStoppingCoalitionMass (laws weight hzero hone)
      ⟨{3}, by simp⟩ = 0 := by
  unfold exactFiniteFirstStoppingCoalitionMass
  apply (tsum_congr ?_).trans (tsum_zero : (∑' _ : ℕ, (0 : ℝ)) = 0)
  intro time
  by_cases htime : time = 1
  · subst time
    have hcomplement : ({3} : Finset (Fin 4))ᶜ = {0, 1, 2} := by decide
    rw [hcomplement]
    norm_num [laws, finiteMass, survival, Finset.sum_range_succ]
  · simp [laws, finiteMass, htime]

theorem positiveCrossPair_mass :
    exactFiniteFirstStoppingCoalitionMass (laws weight hzero hone)
      ⟨{0, 3}, by simp⟩ = 0 := by
  unfold exactFiniteFirstStoppingCoalitionMass
  apply (tsum_congr ?_).trans (tsum_zero : (∑' _ : ℕ, (0 : ℝ)) = 0)
  intro time
  by_cases htime : time = 0
  · subst time
    simp [laws, finiteMass]
  · simp [laws, finiteMass, stopOrNever, PMF.map_apply, htime]

theorem negativeCrossPair_mass :
    exactFiniteFirstStoppingCoalitionMass (laws weight hzero hone)
      ⟨{1, 2}, by simp⟩ = 0 := by
  unfold exactFiniteFirstStoppingCoalitionMass
  apply (tsum_congr ?_).trans (tsum_zero : (∑' _ : ℕ, (0 : ℝ)) = 0)
  intro time
  by_cases htime : time = 0
  · subst time
    simp [laws, finiteMass]
  · simp [laws, finiteMass, stopOrNever, PMF.map_apply, htime]

/-- The plus side is exactly the same three atoms used in the canonical determinant. -/
def positiveCrossMass (source : Fin 4 → PMF (Option ℕ)) : ℝ :=
  exactFiniteFirstStoppingCoalitionMass source ⟨{0}, by simp⟩ +
    exactFiniteFirstStoppingCoalitionMass source ⟨{3}, by simp⟩ +
    exactFiniteFirstStoppingCoalitionMass source ⟨{0, 3}, by simp⟩

def negativeCrossMass (source : Fin 4 → PMF (Option ℕ)) : ℝ :=
  exactFiniteFirstStoppingCoalitionMass source ⟨{1}, by simp⟩ +
    exactFiniteFirstStoppingCoalitionMass source ⟨{2}, by simp⟩ +
    exactFiniteFirstStoppingCoalitionMass source ⟨{1, 2}, by simp⟩

theorem positiveCrossMass_eq :
    positiveCrossMass (laws weight hzero hone) = weight * (1 - weight) := by
  simp only [positiveCrossMass, zeroSingleton_mass, threeSingleton_mass,
    positiveCrossPair_mass, add_zero]

theorem negativeCrossMass_eq :
    negativeCrossMass (laws weight hzero hone) = weight * (1 - weight) := by
  simp only [negativeCrossMass, oneSingleton_mass, twoSingleton_mass,
    negativeCrossPair_mass, add_zero]

theorem determinant_eq :
    exactFiniteFirstStoppingCoalitionMass (laws weight hzero hone)
        ⟨{0, 1}, by simp⟩ *
      exactFiniteFirstStoppingCoalitionMass (laws weight hzero hone)
        ⟨{2, 3}, by simp⟩ =
      positiveCrossMass (laws weight hzero hone) *
        negativeCrossMass (laws weight hzero hone) := by
  rw [firstPair_mass, secondPair_mass, positiveCrossMass_eq, negativeCrossMass_eq]
  ring

theorem squareRoot_boundary :
    Real.sqrt (exactFiniteFirstStoppingCoalitionMass (laws weight hzero hone)
        ⟨{0, 1}, by simp⟩) +
      Real.sqrt (exactFiniteFirstStoppingCoalitionMass (laws weight hzero hone)
        ⟨{2, 3}, by simp⟩) = 1 := by
  rw [firstPair_mass, secondPair_mass, Real.sqrt_sq_eq_abs, Real.sqrt_sq_eq_abs,
    abs_of_nonneg hzero, abs_of_nonneg (sub_nonneg.mpr hone)]
  ring

variable (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))

/-- Actual independent behavioral realization of precisely the displayed laws. -/
def profile : (quittingGame reward).BehaviorProfile :=
  quittingStoppingLawProfile reward (laws weight hzero hone)

theorem profile_stoppingLaw (who : Fin 4) :
    quittingBehaviorStoppingLaw reward (profile weight hzero hone reward who) =
      laws weight hzero hone who :=
  quittingBehaviorStoppingLaw_stoppingLawProfile reward (laws weight hzero hone) who

theorem profile_coalitionMass
    (coalition : {S : Finset (Fin 4) // S.Nonempty}) :
    quittingBehaviorExactFiniteFirstCoalitionMass
      (profile weight hzero hone reward) coalition =
      exactFiniteFirstStoppingCoalitionMass (laws weight hzero hone) coalition := by
  unfold quittingBehaviorExactFiniteFirstCoalitionMass quittingBehaviorStoppingLaws
  simp_rw [profile_stoppingLaw]

/-- All four masses of one actual original-game profile, including endpoint weights. -/
theorem actual_masses :
    quittingBehaviorExactFiniteFirstCoalitionMass
        (profile weight hzero hone reward) ⟨{0, 1}, by simp⟩ = weight ^ 2 ∧
      quittingBehaviorExactFiniteFirstCoalitionMass
        (profile weight hzero hone reward) ⟨{2, 3}, by simp⟩ = (1 - weight) ^ 2 ∧
      positiveCrossMass (quittingBehaviorStoppingLaws reward
        (profile weight hzero hone reward)) = weight * (1 - weight) ∧
      negativeCrossMass (quittingBehaviorStoppingLaws reward
        (profile weight hzero hone reward)) = weight * (1 - weight) := by
  have hlaws : quittingBehaviorStoppingLaws reward
      (profile weight hzero hone reward) = laws weight hzero hone := by
    funext who
    exact profile_stoppingLaw weight hzero hone reward who
  rw [profile_coalitionMass, profile_coalitionMass, hlaws]
  exact ⟨firstPair_mass weight hzero hone, secondPair_mass weight hzero hone,
    positiveCrossMass_eq weight hzero hone, negativeCrossMass_eq weight hzero hone⟩

theorem actual_determinant_eq :
    quittingBehaviorExactFiniteFirstCoalitionMass
        (profile weight hzero hone reward) ⟨{0, 1}, by simp⟩ *
      quittingBehaviorExactFiniteFirstCoalitionMass
        (profile weight hzero hone reward) ⟨{2, 3}, by simp⟩ =
      positiveCrossMass (quittingBehaviorStoppingLaws reward
        (profile weight hzero hone reward)) *
      negativeCrossMass (quittingBehaviorStoppingLaws reward
        (profile weight hzero hone reward)) := by
  have h := actual_masses weight hzero hone reward
  rw [h.1, h.2.1, h.2.2.1, h.2.2.2]
  ring

theorem actual_squareRoot_boundary :
    Real.sqrt (quittingBehaviorExactFiniteFirstCoalitionMass
        (profile weight hzero hone reward) ⟨{0, 1}, by simp⟩) +
      Real.sqrt (quittingBehaviorExactFiniteFirstCoalitionMass
        (profile weight hzero hone reward) ⟨{2, 3}, by simp⟩) = 1 := by
  rw [profile_coalitionMass, profile_coalitionMass]
  exact squareRoot_boundary weight hzero hone

theorem actual_neverMass :
    quittingTerminalOutcomeMass reward (profile weight hzero hone reward) none = 0 := by
  rw [quittingTerminalOutcomeMass_none_eq_prod_stoppingLaw_none]
  apply Finset.prod_eq_zero (Finset.mem_univ (2 : Fin 4))
  rw [profile_stoppingLaw, laws_never]
  norm_num

/-- The literal all-Never case needs no positivity or absorption premise. -/
def allNeverLaws : Fin 4 → PMF (Option ℕ) := fun _ => PMF.pure none

theorem allNever_coalitionMass
    (coalition : {S : Finset (Fin 4) // S.Nonempty}) :
    exactFiniteFirstStoppingCoalitionMass allNeverLaws coalition = 0 := by
  unfold exactFiniteFirstStoppingCoalitionMass
  apply (tsum_congr ?_).trans (tsum_zero : (∑' _ : ℕ, (0 : ℝ)) = 0)
  intro time
  have hproduct :
      (∏ who ∈ coalition.1, finiteMass (allNeverLaws who) time) = 0 := by
    apply Finset.prod_eq_zero coalition.2.choose_spec
    simp [allNeverLaws, finiteMass]
  rw [hproduct, zero_mul]

theorem allNever_crossMasses :
    positiveCrossMass allNeverLaws = 0 ∧ negativeCrossMass allNeverLaws = 0 := by
  simp only [positiveCrossMass, negativeCrossMass, allNever_coalitionMass, add_zero, and_self]

theorem allNever_determinant_eq :
    exactFiniteFirstStoppingCoalitionMass allNeverLaws ⟨{0, 1}, by simp⟩ *
      exactFiniteFirstStoppingCoalitionMass allNeverLaws ⟨{2, 3}, by simp⟩ =
      positiveCrossMass allNeverLaws * negativeCrossMass allNeverLaws := by
  rw [allNever_coalitionMass, allNever_coalitionMass,
    allNever_crossMasses.1, allNever_crossMasses.2]

def allNeverProfile : (quittingGame reward).BehaviorProfile :=
  quittingStoppingLawProfile reward allNeverLaws

theorem actual_allNever_coalitionMass
    (coalition : {S : Finset (Fin 4) // S.Nonempty}) :
    quittingBehaviorExactFiniteFirstCoalitionMass (allNeverProfile reward) coalition = 0 := by
  unfold quittingBehaviorExactFiniteFirstCoalitionMass quittingBehaviorStoppingLaws
    allNeverProfile
  simp_rw [quittingBehaviorStoppingLaw_stoppingLawProfile]
  exact allNever_coalitionMass coalition

theorem actual_allNever_neverMass :
    quittingTerminalOutcomeMass reward (allNeverProfile reward) none = 1 := by
  rw [quittingTerminalOutcomeMass_none_eq_prod_stoppingLaw_none]
  simp [allNeverProfile, quittingBehaviorStoppingLaw_stoppingLawProfile, allNeverLaws]

end GameTheory.TwoPairCrossMassSharpProfiles
