import UniformEquilibrium.Quitting.Paths.BehaviorFirstStoppingPairLaw
import UniformEquilibrium.Quitting.Paths.StoppingLawReconstruction

/-! # Actual profiles attaining the overlapping-pair boundary -/

noncomputable section

namespace GameTheory.OverlappingPairSharpProfiles

open Math.Probability Math.Probability.DiscreteHazard.StoppingLaw

/-- A complete clock stopping at `time` with probability `weight` and Never
otherwise. -/
def stopOrNever (time : ℕ) (weight : ℝ) (hzero : 0 ≤ weight)
    (hone : weight ≤ 1) : PMF (Option ℕ) :=
  (Math.ProbabilityMassFunction.bernoulliBool weight hzero hone).map
    (fun selected => if selected then some time else none)

variable (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
variable (weight : ℝ) (hzero : 0 ≤ weight) (hone : weight ≤ 1)

/-- Same-date clocks attaining adjacent-pair masses
`(weight²,(1-weight)²)`. -/
def sameDateLaws : Fin 4 → PMF (Option ℕ)
  | 0 => PMF.pure (some 0)
  | 1 => stopOrNever 0 weight hzero hone
  | 2 => stopOrNever 0 (1 - weight) (sub_nonneg.mpr hone)
      (by linarith)
  | 3 => PMF.pure none

/-- Actual behavioral realization of the same-date sharp clocks. -/
def sameDateProfile : (quittingGame reward).BehaviorProfile :=
  quittingStoppingLawProfile reward (sameDateLaws weight hzero hone)

def firstPair : {C : Finset (Fin 4) // C.Nonempty} :=
  ⟨{0, 1}, by simp⟩

def secondPair : {C : Finset (Fin 4) // C.Nonempty} :=
  ⟨{0, 2}, by simp⟩

theorem firstPairMass_sameDateProfile :
    quittingBehaviorExactFiniteFirstCoalitionMass
      (sameDateProfile reward weight hzero hone) firstPair = weight ^ 2 := by
  unfold quittingBehaviorExactFiniteFirstCoalitionMass
    exactFiniteFirstStoppingCoalitionMass
  simp_rw [sameDateProfile, quittingBehaviorStoppingLaws,
    quittingBehaviorStoppingLaw_stoppingLawProfile]
  rw [tsum_eq_single 0]
  · simp only [firstPair]
    have hout : ({0, 1} : Finset (Fin 4))ᶜ = {2, 3} := by decide
    rw [hout]
    simp [sameDateLaws, stopOrNever, finiteMass, survival,
      PMF.map_apply]
    ring_nf
  · intro time htime
    simp [sameDateLaws, firstPair, stopOrNever, finiteMass, PMF.map_apply,
      htime]

theorem secondPairMass_sameDateProfile :
    quittingBehaviorExactFiniteFirstCoalitionMass
      (sameDateProfile reward weight hzero hone) secondPair = (1 - weight) ^ 2 := by
  unfold quittingBehaviorExactFiniteFirstCoalitionMass
    exactFiniteFirstStoppingCoalitionMass
  simp_rw [sameDateProfile, quittingBehaviorStoppingLaws,
    quittingBehaviorStoppingLaw_stoppingLawProfile]
  rw [tsum_eq_single 0]
  · simp only [secondPair]
    have hout : ({0, 2} : Finset (Fin 4))ᶜ = {1, 3} := by decide
    rw [hout]
    simp [sameDateLaws, stopOrNever, finiteMass, survival,
      PMF.map_apply]
    ring_nf
  · intro time htime
    simp [sameDateLaws, secondPair, stopOrNever, finiteMass, PMF.map_apply,
      htime]

/-- A two-date clock stopping at date zero with probability `weight` and at
date two otherwise. -/
def stopAtZeroOrTwo (weight : ℝ) (hzero : 0 ≤ weight)
    (hone : weight ≤ 1) : PMF (Option ℕ) :=
  (Math.ProbabilityMassFunction.bernoulliBool weight hzero hone).map
    (fun selected => if selected then some 0 else some 2)

@[simp] theorem stopAtZeroOrTwo_zero_toReal :
    (stopAtZeroOrTwo weight hzero hone (some 0)).toReal = weight := by
  simp [stopAtZeroOrTwo, PMF.map_apply]

@[simp] theorem stopAtZeroOrTwo_two_toReal :
    (stopAtZeroOrTwo weight hzero hone (some 2)).toReal = 1 - weight := by
  simp [stopAtZeroOrTwo, PMF.map_apply]

@[simp] theorem stopAtZeroOrTwo_other_toReal
    (time : ℕ) (hzeroTime : time ≠ 0) (htwoTime : time ≠ 2) :
    (stopAtZeroOrTwo weight hzero hone (some time)).toReal = 0 := by
  simp [stopAtZeroOrTwo, PMF.map_apply, hzeroTime, htwoTime]

/-- Two-date clocks attaining the same boundary for disjoint pairs. -/
def disjointPairLaws : Fin 4 → PMF (Option ℕ)
  | 0 | 1 => stopAtZeroOrTwo weight hzero hone
  | 2 | 3 => PMF.pure (some 1)

def disjointPairProfile : (quittingGame reward).BehaviorProfile :=
  quittingStoppingLawProfile reward (disjointPairLaws weight hzero hone)

def thirdPair : {C : Finset (Fin 4) // C.Nonempty} :=
  ⟨{2, 3}, by simp⟩

theorem firstPairMass_disjointPairProfile :
    quittingBehaviorExactFiniteFirstCoalitionMass
      (disjointPairProfile reward weight hzero hone) firstPair = weight ^ 2 := by
  unfold quittingBehaviorExactFiniteFirstCoalitionMass
    exactFiniteFirstStoppingCoalitionMass
  simp_rw [disjointPairProfile, quittingBehaviorStoppingLaws,
    quittingBehaviorStoppingLaw_stoppingLawProfile]
  rw [tsum_eq_single 0]
  · simp only [firstPair]
    have hout : ({0, 1} : Finset (Fin 4))ᶜ = {2, 3} := by decide
    rw [hout]
    simp [disjointPairLaws, stopAtZeroOrTwo, finiteMass, survival, PMF.map_apply]
    ring_nf
  · intro time htime
    simp only [firstPair]
    have hout : ({0, 1} : Finset (Fin 4))ᶜ = {2, 3} := by decide
    rw [hout]
    by_cases honeTime : time = 1
    · subst time
      norm_num [disjointPairLaws, survival, finiteMass]
    · by_cases htwoTime : time = 2
      · subst time
        have hs : survival (PMF.pure (some 1) : PMF (Option ℕ)) 3 = 0 := by
          unfold survival
          rw [show Finset.range 3 = {0, 1, 2} by decide]
          norm_num [finiteMass]
        simp [disjointPairLaws, hs]
      · simp [disjointPairLaws, finiteMass, htime, htwoTime]

theorem thirdPairMass_disjointPairProfile :
    quittingBehaviorExactFiniteFirstCoalitionMass
      (disjointPairProfile reward weight hzero hone) thirdPair =
        (1 - weight) ^ 2 := by
  unfold quittingBehaviorExactFiniteFirstCoalitionMass
    exactFiniteFirstStoppingCoalitionMass
  simp_rw [disjointPairProfile, quittingBehaviorStoppingLaws,
    quittingBehaviorStoppingLaw_stoppingLawProfile]
  rw [tsum_eq_single 1]
  · simp only [thirdPair]
    have hout : ({2, 3} : Finset (Fin 4))ᶜ = {0, 1} := by decide
    rw [hout]
    have hsum : (∑ x ∈ Finset.range 2,
        ((stopAtZeroOrTwo weight hzero hone) (some x)).toReal) = weight := by
      rw [show Finset.range 2 = {0, 1} by decide]
      simp
    simp [disjointPairLaws, survival, finiteMass, hsum]
    ring_nf
  · intro time htime
    by_cases hzeroTime : time = 0
    · subst time
      simp [thirdPair, disjointPairLaws, finiteMass]
    · simp [thirdPair, disjointPairLaws, finiteMass, htime]

theorem actual_adjacent_and_disjoint_pair_boundary :
    (quittingBehaviorExactFiniteFirstCoalitionMass
        (sameDateProfile reward weight hzero hone) firstPair,
      quittingBehaviorExactFiniteFirstCoalitionMass
        (sameDateProfile reward weight hzero hone) secondPair) =
        (weight ^ 2, (1 - weight) ^ 2) ∧
      (quittingBehaviorExactFiniteFirstCoalitionMass
          (disjointPairProfile reward weight hzero hone) firstPair,
        quittingBehaviorExactFiniteFirstCoalitionMass
          (disjointPairProfile reward weight hzero hone) thirdPair) =
        (weight ^ 2, (1 - weight) ^ 2) := by
  simp [firstPairMass_sameDateProfile, secondPairMass_sameDateProfile,
    firstPairMass_disjointPairProfile, thirdPairMass_disjointPairProfile]

/-- Both actual constructions attain equality in the square-root law. -/
theorem actual_adjacent_and_disjoint_pair_sqrt_eq_one :
    (Real.sqrt (quittingBehaviorExactFiniteFirstCoalitionMass
        (sameDateProfile reward weight hzero hone) firstPair) +
      Real.sqrt (quittingBehaviorExactFiniteFirstCoalitionMass
        (sameDateProfile reward weight hzero hone) secondPair) = 1) ∧
    (Real.sqrt (quittingBehaviorExactFiniteFirstCoalitionMass
        (disjointPairProfile reward weight hzero hone) firstPair) +
      Real.sqrt (quittingBehaviorExactFiniteFirstCoalitionMass
        (disjointPairProfile reward weight hzero hone) thirdPair) = 1) := by
  rw [firstPairMass_sameDateProfile, secondPairMass_sameDateProfile,
    firstPairMass_disjointPairProfile, thirdPairMass_disjointPairProfile]
  simp only [Real.sqrt_sq_eq_abs, abs_of_nonneg hzero,
    abs_of_nonneg (sub_nonneg.mpr hone)]
  constructor <;> ring

end GameTheory.OverlappingPairSharpProfiles
