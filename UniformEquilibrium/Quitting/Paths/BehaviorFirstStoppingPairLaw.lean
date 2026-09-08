import MathUE.Probability.IndependentFirstStoppingPair
import UniformEquilibrium.Quitting.Paths.StageCoalitionStoppingLaw
import UniformEquilibrium.Quitting.Paths.CounterfactualStoppingLaw
import UniformEquilibrium.Quitting.Paths.ProfileNeverMass

/-! # Actual behavioral first-stopping pair laws

The exact finite first-quitter coalition masses of an executed quitting
profile are read from its complete live-spine stopping laws. The generic
independent-clock pair theorem then applies without reconstructing a profile
or restricting its behavioral strategies.
-/

noncomputable section

namespace GameTheory

open Math.Probability.DiscreteHazard.StoppingLaw

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- Actual probability that a specified nonempty coalition is exactly the
finite first-quitter coalition of an executed behavioral profile. -/
def quittingBehaviorExactFiniteFirstCoalitionMass
    (profile : (quittingGame reward).BehaviorProfile)
    (coalition : {C : Finset ι // C.Nonempty}) : ℝ :=
  exactFiniteFirstStoppingCoalitionMass
    (quittingBehaviorStoppingLaws reward profile) coalition

theorem quittingBehaviorExactFiniteFirstCoalitionMass_nonneg
    (profile : (quittingGame reward).BehaviorProfile)
    (coalition : {C : Finset ι // C.Nonempty}) :
    0 ≤ quittingBehaviorExactFiniteFirstCoalitionMass profile coalition := by
  exact exactFiniteFirstStoppingCoalitionMass_nonneg
    (quittingBehaviorStoppingLaws reward profile) coalition

/-- The stopping-clock formula is literally the existing executed terminal
outcome mass of the displayed coalition. -/
theorem quittingBehaviorExactFiniteFirstCoalitionMass_eq_terminalOutcomeMass
    (profile : (quittingGame reward).BehaviorProfile)
    (coalition : {C : Finset ι // C.Nonempty}) :
    quittingBehaviorExactFiniteFirstCoalitionMass profile coalition =
      quittingTerminalOutcomeMass reward profile (some coalition) := by
  rw [quittingTerminalOutcomeMass_eq_timeDisintegration]
  unfold quittingBehaviorExactFiniteFirstCoalitionMass
    exactFiniteFirstStoppingCoalitionMass
  apply tsum_congr
  intro time
  rw [quittingStageCoalitionMass_eq_stoppingLawProduct_mul_tailProduct]
  congr 1
  apply Finset.prod_congr rfl
  intro who _
  simpa only [quittingBehaviorStoppingLaws] using
    stoppingLawSurvival_quittingBehaviorStoppingLaw
      reward (profile who) (time + 1)

/-- Any two distinct two-player first-quitter coalitions of an actual
behavioral profile satisfy the sharp square-root law. This includes both
overlapping and disjoint pairs. -/
theorem quittingBehaviorFirstStoppingPairMass_sqrt_add_sqrt_le_one
    (profile : (quittingGame reward).BehaviorProfile)
    (firstCoalition secondCoalition : {C : Finset ι // C.Nonempty})
    (hfirstCard : firstCoalition.1.card = 2)
    (hsecondCard : secondCoalition.1.card = 2)
    (hne : firstCoalition ≠ secondCoalition) :
    Real.sqrt
          (quittingBehaviorExactFiniteFirstCoalitionMass profile firstCoalition) +
        Real.sqrt
          (quittingBehaviorExactFiniteFirstCoalitionMass profile secondCoalition) ≤ 1 := by
  exact sqrt_exactFiniteFirstStoppingPairMass_add_sqrt_le_one
    (quittingBehaviorStoppingLaws reward profile) firstCoalition secondCoalition
    hfirstCard hsecondCard hne

section FourPlayers

variable {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}

private def firstPair : {S : Finset (Fin 4) // S.Nonempty} :=
  ⟨{0, 1}, by simp⟩

private def secondPair : {S : Finset (Fin 4) // S.Nonempty} :=
  ⟨{2, 3}, by simp⟩

private theorem prod_zero_one (value : Fin 4 → ℝ) :
    ∏ who ∈ ({0, 1} : Finset (Fin 4)), value who = value 0 * value 1 := by
  rw [Finset.prod_insert (by decide), Finset.prod_singleton]

private theorem prod_two_three (value : Fin 4 → ℝ) :
    ∏ who ∈ ({2, 3} : Finset (Fin 4)), value who = value 2 * value 3 := by
  rw [Finset.prod_insert (by decide), Finset.prod_singleton]

private theorem exactFiniteFirstStoppingCoalitionMass_firstPair_eq
    (laws : Fin 4 → PMF (Option ℕ)) :
    exactFiniteFirstStoppingCoalitionMass laws firstPair =
      equalFirstSecondBeforeThirdFourthMass (laws 0) (laws 1) (laws 2) (laws 3) := by
  unfold exactFiniteFirstStoppingCoalitionMass
    equalFirstSecondBeforeThirdFourthMass firstPair
  apply tsum_congr
  intro time
  have hcomplement : ({0, 1} : Finset (Fin 4))ᶜ = {2, 3} := by decide
  rw [hcomplement]
  rw [prod_zero_one, prod_two_three]
  ring

private theorem exactFiniteFirstStoppingCoalitionMass_secondPair_eq
    (laws : Fin 4 → PMF (Option ℕ)) :
    exactFiniteFirstStoppingCoalitionMass laws secondPair =
      equalThirdFourthBeforeFirstSecondMass (laws 0) (laws 1) (laws 2) (laws 3) := by
  unfold exactFiniteFirstStoppingCoalitionMass
    equalThirdFourthBeforeFirstSecondMass secondPair
  apply tsum_congr
  intro time
  have hcomplement : ({2, 3} : Finset (Fin 4))ᶜ = {0, 1} := by decide
  rw [hcomplement]
  rw [prod_two_three, prod_zero_one]
  ring

/-- The two complementary pair masses and Never mass of every actual
four-player quitting profile obey the endpoint-retaining square-root law. -/
theorem quittingBehaviorTwoDisjointPairMasses_sqrt_sum_add_never_le_one
    (profile : (quittingGame reward).BehaviorProfile) :
    Real.sqrt (quittingBehaviorExactFiniteFirstCoalitionMass profile
          ⟨{0, 1}, by simp⟩) +
        Real.sqrt (quittingBehaviorExactFiniteFirstCoalitionMass profile
          ⟨{2, 3}, by simp⟩) +
        Real.sqrt (quittingTerminalOutcomeMass reward profile none) ≤ 1 := by
  let laws := quittingBehaviorStoppingLaws reward profile
  have h := twoDisjointFirstStoppingPairMasses_sqrt_sum_add_never_le_one
    (laws 0) (laws 1) (laws 2) (laws 3)
  rw [← exactFiniteFirstStoppingCoalitionMass_firstPair_eq laws,
    ← exactFiniteFirstStoppingCoalitionMass_secondPair_eq laws] at h
  change Real.sqrt (quittingBehaviorExactFiniteFirstCoalitionMass profile firstPair) +
      Real.sqrt (quittingBehaviorExactFiniteFirstCoalitionMass profile secondPair) +
      Real.sqrt ((laws 0 none).toReal * (laws 1 none).toReal *
        (laws 2 none).toReal * (laws 3 none).toReal) ≤ 1 at h
  have hproduct :
      (∏ who, (quittingBehaviorStoppingLaw reward (profile who) none).toReal) =
        (laws 0 none).toReal * (laws 1 none).toReal *
          (laws 2 none).toReal * (laws 3 none).toReal := by
    change (∏ who, (laws who none).toReal) = _
    norm_num [Fin.prod_univ_succ, laws]
    have hthree : Fin.succ (2 : Fin 3) = (3 : Fin 4) := by decide
    rw [hthree]
    ring
  rw [quittingTerminalOutcomeMass_none_eq_prod_stoppingLaw_none profile, hproduct]
  exact h

/-- The finite terminal mass outside the two complementary pair coalitions
is at least twice the geometric mean of their masses. -/
theorem quittingBehaviorTwoDisjointPairMasses_finiteLeftover_ge_two_sqrt_mul
    (profile : (quittingGame reward).BehaviorProfile) :
    2 * Real.sqrt
        (quittingBehaviorExactFiniteFirstCoalitionMass profile
            ⟨{0, 1}, by simp⟩ *
          quittingBehaviorExactFiniteFirstCoalitionMass profile
            ⟨{2, 3}, by simp⟩) ≤
      1 - quittingBehaviorExactFiniteFirstCoalitionMass profile
          ⟨{0, 1}, by simp⟩ -
        quittingBehaviorExactFiniteFirstCoalitionMass profile
          ⟨{2, 3}, by simp⟩ -
        quittingTerminalOutcomeMass reward profile none := by
  let laws := quittingBehaviorStoppingLaws reward profile
  have h := twoDisjointFirstStoppingPairMasses_finiteLeftover_ge_two_sqrt_mul
    (laws 0) (laws 1) (laws 2) (laws 3)
  rw [← exactFiniteFirstStoppingCoalitionMass_firstPair_eq laws,
    ← exactFiniteFirstStoppingCoalitionMass_secondPair_eq laws] at h
  change 2 * Real.sqrt
      (quittingBehaviorExactFiniteFirstCoalitionMass profile firstPair *
        quittingBehaviorExactFiniteFirstCoalitionMass profile secondPair) ≤
    1 - quittingBehaviorExactFiniteFirstCoalitionMass profile firstPair -
      quittingBehaviorExactFiniteFirstCoalitionMass profile secondPair -
      ((laws 0 none).toReal * (laws 1 none).toReal *
        (laws 2 none).toReal * (laws 3 none).toReal) at h
  have hproduct :
      (∏ who, (quittingBehaviorStoppingLaw reward (profile who) none).toReal) =
        (laws 0 none).toReal * (laws 1 none).toReal *
          (laws 2 none).toReal * (laws 3 none).toReal := by
    change (∏ who, (laws who none).toReal) = _
    norm_num [Fin.prod_univ_succ, laws]
    have hthree : Fin.succ (2 : Fin 3) = (3 : Fin 4) := by decide
    rw [hthree]
    ring
  rw [quittingTerminalOutcomeMass_none_eq_prod_stoppingLaw_none profile, hproduct]
  exact h

end FourPlayers

end GameTheory
