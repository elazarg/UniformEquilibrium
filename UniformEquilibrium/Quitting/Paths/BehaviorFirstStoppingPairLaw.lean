import MathUE.Probability.IndependentFirstStoppingPair
import UniformEquilibrium.Quitting.Paths.StageCoalitionStoppingLaw
import UniformEquilibrium.Quitting.Paths.CounterfactualStoppingLaw

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

end GameTheory
