import MathUE.ProbabilityMassFunction.FiniteSupportSurvival
import UniformEquilibrium.Quitting.Paths.StoppingLawOperationalDistance

/-! # Survival beyond finite stopping-law support -/

noncomputable section

namespace GameTheory

open _root_.Math.Probability _root_.Math.Probability.DiscreteHazard

variable {ι : Type} [Fintype ι]

/-- Once every marginal has no finite atom after `cutoff`, joint live-spine
survival at a later date is exactly the product of the Never atoms. -/
theorem quittingJointSurvivalWeight_eq_prod_none_of_support_prefix
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (cutoff time : ℕ)
    (htime : cutoff < time)
    (hsupport : ∀ who,
      (quittingBehaviorStoppingLaw reward (profile who)).support ⊆
        ↑(stoppingLawFinitePrefix cutoff)) :
    quittingJointSurvivalWeight (quittingProfileLiveRoot reward profile) 0 time =
      ∏ who, (quittingBehaviorStoppingLaw reward (profile who) none).toReal := by
  rw [quittingJointSurvivalWeight_eq_prod]
  simp_rw [quittingStationaryContinueMass_eq_prod_continueProbability]
  rw [Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro who _
  rw [← quittingHazardSurvival_eq_prod]
  have hhazard :
      (fun x => quittingProfileLiveRoot reward profile (0 + x) who) =
        quittingBehaviorLiveHazard reward (profile who) := by
    funext x
    simp only [quittingProfileLiveRoot, quittingBehaviorLiveHazard]
    congr 2 <;> omega
  rw [hhazard]
  rw [← stoppingLawSurvival_quittingBehaviorStoppingLaw]
  exact stoppingLawSurvival_eq_none_of_support_prefix
    _ cutoff time htime (hsupport who)

end GameTheory
