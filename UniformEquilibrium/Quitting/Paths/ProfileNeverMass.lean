import UniformEquilibrium.Quitting.Paths.LiveRootSurvival
import UniformEquilibrium.Quitting.Paths.BehaviorStoppingLaw
import UniformEquilibrium.Quitting.Root.TerminalSemanticMoment

/-! # Joint Never mass of an actual behavioral profile -/

noncomputable section

namespace GameTheory

open Filter
open scoped Topology

variable {ι : Type} [Fintype ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}


/-- The limiting joint live mass is the product of the marginal Never masses. -/
theorem quittingLiveMassLimit_eq_prod_hazardNeverMass
    (profile : (quittingGame reward).BehaviorProfile) :
    quittingLiveMassLimit reward profile =
      ∏ player, quittingHazardNeverMass
        (quittingBehaviorLiveHazard reward (profile player)) := by
  let roots := quittingProfileLiveRoot reward profile
  have hfinite : ∀ cutoff,
      quittingLiveMass reward profile cutoff =
        ∏ player, quittingHazardSurvival
          (fun stage => roots stage player) cutoff := by
    intro cutoff
    rw [quittingLiveMass_eq_jointSurvivalWeight_profileLiveRoot]
    rw [quittingJointSurvivalWeight_eq_prod]
    simp_rw [quittingStationaryContinueMass_eq_prod_continueProbability]
    rw [Finset.prod_comm]
    apply Finset.prod_congr rfl
    intro player _
    rw [quittingHazardSurvival_eq_prod]
    simp [roots]
  have hlimit : Tendsto (fun cutoff =>
      ∏ player, quittingHazardSurvival
        (fun stage => roots stage player) cutoff) atTop
      (nhds (∏ player, quittingHazardNeverMass
        (fun stage => roots stage player))) :=
    tendsto_finsetProd Finset.univ fun player _ =>
      tendsto_quittingHazardSurvival_neverMass
        (fun stage => roots stage player)
  have hlive := tendsto_quittingLiveMass reward profile
  have hfiniteFunction : quittingLiveMass reward profile = fun cutoff =>
      ∏ player, quittingHazardSurvival
        (fun stage => roots stage player) cutoff := by
    funext cutoff
    exact hfinite cutoff
  rw [hfiniteFunction] at hlive
  have heq := tendsto_nhds_unique hlive hlimit
  refine heq.trans ?_
  apply Finset.prod_congr rfl
  intro player _
  congr 1

/-- An actual profile's terminal Never mass is the product of its marginal
stopping-law Never atoms. -/
theorem quittingTerminalOutcomeMass_none_eq_prod_stoppingLaw_none
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (profile : (quittingGame reward).BehaviorProfile) :
    quittingTerminalOutcomeMass reward profile none =
      ∏ who, (quittingBehaviorStoppingLaw reward (profile who) none).toReal := by
  rw [show quittingTerminalOutcomeMass reward profile none =
      quittingLiveMassLimit reward profile by rfl,
    quittingLiveMassLimit_eq_prod_hazardNeverMass]
  apply Finset.prod_congr rfl
  intro who _
  exact (quittingBehaviorStoppingLaw_none_toReal reward (profile who)).symm

end GameTheory
