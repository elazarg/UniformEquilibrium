import UniformEquilibrium.Quitting.Paths.LiveRootSurvival
import UniformEquilibrium.Quitting.Paths.BehaviorStoppingLaw

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

end GameTheory
