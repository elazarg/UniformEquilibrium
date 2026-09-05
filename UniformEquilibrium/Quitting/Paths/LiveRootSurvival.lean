import UniformEquilibrium.Quitting.Root.SequencePayoff
import UniformEquilibrium.Quitting.Boundary.Repair.JointComplementarity
import UniformEquilibrium.Quitting.Stationary.LiveMass

/-! # Live probability and survival of the canonical root sequence -/

noncomputable section

namespace GameTheory

variable {ι : Type} [Fintype ι]

/-- The live probability of an arbitrary profile is the joint survival of
the root word read on its canonical live histories. -/
theorem quittingLiveMass_eq_jointSurvivalWeight_profileLiveRoot
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) :
    ∀ stage,
      quittingLiveMass reward profile stage =
        quittingJointSurvivalWeight
          (quittingProfileLiveRoot reward profile) 0 stage := by
  classical
  intro stage
  induction stage with
  | zero => simp [quittingJointSurvivalWeight, quittingFiniteContinueWeight]
  | succ stage ih =>
      rw [quittingLiveMass_succ, quittingJointSurvivalWeight_succ, ih]
      congr 1
      rw [quittingJointContinueMass_eq_product,
        quittingStationaryContinueMass_eq_prod_continueProbability]
      apply Finset.prod_congr rfl
      intro player _
      unfold quittingProfileLiveRoot
      rw [Nat.zero_add]
      rfl

end GameTheory
