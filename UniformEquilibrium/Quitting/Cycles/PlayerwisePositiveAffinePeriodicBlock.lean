import UniformEquilibrium.Quitting.Cycles.BlockPeriodicProfile
import UniformEquilibrium.Quitting.Root.PlayerwiseAffineReward

/-!
# Playerwise positive-affine transport of periodic quitting blocks

Each player's terminal rewards may be rescaled by an independent positive
factor and translated by an independent constant.  An absorbing exact cyclic
data set survives this transformation with the same root cycle.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.ProbabilityMassFunction

variable {Player : Type} [Fintype Player] [DecidableEq Player]
variable {K : ℕ}


/-- The cyclic terminal value transforms by the same independent affine maps
when every player faces strict fixed-opponent contraction. -/
theorem quittingCyclicTerminalValue_playerwiseAffine
    (reward : {coalition : Finset Player // coalition.Nonempty} → Payoff Player)
    (scale shift : Payoff Player) (cycle : Fin K → Player → PMF Bool)
    (hcontracts : ∀ who,
      (∏ phase : Fin K,
        quittingStationaryFixedOpponentsContinueMass (cycle phase) who) < 1) :
    quittingCyclicTerminalValue
        (quittingPlayerwiseAffineReward reward scale shift) cycle =
      fun phase => quittingPlayerwiseAffinePayoff scale shift
        (quittingCyclicTerminalValue reward cycle phase) := by
  symm
  apply eq_quittingCyclicTerminalValue_of_rootSuccessorPayoff
    (quittingPlayerwiseAffineReward reward scale shift) cycle
  · intro phase
    funext who
    rw [quittingRootSuccessorPayoff_playerwiseAffine]
    simp only [quittingPlayerwiseAffinePayoff]
    rw [quittingCyclicTerminalValue_eq_rootSuccessorPayoff reward cycle phase]
  · exact hcontracts

/-- Contracting exact periodic Nash--Bellman data yield an unrestricted
behavioral uniform-equilibrium payoff after independent positive affine
changes of the players' terminal rewards. -/
theorem isUniformEquilibriumPayoff_playerwiseAffine_of_periodicNashBellmanConditions
    (reward : {coalition : Finset Player // coalition.Nonempty} → Payoff Player)
    (scale shift : Payoff Player) (cycle : Fin K → Player → PMF Bool)
    (value : Fin K → Payoff Player) (initial : Fin K)
    (hscale : ∀ who, 0 < scale who)
    (hpolicy : ∀ phase,
      value phase = quittingRootSuccessorPayoff reward
        (value (finRotate K phase)) (cycle phase))
    (hnash : ∀ phase,
      IsεQuittingRootNash reward (value (finRotate K phase)) 0 (cycle phase))
    (hcontracts : ∀ who,
      (∏ phase : Fin K,
        quittingStationaryFixedOpponentsContinueMass (cycle phase) who) < 1) :
    (quittingGame
      (quittingPlayerwiseAffineReward reward scale shift)).IsUniformEquilibriumPayoff none
        (quittingPlayerwiseAffinePayoff scale shift
          (quittingCyclicTerminalValue reward cycle initial)) := by
  let transformedValue : Fin K → Payoff Player := fun phase =>
    quittingPlayerwiseAffinePayoff scale shift (value phase)
  have htransformedPolicy : ∀ phase,
      transformedValue phase =
        quittingRootSuccessorPayoff
          (quittingPlayerwiseAffineReward reward scale shift)
          (transformedValue (finRotate K phase)) (cycle phase) := by
    intro phase
    funext who
    rw [quittingRootSuccessorPayoff_playerwiseAffine]
    exact congrFun (congrArg
      (quittingPlayerwiseAffinePayoff scale shift) (hpolicy phase)) who
  have htransformedNash : ∀ phase,
      IsεQuittingRootNash
        (quittingPlayerwiseAffineReward reward scale shift)
        (transformedValue (finRotate K phase)) 0 (cycle phase) := by
    intro phase
    exact isZeroQuittingRootNash_playerwiseAffine reward scale shift
      (value (finRotate K phase)) (cycle phase) hscale (hnash phase)
  have hresult :=
    isUniformEquilibriumPayoff_quittingCyclicTerminalValue_of_certificate
      (quittingPlayerwiseAffineReward reward scale shift) cycle
      transformedValue initial htransformedPolicy htransformedNash hcontracts
  rw [quittingCyclicTerminalValue_playerwiseAffine
    reward scale shift cycle hcontracts] at hresult
  exact hresult

end GameTheory

end
