import MathUE.RealQuantifierElimination.IsolatedRealRootParameters
import UniformEquilibrium.Quitting.Root.RewardTableParameters

/-! # Certified isolated-root parameters for quitting reward tables -/

namespace GameTheory

open MathUE.RealQuantifierElimination

variable {players : Nat}

/-- An exact real-algebraic description for each reward-table entry. -/
abbrev CertifiedIsolatedRootQuittingReward (players : Nat) :=
  QuittingRewardTableVariable (Fin players) → CertifiedIsolatedRealRoot

/-- A real reward table is denoted coordinatewise by the certified inputs. -/
def CertifiedIsolatedRootQuittingReward.Denotes
    (encoded : CertifiedIsolatedRootQuittingReward players)
    (reward : {S : Finset (Fin players) // S.Nonempty} → Payoff (Fin players)) : Prop :=
  ∀ terminal observer,
    (encoded (terminal, observer)).data.RootWithin (reward terminal observer)

/-- Enumerate certified reward entries in the same deterministic order as the formula. -/
def certifiedIsolatedRootRewardParameters
    (encoded : CertifiedIsolatedRootQuittingReward players) :
    Fin (quittingRewardParameterCount players) → CertifiedIsolatedRealRoot :=
  fun index => encoded ((quittingRewardTableVariableList players).get index)

end GameTheory
