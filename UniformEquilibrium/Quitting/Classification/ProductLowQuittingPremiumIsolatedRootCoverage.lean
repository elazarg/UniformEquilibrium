import MathUE.RealQuantifierElimination.IsolatedRealRootCoverage
import UniformEquilibrium.Quitting.Classification.ProductLowQuittingPremiumIsolatedRootDecision

/-! # Coverage of isolated-root quitting reward inputs -/

namespace GameTheory

open MathUE.RealQuantifierElimination

variable {players : Nat}

/-- Every coordinatewise real-algebraic quitting reward table has certified
isolated-root codes denoting that same table. This is an existence theorem,
not an executable encoder from real values. -/
theorem exists_certifiedIsolatedRootQuittingReward_of_isAlgebraic
    (reward : {S : Finset (Fin players) // S.Nonempty} → Payoff (Fin players))
    (halgebraic : ∀ terminal observer, IsAlgebraic ℚ (reward terminal observer)) :
    ∃ encoded : CertifiedIsolatedRootQuittingReward players,
      encoded.Denotes reward := by
  have hparameters : ∀ index : Fin (quittingRewardParameterCount players),
      IsAlgebraic ℚ (quittingRewardParameters reward index) := by
    intro index
    exact halgebraic ((quittingRewardTableVariableList players).get index).1
      ((quittingRewardTableVariableList players).get index).2
  obtain ⟨parameters, hroots⟩ :=
    exists_certifiedIsolatedRootParameters (quittingRewardParameters reward) hparameters
  refine ⟨fun entry => parameters (quittingRewardTableVariableIndex entry), ?_⟩
  intro terminal observer
  have hroot := hroots (quittingRewardTableVariableIndex (terminal, observer))
  simpa only [quittingRewardParameters,
    quittingRewardTableVariableList_get_index] using hroot

/-- Every encoded quitting reward table denotes at least one simultaneous real
reward table. The witness is semantic and need not be computed by the decision procedure. -/
theorem CertifiedIsolatedRootQuittingReward.exists_denotedReward
    (encoded : CertifiedIsolatedRootQuittingReward players) :
    ∃ reward : {S : Finset (Fin players) // S.Nonempty} → Payoff (Fin players),
      encoded.Denotes reward := by
  obtain ⟨environment, hroots⟩ := exists_isolatedRootParameterEnvironment
    (certifiedIsolatedRootRewardParameters encoded)
  refine ⟨quittingRewardFromParameters environment, ?_⟩
  intro terminal observer
  have hroot := hroots (quittingRewardTableVariableIndex (terminal, observer))
  simpa only [certifiedIsolatedRootRewardParameters,
    quittingRewardTableVariableList_get_index, quittingRewardFromParameters] using hroot

end GameTheory
