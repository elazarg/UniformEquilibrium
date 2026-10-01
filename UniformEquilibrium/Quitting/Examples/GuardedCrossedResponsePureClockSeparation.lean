import UniformEquilibrium.Quitting.Examples.GuardedCrossedResponseToggleWitnesses

/-! # Complete pure-clock separation for the half-ceiling reward table -/

noncomputable section

namespace GameTheory.GuardedCrossedResponseExamples

/-- Every nonempty first coalition can be improved by a membership toggle
worth at least one, and all-Never can be improved by player zero's solo exit. -/
theorem halfCeiling_membershipToggleGap_one :
    HasQuittingPureTimeMembershipToggleGap halfCeilingReward 1 :=
  halfCeiling_literalToggleGap_one


theorem halfCeiling_exists_behaviorDeviation_gain_one
    (times : QuittingPureTimeProfile (Fin 4)) :
    ∃ (who : Fin 4) (deviation : (quittingGame halfCeilingReward).BehaviorStrategy who),
      quittingTerminalPayoff halfCeilingReward
          (quittingPureTimeProfileBehavior halfCeilingReward times) who + 1 ≤
        quittingTerminalPayoff halfCeilingReward
          (Function.update (quittingPureTimeProfileBehavior halfCeilingReward times)
            who deviation) who :=
  halfCeiling_membershipToggleGap_one.exists_behaviorDeviation times

/-- No choice of hidden later deterministic clocks repairs the earliest
coalition's profitable toggle. -/
theorem halfCeiling_not_terminalNash_pureClocks (times : QuittingPureTimeProfile (Fin 4)) :
    ¬ (quittingGame halfCeilingReward).IsεAsymptoticNash (quittingTerminalPayoff halfCeilingReward)
      0 (quittingPureTimeProfileBehavior halfCeilingReward times) :=
  halfCeiling_membershipToggleGap_one.not_isεAsymptoticNash_zero (by norm_num) times

end GameTheory.GuardedCrossedResponseExamples
