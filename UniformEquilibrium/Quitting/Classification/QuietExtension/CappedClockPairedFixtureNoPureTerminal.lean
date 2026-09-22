/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors.
-/

import UniformEquilibrium.Quitting.Classification.QuietExtension.CappedClockPairedFamily
import UniformEquilibrium.Quitting.Paths.PureTimeMembershipToggleObstruction

/-!
# No complete pure-clock terminal Nash in the paired fixture

Every nonempty first coalition of the explicit paired table has a membership
toggle worth at least one, and a solo exit from all-Never is also worth one.
The generic complete-clock obstruction therefore produces an actual
behavioral deviation gaining at least one from every pure-clock profile.
-/

noncomputable section

namespace GameTheory
namespace CappedClockPairedFixtureNoPureTerminal

open CappedClockPairedFamily

/-- The explicit table has membership-toggle gap one at all fifteen nonempty
coalitions, together with a gap-one solo escape from all-Never. -/
theorem membershipToggleGap_one :
    HasQuittingPureTimeMembershipToggleGap exampleReward 1 := by
  refine ⟨?_, ?_⟩
  · exact ⟨0, by norm_num [exampleReward]⟩
  · intro coalition
    fin_cases coalition <;>
      solve
      | (refine Or.inl ⟨0, ?_, ?_⟩
         · decide
         · norm_num [exampleReward])
      | (refine Or.inl ⟨1, ?_, ?_⟩
         · decide
         · norm_num [exampleReward])
      | (refine Or.inl ⟨2, ?_, ?_⟩
         · decide
         · norm_num [exampleReward])
      | (refine Or.inl ⟨3, ?_, ?_⟩
         · decide
         · norm_num [exampleReward])
      | (refine Or.inr ⟨0, ?_, ?_, ?_⟩
         · decide
         · decide
         · norm_num [exampleReward])
      | (refine Or.inr ⟨1, ?_, ?_, ?_⟩
         · decide
         · decide
         · norm_num [exampleReward])
      | (refine Or.inr ⟨2, ?_, ?_, ?_⟩
         · decide
         · decide
         · norm_num [exampleReward])

/-- Every complete pure-clock profile of the explicit table has an actual
behavioral unilateral deviation gaining at least one. -/
theorem exists_behaviorDeviation_gain_one
    (times : QuittingPureTimeProfile Player) :
    ∃ (who : Player)
        (deviation : (quittingGame exampleReward).BehaviorStrategy who),
      quittingTerminalPayoff exampleReward
          (quittingPureTimeProfileBehavior exampleReward times) who + 1 ≤
        quittingTerminalPayoff exampleReward
          (Function.update
            (quittingPureTimeProfileBehavior exampleReward times)
            who deviation) who :=
  membershipToggleGap_one.exists_behaviorDeviation times

/-- No complete pure-clock profile of the explicit paired table is an exact
terminal Nash equilibrium, even against unrestricted behavioral deviations. -/
theorem not_isεAsymptoticNash_zero
    (times : QuittingPureTimeProfile Player) :
    ¬ (quittingGame exampleReward).IsεAsymptoticNash
        (quittingTerminalPayoff exampleReward) 0
        (quittingPureTimeProfileBehavior exampleReward times) :=
  membershipToggleGap_one.not_isεAsymptoticNash_zero (by norm_num) times

end CappedClockPairedFixtureNoPureTerminal
end GameTheory
