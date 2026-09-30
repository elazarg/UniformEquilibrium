import UniformEquilibrium.Quitting.Classification.QuietExtension.CappedClockMultipleOutsiderDebt

/-!
# Shared terminal one-outsider debt transport

An internal one-outsider bound transports by exact deletion and relabeling.
Public reward-row producers discharge this input from their literal source
certificates, rather than exposing a favorable bound as certificate data.
-/

noncomputable section

namespace GameTheory

open StochasticGame

variable {α : Type} [Fintype α] [DecidableEq α]

local instance terminalOneOutsiderOptionChildNonempty {β : Type} [Nonempty β] :
    Nonempty {who : Option β // ¬ who = none} :=
  Nonempty.map (fun who => ⟨some who, Option.some_ne_none who⟩)
    (inferInstance : Nonempty β)

/-- Exact shared deletion/reindex consumer for a source-proved terminal
one-outsider quiet-lift debt bound. Multi-outsider rewards remain arbitrary. -/
theorem quittingLiftDeletedProfile_outsideTerminalDebt_le_of_oneOutsiderBound
    (deleted : α → Prop) [DecidablePred deleted]
    [Nonempty (QuittingChildPlayer deleted)]
    (reward : {S : Finset α // S.Nonempty} → Payoff α)
    (outside : {who : α // deleted who})
    (weight : QuittingChildPlayer deleted → ℝ)
    (hbound :
      let optionReward := quittingChildWithOutsiderReward reward deleted outside
      ∀ childProfile : (quittingGame
          (quittingDeleteReward optionReward (· = none))).BehaviorProfile,
        let lifted := quittingLiftDeletedProfile optionReward (· = none) childProfile
        quittingBehaviorDeviationPayoffCap optionReward lifted none -
            quittingTerminalPayoff optionReward lifted none ≤
          ∑ who, weight who *
            (quittingBehaviorDeviationPayoffCap
                (quittingDeleteReward optionReward (· = none)) childProfile
                  ⟨some who, Option.some_ne_none who⟩ -
              quittingTerminalPayoff (quittingDeleteReward optionReward (· = none))
                childProfile ⟨some who, Option.some_ne_none who⟩))
    (profile : (quittingGame (quittingDeleteReward reward deleted)).BehaviorProfile) :
    quittingBehaviorDeviationPayoffCap reward
          (quittingLiftDeletedProfile reward deleted profile) outside.1 -
        quittingTerminalPayoff reward
          (quittingLiftDeletedProfile reward deleted profile) outside.1 ≤
      ∑ who, weight who *
        (quittingBehaviorDeviationPayoffCap
            (quittingDeleteReward reward deleted) profile who -
          quittingTerminalPayoff (quittingDeleteReward reward deleted) profile who) := by
  let optionReward := quittingChildWithOutsiderReward reward deleted outside
  let childProfile := quittingChildWithOutsiderChildProfile reward deleted outside profile
  let optionProfile := quittingLiftDeletedProfile optionReward (· = none) childProfile
  have hoption := hbound childProfile
  have hnone := quittingBehaviorDeviationDebt_childWithOutsider_none reward deleted outside profile
  have hsame := quittingBehaviorDeviationDebt_childWithOutsiderFullProfile
    reward deleted outside profile outside.1
  rw [← hsame, ← hnone]
  calc
    quittingBehaviorDeviationPayoffCap optionReward optionProfile none -
        quittingTerminalPayoff optionReward optionProfile none ≤
      ∑ who, weight who *
        (quittingBehaviorDeviationPayoffCap
            (quittingDeleteReward optionReward (· = none)) childProfile
              ⟨some who, Option.some_ne_none who⟩ -
          quittingTerminalPayoff (quittingDeleteReward optionReward (· = none)) childProfile
              ⟨some who, Option.some_ne_none who⟩) := hoption
    _ = _ := by
      apply Finset.sum_congr rfl
      intro who _
      change weight who *
        (quittingBehaviorDeviationPayoffCap
            (quittingDeleteReward
              (quittingChildWithOutsiderReward reward deleted outside) (· = none))
            (quittingChildWithOutsiderChildProfile reward deleted outside profile)
            (quittingChildSomeEquiv deleted who) -
          quittingTerminalPayoff
            (quittingDeleteReward
              (quittingChildWithOutsiderReward reward deleted outside) (· = none))
            (quittingChildWithOutsiderChildProfile reward deleted outside profile)
            (quittingChildSomeEquiv deleted who)) = _
      rw [quittingBehaviorDeviationPayoffCap_childWithOutsiderChildProfile,
        quittingTerminalPayoff_childWithOutsiderChildProfile]

end GameTheory
