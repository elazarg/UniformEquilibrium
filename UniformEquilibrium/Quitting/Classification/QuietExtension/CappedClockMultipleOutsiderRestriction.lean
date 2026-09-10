import UniformEquilibrium.Quitting.Classification.PlayerDeletionLift
import UniformEquilibrium.Quitting.Classification.PlayerReindexNaturality

/-! # Restricting a quiet lift to the child plus one outsider -/

noncomputable section

namespace GameTheory

open StochasticGame

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The surviving child of a deletion predicate. -/
abbrev QuittingChildPlayer (deleted : ι → Prop) := {who : ι // ¬ deleted who}

/-- Retain the child and one displayed outsider, deleting every other outsider. -/
abbrev QuittingChildWithOutsiderPlayer (deleted : ι → Prop) (outside : ι) :=
  {who : ι // ¬ (deleted who ∧ who ≠ outside)}

/-- The retained child-plus-one-outsider type, with the outsider displayed as `none`. -/
def quittingChildWithOutsiderEquiv (deleted : ι → Prop) [DecidablePred deleted]
    (outside : {who : ι // deleted who}) :
    QuittingChildWithOutsiderPlayer deleted outside.1 ≃
      Option (QuittingChildPlayer deleted) where
  toFun who := if hwho : deleted who.1 then none else some ⟨who.1, hwho⟩
  invFun
    | none => ⟨outside.1, fun h => h.2 rfl⟩
    | some who => ⟨who.1, fun h => who.2 h.1⟩
  left_inv who := by
    by_cases hwho : deleted who.1
    · simp only [hwho, ↓reduceDIte]
      apply Subtype.ext
      by_contra hne
      exact who.2 ⟨hwho, fun heq => hne heq.symm⟩
    · simp [hwho]
  right_inv who := by
    cases who with
    | none => simp [outside.2]
    | some child => simp [child.2]

/-- The reward table obtained by retaining the child and one outsider and
displaying that outsider as `none`. -/
def quittingChildWithOutsiderReward
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (deleted : ι → Prop) [DecidablePred deleted]
    (outside : {who : ι // deleted who}) :
    {S : Finset (Option (QuittingChildPlayer deleted)) // S.Nonempty} →
      Payoff (Option (QuittingChildPlayer deleted)) :=
  quittingRewardReindex (quittingChildWithOutsiderEquiv deleted outside)
    (quittingDeleteReward reward
      (fun who => deleted who ∧ who ≠ outside.1))

/-- The child type is canonically the non-`none` part of its one-outsider
display. -/
def quittingChildSomeEquiv (deleted : ι → Prop) :
    QuittingChildPlayer deleted ≃
      {who : Option (QuittingChildPlayer deleted) // who ≠ none} where
  toFun who := ⟨some who, Option.some_ne_none who⟩
  invFun who := who.1.get (Option.ne_none_iff_isSome.mp who.2)
  left_inv who := rfl
  right_inv who := by
    apply Subtype.ext
    exact Option.some_get _

omit [Fintype ι] in
/-- Deleting the displayed outsider from the retained table recovers the
original child restriction, up to the canonical `some` reindexing. -/
theorem quittingDeleteReward_childWithOutsiderReward
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (deleted : ι → Prop) [DecidablePred deleted]
    (outside : {who : ι // deleted who}) :
    quittingDeleteReward
        (quittingChildWithOutsiderReward reward deleted outside) (· = none) =
      quittingRewardReindex (quittingChildSomeEquiv deleted)
        (quittingDeleteReward reward deleted) := by
  funext coalition who
  change reward _ _ = reward _ _
  congr 1
  · apply Subtype.ext
    ext player
    by_cases hplayer : deleted player
    · simp [quittingExtendDeletedCoalition, quittingCoalitionEquiv,
        quittingChildWithOutsiderEquiv, quittingChildSomeEquiv,
        Finset.mem_map_equiv, hplayer]
    · simp [quittingExtendDeletedCoalition, quittingCoalitionEquiv,
        quittingChildWithOutsiderEquiv, quittingChildSomeEquiv,
        Finset.mem_map_equiv, hplayer]
  · cases hwho : who.1 with
    | none => exact absurd hwho who.2
    | some child =>
        simp [quittingChildWithOutsiderEquiv, quittingChildSomeEquiv, hwho]

/-- Transport an actual child profile to the non-`none` part of a displayed
child-plus-one-outsider restriction. -/
def quittingChildWithOutsiderChildProfile
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (deleted : ι → Prop) [DecidablePred deleted]
    (outside : {who : ι // deleted who})
    (profile : (quittingGame
      (quittingDeleteReward reward deleted)).BehaviorProfile) :
    (quittingGame (quittingDeleteReward
      (quittingChildWithOutsiderReward reward deleted outside)
        (· = none))).BehaviorProfile :=
  quittingProfileOfRewardEq
    (quittingDeleteReward_childWithOutsiderReward reward deleted outside)
    (quittingProfilePushforward (quittingChildSomeEquiv deleted)
      (quittingDeleteReward reward deleted) profile)

/-- The transported child profile preserves every child's terminal payoff. -/
theorem quittingTerminalPayoff_childWithOutsiderChildProfile
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (deleted : ι → Prop) [DecidablePred deleted]
    (outside : {who : ι // deleted who})
    (profile : (quittingGame
      (quittingDeleteReward reward deleted)).BehaviorProfile)
    (who : QuittingChildPlayer deleted) :
    quittingTerminalPayoff
        (quittingDeleteReward
          (quittingChildWithOutsiderReward reward deleted outside) (· = none))
        (quittingChildWithOutsiderChildProfile reward deleted outside profile)
        (quittingChildSomeEquiv deleted who) =
      quittingTerminalPayoff (quittingDeleteReward reward deleted) profile who := by
  rw [quittingChildWithOutsiderChildProfile,
    quittingTerminalPayoff_profileOfRewardEq]
  exact quittingTerminalPayoff_profilePushforward
      (quittingChildSomeEquiv deleted)
      (quittingDeleteReward reward deleted) profile who

/-- The transported child profile preserves every child's unrestricted
behavioral deviation cap. -/
theorem quittingBehaviorDeviationPayoffCap_childWithOutsiderChildProfile
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (deleted : ι → Prop) [DecidablePred deleted]
    (outside : {who : ι // deleted who})
    (profile : (quittingGame
      (quittingDeleteReward reward deleted)).BehaviorProfile)
    (who : QuittingChildPlayer deleted) :
    quittingBehaviorDeviationPayoffCap
        (quittingDeleteReward
          (quittingChildWithOutsiderReward reward deleted outside) (· = none))
        (quittingChildWithOutsiderChildProfile reward deleted outside profile)
        (quittingChildSomeEquiv deleted who) =
      quittingBehaviorDeviationPayoffCap
        (quittingDeleteReward reward deleted) profile who := by
  rw [quittingChildWithOutsiderChildProfile,
    quittingBehaviorDeviationPayoffCap_profileOfRewardEq]
  exact quittingBehaviorDeviationPayoffCap_profilePushforward
      (quittingChildSomeEquiv deleted)
      (quittingDeleteReward reward deleted) profile who

/-- The actual one-outsider quiet lift, pulled back to the retained subtype. -/
def quittingChildWithOutsiderPairProfile
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (deleted : ι → Prop) [DecidablePred deleted]
    (outside : {who : ι // deleted who})
    (profile : (quittingGame
      (quittingDeleteReward reward deleted)).BehaviorProfile) :
    (quittingGame (quittingDeleteReward reward
      (fun who => deleted who ∧ who ≠ outside.1))).BehaviorProfile :=
  quittingProfilePullback (quittingChildWithOutsiderEquiv deleted outside)
    (quittingDeleteReward reward
      (fun who => deleted who ∧ who ≠ outside.1))
    (quittingLiftDeletedProfile
      (quittingChildWithOutsiderReward reward deleted outside) (· = none)
      (quittingChildWithOutsiderChildProfile reward deleted outside profile))

/-- Lift the retained child-plus-one-outsider profile back to the full game. -/
def quittingChildWithOutsiderFullProfile
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (deleted : ι → Prop) [DecidablePred deleted]
    (outside : {who : ι // deleted who})
    (profile : (quittingGame
      (quittingDeleteReward reward deleted)).BehaviorProfile) :
    (quittingGame reward).BehaviorProfile :=
  quittingLiftDeletedProfile reward
    (fun who => deleted who ∧ who ≠ outside.1)
    (quittingChildWithOutsiderPairProfile reward deleted outside profile)

/-- Restricting to the child plus one outsider and lifting back gives the
same complete stopping laws as the direct quiet lift of the child. -/
theorem quittingBehaviorStoppingLaws_childWithOutsiderFullProfile
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (deleted : ι → Prop) [DecidablePred deleted]
    (outside : {who : ι // deleted who})
    (profile : (quittingGame
      (quittingDeleteReward reward deleted)).BehaviorProfile) :
    quittingBehaviorStoppingLaws reward
        (quittingChildWithOutsiderFullProfile reward deleted outside profile) =
      quittingBehaviorStoppingLaws reward
        (quittingLiftDeletedProfile reward deleted profile) := by
  funext player
  by_cases hother : deleted player ∧ player ≠ outside.1
  · have hleft := quittingBehaviorStoppingLaw_liftDeletedProfile_of_deleted
      reward (fun who => deleted who ∧ who ≠ outside.1)
      (quittingChildWithOutsiderPairProfile reward deleted outside profile)
      hother
    have hright := quittingBehaviorStoppingLaw_liftDeletedProfile_of_deleted
      reward deleted profile hother.1
    exact hleft.trans hright.symm
  · let pairPlayer : QuittingChildWithOutsiderPlayer deleted outside.1 :=
      ⟨player, hother⟩
    have hleft := quittingBehaviorStoppingLaw_liftDeletedProfile reward
      (fun who => deleted who ∧ who ≠ outside.1)
      (quittingChildWithOutsiderPairProfile reward deleted outside profile)
      pairPlayer
    have hpull := quittingBehaviorStoppingLaw_profilePullback
      (quittingChildWithOutsiderEquiv deleted outside)
      (quittingDeleteReward reward
        (fun who => deleted who ∧ who ≠ outside.1))
      (quittingLiftDeletedProfile
        (quittingChildWithOutsiderReward reward deleted outside) (· = none)
        (quittingChildWithOutsiderChildProfile reward deleted outside profile))
      pairPlayer
    change quittingBehaviorStoppingLaw
        (quittingDeleteReward reward
          (fun who => deleted who ∧ who ≠ outside.1))
        (quittingChildWithOutsiderPairProfile reward deleted outside profile
          pairPlayer) = _ at hpull
    rw [hpull] at hleft
    by_cases hdeleted : deleted player
    · have hoption :
          quittingChildWithOutsiderEquiv deleted outside pairPlayer = none := by
        simp [quittingChildWithOutsiderEquiv, pairPlayer, hdeleted]
      have hoptionNever :=
        quittingBehaviorStoppingLaw_liftDeletedProfile_of_deleted
          (quittingChildWithOutsiderReward reward deleted outside) (· = none)
          (quittingChildWithOutsiderChildProfile reward deleted outside profile)
          rfl
      have hright := quittingBehaviorStoppingLaw_liftDeletedProfile_of_deleted
        reward deleted profile hdeleted
      rw [hoption] at hleft
      exact hleft.trans (hoptionNever.trans hright.symm)
    · let childPlayer : QuittingChildPlayer deleted := ⟨player, hdeleted⟩
      let optionPlayer :
          {who : Option (QuittingChildPlayer deleted) // who ≠ none} :=
        quittingChildSomeEquiv deleted childPlayer
      have hoption :
          quittingChildWithOutsiderEquiv deleted outside pairPlayer =
            optionPlayer.1 := by
        simp [quittingChildWithOutsiderEquiv, pairPlayer, optionPlayer,
          quittingChildSomeEquiv, childPlayer, hdeleted]
      have hoptionChild := quittingBehaviorStoppingLaw_liftDeletedProfile
        (quittingChildWithOutsiderReward reward deleted outside) (· = none)
        (quittingChildWithOutsiderChildProfile reward deleted outside profile)
        optionPlayer
      have htransport := quittingBehaviorStoppingLaw_profileOfRewardEq
        (quittingDeleteReward_childWithOutsiderReward reward deleted outside)
        (quittingProfilePushforward (quittingChildSomeEquiv deleted)
          (quittingDeleteReward reward deleted) profile)
        optionPlayer
      have hreindex := quittingBehaviorStoppingLaw_profilePushforward
        (quittingChildSomeEquiv deleted)
        (quittingDeleteReward reward deleted) profile childPlayer
      have hright := quittingBehaviorStoppingLaw_liftDeletedProfile
        reward deleted profile childPlayer
      rw [hoption] at hleft
      exact hleft.trans (hoptionChild.trans
        (htransport.trans (hreindex.trans hright.symm)))

end GameTheory
