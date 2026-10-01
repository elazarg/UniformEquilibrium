import UniformEquilibrium.Quitting.Root.FiniteDeadlineTimingWord
import UniformEquilibrium.Quitting.Classification.PlayerDeletionLift
import UniformEquilibrium.Quitting.Classification.PlayerReindex

/-! # Actual finite-timing reindexing and quiet extension

A child law keeps its complete date-or-Never distribution and its calendar.
Every deleted player receives the literal point mass at Never. Profile
equalities below include every history, not just positive-probability ones,
and do not discard the empty calendar or post-calendar deviation replies.
-/

noncomputable section

namespace GameTheory

variable {α κ : Type} [Fintype α] [DecidableEq α] [Fintype κ] [DecidableEq κ]

omit [DecidableEq α] [DecidableEq κ] in
theorem quittingFiniteDeadlineTimingProfile_pullback
    (label : α ≃ κ) (reward : {S : Finset α // S.Nonempty} → Payoff α)
    (deadline : ℕ) (mixed : κ → PMF (QuittingFiniteDeadlineTimingAction deadline)) :
    quittingProfilePullback label reward
        (quittingFiniteDeadlineTimingProfile (quittingRewardReindex label reward)
          deadline mixed) =
      quittingFiniteDeadlineTimingProfile reward deadline (fun who => mixed (label who)) := by
  funext who time history
  rfl

omit [Fintype α] [DecidableEq α] [Fintype κ] [DecidableEq κ] in
/-- Append actual independent Never laws, retaining the child's exact deadline. -/
def quittingExtendDeletedFiniteTimingLaws
    (deleted : α → Prop) [DecidablePred deleted] (deadline : ℕ)
    (mixed : {who : α // ¬ deleted who} → PMF (QuittingFiniteDeadlineTimingAction deadline)) :
    α → PMF (QuittingFiniteDeadlineTimingAction deadline) := fun who =>
  if h : deleted who then PMF.pure none else mixed ⟨who, h⟩

omit [Fintype α] [DecidableEq α] [Fintype κ] [DecidableEq κ] in
theorem quittingExtendDeletedFiniteTimingLaws_of_deleted
    (deleted : α → Prop) [DecidablePred deleted] (deadline : ℕ)
    (mixed : {who : α // ¬ deleted who} → PMF (QuittingFiniteDeadlineTimingAction deadline))
    (who : α) (hwho : deleted who) :
    quittingExtendDeletedFiniteTimingLaws deleted deadline mixed who = PMF.pure none := by
  simp only [quittingExtendDeletedFiniteTimingLaws, dite_eq_left hwho]

omit [Fintype α] [DecidableEq α] [Fintype κ] [DecidableEq κ] in
theorem quittingExtendDeletedFiniteTimingLaws_apply
    (deleted : α → Prop) [DecidablePred deleted] (deadline : ℕ)
    (mixed : {who : α // ¬ deleted who} → PMF (QuittingFiniteDeadlineTimingAction deadline))
    (who : {who : α // ¬ deleted who}) :
    quittingExtendDeletedFiniteTimingLaws deleted deadline mixed who.1 = mixed who := by
  simp only [quittingExtendDeletedFiniteTimingLaws, dite_eq_right who.2]

omit [Fintype κ] [DecidableEq κ] [DecidableEq α] in
/-- The finite-law parent is exactly the canonical actual quiet profile lift. -/
theorem quittingFiniteDeadlineTimingProfile_extendDeleted
    (deleted : α → Prop) [DecidablePred deleted]
    (reward : {S : Finset α // S.Nonempty} → Payoff α)
    (deadline : ℕ)
    (mixed : {who : α // ¬ deleted who} → PMF (QuittingFiniteDeadlineTimingAction deadline)) :
    quittingLiftDeletedProfile reward deleted
        (quittingFiniteDeadlineTimingProfile (quittingDeleteReward reward deleted)
          deadline mixed) =
      quittingFiniteDeadlineTimingProfile reward deadline
        (quittingExtendDeletedFiniteTimingLaws deleted deadline mixed) := by
  funext who time history
  simp only [quittingLiftDeletedProfile, quittingInfinitePathProfile,
    quittingRootSequenceProfile, Nat.zero_add]
  change quittingExtendDeletedRoots deleted
    (quittingProfileLiveRoot (quittingDeleteReward reward deleted)
      (quittingFiniteDeadlineTimingProfile (quittingDeleteReward reward deleted)
        deadline mixed)) time who = _
  by_cases hwho : deleted who
  · rw [quittingExtendDeletedRoots_of_deleted deleted _ time hwho]
    have hprofile := quittingFiniteDeadlineTimingProfile_eq_alwaysContinue_of_pure_none
      reward deadline (quittingExtendDeletedFiniteTimingLaws deleted deadline mixed) who
      (quittingExtendDeletedFiniteTimingLaws_of_deleted deleted deadline mixed who hwho)
    rw [hprofile]
    rfl
  · simp only [quittingExtendDeletedRoots, quittingExtendDeletedRoot, dite_eq_right hwho,
      quittingProfileLiveRoot, quittingFiniteDeadlineTimingProfile,
      quittingCompactStoppingLawProfile, quittingStoppingLawBehaviorStrategy,
      quittingExtendDeletedFiniteTimingLaws]

end GameTheory
