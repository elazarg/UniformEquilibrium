import UniformEquilibrium.Quitting.Classification.QuietExtension.CappedClockFullBehavioralCap
import UniformEquilibrium.Quitting.Classification.PlayerDeletionLift

/-!
# Child-game deviation debts under a quiet deletion lift

This adapter identifies actual terminal payoffs and unrestricted behavioral
deviation caps. It applies to every actual child behavioral profile and makes
no claim that profiles with the same live-spine laws are literally equal away
from the unique live history.
-/

noncomputable section

namespace GameTheory

open StochasticGame

section QuietOutsider

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Child laws indexed by the original child type, read from an actual
behavioral profile of the game obtained by deleting the parent outsider. -/
def quietOutsiderChildLaws
    (reward : {S : Finset (Option ι) // S.Nonempty} → Payoff (Option ι))
    (profile : (quittingGame
      (quittingDeleteReward reward (· = none))).BehaviorProfile)
    (i : ι) : PMF (Option ℕ) :=
  quittingBehaviorStoppingLaw (quittingDeleteReward reward (· = none))
    (profile ⟨some i, Option.some_ne_none i⟩)

/-- The actual Never lift of any child behavioral profile induces exactly the
quiet parent stopping laws obtained from that profile's actual stopping laws. -/
theorem quittingBehaviorStoppingLaws_liftDeletedProfile_eq_quiet
    (reward : {S : Finset (Option ι) // S.Nonempty} → Payoff (Option ι))
    (profile : (quittingGame
      (quittingDeleteReward reward (· = none))).BehaviorProfile) :
    quittingBehaviorStoppingLaws reward
        (quittingLiftDeletedProfile reward (· = none) profile) =
      quietParentStoppingLaws (quietOutsiderChildLaws reward profile) := by
  funext player
  cases player with
  | none =>
      exact quittingBehaviorStoppingLaw_liftDeletedProfile_of_deleted
        reward (· = none) profile rfl
  | some i =>
      let who : {who : Option ι // who ≠ none} :=
        ⟨some i, Option.some_ne_none i⟩
      have hlift := quittingBehaviorStoppingLaw_liftDeletedProfile
        reward (· = none) profile who
      change quittingBehaviorStoppingLaw reward
          (quittingLiftDeletedProfile reward (· = none) profile (some i)) =
        quittingBehaviorStoppingLaw (quittingDeleteReward reward (· = none))
          (profile ⟨some i, Option.some_ne_none i⟩)
      change quittingBehaviorStoppingLaw reward
          (quittingLiftDeletedProfile reward (· = none) profile who.1) =
        quittingBehaviorStoppingLaw (quittingDeleteReward reward (· = none))
          (profile who)
      exact hlift

/-- The slack capped-clock parent bound transported to the actual Never lift,
with actual child debts and joint-Never mass on its right side. -/
theorem quietLift_outsideBehaviorDeviationDebt_le_weighted_childDebt_add_slack
    [Nonempty ι]
    (reward : {S : Finset (Option ι) // S.Nonempty} → Payoff (Option ι))
    (certificate : CappedClockParentRewardSlackCertificate reward)
    (childProfile : (quittingGame
      (quittingDeleteReward reward (· = none))).BehaviorProfile) :
    let lifted := quittingLiftDeletedProfile reward (· = none) childProfile
    quittingBehaviorDeviationPayoffCap reward lifted none -
        quittingTerminalPayoff reward lifted none ≤
      (∑ i, certificate.weight i *
        (quittingBehaviorDeviationPayoffCap
            (quittingDeleteReward reward (· = none)) childProfile
              ⟨some i, Option.some_ne_none i⟩ -
          quittingTerminalPayoff
            (quittingDeleteReward reward (· = none)) childProfile
              ⟨some i, Option.some_ne_none i⟩)) +
      certificate.neverSlack *
        ∏ i, (quietOutsiderChildLaws reward childProfile i none).toReal := by
  dsimp only
  let childLaws := quietOutsiderChildLaws reward childProfile
  let lifted := quittingLiftDeletedProfile reward (· = none) childProfile
  let canonical := quittingStoppingLawProfile reward
    (quietParentStoppingLaws childLaws)
  have hlift : quittingBehaviorStoppingLaws reward lifted =
      quietParentStoppingLaws childLaws := by
    exact quittingBehaviorStoppingLaws_liftDeletedProfile_eq_quiet
      reward childProfile
  have hcanonical : quittingBehaviorStoppingLaws reward canonical =
      quietParentStoppingLaws childLaws := by
    funext player
    exact quittingBehaviorStoppingLaw_stoppingLawProfile reward
      (quietParentStoppingLaws childLaws) player
  have hsame : quittingBehaviorStoppingLaws reward canonical =
      quittingBehaviorStoppingLaws reward lifted := hcanonical.trans hlift.symm
  have h :=
    outsideBehaviorDeviationDebt_le_weighted_childBehaviorDeviationDebt_add_slack
    reward certificate childLaws
  change quittingBehaviorDeviationPayoffCap reward canonical none -
      quittingTerminalPayoff reward canonical none ≤
    (∑ i, certificate.weight i *
      (quittingBehaviorDeviationPayoffCap reward canonical (some i) -
        quittingTerminalPayoff reward canonical (some i))) +
      certificate.neverSlack * ∏ i, (childLaws i none).toReal at h
  have hdebt (who : Option ι) :
      quittingBehaviorDeviationPayoffCap reward canonical who -
          quittingTerminalPayoff reward canonical who =
        quittingBehaviorDeviationPayoffCap reward lifted who -
          quittingTerminalPayoff reward lifted who := by
    rw [quittingBehaviorDeviationPayoffCap_eq_of_behaviorStoppingLaws_eq
        reward canonical lifted hsame who,
      quittingTerminalPayoff_eq_of_behaviorStoppingLaws_eq
        reward canonical lifted hsame who]
  rw [hdebt none] at h
  calc
    quittingBehaviorDeviationPayoffCap reward lifted none -
        quittingTerminalPayoff reward lifted none ≤
      (∑ i, certificate.weight i *
        (quittingBehaviorDeviationPayoffCap reward canonical (some i) -
          quittingTerminalPayoff reward canonical (some i))) +
        certificate.neverSlack * ∏ i, (childLaws i none).toReal := h
    _ = (∑ i, certificate.weight i *
        (quittingBehaviorDeviationPayoffCap
            (quittingDeleteReward reward (· = none)) childProfile
              ⟨some i, Option.some_ne_none i⟩ -
          quittingTerminalPayoff
            (quittingDeleteReward reward (· = none)) childProfile
              ⟨some i, Option.some_ne_none i⟩)) +
        certificate.neverSlack *
          ∏ i, (quietOutsiderChildLaws reward childProfile i none).toReal := by
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      rw [hdebt (some i)]
      congr 1
      exact quittingBehaviorDeviationDebt_liftDeletedProfile reward
        (· = none) childProfile ⟨some i, Option.some_ne_none i⟩

/-- Exact N/F/J transport is the zero-slack specialization. -/
theorem quietLift_outsideBehaviorDeviationDebt_le_weighted_childDebt
    [Nonempty ι]
    (reward : {S : Finset (Option ι) // S.Nonempty} → Payoff (Option ι))
    (certificate : CappedClockParentRewardCertificate reward)
    (childProfile : (quittingGame
      (quittingDeleteReward reward (· = none))).BehaviorProfile) :
    let lifted := quittingLiftDeletedProfile reward (· = none) childProfile
    quittingBehaviorDeviationPayoffCap reward lifted none -
        quittingTerminalPayoff reward lifted none ≤
      ∑ i, certificate.weight i *
        (quittingBehaviorDeviationPayoffCap
            (quittingDeleteReward reward (· = none)) childProfile
              ⟨some i, Option.some_ne_none i⟩ -
          quittingTerminalPayoff
            (quittingDeleteReward reward (· = none)) childProfile
              ⟨some i, Option.some_ne_none i⟩) := by
  simpa [CappedClockParentRewardCertificate.withZeroSlack] using
    quietLift_outsideBehaviorDeviationDebt_le_weighted_childDebt_add_slack
      reward certificate.withZeroSlack childProfile

end QuietOutsider

end GameTheory
