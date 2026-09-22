import UniformEquilibrium.Quitting.Classification.QuietExtension.CappedClockPositiveSingletonQuietExtension

/-!
# A future/join certificate whose missing Never row is essential

This one-child table has zero future and joining weights.  The child can
continue forever in exact terminal equilibrium, but the actual quiet lift
leaves the outsider a unit deviation gain.  The entire gap is the omitted
joint-Never row.
-/

noncomputable section

namespace GameTheory
namespace CappedClockMissingNeverFixture

open StochasticGame

abbrev Child := Unit
abbrev Player := Option Child

/-- The child always receives zero, while the quiet outsider receives one at
every terminal coalition. -/
def reward (_ : {S : Finset Player // S.Nonempty}) (who : Player) : ℝ :=
  if who = none then 1 else 0

@[simp] theorem reward_outsider
    (coalition : {S : Finset Player // S.Nonempty}) :
    reward coalition none = 1 := by
  simp [reward]

@[simp] theorem reward_child
    (coalition : {S : Finset Player // S.Nonempty}) (child : Child) :
    reward coalition (some child) = 0 := by
  simp [reward]

/-- The future and joining rows hold with identically zero weights. -/
def futureJoinCertificate : CappedClockParentFutureJoinCertificate reward where
  weight := 0
  weight_nonneg := by simp
  future_row := by simp
  join_row := by simp

/-- The omitted joint-Never row has exact positive-part residual one. -/
theorem neverExcess_eq_one :
    cappedClockNeverExcess reward futureJoinCertificate = 1 := by
  simp [cappedClockNeverExcess, futureJoinCertificate]

/-- The child profile in which the unique child continues forever. -/
def childProfile :
    (quittingGame (quittingDeleteReward reward (· = none))).BehaviorProfile :=
  quittingAlwaysContinueProfile (quittingDeleteReward reward (· = none))

/-- Perpetual continuation is exact terminal Nash in the one-child deletion. -/
theorem childProfile_exactTerminalNash :
    (quittingGame (quittingDeleteReward reward (· = none))).IsεAsymptoticNash
      (quittingTerminalPayoff (quittingDeleteReward reward (· = none))) 0
      childProfile := by
  intro who deviation
  have hdeviation := quittingTerminalPayoff_update_le_continuationBestResponseValue
    (quittingDeleteReward reward (· = none)) childProfile who deviation
  unfold childProfile at hdeviation ⊢
  rw [quittingContinuationBestResponseValue_quittingAlwaysContinueProfile] at hdeviation
  rw [quittingDeleteReward_singletonTerminal] at hdeviation
  have hwho : who.1 ≠ none := who.2
  simp [reward, hwho] at hdeviation ⊢
  exact hdeviation

/-- The actual quiet lift of the all-Never child profile. -/
def liftedProfile : (quittingGame reward).BehaviorProfile :=
  quittingLiftDeletedProfile reward (· = none) childProfile

private theorem behaviorStoppingLaw_alwaysContinue
    {PlayerType : Type} [Fintype PlayerType] [DecidableEq PlayerType]
    (table : {S : Finset PlayerType // S.Nonempty} → Payoff PlayerType)
    (who : PlayerType) :
    quittingBehaviorStoppingLaw table
        (quittingAlwaysContinueProfile table who) = PMF.pure none := by
  change quittingBehaviorStoppingLaw table
      (quittingPureTimeBehaviorStrategy table who none) = PMF.pure none
  exact quittingBehaviorStoppingLaw_pureTime_never table who

private theorem lifted_stoppingLaws_eq_alwaysContinue :
    quittingBehaviorStoppingLaws reward liftedProfile =
      quittingBehaviorStoppingLaws reward (quittingAlwaysContinueProfile reward) := by
  rw [show quittingBehaviorStoppingLaws reward liftedProfile =
      quietParentStoppingLaws (quietOutsiderChildLaws reward childProfile) by
    exact quittingBehaviorStoppingLaws_liftDeletedProfile_eq_quiet reward childProfile]
  funext who
  unfold quittingBehaviorStoppingLaws
  cases who with
  | none =>
      change PMF.pure none = quittingBehaviorStoppingLaw reward
        (quittingAlwaysContinueProfile reward none)
      exact (behaviorStoppingLaw_alwaysContinue reward none).symm
  | some child =>
      change quittingBehaviorStoppingLaw (quittingDeleteReward reward (· = none))
          (childProfile ⟨some child, Option.some_ne_none child⟩) =
        quittingBehaviorStoppingLaw reward
          (quittingAlwaysContinueProfile reward (some child))
      unfold childProfile
      rw [behaviorStoppingLaw_alwaysContinue,
        behaviorStoppingLaw_alwaysContinue]

/-- At the actual quiet lift the outsider's unrestricted terminal deviation
debt is exactly one. -/
theorem liftedProfile_outsiderDebt_eq_one :
    quittingBehaviorDeviationPayoffCap reward liftedProfile none -
        quittingTerminalPayoff reward liftedProfile none = 1 := by
  have hsame := lifted_stoppingLaws_eq_alwaysContinue
  rw [quittingBehaviorDeviationPayoffCap_eq_of_behaviorStoppingLaws_eq
      reward liftedProfile (quittingAlwaysContinueProfile reward) hsame none,
    quittingTerminalPayoff_eq_of_behaviorStoppingLaws_eq
      reward liftedProfile (quittingAlwaysContinueProfile reward) hsame none,
    quittingBehaviorDeviationPayoffCap_eq_bestReplyValue]
  change quittingContinuationBestResponseValue reward
      (quittingAlwaysContinueProfile reward) none -
    quittingTerminalPayoff reward (quittingAlwaysContinueProfile reward) none = 1
  rw [quittingContinuationBestResponseValue_quittingAlwaysContinueProfile,
    quittingTerminalPayoff_quittingAlwaysContinue]
  simp

end CappedClockMissingNeverFixture
end GameTheory
