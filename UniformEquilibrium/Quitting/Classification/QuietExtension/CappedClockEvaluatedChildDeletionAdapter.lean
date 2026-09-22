import UniformEquilibrium.Quitting.Classification.PlayerDeletionEvaluatedPayoff
import UniformEquilibrium.Quitting.Classification.QuietExtension.CappedClockAdditiveDomination
import UniformEquilibrium.Quitting.Classification.QuietExtension.CappedClockChildDeletionAdapter
import UniformEquilibrium.Quitting.Classification.QuietExtension.CappedClockEvaluatedFullBehavioralCap

/-!
# Evaluated child-game debts under a quiet deletion lift

Exact and uniformly approximate capped-clock comparisons apply to the actual
Never lift of every child behavioral profile.  Parent-law transport and
deletion naturality preserve unrestricted evaluated behavioral debt exactly.
-/

noncomputable section

namespace GameTheory

open StochasticGame

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

local instance quietOutsiderChildNonempty :
    Nonempty {who : Option ι // ¬ who = none} :=
  Nonempty.map (fun who => ⟨some who, Option.some_ne_none who⟩)
    (inferInstance : Nonempty ι)

/-- A reconstructed quiet-profile debt bound with one constant allowance
transports to the actual Never lift and literal deleted-child debts. -/
theorem
    quietLift_outsideBehaviorEvaluatedDeviationDebt_le_weighted_childDebt_add_const_of_canonical
    (reward : {S : Finset (Option ι) // S.Nonempty} → Payoff (Option ι))
    (weight : ι → ℝ)
    (evaluation : WithTop ℕ → ℝ)
    (childProfile : (quittingGame
      (quittingDeleteReward reward (· = none))).BehaviorProfile)
    (allowance : ℝ)
    (hCanonical :
      let childLaws := quietOutsiderChildLaws reward childProfile
      let canonical := quittingStoppingLawProfile reward
        (quietParentStoppingLaws childLaws)
      quittingBehaviorEvaluatedDeviationPayoffCap reward evaluation
            canonical none -
          quittingBehaviorEvaluatedPayoff reward evaluation canonical none ≤
        (∑ i, weight i *
          (quittingBehaviorEvaluatedDeviationPayoffCap reward evaluation
              canonical (some i) -
            quittingBehaviorEvaluatedPayoff reward evaluation
              canonical (some i))) + allowance) :
    let lifted := quittingLiftDeletedProfile reward (· = none) childProfile
    quittingBehaviorEvaluatedDeviationPayoffCap reward evaluation lifted none -
        quittingBehaviorEvaluatedPayoff reward evaluation lifted none ≤
      (∑ i, weight i *
        (quittingBehaviorEvaluatedDeviationPayoffCap
            (quittingDeleteReward reward (· = none)) evaluation childProfile
              ⟨some i, Option.some_ne_none i⟩ -
          quittingBehaviorEvaluatedPayoff
            (quittingDeleteReward reward (· = none)) evaluation childProfile
              ⟨some i, Option.some_ne_none i⟩)) + allowance := by
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
  have h := hCanonical
  dsimp only at h
  change quittingBehaviorEvaluatedDeviationPayoffCap reward evaluation
        canonical none -
      quittingBehaviorEvaluatedPayoff reward evaluation canonical none ≤
    (∑ i, weight i *
      (quittingBehaviorEvaluatedDeviationPayoffCap reward evaluation
          canonical (some i) -
        quittingBehaviorEvaluatedPayoff reward evaluation
          canonical (some i))) + allowance at h
  have hdebt (who : Option ι) :
      quittingBehaviorEvaluatedDeviationPayoffCap reward evaluation
            canonical who -
          quittingBehaviorEvaluatedPayoff reward evaluation canonical who =
        quittingBehaviorEvaluatedDeviationPayoffCap reward evaluation
            lifted who -
          quittingBehaviorEvaluatedPayoff reward evaluation lifted who := by
    rw [
      quittingBehaviorEvaluatedDeviationPayoffCap_eq_of_behaviorStoppingLaws_eq
        reward evaluation canonical lifted hsame who,
      quittingBehaviorEvaluatedPayoff_eq_of_behaviorStoppingLaws_eq
        reward evaluation canonical lifted hsame who]
  rw [hdebt none] at h
  calc
    quittingBehaviorEvaluatedDeviationPayoffCap reward evaluation lifted none -
        quittingBehaviorEvaluatedPayoff reward evaluation lifted none ≤
      (∑ i, weight i *
        (quittingBehaviorEvaluatedDeviationPayoffCap reward evaluation
            canonical (some i) -
          quittingBehaviorEvaluatedPayoff reward evaluation
            canonical (some i))) + allowance := h
    _ = (∑ i, weight i *
        (quittingBehaviorEvaluatedDeviationPayoffCap
            (quittingDeleteReward reward (· = none)) evaluation childProfile
              ⟨some i, Option.some_ne_none i⟩ -
          quittingBehaviorEvaluatedPayoff
            (quittingDeleteReward reward (· = none)) evaluation childProfile
              ⟨some i, Option.some_ne_none i⟩)) + allowance := by
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      rw [hdebt (some i)]
      congr 1
      exact quittingBehaviorEvaluatedDeviationDebt_liftDeletedProfile
        (deleted := (· = none)) (reward := reward) (evaluation := evaluation)
        (profile := childProfile) (who := ⟨some i, Option.some_ne_none i⟩)

/-- Exact Never/future/joining domination for the actual Never lift, under
every nonnegative antitone clock evaluation. -/
theorem quietLift_outsideBehaviorEvaluatedDeviationDebt_le_weighted_childDebt
    (reward : {S : Finset (Option ι) // S.Nonempty} → Payoff (Option ι))
    (certificate : CappedClockParentRewardCertificate reward)
    (evaluation : WithTop ℕ → ℝ)
    (evaluation_nonneg : ∀ clock, 0 ≤ evaluation clock)
    (evaluation_antitone : Antitone evaluation)
    (childProfile : (quittingGame
      (quittingDeleteReward reward (· = none))).BehaviorProfile) :
    let lifted := quittingLiftDeletedProfile reward (· = none) childProfile
    quittingBehaviorEvaluatedDeviationPayoffCap reward evaluation lifted none -
        quittingBehaviorEvaluatedPayoff reward evaluation lifted none ≤
      ∑ i, certificate.weight i *
        (quittingBehaviorEvaluatedDeviationPayoffCap
            (quittingDeleteReward reward (· = none)) evaluation childProfile
              ⟨some i, Option.some_ne_none i⟩ -
          quittingBehaviorEvaluatedPayoff
            (quittingDeleteReward reward (· = none)) evaluation childProfile
              ⟨some i, Option.some_ne_none i⟩) := by
  simpa using
    (quietLift_outsideBehaviorEvaluatedDeviationDebt_le_weighted_childDebt_add_const_of_canonical
      reward certificate.weight evaluation childProfile 0
        (by simpa using
          (outsideBehaviorEvaluatedDeviationDebt_le_weighted_childDebt
            reward certificate evaluation evaluation_nonneg evaluation_antitone
              (quietOutsiderChildLaws reward childProfile))))

/-- A common additive violation of all parent rows bounds the actual Never
lift's outsider debt by the literal child debts plus one evaluation-scaled
allowance. -/
theorem
    quietLift_outsideBehaviorEvaluatedDeviationDebt_le_weighted_childDebt_add_error
    (reward : {S : Finset (Option ι) // S.Nonempty} → Payoff (Option ι))
    (certificate : CappedClockParentRewardAdditiveCertificate reward)
    (evaluation : WithTop ℕ → ℝ)
    (evaluation_nonneg : ∀ clock, 0 ≤ evaluation clock)
    (evaluation_antitone : Antitone evaluation)
    (childProfile : (quittingGame
      (quittingDeleteReward reward (· = none))).BehaviorProfile) :
    let lifted := quittingLiftDeletedProfile reward (· = none) childProfile
    quittingBehaviorEvaluatedDeviationPayoffCap reward evaluation lifted none -
        quittingBehaviorEvaluatedPayoff reward evaluation lifted none ≤
      (∑ i, certificate.weight i *
        (quittingBehaviorEvaluatedDeviationPayoffCap
            (quittingDeleteReward reward (· = none)) evaluation childProfile
              ⟨some i, Option.some_ne_none i⟩ -
          quittingBehaviorEvaluatedPayoff
            (quittingDeleteReward reward (· = none)) evaluation childProfile
              ⟨some i, Option.some_ne_none i⟩)) +
        certificate.rowError * evaluation 0 := by
  exact
    quietLift_outsideBehaviorEvaluatedDeviationDebt_le_weighted_childDebt_add_const_of_canonical
      reward certificate.weight evaluation childProfile
        (certificate.rowError * evaluation 0)
          (outsideBehaviorEvaluatedDeviationDebt_le_weighted_childDebt_add_error
            reward certificate evaluation evaluation_nonneg evaluation_antitone
              (quietOutsiderChildLaws reward childProfile))

/-- For an evaluation normalized by `evaluation 0 ≤ 1`, the actual Never
lift pays at most the literal common row allowance. -/
theorem
    quietLift_outsideBehaviorEvaluatedDeviationDebt_le_weighted_childDebt_add_rowError
    (reward : {S : Finset (Option ι) // S.Nonempty} → Payoff (Option ι))
    (certificate : CappedClockParentRewardAdditiveCertificate reward)
    (evaluation : WithTop ℕ → ℝ)
    (evaluation_nonneg : ∀ clock, 0 ≤ evaluation clock)
    (evaluation_antitone : Antitone evaluation)
    (evaluation_zero_le_one : evaluation 0 ≤ 1)
    (childProfile : (quittingGame
      (quittingDeleteReward reward (· = none))).BehaviorProfile) :
    let lifted := quittingLiftDeletedProfile reward (· = none) childProfile
    quittingBehaviorEvaluatedDeviationPayoffCap reward evaluation lifted none -
        quittingBehaviorEvaluatedPayoff reward evaluation lifted none ≤
      (∑ i, certificate.weight i *
        (quittingBehaviorEvaluatedDeviationPayoffCap
            (quittingDeleteReward reward (· = none)) evaluation childProfile
              ⟨some i, Option.some_ne_none i⟩ -
          quittingBehaviorEvaluatedPayoff
            (quittingDeleteReward reward (· = none)) evaluation childProfile
              ⟨some i, Option.some_ne_none i⟩)) + certificate.rowError := by
  refine
    (quietLift_outsideBehaviorEvaluatedDeviationDebt_le_weighted_childDebt_add_error
      reward certificate evaluation evaluation_nonneg evaluation_antitone
        childProfile).trans ?_
  exact add_le_add le_rfl
    (mul_le_of_le_one_right certificate.rowError_nonneg evaluation_zero_le_one)

end GameTheory
