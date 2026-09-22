import UniformEquilibrium.Quitting.Classification.PlayerDeletionEvaluatedPayoff
import UniformEquilibrium.Quitting.Classification.QuietExtension.CappedClockChildDeletionAdapter
import UniformEquilibrium.Quitting.Classification.QuietExtension.CappedClockEvaluatedFullBehavioralCap

/-!
# Evaluated child-game debts under a quiet deletion lift

The exact capped-clock comparison applies to the actual Never lift of every
child behavioral profile.  Both the parent law transport and deletion
naturality preserve unrestricted evaluated behavioral debt exactly.
-/

noncomputable section

namespace GameTheory

open StochasticGame

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

local instance quietOutsiderChildNonempty :
    Nonempty {who : Option ι // ¬ who = none} :=
  Nonempty.map (fun who => ⟨some who, Option.some_ne_none who⟩)
    (inferInstance : Nonempty ι)

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
  have h := outsideBehaviorEvaluatedDeviationDebt_le_weighted_childDebt
    reward certificate evaluation evaluation_nonneg evaluation_antitone childLaws
  change quittingBehaviorEvaluatedDeviationPayoffCap reward evaluation
        canonical none -
      quittingBehaviorEvaluatedPayoff reward evaluation canonical none ≤
    ∑ i, certificate.weight i *
      (quittingBehaviorEvaluatedDeviationPayoffCap reward evaluation
          canonical (some i) -
        quittingBehaviorEvaluatedPayoff reward evaluation
          canonical (some i)) at h
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
      ∑ i, certificate.weight i *
        (quittingBehaviorEvaluatedDeviationPayoffCap reward evaluation
            canonical (some i) -
          quittingBehaviorEvaluatedPayoff reward evaluation
            canonical (some i)) := h
    _ = ∑ i, certificate.weight i *
        (quittingBehaviorEvaluatedDeviationPayoffCap
            (quittingDeleteReward reward (· = none)) evaluation childProfile
              ⟨some i, Option.some_ne_none i⟩ -
          quittingBehaviorEvaluatedPayoff
            (quittingDeleteReward reward (· = none)) evaluation childProfile
              ⟨some i, Option.some_ne_none i⟩) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hdebt (some i)]
      congr 1
      exact quittingBehaviorEvaluatedDeviationDebt_liftDeletedProfile
        (deleted := (· = none)) (reward := reward) (evaluation := evaluation)
        (profile := childProfile) (who := ⟨some i, Option.some_ne_none i⟩)

end GameTheory
