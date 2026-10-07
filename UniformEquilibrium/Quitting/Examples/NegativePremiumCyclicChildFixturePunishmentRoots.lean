import MathUE.Finset.FinFourNonemptyCoalitions
import UniformEquilibrium.Quitting.Examples.NegativePremiumCyclicChildFixtures
import UniformEquilibrium.Quitting.Punishment.ContinueFloor
import UniformEquilibrium.Quitting.Root.OpponentCoalitionPayoff
import UniformEquilibrium.Quitting.Root.FullClippedEndpointMap
import Mathlib.Order.Iterate

/-! # Actual punishment and full-cube roots of the negative-premium fixture

The punishment calculation uses an actual legal immediate-Quit replacement
against every behavioral opponent plan and an adverse pure-row cap. Full-cube
root classification is a separate development after these semantic bounds.
-/

noncomputable section

namespace GameTheory.NegativePremiumCyclicChild.Fixtures

open QuittingSureSetOwnerRepair
open scoped BigOperators

theorem participantReward_ge_lower
    (coalition : {S : Finset Player // S.Nonempty}) (who : Player)
    (hwho : who ∈ coalition.val) : lower ≤ survivorReward coalition who := by
  obtain ⟨row, hrow⟩ := Math.Finset.finFourCoalitionRowEquiv.surjective coalition
  have heq : Math.Finset.finFourCoalitionOfRow row = coalition.val :=
    congrArg Subtype.val hrow
  have hmember : who ∈ Math.Finset.finFourCoalitionOfRow row := heq.symm ▸ hwho
  have hcoalition : coalition =
      ⟨Math.Finset.finFourCoalitionOfRow row,
        Math.Finset.finFourCoalitionOfRow_nonempty row⟩ := Subtype.ext heq.symm
  rw [hcoalition]
  fin_cases row <;> fin_cases who
  all_goals
    norm_num [Math.Finset.finFourCoalitionOfRow] at hmember
  all_goals
    norm_num [Math.Finset.finFourCoalitionOfRow, survivorReward, lower, upper,
      Finset.ext_iff, Fin.forall_fin_succ]

/-- Every actual opponent coalition gives the participant the same lower bound. -/
theorem rootQuitPayoff_ge_lower (root : Player → PMF Bool) (who : Player) :
    lower ≤ quittingRootQuitPayoff survivorReward 0 root who := by
  rw [quittingRootQuitPayoff_eq_sum_opponentCoalitionMass]
  calc
    lower = ∑ coalition ∈ (Finset.univ.erase who).powerset,
        quittingOpponentCoalitionMass root who coalition * lower := by
      rw [← Finset.sum_mul, quittingOpponentCoalitionMass_sum_powerset, one_mul]
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro coalition _
      apply mul_le_mul_of_nonneg_left _
        (quittingOpponentCoalitionMass_nonneg root who coalition)
      simp only [quittingStageCoalitionPayoff, Finset.insert_nonempty, ↓reduceDIte]
      exact participantReward_ge_lower _ who (Finset.mem_insert_self _ _)

/-- Quit at date zero guarantees the literal floor against all behavioral opponents. -/
theorem immediateQuit_payoff_ge_lower
    (profile : (quittingGame survivorReward).BehaviorProfile) (who : Player) :
    lower ≤ quittingTerminalPayoff survivorReward
      (Function.update profile who
        (quittingPureTimeBehaviorStrategy survivorReward who (some 0))) who := by
  rw [quittingTerminalPayoff_update_pureTimeBehaviorStrategy,
    quittingRootSequencePureTimeTerminalValue_some_self_eq_fixedOpponents,
    ← quittingRootQuitPayoff_eq_fixedOpponentsQuitValue survivorReward
      (quittingProfileLiveRoot survivorReward profile) who 0 0]
  exact rootQuitPayoff_ge_lower _ who

def adverseQuitter : Player → Player := ![3, 0, 0, 0]

theorem punishmentValue_le_lower (who : Player) :
    quittingPunishmentValue survivorReward who ≤ lower := by
  have hcap := quittingPunishmentValue_le_pureRowCap survivorReward who {adverseQuitter who}
  fin_cases who
  all_goals
    norm_num [adverseQuitter, quittingSetReward, survivorReward, lower, upper,
      Finset.ext_iff, Fin.forall_fin_succ] at hcap ⊢
  all_goals exact hcap

/-- The original sixty-coordinate table has punishment value `629/729` for every player. -/
theorem punishmentValue_eq_lower (who : Player) :
    quittingPunishmentValue survivorReward who = lower := by
  refine le_antisymm (punishmentValue_le_lower who) ?_
  let : Nonempty ((quittingGame survivorReward).BehaviorProfile) :=
    ⟨quittingAlwaysContinueProfile survivorReward⟩
  exact le_ciInf fun profile =>
    (immediateQuit_payoff_ge_lower profile who).trans
      (le_quittingBestReplyValue survivorReward profile who
        (quittingPureTimeBehaviorStrategy survivorReward who (some 0)))

end GameTheory.NegativePremiumCyclicChild.Fixtures
