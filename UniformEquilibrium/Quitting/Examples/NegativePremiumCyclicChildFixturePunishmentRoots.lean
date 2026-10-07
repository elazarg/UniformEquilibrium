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

def childEndpointGap (h next previous : ℝ) : ℝ :=
  loss * (1 - h) * (1 - next) * (1 - previous) + (1 - loss) * h + next -
    (3 - loss) * previous

def pivotEndpointGap (first second third : ℝ) : ℝ :=
  -(1 - loss) * first - second + (1 - loss) * third +
    loss * (1 - first) * (1 - second) * (1 - third)

/-- The packet's four endpoint polynomials are the actual annotated-root gaps. -/
theorem rootEndpointGap_eq (root : Player → PMF Bool) :
    quittingRootEndpointDifference survivorReward (fun _ => lower) root =
      ![pivotEndpointGap (hazardOfRoot root 1) (hazardOfRoot root 2) (hazardOfRoot root 3),
        childEndpointGap (hazardOfRoot root 0) (hazardOfRoot root 2) (hazardOfRoot root 3),
        childEndpointGap (hazardOfRoot root 0) (hazardOfRoot root 3) (hazardOfRoot root 1),
        childEndpointGap (hazardOfRoot root 0) (hazardOfRoot root 1) (hazardOfRoot root 2)] := by
  funext who
  rw [quittingRootEndpointDifference_eq_gainValue]
  fin_cases who
  · change gainValue (weightOfReward survivorReward) (hazardOfRoot root) (0 : Player) lower =
      pivotEndpointGap (hazardOfRoot root 1) (hazardOfRoot root 2) (hazardOfRoot root 3)
    unfold gainValue sigmaValue gammaValue excludedValue continueMassExcl
    rw [show Finset.univ.erase (0 : Player) = {1, 2, 3} by decide]
    rw [show ({1, 2, 3} : Finset Player).powerset =
      {∅, {1}, {2}, {3}, {1, 2}, {1, 3}, {2, 3}, {1, 2, 3}} by decide]
    simp +decide [weightOfReward, survivorReward, pivotEndpointGap, Finset.sdiff_insert,
      Finset.sdiff_singleton_eq_erase, Finset.erase_insert_of_ne,
      lower, upper, loss, Finset.ext_iff, Fin.forall_fin_succ]
    ring
  · change gainValue (weightOfReward survivorReward) (hazardOfRoot root) (1 : Player) lower =
      childEndpointGap (hazardOfRoot root 0) (hazardOfRoot root 2) (hazardOfRoot root 3)
    unfold gainValue sigmaValue gammaValue excludedValue continueMassExcl
    rw [show Finset.univ.erase (1 : Player) = {0, 2, 3} by decide]
    rw [show ({0, 2, 3} : Finset Player).powerset =
      {∅, {0}, {2}, {3}, {0, 2}, {0, 3}, {2, 3}, {0, 2, 3}} by decide]
    simp +decide [weightOfReward, survivorReward, childEndpointGap, Finset.sdiff_insert,
      Finset.sdiff_singleton_eq_erase, Finset.erase_insert_of_ne,
      lower, upper, loss, Finset.ext_iff, Fin.forall_fin_succ]
    ring
  · change gainValue (weightOfReward survivorReward) (hazardOfRoot root) (2 : Player) lower =
      childEndpointGap (hazardOfRoot root 0) (hazardOfRoot root 3) (hazardOfRoot root 1)
    unfold gainValue sigmaValue gammaValue excludedValue continueMassExcl
    rw [show Finset.univ.erase (2 : Player) = {0, 1, 3} by decide]
    rw [show ({0, 1, 3} : Finset Player).powerset =
      {∅, {0}, {1}, {3}, {0, 1}, {0, 3}, {1, 3}, {0, 1, 3}} by decide]
    simp +decide [weightOfReward, survivorReward, childEndpointGap, Finset.sdiff_insert,
      Finset.sdiff_singleton_eq_erase, Finset.erase_insert_of_ne,
      lower, upper, loss, Finset.ext_iff, Fin.forall_fin_succ]
    ring
  · change gainValue (weightOfReward survivorReward) (hazardOfRoot root) (3 : Player) lower =
      childEndpointGap (hazardOfRoot root 0) (hazardOfRoot root 1) (hazardOfRoot root 2)
    unfold gainValue sigmaValue gammaValue excludedValue continueMassExcl
    rw [show Finset.univ.erase (3 : Player) = {0, 1, 2} by decide]
    rw [show ({0, 1, 2} : Finset Player).powerset =
      {∅, {0}, {1}, {2}, {0, 1}, {0, 2}, {1, 2}, {0, 1, 2}} by decide]
    simp +decide [weightOfReward, survivorReward, childEndpointGap, Finset.sdiff_insert,
      Finset.sdiff_singleton_eq_erase, Finset.erase_insert_of_ne,
      lower, upper, loss, Finset.ext_iff, Fin.forall_fin_succ]
    ring

end GameTheory.NegativePremiumCyclicChild.Fixtures
