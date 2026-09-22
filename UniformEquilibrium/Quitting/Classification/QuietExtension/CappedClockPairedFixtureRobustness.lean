/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors.
-/

import UniformEquilibrium.Quitting.Classification.QuietExtension.CappedClockPairedFixtureNoPureTerminal
import UniformEquilibrium.Quitting.Classification.QuietExtension.CappedClockPairedFixtureSlacks
import UniformEquilibrium.Quitting.Classification.QuietExtension.CappedClockPairedFixtureTerminal
import UniformEquilibrium.Quitting.Cycles.CyclicSingletonEscort
import UniformEquilibrium.Quitting.Terminal.TerminalExploitabilityRewardRobustness

/-!
# Reward robustness of the paired capped-clock fixture

Every sufficiently close table still excludes all complete pure-clock exact
terminal equilibria. The fixture's literal one-date behavioral profile retains
its payoff and full response cap within the perturbation radius, and its
terminal Nash error is at most twice that radius.

Every reward radius below one sixth also preserves the literal weight-two
capped-clock certificate. Its Never margin loses at most three radii and its
future and joining margins lose at most six radii. The existing certificate
consumer then supplies a fixed uniform-equilibrium payoff for the nearby game.
-/

noncomputable section

namespace GameTheory
namespace CappedClockPairedFixtureRobustness

open CappedClockPairedFamily CappedClockPairedFixtureTerminal
open QuittingLCPClassification

/-- The unit membership-toggle gap loses at most twice the reward radius. -/
theorem membershipToggleGap_of_reward_close
    (reward : {S : Finset Player // S.Nonempty} → Payoff Player)
    {radius : ℝ} (hradius : 0 ≤ radius)
    (hclose : ∀ coalition who,
      |exampleReward coalition who - reward coalition who| ≤ radius) :
    HasQuittingPureTimeMembershipToggleGap reward (1 - 2 * radius) :=
  CappedClockPairedFixtureNoPureTerminal.membershipToggleGap_one.of_reward_close hradius hclose

/-- Every radius below one half preserves the obstruction for all complete
pure-clock profiles, with arbitrary finite first dates and Never retained. -/
theorem not_isεAsymptoticNash_zero_of_reward_close
    (reward : {S : Finset Player // S.Nonempty} → Payoff Player)
    {radius : ℝ} (hradius : 0 ≤ radius) (hsmall : radius < 1 / 2)
    (hclose : ∀ coalition who,
      |exampleReward coalition who - reward coalition who| ≤ radius)
    (times : QuittingPureTimeProfile Player) :
    ¬ (quittingGame reward).IsεAsymptoticNash
        (quittingTerminalPayoff reward) 0
        (quittingPureTimeProfileBehavior reward times) :=
  (membershipToggleGap_of_reward_close reward hradius hclose).not_isεAsymptoticNash_zero
    (by linarith) times

/-- The same one-date profile keeps its prescribed payoff within the reward
radius of the displayed fixture target. -/
theorem abs_profile_terminalPayoff_sub_target_le
    (reward : {S : Finset Player // S.Nonempty} → Payoff Player)
    {radius : ℝ} (hradius : 0 ≤ radius)
    (hclose : ∀ coalition who,
      |exampleReward coalition who - reward coalition who| ≤ radius) (who : Player) :
    |quittingTerminalPayoff reward profile who - target who| ≤ radius := by
  have hbound := abs_quittingTerminalPayoff_sub_le_of_forall_abs_sub_le
    exampleReward reward profile who hradius hclose
  rw [profile_terminalPayoff] at hbound
  simpa only [abs_sub_comm] using hbound

/-- The same one-date profile keeps its unrestricted behavioral response cap
within the reward radius of the displayed fixture target. -/
theorem abs_profile_continuationBestResponseValue_sub_target_le
    (reward : {S : Finset Player // S.Nonempty} → Payoff Player)
    {radius : ℝ} (hradius : 0 ≤ radius)
    (hclose : ∀ coalition who,
      |exampleReward coalition who - reward coalition who| ≤ radius) (who : Player) :
    |quittingContinuationBestResponseValue reward profile who - target who| ≤ radius := by
  have hbound := abs_quittingContinuationBestResponseValue_sub_le_of_reward_close
    exampleReward reward profile who hradius hclose
  rw [profile_continuationBestResponseValue] at hbound
  simpa only [abs_sub_comm] using hbound

/-- At every nearby table the literal one-date profile is terminal Nash with
error at most twice the reward radius, against all behavioral deviations. -/
theorem profile_terminalNash_of_reward_close
    (reward : {S : Finset Player // S.Nonempty} → Payoff Player)
    {radius : ℝ} (hradius : 0 ≤ radius)
    (hclose : ∀ coalition who,
      |exampleReward coalition who - reward coalition who| ≤ radius) :
    (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) (2 * radius) profile := by
  simpa only [zero_add] using IsεAsymptoticNash.of_reward_close
    exampleReward reward profile hradius hclose profile_exactTerminalNash

private theorem weighted_sum (value : Child → ℝ) :
    (∑ child, weight child * value child) = 2 * value childTwo := by
  simp [weight]

private theorem parent_reward_close
    (reward : {S : Finset Player // S.Nonempty} → Payoff Player)
    {radius : ℝ}
    (hclose : ∀ coalition who,
      |exampleReward coalition who - reward coalition who| ≤ radius)
    (coalition : {S : Finset (Option Child) // S.Nonempty}) (who : Option Child) :
    |parentReward exampleReward coalition who - parentReward reward coalition who| ≤ radius :=
  hclose _ _

private theorem childCoalition_surjective :
    Function.Surjective CappedClockPairedFixtureSlacks.childCoalition := by
  decide

private theorem one_le_futureSlack (coalition : {S : Finset Child // S.Nonempty}) :
    1 ≤ CappedClockPairedFixtureSlacks.futureSlack coalition := by
  obtain ⟨index, rfl⟩ := childCoalition_surjective coalition
  rw [CappedClockPairedFixtureSlacks.futureSlack_childCoalition]
  fin_cases index <;> norm_num

private theorem one_le_joinSlack (coalition : {S : Finset Child // S.Nonempty}) :
    1 ≤ CappedClockPairedFixtureSlacks.joinSlack coalition := by
  obtain ⟨index, rfl⟩ := childCoalition_surjective coalition
  rw [CappedClockPairedFixtureSlacks.joinSlack_childCoalition]
  fin_cases index <;> norm_num

/-- The two reward differences in a weight-two row lose at most six reward
radii, retaining independent changes to all four coordinates. -/
private theorem weighted_difference_transport
    {firstA firstB firstC firstD secondA secondB secondC secondD radius : ℝ}
    (hA : |firstA - secondA| ≤ radius) (hB : |firstB - secondB| ≤ radius)
    (hC : |firstC - secondC| ≤ radius) (hD : |firstD - secondD| ≤ radius) :
    2 * (firstA - firstB) - (firstC - firstD) - 6 * radius ≤
      2 * (secondA - secondB) - (secondC - secondD) := by
  have hA' := (abs_le.mp hA).2
  have hB' := (abs_le.mp hB).1
  have hC' := (abs_le.mp hC).1
  have hD' := (abs_le.mp hD).2
  linarith

/-- Every radius below one sixth preserves the actual capped-clock parent
certificate with its original weight `2e₂`; singleton rewards may also vary. -/
def certificate_of_reward_close
    (reward : {S : Finset Player // S.Nonempty} → Payoff Player)
    {radius : ℝ} (hsmall : radius < 1 / 6)
    (hclose : ∀ coalition who,
      |exampleReward coalition who - reward coalition who| ≤ radius) :
    CappedClockParentRewardCertificate (parentReward reward) where
  weight := weight
  weight_nonneg := by
    intro child
    unfold weight
    split_ifs <;> norm_num
  never_row := by
    have hsource := CappedClockPairedFixtureSlacks.neverSlack_eq_one
    unfold CappedClockPairedFixtureSlacks.neverSlack at hsource
    simp only [weighted_sum] at hsource ⊢
    have hchild := (abs_le.mp (parent_reward_close reward hclose
      (quittingSingletonTerminal (some childTwo)) (some childTwo))).2
    have howner := (abs_le.mp (parent_reward_close reward hclose
      (quittingSingletonTerminal none) none)).1
    have hmargin :
        1 - 3 * radius ≤
          2 * parentReward reward (quittingSingletonTerminal (some childTwo))
            (some childTwo) - parentReward reward (quittingSingletonTerminal none) none := by
      linarith
    change parentReward reward (quittingSingletonTerminal none) none ≤
      2 * parentReward reward (quittingSingletonTerminal (some childTwo)) (some childTwo)
    linarith
  future_row := by
    intro coalition hcoalition
    have hsource := one_le_futureSlack ⟨coalition, hcoalition⟩
    rw [CappedClockPairedFixtureSlacks.futureSlack_eq_certificateMargin] at hsource
    simp only [weighted_sum] at hsource ⊢
    have hmargin := weighted_difference_transport
      (parent_reward_close reward hclose
        (quittingSingletonTerminal (some childTwo)) (some childTwo))
      (parent_reward_close reward hclose
        ⟨cappedClockChildCoalition coalition,
          cappedClockChildCoalition_nonempty hcoalition⟩ (some childTwo))
      (parent_reward_close reward hclose (quittingSingletonTerminal none) none)
      (parent_reward_close reward hclose
        ⟨cappedClockChildCoalition coalition,
          cappedClockChildCoalition_nonempty hcoalition⟩ none)
    change parentReward reward (quittingSingletonTerminal none) none -
        parentReward reward ⟨cappedClockChildCoalition coalition,
          cappedClockChildCoalition_nonempty hcoalition⟩ none ≤
      2 * (parentReward reward (quittingSingletonTerminal (some childTwo)) (some childTwo) -
        parentReward reward ⟨cappedClockChildCoalition coalition,
          cappedClockChildCoalition_nonempty hcoalition⟩ (some childTwo))
    linarith
  join_row := by
    intro coalition hcoalition
    have hsource := one_le_joinSlack ⟨coalition, hcoalition⟩
    rw [CappedClockPairedFixtureSlacks.joinSlack_eq_certificateMargin] at hsource
    simp only [weighted_sum] at hsource ⊢
    have hmargin := weighted_difference_transport
      (parent_reward_close reward hclose
        ⟨cappedClockChildCoalition (insert childTwo coalition),
          cappedClockChildCoalition_nonempty (Finset.insert_nonempty childTwo coalition)⟩
        (some childTwo))
      (parent_reward_close reward hclose
        ⟨cappedClockChildCoalition coalition,
          cappedClockChildCoalition_nonempty hcoalition⟩ (some childTwo))
      (parent_reward_close reward hclose
        ⟨cappedClockJoinedCoalition coalition,
          cappedClockJoinedCoalition_nonempty coalition⟩ none)
      (parent_reward_close reward hclose
        ⟨cappedClockChildCoalition coalition,
          cappedClockChildCoalition_nonempty hcoalition⟩ none)
    linarith

/-- The perturbed certificate retains exactly the fixture's original weight. -/
@[simp] theorem certificate_of_reward_close_weight
    (reward : {S : Finset Player // S.Nonempty} → Payoff Player)
    {radius : ℝ} (hsmall : radius < 1 / 6)
    (hclose : ∀ coalition who,
      |exampleReward coalition who - reward coalition who| ≤ radius) :
    (certificate_of_reward_close reward hsmall hclose).weight = weight :=
  rfl

/-- A full reward neighborhood of the fixture has a fixed uniform-equilibrium
payoff through the actual capped-clock certificate consumer. -/
theorem exists_uniformEquilibriumPayoff_of_reward_close
    (reward : {S : Finset Player // S.Nonempty} → Payoff Player)
    {radius : ℝ} (hsmall : radius < 1 / 6)
    (hclose : ∀ coalition who,
      |exampleReward coalition who - reward coalition who| ≤ radius) :
    ∃ payoff : Payoff Player,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff :=
  quittingGame_exists_uniformEquilibriumPayoff_of_finFour_cappedClockCertificate
    reward 3 (certificate_of_reward_close reward hsmall hclose)

/-- Every radius below one half preserves the absence of escort edges:
the two singleton differences defining an edge each lose at most two radii. -/
theorem not_escortEdge_of_reward_close
    (reward : {S : Finset Player // S.Nonempty} → Payoff Player)
    {radius : ℝ} (hsmall : radius < 1 / 2)
    (hclose : ∀ coalition who,
      |exampleReward coalition who - reward coalition who| ≤ radius)
    (owner nextOwner : Player) :
    ¬IsQuittingSingletonEscortEdge reward owner nextOwner := by
  rintro ⟨hne, hforward, hreverse⟩
  have hforwardQuit := (abs_le.mp
    (hclose (quittingSingletonTerminal nextOwner) owner)).2
  have hforwardSolo := (abs_le.mp
    (hclose (quittingSingletonTerminal owner) owner)).1
  have hreverseQuit := (abs_le.mp
    (hclose (quittingSingletonTerminal owner) nextOwner)).1
  have hreverseSolo := (abs_le.mp
    (hclose (quittingSingletonTerminal nextOwner) nextOwner)).2
  have hforwardSource :
      quittingSingletonMatrix exampleReward owner nextOwner ≤ 2 * radius := by
    change reward (quittingSingletonTerminal nextOwner) owner -
      reward (quittingSingletonTerminal owner) owner ≤ 0 at hforward
    change exampleReward (quittingSingletonTerminal nextOwner) owner -
      exampleReward (quittingSingletonTerminal owner) owner ≤ 2 * radius
    linarith
  have hreverseSource :
      -2 * radius ≤ quittingSingletonMatrix exampleReward nextOwner owner := by
    change 0 ≤ reward (quittingSingletonTerminal owner) nextOwner -
      reward (quittingSingletonTerminal nextOwner) nextOwner at hreverse
    change -2 * radius ≤ exampleReward (quittingSingletonTerminal owner) nextOwner -
      exampleReward (quittingSingletonTerminal nextOwner) nextOwner
    linarith
  fin_cases owner <;> fin_cases nextOwner
  all_goals first
    | exact hne rfl
    | (norm_num [quittingSingletonMatrix, exampleReward] at hforwardSource hreverseSource
       linarith)

/-- No nearby parent table admits a balanced singleton certificate of any
period; the escort necessity retains repeated owners and zero-hazard phases. -/
theorem not_nonempty_balancedSingletonCycleCertificate_of_reward_close
    (reward : {S : Finset Player // S.Nonempty} → Payoff Player)
    {radius : ℝ} (hsmall : radius < 1 / 2)
    (hclose : ∀ coalition who,
      |exampleReward coalition who - reward coalition who| ≤ radius) (L : ℕ) :
    ¬Nonempty (BalancedSingletonCycleCertificate (L := L) reward) := by
  rintro ⟨certificate⟩
  obtain ⟨cycle, -⟩ := certificate.exists_escortCycle
  exact not_escortEdge_of_reward_close reward hsmall hclose _ _ (cycle.edge 0)

/-- The same exclusion holds on every principal player restriction, including
the three-player child used by the capped-clock certificate. -/
theorem not_nonempty_balancedSingletonCycleCertificate_delete_of_reward_close
    (reward : {S : Finset Player // S.Nonempty} → Payoff Player)
    {radius : ℝ} (hsmall : radius < 1 / 2)
    (hclose : ∀ coalition who,
      |exampleReward coalition who - reward coalition who| ≤ radius)
    (deleted : Player → Prop) [DecidablePred deleted] (L : ℕ) :
    ¬Nonempty (BalancedSingletonCycleCertificate (L := L)
      (quittingDeleteReward reward deleted)) := by
  rintro ⟨certificate⟩
  obtain ⟨cycle, -⟩ := certificate.exists_escortCycle
  obtain ⟨hne, hforward, hreverse⟩ := cycle.edge 0
  have hrestriction (recipient quitter : {who : Player // ¬deleted who}) :
      quittingSingletonMatrix (quittingDeleteReward reward deleted) recipient quitter =
        quittingSingletonMatrix reward recipient.1 quitter.1 := by
    change quittingDeleteReward reward deleted
        (quittingSingletonTerminal quitter) recipient -
      quittingDeleteReward reward deleted (quittingSingletonTerminal recipient) recipient =
        reward (quittingSingletonTerminal quitter.1) recipient.1 -
          reward (quittingSingletonTerminal recipient.1) recipient.1
    simp only [quittingDeleteReward_singletonTerminal]
  rw [hrestriction] at hforward hreverse
  apply not_escortEdge_of_reward_close reward hsmall hclose
    (cycle.vertex 0).1 (cycle.vertex 1).1
  exact ⟨fun heq => hne (Subtype.ext heq), hforward, hreverse⟩

/-- Own singleton values remain positive below radius one, while the exact
deletion gate's continue floor always includes Never's zero. -/
theorem not_blockDispensable_of_reward_close
    (reward : {S : Finset Player // S.Nonempty} → Payoff Player)
    {radius : ℝ} (hsmall : radius < 1)
    (hclose : ∀ coalition who,
      |exampleReward coalition who - reward coalition who| ≤ radius) (owner : Player) :
    ¬QuittingBlockDispensable reward {owner} owner := by
  intro hgate
  have hbound := (abs_le.mp (hclose (quittingSingletonTerminal owner) owner)).2
  rw [CappedClockPairedFixtureSlacks.singleton_self] at hbound
  have hnonpos := quittingBlockContinueFloor_nonpos reward {owner} owner
  linarith [hgate.2]

/-- The source fixture violates the capped joint-exit hypothesis at coalition
`{0,2}`, whose member `0` receives two rather than at most one. -/
theorem exampleReward_not_cappedJointExit :
    ¬QuittingCappedJointExit exampleReward := by
  intro hcapped
  have hbound := hcapped ⟨{0, 2}, by simp⟩ 0 (by simp)
  norm_num [exampleReward] at hbound

/-- The same source witness rejects capped joint exit throughout every reward
neighborhood of radius below one. -/
theorem not_cappedJointExit_of_reward_close
    (reward : {S : Finset Player // S.Nonempty} → Payoff Player)
    {radius : ℝ} (hsmall : radius < 1)
    (hclose : ∀ coalition who,
      |exampleReward coalition who - reward coalition who| ≤ radius) :
    ¬QuittingCappedJointExit reward := by
  intro hcapped
  have hbound := hcapped ⟨{0, 2}, by simp⟩ 0 (by simp)
  have hperturb := (abs_le.mp (hclose ⟨{0, 2}, by simp⟩ 0)).2
  norm_num [exampleReward] at hperturb
  linarith

end CappedClockPairedFixtureRobustness
end GameTheory
