import MathUE.LinearProgramming.CrossedMatchingPositiveOdds
import MathUE.LinearProgramming.PositiveInverseTwoPairOdds
import UniformEquilibrium.Quitting.Cycles.TwoPairOddsValues
import UniformEquilibrium.Quitting.Projective.FinFourAmbientQSimplex
import UniformEquilibrium.Quitting.Terminal.TerminalExploitabilityRewardRobustness
import UniformEquilibrium.Quitting.Classification.PlayerReindex
import UniformEquilibrium.Quitting.Root.PureSureSetExactHorizons

/-! # Actual crossed-matching two-pair phases

The literal reward comparisons produce positive odds and all passive endpoint
tests internally. Singleton levels, participant increments and passive pair
entries may be signed. One fixed profile supplies the target and approximate
Nash bounds at every accuracy over sufficiently long horizons.
-/

noncomputable section

namespace GameTheory.PairedCycle.CrossedMatching

open Math.CrossedMatching Math.PairedAffine Math.LinearProgramming
open QuittingSureSetOwnerRepair

abbrev Reward := {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)

export TwoPairOdds (premium passive hazard hazard_proper matrix_entry activeValue_eq
  postValue_eq passive_continue)

/-- Only the printed singleton, scheduled joining and passive insertion tests. -/
structure RawSource (reward : Reward) : Prop where
  favorite_gt : ∀ player, singleton reward player <
    reward (quittingSingletonTerminal (favorite player)) player
  scheduled_lt : ∀ player, reward (quittingSingletonTerminal (scheduled player)) player <
    singleton reward player
  other_lt : ∀ player, reward (quittingSingletonTerminal (other player)) player <
    singleton reward player
  scheduled_join_gt : ∀ player,
    reward (quittingSingletonTerminal (scheduled player)) player <
      reward ⟨{player, scheduled player}, by simp⟩ player
  cap_favorite : ∀ player, reward ⟨{player, favorite player}, by simp⟩ player ≤
    singleton reward player
  cap_other : ∀ player, reward ⟨{player, other player}, by simp⟩ player ≤
    singleton reward player
  cap_joint : ∀ player, reward ⟨{player, favorite player, other player}, by simp⟩ player ≤
    singleton reward player


theorem RawSource.matchingSigns {reward : Reward} (hraw : RawSource reward) :
    HasStrictMatchingSigns (quittingProjectiveLCPMatrix reward) := by
  constructor
  · intro player
    rw [matrix_entry]
    exact sub_self _
  · intro player
    rw [matrix_entry]
    exact sub_pos.mpr (hraw.favorite_gt player)
  · intro player
    rw [matrix_entry]
    exact sub_neg.mpr (hraw.scheduled_lt player)
  · intro player
    rw [matrix_entry]
    exact sub_neg.mpr (hraw.other_lt player)

theorem RawSource.premium_gt {reward : Reward} (hraw : RawSource reward) (player : Fin 4) :
    quittingProjectiveLCPMatrix reward player (scheduled player) < premium reward player := by
  rw [matrix_entry]
  exact sub_lt_sub_right (hraw.scheduled_join_gt player) _


theorem postValue_gt_singleton {reward : Reward} (hraw : RawSource reward)
    {point : Fin 4 → ℝ} (hpoint : ∀ player, 0 < point player) (player : Fin 4) :
    singleton reward player < twoPairPostValue reward fin4Schedule (hazard point) player := by
  rw [postValue_eq reward hpoint]
  exact lt_add_of_pos_right _
    (mul_pos (sub_pos.mpr (hraw.premium_gt player)) (hpoint _))


theorem passive_quit_of_caps (reward : Reward)
    (hgap : ∀ player, quittingProjectiveLCPMatrix reward player (scheduled player) <
      premium reward player)
    (hcapFavorite : ∀ player, reward ⟨{player, favorite player}, by simp⟩ player ≤
      singleton reward player)
    (hcapOther : ∀ player, reward ⟨{player, other player}, by simp⟩ player ≤
      singleton reward player)
    (hcapJoint : ∀ player, reward ⟨{player, favorite player, other player}, by simp⟩ player ≤
      singleton reward player)
    {point : Fin 4 → ℝ} (hpoint : ∀ player, 0 < point player) (player : Fin 4) :
    quittingRootQuitPayoff reward
      (twoPairPhaseValue reward fin4Schedule (hazard point) (fin4Schedule.phase player))
      (cycle fin4Schedule (hazard point) (properUnitBounds _ (hazard_proper hpoint))
        (finRotate 2 (fin4Schedule.phase player))) player ≤
      twoPairPostValue reward fin4Schedule (hazard point) player := by
  rw [fin4Schedule_passive_root, rootQuit_eq_bellman]
  · simp only [quittingHazardCoin_true_toReal]
    apply le_trans (bellman_le
      (properUnitBounds _ (hazard_proper hpoint) _) (properUnitBounds _ (hazard_proper hpoint) _)
      (hcapFavorite player) (hcapOther player) (hcapJoint player) le_rfl)
    rw [postValue_eq reward hpoint]
    exact le_add_of_nonneg_right (mul_pos (sub_pos.mpr (hgap player)) (hpoint _)).le
  · fin_cases player <;> decide

theorem passive_quit {reward : Reward} (hraw : RawSource reward)
    {point : Fin 4 → ℝ} (hpoint : ∀ player, 0 < point player) (player : Fin 4) :
    quittingRootQuitPayoff reward
      (twoPairPhaseValue reward fin4Schedule (hazard point) (fin4Schedule.phase player))
      (cycle fin4Schedule (hazard point) (properUnitBounds _ (hazard_proper hpoint))
        (finRotate 2 (fin4Schedule.phase player))) player ≤
      twoPairPostValue reward fin4Schedule (hazard point) player :=
  passive_quit_of_caps reward hraw.premium_gt hraw.cap_favorite hraw.cap_other
    hraw.cap_joint hpoint player

theorem exists_exact_cycle_of_standardQ_all_initial {reward : Reward} (hraw : RawSource reward)
    (hQ : IsStandardQ (quittingProjectiveLCPMatrix reward)) :
    ∃ (q : Fin 4 → ℝ) (hproper : ∀ player, q player ∈ Set.Ioo (0 : ℝ) 1), ∀ initial : Fin 2,
      let profile := quittingCyclicBehaviorProfile reward
        (cycle fin4Schedule q (properUnitBounds q hproper)) initial
      quittingTerminalPayoff reward profile = twoPairPhaseValue reward fin4Schedule q initial ∧
      (quittingGame reward).IsεAsymptoticNash (quittingTerminalPayoff reward) 0 profile ∧
      (∀ ε : ℝ, 0 < ε → ∃ threshold : ℕ, ∀ horizon, threshold ≤ horizon →
        (quittingGame reward).IsεHorizonNash none horizon ε profile ∧
          ∀ player, |(quittingGame reward).finiteAveragePayoff none horizon profile player -
            twoPairPhaseValue reward fin4Schedule q initial player| ≤ ε) ∧
      (quittingGame reward).IsUniformEquilibriumPayoff none
        (twoPairPhaseValue reward fin4Schedule q initial) := by
  obtain ⟨point, hpoint, _, hequation⟩ := exists_positive_odds_of_matching_standardQ
    (quittingProjectiveLCPMatrix reward) hraw.matchingSigns hQ (premium reward) (passive reward)
    hraw.premium_gt
  exact ⟨hazard point, hazard_proper hpoint, fun initial =>
    twoPair_exact_terminal_and_fixedProfile reward fin4Schedule (hazard point)
      (hazard_proper hpoint) (passive_continue reward hpoint hequation)
      (passive_quit hraw hpoint) initial⟩

theorem exists_exact_cycle_of_standardQ {reward : Reward} (hraw : RawSource reward)
    (hQ : IsStandardQ (quittingProjectiveLCPMatrix reward)) (initial : Fin 2) :
    ∃ (q : Fin 4 → ℝ) (hproper : ∀ player, q player ∈ Set.Ioo (0 : ℝ) 1),
      let profile := quittingCyclicBehaviorProfile reward
        (cycle fin4Schedule q (properUnitBounds q hproper)) initial
      quittingTerminalPayoff reward profile = twoPairPhaseValue reward fin4Schedule q initial ∧
      (quittingGame reward).IsεAsymptoticNash (quittingTerminalPayoff reward) 0 profile ∧
      (∀ ε : ℝ, 0 < ε → ∃ threshold : ℕ, ∀ horizon, threshold ≤ horizon →
        (quittingGame reward).IsεHorizonNash none horizon ε profile ∧
          ∀ player, |(quittingGame reward).finiteAveragePayoff none horizon profile player -
            twoPairPhaseValue reward fin4Schedule q initial player| ≤ ε) ∧
      (quittingGame reward).IsUniformEquilibriumPayoff none
        (twoPairPhaseValue reward fin4Schedule q initial) := by
  obtain ⟨q, hproper, hprofile⟩ := exists_exact_cycle_of_standardQ_all_initial hraw hQ
  exact ⟨q, hproper, hprofile initial⟩

/-- Bare original-game no-UE supplies Q; no singleton normalization or sign is input. -/
theorem exists_uniformEquilibriumPayoff {reward : Reward} (hraw : RawSource reward) :
    ∃ target : Payoff (Fin 4), (quittingGame reward).IsUniformEquilibriumPayoff none target := by
  by_contra hnot
  have hQ := isStandardQ_quittingProjectiveLCPMatrix_of_finFour_no_uniformPayoff reward hnot
  obtain ⟨q, hproper, _, _, _, hUE⟩ := exists_exact_cycle_of_standardQ hraw hQ 0
  exact hnot ⟨twoPairPhaseValue reward fin4Schedule q 0, hUE⟩

/-- The weak predicate contains the same literal comparisons with non-strict signs. -/
structure WeakRawSource (reward : Reward) : Prop where
  favorite_ge : ∀ player, singleton reward player ≤
    reward (quittingSingletonTerminal (favorite player)) player
  scheduled_le : ∀ player, reward (quittingSingletonTerminal (scheduled player)) player ≤
    singleton reward player
  other_le : ∀ player, reward (quittingSingletonTerminal (other player)) player ≤
    singleton reward player
  scheduled_join_ge : ∀ player,
    reward (quittingSingletonTerminal (scheduled player)) player ≤
      reward ⟨{player, scheduled player}, by simp⟩ player
  cap_favorite : ∀ player, reward ⟨{player, favorite player}, by simp⟩ player ≤
    singleton reward player
  cap_other : ∀ player, reward ⟨{player, other player}, by simp⟩ player ≤
    singleton reward player
  cap_joint : ∀ player, reward ⟨{player, favorite player, other player}, by simp⟩ player ≤
    singleton reward player

/-- Only the twelve off-diagonal singleton coordinates change. -/
def singletonPerturbation (reward : Reward) (delta : ℝ) : Reward := fun terminal player =>
  if terminal.val = {favorite player} then reward terminal player + delta
  else if terminal.val = {scheduled player} ∨ terminal.val = {other player} then
    reward terminal player - delta else reward terminal player

private theorem singletonPerturbation_entries (reward : Reward) (delta : ℝ) (player : Fin 4) :
    singleton (singletonPerturbation reward delta) player = singleton reward player ∧
    singletonPerturbation reward delta (quittingSingletonTerminal (favorite player)) player =
      reward (quittingSingletonTerminal (favorite player)) player + delta ∧
    singletonPerturbation reward delta (quittingSingletonTerminal (scheduled player)) player =
      reward (quittingSingletonTerminal (scheduled player)) player - delta ∧
    singletonPerturbation reward delta (quittingSingletonTerminal (other player)) player =
      reward (quittingSingletonTerminal (other player)) player - delta := by
  fin_cases player <;> simp [singletonPerturbation, singleton, quittingSingletonTerminal,
    favorite, scheduled, other]

private theorem singletonPerturbation_eq_of_nonsingleton
    (reward : Reward) (delta : ℝ) (terminal : {S : Finset (Fin 4) // S.Nonempty})
    (hcard : 1 < terminal.val.card) (player : Fin 4) :
    singletonPerturbation reward delta terminal player = reward terminal player := by
  have hnot : ∀ who : Fin 4, terminal.val ≠ {who} := by
    intro who hequal
    rw [hequal, Finset.card_singleton] at hcard
    exact (lt_irrefl _ hcard)
  simp [singletonPerturbation, hnot]

private theorem singletonPerturbation_joint_entries
    (reward : Reward) (delta : ℝ) (player : Fin 4) :
    singletonPerturbation reward delta ⟨{player, scheduled player}, by simp⟩ player =
        reward ⟨{player, scheduled player}, by simp⟩ player ∧
    singletonPerturbation reward delta ⟨{player, favorite player}, by simp⟩ player =
        reward ⟨{player, favorite player}, by simp⟩ player ∧
    singletonPerturbation reward delta ⟨{player, other player}, by simp⟩ player =
        reward ⟨{player, other player}, by simp⟩ player ∧
    singletonPerturbation reward delta ⟨{player, favorite player, other player}, by simp⟩ player =
        reward ⟨{player, favorite player, other player}, by simp⟩ player := by
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals apply singletonPerturbation_eq_of_nonsingleton
  all_goals fin_cases player <;> decide

theorem singletonPerturbation_distance (reward : Reward) (delta : ℝ)
    (terminal : {S : Finset (Fin 4) // S.Nonempty}) (player : Fin 4) :
    |singletonPerturbation reward delta terminal player - reward terminal player| ≤ |delta| := by
  unfold singletonPerturbation
  split_ifs <;> simp only [add_sub_cancel_left, sub_sub_cancel_left, abs_neg, sub_self,
    abs_zero, le_refl, abs_nonneg]

theorem WeakRawSource.strictPerturbation {reward : Reward} (hraw : WeakRawSource reward)
    {delta : ℝ} (hdelta : 0 < delta) : RawSource (singletonPerturbation reward delta) := by
  constructor
  · intro player
    obtain ⟨hown, hf, _, _⟩ := singletonPerturbation_entries reward delta player
    rw [hown, hf]
    linarith [hraw.favorite_ge player]
  · intro player
    obtain ⟨hown, _, hs, _⟩ := singletonPerturbation_entries reward delta player
    rw [hown, hs]
    linarith [hraw.scheduled_le player]
  · intro player
    obtain ⟨hown, _, _, ho⟩ := singletonPerturbation_entries reward delta player
    rw [hown, ho]
    linarith [hraw.other_le player]
  · intro player
    obtain ⟨_, _, hs, _⟩ := singletonPerturbation_entries reward delta player
    obtain ⟨hjoint, _, _, _⟩ := singletonPerturbation_joint_entries reward delta player
    rw [hs, hjoint]
    linarith [hraw.scheduled_join_ge player]
  · intro player
    obtain ⟨hown, _, _, _⟩ := singletonPerturbation_entries reward delta player
    obtain ⟨_, hf, _, _⟩ := singletonPerturbation_joint_entries reward delta player
    rw [hown, hf]
    exact hraw.cap_favorite player
  · intro player
    obtain ⟨hown, _, _, _⟩ := singletonPerturbation_entries reward delta player
    obtain ⟨_, _, ho, _⟩ := singletonPerturbation_joint_entries reward delta player
    rw [hown, ho]
    exact hraw.cap_other player
  · intro player
    obtain ⟨hown, _, _, _⟩ := singletonPerturbation_entries reward delta player
    obtain ⟨_, _, _, hj⟩ := singletonPerturbation_joint_entries reward delta player
    rw [hown, hj]
    exact hraw.cap_joint player

/-- Weak boundaries use reward closure, not a limiting periodic strategy. -/
theorem exists_uniformEquilibriumPayoff_of_weak {reward : Reward}
    (hraw : WeakRawSource reward) :
    ∃ target : Payoff (Fin 4), (quittingGame reward).IsUniformEquilibriumPayoff none target := by
  apply exists_uniformEquilibriumPayoff_of_arbitrarily_close_reward_tables reward
  intro delta hdelta
  refine ⟨singletonPerturbation reward delta, ?_,
    exists_uniformEquilibriumPayoff (hraw.strictPerturbation hdelta)⟩
  intro terminal player
  exact (singletonPerturbation_distance reward delta terminal player).trans_eq
    (abs_of_pos hdelta)

structure InverseRawSource (reward : Reward) : Prop where
  inverse_positive : HasStrictlyPositiveInverse (quittingProjectiveLCPMatrix reward)
  scheduled_lt : ∀ player,
    reward (quittingSingletonTerminal (scheduled player)) player < singleton reward player
  participant_ge : ∀ player, singleton reward player ≤
    reward ⟨{player, scheduled player}, by simp⟩ player
  passive_le : ∀ player, reward ⟨{favorite player, other player}, by simp⟩ player ≤
    singleton reward player
  cap_favorite : ∀ player, reward ⟨{player, favorite player}, by simp⟩ player ≤
    singleton reward player
  cap_other : ∀ player, reward ⟨{player, other player}, by simp⟩ player ≤
    singleton reward player
  cap_joint : ∀ player, reward ⟨{player, favorite player, other player}, by simp⟩ player ≤
    singleton reward player

private theorem InverseRawSource.premium_nonnegative {reward : Reward}
    (hraw : InverseRawSource reward) (player : Fin 4) : 0 ≤ premium reward player :=
  sub_nonneg.mpr (hraw.participant_ge player)

private theorem InverseRawSource.passive_nonpositive {reward : Reward}
    (hraw : InverseRawSource reward) (player : Fin 4) : passive reward player ≤ 0 :=
  sub_nonpos.mpr (hraw.passive_le player)

private theorem InverseRawSource.scheduled_negative {reward : Reward}
    (hraw : InverseRawSource reward) (player : Fin 4) :
    quittingProjectiveLCPMatrix reward player (scheduled player) < 0 := by
  rw [matrix_entry]
  exact sub_neg.mpr (hraw.scheduled_lt player)

private theorem InverseRawSource.premium_gap {reward : Reward}
    (hraw : InverseRawSource reward) (player : Fin 4) :
    quittingProjectiveLCPMatrix reward player (scheduled player) < premium reward player :=
  (hraw.scheduled_negative player).trans_le (hraw.premium_nonnegative player)


theorem exists_exact_cycle_of_positive_inverse_all_initial {reward : Reward}
    (hraw : InverseRawSource reward) :
    ∃ (q : Fin 4 → ℝ) (hproper : ∀ player, q player ∈ Set.Ioo (0 : ℝ) 1), ∀ initial : Fin 2,
      let profile := quittingCyclicBehaviorProfile reward
        (cycle fin4Schedule q (properUnitBounds q hproper)) initial
      quittingTerminalPayoff reward profile = twoPairPhaseValue reward fin4Schedule q initial ∧
      (quittingGame reward).IsεAsymptoticNash (quittingTerminalPayoff reward) 0 profile ∧
      (∀ ε : ℝ, 0 < ε → ∃ threshold : ℕ, ∀ horizon, threshold ≤ horizon →
        (quittingGame reward).IsεHorizonNash none horizon ε profile ∧
          ∀ player, |(quittingGame reward).finiteAveragePayoff none horizon profile player -
            twoPairPhaseValue reward fin4Schedule q initial player| ≤ ε) ∧
      (quittingGame reward).IsUniformEquilibriumPayoff none
        (twoPairPhaseValue reward fin4Schedule q initial) := by
  have hdiagonal : ∀ player, quittingProjectiveLCPMatrix reward player player = 0 := by
    intro player
    simp only [matrix_entry, singleton, sub_self]
  obtain ⟨point, hpoint, _, hequation⟩ := exists_positive_odds_of_positive_inverse
    (quittingProjectiveLCPMatrix reward) hdiagonal hraw.inverse_positive
    (premium reward) (passive reward) hraw.scheduled_negative
    hraw.premium_nonnegative hraw.passive_nonpositive
  exact ⟨hazard point, hazard_proper hpoint, fun initial =>
    twoPair_exact_terminal_and_fixedProfile reward fin4Schedule (hazard point)
      (hazard_proper hpoint) (passive_continue reward hpoint hequation)
      (passive_quit_of_caps reward hraw.premium_gap hraw.cap_favorite
        hraw.cap_other hraw.cap_joint hpoint) initial⟩

theorem exists_exact_cycle_of_positive_inverse {reward : Reward}
    (hraw : InverseRawSource reward) (initial : Fin 2) :
    ∃ (q : Fin 4 → ℝ) (hproper : ∀ player, q player ∈ Set.Ioo (0 : ℝ) 1),
      let profile := quittingCyclicBehaviorProfile reward
        (cycle fin4Schedule q (properUnitBounds q hproper)) initial
      quittingTerminalPayoff reward profile = twoPairPhaseValue reward fin4Schedule q initial ∧
      (quittingGame reward).IsεAsymptoticNash (quittingTerminalPayoff reward) 0 profile ∧
      (∀ ε : ℝ, 0 < ε → ∃ threshold : ℕ, ∀ horizon, threshold ≤ horizon →
        (quittingGame reward).IsεHorizonNash none horizon ε profile ∧
          ∀ player, |(quittingGame reward).finiteAveragePayoff none horizon profile player -
            twoPairPhaseValue reward fin4Schedule q initial player| ≤ ε) ∧
      (quittingGame reward).IsUniformEquilibriumPayoff none
        (twoPairPhaseValue reward fin4Schedule q initial) := by
  obtain ⟨q, hproper, hprofile⟩ := exists_exact_cycle_of_positive_inverse_all_initial hraw
  exact ⟨q, hproper, hprofile initial⟩

def HasReindexedWeakSource {ι : Type} [Fintype ι] [DecidableEq ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) : Prop :=
  ∃ order : ι ≃ Fin 4, WeakRawSource (quittingRewardReindex order reward)

theorem exists_uniformEquilibriumPayoff_of_reindexed_weak
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hraw : HasReindexedWeakSource reward) :
    ∃ target : Payoff ι, (quittingGame reward).IsUniformEquilibriumPayoff none target := by
  obtain ⟨order, hsource⟩ := hraw
  exact quittingGame_exists_uniformEquilibriumPayoff_of_reindex order reward
    (exists_uniformEquilibriumPayoff_of_weak hsource)

structure ScheduledPairCapSource (reward : Reward) : Prop where
  participant_ge : ∀ player,
    reward (quittingSingletonTerminal (scheduled player)) player ≤
      reward ⟨{player, scheduled player}, by simp⟩ player
  cap_favorite : ∀ player, reward ⟨{player, favorite player}, by simp⟩ player ≤
    singleton reward player
  cap_other : ∀ player, reward ⟨{player, other player}, by simp⟩ player ≤
    singleton reward player
  cap_joint : ∀ player, reward ⟨{player, favorite player, other player}, by simp⟩ player ≤
    singleton reward player

private theorem scheduled_first (phase : Fin 2) :
    scheduled (fin4Schedule.first phase) = fin4Schedule.second phase := by
  rw [← fin4Schedule_partner_eq_scheduled, fin4Schedule.partner_first]

private theorem scheduled_second (phase : Fin 2) :
    scheduled (fin4Schedule.second phase) = fin4Schedule.first phase := by
  rw [← fin4Schedule_partner_eq_scheduled, fin4Schedule.partner_second]

private theorem passive_pair_eq_of_outside (phase : Fin 2) (player : Fin 4)
    (hout : player ∉ fin4Schedule.pair phase) :
    {favorite player, other player} = fin4Schedule.pair phase := by
  fin_cases phase <;> fin_cases player <;>
    simp_all [Schedule.pair, favorite, other, Finset.pair_comm]

theorem isSureExitSet_scheduledPair_of_caps {reward : Reward}
    (hraw : ScheduledPairCapSource reward) (phase : Fin 2)
    (hpassive : ∀ player, player ∉ fin4Schedule.pair phase → 0 ≤ passive reward player) :
    IsQuittingSureExitSet reward (fin4Schedule.pair phase) := by
  change IsQuittingSureExitSet reward
    {fin4Schedule.first phase, fin4Schedule.second phase}
  apply (isQuittingSureExitSet_pair_iff reward (fin4Schedule.first_ne_second phase)).mpr
  refine ⟨?_, ?_, ?_⟩
  · have hfirst := hraw.participant_ge (fin4Schedule.first phase)
    rw [scheduled_first] at hfirst
    simpa only [quittingSoloReward, quittingSingletonCollisionReward,
      quittingSingletonTerminal, Finset.pair_comm]
      using hfirst
  · have hsecond := hraw.participant_ge (fin4Schedule.second phase)
    rw [scheduled_second] at hsecond
    simpa only [quittingSoloReward, quittingSingletonCollisionReward,
      quittingSingletonTerminal, Finset.pair_comm] using hsecond
  · intro player hfirst hsecond
    have hout : player ∉ fin4Schedule.pair phase := by
      simpa only [Schedule.pair, Finset.mem_insert, Finset.mem_singleton, not_or] using
        And.intro hfirst hsecond
    have hpair := passive_pair_eq_of_outside phase player hout
    have hnonnegative := hpassive player hout
    have hcap := hraw.cap_joint player
    have hterminal : (⟨{favorite player, other player}, by simp⟩ :
        {S : Finset (Fin 4) // S.Nonempty}) =
        ⟨fin4Schedule.pair phase, fin4Schedule.pair_nonempty phase⟩ :=
      Subtype.ext hpair
    have hinsert : (⟨{player, favorite player, other player}, by simp⟩ :
        {S : Finset (Fin 4) // S.Nonempty}) =
        ⟨insert player (fin4Schedule.pair phase), Finset.insert_nonempty _ _⟩ := by
      apply Subtype.ext
      exact congrArg (fun coalition : Finset (Fin 4) => insert player coalition) hpair
    unfold passive at hnonnegative
    rw [hterminal] at hnonnegative
    rw [hinsert] at hcap
    change quittingSetReward reward (insert player (fin4Schedule.pair phase)) player ≤
      quittingSetReward reward (fin4Schedule.pair phase) player
    rw [quittingSetReward_of_nonempty reward (Finset.insert_nonempty _ _),
      quittingSetReward_of_nonempty reward (fin4Schedule.pair_nonempty phase)]
    linarith

theorem scheduledPair_oneDate_exactHorizon {reward : Reward}
    (hraw : ScheduledPairCapSource reward) (phase : Fin 2)
    (hpassive : ∀ player, player ∉ fin4Schedule.pair phase → 0 ≤ passive reward player)
    (horizon : ℕ) :
    (quittingGame reward).IsεHorizonNash none horizon 0
      (quittingOneDateThenNeverProfile reward (quittingPureSetRoot (fin4Schedule.pair phase))) :=
  oneDateThenNever_exactHorizon_of_sureExitSet reward (fin4Schedule.pair phase)
    (by simp [Schedule.pair, fin4Schedule.first_ne_second])
    (isSureExitSet_scheduledPair_of_caps hraw phase hpassive) horizon

/-- The same one-date pure pair gives its actual reward and exact Nash at every horizon. -/
theorem scheduledPair_exact_profile {reward : Reward}
    (hraw : ScheduledPairCapSource reward) (phase : Fin 2)
    (hpassive : ∀ player, player ∉ fin4Schedule.pair phase → 0 ≤ passive reward player) :
    let profile := quittingOneDateThenNeverProfile reward
      (quittingPureSetRoot (fin4Schedule.pair phase))
    quittingTerminalPayoff reward profile = quittingSetReward reward (fin4Schedule.pair phase) ∧
    (quittingGame reward).IsεAsymptoticNash (quittingTerminalPayoff reward) 0 profile ∧
    (∀ horizon, (quittingGame reward).IsεHorizonNash none horizon 0 profile) ∧
    (∀ accuracy : ℝ, 0 < accuracy → ∃ threshold : ℕ,
      ∀ horizon : ℕ, threshold ≤ horizon →
        (quittingGame reward).IsεHorizonNash none horizon accuracy profile ∧
          ∀ player, |(quittingGame reward).finiteAveragePayoff none horizon profile player -
            quittingSetReward reward (fin4Schedule.pair phase) player| ≤ accuracy) ∧
    (quittingGame reward).IsUniformEquilibriumPayoff none
      (quittingSetReward reward (fin4Schedule.pair phase)) := by
  have hsure := isSureExitSet_scheduledPair_of_caps hraw phase hpassive
  have hcard : 2 ≤ (fin4Schedule.pair phase).card := by
    simp [Schedule.pair, fin4Schedule.first_ne_second]
  have hpayoff := oneDateThenNever_payoff_of_nonempty reward (fin4Schedule.pair phase)
    (fin4Schedule.pair_nonempty phase)
  refine ⟨hpayoff, oneDateThenNever_terminalNash_of_sureExitSet reward _ hcard hsure,
    scheduledPair_oneDate_exactHorizon hraw phase hpassive, ?_,
    isUniformEquilibriumPayoff_setReward_of_isQuittingSureExitSet reward hsure⟩
  simpa only [hpayoff] using
    oneDateThenNever_sameProfile_of_sureExitSet reward (fin4Schedule.pair phase) hcard hsure

theorem exists_uniformEquilibriumPayoff_of_positive_inverse {reward : Reward}
    (hraw : InverseRawSource reward) :
    ∃ target : Payoff (Fin 4), (quittingGame reward).IsUniformEquilibriumPayoff none target := by
  obtain ⟨q, hproper, _, _, _, hUE⟩ := exists_exact_cycle_of_positive_inverse hraw 0
  exact ⟨twoPairPhaseValue reward fin4Schedule q 0, hUE⟩

def HasReindexedStrictSource {ι : Type} [Fintype ι] [DecidableEq ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) : Prop :=
  ∃ order : ι ≃ Fin 4, RawSource (quittingRewardReindex order reward)

def HasReindexedInverseSource {ι : Type} [Fintype ι] [DecidableEq ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) : Prop :=
  ∃ order : ι ≃ Fin 4, InverseRawSource (quittingRewardReindex order reward)

theorem exists_uniformEquilibriumPayoff_of_reindexed_strict
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (hraw : HasReindexedStrictSource reward) :
    ∃ target : Payoff ι, (quittingGame reward).IsUniformEquilibriumPayoff none target := by
  obtain ⟨order, hsource⟩ := hraw
  exact quittingGame_exists_uniformEquilibriumPayoff_of_reindex order reward
    (exists_uniformEquilibriumPayoff hsource)

theorem exists_uniformEquilibriumPayoff_of_reindexed_inverse
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (hraw : HasReindexedInverseSource reward) :
    ∃ target : Payoff ι, (quittingGame reward).IsUniformEquilibriumPayoff none target := by
  obtain ⟨order, hsource⟩ := hraw
  exact quittingGame_exists_uniformEquilibriumPayoff_of_reindex order reward
    (exists_uniformEquilibriumPayoff_of_positive_inverse hsource)

end GameTheory.PairedCycle.CrossedMatching
