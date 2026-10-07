import MathUE.LinearProgramming.CrossedMatchingPositiveOdds
import UniformEquilibrium.Quitting.Cycles.TwoPairOddsValues
import UniformEquilibrium.Quitting.Projective.FinFourAmbientQSimplex
import UniformEquilibrium.Quitting.Terminal.TerminalExploitabilityRewardRobustness

/-! # Actual crossed-matching two-pair phases

The literal reward comparisons produce positive odds and all passive endpoint
tests internally. Singleton levels, participant increments and passive pair
entries may be signed. One fixed profile supplies the target and approximate
Nash bounds at every accuracy over sufficiently long horizons.
-/

noncomputable section

namespace GameTheory.PairedCycle.CrossedMatching

open Math.CrossedMatching Math.PairedAffine Math.LinearProgramming

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


theorem passive_quit {reward : Reward} (hraw : RawSource reward)
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
      (hraw.cap_favorite player) (hraw.cap_other player) (hraw.cap_joint player) le_rfl)
    exact (postValue_gt_singleton hraw hpoint player).le
  · fin_cases player <;> decide

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
  obtain ⟨point, hpoint, _, hequation⟩ := exists_positive_odds_of_matching_standardQ
    (quittingProjectiveLCPMatrix reward) hraw.matchingSigns hQ (premium reward) (passive reward)
    hraw.premium_gt
  exact ⟨hazard point, hazard_proper hpoint,
    twoPair_exact_terminal_and_fixedProfile reward fin4Schedule (hazard point)
      (hazard_proper hpoint) (passive_continue reward hpoint hequation)
      (passive_quit hraw hpoint) initial⟩

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

end GameTheory.PairedCycle.CrossedMatching
