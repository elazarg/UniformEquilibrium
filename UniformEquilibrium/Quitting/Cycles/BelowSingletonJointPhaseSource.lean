import MathUE.PairedBelowSingletonScalar
import MathUE.LinearProgramming.CrossedMatchingMaps
import UniformEquilibrium.Quitting.Cycles.TwoPairExactCertificate

/-! # A raw signed two-pair producer below the singleton levels

The actual table supplies singleton and scheduled-pair identities and twelve
passive joining caps. The selected scalar root and both phase endpoint tests
are produced internally. Own-singleton levels and all unmentioned collisions
are unrestricted.
-/

noncomputable section

namespace GameTheory.PairedCycle.BelowSingleton

open Math.CrossedMatching Math.PairedAffine

abbrev Reward := {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)

/-- Only literal reward comparisons and scalar inequalities are input data. -/
structure RawFamily (reward : Reward) (scale : Fin 4 → ℝ)
    (favorable premium passive : ℝ) : Prop where
  scale_pos : ∀ player, 0 < scale player
  favorable_gt : 2 < favorable
  premium_lt : premium < -1
  passive_lt : passive < (7 * premium + 10 - 2 * favorable) / 2
  favorite_singleton : ∀ player,
    reward (quittingSingletonTerminal (favorite player)) player =
      singleton reward player + favorable * scale player
  scheduled_singleton : ∀ player,
    reward (quittingSingletonTerminal (scheduled player)) player =
      singleton reward player - scale player
  other_singleton : ∀ player,
    reward (quittingSingletonTerminal (other player)) player =
      singleton reward player - scale player
  active_pair : ∀ player,
    reward ⟨{player, scheduled player}, by simp⟩ player =
      singleton reward player + premium * scale player
  passive_pair : ∀ player,
    reward ⟨{favorite player, other player}, by simp⟩ player =
      singleton reward player + passive * scale player
  cap_favorite : ∀ player,
    reward ⟨{player, favorite player}, by simp⟩ player ≤
      singleton reward player - (4 * (-premium - 1) / 3) * scale player
  cap_other : ∀ player,
    reward ⟨{player, other player}, by simp⟩ player ≤
      singleton reward player - (4 * (-premium - 1) / 3) * scale player
  cap_joint : ∀ player,
    reward ⟨{player, favorite player, other player}, by simp⟩ player ≤
      singleton reward player - (4 * (-premium - 1) / 3) * scale player

private theorem phase_one : fin4Schedule.phase 1 = 1 := by
  exact fin4Schedule.phase_first 1

private theorem phase_two : fin4Schedule.phase 2 = 0 := by
  exact fin4Schedule.phase_second 0

private theorem phase_three : fin4Schedule.phase 3 = 1 := by
  exact fin4Schedule.phase_second 1

private theorem partner_eq_scheduled (player : Fin 4) :
    fin4Schedule.partner player = scheduled player := by
  fin_cases player
  · exact fin4Schedule.partner_first 0
  · exact fin4Schedule.partner_first 1
  · exact fin4Schedule.partner_second 0
  · exact fin4Schedule.partner_second 1

private theorem passive_root (q : ℝ) (hq : q ∈ Set.Icc (0 : ℝ) 1)
    (player : Fin 4) :
    cycle fin4Schedule (fun _ => q) (fun _ => hq)
        (finRotate 2 (fin4Schedule.phase player)) =
      root (favorite player) (other player)
        (quittingHazardCoin q hq.1 hq.2) (quittingHazardCoin q hq.1 hq.2) := by
  fin_cases player
  · change cycle fin4Schedule (fun _ => q) (fun _ => hq)
        (finRotate 2 (fin4Schedule.phase (0 : Fin 4))) = root (1 : Fin 4) 3 _ _
    rw [fin4Schedule_phase_zero]
    rfl
  · change cycle fin4Schedule (fun _ => q) (fun _ => hq)
        (finRotate 2 (fin4Schedule.phase (1 : Fin 4))) = root (0 : Fin 4) 2 _ _
    rw [phase_one]
    rfl
  · change cycle fin4Schedule (fun _ => q) (fun _ => hq)
        (finRotate 2 (fin4Schedule.phase (2 : Fin 4))) = root (3 : Fin 4) 1 _ _
    rw [phase_two]
    exact root_swap (by decide : (1 : Fin 4) ≠ 3) _ _
  · change cycle fin4Schedule (fun _ => q) (fun _ => hq)
        (finRotate 2 (fin4Schedule.phase (3 : Fin 4))) = root (2 : Fin 4) 0 _ _
    rw [phase_three]
    exact root_swap (by decide : (0 : Fin 4) ≠ 2) _ _

private theorem jointReward_eq {reward : Reward} {scale : Fin 4 → ℝ}
    {favorable premium passive : ℝ} (hraw : RawFamily reward scale favorable premium passive)
    (player : Fin 4) :
    jointReward reward fin4Schedule player =
      singleton reward player + premium * scale player := by
  unfold jointReward
  have hterminal : (⟨fin4Schedule.pair (fin4Schedule.phase player),
      fin4Schedule.pair_nonempty _⟩ : {S : Finset (Fin 4) // S.Nonempty}) =
      ⟨{player, scheduled player}, by simp⟩ := by
    apply Subtype.ext
    change fin4Schedule.pair (fin4Schedule.phase player) = {player, scheduled player}
    rw [fin4Schedule.pair_phase_eq, partner_eq_scheduled]
  rw [hterminal, hraw.active_pair]

theorem activeValue_eq {reward : Reward} {scale : Fin 4 → ℝ}
    {favorable premium passive : ℝ} (hraw : RawFamily reward scale favorable premium passive)
    (t : ℝ) (player : Fin 4) :
    twoPairActiveValue reward fin4Schedule (fun _ => 1 - t) player =
      singleton reward player + (1 - t) * premium * scale player := by
  unfold twoPairActiveValue activeValue
  rw [jointReward_eq hraw]
  ring

theorem postValue_eq {reward : Reward} {scale : Fin 4 → ℝ}
    {favorable premium passive : ℝ} (hraw : RawFamily reward scale favorable premium passive)
    (t : ℝ) (player : Fin 4) :
    twoPairPostValue reward fin4Schedule (fun _ => 1 - t) player =
      singleton reward player + (1 - t) * (premium + 1) * scale player / t := by
  unfold twoPairPostValue postValue
  rw [jointReward_eq hraw]
  unfold partnerReward
  rw [partner_eq_scheduled, hraw.scheduled_singleton]
  ring

theorem passive_continue {reward : Reward} {scale : Fin 4 → ℝ}
    {favorable premium passive t : ℝ}
    (hraw : RawFamily reward scale favorable premium passive)
    (ht : t ∈ Set.Ioo (1 / 2 : ℝ) 1)
    (hroot : Math.PairedBelowSingleton.polynomial favorable premium passive t = 0)
    (player : Fin 4) :
    quittingRootContinuePayoff reward
        (twoPairPhaseValue reward fin4Schedule (fun _ => 1 - t) (fin4Schedule.phase player))
        (cycle fin4Schedule (fun _ => 1 - t)
          (properUnitBounds _ (fun _ => ⟨by linarith [ht.2], by linarith [ht.1]⟩))
          (finRotate 2 (fin4Schedule.phase player))) player =
      twoPairPostValue reward fin4Schedule (fun _ => 1 - t) player := by
  rw [passive_root (1 - t) ⟨by linarith [ht.2], by linarith [ht.1]⟩ player]
  have hne : favorite player ≠ other player := by fin_cases player <;> decide
  have hfirst : player ≠ favorite player := by fin_cases player <;> decide
  have hsecond : player ≠ other player := by fin_cases player <;> decide
  rw [rootContinue_outside reward _ hne hfirst hsecond,
    quittingHazardCoin_true_toReal,
    hraw.favorite_singleton, hraw.other_singleton, hraw.passive_pair,
    twoPairPhaseValue_active, activeValue_eq hraw, postValue_eq hraw]
  have hidentity := Math.PairedBelowSingleton.passive_continue_identity
    (by linarith [ht.1] : 0 < t) hroot
  unfold bellman contribution
  calc
    _ = singleton reward player + scale player *
        ((1 - t) * t * (favorable - 1) + (1 - t) ^ 2 * passive +
          t ^ 2 * (1 - t) * premium) := by ring
    _ = _ := by rw [hidentity]; ring

theorem passive_quit_lt {reward : Reward} {scale : Fin 4 → ℝ}
    {favorable premium passive t : ℝ}
    (hraw : RawFamily reward scale favorable premium passive)
    (ht : t ∈ Set.Ioo (1 / 2 : ℝ) 1) (player : Fin 4) :
    quittingRootQuitPayoff reward
        (twoPairPhaseValue reward fin4Schedule (fun _ => 1 - t) (fin4Schedule.phase player))
        (cycle fin4Schedule (fun _ => 1 - t)
          (properUnitBounds _ (fun _ => ⟨by linarith [ht.2], by linarith [ht.1]⟩))
          (finRotate 2 (fin4Schedule.phase player))) player <
      twoPairPostValue reward fin4Schedule (fun _ => 1 - t) player := by
  rw [passive_root (1 - t) ⟨by linarith [ht.2], by linarith [ht.1]⟩ player]
  have hne : favorite player ≠ other player := by fin_cases player <;> decide
  rw [rootQuit_eq_bellman reward _ hne, quittingHazardCoin_true_toReal, postValue_eq hraw]
  apply lt_of_le_of_lt _ (Math.PairedBelowSingleton.passive_cap_lt_post
    (singleton reward player) hraw.premium_lt ht (hraw.scale_pos player))
  have hqt : 0 ≤ (1 - t) * t := mul_nonneg (by linarith [ht.2]) (by linarith [ht.1])
  have hqq : 0 ≤ (1 - t) * (1 - t) := mul_self_nonneg _
  have hleft := mul_le_mul_of_nonneg_left (hraw.cap_favorite player) hqt
  have hright := mul_le_mul_of_nonneg_left (hraw.cap_other player) hqt
  have hjoint := mul_le_mul_of_nonneg_left (hraw.cap_joint player) hqq
  unfold bellman contribution singleton
  dsimp only [singleton] at hleft hright hjoint
  nlinarith [hleft, hright, hjoint]

theorem phaseValue_lt_singleton {reward : Reward} {scale : Fin 4 → ℝ}
    {favorable premium passive t : ℝ}
    (hraw : RawFamily reward scale favorable premium passive)
    (ht : t ∈ Set.Ioo (1 / 2 : ℝ) 1) (phase : Fin 2) (player : Fin 4) :
    twoPairPhaseValue reward fin4Schedule (fun _ => 1 - t) phase player <
      singleton reward player := by
  unfold twoPairPhaseValue
  split_ifs
  · rw [activeValue_eq hraw]
    have hnegative : (1 - t) * premium * scale player < 0 :=
      mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (by linarith [ht.2])
        (by linarith [hraw.premium_lt])) (hraw.scale_pos player)
    linarith
  · rw [postValue_eq hraw]
    have hnegative : (1 - t) * (premium + 1) * scale player / t < 0 :=
      div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos
        (mul_neg_of_pos_of_neg (by linarith [ht.2]) (by linarith [hraw.premium_lt]))
        (hraw.scale_pos player)) (by linarith [ht.1])
    linarith

/-- The actual periodic profile produced at a selected scalar root. -/
def profile (reward : Reward) (t : ℝ) (ht : t ∈ Set.Ioo (1 / 2 : ℝ) 1) :
    (quittingGame reward).BehaviorProfile :=
  quittingCyclicBehaviorProfile reward
    (cycle fin4Schedule (fun _ => 1 - t)
      (properUnitBounds _ (fun _ => ⟨by linarith [ht.2], by linarith [ht.1]⟩))) 0

/-- Literal reward data produce one proper profile, one target and the same
profile as the finite-horizon witness at every positive accuracy. -/
theorem exists_exact_terminal_and_fixedProfile_of_rawFamily
    {reward : Reward} {scale : Fin 4 → ℝ} {favorable premium passive : ℝ}
    (hraw : RawFamily reward scale favorable premium passive) :
    ∃ t : ℝ, ∃ ht : t ∈ Set.Ioo (1 / 2 : ℝ) 1,
      Math.PairedBelowSingleton.polynomial favorable premium passive t = 0 ∧
      (∀ phase player,
        twoPairPhaseValue reward fin4Schedule (fun _ => 1 - t) phase player <
          singleton reward player) ∧
      quittingTerminalPayoff reward (profile reward t ht) =
        twoPairPhaseValue reward fin4Schedule (fun _ => 1 - t) 0 ∧
      (quittingGame reward).IsεAsymptoticNash (quittingTerminalPayoff reward) 0
        (profile reward t ht) ∧
      (∀ ε : ℝ, 0 < ε → ∃ threshold : ℕ,
        ∀ horizon, threshold ≤ horizon →
          (quittingGame reward).IsεHorizonNash none horizon ε (profile reward t ht) ∧
            ∀ player, |(quittingGame reward).finiteAveragePayoff none horizon
                (profile reward t ht) player -
              twoPairPhaseValue reward fin4Schedule (fun _ => 1 - t) 0 player| ≤ ε) ∧
      (quittingGame reward).IsUniformEquilibriumPayoff none
        (twoPairPhaseValue reward fin4Schedule (fun _ => 1 - t) 0) := by
  obtain ⟨t, ht, hroot⟩ := Math.PairedBelowSingleton.exists_selected_root
    hraw.favorable_gt hraw.passive_lt
  refine ⟨t, ht, hroot, phaseValue_lt_singleton hraw ht, ?_⟩
  exact twoPair_exact_terminal_and_fixedProfile reward fin4Schedule (fun _ => 1 - t)
    (fun _ => ⟨by linarith [ht.2], by linarith [ht.1]⟩)
    (passive_continue hraw ht hroot) (fun player => (passive_quit_lt hraw ht player).le) 0

/-- The fixed payoff conclusion retains unrestricted singleton signs. -/
theorem exists_uniformEquilibriumPayoff_of_rawFamily
    {reward : Reward} {scale : Fin 4 → ℝ} {favorable premium passive : ℝ}
    (hraw : RawFamily reward scale favorable premium passive) :
    ∃ target, (quittingGame reward).IsUniformEquilibriumPayoff none target := by
  obtain ⟨t, _, _, _, _, _, _, hpayoff⟩ :=
    exists_exact_terminal_and_fixedProfile_of_rawFamily hraw
  exact ⟨twoPairPhaseValue reward fin4Schedule (fun _ => 1 - t) 0, hpayoff⟩

end GameTheory.PairedCycle.BelowSingleton
