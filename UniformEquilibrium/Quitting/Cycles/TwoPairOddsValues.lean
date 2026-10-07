import MathUE.LinearProgramming.CrossedMatchingOdds
import UniformEquilibrium.Quitting.Cycles.TwoPairExactCertificate
import UniformEquilibrium.Quitting.Projective.SingletonLCP

/-! # Actual two-pair values and odds equations

These formulas use the complete raw reward table and independent positive odds.
No matching sign, participant increment, singleton floor, joining cap, matrix
inverse or equilibrium hypothesis is assumed.
-/

noncomputable section

namespace GameTheory.PairedCycle.TwoPairOdds

open Math.CrossedMatching Math.PairedAffine

abbrev Reward := {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)

def premium (reward : Reward) (player : Fin 4) : ℝ :=
  reward ⟨{player, scheduled player}, by simp⟩ player - singleton reward player

def passive (reward : Reward) (player : Fin 4) : ℝ :=
  reward ⟨{favorite player, other player}, by simp⟩ player - singleton reward player

theorem matrix_entry (reward : Reward) (player owner : Fin 4) :
    quittingProjectiveLCPMatrix reward player owner =
      reward (quittingSingletonTerminal owner) player - singleton reward player := by
  rfl

private theorem jointReward_eq (reward : Reward) (player : Fin 4) :
    jointReward reward fin4Schedule player = singleton reward player + premium reward player := by
  have hterminal : (⟨fin4Schedule.pair (fin4Schedule.phase player),
      fin4Schedule.pair_nonempty _⟩ : {S : Finset (Fin 4) // S.Nonempty}) =
      ⟨{player, scheduled player}, by simp⟩ := by
    apply Subtype.ext
    change fin4Schedule.pair (fin4Schedule.phase player) = {player, scheduled player}
    rw [fin4Schedule.pair_phase_eq, fin4Schedule_partner_eq_scheduled]
  unfold jointReward
  rw [hterminal]
  unfold premium
  ring

def hazard (point : Fin 4 → ℝ) (player : Fin 4) : ℝ :=
  point player / (1 + point player)

theorem hazard_proper {point : Fin 4 → ℝ} (hpoint : ∀ player, 0 < point player) :
    ∀ player, hazard point player ∈ Set.Ioo (0 : ℝ) 1 := by
  intro player
  have hdenom : 0 < 1 + point player := by linarith [hpoint player]
  constructor
  · exact div_pos (hpoint player) hdenom
  · exact (div_lt_one hdenom).mpr (by linarith)

theorem activeValue_eq (reward : Reward) (point : Fin 4 → ℝ) (player : Fin 4) :
    twoPairActiveValue reward fin4Schedule (hazard point) player =
      singleton reward player + premium reward player * hazard point (scheduled player) := by
  unfold twoPairActiveValue activeValue
  rw [jointReward_eq, fin4Schedule_partner_eq_scheduled]
  ring

theorem postValue_eq (reward : Reward) {point : Fin 4 → ℝ}
    (hpoint : ∀ player, 0 < point player) (player : Fin 4) :
    twoPairPostValue reward fin4Schedule (hazard point) player =
      singleton reward player +
        (premium reward player - quittingProjectiveLCPMatrix reward player (scheduled player)) *
          point (scheduled player) := by
  unfold twoPairPostValue postValue partnerReward
  rw [jointReward_eq, fin4Schedule_partner_eq_scheduled, matrix_entry]
  unfold hazard
  have hdenom : 1 + point (scheduled player) ≠ 0 := by linarith [hpoint (scheduled player)]
  field_simp
  ring

private theorem passive_equation_identity (reward : Reward) {point : Fin 4 → ℝ}
    (hpoint : ∀ player, 0 < point player) (player : Fin 4) :
    passiveEquation (quittingProjectiveLCPMatrix reward) (premium reward)
        (passive reward) point player =
      (1 + point (favorite player)) * (1 + point (other player)) *
        (twoPairPostValue reward fin4Schedule (hazard point) player -
          bellman (reward (quittingSingletonTerminal (favorite player)) player)
            (reward (quittingSingletonTerminal (other player)) player)
            (reward ⟨{favorite player, other player}, by simp⟩ player)
            (hazard point (favorite player)) (hazard point (other player))
            (twoPairActiveValue reward fin4Schedule (hazard point) player)) := by
  rw [postValue_eq reward hpoint, activeValue_eq]
  unfold passiveEquation passive hazard bellman contribution
  simp only [matrix_entry]
  have ha : 1 + point (scheduled player) ≠ 0 := by linarith [hpoint (scheduled player)]
  have hf : 1 + point (favorite player) ≠ 0 := by linarith [hpoint (favorite player)]
  have ho : 1 + point (other player) ≠ 0 := by linarith [hpoint (other player)]
  field_simp
  ring

/-- The literal odds equation is the scaled actual passive Continue deficit. -/
theorem passiveEquation_eq_scaled_post_sub_continue (reward : Reward)
    {point : Fin 4 → ℝ} (hpoint : ∀ player, 0 < point player) (player : Fin 4) :
    passiveEquation (quittingProjectiveLCPMatrix reward) (premium reward)
        (passive reward) point player =
      (1 + point (favorite player)) * (1 + point (other player)) *
        (twoPairPostValue reward fin4Schedule (hazard point) player -
          quittingRootContinuePayoff reward
            (twoPairPhaseValue reward fin4Schedule (hazard point) (fin4Schedule.phase player))
            (cycle fin4Schedule (hazard point) (properUnitBounds _ (hazard_proper hpoint))
              (finRotate 2 (fin4Schedule.phase player))) player) := by
  rw [fin4Schedule_passive_root, rootContinue_outside]
  · simp only [quittingHazardCoin_true_toReal, twoPairPhaseValue_active]
    exact passive_equation_identity reward hpoint player
  · fin_cases player <;> decide
  · fin_cases player <;> decide
  · fin_cases player <;> decide

theorem passive_continue (reward : Reward) {point : Fin 4 → ℝ}
    (hpoint : ∀ player, 0 < point player)
    (hequation : ∀ player, passiveEquation (quittingProjectiveLCPMatrix reward)
      (premium reward) (passive reward) point player = 0) (player : Fin 4) :
    quittingRootContinuePayoff reward
      (twoPairPhaseValue reward fin4Schedule (hazard point) (fin4Schedule.phase player))
      (cycle fin4Schedule (hazard point) (properUnitBounds _ (hazard_proper hpoint))
        (finRotate 2 (fin4Schedule.phase player))) player =
      twoPairPostValue reward fin4Schedule (hazard point) player := by
  rw [fin4Schedule_passive_root, rootContinue_outside]
  · simp only [quittingHazardCoin_true_toReal, twoPairPhaseValue_active]
    have hzero := hequation player
    rw [passive_equation_identity reward hpoint player] at hzero
    have hf : 0 < 1 + point (favorite player) := by linarith [hpoint (favorite player)]
    have ho : 0 < 1 + point (other player) := by linarith [hpoint (other player)]
    have hdifference := (mul_eq_zero.mp hzero).resolve_left (mul_pos hf ho).ne'
    exact (sub_eq_zero.mp hdifference).symm
  · fin_cases player <;> decide
  · fin_cases player <;> decide
  · fin_cases player <;> decide

end GameTheory.PairedCycle.TwoPairOdds
