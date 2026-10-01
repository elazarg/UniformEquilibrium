import UniformEquilibrium.Quitting.Paths.FiniteUnpreemptedSoloExit

/-! # Sharp finite solo truncation of an exact stationary exit

All caps are actual unrestricted behavioral caps. Only the selected owner's
own singleton needs to be nonnegative; outsider singleton and solo payoffs
may be signed. The tail is literally Always Continue.
-/

noncomputable section

namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem quittingTerminalSemanticPair_alwaysContinue_eq_neverBoundary
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    quittingTerminalSemanticPair reward (quittingAlwaysContinueProfile reward) =
      quittingNeverBoundarySemanticPair reward := by
  apply Prod.ext
  · funext who
    exact quittingTerminalPayoff_quittingAlwaysContinue reward who
  · funext who
    exact quittingContinuationBestResponseValue_quittingAlwaysContinueProfile reward who

/-- Literal repeated solo/Never payoff, independent of strategic inequalities. -/
theorem quittingTerminalPayoff_replicate_solo_never_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner who : ι) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (steps : ℕ) :
    quittingTerminalPayoff reward
      (quittingLiteralRootStackProfile reward
        (List.replicate steps (quittingSoloStationaryRoot owner
          (quittingHazardCoin t ht0 ht1))) (quittingAlwaysContinueProfile reward)) who =
      (1 - (1 - t) ^ steps) * reward (quittingSingletonTerminal owner) who := by
  have hequal := quittingTerminalSemanticPair_replicate_solo_word
    reward owner (quittingHazardCoin t ht0 ht1) (quittingAlwaysContinueProfile reward) steps
  rw [quittingTerminalSemanticPair_alwaysContinue_eq_neverBoundary] at hequal
  have hpayoff := congrArg (fun pair => pair.1 who) hequal
  change quittingTerminalPayoff reward _ who = _ at hpayoff
  exact hpayoff.trans (quittingSoloSemanticIterate_never_payoff
    reward owner who ht0 ht1 steps)

/-- Exact inactive inequalities remove the fixed one-row hazard surcharge
from the finite solo cap bound. -/
theorem quittingSoloSemanticIterate_never_other_cap_le_max
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hunpreempted : ∀ who, who ≠ owner →
      reward (quittingSingletonTerminal who) who ≤
        reward (quittingSingletonTerminal owner) who)
    (hinactive : ∀ who, who ≠ owner →
      (1 - t) * reward (quittingSingletonTerminal who) who +
        t * quittingSingletonCollisionReward reward owner who ≤
          reward (quittingSingletonTerminal owner) who)
    {who : ι} (hne : who ≠ owner) :
    ∀ steps,
      (quittingSoloSemanticIterate reward owner
        (quittingHazardCoin t ht0 ht1)
        (quittingNeverBoundarySemanticPair reward) steps).2 who ≤
      max (reward (quittingSingletonTerminal owner) who)
        ((1 - (1 - t) ^ steps) *
          reward (quittingSingletonTerminal owner) who) := by
  let a := reward (quittingSingletonTerminal owner) who
  have hρ : 0 ≤ 1 - t := sub_nonneg.mpr ht1
  intro steps
  induction steps with
  | zero =>
      simp only [quittingSoloSemanticIterate_zero, quittingNeverBoundarySemanticPair,
        pow_zero, sub_self, zero_mul]
      exact max_le (le_max_right _ _) ((hunpreempted who hne).trans (le_max_left _ _))
  | succ steps ih =>
      rw [quittingSoloSemanticIterate_succ]
      unfold quittingTerminalSemanticPrefix
      dsimp only
      rw [quittingRootQuitPayoff_soloStationaryRoot_other reward hne,
        quittingRootContinuePayoff_soloStationaryRoot_other reward hne,
        quittingHazardCoin_true_toReal, quittingHazardCoin_false_toReal,
        Function.update_self, pow_succ]
      change max ((1 - t) * reward (quittingSingletonTerminal who) who +
          t * quittingSingletonCollisionReward reward owner who)
          (t * a + (1 - t) * _) ≤
        max a ((1 - (1 - t) ^ steps * (1 - t)) * a)
      apply max_le
      · exact (hinactive who hne).trans (le_max_left _ _)
      · have hscaled := add_le_add_right (mul_le_mul_of_nonneg_left ih hρ) (t * a)
        have hmax :
            t * a + (1 - t) * max a ((1 - (1 - t) ^ steps) * a) =
              max a ((1 - (1 - t) ^ steps * (1 - t)) * a) := by
          rw [mul_max_of_nonneg _ _ hρ, ← max_add_add_left]
          congr 1 <;> ring
        exact hscaled.trans_eq hmax

/-- The finite word retains its actual payoff and a sharp full cap. -/
theorem quittingTerminalSemanticPair_replicate_solo_never_sharp
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (howner : 0 ≤ reward (quittingSingletonTerminal owner) owner)
    (hunpreempted : ∀ who, who ≠ owner →
      reward (quittingSingletonTerminal who) who ≤
        reward (quittingSingletonTerminal owner) who)
    (hinactive : ∀ who, who ≠ owner →
      (1 - t) * reward (quittingSingletonTerminal who) who +
        t * quittingSingletonCollisionReward reward owner who ≤
          reward (quittingSingletonTerminal owner) who)
    (steps : ℕ) :
    let profile := quittingLiteralRootStackProfile reward
      (List.replicate steps (quittingSoloStationaryRoot owner
        (quittingHazardCoin t ht0 ht1))) (quittingAlwaysContinueProfile reward)
    (∀ who, quittingTerminalPayoff reward profile who =
      (1 - (1 - t) ^ steps) * reward (quittingSingletonTerminal owner) who) ∧
    quittingContinuationBestResponseValue reward profile owner =
      reward (quittingSingletonTerminal owner) owner ∧
    (∀ who, quittingContinuationBestResponseValue reward profile who ≤
      max (reward (quittingSingletonTerminal owner) who)
        ((1 - (1 - t) ^ steps) * reward (quittingSingletonTerminal owner) who)) := by
  dsimp only
  have hequal := quittingTerminalSemanticPair_replicate_solo_word
    reward owner (quittingHazardCoin t ht0 ht1)
    (quittingAlwaysContinueProfile reward) steps
  rw [quittingTerminalSemanticPair_alwaysContinue_eq_neverBoundary] at hequal
  refine ⟨?_, ?_, ?_⟩
  · intro who
    have hpayoff := congrArg (fun pair => pair.1 who) hequal
    change quittingTerminalPayoff reward _ who = _ at hpayoff
    exact hpayoff.trans
      (quittingSoloSemanticIterate_never_payoff reward owner who ht0 ht1 steps)
  · have hcap := congrArg (fun pair => pair.2 owner) hequal
    change quittingContinuationBestResponseValue reward _ owner = _ at hcap
    exact hcap.trans
      (quittingSoloSemanticIterate_never_owner_cap reward owner ht0 ht1 howner steps)
  · intro who
    have hcap := congrArg (fun pair => pair.2 who) hequal
    change quittingContinuationBestResponseValue reward _ who = _ at hcap
    rw [hcap]
    by_cases hwho : who = owner
    · subst who
      rw [quittingSoloSemanticIterate_never_owner_cap reward owner ht0 ht1 howner steps]
      exact le_max_left _ _
    · exact quittingSoloSemanticIterate_never_other_cap_le_max
        reward owner ht0 ht1 hunpreempted hinactive hwho steps

/-- Sharp coordinate regret, with no sign assumption on any outsider payoff. -/
theorem quittingTerminalSemanticDebt_replicate_solo_never_sharp_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner who : ι) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (howner : 0 ≤ reward (quittingSingletonTerminal owner) owner)
    (hunpreempted : ∀ player, player ≠ owner →
      reward (quittingSingletonTerminal player) player ≤
        reward (quittingSingletonTerminal owner) player)
    (hinactive : ∀ player, player ≠ owner →
      (1 - t) * reward (quittingSingletonTerminal player) player +
        t * quittingSingletonCollisionReward reward owner player ≤
          reward (quittingSingletonTerminal owner) player)
    (steps : ℕ) :
    let profile := quittingLiteralRootStackProfile reward
      (List.replicate steps (quittingSoloStationaryRoot owner
        (quittingHazardCoin t ht0 ht1))) (quittingAlwaysContinueProfile reward)
    quittingTerminalSemanticDebt (quittingTerminalSemanticPair reward profile) who ≤
      (1 - t) ^ steps * max (reward (quittingSingletonTerminal owner) who) 0 := by
  dsimp only
  obtain ⟨hpayoff, _, hcap⟩ := quittingTerminalSemanticPair_replicate_solo_never_sharp
    reward owner ht0 ht1 howner hunpreempted hinactive steps
  have hbound := hcap who
  have hρ : 0 ≤ (1 - t) ^ steps := pow_nonneg (sub_nonneg.mpr ht1) _
  change quittingContinuationBestResponseValue reward _ who -
      quittingTerminalPayoff reward _ who ≤ _
  rw [hpayoff who]
  apply (sub_le_sub_right hbound _).trans
  apply (sub_le_iff_le_add).mpr
  by_cases ha : 0 ≤ reward (quittingSingletonTerminal owner) who
  · rw [max_eq_left ha]
    apply max_le
    · nlinarith
    · nlinarith
  · have ha' : reward (quittingSingletonTerminal owner) who ≤ 0 := (lt_of_not_ge ha).le
    rw [max_eq_right ha']
    apply max_le
    · nlinarith
    · nlinarith

/-- Summing the sharp truncation regrets costs only the surviving tail mass. -/
theorem quittingTerminalSemanticDebtSum_replicate_solo_never_sharp_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) {M t : ℝ}
    (hreward : ∀ terminal who, |reward terminal who| ≤ M)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (howner : 0 ≤ reward (quittingSingletonTerminal owner) owner)
    (hunpreempted : ∀ who, who ≠ owner →
      reward (quittingSingletonTerminal who) who ≤
        reward (quittingSingletonTerminal owner) who)
    (hinactive : ∀ who, who ≠ owner →
      (1 - t) * reward (quittingSingletonTerminal who) who +
        t * quittingSingletonCollisionReward reward owner who ≤
          reward (quittingSingletonTerminal owner) who)
    (steps : ℕ) :
    quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPair reward
        (quittingLiteralRootStackProfile reward
          (List.replicate steps (quittingSoloStationaryRoot owner
            (quittingHazardCoin t ht0 ht1))) (quittingAlwaysContinueProfile reward))) ≤
      Fintype.card ι * M * (1 - t) ^ steps := by
  have hM : 0 ≤ M := (abs_nonneg _).trans (hreward (quittingSingletonTerminal owner) owner)
  have hρ : 0 ≤ (1 - t) ^ steps := pow_nonneg (sub_nonneg.mpr ht1) _
  unfold quittingTerminalSemanticDebtSum
  calc
    _ ≤ ∑ who : ι, ((1 - t) ^ steps * M) := by
      apply Finset.sum_le_sum
      intro who _
      exact (quittingTerminalSemanticDebt_replicate_solo_never_sharp_le
        reward owner who ht0 ht1 howner hunpreempted hinactive steps).trans
          (mul_le_mul_of_nonneg_left
            (max_le (le_of_abs_le (hreward (quittingSingletonTerminal owner) who)) hM) hρ)
    _ = Fintype.card ι * M * (1 - t) ^ steps := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring

end GameTheory
