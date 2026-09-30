import UniformEquilibrium.Quitting.Terminal.FiniteDeadlineHorizonError
import UniformEquilibrium.Quitting.Punishment.NegativeSoloUniformization

/-!
# Signed finite-support horizon bounds against the full terminal cap

Each stage payoff is compared with an actual deviation that continues forever
after that stage. The comparison terminal payoff is below the fixed full
behavioral cap, regardless of the singleton reward's sign. Averaging the
opponent live-tail error gives the finite-deadline bound. In particular, a
late negative singleton is compared with a Never continuation rather than
with its own negative terminal payoff.
-/

noncomputable section

namespace GameTheory

open StochasticGame _root_.Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- For arbitrary signed rewards, every finite-horizon behavioral deviation
is below the full terminal cap plus one opponent live-tail Cesaro charge. -/
theorem finiteAveragePayoff_update_le_fullTerminalCap_add_opponentLiveTailCesaro
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι)
    (deviation : (quittingGame reward).BehaviorStrategy who)
    (horizon : ℕ) {M : ℝ}
    (hreward : ∀ terminal, |reward terminal who| ≤ M)
    (hhorizon : 0 < horizon) :
    (quittingGame reward).finiteAveragePayoff none horizon
        (Function.update profile who deviation) who ≤
      quittingContinuationBestResponseValue reward profile who +
        M * ((horizon : ℝ)⁻¹ * ∑ time ∈ Finset.range horizon,
          (quittingLiveMass reward
              (quittingOpponentOnlyProfile reward profile who) time -
            quittingLiveMassLimit reward
              (quittingOpponentOnlyProfile reward profile who))) := by
  have hM : 0 ≤ M := (abs_nonneg _).trans (hreward (quittingSingletonTerminal who))
  let : Finite (quittingGame reward).State :=
    inferInstanceAs (Finite (Option {S : Finset ι // S.Nonempty}))
  let : ∀ player : ι, Finite ((quittingGame reward).Act player) :=
    fun _ => inferInstanceAs (Finite Bool)
  have hstage (time : ℕ) :
      (quittingGame reward).expectedStagePayoff
          (Function.update profile who deviation) none time who ≤
        quittingContinuationBestResponseValue reward profile who +
          M * (quittingLiveMass reward
              (quittingOpponentOnlyProfile reward profile who) time -
            quittingLiveMassLimit reward
              (quittingOpponentOnlyProfile reward profile who)) := by
    have hcomparison := expectedStagePayoff_update_le_cutoffTerminal_add_opponentLiveTail
      reward profile who deviation time M hM hreward
    have hcap := quittingTerminalPayoff_update_le_continuationBestResponseValue
      reward profile who (quittingContinueAfterStrategy reward who deviation time)
    exact hcomparison.trans (_root_.add_le_add hcap le_rfl)
  have haverage := (quittingGame reward).finiteAveragePayoff_eq_sum_expectedStagePayoff
    (Function.update profile who deviation)
    (show (quittingGame reward).State from none) who horizon
  rw [haverage]
  calc
    (horizon : ℝ)⁻¹ * ∑ time ∈ Finset.range horizon,
        (quittingGame reward).expectedStagePayoff
          (Function.update profile who deviation) none time who ≤
      (horizon : ℝ)⁻¹ * ∑ time ∈ Finset.range horizon,
        (quittingContinuationBestResponseValue reward profile who +
          M * (quittingLiveMass reward
              (quittingOpponentOnlyProfile reward profile who) time -
            quittingLiveMassLimit reward
              (quittingOpponentOnlyProfile reward profile who))) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Finset.sum_le_sum fun time _ => hstage time
    _ = _ := by
      have hne : (horizon : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hhorizon
      rw [Finset.sum_add_distrib]
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      rw [← Finset.mul_sum]
      field_simp

/-- Finite timing support gives a signed bound by the full terminal cap,
uniformly over every actual behavioral replacement. -/
theorem finiteAveragePayoff_update_finiteDeadline_le_fullTerminalCap_add
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (deadline horizon : ℕ)
    (mixed : ι → PMF (QuittingFiniteDeadlineTimingAction deadline))
    (who : ι) (deviation : (quittingGame reward).BehaviorStrategy who)
    {M : ℝ} (hreward : ∀ terminal, |reward terminal who| ≤ M)
    (hhorizon : 0 < horizon) :
    (quittingGame reward).finiteAveragePayoff none horizon
        (Function.update
          (quittingFiniteDeadlineTimingProfile reward deadline mixed) who deviation) who ≤
      quittingContinuationBestResponseValue reward
          (quittingFiniteDeadlineTimingProfile reward deadline mixed) who +
        M * deadline / horizon := by
  have hM : 0 ≤ M := (abs_nonneg _).trans (hreward (quittingSingletonTerminal who))
  have hraw := finiteAveragePayoff_update_le_fullTerminalCap_add_opponentLiveTailCesaro
    reward (quittingFiniteDeadlineTimingProfile reward deadline mixed) who deviation
    horizon hreward hhorizon
  have htail := sum_opponentLiveTail_finiteDeadline_le reward deadline horizon mixed who
  have hinv : 0 ≤ (horizon : ℝ)⁻¹ := by positivity
  have hscaled := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left htail hinv) hM
  have hboundary : M * ((horizon : ℝ)⁻¹ * (deadline : ℝ)) =
      M * deadline / horizon := by rw [div_eq_mul_inv]; ring
  rw [hboundary] at hscaled
  exact hraw.trans (_root_.add_le_add le_rfl hscaled)

/-- The same bound written using the existing complete finite-menu cap:
the Never candidate and the single late row are both retained. -/
theorem finiteAveragePayoff_update_finiteDeadline_le_fullReplyCap_add
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (deadline horizon : ℕ)
    (mixed : ι → PMF (QuittingFiniteDeadlineTimingAction deadline))
    (who : ι) (deviation : (quittingGame reward).BehaviorStrategy who)
    {M : ℝ} (hreward : ∀ terminal, |reward terminal who| ≤ M)
    (hhorizon : 0 < horizon) :
    (quittingGame reward).finiteAveragePayoff none horizon
        (Function.update
          (quittingFiniteDeadlineTimingProfile reward deadline mixed) who deviation) who ≤
      max (quittingFiniteDeadlineReplyCap reward deadline mixed who)
          (quittingFiniteDeadlineNeverPayoff reward deadline mixed who +
            quittingFiniteDeadlineOpponentNeverProduct deadline mixed who *
              reward (quittingSingletonTerminal who) who) +
        M * deadline / horizon := by
  simpa only [quittingContinuationBestResponseValue_finiteDeadlineTimingProfile_eq_max] using
    finiteAveragePayoff_update_finiteDeadline_le_fullTerminalCap_add
      reward deadline horizon mixed who deviation hreward hhorizon

/-- Signed finite-horizon regret is at most the player's complete terminal
debt plus twice the finite-support boundary charge. -/
theorem finiteAveragePayoff_update_sub_finiteDeadline_le_terminalDebt_add
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (deadline horizon : ℕ)
    (mixed : ι → PMF (QuittingFiniteDeadlineTimingAction deadline))
    (who : ι) (deviation : (quittingGame reward).BehaviorStrategy who)
    {M : ℝ} (hreward : ∀ terminal, |reward terminal who| ≤ M)
    (hhorizon : 0 < horizon) :
    (quittingGame reward).finiteAveragePayoff none horizon
        (Function.update
          (quittingFiniteDeadlineTimingProfile reward deadline mixed) who deviation) who -
      (quittingGame reward).finiteAveragePayoff none horizon
        (quittingFiniteDeadlineTimingProfile reward deadline mixed) who ≤
      quittingTerminalDeviationDebt reward
          (quittingFiniteDeadlineTimingProfile reward deadline mixed) who +
        2 * M * deadline / horizon := by
  have hdev := finiteAveragePayoff_update_finiteDeadline_le_fullTerminalCap_add
    reward deadline horizon mixed who deviation hreward hhorizon
  have hon := abs_finiteAveragePayoff_sub_terminal_finiteDeadline_le
    reward deadline horizon mixed who hreward hhorizon
  have hlower := (abs_le.mp hon).1
  have hboundary : 2 * M * (deadline : ℝ) / (horizon : ℝ) =
      2 * (M * deadline / horizon) := by ring
  rw [hboundary]
  unfold quittingTerminalDeviationDebt
  linarith

/-- The source packet's deadline-plus-one convention for the signed full-cap bound. -/
theorem finiteAveragePayoff_update_finiteDeadline_le_fullTerminalCap_add_one
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (deadline horizon : ℕ)
    (mixed : ι → PMF (QuittingFiniteDeadlineTimingAction deadline))
    (who : ι) (deviation : (quittingGame reward).BehaviorStrategy who)
    {M : ℝ} (hreward : ∀ terminal, |reward terminal who| ≤ M)
    (hhorizon : 0 < horizon) :
    (quittingGame reward).finiteAveragePayoff none horizon
        (Function.update
          (quittingFiniteDeadlineTimingProfile reward deadline mixed) who deviation) who ≤
      quittingContinuationBestResponseValue reward
          (quittingFiniteDeadlineTimingProfile reward deadline mixed) who +
        M * (deadline + 1) / horizon := by
  have hM : 0 ≤ M := (abs_nonneg _).trans (hreward (quittingSingletonTerminal who))
  have h := finiteAveragePayoff_update_finiteDeadline_le_fullTerminalCap_add
    reward deadline horizon mixed who deviation hreward hhorizon
  refine h.trans (_root_.add_le_add le_rfl ?_)
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact mul_le_mul_of_nonneg_left (by norm_num : (deadline : ℝ) ≤ deadline + 1) hM

/-- The packet's signed playerwise regret bound under its deadline-plus-one convention. -/
theorem finiteAveragePayoff_update_sub_finiteDeadline_le_terminalDebt_add_one
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (deadline horizon : ℕ)
    (mixed : ι → PMF (QuittingFiniteDeadlineTimingAction deadline))
    (who : ι) (deviation : (quittingGame reward).BehaviorStrategy who)
    {M : ℝ} (hreward : ∀ terminal, |reward terminal who| ≤ M)
    (hhorizon : 0 < horizon) :
    (quittingGame reward).finiteAveragePayoff none horizon
        (Function.update
          (quittingFiniteDeadlineTimingProfile reward deadline mixed) who deviation) who -
      (quittingGame reward).finiteAveragePayoff none horizon
        (quittingFiniteDeadlineTimingProfile reward deadline mixed) who ≤
      quittingTerminalDeviationDebt reward
          (quittingFiniteDeadlineTimingProfile reward deadline mixed) who +
        2 * M * (deadline + 1) / horizon := by
  have hM : 0 ≤ M := (abs_nonneg _).trans (hreward (quittingSingletonTerminal who))
  have h := finiteAveragePayoff_update_sub_finiteDeadline_le_terminalDebt_add
    reward deadline horizon mixed who deviation hreward hhorizon
  refine h.trans (_root_.add_le_add le_rfl ?_)
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact mul_le_mul_of_nonneg_left (by norm_num : (deadline : ℝ) ≤ deadline + 1)
    (by positivity : 0 ≤ 2 * M)

/-- A signed terminal approximate Nash finite timing profile is an
approximate Nash profile at each positive horizon with the explicit rate. -/
theorem isHorizonNash_finiteDeadline_of_terminalNash_signed
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (deadline horizon : ℕ)
    (mixed : ι → PMF (QuittingFiniteDeadlineTimingAction deadline))
    {D M : ℝ}
    (hnash : (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) D
      (quittingFiniteDeadlineTimingProfile reward deadline mixed))
    (hreward : ∀ terminal who, |reward terminal who| ≤ M)
    (hhorizon : 0 < horizon) :
    (quittingGame reward).IsεHorizonNash none horizon
      (D + 2 * M * deadline / horizon)
      (quittingFiniteDeadlineTimingProfile reward deadline mixed) := by
  intro who deviation
  have hcap : quittingContinuationBestResponseValue reward
      (quittingFiniteDeadlineTimingProfile reward deadline mixed) who ≤
      quittingTerminalPayoff reward
        (quittingFiniteDeadlineTimingProfile reward deadline mixed) who + D := by
    unfold quittingContinuationBestResponseValue
    apply csSup_le
    · exact ⟨_, (quittingFiniteDeadlineTimingProfile reward deadline mixed) who, rfl⟩
    · rintro value ⟨replacement, rfl⟩
      exact hnash who replacement
  have h := finiteAveragePayoff_update_sub_finiteDeadline_le_terminalDebt_add
    reward deadline horizon mixed who deviation (fun terminal => hreward terminal who)
      hhorizon
  unfold quittingTerminalDeviationDebt at h
  linarith

/-- Equation (16)'s deadline-plus-one signed Nash bound, with unrestricted
behavioral deviations at every positive finite horizon. -/
theorem isHorizonNash_finiteDeadline_of_terminalNash_add_one_signed
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (deadline horizon : ℕ)
    (mixed : ι → PMF (QuittingFiniteDeadlineTimingAction deadline))
    {D M : ℝ}
    (hnash : (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) D
      (quittingFiniteDeadlineTimingProfile reward deadline mixed))
    (hreward : ∀ terminal who, |reward terminal who| ≤ M)
    (hhorizon : 0 < horizon) :
    (quittingGame reward).IsεHorizonNash none horizon
      (D + 2 * M * (deadline + 1) / horizon)
      (quittingFiniteDeadlineTimingProfile reward deadline mixed) := by
  intro who deviation
  have h := isHorizonNash_finiteDeadline_of_terminalNash_signed
    reward deadline horizon mixed hnash hreward hhorizon who deviation
  have hM : 0 ≤ M := (abs_nonneg _).trans (hreward (quittingSingletonTerminal who) who)
  refine h.trans (_root_.add_le_add le_rfl (_root_.add_le_add le_rfl ?_))
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact mul_le_mul_of_nonneg_left (by norm_num : (deadline : ℝ) ≤ deadline + 1)
    (by positivity : 0 ≤ 2 * M)

/-- Finite date-or-Never laws with terminal regret and target delivery at half
accuracy satisfy the printed signed horizon cutoff for every reward
bound. The same laws are used at every sufficiently long horizon. -/
theorem finiteDeadlineTiming_uniformPayoffWitness_of_terminal_bounds
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (target : Payoff ι) (deadline : ℕ)
    (mixed : ι → PMF (QuittingFiniteDeadlineTimingAction deadline))
    {accuracy : ℝ} (haccuracy : 0 < accuracy)
    (hnash : (quittingGame reward).IsεAsymptoticNash (quittingTerminalPayoff reward)
      (accuracy / 2) (quittingFiniteDeadlineTimingProfile reward deadline mixed))
    (htarget : ∀ who, |quittingTerminalPayoff reward
        (quittingFiniteDeadlineTimingProfile reward deadline mixed) who - target who| ≤
      accuracy / 2)
    {M : ℝ}
    (hreward : ∀ terminal who, |reward terminal who| ≤ M) :
    ∀ horizon : ℕ,
      max 1 (Nat.ceil (4 * M * (deadline + 1) / accuracy)) ≤ horizon →
      (quittingGame reward).IsεHorizonNash none horizon accuracy
        (quittingFiniteDeadlineTimingProfile reward deadline mixed) ∧
      ∀ who, |(quittingGame reward).finiteAveragePayoff none horizon
        (quittingFiniteDeadlineTimingProfile reward deadline mixed) who - target who| ≤
          accuracy := by
  intro horizon hhorizon
  have hpositive : 0 < horizon := lt_of_lt_of_le Nat.zero_lt_one
    ((Nat.le_max_left _ _).trans hhorizon)
  have hreal : (0 : ℝ) < horizon := by exact_mod_cast hpositive
  have hceil : Nat.ceil (4 * M * (deadline + 1) / accuracy) ≤ horizon :=
    (Nat.le_max_right _ _).trans hhorizon
  have hcast : (Nat.ceil (4 * M * (deadline + 1) / accuracy) : ℝ) ≤ horizon := by
    exact_mod_cast hceil
  have hquotient := (Nat.le_ceil (4 * M * (deadline + 1) / accuracy)).trans hcast
  have hmul := (div_le_iff₀ haccuracy).mp hquotient
  have hboundary : 2 * M * (deadline + 1) / horizon ≤ accuracy / 2 := by
    apply (div_le_iff₀ hreal).mpr
    nlinarith
  constructor
  · exact (isHorizonNash_finiteDeadline_of_terminalNash_add_one_signed
      reward deadline horizon mixed hnash hreward hpositive).mono (by linarith)
  · intro who
    have hM : 0 ≤ M :=
      (abs_nonneg _).trans (hreward (quittingSingletonTerminal who) who)
    have hon := abs_finiteAveragePayoff_sub_terminal_finiteDeadline_le
      reward deadline horizon mixed who (fun terminal => hreward terminal who) hpositive
    have hsmall : M * deadline / horizon ≤ 2 * M * (deadline + 1) / horizon := by
      apply div_le_div_of_nonneg_right _ hreal.le
      have hdate : (0 : ℝ) ≤ deadline := Nat.cast_nonneg deadline
      nlinarith
    have htriangle := abs_sub_le
      ((quittingGame reward).finiteAveragePayoff none horizon
        (quittingFiniteDeadlineTimingProfile reward deadline mixed) who)
      (quittingTerminalPayoff reward
        (quittingFiniteDeadlineTimingProfile reward deadline mixed) who) (target who)
    linarith [htarget who]

end GameTheory
