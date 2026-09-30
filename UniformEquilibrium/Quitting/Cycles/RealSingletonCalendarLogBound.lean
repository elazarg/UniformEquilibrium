import MathUE.PowerCutoffLogBound
import UniformEquilibrium.Quitting.Cycles.RationalSingletonFiniteCalendar

/-! # Fixed-input logarithmic calendar bounds for real singleton data

A fixed balanced certificate and fixed positive real reward bound determine
constants before accuracy. A positive comparison cutoff preserves the existing
finite calendar's terminal regret and fixed-target delivery estimates, while
its actual date count has the fixed-input logarithmic bound. No rationality,
bit complexity or uniform weak-boundary estimate is asserted.
-/

noncomputable section

namespace GameTheory.BalancedSingletonCycleCertificate

variable {ι : Type} [Fintype ι] [DecidableEq ι] {phases : ℕ}
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- Every sufficiently small positive real accuracy has a positive cutoff for
the same certificate's finite calendar. Its terminal and literal date-count
bounds hold together, with the target and eventual constants fixed in advance. -/
theorem exists_realFiniteCalendar_log_bound
    (certificate : BalancedSingletonCycleCertificate (L := phases) reward)
    {M : ℝ} (hM : 0 < M)
    (hreward : ∀ terminal who, |reward terminal who| ≤ M) :
    ∃ constant : ℝ, 0 < constant ∧
      ∃ threshold : ℝ, 0 < threshold ∧
        ∀ (η : ℝ), 0 < η → η ≤ threshold →
          let turns := Math.powerLogCutoff certificate.opponentProductCap (η / (6 * M))
          0 < turns ∧
          (∀ who,
            (∏ phase : Fin phases,
              if who = certificate.owner phase then 1 else 1 - certificate.hazard phase) ^
                turns ≤ η / (6 * M)) ∧
          (quittingGame reward).IsεAsymptoticNash (quittingTerminalPayoff reward) η
            (certificate.rationalFiniteProfile (η / (4 * M)) turns) ∧
          (∀ who, |quittingTerminalPayoff reward
                (certificate.rationalFiniteProfile (η / (4 * M)) turns) who -
              certificate.coarse certificate.initial who| ≤ η / 6) ∧
          ((turns * certificate.rationalPeriod (η / (4 * M)) : ℕ) : ℝ) ≤
            (turns : ℝ) * ((phases : ℝ) + (4 * M / η) *
              ∑ phase, Math.rationalArcOdds (certificate.hazard phase)) ∧
          ((turns * certificate.rationalPeriod (η / (4 * M)) : ℕ) : ℝ) ≤
            constant * (η⁻¹ * Real.log (η⁻¹)) := by
  have hproduct (who : ι) :
      0 ≤ ∏ phase : Fin phases,
        if who = certificate.owner phase then 1 else 1 - certificate.hazard phase := by
    apply Finset.prod_nonneg
    intro phase _
    split_ifs
    · norm_num
    · exact (sub_pos.mpr (certificate.hazard_lt_one phase)).le
  have hcap : 0 ≤ certificate.opponentProductCap :=
    (hproduct (certificate.owner certificate.initial)).trans
      (certificate.opponent_product_le_cap _)
  have hodds : 0 ≤ ∑ phase, Math.rationalArcOdds (certificate.hazard phase) := by
    apply Finset.sum_nonneg
    intro phase _
    exact div_nonneg (certificate.hazard_nonneg phase)
      (sub_nonneg.mpr (certificate.hazard_lt_one phase).le)
  let coefficient := 4 * M * ∑ phase, Math.rationalArcOdds (certificate.hazard phase)
  have hcoefficient : 0 ≤ coefficient := mul_nonneg (by positivity) hodds
  obtain ⟨constant, hconstant, scalarThreshold, hscalarThreshold, hbound⟩ :=
    Math.exists_powerCutoff_calendar_log_bound hcap certificate.opponentProductCap_lt_one
      hM (Nat.cast_nonneg phases) hcoefficient
  refine ⟨constant, hconstant, min M scalarThreshold, lt_min hM hscalarThreshold, ?_⟩
  intro η hη hsmall
  have hηM : η ≤ M := hsmall.trans (min_le_left _ _)
  have hηscalar : η ≤ scalarThreshold := hsmall.trans (min_le_right _ _)
  have htolerance : 0 < η / (6 * M) := div_pos hη (by positivity)
  have htolerance1 : η / (6 * M) ≤ 1 := by
    apply (div_le_one (by positivity : 0 < 6 * M)).mpr
    linarith
  let turns := Math.powerLogCutoff certificate.opponentProductCap (η / (6 * M))
  have hscalar := Math.powerLogCutoff_spec_and_bound
    hcap certificate.opponentProductCap_lt_one htolerance htolerance1
  have hcut : ∀ who,
      (∏ phase : Fin phases,
        if who = certificate.owner phase then 1 else 1 - certificate.hazard phase) ^ turns ≤
          η / (6 * M) := by
    intro who
    exact (pow_le_pow_left₀ (hproduct who)
      (certificate.opponent_product_le_cap who) turns).trans hscalar.2.1
  have hterminal := certificate.rationalFiniteProfile_isTerminalNash_and_delivery_le
    hreward hη hηM turns hcut
  have hdates := certificate.rationalFiniteProfile_dateCount_le hη hηM turns
  refine ⟨hscalar.1, hcut, hterminal.1, hterminal.2, hdates, ?_⟩
  have hmesh : (4 * M / η) *
      ∑ phase, Math.rationalArcOdds (certificate.hazard phase) = coefficient / η := by
    dsimp only [coefficient]
    ring
  rw [hmesh] at hdates
  exact hdates.trans (hbound η hη hηM hηscalar)

end GameTheory.BalancedSingletonCycleCertificate
