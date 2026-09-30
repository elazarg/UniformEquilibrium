import UniformEquilibrium.Quitting.Cycles.ApproximateCyclicCensor
import UniformEquilibrium.Quitting.Cycles.RationalSingletonCalendar

/-! # Finite calendars from the actual balanced singleton subdivision

The supplied balanced certificate generates the local roots, their actual
periodic value, and the full behavioral cap. Censoring these same roots after
complete turns gives terminal accuracy at the certificate's fixed coarse target.
The cutoff is a supplied integer with a verified survival bound. This stage is
noncomputable; executable rational clock laws and an exact cutoff search are
separate obligations.
-/

noncomputable section

namespace GameTheory

variable {L : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

namespace BalancedSingletonCycleCertificate

variable (certificate : BalancedSingletonCycleCertificate (L := L) reward)

/-- The concrete produced roots retained for `turns` complete microcycles, then Never. -/
def rationalFiniteProfile (δ : ℝ) (turns : ℕ) : (quittingGame reward).BehaviorProfile :=
  quittingCyclicFiniteProfile reward (certificate.rationalRoot δ)
    (certificate.rationalInitial δ) (turns * certificate.rationalPeriod δ)

/-- The actual infinite periodic value is the original selected coarse target. -/
theorem rational_cyclicTerminalValue_initial (δ : ℝ) (hδ : 0 < δ) {M : ℝ}
    (hreward : ∀ terminal who, |reward terminal who| ≤ M) :
    quittingCyclicTerminalValue reward (certificate.rationalRoot δ)
      (certificate.rationalInitial δ) = certificate.coarse certificate.initial :=
  (certificate.rational_isTerminalNash_and_hasValue δ hδ hreward).2

/-- The complete cap comes from the actual produced periodic Nash certificate. -/
theorem rational_fullCap_le (δ : ℝ) (hδ : 0 < δ) {M : ℝ}
    (hreward : ∀ terminal who, |reward terminal who| ≤ M) (who : ι) :
    quittingContinuationBestResponseValue reward (certificate.rationalProfile δ) who ≤
      quittingCyclicTerminalValue reward (certificate.rationalRoot δ)
        (certificate.rationalInitial δ) who + 2 * M * δ := by
  have hsource := certificate.rational_isTerminalNash_and_hasValue δ hδ hreward
  unfold quittingContinuationBestResponseValue
  apply csSup_le
  · exact ⟨_, certificate.rationalProfile δ who, rfl⟩
  · rintro value ⟨deviation, rfl⟩
    exact hsource.1 who deviation

/-- Exact prescribed payoff factor; the target depends only on the original certificate. -/
theorem rationalFiniteProfile_payoff_eq (δ : ℝ) (hδ : 0 < δ) (turns : ℕ) {M : ℝ}
    (hreward : ∀ terminal who, |reward terminal who| ≤ M) (who : ι) :
    quittingTerminalPayoff reward (certificate.rationalFiniteProfile δ turns) who =
      (1 - (∏ p : Fin L, (1 - certificate.hazard p)) ^ turns) *
        certificate.coarse certificate.initial who := by
  unfold rationalFiniteProfile
  rw [quittingTerminalPayoff_cyclicFiniteProfile_mul_card,
    certificate.rational_joint_product,
    certificate.rational_cyclicTerminalValue_initial δ hδ hreward]

/-- The full behavioral censor bound expressed entirely in the original coarse hazards. -/
theorem rationalFiniteProfile_debt_le (δ : ℝ) (hδ : 0 < δ) (turns : ℕ) {M : ℝ}
    (hreward : ∀ terminal who, |reward terminal who| ≤ M) (who : ι) :
    quittingTerminalDeviationDebt reward (certificate.rationalFiniteProfile δ turns) who ≤
      2 * M * δ + 2 * M *
        (∏ p : Fin L, if who = certificate.owner p then 1 else 1 - certificate.hazard p) ^
          turns + M * (∏ p : Fin L, (1 - certificate.hazard p)) ^ turns := by
  have hcap := certificate.rational_fullCap_le δ hδ hreward who
  have h := quittingTerminalDeviationDebt_cyclicFiniteProfile_le_of_full_cap reward
    (certificate.rationalRoot δ) (certificate.rationalInitial δ) turns who hreward hcap
  simpa only [rationalFiniteProfile, certificate.rational_opponent_product,
    certificate.rational_joint_product] using h

theorem rationalFiniteProfile_delivery_le (δ : ℝ) (hδ : 0 < δ) (turns : ℕ) {M : ℝ}
    (hreward : ∀ terminal who, |reward terminal who| ≤ M) (who : ι) :
    |quittingTerminalPayoff reward (certificate.rationalFiniteProfile δ turns) who -
        certificate.coarse certificate.initial who| ≤
      M * (∏ p : Fin L, (1 - certificate.hazard p)) ^ turns := by
  have h := abs_quittingTerminalPayoff_cyclicFiniteProfile_sub_le reward
    (certificate.rationalRoot δ) (certificate.rationalInitial δ) turns who hreward
  simpa only [rationalFiniteProfile, certificate.rational_joint_product,
    certificate.rational_cyclicTerminalValue_initial δ hδ hreward] using h

omit [Fintype ι] in
/-- Joint survival never exceeds any player's deleted-opponent survival. -/
theorem coarse_joint_power_le_opponent_power (turns : ℕ) (who : ι) :
    (∏ p : Fin L, (1 - certificate.hazard p)) ^ turns ≤
      (∏ p : Fin L, if who = certificate.owner p then 1 else 1 - certificate.hazard p) ^
        turns := by
  have hnonneg : 0 ≤ ∏ p : Fin L, (1 - certificate.hazard p) :=
    Finset.prod_nonneg fun p _ => (sub_pos.mpr (certificate.hazard_lt_one p)).le
  apply pow_le_pow_left₀ hnonneg
  apply Finset.prod_le_prod₀
  · intro p _
    exact (sub_pos.mpr (certificate.hazard_lt_one p)).le
  · intro p _
    split_ifs
    · linarith [certificate.hazard_nonneg p]
    · exact le_rfl

/-- For the specified terminal tolerance, the produced finite calendar is an
`η`-Nash profile and delivers the fixed target within `η / 6`. -/
theorem rationalFiniteProfile_isTerminalNash_and_delivery_le
    {M η : ℝ} (hreward : ∀ terminal who, |reward terminal who| ≤ M)
    (hη : 0 < η) (hηM : η ≤ M) (turns : ℕ)
    (hcut : ∀ who,
      (∏ p : Fin L, if who = certificate.owner p then 1 else 1 - certificate.hazard p) ^
        turns ≤ η / (6 * M)) :
    (quittingGame reward).IsεAsymptoticNash (quittingTerminalPayoff reward) η
        (certificate.rationalFiniteProfile (η / (4 * M)) turns) ∧
      ∀ who, |quittingTerminalPayoff reward
            (certificate.rationalFiniteProfile (η / (4 * M)) turns) who -
          certificate.coarse certificate.initial who| ≤ η / 6 := by
  have hM : 0 < M := hη.trans_le hηM
  have hδ : 0 < η / (4 * M) := div_pos hη (by positivity)
  have hmesh : 2 * M * (η / (4 * M)) = η / 2 := by
    field_simp [ne_of_gt hM]
    ring
  have hscale : M * (η / (6 * M)) = η / 6 := by
    field_simp [ne_of_gt hM]
  have hopponent (who : ι) :
      M * (∏ p : Fin L,
        if who = certificate.owner p then 1 else 1 - certificate.hazard p) ^ turns ≤
        η / 6 := by
    have h := mul_le_mul_of_nonneg_left (hcut who) hM.le
    rwa [hscale] at h
  have hjoint (who : ι) :
      M * (∏ p : Fin L, (1 - certificate.hazard p)) ^ turns ≤ η / 6 :=
    (mul_le_mul_of_nonneg_left
      (certificate.coarse_joint_power_le_opponent_power turns who) hM.le).trans
      (hopponent who)
  constructor
  · intro who deviation
    have hdebt := certificate.rationalFiniteProfile_debt_le
      (η / (4 * M)) hδ turns hreward who
    rw [hmesh] at hdebt
    have hreply := quittingTerminalPayoff_update_le_continuationBestResponseValue
      reward (certificate.rationalFiniteProfile (η / (4 * M)) turns) who deviation
    unfold quittingTerminalDeviationDebt at hdebt
    linarith [hopponent who, hjoint who]
  · intro who
    exact (certificate.rationalFiniteProfile_delivery_le
      (η / (4 * M)) hδ turns hreward who).trans (hjoint who)

omit [Fintype ι] [DecidableEq ι] in
/-- The literal number of retained dates has the variable-length source bound. -/
theorem rationalFiniteProfile_dateCount_le {M η : ℝ}
    (hη : 0 < η) (hηM : η ≤ M) (turns : ℕ) :
    ((turns * certificate.rationalPeriod (η / (4 * M)) : ℕ) : ℝ) ≤
      (turns : ℝ) * ((L : ℝ) + (4 * M / η) *
        ∑ p : Fin L, Math.rationalArcOdds (certificate.hazard p)) := by
  have hM : 0 < M := hη.trans_le hηM
  have hδ : 0 < η / (4 * M) := div_pos hη (by positivity)
  have hperiod := certificate.rationalPeriod_le (η / (4 * M)) hδ
  have hdivision :
      (∑ p : Fin L, Math.rationalArcOdds (certificate.hazard p)) / (η / (4 * M)) =
        (4 * M / η) * ∑ p : Fin L, Math.rationalArcOdds (certificate.hazard p) := by
    field_simp [ne_of_gt hM, ne_of_gt hη]
  rw [hdivision] at hperiod
  rw [Nat.cast_mul]
  exact mul_le_mul_of_nonneg_left hperiod (Nat.cast_nonneg turns)

/-- Outsiders retain literal Never at every history, including histories of zero probability. -/
theorem rationalFiniteProfile_outside_continue (δ : ℝ) (turns : ℕ) (who : ι)
    (houtside : ∀ p, who ≠ certificate.owner p) (time : ℕ)
    (history : (quittingGame reward).Hist time) :
    certificate.rationalFiniteProfile δ turns who time history = PMF.pure false := by
  apply quittingCyclicFiniteProfile_apply_eq_continue_of_roots
  intro phase
  unfold rationalRoot quittingSoloStationaryRoot
  exact Function.update_of_ne (houtside _) _ _

end BalancedSingletonCycleCertificate

end GameTheory
