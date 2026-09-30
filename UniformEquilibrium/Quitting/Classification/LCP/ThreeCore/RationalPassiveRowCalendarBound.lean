import MathUE.RationalPowerCutoffLogBound
import UniformEquilibrium.Quitting.Classification.LCP.ThreeCore.RationalRawPassiveRowClocks

/-! # Fixed-input calendar bounds for the actual rational passive-row clocks

The exact mesh, chronological word and rational power search are unchanged.
The scalar logarithmic estimate bounds their date count at a fixed input.
The raw strict-inverse consumer retains the same independent laws, exact
stopping masses and full terminal semantic pair as the existing clock producer.
Neither a bit-complexity bound nor a constant uniform over weak inverse
boundary inputs is claimed.
-/

namespace GameTheory

open scoped BigOperators

namespace BalancedSingletonCycleCertificate

variable {players phases : ℕ}
variable {reward : {S : Finset (Fin players) // S.Nonempty} → Payoff (Fin players)}

/-- Fixed coarse data and reward scale give a fixed eventual calendar constant,
before the accuracy-dependent mesh and exact rational cutoff are selected. -/
theorem exists_rationalClockDateCount_log_bound
    (certificate : BalancedSingletonCycleCertificate (L := phases) reward)
    (q : Fin phases → ℚ) (hq : ∀ phase, certificate.hazard phase = (q phase : ℝ))
    {M : ℚ} (hM : 0 < M) :
    ∃ constant : ℝ, 0 < constant ∧
      ∃ threshold : ℝ, 0 < threshold ∧
        ∀ (η : ℚ) (hη : 0 < η) (hηM : η ≤ M), (η : ℝ) ≤ threshold →
          let data := certificate.rationalClockData q hq
          let turns := data.turns M η (hη.trans_le hηM) hη
            (certificate.rationalClockData_survivalBound_lt_one q hq)
          ((turns * data.period (η / (4 * M)) : ℕ) : ℝ) ≤
            constant * ((η : ℝ)⁻¹ * Real.log ((η : ℝ)⁻¹)) := by
  let data := certificate.rationalClockData q hq
  let coefficient := 4 * (M : ℝ) *
    ∑ phase, Math.rationalArcOdds (certificate.hazard phase)
  have hMreal : (0 : ℝ) < M := by exact_mod_cast hM
  have hodds : 0 ≤ ∑ phase, Math.rationalArcOdds (certificate.hazard phase) := by
    apply Finset.sum_nonneg
    intro phase _
    exact div_nonneg (certificate.hazard_nonneg phase)
      (sub_nonneg.mpr (certificate.hazard_lt_one phase).le)
  have hcoefficient : 0 ≤ coefficient := mul_nonneg (by positivity) hodds
  obtain ⟨constant, hconstant, threshold, hthreshold, hbound⟩ :=
    Math.exists_rationalPowerCutoff_calendar_log_bound data.survivalBound_nonneg
      (certificate.rationalClockData_survivalBound_lt_one q hq) hM
      (Nat.cast_nonneg phases) hcoefficient
  refine ⟨constant, hconstant, threshold, hthreshold, ?_⟩
  intro η hη hηM hsmall
  let turns := data.turns M η (hη.trans_le hηM) hη
    (certificate.rationalClockData_survivalBound_lt_one q hq)
  have hδcast : ((η / (4 * M) : ℚ) : ℝ) =
      (η : ℝ) / (4 * (M : ℝ)) := by push_cast; rfl
  have hperiod : data.period (η / (4 * M)) =
      certificate.rationalPeriod ((η : ℝ) / (4 * (M : ℝ))) :=
    (certificate.rationalClockData_period_eq q hq _).trans
      (congrArg certificate.rationalPeriod hδcast)
  have hdates := certificate.rationalFiniteProfile_dateCount_le
    (show (0 : ℝ) < (η : ℝ) by exact_mod_cast hη)
    (show (η : ℝ) ≤ (M : ℝ) by exact_mod_cast hηM) turns
  rw [← hperiod] at hdates
  have hmesh : (4 * (M : ℝ) / (η : ℝ)) *
      ∑ phase, Math.rationalArcOdds (certificate.hazard phase) =
        coefficient / (η : ℝ) := by
    dsimp only [coefficient]
    ring
  rw [hmesh] at hdates
  exact hdates.trans (hbound η hη hηM hsmall)

end BalancedSingletonCycleCertificate

namespace PassiveRowInverseCriterion

variable {players : ℕ}
variable (reward : {S : Finset (Fin players) // S.Nonempty} → Payoff (Fin players))
variable (deleted : Fin players → Prop) [DecidablePred deleted]

local notation "Child" => {who : Fin players // ¬ deleted who}

/-- The raw strict singleton class produces one target and fixed calendar
constants before accuracy. The actual clocks are exactly those of the checked
rational source producer; their complete behavioral bounds are not reproved. -/
theorem exists_rationalClocks_log_bound_of_raw_strictInverse_triple
    (rationalSingleton : Fin players → Fin players → ℚ)
    (hsingleton : ∀ owner who, quittingSoloReward reward owner who =
      (rationalSingleton owner who : ℝ))
    (hcard : Fintype.card Child = 3)
    (hdet : (childMatrix reward deleted).det ≠ 0)
    (hinverse : ∀ row column : Child, 0 < (childMatrix reward deleted)⁻¹ row column)
    (houtside : ∀ outside, deleted outside →
      ∀ inside : Child, 0 ≤ inverseWeight reward deleted outside inside)
    {M : ℚ} (hM : 0 < M)
    (hreward : ∀ terminal who, |reward terminal who| ≤ (M : ℝ)) :
    ∃ (certificate : BalancedSingletonCycleCertificate (L := 3) reward)
      (hazard : Fin 3 → ℚ),
      ∃ hcast : ∀ phase, certificate.hazard phase = (hazard phase : ℝ),
      ∃ constant : ℝ, 0 < constant ∧
        ∃ threshold : ℝ, 0 < threshold ∧
          ∀ (η : ℚ) (hη : 0 < η) (hηM : η ≤ M), (η : ℝ) ≤ threshold →
            let data := certificate.rationalClockData hazard hcast
            let turns := data.turns M η (hη.trans_le hηM) hη
              (certificate.rationalClockData_survivalBound_lt_one hazard hcast)
            let δ := η / (4 * M)
            ∃ mixed : Fin players → PMF (Option (Fin (turns * data.period δ))),
              (∀ who choice,
                (mixed who choice).toReal = (data.mass δ turns who choice : ℝ)) ∧
              (∀ who, (quittingFiniteDeadlineTimingLaw (mixed who)).toPMF =
                quittingBehaviorStoppingLaw reward
                  (certificate.rationalFiniteProfile (δ : ℝ) turns who)) ∧
              quittingTerminalSemanticPair reward
                  (quittingFiniteDeadlineTimingProfile reward (turns * data.period δ) mixed) =
                quittingTerminalSemanticPair reward
                  (certificate.rationalFiniteProfile (δ : ℝ) turns) ∧
              (quittingGame reward).IsεAsymptoticNash (quittingTerminalPayoff reward) (η : ℝ)
                (quittingFiniteDeadlineTimingProfile reward (turns * data.period δ) mixed) ∧
              (∀ who, |quittingTerminalPayoff reward
                  (quittingFiniteDeadlineTimingProfile reward (turns * data.period δ) mixed)
                    who - certificate.coarse certificate.initial who| ≤ (η : ℝ) / 6) ∧
              (∀ who, deleted who → mixed who = PMF.pure none) ∧
              ((turns * data.period δ : ℕ) : ℝ) ≤ (turns : ℝ) *
                (3 + (4 * (M : ℝ) / (η : ℝ)) *
                  ∑ phase, Math.rationalArcOdds (certificate.hazard phase)) ∧
              ((turns * data.period δ : ℕ) : ℝ) ≤
                constant * ((η : ℝ)⁻¹ * Real.log ((η : ℝ)⁻¹)) := by
  obtain ⟨certificate, hazard, hcast, hsource⟩ :=
    exists_rationalClocks_of_raw_strictInverse_triple reward deleted
      rationalSingleton hsingleton hcard hdet hinverse houtside
  obtain ⟨constant, hconstant, threshold, hthreshold, hbound⟩ :=
    certificate.exists_rationalClockDateCount_log_bound hazard hcast hM
  refine ⟨certificate, hazard, hcast, constant, hconstant, threshold, hthreshold, ?_⟩
  intro η hη hηM hsmall
  obtain ⟨mixed, hmass, hlaws, hpair, hnash, hdelivery, hnever, hdates⟩ :=
    hsource M η hη hηM hreward
  exact ⟨mixed, hmass, hlaws, hpair, hnash, hdelivery, hnever, hdates,
    hbound η hη hηM hsmall⟩

end PassiveRowInverseCriterion

end GameTheory
