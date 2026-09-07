import MathUE.Probability.DiscreteHazardMixture

/-! # Literal first-row realization of a mixture with immediate stopping -/

noncomputable section

namespace Math.Probability.DiscreteHazard

/-- Complete stopping laws depend on survival masses, not on arbitrary
hazards prescribed after a zero-survival date. -/
theorem ScalarHazard.stoppingLaw_eq_of_survival_eq
    (first second : ScalarHazard)
    (hsurvival : ∀ time, first.survival 0 time = second.survival 0 time) :
    first.stoppingLaw = second.stoppingLaw := by
  apply Math.ProbabilityMassFunction.eq_of_forall_toReal_eq
  intro choice
  cases choice with
  | none =>
      simp only [ScalarHazard.stoppingLaw_none_toReal, ScalarHazard.neverMass]
      exact congrArg iInf (funext hsurvival)
  | some time =>
      simp only [ScalarHazard.stoppingLaw_some_toReal,
        ScalarHazard.stopMass_eq_survival_sub_succ, hsurvival]

/-- Increase only the first Quit probability by privately mixing in Quit0;
keep every later displayed marginal, including null-tail prescriptions. -/
def BooleanHazard.installQuitZero
    (source : BooleanHazard) (lambda : ℝ)
    (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1) : BooleanHazard
  | 0 => booleanCoin (lambda + (1 - lambda) * stopProbability source 0)
      (by have := stop_nonneg source 0; positivity)
      (by
        have hstop0 := stop_nonneg source 0
        have hstop1 := source.toScalar.stop_le_one 0
        change stopProbability source 0 ≤ 1 at hstop1
        nlinarith)
  | time + 1 => source (time + 1)

/-- The literal first-row realizer has exactly the full stopping-law mixture
with any target that stops surely at date zero. Source survival may vanish,
and both closed-interval mixture endpoints are allowed. -/
theorem BooleanHazard.installQuitZero_stoppingLaw_eq_convexMix
    (source target : BooleanHazard) (lambda : ℝ)
    (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1)
    (htarget : target 0 = PMF.pure true) :
    (BooleanHazard.installQuitZero source lambda hlambda0 hlambda1).toScalar.stoppingLaw =
      (BooleanHazard.convexMix source target lambda hlambda0 hlambda1).toScalar.stoppingLaw := by
  rw [BooleanHazard.toScalar_convexMix]
  apply ScalarHazard.stoppingLaw_eq_of_survival_eq
  intro cutoff
  rw [ScalarHazard.convexMix_survival]
  cases cutoff with
  | zero => simp [ScalarHazard.mixedSurvival, ScalarHazard.survival_zero]
  | succ time =>
      have htail :
          (BooleanHazard.installQuitZero source lambda hlambda0 hlambda1).toScalar.survival
              1 time = source.toScalar.survival 1 time := by
        unfold ScalarHazard.survival Math.survivalProduct
        apply Finset.prod_congr rfl
        intro offset _
        simp only [BooleanHazard.toScalar, stopProbability,
          show 1 + offset = offset + 1 by omega, BooleanHazard.installQuitZero]
      have hzero : target.toScalar.stop 0 = 1 := by
        simp [BooleanHazard.toScalar, stopProbability, htarget]
      have hfirst :
          (BooleanHazard.installQuitZero source lambda hlambda0 hlambda1).toScalar.stop 0 =
            lambda + (1 - lambda) * source.toScalar.stop 0 := by
        simp only [BooleanHazard.toScalar, stopProbability,
          BooleanHazard.installQuitZero, booleanCoin_true_toReal]
      simp only [ScalarHazard.mixedSurvival, ScalarHazard.survival_succ_left, Nat.zero_add]
      rw [hzero, htail, hfirst]
      ring

end Math.Probability.DiscreteHazard
