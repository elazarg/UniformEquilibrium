import UniformEquilibrium.ProofView.Concepts.Stochastic.Models.RecursiveAbsorption.Payoff
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Stationary payoff accounting for recursive absorption

Absorption mass and absorbing payoff contribution are computed from the actual
independent action PMFs and the model's probability and reward tables. A zero
absorption mass forces a zero contribution; this is derived rather than assumed.
Absorbed initial states have their literal constant payoff against every
behavioral profile. The stationary live-state stage payoff satisfies the actual
one-step affine recurrence used in Flesch, Thuijsman and Vrieze (1996), Lemma 2.2.
Its geometric solution and the actual expected-pathwise-liminf bridge identify
the stationary live-state payoff with the absorption-weighted reward ratio.
Zero absorption mass is included without a separate public positivity premise.
-/

noncomputable section

open _root_.Math.Probability Filter
open scoped Topology

namespace GameTheory.RecursiveAbsorption

variable {I J : Type} [Fintype I] [Fintype J]

/-- Actual one-step absorption probability under independent stationary mixed actions. -/
def absorptionMass (D : Data I J) (x : PMF I) (y : PMF J) : ℝ :=
  expect x fun i => expect y fun j => (D.absorption i j : ℝ)

/-- Actual absorption-weighted reward contribution for one player. -/
def absorbingContribution (D : Data I J) (x : PMF I) (y : PMF J) (who : Bool) : ℝ :=
  expect x fun i => expect y fun j => (D.absorption i j : ℝ) * D.reward i j who

/-- The numerical stationary ratio, taking value zero when the absorption mass is zero. -/
def stationaryPayoff (D : Data I J) (x : PMF I) (y : PMF J) (who : Bool) : ℝ :=
  absorbingContribution D x y who / absorptionMass D x y

omit [Fintype I] [Fintype J] in
theorem absorptionMass_nonneg (D : Data I J) (x : PMF I) (y : PMF J) :
    0 ≤ absorptionMass D x y :=
  expect_nonneg _ _ fun i => expect_nonneg _ _ fun j => (D.absorption i j).2.1

theorem absorptionMass_le_one (D : Data I J) (x : PMF I) (y : PMF J) :
    absorptionMass D x y ≤ 1 := by
  unfold absorptionMass
  calc
    expect x (fun i => expect y fun j => (D.absorption i j : ℝ)) ≤
        expect x (fun _ => 1) := by
      apply expect_mono
      intro i
      calc
        expect y (fun j => (D.absorption i j : ℝ)) ≤ expect y (fun _ => 1) :=
          expect_mono _ _ _ fun j => (D.absorption i j).2.2
        _ = 1 := expect_const _ _
    _ = 1 := expect_const _ _

/-- A pointwise reward ceiling bounds the actual absorption-weighted contribution. -/
theorem absorbingContribution_le_mul_mass (D : Data I J) (x : PMF I) (y : PMF J)
    (who : Bool) (C : ℝ) (hC : ∀ i j, D.reward i j who ≤ C) :
    absorbingContribution D x y who ≤ C * absorptionMass D x y := by
  unfold absorbingContribution absorptionMass
  calc
    expect x (fun i => expect y fun j =>
        (D.absorption i j : ℝ) * D.reward i j who) ≤
        expect x (fun i => expect y fun j => C * (D.absorption i j : ℝ)) := by
      apply expect_mono
      intro i
      apply expect_mono
      intro j
      simpa only [mul_comm] using
        mul_le_mul_of_nonneg_left (hC i j) (D.absorption i j).2.1
    _ = C * expect x (fun i => expect y fun j => (D.absorption i j : ℝ)) := by
      simp only [expect_const_mul]

/-- A pointwise reward floor gives the corresponding weighted contribution floor. -/
theorem mul_mass_le_absorbingContribution (D : Data I J) (x : PMF I) (y : PMF J)
    (who : Bool) (C : ℝ) (hC : ∀ i j, C ≤ D.reward i j who) :
    C * absorptionMass D x y ≤ absorbingContribution D x y who := by
  unfold absorbingContribution absorptionMass
  calc
    C * expect x (fun i => expect y fun j => (D.absorption i j : ℝ)) =
        expect x (fun i => expect y fun j => C * (D.absorption i j : ℝ)) := by
      simp only [expect_const_mul]
    _ ≤ expect x (fun i => expect y fun j =>
        (D.absorption i j : ℝ) * D.reward i j who) := by
      apply expect_mono
      intro i
      apply expect_mono
      intro j
      simpa only [mul_comm] using
        mul_le_mul_of_nonneg_left (hC i j) (D.absorption i j).2.1

/-- Zero actual absorption mass cannot hide an independent nonzero numerator. -/
theorem absorbingContribution_eq_zero_of_mass_eq_zero
    (D : Data I J) (x : PMF I) (y : PMF J) (who : Bool)
    (hzero : absorptionMass D x y = 0) : absorbingContribution D x y who = 0 := by
  obtain ⟨C, hC⟩ := exists_abs_bound_of_finite
    (fun pair : I × J => D.reward pair.1 pair.2 who)
  have hupper := absorbingContribution_le_mul_mass D x y who C
    (fun i j => (abs_le.mp (hC (i, j))).2)
  have hlower := mul_mass_le_absorbingContribution D x y who (-C)
    (fun i j => (abs_le.mp (hC (i, j))).1)
  rw [hzero, mul_zero] at hupper hlower
  exact le_antisymm hupper hlower

omit [Fintype I] [Fintype J] in
/-- Every behavioral profile has the named absorber's constant stage payoff. -/
theorem expectedStagePayoff_some (D : Data I J) (σ : (game D).BehaviorProfile)
    (pair : I × J) (n : ℕ) (who : Bool) :
    (game D).expectedStagePayoff σ (some pair) n who = D.reward pair.1 pair.2 who := by
  unfold StochasticGame.expectedStagePayoff
  have hconstant : ∀ history ∈ ((game D).histDist σ (some pair) n).support,
      (game D).stageEUAt σ history who = D.reward pair.1 pair.2 who := by
    intro history hhistory
    have hstate := (game D).snd_eq_of_mem_support_histDist_of_isAbsorbingState
      (isAbsorbingState_some D pair) σ n history hhistory
    unfold StochasticGame.stageEUAt
    simp only [hstate, stagePayoff_some]
    exact expect_const _ _
  rw [Math.ProbabilityMassFunction.expect_congr_on_support _ _ _ hconstant]
  exact expect_const _ _

/-- The literal expected-pathwise-liminf payoff at an absorber is independent of all play. -/
theorem liminfPayoff_some (D : Data I J) (σ : (game D).BehaviorProfile)
    (pair : I × J) (who : Bool) :
    liminfPayoff D (some pair) σ who = D.reward pair.1 pair.2 who := by
  have hstage : Tendsto
      (fun n => (game D).expectedStagePayoff σ (some pair) n who) atTop
      (𝓝 (D.reward pair.1 pair.2 who)) := by
    simp only [expectedStagePayoff_some]
    exact tendsto_const_nhds
  have haverage : Tendsto (fun n => (game D).finiteAveragePayoff (some pair) n σ who)
      atTop (𝓝 (D.reward pair.1 pair.2 who)) := by
    exact hstage.cesaro.congr' (Eventually.of_forall fun n =>
      ((game D).finiteAveragePayoff_eq_sum_expectedStagePayoff σ (some pair) who n).symm)
  exact tendsto_nhds_unique (tendsto_finiteAveragePayoff_liminfPayoff D σ (some pair) who)
    haverage

omit [Fintype I] [Fintype J] in
/-- The actual stationary live-state stage payoff starts at zero. -/
theorem expectedStagePayoff_stationary_zero (D : Data I J) (x : PMF I) (y : PMF J)
    (who : Bool) : (game D).expectedStagePayoff (stationaryProfile D x y) none 0 who = 0 := by
  rw [(game D).expectedStagePayoff_zero (stationaryProfile D x y)
    (none : (game D).State) who]
  unfold StochasticGame.stageEUAt
  simp only [StochasticGame.emptyHist, stagePayoff_none]
  exact expect_const _ _

/-- First-stage disintegration gives the literal stationary payoff recurrence. -/
theorem expectedStagePayoff_stationary_succ (D : Data I J) (x : PMF I) (y : PMF J)
    (n : ℕ) (who : Bool) :
    (game D).expectedStagePayoff (stationaryProfile D x y) none (n + 1) who =
      (1 - absorptionMass D x y) *
          (game D).expectedStagePayoff (stationaryProfile D x y) none n who +
        absorbingContribution D x y who := by
  rw [(game D).expectedStagePayoff_succ_shift (stationaryProfile D x y)
    (none : (game D).State) n who]
  change expect ((game D).stageActionDist (stationaryProfile D x y)
      ((game D).emptyHist none))
    (fun action => expect ((game D).transition none action)
      (fun state => (game D).expectedStagePayoff (stationaryProfile D x y) state n who)) = _
  rw [expect_stationaryTransition_none]
  simp only [expectedStagePayoff_some]
  let value := (game D).expectedStagePayoff (stationaryProfile D x y) none n who
  have hpoint (i : I) (j : J) :
      (1 - (D.absorption i j : ℝ)) * value +
          (D.absorption i j : ℝ) * D.reward i j who =
        value - value * (D.absorption i j : ℝ) +
          (D.absorption i j : ℝ) * D.reward i j who := by ring
  change expect x (fun i => expect y (fun j =>
      (1 - (D.absorption i j : ℝ)) * value +
        (D.absorption i j : ℝ) * D.reward i j who)) =
    (1 - absorptionMass D x y) * value + absorbingContribution D x y who
  simp_rw [hpoint, expect_add, expect_sub, expect_const, expect_const_mul]
  change value - value * absorptionMass D x y + absorbingContribution D x y who = _
  ring

/-- The stationary ratio reconstructs its actual numerator, including zero mass. -/
theorem stationaryPayoff_mul_absorptionMass (D : Data I J) (x : PMF I) (y : PMF J)
    (who : Bool) : stationaryPayoff D x y who * absorptionMass D x y =
      absorbingContribution D x y who := by
  by_cases hzero : absorptionMass D x y = 0
  · rw [hzero, mul_zero, absorbingContribution_eq_zero_of_mass_eq_zero D x y who hzero]
  · exact div_mul_cancel₀ _ hzero

/-- The actual stage recurrence has the paper's geometric stationary solution. -/
theorem expectedStagePayoff_stationary_eq (D : Data I J) (x : PMF I) (y : PMF J)
    (n : ℕ) (who : Bool) :
    (game D).expectedStagePayoff (stationaryProfile D x y) none n who =
      stationaryPayoff D x y who * (1 - (1 - absorptionMass D x y) ^ n) := by
  induction n with
  | zero => simp only [expectedStagePayoff_stationary_zero, pow_zero, sub_self, mul_zero]
  | succ n ih =>
      rw [expectedStagePayoff_stationary_succ, ih, pow_succ,
        ← stationaryPayoff_mul_absorptionMass D x y who]
      ring

/-- Actual stationary stage payoffs converge to the ratio, even at zero absorption mass. -/
theorem tendsto_expectedStagePayoff_stationary (D : Data I J) (x : PMF I) (y : PMF J)
    (who : Bool) :
    Tendsto (fun n => (game D).expectedStagePayoff (stationaryProfile D x y) none n who)
      atTop (𝓝 (stationaryPayoff D x y who)) := by
  by_cases hzero : absorptionMass D x y = 0
  · have hratio : stationaryPayoff D x y who = 0 := by
      simp only [stationaryPayoff, hzero, div_zero]
    simp only [expectedStagePayoff_stationary_eq, hratio, zero_mul]
    exact tendsto_const_nhds
  · have hpositive : 0 < absorptionMass D x y :=
      lt_of_le_of_ne (absorptionMass_nonneg D x y) (Ne.symm hzero)
    have hsurvival : 0 ≤ 1 - absorptionMass D x y :=
      sub_nonneg.mpr (absorptionMass_le_one D x y)
    have hsurvival_lt : 1 - absorptionMass D x y < 1 := by linarith
    have hpow := tendsto_pow_atTop_nhds_zero_of_lt_one hsurvival hsurvival_lt
    have hlimit : Tendsto
        (fun n : ℕ => stationaryPayoff D x y who * (1 - (1 - absorptionMass D x y) ^ n))
        atTop (𝓝 (stationaryPayoff D x y who * (1 - 0))) :=
      tendsto_const_nhds.mul (tendsto_const_nhds.sub hpow)
    simpa only [expectedStagePayoff_stationary_eq, sub_zero, mul_one] using hlimit

/-- Lemma 2.2's ratio is the literal expected-pathwise-liminf stationary payoff. -/
theorem liminfPayoff_stationary_none (D : Data I J) (x : PMF I) (y : PMF J)
    (who : Bool) : liminfPayoff D none (stationaryProfile D x y) who =
      stationaryPayoff D x y who := by
  have haverage : Tendsto
      (fun n => (game D).finiteAveragePayoff none n (stationaryProfile D x y) who)
      atTop (𝓝 (stationaryPayoff D x y who)) :=
    (tendsto_expectedStagePayoff_stationary D x y who).cesaro.congr'
      (Eventually.of_forall fun n =>
        ((game D).finiteAveragePayoff_eq_sum_expectedStagePayoff
          (stationaryProfile D x y) none who n).symm)
  exact tendsto_nhds_unique
    (tendsto_finiteAveragePayoff_liminfPayoff D (stationaryProfile D x y) none who)
    haverage

end GameTheory.RecursiveAbsorption
