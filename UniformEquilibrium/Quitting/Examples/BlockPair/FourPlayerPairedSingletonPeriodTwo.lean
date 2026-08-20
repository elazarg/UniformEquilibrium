/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Examples.BlockPair.FourPlayerPairedSingleton
import UniformEquilibrium.Quitting.Examples.SolanVieilleBoundaryTable
import MathUE.PMFProduct.FiniteFubini
import UniformEquilibrium.Quitting.Cycles.AdmissibleCycleTerminalEquilibrium
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Topology.Order.IntermediateValue

/-!
# An exact period-two equilibrium on the Solan–Vieille boundary table

The table treated here is `GameTheory.SolanVieilleBoundary.boundaryReward`,
which is simultaneously the period-two completion of the four-player
paired-singleton family: its normalized singleton rows are
`pairedSingletonMatrix`, as `periodTwo_singletonMatrix` records.  Payoffs are
shifted playerwise so that perpetual continuation has value zero;
equivalently, every displayed absorbing payoff in the unshifted
paired-singleton table is increased by one.  This harmless normalization is
the convention used by the repository's quitting-game model.

An algebraic continuation probability `a` is selected as the unique root of

`44 a^4 - 7 a^3 - 26 a^2 + a + 3`

in `(1/2,1)`, and `b = (4a^2-1)/(3a^2)`.  The two product rows alternate
active pairs `{0,2}` and `{1,3}`, with continuation probabilities `a,b`.
-/

noncomputable section

namespace GameTheory
namespace FourPlayerPairedSingleton

open Filter Math.Probability Math.PMFProduct Math.ProbabilityMassFunction
  StochasticGame
open SolanVieilleBoundary (boundaryReward)

/-- The normalized singleton rows of the period-two completion have the
paired comparison matrix. -/
theorem periodTwo_singletonMatrix (who owner : Player) :
    QuittingLCPClassification.quittingSingletonMatrix boundaryReward who owner =
      pairedSingletonMatrix who owner := by
  rw [QuittingLCPClassification.quittingSingletonMatrix]
  fin_cases who <;> fin_cases owner <;>
    simp [boundaryReward, pairedSingletonMatrix] <;> norm_num

/-- The quartic selecting the exact period-two continuation probability. -/
def periodTwoPolynomial (x : ℝ) : ℝ :=
  44 * x ^ 4 - 7 * x ^ 3 - 26 * x ^ 2 + x + 3

theorem periodTwoPolynomial_thirtySeven_fiftieths :
    periodTwoPolynomial ((37 : ℝ) / 50) = -437733 / 3125000 := by
  norm_num [periodTwoPolynomial]

theorem periodTwoPolynomial_three_quarters :
    periodTwoPolynomial ((3 : ℝ) / 4) = 3 / 32 := by
  norm_num [periodTwoPolynomial]

/-- Substituting the rational expression for the secondary continuation
probability into the first active equation exposes the selecting quartic,
including the extraneous all-Continue factor `a - 1`. -/
theorem periodTwo_secondary_substitution_factorization
    {a : ℝ} (ha : a ≠ 0) :
    let b := (4 * a ^ 2 - 1) / (3 * a ^ 2)
    b * (1 - a + 3 * b - 2 * a * b) - 1 =
      -(a - 1) * periodTwoPolynomial a / (9 * a ^ 4) := by
  dsimp
  unfold periodTwoPolynomial
  field_simp [ha]
  ring

/-- The derivative has the displayed cubic form. -/
theorem deriv_periodTwoPolynomial (x : ℝ) :
    deriv periodTwoPolynomial x =
      176 * x ^ 3 - 21 * x ^ 2 - 52 * x + 1 := by
  change deriv (fun y : ℝ =>
    44 * y ^ 4 - 7 * y ^ 3 - 26 * y ^ 2 + y + 3) x = _
  have h4 := (hasDerivAt_pow 4 x).const_mul (44 : ℝ)
  have h3 := (hasDerivAt_pow 3 x).const_mul (7 : ℝ)
  have h2 := (hasDerivAt_pow 2 x).const_mul (26 : ℝ)
  have h := (((h4.sub h3).sub h2).add (hasDerivAt_id x)).add_const (3 : ℝ)
  convert h.deriv using 1
  all_goals norm_num
  all_goals ring

/-- Above `7/10`, the selecting quartic is strictly increasing. -/
theorem periodTwoPolynomial_strictMonoOn :
    StrictMonoOn periodTwoPolynomial (Set.Icc ((7 : ℝ) / 10) 1) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc ((7 : ℝ) / 10) 1)
    (by unfold periodTwoPolynomial; fun_prop)
  intro x hx
  rw [interior_Icc] at hx
  rw [deriv_periodTwoPolynomial]
  let t := x - (7 : ℝ) / 10
  have ht : 0 < t := by
    dsimp [t]
    norm_num at hx ⊢
    linarith
  have ht2 : 0 ≤ t ^ 2 := sq_nonneg t
  have ht3 : 0 ≤ t ^ 3 := by positivity
  have hid :
      176 * x ^ 3 - 21 * x ^ 2 - 52 * x + 1 =
        7339 / 500 + (4433 / 25) * t +
          (1743 / 5) * t ^ 2 + 176 * t ^ 3 := by
    dsimp [t]
    ring
  rw [hid]
  positivity

/-- The quartic is negative throughout `(1/2,7/10]`.  This exact Bernstein
certificate rules out a second root below the monotonicity interval. -/
theorem periodTwoPolynomial_neg_of_half_lt_of_le_seven_tenths
    {x : ℝ} (hx0 : (1 : ℝ) / 2 < x) (hx1 : x ≤ 7 / 10) :
    periodTwoPolynomial x < 0 := by
  let t := 5 * (x - (1 : ℝ) / 2)
  have ht0 : 0 ≤ t := by dsimp [t]; linarith
  have ht1 : t ≤ 1 := by dsimp [t]; linarith
  let w0 := (1 - t) ^ 4
  let w1 := 4 * t * (1 - t) ^ 3
  let w2 := 6 * t ^ 2 * (1 - t) ^ 2
  let w3 := 4 * t ^ 3 * (1 - t)
  let w4 := t ^ 4
  have hw0 : 0 ≤ w0 := by dsimp [w0]; positivity
  have hw1 : 0 ≤ w1 := by dsimp [w1]; positivity
  have hw2 : 0 ≤ w2 := by dsimp [w2]; positivity
  have hw3 : 0 ≤ w3 := by dsimp [w3]; positivity
  have hw4 : 0 ≤ w4 := by dsimp [w4]; positivity
  have hsum : w0 + w1 + w2 + w3 + w4 = 1 := by
    dsimp [w0, w1, w2, w3, w4]
    ring
  have hbernstein :
      periodTwoPolynomial x =
        (-9 / 8) * w0 + (-123 / 80) * w1 +
          (-263 / 150) * w2 + (-3221 / 2000) * w3 +
            (-4383 / 5000) * w4 := by
    dsimp [periodTwoPolynomial, t, w0, w1, w2, w3, w4]
    ring
  rw [hbernstein]
  have hbound :
      (-9 / 8 : ℝ) * w0 + (-123 / 80) * w1 +
          (-263 / 150) * w2 + (-3221 / 2000) * w3 +
            (-4383 / 5000) * w4 ≤
        (-4383 / 5000) * (w0 + w1 + w2 + w3 + w4) := by
    nlinarith
  rw [hsum] at hbound
  norm_num at hbound ⊢
  linarith

/-- The selecting quartic has a root in the explicit rational isolation
interval `(37/50,3/4)`. -/
theorem exists_periodTwoParameter_mem_isolatingInterval :
    ∃ a : ℝ,
      a ∈ Set.Ioo ((37 : ℝ) / 50) (3 / 4) ∧
        periodTwoPolynomial a = 0 := by
  have hleft : periodTwoPolynomial ((37 : ℝ) / 50) < 0 := by
    rw [periodTwoPolynomial_thirtySeven_fiftieths]
    norm_num
  have hright : 0 < periodTwoPolynomial ((3 : ℝ) / 4) := by
    rw [periodTwoPolynomial_three_quarters]
    norm_num
  have hcontinuous : ContinuousOn periodTwoPolynomial
      (Set.Icc ((37 : ℝ) / 50) (3 / 4)) := by
    unfold periodTwoPolynomial
    fun_prop
  obtain ⟨a, haIcc, haroot⟩ :=
    intermediate_value_Icc
      (by norm_num : (37 : ℝ) / 50 ≤ 3 / 4)
      hcontinuous ⟨hleft.le, hright.le⟩
  refine ⟨a, ⟨?_, ?_⟩, haroot⟩
  · exact lt_of_le_of_ne haIcc.1 fun h ↦ by
      subst a
      linarith
  · exact lt_of_le_of_ne haIcc.2 fun h ↦ by
      subst a
      linarith

/-- There is exactly one quartic root in `(1/2,1)`; it lies in the
rational isolating interval `(37/50,3/4)`. -/
theorem existsUnique_periodTwoParameter :
    ∃! a : ℝ,
      a ∈ Set.Ioo ((1 : ℝ) / 2) 1 ∧ periodTwoPolynomial a = 0 := by
  obtain ⟨a, haOpen, haroot⟩ :=
    exists_periodTwoParameter_mem_isolatingInterval
  refine ⟨a, ⟨⟨by norm_num at haOpen ⊢; linarith,
      by norm_num at haOpen ⊢; linarith⟩, haroot⟩, ?_⟩
  intro y hy
  have hySevenTenths : (7 : ℝ) / 10 < y := by
    by_contra h
    have hle : y ≤ 7 / 10 := le_of_not_gt h
    have hneg := periodTwoPolynomial_neg_of_half_lt_of_le_seven_tenths
      hy.1.1 hle
    linarith
  have haSevenTenths : (7 : ℝ) / 10 < a := by
    norm_num at haOpen ⊢
    linarith
  have haMem : a ∈ Set.Icc ((7 : ℝ) / 10) 1 :=
    ⟨haSevenTenths.le, by norm_num at haOpen ⊢; linarith⟩
  have hyMem : y ∈ Set.Icc ((7 : ℝ) / 10) 1 :=
    ⟨hySevenTenths.le, hy.1.2.le⟩
  exact (periodTwoPolynomial_strictMonoOn.injOn haMem hyMem
    (haroot.trans hy.2.symm)).symm

/-- The exact selected continuation probability. -/
def periodTwoParameter : ℝ :=
  Classical.choose existsUnique_periodTwoParameter

theorem periodTwoParameter_mem :
    periodTwoParameter ∈ Set.Ioo ((1 : ℝ) / 2) 1 :=
  (Classical.choose_spec existsUnique_periodTwoParameter).1.1

theorem periodTwoParameter_root :
    periodTwoPolynomial periodTwoParameter = 0 :=
  (Classical.choose_spec existsUnique_periodTwoParameter).1.2

theorem periodTwoParameter_pos : 0 < periodTwoParameter :=
  lt_trans (by norm_num) periodTwoParameter_mem.1

theorem periodTwoParameter_lt_one : periodTwoParameter < 1 :=
  periodTwoParameter_mem.2

/-- The chosen parameter retains the full rational isolation certificate. -/
theorem periodTwoParameter_mem_isolatingInterval :
    periodTwoParameter ∈ Set.Ioo ((37 : ℝ) / 50) (3 / 4) := by
  obtain ⟨a, haInterval, haroot⟩ :=
    exists_periodTwoParameter_mem_isolatingInterval
  have haMem : a ∈ Set.Ioo ((1 : ℝ) / 2) 1 := by
    constructor <;> norm_num at haInterval ⊢ <;> linarith
  have heq : a = periodTwoParameter :=
    (Classical.choose_spec existsUnique_periodTwoParameter).2 a
      ⟨haMem, haroot⟩
  rwa [← heq]

theorem periodTwoParameter_lt_three_quarters :
    periodTwoParameter < (3 : ℝ) / 4 :=
  periodTwoParameter_mem_isolatingInterval.2

theorem thirtySeven_fiftieths_lt_periodTwoParameter :
    (37 : ℝ) / 50 < periodTwoParameter := by
  exact periodTwoParameter_mem_isolatingInterval.1

/-- The second exact continuation probability. -/
def periodTwoSecondary : ℝ :=
  (4 * periodTwoParameter ^ 2 - 1) /
    (3 * periodTwoParameter ^ 2)

theorem periodTwoSecondary_pos : 0 < periodTwoSecondary := by
  have ha := periodTwoParameter_mem.1
  have ha2 : 0 < periodTwoParameter ^ 2 := sq_pos_of_pos periodTwoParameter_pos
  have hquarter : ((1 : ℝ) / 2) ^ 2 < periodTwoParameter ^ 2 :=
    by simpa [pow_two] using mul_self_lt_mul_self (by norm_num) ha
  unfold periodTwoSecondary
  apply div_pos
  · nlinarith
  · positivity

theorem periodTwoSecondary_lt_one : periodTwoSecondary < 1 := by
  have ha2 : 0 < periodTwoParameter ^ 2 := sq_pos_of_pos periodTwoParameter_pos
  have ha1 := periodTwoParameter_lt_one
  have haSq : periodTwoParameter ^ 2 < (1 : ℝ) ^ 2 :=
    by simpa [pow_two] using
      mul_self_lt_mul_self periodTwoParameter_pos.le ha1
  unfold periodTwoSecondary
  rw [div_lt_one (by positivity : 0 < 3 * periodTwoParameter ^ 2)]
  nlinarith

theorem one_half_lt_periodTwoSecondary :
    (1 : ℝ) / 2 < periodTwoSecondary := by
  have ha := thirtySeven_fiftieths_lt_periodTwoParameter
  have hlowerSq : ((37 : ℝ) / 50) ^ 2 < periodTwoParameter ^ 2 := by
    simpa [pow_two] using
      mul_self_lt_mul_self (by norm_num) ha
  have hden : 0 < 3 * periodTwoParameter ^ 2 := by positivity
  unfold periodTwoSecondary
  rw [lt_div_iff₀ hden]
  norm_num at hlowerSq ⊢
  nlinarith

theorem periodTwo_active_identity_second :
    periodTwoParameter ^ 2 * (4 - 3 * periodTwoSecondary) = 1 := by
  have hb :
      3 * periodTwoParameter ^ 2 * periodTwoSecondary =
        4 * periodTwoParameter ^ 2 - 1 := by
    unfold periodTwoSecondary
    field_simp [periodTwoParameter_pos.ne']
  nlinarith

theorem periodTwo_active_identity_first :
    periodTwoSecondary *
      (1 - periodTwoParameter + 3 * periodTwoSecondary -
        2 * periodTwoParameter * periodTwoSecondary) = 1 := by
  apply sub_eq_zero.mp
  rw [show periodTwoSecondary =
      (4 * periodTwoParameter ^ 2 - 1) /
        (3 * periodTwoParameter ^ 2) by rfl]
  rw [periodTwo_secondary_substitution_factorization
    periodTwoParameter_pos.ne']
  rw [periodTwoParameter_root]
  ring

/-- At the selected parameters, the first active equation is equivalent to
the vanishing of the all-Continue factor times the selecting quartic. -/
theorem periodTwo_active_first_iff_elimination_factor_zero :
    periodTwoSecondary *
        (1 - periodTwoParameter + 3 * periodTwoSecondary -
          2 * periodTwoParameter * periodTwoSecondary) = 1 ↔
      (periodTwoParameter - 1) *
        periodTwoPolynomial periodTwoParameter = 0 := by
  constructor
  · intro _
    rw [periodTwoParameter_root, mul_zero]
  · intro _
    exact periodTwo_active_identity_first

/-- The Boolean law whose continuation probability is `a`. -/
def primaryCoin : PMF Bool :=
  quittingHazardCoin (1 - periodTwoParameter)
    (sub_nonneg.mpr periodTwoParameter_lt_one.le)
    (by linarith [periodTwoParameter_pos])

/-- The Boolean law whose continuation probability is `b`. -/
def secondaryCoin : PMF Bool :=
  quittingHazardCoin (1 - periodTwoSecondary)
    (sub_nonneg.mpr periodTwoSecondary_lt_one.le)
    (by linarith [periodTwoSecondary_pos])

@[simp] theorem primaryCoin_true_toReal :
    (primaryCoin true).toReal = 1 - periodTwoParameter := by
  simp [primaryCoin]

@[simp] theorem primaryCoin_false_toReal :
    (primaryCoin false).toReal = periodTwoParameter := by
  simp [primaryCoin]

@[simp] theorem secondaryCoin_true_toReal :
    (secondaryCoin true).toReal = 1 - periodTwoSecondary := by
  simp [secondaryCoin]

@[simp] theorem secondaryCoin_false_toReal :
    (secondaryCoin false).toReal = periodTwoSecondary := by
  simp [secondaryCoin]

@[simp] theorem expect_primaryCoin (f : Bool → ℝ) :
    expect primaryCoin f =
      periodTwoParameter * f false +
        (1 - periodTwoParameter) * f true := by
  rw [expect_eq_sum, Fintype.sum_bool]
  simp
  ring

@[simp] theorem expect_secondaryCoin (f : Bool → ℝ) :
    expect secondaryCoin f =
      periodTwoSecondary * f false +
        (1 - periodTwoSecondary) * f true := by
  rw [expect_eq_sum, Fintype.sum_bool]
  simp
  ring

/-- The odd phase: players `0,2` are active. -/
def oddRoot : Player → PMF Bool := ![
  primaryCoin, PMF.pure false, secondaryCoin, PMF.pure false]

/-- The even phase: players `1,3` are active. -/
def evenRoot : Player → PMF Bool := ![
  PMF.pure false, primaryCoin, PMF.pure false, secondaryCoin]

/-- Conditional payoff at the odd phase. -/
def oddValue : Payoff Player := ![
  1, 1 / periodTwoSecondary, 1, 1 / periodTwoParameter]

/-- Conditional payoff at the even phase. -/
def evenValue : Payoff Player := ![
  1 / periodTwoSecondary, 1, 1 / periodTwoParameter, 1]

/-- The two displayed product roots are genuinely different: player `0`
has a positive Quit hazard in the odd phase and surely continues in the even
phase. -/
theorem oddRoot_ne_evenRoot : oddRoot ≠ evenRoot := by
  intro h
  have hprob := congrArg
    (fun root : Player → PMF Bool ↦ (root 0 true).toReal) h
  simp [oddRoot, evenRoot] at hprob
  linarith [periodTwoParameter_lt_one]

/-- The phase values are also different. -/
theorem oddValue_ne_evenValue : oddValue ≠ evenValue := by
  intro h
  have hcoordinate := congrFun h 0
  change (1 : ℝ) = 1 / periodTwoSecondary at hcoordinate
  have hsecondary : periodTwoSecondary = 1 := by
    have hmul := (eq_div_iff periodTwoSecondary_pos.ne').mp hcoordinate
    simpa using hmul
  exact (ne_of_lt periodTwoSecondary_lt_one) hsecondary

/-- One-stage value recursion at the odd phase. -/
theorem oddRoot_successor :
    quittingRootSuccessorPayoff boundaryReward evenValue oddRoot = oddValue := by
  funext who
  change quittingRootExpectedPayoff boundaryReward evenValue oddRoot who = _
  unfold quittingRootExpectedPayoff
  rw [Math.PMFProduct.expect_pmfPi_fin4]
  fin_cases who <;>
    simp [oddRoot, oddValue, evenValue, quittingRootPayoff, quittingQuitters,
      boundaryReward] <;>
    field_simp [periodTwoParameter_pos.ne', periodTwoSecondary_pos.ne'] <;>
    nlinarith [periodTwo_active_identity_first,
      periodTwo_active_identity_second]

/-- One-stage value recursion at the even phase. -/
theorem evenRoot_successor :
    quittingRootSuccessorPayoff boundaryReward oddValue evenRoot = evenValue := by
  funext who
  change quittingRootExpectedPayoff boundaryReward oddValue evenRoot who = _
  unfold quittingRootExpectedPayoff
  rw [Math.PMFProduct.expect_pmfPi_fin4]
  fin_cases who <;>
    simp [evenRoot, oddValue, evenValue, quittingRootPayoff, quittingQuitters,
      boundaryReward] <;>
    field_simp [periodTwoParameter_pos.ne', periodTwoSecondary_pos.ne'] <;>
    nlinarith [periodTwo_active_identity_first,
      periodTwo_active_identity_second]

/-- Exact endpoint differences at the odd phase. -/
theorem oddRoot_endpointDifference (who : Player) :
    quittingRootEndpointDifference boundaryReward evenValue oddRoot who =
      ![0,
        periodTwoParameter + periodTwoSecondary -
          periodTwoParameter * periodTwoSecondary -
            1 / periodTwoSecondary,
        0,
        1 - 1 / periodTwoParameter] who := by
  unfold quittingRootEndpointDifference quittingRootQuitPayoff
    quittingRootContinuePayoff quittingRootExpectedPayoff
  rw [Math.PMFProduct.expect_pmfPi_fin4, Math.PMFProduct.expect_pmfPi_fin4]
  fin_cases who <;>
    simp [oddRoot, evenValue, quittingRootPayoff, quittingQuitters,
      boundaryReward] <;>
    field_simp [periodTwoParameter_pos.ne', periodTwoSecondary_pos.ne'] <;>
    nlinarith [periodTwo_active_identity_first,
      periodTwo_active_identity_second]

/-- Exact endpoint differences at the even phase. -/
theorem evenRoot_endpointDifference (who : Player) :
    quittingRootEndpointDifference boundaryReward oddValue evenRoot who =
      ![periodTwoParameter + periodTwoSecondary -
          periodTwoParameter * periodTwoSecondary -
            1 / periodTwoSecondary,
        0,
        1 - 1 / periodTwoParameter,
        0] who := by
  unfold quittingRootEndpointDifference quittingRootQuitPayoff
    quittingRootContinuePayoff quittingRootExpectedPayoff
  rw [Math.PMFProduct.expect_pmfPi_fin4, Math.PMFProduct.expect_pmfPi_fin4]
  fin_cases who <;>
    simp [evenRoot, oddValue, quittingRootPayoff, quittingQuitters,
      boundaryReward] <;>
    field_simp [periodTwoParameter_pos.ne', periodTwoSecondary_pos.ne'] <;>
    nlinarith [periodTwo_active_identity_first,
      periodTwo_active_identity_second]

theorem inactivePairGap_neg :
    periodTwoParameter + periodTwoSecondary -
        periodTwoParameter * periodTwoSecondary -
          1 / periodTwoSecondary < 0 := by
  have hab :
      periodTwoParameter + periodTwoSecondary -
          periodTwoParameter * periodTwoSecondary < 1 := by
    nlinarith [mul_pos (sub_pos.mpr periodTwoParameter_lt_one)
      (sub_pos.mpr periodTwoSecondary_lt_one)]
  have hinv : 1 < 1 / periodTwoSecondary := by
    rw [lt_div_iff₀ periodTwoSecondary_pos]
    simpa using periodTwoSecondary_lt_one
  linarith

theorem inactivePrimaryGap_neg :
    1 - 1 / periodTwoParameter < 0 := by
  rw [sub_neg, lt_div_iff₀ periodTwoParameter_pos]
  simpa using periodTwoParameter_lt_one

/-- The odd row is exact endpoint Nash against the even continuation value. -/
theorem oddRoot_isZeroEndpointNash :
    IsεQuittingRootEndpointNash boundaryReward evenValue 0 oddRoot := by
  intro who
  rw [oddRoot_endpointDifference]
  have hpair :
      periodTwoParameter + periodTwoSecondary ≤
        periodTwoSecondary⁻¹ +
          periodTwoParameter * periodTwoSecondary := by
    have h := inactivePairGap_neg
    rw [div_eq_mul_inv] at h
    linarith
  have hprimary : 1 ≤ periodTwoParameter⁻¹ := by
    have h := inactivePrimaryGap_neg
    rw [div_eq_mul_inv] at h
    linarith
  fin_cases who <;> simp [oddRoot, hpair, hprimary]

/-- The even row is exact endpoint Nash against the odd continuation value. -/
theorem evenRoot_isZeroEndpointNash :
    IsεQuittingRootEndpointNash boundaryReward oddValue 0 evenRoot := by
  intro who
  rw [evenRoot_endpointDifference]
  have hpair :
      periodTwoParameter + periodTwoSecondary ≤
        periodTwoSecondary⁻¹ +
          periodTwoParameter * periodTwoSecondary := by
    have h := inactivePairGap_neg
    rw [div_eq_mul_inv] at h
    linarith
  have hprimary : 1 ≤ periodTwoParameter⁻¹ := by
    have h := inactivePrimaryGap_neg
    rw [div_eq_mul_inv] at h
    linarith
  fin_cases who <;> simp [evenRoot, hpair, hprimary]

/-! ## The exact cyclic block -/

def oddSimplexRoot : QuittingRootSimplex Player :=
  fun who => stdSimplexEquiv (oddRoot who)

def evenSimplexRoot : QuittingRootSimplex Player :=
  fun who => stdSimplexEquiv (evenRoot who)

@[simp] theorem quittingRootOfSimplex_oddSimplexRoot :
    quittingRootOfSimplex oddSimplexRoot = oddRoot := by
  funext who
  exact (stdSimplexEquiv (α := Bool)).symm_apply_apply (oddRoot who)

@[simp] theorem quittingRootOfSimplex_evenSimplexRoot :
    quittingRootOfSimplex evenSimplexRoot = evenRoot := by
  funext who
  exact (stdSimplexEquiv (α := Bool)).symm_apply_apply (evenRoot who)

def oddPoint : QuittingNashBellmanPoint Player :=
  (oddValue, oddSimplexRoot)

def evenPoint : QuittingNashBellmanPoint Player :=
  (evenValue, evenSimplexRoot)

/-- The two phases followed by the repeated origin. -/
def periodTwoBlock : QuittingFiniteNashBellmanPath Player 2 :=
  ![oddPoint, evenPoint, oddPoint]

theorem four_le_boundaryRewardBound :
    (4 : ℝ) ≤ quittingRewardBound boundaryReward := by
  have h := abs_reward_le_quittingRewardBound boundaryReward
    (quittingSingletonTerminal 0) 1
  simpa [boundaryReward, quittingSingletonTerminal] using h

theorem oddPoint_mem_box :
    oddPoint ∈ quittingNashBellmanBox
      (quittingRewardBound boundaryReward) := by
  have hbound := four_le_boundaryRewardBound
  have haInvPos : 0 < periodTwoParameter⁻¹ :=
    inv_pos.mpr periodTwoParameter_pos
  have hbInvPos : 0 < periodTwoSecondary⁻¹ :=
    inv_pos.mpr periodTwoSecondary_pos
  have haInv : periodTwoParameter⁻¹ < 2 := by
    have hdiv : (1 : ℝ) / periodTwoParameter < 2 := by
      rw [div_lt_iff₀ periodTwoParameter_pos]
      nlinarith [periodTwoParameter_mem.1]
    simpa [one_div] using hdiv
  have hbInv : periodTwoSecondary⁻¹ < 2 := by
    have hdiv : (1 : ℝ) / periodTwoSecondary < 2 := by
      rw [div_lt_iff₀ periodTwoSecondary_pos]
      nlinarith [one_half_lt_periodTwoSecondary]
    simpa [one_div] using hdiv
  change oddValue ∈
    Set.Icc (fun _ : Player => -(quittingRewardBound boundaryReward))
      (fun _ => quittingRewardBound boundaryReward)
  constructor <;> intro who <;> fin_cases who <;>
    simp [oddValue] <;> linarith

theorem evenPoint_mem_box :
    evenPoint ∈ quittingNashBellmanBox
      (quittingRewardBound boundaryReward) := by
  have hbound := four_le_boundaryRewardBound
  have haInvPos : 0 < periodTwoParameter⁻¹ :=
    inv_pos.mpr periodTwoParameter_pos
  have hbInvPos : 0 < periodTwoSecondary⁻¹ :=
    inv_pos.mpr periodTwoSecondary_pos
  have haInv : periodTwoParameter⁻¹ < 2 := by
    have hdiv : (1 : ℝ) / periodTwoParameter < 2 := by
      rw [div_lt_iff₀ periodTwoParameter_pos]
      nlinarith [periodTwoParameter_mem.1]
    simpa [one_div] using hdiv
  have hbInv : periodTwoSecondary⁻¹ < 2 := by
    have hdiv : (1 : ℝ) / periodTwoSecondary < 2 := by
      rw [div_lt_iff₀ periodTwoSecondary_pos]
      nlinarith [one_half_lt_periodTwoSecondary]
    simpa [one_div] using hdiv
  change evenValue ∈
    Set.Icc (fun _ : Player => -(quittingRewardBound boundaryReward))
      (fun _ => quittingRewardBound boundaryReward)
  constructor <;> intro who <;> fin_cases who <;>
    simp [evenValue] <;> linarith

theorem oddPoint_edge_evenPoint :
    IsQuittingNashBellmanEdge boundaryReward oddPoint evenPoint := by
  constructor
  · change oddValue =
      quittingRootSuccessorPayoff boundaryReward evenValue
        (quittingRootOfSimplex oddSimplexRoot)
    rw [quittingRootOfSimplex_oddSimplexRoot, oddRoot_successor]
  · change IsεQuittingRootEndpointNash boundaryReward evenValue 0
      (quittingRootOfSimplex oddSimplexRoot)
    rw [quittingRootOfSimplex_oddSimplexRoot]
    exact oddRoot_isZeroEndpointNash

theorem evenPoint_edge_oddPoint :
    IsQuittingNashBellmanEdge boundaryReward evenPoint oddPoint := by
  constructor
  · change evenValue =
      quittingRootSuccessorPayoff boundaryReward oddValue
        (quittingRootOfSimplex evenSimplexRoot)
    rw [quittingRootOfSimplex_evenSimplexRoot, evenRoot_successor]
  · change IsεQuittingRootEndpointNash boundaryReward oddValue 0
      (quittingRootOfSimplex evenSimplexRoot)
    rw [quittingRootOfSimplex_evenSimplexRoot]
    exact evenRoot_isZeroEndpointNash

theorem oddRoot_continueMass :
    quittingStationaryContinueMass oddRoot =
      periodTwoParameter * periodTwoSecondary := by
  rw [quittingStationaryContinueMass_eq_prod_continueProbability]
  simp [oddRoot, Fin.prod_univ_succ]

theorem evenRoot_continueMass :
    quittingStationaryContinueMass evenRoot =
      periodTwoParameter * periodTwoSecondary := by
  rw [quittingStationaryContinueMass_eq_prod_continueProbability]
  simp [evenRoot, Fin.prod_univ_succ]

theorem oddRoot_absorption_pos :
    0 < quittingRootAbsorptionMass oddRoot := by
  rw [quittingRootAbsorptionMass, oddRoot_continueMass]
  have hmul : periodTwoParameter * periodTwoSecondary < 1 := by
    have h := mul_pos periodTwoParameter_pos
      (sub_pos.mpr periodTwoSecondary_lt_one)
    nlinarith [periodTwoParameter_lt_one]
  linarith

/-- The two displayed rows form an absorbing exact Nash--Bellman cycle. -/
theorem periodTwoBlock_isQuittingCyclicContinuationBlock :
    IsQuittingCyclicContinuationBlock boundaryReward oddValue 2
      periodTwoBlock := by
  refine ⟨⟨?_, ?_, ?_⟩, rfl, ⟨0, ?_⟩⟩
  · intro time
    fin_cases time
    · exact oddPoint_mem_box
    · exact evenPoint_mem_box
    · exact oddPoint_mem_box
  · rfl
  · intro time
    fin_cases time
    · exact oddPoint_edge_evenPoint
    · exact evenPoint_edge_oddPoint
  · change 0 < quittingRootAbsorptionMass
      (quittingRootOfSimplex oddSimplexRoot)
    rw [quittingRootOfSimplex_oddSimplexRoot]
    exact oddRoot_absorption_pos

@[simp] theorem quittingCyclicContinuationBlockCycle_periodTwoBlock
    (stage : Fin 2) :
    quittingCyclicContinuationBlockCycle 1 periodTwoBlock stage =
      ![oddRoot, evenRoot] stage := by
  fin_cases stage
  · exact quittingRootOfSimplex_oddSimplexRoot
  · exact quittingRootOfSimplex_evenSimplexRoot

/-- Admissibility is automatic: every own-singleton payoff in the shifted
table equals one. -/
theorem periodTwoBlockCycle_isAdmissible :
    IsQuittingCycleAdmissible boundaryReward
      (quittingCyclicContinuationBlockCycle 1 periodTwoBlock) := by
  intro who
  refine Or.inr ?_
  fin_cases who <;>
    simp [boundaryReward, quittingSingletonTerminal]

/-- The exact alternating behavioral profile. -/
def periodTwoProfile : (quittingGame boundaryReward).BehaviorProfile :=
  quittingCyclicContinuationBlockProfile boundaryReward 1 periodTwoBlock 0

/-- The alternating profile is exact terminal Nash against every behavioral
deviation. -/
theorem periodTwoProfile_isExactTerminalNash :
    (quittingGame boundaryReward).IsεAsymptoticNash
      (quittingTerminalPayoff boundaryReward) 0 periodTwoProfile :=
  isZeroAsymptoticNash_quittingCyclicContinuationBlockProfile
    boundaryReward oddValue 1 periodTwoBlock
      periodTwoBlock_isQuittingCyclicContinuationBlock
      periodTwoBlockCycle_isAdmissible 0

/-- The exact alternating profile is a literal zero-debt carrier for the
canonical maximum all-behavior terminal exploitability. -/
theorem periodTwoProfile_terminalExploitability_eq_zero :
    quittingTerminalExploitability boundaryReward periodTwoProfile = 0 := by
  apply le_antisymm
  · unfold quittingTerminalExploitability
    apply QuittingBoundaryHolonomy.finitePlayerMax_le
    intro who
    apply max_le
    · exact le_rfl
    · have hbest : quittingContinuationBestResponseValue
          boundaryReward periodTwoProfile who ≤
        quittingTerminalPayoff boundaryReward periodTwoProfile who := by
        unfold quittingContinuationBestResponseValue
        apply csSup_le
        · exact ⟨_, periodTwoProfile who, rfl⟩
        · rintro value ⟨deviation, rfl⟩
          simpa using periodTwoProfile_isExactTerminalNash who deviation
      linarith
  · exact quittingTerminalExploitability_nonneg _ _

/-- The period-two completion has zero canonical semantic min-max
exploitability: the infimum over all behavior profiles of maximum positive
unilateral terminal gain is exactly zero. -/
theorem periodTwo_terminalExploitabilityInf_eq_zero :
    quittingTerminalExploitabilityInf boundaryReward = 0 := by
  apply le_antisymm
  · exact (quittingTerminalExploitabilityInf_le
      boundaryReward periodTwoProfile).trans_eq
      periodTwoProfile_terminalExploitability_eq_zero
  · unfold quittingTerminalExploitabilityInf
    have hprofiles : Set.Nonempty
        (Set.range fun profile :
            (quittingGame boundaryReward).BehaviorProfile ↦
          quittingTerminalExploitability boundaryReward profile) :=
      ⟨_, periodTwoProfile, rfl⟩
    apply le_csInf hprofiles
    rintro value ⟨profile, rfl⟩
    exact quittingTerminalExploitability_nonneg _ _

theorem periodTwoProfile_terminalPayoff :
    quittingTerminalPayoff boundaryReward periodTwoProfile = oddValue :=
  quittingTerminalPayoff_quittingCyclicContinuationBlockProfile
    boundaryReward oddValue 1 periodTwoBlock
      periodTwoBlock_isQuittingCyclicContinuationBlock

/-- The period-two completion has the exact uniform-equilibrium payoff
`(1,1/b,1,1/a)` in the shifted normalization. -/
theorem periodTwo_isUniformEquilibriumPayoff :
    (quittingGame boundaryReward).IsUniformEquilibriumPayoff none oddValue :=
  isUniformEquilibriumPayoff_terminal_of_admissible_quittingCyclicContinuationBlock
    boundaryReward oddValue 1 periodTwoBlock
      periodTwoBlock_isQuittingCyclicContinuationBlock
      periodTwoBlockCycle_isAdmissible

end FourPlayerPairedSingleton
end GameTheory
