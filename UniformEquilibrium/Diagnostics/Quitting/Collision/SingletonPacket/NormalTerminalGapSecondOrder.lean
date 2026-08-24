/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import Mathlib.Algebra.Polynomial.Div
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Polynomial
import
  UniformEquilibrium.Diagnostics.Quitting.Collision.SingletonPacket.NormalTerminalGapConstrainedStationary

/-!
# Radial second-order data of constrained stationary face roots

The normal terminal-gap construction retains exact face numerators before
passing to its normalized singleton limit.  This file records their radial
polynomial, so the coefficient after the singleton term is available without
postulating a jet.

The coefficient of degree two contains literal two-quitter rewards.  Exact
interior face equations do not, by themselves, give it a sign: motion of the
normalized hazard direction contributes at the same order.  The final lemma
records the correct finite-dimensional conclusion.  Even if those normalized
direction quotients are unbounded, convergence of their image under the
singleton linearization gives an actual correction vector because a
finite-dimensional linear range is closed.
-/

noncomputable section

namespace GameTheory

open Filter Polynomial Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The polynomial hazard row obtained by radially scaling a fixed direction. -/
def quittingRadialHazardPolynomial (direction : ι → ℝ) : ι → ℝ[X] :=
  fun owner => C (direction owner) * X

/-- The opponents' all-Continue mass along a radial hazard ray. -/
def quittingRadialContinueMassExclPolynomial
    (direction : ι → ℝ) (who : ι) : ℝ[X] :=
  ∏ owner ∈ Finset.univ.erase who,
    (1 - quittingRadialHazardPolynomial direction owner)

/-- The pure-Quit endpoint along a radial hazard ray. -/
def quittingRadialSigmaPolynomial
    (weight : Finset ι → ι → ℝ) (direction : ι → ℝ) (who : ι) : ℝ[X] :=
  ∑ coalition ∈ (Finset.univ.erase who).powerset,
    (∏ owner ∈ coalition, quittingRadialHazardPolynomial direction owner) *
      (∏ owner ∈ Finset.univ.erase who \ coalition,
        (1 - quittingRadialHazardPolynomial direction owner)) *
      C (weight (insert who coalition) who)

/-- The nonempty-opponent absorbing contribution along a radial hazard ray. -/
def quittingRadialExcludedPolynomial
    (weight : Finset ι → ι → ℝ) (direction : ι → ℝ) (who : ι) : ℝ[X] :=
  ∑ coalition ∈ (Finset.univ.erase who).powerset.erase ∅,
    (∏ owner ∈ coalition, quittingRadialHazardPolynomial direction owner) *
      (∏ owner ∈ Finset.univ.erase who \ coalition,
        (1 - quittingRadialHazardPolynomial direction owner)) *
      C (weight coalition who)

/-- The exact face numerator as a polynomial in radial scale. -/
def quittingRadialFacePolynomial
    (weight : Finset ι → ι → ℝ) (direction : ι → ℝ) (who : ι) : ℝ[X] :=
  (1 - quittingRadialContinueMassExclPolynomial direction who) *
      quittingRadialSigmaPolynomial weight direction who -
    quittingRadialExcludedPolynomial weight direction who

/-- Evaluation of the radial Continue polynomial is the literal product law. -/
theorem eval_quittingRadialContinueMassExclPolynomial
    (direction : ι → ℝ) (who : ι) (scale : ℝ) :
    (quittingRadialContinueMassExclPolynomial direction who).eval scale =
      continueMassExcl (fun owner => scale * direction owner) who := by
  simp only [quittingRadialContinueMassExclPolynomial,
    quittingRadialHazardPolynomial, eval_prod, eval_sub, eval_one, eval_mul,
    eval_C, eval_X, continueMassExcl]
  apply Finset.prod_congr rfl
  intro owner _
  ring

/-- Evaluation of the radial pure-Quit polynomial is the literal endpoint. -/
theorem eval_quittingRadialSigmaPolynomial
    (weight : Finset ι → ι → ℝ) (direction : ι → ℝ) (who : ι)
    (scale : ℝ) :
    (quittingRadialSigmaPolynomial weight direction who).eval scale =
      sigmaValue weight (fun owner => scale * direction owner) who := by
  unfold quittingRadialSigmaPolynomial sigmaValue
  change (evalRingHom scale)
      (∑ coalition ∈ (Finset.univ.erase who).powerset,
        (∏ owner ∈ coalition, quittingRadialHazardPolynomial direction owner) *
          (∏ owner ∈ Finset.univ.erase who \ coalition,
            (1 - quittingRadialHazardPolynomial direction owner)) *
          C (weight (insert who coalition) who)) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro coalition hcoalition
  simp only [map_mul, map_prod, map_sub, map_one, coe_evalRingHom,
    quittingRadialHazardPolynomial, eval_C, eval_X]
  have hacting :
      (∏ owner ∈ coalition, direction owner * scale) =
        ∏ owner ∈ coalition, scale * direction owner := by
    apply Finset.prod_congr rfl
    intro owner _
    ring
  have hcontinue :
      (∏ owner ∈ Finset.univ.erase who \ coalition,
          (1 - direction owner * scale)) =
        ∏ owner ∈ Finset.univ.erase who \ coalition,
          (1 - scale * direction owner) := by
    apply Finset.prod_congr rfl
    intro owner _
    ring
  rw [hacting, hcontinue]

/-- Evaluation of the radial Continue contribution is the literal endpoint. -/
theorem eval_quittingRadialExcludedPolynomial
    (weight : Finset ι → ι → ℝ) (direction : ι → ℝ) (who : ι)
    (scale : ℝ) :
    (quittingRadialExcludedPolynomial weight direction who).eval scale =
      excludedValue weight (fun owner => scale * direction owner) who := by
  unfold quittingRadialExcludedPolynomial excludedValue
  change (evalRingHom scale)
      (∑ coalition ∈ (Finset.univ.erase who).powerset.erase ∅,
        (∏ owner ∈ coalition, quittingRadialHazardPolynomial direction owner) *
          (∏ owner ∈ Finset.univ.erase who \ coalition,
            (1 - quittingRadialHazardPolynomial direction owner)) *
          C (weight coalition who)) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro coalition hcoalition
  simp only [map_mul, map_prod, map_sub, map_one, coe_evalRingHom,
    quittingRadialHazardPolynomial, eval_C, eval_X]
  have hacting :
      (∏ owner ∈ coalition, direction owner * scale) =
        ∏ owner ∈ coalition, scale * direction owner := by
    apply Finset.prod_congr rfl
    intro owner _
    ring
  have hcontinue :
      (∏ owner ∈ Finset.univ.erase who \ coalition,
          (1 - direction owner * scale)) =
        ∏ owner ∈ Finset.univ.erase who \ coalition,
          (1 - scale * direction owner) := by
    apply Finset.prod_congr rfl
    intro owner _
    ring
  rw [hacting, hcontinue]

/-- The radial polynomial evaluates to the exact stationary face numerator. -/
theorem eval_quittingRadialFacePolynomial
    (weight : Finset ι → ι → ℝ) (direction : ι → ℝ) (who : ι)
    (scale : ℝ) :
    (quittingRadialFacePolynomial weight direction who).eval scale =
      quittingFaceNumerator weight (fun owner => scale * direction owner) who := by
  simp only [quittingRadialFacePolynomial, eval_sub, eval_mul, eval_one,
    eval_quittingRadialContinueMassExclPolynomial,
    eval_quittingRadialSigmaPolynomial,
    eval_quittingRadialExcludedPolynomial, quittingFaceNumerator]

/-- The radial face polynomial has no constant term. -/
theorem coeff_zero_quittingRadialFacePolynomial
    (weight : Finset ι → ι → ℝ) (direction : ι → ℝ) (who : ι) :
    (quittingRadialFacePolynomial weight direction who).coeff 0 = 0 := by
  rw [coeff_zero_eq_eval_zero,
    eval_quittingRadialFacePolynomial]
  have hcontinue : continueMassExcl (fun _ : ι => (0 : ℝ)) who = 1 := by
    simp [continueMassExcl]
  have hexcluded : excludedValue weight (fun _ : ι => (0 : ℝ)) who = 0 := by
    unfold excludedValue
    apply Finset.sum_eq_zero
    intro coalition hcoalition
    have hnonempty : coalition.Nonempty := by
      exact Finset.nonempty_iff_ne_empty.mpr (Finset.mem_erase.mp hcoalition).1
    obtain ⟨owner, howner⟩ := hnonempty
    have hzero : (∏ player ∈ coalition, (0 : ℝ)) = 0 :=
      Finset.prod_eq_zero howner rfl
    rw [hzero]
    ring
  simp only [zero_mul]
  rw [quittingFaceNumerator, hcontinue, hexcluded]
  ring

/-- The singleton and pair layers of the exact radial face equation. -/
structure QuittingRadialFaceTwoJet
    (weight : Finset ι → ι → ℝ) (direction : ι → ℝ) (who : ι) where
  /-- The singleton coefficient. -/
  linear : ℝ := (quittingRadialFacePolynomial weight direction who).coeff 1
  /-- The coefficient containing the literal two-quitter rewards. -/
  quadratic : ℝ := (quittingRadialFacePolynomial weight direction who).coeff 2

/-- Remove the constant and linear coefficients of a real polynomial and
divide the result by `X^2`. -/
def polynomialQuadraticTail (polynomial : ℝ[X]) : ℝ[X] :=
  (polynomial - C (polynomial.coeff 0) - C (polynomial.coeff 1) * X) /ₘ X ^ 2

/-- Exact reconstruction from the constant, linear, and quadratic tail. -/
theorem polynomial_eq_constant_add_linear_add_sq_mul_quadraticTail
    (polynomial : ℝ[X]) :
    polynomial = C (polynomial.coeff 0) + C (polynomial.coeff 1) * X +
      X ^ 2 * polynomialQuadraticTail polynomial := by
  let remainder :=
    polynomial - C (polynomial.coeff 0) - C (polynomial.coeff 1) * X
  have hcoeff : ∀ degree < 2, remainder.coeff degree = 0 := by
    intro degree hdegree
    interval_cases degree <;> simp [remainder]
  have hdivides : X ^ 2 ∣ remainder := X_pow_dvd_iff.mpr hcoeff
  have hmonic : (X ^ 2 : ℝ[X]).Monic := monic_X.pow 2
  have hmod : remainder %ₘ X ^ 2 = 0 :=
    (modByMonic_eq_zero_iff_dvd hmonic).2 hdivides
  have hcancel : X ^ 2 * (remainder /ₘ X ^ 2) = remainder := by
    have hdivision := modByMonic_add_div remainder (X ^ 2)
    rw [hmod, zero_add] at hdivision
    exact hdivision
  dsimp only [polynomialQuadraticTail]
  rw [show polynomial - C (polynomial.coeff 0) -
      C (polynomial.coeff 1) * X = remainder by rfl]
  rw [hcancel]
  dsimp only [remainder]
  ring

/-- The quadratic tail evaluates at zero to the quadratic coefficient. -/
theorem polynomialQuadraticTail_eval_zero (polynomial : ℝ[X]) :
    (polynomialQuadraticTail polynomial).eval 0 = polynomial.coeff 2 := by
  have hidentity := congrArg (fun p : ℝ[X] => p.coeff 2)
    (polynomial_eq_constant_add_linear_add_sq_mul_quadraticTail polynomial)
  have htailCoeff :
      (X ^ 2 * polynomialQuadraticTail polynomial).coeff 2 =
        (polynomialQuadraticTail polynomial).coeff 0 := by
    simpa using coeff_X_pow_mul (polynomialQuadraticTail polynomial) 2 0
  simp only [coeff_add] at hidentity
  rw [htailCoeff] at hidentity
  norm_num [coeff_C, coeff_mul_X] at hidentity
  rw [coeff_zero_eq_eval_zero] at hidentity
  exact hidentity.symm

/-- Dividing an exact polynomial by its radial scale twice after subtracting
the singleton term converges to the literal quadratic coefficient. -/
theorem tendsto_polynomial_secondCoefficient
    (polynomial : ℝ[X]) (hconstant : polynomial.coeff 0 = 0) :
    Tendsto
      (fun scale : ℝ =>
        (polynomial.eval scale - scale * polynomial.coeff 1) / scale ^ 2)
      (nhdsWithin 0 {0}ᶜ) (nhds (polynomial.coeff 2)) := by
  have heventually : ∀ᶠ scale : ℝ in nhdsWithin 0 {0}ᶜ,
      (polynomial.eval scale - scale * polynomial.coeff 1) / scale ^ 2 =
        (polynomialQuadraticTail polynomial).eval scale := by
    filter_upwards [self_mem_nhdsWithin] with scale hscale
    have hscaleNe : scale ≠ 0 := by simpa using hscale
    have hidentity := congrArg (fun p : ℝ[X] => p.eval scale)
      (polynomial_eq_constant_add_linear_add_sq_mul_quadraticTail polynomial)
    simp only [eval_add, eval_C, eval_mul, eval_X, eval_pow] at hidentity
    rw [hconstant, zero_add] at hidentity
    rw [hidentity]
    field_simp
    ring
  have htail : Tendsto
      (fun scale : ℝ => (polynomialQuadraticTail polynomial).eval scale)
      (nhdsWithin 0 {0}ᶜ)
      (nhds ((polynomialQuadraticTail polynomial).eval 0)) :=
    (polynomialQuadraticTail polynomial).continuous.continuousAt.tendsto.mono_left
      inf_le_left
  rw [← polynomialQuadraticTail_eval_zero polynomial]
  have heventuallySymm :
      (fun scale : ℝ => (polynomialQuadraticTail polynomial).eval scale) =ᶠ[
        nhdsWithin 0 {0}ᶜ]
      (fun scale : ℝ =>
        (polynomial.eval scale - scale * polynomial.coeff 1) / scale ^ 2) := by
    filter_upwards [heventually] with scale hscale
    exact hscale.symm
  exact htail.congr' heventuallySymm

/-- **Exact second-order readout of a constrained radial face.**  The
subtracted term is precisely the degree-one singleton face equation; the
limit is the degree-two coefficient of the literal product-law numerator. -/
theorem tendsto_quittingRadialFace_secondCoefficient
    (weight : Finset ι → ι → ℝ) (direction : ι → ℝ) (who : ι) :
    Tendsto
      (fun scale : ℝ =>
        (quittingFaceNumerator weight
            (fun owner => scale * direction owner) who -
          scale * (quittingRadialFacePolynomial weight direction who).coeff 1) /
            scale ^ 2)
      (nhdsWithin 0 {0}ᶜ)
      (nhds ((quittingRadialFacePolynomial weight direction who).coeff 2)) := by
  simpa only [eval_quittingRadialFacePolynomial] using
    tendsto_polynomial_secondCoefficient
      (quittingRadialFacePolynomial weight direction who)
      (coeff_zero_quittingRadialFacePolynomial weight direction who)

/-! ## What the fixed terminal gap actually says at the selected face -/

/-- A positive unrestricted full-rate gain makes a nonpositive face numerator
strictly negative.  Hence the player selected by the terminal gap is a
first-order strict row, not a source of a quadratic equality. -/
theorem quittingFaceNumerator_lt_zero_of_fullRateGain
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {gap : ℝ} (hgap : 0 < gap)
    (hazard : ι → ℝ) (hhazard0 : ∀ who, 0 ≤ hazard who)
    (hhazard1 : ∀ who, hazard who ≤ 1) (who : ι)
    (hcontracts : quittingStationaryFixedOpponentsContinueMass
      (rootOfHazard hazard hhazard0 hhazard1) who < 1)
    (habsorption : 0 < quittingRootAbsorptionMass
      (rootOfHazard hazard hhazard0 hhazard1))
    (hnumerator : quittingFaceNumerator
      (weightOfReward reward) hazard who ≤ 0)
    (hgain : quittingTerminalPayoff reward
          (quittingStationaryProfile reward
            (rootOfHazard hazard hhazard0 hhazard1)) who + gap ≤
        quittingStationaryFullRateUnilateralCap reward
          (rootOfHazard hazard hhazard0 hhazard1) who) :
    quittingFaceNumerator (weightOfReward reward) hazard who < 0 := by
  apply lt_of_le_of_ne hnumerator
  intro hzero
  have hzero' : quittingFaceNumerator
      (weightOfReward reward) hazard who = 0 := hzero
  let root := rootOfHazard hazard hhazard0 hhazard1
  have hstationaryGain : quittingStationaryGain reward root who = 0 := by
    rw [quittingStationaryGain_rootOfHazard_eq_faceNumerator
      reward hazard hhazard0 hhazard1 who]
    exact hzero'
  have hcap := quittingStationaryFullRateUnilateralCap_le_of_gain_signs
    reward root who hcontracts habsorption (by simp [hstationaryGain])
      (by simp [hstationaryGain])
  linarith

/-- At every genuine constrained root, terminal exploitability selects a
lower-face coordinate with a strictly negative exact face numerator. -/
theorem exists_lowerFace_strictFaceNumerator_of_terminalGap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {epsilon gap : ℝ} (hepsilon0 : 0 < epsilon)
    (hepsilon1 : epsilon < 1) (hgap : 0 < gap)
    (hazard : ι → ℝ) (hhazardLower : ∀ who, epsilon ≤ hazard who)
    (hhazardUpper : ∀ who, hazard who ≤ 1)
    (hbest : ∀ who rate, epsilon ≤ rate → rate ≤ 1 →
      rate * quittingFaceNumerator (weightOfReward reward) hazard who ≤
        hazard who * quittingFaceNumerator
          (weightOfReward reward) hazard who)
    (hcontracts : ∀ who,
      quittingStationaryFixedOpponentsContinueMass
        (rootOfHazard hazard
          (fun who => hepsilon0.le.trans (hhazardLower who))
          hhazardUpper) who < 1)
    (habsorption : 0 < quittingRootAbsorptionMass
      (rootOfHazard hazard
        (fun who => hepsilon0.le.trans (hhazardLower who))
        hhazardUpper))
    (hexploit : HasTerminalExploitabilityGap reward gap) :
    ∃ who, hazard who = epsilon ∧
      quittingFaceNumerator (weightOfReward reward) hazard who < 0 := by
  let hhazard0 : ∀ who, 0 ≤ hazard who := fun who =>
    hepsilon0.le.trans (hhazardLower who)
  obtain ⟨who, hselected, hgain⟩ :=
    exists_lowerFace_fullRateGain_of_terminalGap reward hepsilon0
      hepsilon1.le hgap hazard hhazardLower hhazardUpper hbest hcontracts
        habsorption hexploit
  have hhazardLtOne : hazard who < 1 := by
    rw [hselected]
    exact hepsilon1
  have hnumerator :=
    quittingFaceNumerator_nonpos_of_constrainedNash_of_lt_one
      hbest hepsilon1.le who hhazardLtOne
  refine ⟨who, hselected, ?_⟩
  exact quittingFaceNumerator_lt_zero_of_fullRateGain
    reward hgap hazard hhazard0 hhazardUpper who (hcontracts who)
      habsorption hnumerator hgain

/-! ## The correct closure conclusion when normalized jets are unbounded -/

/-- A convergent sequence in the image of a finite-dimensional linear map
has an actual preimage.  This is the quotient-safe replacement for assuming
that a chosen sequence of input jets is bounded. -/
theorem exists_preimage_of_tendsto_apply_of_finiteDimensional
    {Domain Codomain : Type} [NormedAddCommGroup Domain]
    [NormedSpace ℝ Domain] [FiniteDimensional ℝ Domain]
    [NormedAddCommGroup Codomain] [NormedSpace ℝ Codomain]
    [FiniteDimensional ℝ Codomain]
    (linear : Domain →ₗ[ℝ] Codomain) (jet : ℕ → Domain)
    (limit : Codomain)
    (hlimit : Tendsto (fun n => linear (jet n)) atTop (nhds limit)) :
    ∃ correction, linear correction = limit := by
  have hmemClosure : limit ∈ closure (LinearMap.range linear) := by
    exact mem_closure_of_tendsto hlimit
      (Eventually.of_forall fun n => ⟨jet n, rfl⟩)
  have hclosed : IsClosed (LinearMap.range linear : Set Codomain) :=
    (LinearMap.range linear).closed_of_finiteDimensional
  rw [hclosed.closure_eq] at hmemClosure
  exact hmemClosure

/-! ## Sharp source-level direction-motion regression -/

namespace ConstrainedFaceDirectionMotionRegression

/-- Three-player table whose only nonzero row is player `2`'s.  Its
singleton opponent rewards are `-1,1`, while the literal opponent-pair reward
is `-3`. -/
def reward : {S : Finset (Fin 3) // S.Nonempty} → Payoff (Fin 3) :=
  fun terminal who =>
    if who = 2 then
      if terminal.val = {0} then -1
      else if terminal.val = {1} then 1
      else if terminal.val = {0, 1} then -3
      else 0
    else 0

/-- The full-support limiting direction. -/
def baseDirection : Fin 3 → ℝ := ![1 / 3, 1 / 3, 1 / 3]

/-- A sum-one direction moving at exactly the radial scale.  Player `2` is
the lower-face coordinate. -/
def movingDirection (scale : ℝ) : Fin 3 → ℝ :=
  ![1 / 3, 1 / 3 + scale, 1 / 3 - scale]

/-- Literal hazards on the moving ray. -/
def hazard (scale : ℝ) : Fin 3 → ℝ :=
  fun owner => scale * movingDirection scale owner

/-- The common constrained lower cutoff, attained by player `2`. -/
def cutoff (scale : ℝ) : ℝ := scale * (1 / 3 - scale)

theorem baseDirection_sum : ∑ owner, baseDirection owner = 1 := by
  norm_num [baseDirection, Fin.sum_univ_succ]

theorem movingDirection_sum (scale : ℝ) :
    ∑ owner, movingDirection scale owner = 1 := by
  simp [movingDirection, Fin.sum_univ_succ]
  ring

theorem hazard_eq_cutoff_two (scale : ℝ) : hazard scale 2 = cutoff scale := by
  rfl

theorem sum_hazard_eq (scale : ℝ) : ∑ owner, hazard scale owner = scale := by
  unfold hazard
  rw [← Finset.mul_sum, movingDirection_sum]
  ring

theorem tendsto_movingDirection :
    Tendsto movingDirection (nhds 0) (nhds baseDirection) := by
  rw [tendsto_pi_nhds]
  intro owner
  fin_cases owner
  · simp [movingDirection, baseDirection]
  · have hcontinuous : ContinuousAt
        (fun scale : ℝ => (1 / 3 : ℝ) + scale) 0 := by fun_prop
    simpa [movingDirection, baseDirection] using hcontinuous.tendsto
  · have hcontinuous : ContinuousAt
        (fun scale : ℝ => (1 / 3 : ℝ) - scale) 0 := by fun_prop
    simpa [movingDirection, baseDirection] using hcontinuous.tendsto

theorem hazard_pos
    {scale : ℝ} (hscale : 0 < scale) (hsmall : scale < 1 / 3) (who : Fin 3) :
    0 < hazard scale who := by
  fin_cases who <;> simp [hazard, movingDirection] <;> nlinarith

private theorem sigmaValue_two_eq_zero (x : Fin 3 → ℝ) :
    sigmaValue (weightOfReward reward) x 2 = 0 := by
  unfold sigmaValue
  apply Finset.sum_eq_zero
  intro coalition hcoalition
  have htwo : 2 ∈ insert 2 coalition := Finset.mem_insert_self 2 coalition
  have hneZero : insert 2 coalition ≠ ({0} : Finset (Fin 3)) := by
    intro heq
    rw [heq] at htwo
    norm_num at htwo
  have hneOne : insert 2 coalition ≠ ({1} : Finset (Fin 3)) := by
    intro heq
    rw [heq] at htwo
    norm_num at htwo
  have hnePair : insert 2 coalition ≠ ({0, 1} : Finset (Fin 3)) := by
    intro heq
    rw [heq] at htwo
    norm_num at htwo
  simp [weightOfReward, reward, hneZero, hneOne, hnePair]

private theorem excludedValue_two_eq
    (x : Fin 3 → ℝ) :
    excludedValue (weightOfReward reward) x 2 =
      -(x 0 * (1 - x 1)) + x 1 * (1 - x 0) - 3 * (x 0 * x 1) := by
  have hplayers : (Finset.univ : Finset (Fin 3)) = {0, 1, 2} := by decide
  have herase : ({0, 1, 2} : Finset (Fin 3)).erase 2 = {0, 1} := by decide
  have hpowerset :
      (({0, 1} : Finset (Fin 3)).powerset : Finset (Finset (Fin 3))) =
        {∅, {0}, {1}, {0, 1}} := by decide
  have heraseEmpty :
      ({∅, {0}, {1}, {0, 1}} : Finset (Finset (Fin 3))).erase ∅ =
        {{0}, {1}, {0, 1}} := by decide
  have hdiffZero : ({0, 1} : Finset (Fin 3)) \ {0} = {1} := by decide
  have hdiffOne : ({0, 1} : Finset (Fin 3)) \ {1} = {0} := by decide
  have hpairNeZero : ({0, 1} : Finset (Fin 3)) ≠ {0} := by decide
  unfold excludedValue
  rw [hplayers, herase, hpowerset, heraseEmpty]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  norm_num [reward, weightOfReward, hdiffZero, hdiffOne, hpairNeZero]
  ring

/-- On the fixed radial direction, the opponent-pair payoff gives a strictly
positive quadratic face coefficient. -/
theorem faceNumerator_baseDirection (scale : ℝ) :
    quittingFaceNumerator (weightOfReward reward)
      (fun owner => scale * baseDirection owner) 2 = scale ^ 2 / 3 := by
  rw [quittingFaceNumerator, sigmaValue_two_eq_zero,
    excludedValue_two_eq]
  norm_num [baseDirection]
  ring

/-- Moving the normalized direction at order `scale` reverses that sign,
although the table and its positive radial pair coefficient are unchanged. -/
theorem faceNumerator_hazard (scale : ℝ) :
    quittingFaceNumerator (weightOfReward reward) (hazard scale) 2 =
      scale ^ 2 * (scale - 2 / 3) := by
  rw [quittingFaceNumerator, sigmaValue_two_eq_zero,
    excludedValue_two_eq]
  norm_num [hazard, movingDirection]
  ring

theorem faceNumerator_hazard_zero (scale : ℝ) (who : Fin 3)
    (hwho : who ≠ 2) :
    quittingFaceNumerator (weightOfReward reward) (hazard scale) who = 0 := by
  unfold quittingFaceNumerator sigmaValue excludedValue
  simp [reward, weightOfReward, hwho]

/-- The moving hazards stay in the constrained cube and player `2` is its
lower coordinate. -/
theorem hazard_mem_constrainedCube
    {scale : ℝ} (hscale : 0 < scale) (hsmall : scale < 1 / 3) :
    (∀ who, cutoff scale ≤ hazard scale who) ∧
      ∀ who, hazard scale who ≤ 1 := by
  constructor
  · intro who
    fin_cases who <;>
      simp [cutoff, hazard, movingDirection] <;> nlinarith
  · intro who
    fin_cases who <;>
      simp [hazard, movingDirection] <;> nlinarith [sq_nonneg scale]

/-- **Sharp constrained-source regression.**  At every scale in `(0,1/3)`,
the moving row is a literal constrained stationary face-Nash source.  Its
normalized directions have full support and converge to `baseDirection`, but
player `2`'s exact face numerator is negative even though the degree-two
coefficient on the limiting radial direction is positive.

Thus exact constrained complementarity and quantitative hazard comparability
do not assign a sign to the pair layer.  A valid second-order consequence has
to retain the direction-motion correction (or pass to its singleton-linear
range as above). -/
theorem constrainedFaceNash_with_positiveRadialPairCoefficient
    {scale : ℝ} (hscale : 0 < scale) (hsmall : scale < 1 / 3) :
    (∀ who, 0 < hazard scale who) ∧
    (∑ who, hazard scale who) = scale ∧
    (∀ who, cutoff scale ≤ hazard scale who) ∧
    (∀ who, hazard scale who ≤ 1) ∧
    (∀ who rate, cutoff scale ≤ rate → rate ≤ 1 →
      rate * quittingFaceNumerator (weightOfReward reward) (hazard scale) who ≤
        hazard scale who *
          quittingFaceNumerator (weightOfReward reward) (hazard scale) who) ∧
    0 < (quittingRadialFacePolynomial (weightOfReward reward)
      baseDirection 2).coeff 2 ∧
    quittingFaceNumerator (weightOfReward reward) (hazard scale) 2 < 0 := by
  obtain ⟨hlower, hupper⟩ := hazard_mem_constrainedCube hscale hsmall
  refine ⟨hazard_pos hscale hsmall, sum_hazard_eq scale, hlower, hupper,
    ?_, ?_, ?_⟩
  · intro who rate hrateLower hrateUpper
    by_cases hwho : who = 2
    · subst who
      rw [faceNumerator_hazard, hazard_eq_cutoff_two]
      have hfaceNonpos : scale ^ 2 * (scale - 2 / 3) ≤ 0 := by
        exact mul_nonpos_of_nonneg_of_nonpos (sq_nonneg scale) (by linarith)
      exact mul_le_mul_of_nonpos_right hrateLower hfaceNonpos
    · rw [faceNumerator_hazard_zero scale who hwho]
      simp
  ·
    have hpoly : quittingRadialFacePolynomial (weightOfReward reward)
        baseDirection 2 = X ^ 2 * C (1 / 3 : ℝ) := by
      have heval : ∀ x : ℝ,
          (quittingRadialFacePolynomial (weightOfReward reward)
              baseDirection 2).eval x = (X ^ 2 * C (1 / 3 : ℝ)).eval x := by
        intro x
        rw [eval_quittingRadialFacePolynomial, faceNumerator_baseDirection]
        simp
        ring
      exact Polynomial.funext heval
    rw [hpoly]
    norm_num
  · rw [faceNumerator_hazard]
    have hsq : 0 < scale ^ 2 := sq_pos_of_pos hscale
    nlinarith

end ConstrainedFaceDirectionMotionRegression

end GameTheory
