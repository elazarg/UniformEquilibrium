/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.AbsorptionPath.CollisionConcentration
import UniformEquilibrium.Quitting.Cycles.ConditionedDiffuseProductRescaling
import UniformEquilibrium.Quitting.Paths.SupportWitnessPathCompiler

/-!
# Stochastic-button atom/diffuse compression

At one quitting row, regard the probability that at least one button works as
the row's scalar **effectiveness**.  A row above a threshold is retained as an
atomic packet.  A row below the threshold belongs to the diffuse part.

This experiment proves a finite-window compression ledger with three exact or
quantitative conclusions.

* Survival-weighted effectiveness telescopes exactly to absorbed mass.
* The number of effectiveness atoms is paid by cumulative unweighted
  effectiveness.
* The entire survival-weighted collision mass of the diffuse rows is at most
  `choose (card ι) 2 * threshold`, independently of the number of rows.

Consequently, on a window whose cumulative effectiveness lies in
`[level, level + 1]`, at most `(level + 1) / threshold` large rows remain,
diffuse collisions cost `O(threshold)`, and the surviving tail is at most
`exp (-level)`.

The result is an exact theorem about arbitrary quitting-root sequences.  It
does not yet compress the continuation-value motion or prove that deleting
the diffuse collision atoms preserves Nash--Bellman and punishment-floor
certificates.
-/


noncomputable section

namespace Experiments.QuittingStochasticButtonCompression

open GameTheory Filter Math.Probability
open scoped BigOperators

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Probability that at least one stochastic quitting button works at a row. -/
def buttonEffectiveness (roots : ℕ → ι → PMF Bool) (time : ℕ) : ℝ :=
  quittingRootAbsorptionMass (roots time)

/-- Sum of the individual button-success probabilities at one product row. -/
def totalButtonProbability (root : ι → PMF Bool) : ℝ :=
  ∑ who, (root who true).toReal

/-- Individual button probability normalized by the probability that at least
one button works.  Positive-effectiveness rows are resolved into a scalar
effectiveness and this bounded direction. -/
def buttonDirection (root : ι → PMF Bool) (who : ι) : ℝ :=
  (root who true).toReal / quittingRootAbsorptionMass root

/-- Unweighted effectiveness accumulated over a finite chronological window. -/
def cumulativeEffectiveness
    (roots : ℕ → ι → PMF Bool) (horizon : ℕ) : ℝ :=
  ∑ time ∈ Finset.range horizon, buttonEffectiveness roots time

omit [DecidableEq ι] in
@[simp] theorem cumulativeEffectiveness_zero
    (roots : ℕ → ι → PMF Bool) :
    cumulativeEffectiveness roots 0 = 0 := by
  simp [cumulativeEffectiveness]

omit [DecidableEq ι] in
theorem cumulativeEffectiveness_succ
    (roots : ℕ → ι → PMF Bool) (horizon : ℕ) :
    cumulativeEffectiveness roots (horizon + 1) =
      cumulativeEffectiveness roots horizon +
        buttonEffectiveness roots horizon := by
  simp [cumulativeEffectiveness, Finset.sum_range_succ]

/-- Rows whose effectiveness is strictly above the diffuse threshold. -/
def atomicButtonTimes
    (roots : ℕ → ι → PMF Bool) (horizon : ℕ) (threshold : ℝ) : Finset ℕ :=
  (Finset.range horizon).filter fun time =>
    threshold < buttonEffectiveness roots time

/-- Survival-weighted absorbed mass over a finite window. -/
def weightedEffectiveness
    (roots : ℕ → ι → PMF Bool) (horizon : ℕ) : ℝ :=
  ∑ time ∈ Finset.range horizon,
    quittingSurvivalPrefix roots time * buttonEffectiveness roots time

/-- Survival-weighted simultaneous-quitting mass on the diffuse rows. -/
def diffuseCollisionMass
    (roots : ℕ → ι → PMF Bool) (horizon : ℕ) (threshold : ℝ) : ℝ :=
  ∑ time ∈ (Finset.range horizon).filter
      (fun time => buttonEffectiveness roots time ≤ threshold),
    quittingSurvivalPrefix roots time *
      quittingRootCollisionMass (roots time)

omit [DecidableEq ι] in
theorem buttonEffectiveness_nonneg
    (roots : ℕ → ι → PMF Bool) (time : ℕ) :
    0 ≤ buttonEffectiveness roots time := by
  exact quittingRootAbsorptionMass_nonneg (roots time)

omit [DecidableEq ι] in
theorem buttonEffectiveness_le_one
    (roots : ℕ → ι → PMF Bool) (time : ℕ) :
    buttonEffectiveness roots time ≤ 1 := by
  unfold buttonEffectiveness quittingRootAbsorptionMass
  exact sub_le_self 1 (quittingStationaryContinueMass_nonneg (roots time))

omit [DecidableEq ι] in
/-- Scale and button direction reconstruct each individual marginal exactly. -/
theorem effectiveness_mul_buttonDirection
    (root : ι → PMF Bool) (who : ι)
    (hpositive : 0 < quittingRootAbsorptionMass root) :
    quittingRootAbsorptionMass root * buttonDirection root who =
      (root who true).toReal := by
  unfold buttonDirection
  exact mul_div_cancel₀ _ hpositive.ne'

omit [DecidableEq ι] in
theorem buttonDirection_nonneg
    (root : ι → PMF Bool) (who : ι)
    (hpositive : 0 < quittingRootAbsorptionMass root) :
    0 ≤ buttonDirection root who := by
  exact div_nonneg ENNReal.toReal_nonneg hpositive.le

omit [DecidableEq ι] in
theorem buttonDirection_le_one
    (root : ι → PMF Bool) (who : ι)
    (hpositive : 0 < quittingRootAbsorptionMass root) :
    buttonDirection root who ≤ 1 := by
  exact (div_le_one hpositive).2
    (quittingRoot_quitProbability_le_absorptionMass root who)

omit [DecidableEq ι] in
/-- Joint effectiveness is no larger than the sum of individual button
probabilities. -/
theorem absorptionMass_le_totalButtonProbability
    (root : ι → PMF Bool) :
    quittingRootAbsorptionMass root ≤ totalButtonProbability root := by
  have hunion := Math.one_sub_prod_one_sub_le_sum
    (quittingRootQuitRates root) Finset.univ
    (fun who _ => ENNReal.toReal_nonneg)
    (fun who _ => by
      unfold quittingRootQuitRates
      exact ENNReal.toReal_mono ENNReal.one_ne_top
        (PMF.coe_le_one (root who) true))
  have hcontinue := continueMass_quittingRootQuitRates root
  unfold Math.PMFProduct.continueMass at hcontinue
  rw [hcontinue] at hunion
  simpa [quittingRootAbsorptionMass, totalButtonProbability,
    quittingRootQuitRates] using hunion

omit [DecidableEq ι] in
/-- The resolved direction is not generally a simplex point: collisions make
its coordinate sum exceed one.  Nevertheless the sum always lies in
`[1, card ι]`. -/
theorem sum_buttonDirection_mem_interval
    (root : ι → PMF Bool)
    (hpositive : 0 < quittingRootAbsorptionMass root) :
    1 ≤ ∑ who, buttonDirection root who ∧
      (∑ who, buttonDirection root who) ≤ Fintype.card ι := by
  have hsum : (∑ who, buttonDirection root who) =
      totalButtonProbability root / quittingRootAbsorptionMass root := by
    unfold buttonDirection totalButtonProbability
    exact (Finset.sum_div _ _ _).symm
  have hlower := div_le_div_of_nonneg_right
    (absorptionMass_le_totalButtonProbability root) hpositive.le
  have htotalUpper : totalButtonProbability root ≤
      Fintype.card ι * quittingRootAbsorptionMass root := by
    unfold totalButtonProbability
    calc
      (∑ who, (root who true).toReal) ≤
          ∑ _who : ι, quittingRootAbsorptionMass root := by
        exact Finset.sum_le_sum fun who _ =>
          quittingRoot_quitProbability_le_absorptionMass root who
      _ = Fintype.card ι * quittingRootAbsorptionMass root := by simp
  have hupper := div_le_div_of_nonneg_right htotalUpper hpositive.le
  constructor
  · rw [hsum]
    simpa [div_self hpositive.ne'] using hlower
  · rw [hsum]
    simpa [mul_div_cancel_right₀ _ hpositive.ne'] using hupper

omit [DecidableEq ι] in
/-- The live mass spent at each row on absorption telescopes exactly. -/
theorem weightedEffectiveness_eq_one_sub_survival
    (roots : ℕ → ι → PMF Bool) (horizon : ℕ) :
    weightedEffectiveness roots horizon =
      1 - quittingSurvivalPrefix roots horizon := by
  induction horizon with
  | zero =>
      simp [weightedEffectiveness]
  | succ horizon ih =>
      rw [weightedEffectiveness, Finset.sum_range_succ]
      rw [show (∑ time ∈ Finset.range horizon,
          quittingSurvivalPrefix roots time * buttonEffectiveness roots time) =
          weightedEffectiveness roots horizon by rfl, ih]
      rw [quittingSurvivalPrefix_succ]
      unfold buttonEffectiveness quittingRootAbsorptionMass
      ring

omit [DecidableEq ι] in
/-- A finite cumulative-effectiveness budget permits only finitely many rows
above a fixed positive scale. -/
theorem atomicButtonTimes_card_mul_threshold_le_cumulativeEffectiveness
    (roots : ℕ → ι → PMF Bool) (horizon : ℕ) {threshold : ℝ}
    (_hthreshold : 0 ≤ threshold) :
    (atomicButtonTimes roots horizon threshold).card * threshold ≤
      cumulativeEffectiveness roots horizon := by
  calc
    (atomicButtonTimes roots horizon threshold).card * threshold =
        ∑ _time ∈ atomicButtonTimes roots horizon threshold, threshold := by
          simp
    _ ≤ ∑ time ∈ atomicButtonTimes roots horizon threshold,
        buttonEffectiveness roots time := by
          apply Finset.sum_le_sum
          intro time htime
          exact (Finset.mem_filter.mp htime).2.le
    _ ≤ ∑ time ∈ Finset.range horizon,
        buttonEffectiveness roots time := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · exact Finset.filter_subset _ _
          · intro time _ _
            exact buttonEffectiveness_nonneg roots time
    _ = cumulativeEffectiveness roots horizon := rfl

omit [DecidableEq ι] in
/-- Explicit cardinal form of the atomic-packet bound. -/
theorem atomicButtonTimes_card_le_budget_div_threshold
    (roots : ℕ → ι → PMF Bool) (horizon : ℕ)
    {threshold budget : ℝ} (hthreshold : 0 < threshold)
    (hbudget : cumulativeEffectiveness roots horizon ≤ budget) :
    (atomicButtonTimes roots horizon threshold).card ≤ budget / threshold := by
  apply (le_div_iff₀ hthreshold).2
  exact (atomicButtonTimes_card_mul_threshold_le_cumulativeEffectiveness
    roots horizon hthreshold.le).trans hbudget

/-- **Diffuse collision bound.**  After retaining every row above
`threshold` as an atom, the total survival-weighted collision probability of
all remaining rows is at most

`choose (card ι) 2 * threshold * absorbedMass`.

In particular it is at most `choose (card ι) 2 * threshold`, uniformly in the
window length. -/
theorem diffuseCollisionMass_le_threshold_mul_absorbedMass
    (roots : ℕ → ι → PMF Bool) (horizon : ℕ) {threshold : ℝ}
    (hthreshold : 0 ≤ threshold) :
    diffuseCollisionMass roots horizon threshold ≤
      (Fintype.card ι).choose 2 * threshold *
        (1 - quittingSurvivalPrefix roots horizon) := by
  let coefficient : ℝ := (Fintype.card ι).choose 2
  let diffuseTimes := (Finset.range horizon).filter
    (fun time => buttonEffectiveness roots time ≤ threshold)
  have hcoefficient : 0 ≤ coefficient := by
    dsimp only [coefficient]
    positivity
  have hrow : ∀ time ∈ diffuseTimes,
      quittingSurvivalPrefix roots time *
          quittingRootCollisionMass (roots time) ≤
        coefficient * threshold *
          (quittingSurvivalPrefix roots time *
            buttonEffectiveness roots time) := by
    intro time htime
    have heffect0 := buttonEffectiveness_nonneg roots time
    have heffectLe : buttonEffectiveness roots time ≤ threshold :=
      (Finset.mem_filter.mp htime).2
    have hcollision :=
      quittingRootCollisionMass_le_choose_card_mul_absorption_sq
        (roots time)
    have hsquare : buttonEffectiveness roots time ^ 2 ≤
        threshold * buttonEffectiveness roots time := by
      nlinarith
    have hcollision' : quittingRootCollisionMass (roots time) ≤
        coefficient * (threshold * buttonEffectiveness roots time) := by
      calc
        quittingRootCollisionMass (roots time) ≤
            coefficient * buttonEffectiveness roots time ^ 2 := by
              simpa [coefficient, buttonEffectiveness] using hcollision
        _ ≤ coefficient *
            (threshold * buttonEffectiveness roots time) :=
              mul_le_mul_of_nonneg_left hsquare hcoefficient
    have hsurvival := quittingSurvivalPrefix_nonneg roots time
    calc
      quittingSurvivalPrefix roots time *
          quittingRootCollisionMass (roots time) ≤
        quittingSurvivalPrefix roots time *
          (coefficient *
            (threshold * buttonEffectiveness roots time)) :=
          mul_le_mul_of_nonneg_left hcollision' hsurvival
      _ = coefficient * threshold *
          (quittingSurvivalPrefix roots time *
            buttonEffectiveness roots time) := by ring
  calc
    diffuseCollisionMass roots horizon threshold =
        ∑ time ∈ diffuseTimes,
          quittingSurvivalPrefix roots time *
            quittingRootCollisionMass (roots time) := by rfl
    _ ≤ ∑ time ∈ diffuseTimes,
        coefficient * threshold *
          (quittingSurvivalPrefix roots time *
            buttonEffectiveness roots time) :=
      Finset.sum_le_sum hrow
    _ ≤ ∑ time ∈ Finset.range horizon,
        coefficient * threshold *
          (quittingSurvivalPrefix roots time *
            buttonEffectiveness roots time) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.filter_subset _ _
      · intro time _ _
        exact mul_nonneg
          (mul_nonneg hcoefficient hthreshold)
          (mul_nonneg (quittingSurvivalPrefix_nonneg roots time)
            (buttonEffectiveness_nonneg roots time))
    _ = coefficient * threshold * weightedEffectiveness roots horizon := by
      unfold weightedEffectiveness
      rw [Finset.mul_sum]
    _ = coefficient * threshold *
        (1 - quittingSurvivalPrefix roots horizon) := by
      rw [weightedEffectiveness_eq_one_sub_survival]
    _ = (Fintype.card ι).choose 2 * threshold *
        (1 - quittingSurvivalPrefix roots horizon) := by rfl

theorem diffuseCollisionMass_le_threshold
    (roots : ℕ → ι → PMF Bool) (horizon : ℕ) {threshold : ℝ}
    (hthreshold : 0 ≤ threshold) :
    diffuseCollisionMass roots horizon threshold ≤
      (Fintype.card ι).choose 2 * threshold := by
  have hmain := diffuseCollisionMass_le_threshold_mul_absorbedMass
    roots horizon hthreshold
  have hfactor : 1 - quittingSurvivalPrefix roots horizon ≤ 1 := by
    linarith [quittingSurvivalPrefix_nonneg roots horizon]
  have hcoefficient : 0 ≤
      ((Fintype.card ι).choose 2 : ℝ) * threshold :=
    mul_nonneg (by positivity) hthreshold
  exact hmain.trans <| by
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left hfactor hcoefficient

omit [DecidableEq ι] in
/-- Cumulative button effectiveness controls the exact surviving tail. -/
theorem survival_le_exp_neg_cumulativeEffectiveness
    (roots : ℕ → ι → PMF Bool) (horizon : ℕ) :
    quittingSurvivalPrefix roots horizon ≤
      Real.exp (-cumulativeEffectiveness roots horizon) := by
  simpa [cumulativeEffectiveness, buttonEffectiveness,
    quittingTotalAbsorptionCharge] using
      quittingSurvivalPrefix_le_exp_neg_sum_totalAbsorptionCharge roots horizon

omit [DecidableEq ι] in
/-- A divergent effectiveness clock has a finite first-crossing window whose
total charge lies between `level` and `level + 1`.  The overshoot is at most
one because one quitting row has effectiveness at most one. -/
theorem exists_cumulativeEffectiveness_mem_unitWindow
    (roots : ℕ → ι → PMF Bool) {level : ℝ} (hlevel : 0 < level)
    (hdiverges : Tendsto (cumulativeEffectiveness roots) atTop atTop) :
    ∃ horizon,
      level ≤ cumulativeEffectiveness roots horizon ∧
        cumulativeEffectiveness roots horizon ≤ level + 1 := by
  classical
  have heventually : ∀ᶠ horizon : ℕ in atTop,
      level ≤ cumulativeEffectiveness roots horizon :=
    (tendsto_atTop.1 hdiverges) level
  obtain ⟨start, hstart⟩ := eventually_atTop.1 heventually
  have hexists : ∃ horizon,
      level ≤ cumulativeEffectiveness roots horizon :=
    ⟨start, hstart start le_rfl⟩
  let horizon := Nat.find hexists
  have hlower : level ≤ cumulativeEffectiveness roots horizon :=
    Nat.find_spec hexists
  refine ⟨horizon, hlower, ?_⟩
  have hpositive : 0 < horizon := by
    by_contra hnot
    have hzero : horizon = 0 := Nat.eq_zero_of_not_pos hnot
    rw [hzero, cumulativeEffectiveness_zero] at hlower
    linarith
  obtain ⟨previous, hhorizon⟩ :=
    Nat.exists_eq_succ_of_ne_zero hpositive.ne'
  have hpreviousLt : previous < horizon := by omega
  have hnotLower : ¬level ≤ cumulativeEffectiveness roots previous :=
    Nat.find_min hexists (by simpa only [horizon] using hpreviousLt)
  rw [hhorizon, cumulativeEffectiveness_succ]
  have hrow := buttonEffectiveness_le_one roots previous
  linarith

/-- **Finite atom/diffuse/tail certificate.**  If a selected window carries
cumulative effectiveness between `level` and `level + 1`, then:

1. its large-effectiveness rows have total count paid by `level + 1`;
2. all diffuse collision mass costs only `O(threshold)`; and
3. its surviving tail is at most `exp (-level)`.

This is the finite-compression interface suggested by stochastic buttons. -/
theorem stochasticButton_atom_diffuse_tail_certificate
    (roots : ℕ → ι → PMF Bool) (horizon : ℕ)
    {threshold level : ℝ} (hthreshold : 0 ≤ threshold)
    (hlower : level ≤ cumulativeEffectiveness roots horizon)
    (hupper : cumulativeEffectiveness roots horizon ≤ level + 1) :
    (atomicButtonTimes roots horizon threshold).card * threshold ≤ level + 1 ∧
      diffuseCollisionMass roots horizon threshold ≤
        (Fintype.card ι).choose 2 * threshold ∧
      quittingSurvivalPrefix roots horizon ≤ Real.exp (-level) := by
  refine ⟨
    (atomicButtonTimes_card_mul_threshold_le_cumulativeEffectiveness
      roots horizon hthreshold).trans hupper,
    diffuseCollisionMass_le_threshold roots horizon hthreshold,
    ?_⟩
  have hsurvival := survival_le_exp_neg_cumulativeEffectiveness roots horizon
  have hexp : Real.exp (-cumulativeEffectiveness roots horizon) ≤
      Real.exp (-level) := by
    exact Real.exp_le_exp.mpr (by linarith)
  exact hsurvival.trans hexp

/-- Divergent stochastic-button effectiveness therefore produces a finite
window with a quantitative atom bound, a horizon-independent diffuse
collision bound, and an exponentially small tail. -/
theorem exists_stochasticButton_atom_diffuse_tail_certificate
    (roots : ℕ → ι → PMF Bool) {threshold level : ℝ}
    (hthreshold : 0 ≤ threshold) (hlevel : 0 < level)
    (hdiverges : Tendsto (cumulativeEffectiveness roots) atTop atTop) :
    ∃ horizon,
      (atomicButtonTimes roots horizon threshold).card * threshold ≤ level + 1 ∧
        diffuseCollisionMass roots horizon threshold ≤
          (Fintype.card ι).choose 2 * threshold ∧
        quittingSurvivalPrefix roots horizon ≤ Real.exp (-level) := by
  obtain ⟨horizon, hlower, hupper⟩ :=
    exists_cumulativeEffectiveness_mem_unitWindow roots hlevel hdiverges
  exact ⟨horizon,
    stochasticButton_atom_diffuse_tail_certificate roots horizon
      hthreshold hlower hupper⟩

/-- Nonsummable effectiveness is the intrinsic quitting-path hypothesis that
supplies the divergent clock required by the finite certificate. -/
theorem exists_stochasticButton_atom_diffuse_tail_certificate_of_not_summable
    (roots : ℕ → ι → PMF Bool) {threshold level : ℝ}
    (hthreshold : 0 ≤ threshold) (hlevel : 0 < level)
    (hnotSummable : ¬Summable (buttonEffectiveness roots)) :
    ∃ horizon,
      (atomicButtonTimes roots horizon threshold).card * threshold ≤ level + 1 ∧
        diffuseCollisionMass roots horizon threshold ≤
          (Fintype.card ι).choose 2 * threshold ∧
        quittingSurvivalPrefix roots horizon ≤ Real.exp (-level) := by
  have hdiverges : Tendsto (cumulativeEffectiveness roots) atTop atTop := by
    have hsum := (not_summable_iff_tendsto_nat_atTop_of_nonneg
      (buttonEffectiveness_nonneg roots)).1 hnotSummable
    change Tendsto (fun horizon : ℕ =>
      ∑ time ∈ Finset.range horizon, buttonEffectiveness roots time)
        atTop atTop
    exact hsum
  exact exists_stochasticButton_atom_diffuse_tail_certificate
    roots hthreshold hlevel hdiverges


end Experiments.QuittingStochasticButtonCompression
