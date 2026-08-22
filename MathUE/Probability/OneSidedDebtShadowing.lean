/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.Probability.DiscountedBackwardRecursion

/-!
# Generated-secant two-discount debt shadowing

This file isolates the game-independent accounting behind chronological debt
shadowing.  The prescribed error and the best-response error are unrolled
separately, with discounts `beta` and `lambda`.  Their exact difference is
controlled by adverse direct forcing plus two Abel-weighted copies of the
same prescribed forcing.  No comparison between the two discounts is needed.

The older direct debt-error estimate with a positive secant-over-discount
budget remains below as an optional refinement.  It is not a hypothesis of
the base compiler.
-/

noncomputable section

open Filter
open scoped BigOperators Topology

namespace Math

/-- A max of a constant and an affine branch has an exact secant whose slope
lies between zero and the affine slope.  Branch switching is allowed. -/
theorem exists_max_const_add_mul_secant
    (stop immediate slope first second : ℝ)
    (hslope0 : 0 ≤ slope) :
    ∃ secant : ℝ, 0 ≤ secant ∧ secant ≤ slope ∧
      max stop (immediate + slope * second) -
          max stop (immediate + slope * first) =
        secant * (second - first) := by
  let value : ℝ → ℝ := fun continuation ↦
    max stop (immediate + slope * continuation)
  have hmonotone : Monotone value := by
    intro x y hxy
    dsimp only [value]
    exact max_le_max le_rfl (by nlinarith)
  have hlipschitz : ∀ x y,
      |value y - value x| ≤ slope * |y - x| := by
    intro x y
    dsimp only [value]
    calc
      _ ≤ |(immediate + slope * y) - (immediate + slope * x)| := by
        rw [max_comm stop, max_comm stop]
        exact abs_max_sub_max_le_abs _ _ _
      _ = slope * |y - x| := by
        rw [show immediate + slope * y - (immediate + slope * x) =
          slope * (y - x) by ring_nf, abs_mul, abs_of_nonneg hslope0]
  have hforward : ∀ x y, x ≤ y →
      ∃ secant : ℝ, 0 ≤ secant ∧ secant ≤ slope ∧
        value y - value x = secant * (y - x) := by
    intro x y hxy
    by_cases heq : x = y
    · subst y
      exact ⟨0, le_rfl, hslope0, by ring⟩
    · have hxy' : 0 < y - x := sub_pos.mpr (lt_of_le_of_ne hxy heq)
      let secant := (value y - value x) / (y - x)
      have hdiff0 : 0 ≤ value y - value x :=
        sub_nonneg.mpr (hmonotone hxy)
      have hdiffUpper : value y - value x ≤ slope * (y - x) := by
        have h := hlipschitz x y
        rw [abs_of_nonneg hdiff0, abs_of_pos hxy'] at h
        exact h
      refine ⟨secant, div_nonneg hdiff0 hxy'.le, ?_, ?_⟩
      · exact (div_le_iff₀ hxy').2 (by nlinarith)
      · dsimp only [secant]
        field_simp
  rcases le_total first second with hforwardOrder | hbackwardOrder
  · simpa [value] using hforward first second hforwardOrder
  · obtain ⟨secant, hsecant0, hsecantSlope, hsecant⟩ :=
      hforward second first hbackwardOrder
    refine ⟨secant, hsecant0, hsecantSlope, ?_⟩
    dsimp only [value] at hsecant ⊢
    linarith

/-- Finite unfolding of a scalar backward affine recursion. -/
theorem backwardRecursion_eq_weighted_sum_add_terminal
    (error forcing discount : ℕ → ℝ) (start length : ℕ)
    (hrec : ∀ time, error time =
      forcing time + discount time * error (time + 1)) :
    error start =
      (∑ offset ∈ Finset.range length,
        survivalProduct discount start offset * forcing (start + offset)) +
      survivalProduct discount start length * error (start + length) := by
  induction length generalizing start with
  | zero => simp [survivalProduct]
  | succ length ih =>
      rw [hrec start, ih (start + 1), Finset.sum_range_succ',
        survivalProduct_succ_left]
      have hshift :
          (∑ offset ∈ Finset.range length,
              survivalProduct discount start (offset + 1) *
                forcing (start + (offset + 1))) =
            discount start *
              ∑ offset ∈ Finset.range length,
                survivalProduct discount (start + 1) offset *
                  forcing (start + 1 + offset) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro offset _
        rw [survivalProduct_succ_left]
        simp only [Nat.add_left_comm, Nat.add_comm]
        ring_nf
      rw [hshift]
      simp [survivalProduct]
      ring_nf

/-- A bounded tail multiplied by a survival product tending to zero also
tends to zero. -/
theorem tendsto_survivalProduct_mul_bounded_zero
    (discount value : ℕ → ℝ) (start : ℕ)
    (hsurvival : Tendsto (survivalProduct discount start) atTop (nhds 0))
    (hbound : ∃ bound : ℝ, ∀ time, |value time| ≤ bound) :
    Tendsto
      (fun length ↦ survivalProduct discount start length *
        value (start + length)) atTop (nhds 0) := by
  obtain ⟨bound, hbound⟩ := hbound
  have hbdd : IsBoundedUnder (· ≤ ·) atTop
      ((norm : ℝ → ℝ) ∘ fun length : ℕ ↦ value (start + length)) := by
    change ∃ bound : ℝ, ∀ᶠ length : ℕ in atTop,
      |value (start + length)| ≤ bound
    refine ⟨bound, Eventually.of_forall fun length ↦ ?_⟩
    exact hbound (start + length)
  exact hsurvival.zero_mul_isBoundedUnder_le hbdd

/-- A nonnegative coefficient sequence dominated pointwise by a survival
clock inherits vanishing survival on every fixed tail. -/
theorem tendsto_survivalProduct_zero_of_le
    (coefficient discount : ℕ → ℝ) (start : ℕ)
    (hcoefficient0 : ∀ time, 0 ≤ coefficient time)
    (hle : ∀ time, coefficient time ≤ discount time)
    (hsurvival : Tendsto (survivalProduct discount start) atTop (nhds 0)) :
    Tendsto (survivalProduct coefficient start) atTop (nhds 0) := by
  apply squeeze_zero'
  · exact Eventually.of_forall fun length ↦
      survivalProduct_nonneg coefficient hcoefficient0 start length
  · exact Eventually.of_forall fun length ↦ by
      unfold survivalProduct
      exact Finset.prod_le_prod
        (fun offset _ ↦ hcoefficient0 (start + offset))
        (fun offset _ ↦ hle (start + offset))
  · exact hsurvival

/-- All finite suffix discrepancies bounded by `eta` shadow a bounded
backward recursion whose survival product vanishes. -/
theorem abs_prescribedError_le_of_suffixDiscrepancy
    (prescribedError prescribedDefect discount : ℕ → ℝ) (eta : ℝ)
    (hdiscount0 : ∀ time, 0 ≤ discount time)
    (hdiscount1 : ∀ time, discount time ≤ 1)
    (hrec : ∀ time, prescribedError time =
      discount time * prescribedError (time + 1) - prescribedDefect time)
    (hdiscrepancy : ∀ start length,
      |∑ offset ∈ Finset.range length,
        prescribedDefect (start + offset)| ≤ eta)
    (hsurvival : ∀ start,
      Tendsto (survivalProduct discount start) atTop (nhds 0))
    (hbound : ∃ bound : ℝ, ∀ time, |prescribedError time| ≤ bound)
    (start : ℕ) :
    |prescribedError start| ≤ eta := by
  have hprefix : ∀ length,
      prefixAbsMax (fun time ↦ -prescribedDefect time) start length ≤ eta := by
    intro length
    unfold prefixAbsMax
    apply Finset.sup'_le
    intro count hcount
    have hcount' : count ≤ length := by
      exact Nat.le_of_lt_succ (Finset.mem_range.mp hcount)
    simpa only [Finset.sum_neg_distrib, abs_neg] using
      hdiscrepancy start count
  have hfinite : ∀ length,
      |prescribedError start| ≤
        eta + survivalProduct discount start length *
          |prescribedError (start + length)| := by
    intro length
    refine (abs_discrepancy_le_prefix_max_add_terminal
      (fun time ↦ -prescribedDefect time) discount prescribedError
      start length ?_ hdiscount0 hdiscount1).trans ?_
    · intro offset _
      have h := hrec (start + offset)
      linarith
    · exact add_le_add (hprefix length) le_rfl
  have hterminal : Tendsto
      (fun length ↦ survivalProduct discount start length *
        |prescribedError (start + length)|) atTop (nhds 0) := by
    have h := tendsto_survivalProduct_mul_bounded_zero discount
      (fun time ↦ |prescribedError time|) start (hsurvival start)
      ⟨hbound.choose, fun time ↦ by
        simpa only [abs_abs] using hbound.choose_spec time⟩
    exact h
  have hlimit : Tendsto
      (fun length ↦ eta + survivalProduct discount start length *
        |prescribedError (start + length)|) atTop (nhds eta) := by
    simpa using (tendsto_const_nhds.add hterminal)
  exact ge_of_tendsto' hlimit hfinite

/-! ## Exact two-discount accounting -/

/-- Exact finite identity obtained by unrolling prescribed and best-response
errors separately.  It makes no comparison between `discount` and `secant`.
-/
theorem twoDiscountDebtError_eq
    (prescribedError bestResponseError prescribedDefect directDefect
      discount secant : ℕ → ℝ)
    (start length : ℕ)
    (hprescribedRec : ∀ time, prescribedError time =
      discount time * prescribedError (time + 1) - prescribedDefect time)
    (hbestResponseRec : ∀ time, bestResponseError time =
      secant time * bestResponseError (time + 1) -
        (prescribedDefect time + directDefect time)) :
    bestResponseError start - prescribedError start =
      -∑ offset ∈ Finset.range length,
          survivalProduct secant start offset *
            directDefect (start + offset) +
        ∑ offset ∈ Finset.range length,
          (survivalProduct discount start offset -
            survivalProduct secant start offset) *
            prescribedDefect (start + offset) +
        survivalProduct secant start length *
            bestResponseError (start + length) -
          survivalProduct discount start length *
            prescribedError (start + length) := by
  have hprescribed := backwardRecursion_eq_weighted_sum_add_terminal
    prescribedError (fun time ↦ -prescribedDefect time) discount start length
    (fun time ↦ by rw [hprescribedRec time]; ring)
  have hbest := backwardRecursion_eq_weighted_sum_add_terminal
    bestResponseError
      (fun time ↦ -(prescribedDefect time + directDefect time))
      secant start length
      (fun time ↦ by rw [hbestResponseRec time]; ring)
  rw [hprescribed, hbest]
  have hbestSum :
      (∑ offset ∈ Finset.range length,
        survivalProduct secant start offset *
          -(prescribedDefect (start + offset) +
            directDefect (start + offset))) =
        -(∑ offset ∈ Finset.range length,
          survivalProduct secant start offset *
            prescribedDefect (start + offset)) -
        ∑ offset ∈ Finset.range length,
          survivalProduct secant start offset *
            directDefect (start + offset) := by
    calc
      _ = ∑ offset ∈ Finset.range length,
          (-(survivalProduct secant start offset *
              prescribedDefect (start + offset)) +
            -(survivalProduct secant start offset *
              directDefect (start + offset))) := by
        apply Finset.sum_congr rfl
        intro offset _
        ring
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_neg_distrib,
          Finset.sum_neg_distrib]
        ring
  have hprescribedSum :
      (∑ offset ∈ Finset.range length,
        survivalProduct discount start offset *
          -prescribedDefect (start + offset)) =
        -(∑ offset ∈ Finset.range length,
          survivalProduct discount start offset *
            prescribedDefect (start + offset)) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro offset _
    ring
  have hdifferenceSum :
      (∑ offset ∈ Finset.range length,
        (survivalProduct discount start offset -
          survivalProduct secant start offset) *
          prescribedDefect (start + offset)) =
        (∑ offset ∈ Finset.range length,
          survivalProduct discount start offset *
            prescribedDefect (start + offset)) -
        ∑ offset ∈ Finset.range length,
          survivalProduct secant start offset *
            prescribedDefect (start + offset) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro offset _
    ring
  rw [hbestSum, hprescribedSum, hdifferenceSum]
  ring

/-- Survival weights are nonnegative, decreasing from one, so Abel summation
bounds their forcing sum by the largest unweighted prefix discrepancy. -/
theorem abs_survivalWeightedSum_le_prefixAbsMax
    (forcing discount : ℕ → ℝ) (start length : ℕ)
    (hdiscount0 : ∀ time, 0 ≤ discount time)
    (hdiscount1 : ∀ time, discount time ≤ 1) :
    |∑ offset ∈ Finset.range length,
        survivalProduct discount start offset * forcing (start + offset)| ≤
      prefixAbsMax forcing start length := by
  let weight : ℕ → ℝ := fun offset ↦ survivalProduct discount start offset
  let summand : ℕ → ℝ := fun offset ↦ forcing (start + offset)
  have hweight0 : ∀ offset, 0 ≤ weight offset := fun offset ↦
    survivalProduct_nonneg discount hdiscount0 start offset
  have hweightAntitone : ∀ offset, weight (offset + 1) ≤ weight offset := by
    intro offset
    dsimp only [weight]
    rw [survivalProduct_succ]
    exact (mul_le_mul_of_nonneg_left (hdiscount1 (start + offset))
      (survivalProduct_nonneg discount hdiscount0 start offset)).trans_eq
        (by simp)
  have hupper :
      ∑ offset ∈ Finset.range length, weight offset * summand offset ≤
        prefixAbsMax forcing start length := by
    simpa [weight, survivalProduct] using
      (MathUE.sum_mul_le_initialWeight_mul_of_partialSum_le
      (weight := weight) (summand := summand)
      (ε := prefixAbsMax forcing start length) length hweightAntitone
      (hweight0 length) (fun count hcount ↦ by
        simpa [summand] using
          prefixSum_le_prefixAbsMax forcing start length count hcount))
  have hlower :
      -prefixAbsMax forcing start length ≤
        ∑ offset ∈ Finset.range length, weight offset * summand offset := by
    have hnegative := MathUE.sum_mul_le_initialWeight_mul_of_partialSum_le
      (weight := weight) (summand := fun offset ↦ -summand offset)
      (ε := prefixAbsMax forcing start length) length hweightAntitone
      (hweight0 length) (fun count hcount ↦ by
        simpa [summand, Finset.sum_neg_distrib] using
          neg_prefixSum_le_prefixAbsMax forcing start length count hcount)
    have hrewrite :
        (∑ offset ∈ Finset.range length, weight offset * -summand offset) =
          -(∑ offset ∈ Finset.range length,
            weight offset * summand offset) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro offset _
      ring
    rw [hrewrite] at hnegative
    have hnegative' :
        -(∑ offset ∈ Finset.range length,
          weight offset * summand offset) ≤
            prefixAbsMax forcing start length := by
      simpa [weight, survivalProduct] using hnegative
    linarith
  rw [abs_le]
  simpa [weight, summand] using And.intro hlower hupper

/-- An all-prefix discrepancy bound controls every survival-weighted sum by
the same constant. -/
theorem abs_survivalWeightedSum_le_of_suffixDiscrepancy
    (forcing discount : ℕ → ℝ) (bound : ℝ)
    (hdiscount0 : ∀ time, 0 ≤ discount time)
    (hdiscount1 : ∀ time, discount time ≤ 1)
    (hdiscrepancy : ∀ start length,
      |∑ offset ∈ Finset.range length, forcing (start + offset)| ≤ bound)
    (start length : ℕ) :
    |∑ offset ∈ Finset.range length,
        survivalProduct discount start offset * forcing (start + offset)| ≤
      bound := by
  refine (abs_survivalWeightedSum_le_prefixAbsMax forcing discount start length
    hdiscount0 hdiscount1).trans ?_
  unfold prefixAbsMax
  apply Finset.sup'_le
  intro count hcount
  exact hdiscrepancy start count

/-- The difference of the two Abel-weighted prescribed forcings costs at
most twice the common all-prefix discrepancy budget. -/
theorem abs_twoDiscountWeightedDifference_le
    (forcing discount secant : ℕ → ℝ) (bound : ℝ)
    (hdiscount0 : ∀ time, 0 ≤ discount time)
    (hdiscount1 : ∀ time, discount time ≤ 1)
    (hsecant0 : ∀ time, 0 ≤ secant time)
    (hsecant1 : ∀ time, secant time ≤ 1)
    (hdiscrepancy : ∀ start length,
      |∑ offset ∈ Finset.range length, forcing (start + offset)| ≤ bound)
    (start length : ℕ) :
    |∑ offset ∈ Finset.range length,
        (survivalProduct discount start offset -
          survivalProduct secant start offset) *
          forcing (start + offset)| ≤ 2 * bound := by
  have hrewrite :
      (∑ offset ∈ Finset.range length,
        (survivalProduct discount start offset -
          survivalProduct secant start offset) *
          forcing (start + offset)) =
        (∑ offset ∈ Finset.range length,
          survivalProduct discount start offset * forcing (start + offset)) -
        ∑ offset ∈ Finset.range length,
          survivalProduct secant start offset * forcing (start + offset) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro offset _
    ring
  rw [hrewrite]
  calc
    _ ≤ |∑ offset ∈ Finset.range length,
          survivalProduct discount start offset * forcing (start + offset)| +
        |∑ offset ∈ Finset.range length,
          survivalProduct secant start offset * forcing (start + offset)| :=
      abs_sub _ _
    _ ≤ bound + bound := add_le_add
      (abs_survivalWeightedSum_le_of_suffixDiscrepancy forcing discount bound
        hdiscount0 hdiscount1 hdiscrepancy start length)
      (abs_survivalWeightedSum_le_of_suffixDiscrepancy forcing secant bound
        hsecant0 hsecant1 hdiscrepancy start length)
    _ = 2 * bound := by ring

/-- Sharp finite upper bound with one-sided terminal remainders. -/
theorem twoDiscountDebtError_le_oneSided
    (prescribedError bestResponseError prescribedDefect directDefect
      discount secant : ℕ → ℝ)
    (forcingBound adverseBound : ℝ)
    (hdiscount0 : ∀ time, 0 ≤ discount time)
    (hdiscount1 : ∀ time, discount time ≤ 1)
    (hsecant0 : ∀ time, 0 ≤ secant time)
    (hsecant1 : ∀ time, secant time ≤ 1)
    (hprescribedRec : ∀ time, prescribedError time =
      discount time * prescribedError (time + 1) - prescribedDefect time)
    (hbestResponseRec : ∀ time, bestResponseError time =
      secant time * bestResponseError (time + 1) -
        (prescribedDefect time + directDefect time))
    (hdiscrepancy : ∀ start length,
      |∑ offset ∈ Finset.range length,
        prescribedDefect (start + offset)| ≤ forcingBound)
    (start length : ℕ)
    (hadverse :
      -∑ offset ∈ Finset.range length,
        survivalProduct secant start offset *
          directDefect (start + offset) ≤ adverseBound) :
    bestResponseError start - prescribedError start ≤
      adverseBound + 2 * forcingBound +
        survivalProduct secant start length *
          max (bestResponseError (start + length)) 0 +
        survivalProduct discount start length *
          max (-prescribedError (start + length)) 0 := by
  rw [twoDiscountDebtError_eq prescribedError bestResponseError
    prescribedDefect directDefect discount secant start length
    hprescribedRec hbestResponseRec]
  have hforcing := le_abs_self
    (∑ offset ∈ Finset.range length,
      (survivalProduct discount start offset -
        survivalProduct secant start offset) *
        prescribedDefect (start + offset))
  have hforcingAbs := abs_twoDiscountWeightedDifference_le
    prescribedDefect discount secant forcingBound hdiscount0 hdiscount1
    hsecant0 hsecant1 hdiscrepancy start length
  have hsecantWeight := survivalProduct_nonneg secant hsecant0 start length
  have hdiscountWeight := survivalProduct_nonneg discount hdiscount0 start length
  have hbestTerminal :
      survivalProduct secant start length *
          bestResponseError (start + length) ≤
        survivalProduct secant start length *
          max (bestResponseError (start + length)) 0 :=
    mul_le_mul_of_nonneg_left (le_max_left _ _) hsecantWeight
  have hprescribedTerminal :
      -(survivalProduct discount start length *
          prescribedError (start + length)) ≤
        survivalProduct discount start length *
          max (-prescribedError (start + length)) 0 := by
    rw [← mul_neg]
    exact mul_le_mul_of_nonneg_left (le_max_left _ _) hdiscountWeight
  linarith

/-- Convenient finite upper bound with symmetric absolute-value terminal
remainders. -/
theorem twoDiscountDebtError_le_abs
    (prescribedError bestResponseError prescribedDefect directDefect
      discount secant : ℕ → ℝ)
    (forcingBound adverseBound : ℝ)
    (hdiscount0 : ∀ time, 0 ≤ discount time)
    (hdiscount1 : ∀ time, discount time ≤ 1)
    (hsecant0 : ∀ time, 0 ≤ secant time)
    (hsecant1 : ∀ time, secant time ≤ 1)
    (hprescribedRec : ∀ time, prescribedError time =
      discount time * prescribedError (time + 1) - prescribedDefect time)
    (hbestResponseRec : ∀ time, bestResponseError time =
      secant time * bestResponseError (time + 1) -
        (prescribedDefect time + directDefect time))
    (hdiscrepancy : ∀ start length,
      |∑ offset ∈ Finset.range length,
        prescribedDefect (start + offset)| ≤ forcingBound)
    (start length : ℕ)
    (hadverse :
      -∑ offset ∈ Finset.range length,
        survivalProduct secant start offset *
          directDefect (start + offset) ≤ adverseBound) :
    bestResponseError start - prescribedError start ≤
      adverseBound + 2 * forcingBound +
        survivalProduct secant start length *
          |bestResponseError (start + length)| +
        survivalProduct discount start length *
          |prescribedError (start + length)| := by
  refine (twoDiscountDebtError_le_oneSided prescribedError bestResponseError
    prescribedDefect directDefect discount secant forcingBound adverseBound
    hdiscount0 hdiscount1 hsecant0 hsecant1 hprescribedRec
    hbestResponseRec hdiscrepancy start length hadverse).trans ?_
  have hsecantWeight := survivalProduct_nonneg secant hsecant0 start length
  have hdiscountWeight := survivalProduct_nonneg discount hdiscount0 start length
  gcongr
  · exact max_le (le_abs_self _) (abs_nonneg _)
  · rw [← abs_neg]
    exact max_le (le_abs_self _) (abs_nonneg _)

/-- Infinite two-discount shadowing from limsup adverse forcing and vanishing
one-sided terminal remainders.  Neither forcing series need converge. -/
theorem twoDiscountDebtShadowing
    (prescribedError bestResponseError prescribedDefect directDefect
      discount secant : ℕ → ℝ)
    (forcingBound adverseBound : ℝ)
    (hdiscount0 : ∀ time, 0 ≤ discount time)
    (hdiscount1 : ∀ time, discount time ≤ 1)
    (hsecant0 : ∀ time, 0 ≤ secant time)
    (hsecant1 : ∀ time, secant time ≤ 1)
    (hprescribedRec : ∀ time, prescribedError time =
      discount time * prescribedError (time + 1) - prescribedDefect time)
    (hbestResponseRec : ∀ time, bestResponseError time =
      secant time * bestResponseError (time + 1) -
        (prescribedDefect time + directDefect time))
    (hdiscrepancy : ∀ start length,
      |∑ offset ∈ Finset.range length,
        prescribedDefect (start + offset)| ≤ forcingBound)
    (start : ℕ)
    (hadverse : ∀ slack, 0 < slack → ∀ᶠ length in atTop,
      -∑ offset ∈ Finset.range length,
        survivalProduct secant start offset *
          directDefect (start + offset) ≤ adverseBound + slack)
    (hbestTerminal : Tendsto (fun length ↦
      survivalProduct secant start length *
        max (bestResponseError (start + length)) 0) atTop (nhds 0))
    (hprescribedTerminal : Tendsto (fun length ↦
      survivalProduct discount start length *
        max (-prescribedError (start + length)) 0) atTop (nhds 0)) :
    bestResponseError start - prescribedError start ≤
      adverseBound + 2 * forcingBound := by
  refine le_of_forall_pos_le_add fun slack hslack ↦ ?_
  have hterminal : Tendsto (fun length ↦
      survivalProduct secant start length *
          max (bestResponseError (start + length)) 0 +
        survivalProduct discount start length *
          max (-prescribedError (start + length)) 0) atTop (nhds 0) :=
    by simpa using hbestTerminal.add hprescribedTerminal
  have hterminalEventually : ∀ᶠ length in atTop,
      survivalProduct secant start length *
          max (bestResponseError (start + length)) 0 +
        survivalProduct discount start length *
          max (-prescribedError (start + length)) 0 ≤ slack / 2 := by
    exact ((tendsto_order.1 hterminal).2 _ (by linarith)).mono
      (fun _ h ↦ h.le)
  obtain ⟨length, hadverseLength, hterminalLength⟩ :=
    ((hadverse (slack / 2) (by linarith)).and hterminalEventually).exists
  have hfinite := twoDiscountDebtError_le_oneSided
    prescribedError bestResponseError prescribedDefect directDefect
    discount secant forcingBound (adverseBound + slack / 2)
    hdiscount0 hdiscount1 hsecant0 hsecant1 hprescribedRec
    hbestResponseRec hdiscrepancy start length hadverseLength
  linarith

/-- **Optional owner-excess refinement.**

The prescribed error has all-suffix discrepancy at most `eta`.  The debt
error is driven by a generated secant, adverse direct forcing of asymptotic
size at most `eta`, and positive secant-over-discount mass at most `K`.
Vanishing survival removes both bounded terminal remainders. -/
theorem oneSidedDebtShadowing_with_excess
    (prescribedError debtError prescribedDefect directDefect
      discount secant : ℕ → ℝ)
    (eta K : ℝ)
    (heta : 0 ≤ eta)
    (hdiscount0 : ∀ time, 0 ≤ discount time)
    (hdiscount1 : ∀ time, discount time ≤ 1)
    (hsecant0 : ∀ time, 0 ≤ secant time)
    (hsecant1 : ∀ time, secant time ≤ 1)
    (hprescribedRec : ∀ time, prescribedError time =
      discount time * prescribedError (time + 1) - prescribedDefect time)
    (hdebtRec : ∀ time, debtError time =
      secant time * debtError (time + 1) +
        (secant time - discount time) * prescribedError (time + 1) -
        directDefect time)
    (hdiscrepancy : ∀ start length,
      |∑ offset ∈ Finset.range length,
        prescribedDefect (start + offset)| ≤ eta)
    (hdiscountSurvival : ∀ start,
      Tendsto (survivalProduct discount start) atTop (nhds 0))
    (hsecantSurvival : ∀ start,
      Tendsto (survivalProduct secant start) atTop (nhds 0))
    (hprescribedBound : ∃ bound : ℝ,
      ∀ time, |prescribedError time| ≤ bound)
    (hdebtBound : ∃ bound : ℝ, ∀ time, |debtError time| ≤ bound)
    (hadverse : ∀ start slack, 0 < slack →
      ∀ᶠ length in atTop,
        -∑ offset ∈ Finset.range length,
          survivalProduct secant start offset *
            directDefect (start + offset) ≤ eta + slack)
    (hexcess : ∀ start length,
      ∑ offset ∈ Finset.range length,
          survivalProduct secant start offset *
            max (secant (start + offset) - discount (start + offset)) 0 ≤ K)
    (start : ℕ) :
    debtError start ≤ (2 + 2 * K) * eta := by
  have hprescribed : ∀ time, |prescribedError time| ≤ eta :=
    fun time ↦ abs_prescribedError_le_of_suffixDiscrepancy
      prescribedError prescribedDefect discount eta hdiscount0 hdiscount1
      hprescribedRec hdiscrepancy hdiscountSurvival hprescribedBound time
  have hdebtUnroll : ∀ length,
      debtError start =
        survivalProduct secant start length * debtError (start + length) -
          ∑ offset ∈ Finset.range length,
            survivalProduct secant start offset * directDefect (start + offset) +
          ∑ offset ∈ Finset.range length,
            survivalProduct secant start offset *
              (secant (start + offset) - discount (start + offset)) *
              prescribedError (start + offset + 1) := by
    intro length
    have h := backwardRecursion_eq_weighted_sum_add_terminal debtError
      (fun time ↦ (secant time - discount time) * prescribedError (time + 1) -
        directDefect time) secant start length (fun time ↦ by
          rw [hdebtRec time]
          ring_nf)
    rw [h]
    simp only [mul_sub, Finset.sum_sub_distrib]
    ring_nf
  have hcoupling : ∀ length,
      ∑ offset ∈ Finset.range length,
          survivalProduct secant start offset *
            (secant (start + offset) - discount (start + offset)) *
            prescribedError (start + offset + 1) ≤
        (1 + 2 * K) * eta := by
    intro length
    have hterm : ∀ offset ∈ Finset.range length,
        survivalProduct secant start offset *
            (secant (start + offset) - discount (start + offset)) *
            prescribedError (start + offset + 1) ≤
          survivalProduct secant start offset *
            ((1 - secant (start + offset)) +
              2 * max (secant (start + offset) -
                discount (start + offset)) 0) * eta := by
      intro offset _
      have hweight := survivalProduct_nonneg secant hsecant0 start offset
      have habs := hprescribed (start + offset + 1)
      have hcoefficient :
          |secant (start + offset) - discount (start + offset)| ≤
            (1 - secant (start + offset)) +
              2 * max (secant (start + offset) -
                discount (start + offset)) 0 := by
        rw [abs_le]
        constructor
        · have hdiscount := hdiscount1 (start + offset)
          have hmax : 0 ≤ max (secant (start + offset) -
              discount (start + offset)) 0 := le_max_right _ _
          nlinarith
        · by_cases hpositive : 0 ≤ secant (start + offset) -
              discount (start + offset)
          · rw [max_eq_left hpositive]
            have hsec := hsecant1 (start + offset)
            nlinarith
          · rw [max_eq_right (le_of_not_ge hpositive)]
            have hsec := hsecant1 (start + offset)
            linarith
      calc
        _ ≤ survivalProduct secant start offset *
              |secant (start + offset) - discount (start + offset)| *
              |prescribedError (start + offset + 1)| := by
            calc
              _ ≤ |survivalProduct secant start offset *
                    (secant (start + offset) - discount (start + offset)) *
                    prescribedError (start + offset + 1)| := le_abs_self _
              _ = _ := by
                rw [abs_mul, abs_mul, abs_of_nonneg hweight]
        _ ≤ survivalProduct secant start offset *
              |secant (start + offset) - discount (start + offset)| * eta := by
            exact mul_le_mul_of_nonneg_left habs
              (mul_nonneg hweight (abs_nonneg _))
        _ ≤ survivalProduct secant start offset *
              ((1 - secant (start + offset)) +
                2 * max (secant (start + offset) -
                  discount (start + offset)) 0) * eta := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hcoefficient hweight) heta
    calc
      _ ≤ ∑ offset ∈ Finset.range length,
          survivalProduct secant start offset *
            ((1 - secant (start + offset)) +
              2 * max (secant (start + offset) -
                discount (start + offset)) 0) * eta :=
        Finset.sum_le_sum hterm
      _ = ((1 - survivalProduct secant start length) +
          2 * ∑ offset ∈ Finset.range length,
            survivalProduct secant start offset *
              max (secant (start + offset) - discount (start + offset)) 0) *
            eta := by
        rw [← Finset.sum_mul]
        congr 1
        have hsplit :
            (∑ offset ∈ Finset.range length,
              survivalProduct secant start offset *
                ((1 - secant (start + offset)) +
                  2 * max (secant (start + offset) -
                    discount (start + offset)) 0)) =
              (1 - survivalProduct secant start length) +
                2 * ∑ offset ∈ Finset.range length,
                  survivalProduct secant start offset *
                    max (secant (start + offset) -
                      discount (start + offset)) 0 := by
          calc
            _ = (∑ offset ∈ Finset.range length,
                  survivalProduct secant start offset *
                    (1 - secant (start + offset))) +
                ∑ offset ∈ Finset.range length,
                  2 * (survivalProduct secant start offset *
                    max (secant (start + offset) -
                      discount (start + offset)) 0) := by
                rw [← Finset.sum_add_distrib]
                apply Finset.sum_congr rfl
                intro offset _
                ring_nf
            _ = _ := by
              rw [sum_survivalProduct_mul_one_sub, Finset.mul_sum]
        exact hsplit
      _ ≤ (1 + 2 * K) * eta := by
        have hsurvival0 := survivalProduct_nonneg secant hsecant0 start length
        have hexcess' := hexcess start length
        nlinarith
  have hterminal := tendsto_survivalProduct_mul_bounded_zero secant debtError
    start (hsecantSurvival start) hdebtBound
  refine le_of_forall_pos_le_add fun slack hslack ↦ ?_
  have hterminalEventually : ∀ᶠ length in atTop,
      survivalProduct secant start length * debtError (start + length) ≤
        slack / 2 := by
    have hlt : ∀ᶠ length in atTop,
        survivalProduct secant start length * debtError (start + length) <
          slack / 2 :=
      (tendsto_order.1 hterminal).2 _ (by linarith)
    exact hlt.mono fun _ h ↦ h.le
  obtain ⟨length, hterminalLength, hadverseLength⟩ :=
    (hterminalEventually.and
      (hadverse start (slack / 2) (by linarith))).exists
  rw [hdebtUnroll length]
  have hcouplingLength := hcoupling length
  nlinarith

/-! ## Endpoint cancellation is not chronological cancellation -/

/-- Two forcing terms may cancel without controlling a survival-weighted
chronological cut.  The first coefficient is zero, so the later positive
compensation disappears while the initial adverse term keeps weight one.
This is algebraic evidence only; it is not a quitting-semantic
counterexample. -/
theorem exists_zero_sum_with_prescribed_adverse_survivalWeight
    (epsilon : ℝ) :
    ∃ forcing coefficient : ℕ → ℝ,
      (∀ time, 0 ≤ coefficient time ∧ coefficient time ≤ 1) ∧
      (∑ time ∈ Finset.range 2, forcing time) = 0 ∧
      -∑ time ∈ Finset.range 2,
          survivalProduct coefficient 0 time * forcing time = epsilon := by
  let forcing : ℕ → ℝ := fun time ↦
    if time = 0 then -epsilon else if time = 1 then epsilon else 0
  let coefficient : ℕ → ℝ := fun _ ↦ 0
  refine ⟨forcing, coefficient, ?_, ?_, ?_⟩
  · intro time
    simp [coefficient]
  · simp [Finset.sum_range_succ, forcing]
  · simp [Finset.sum_range_succ, forcing, coefficient, survivalProduct]

/-- Consequently, zero endpoint forcing does not by itself imply a
nonpositive chronological adverse forcing sum. -/
theorem zero_sum_does_not_imply_nonpositive_adverse_survivalWeight :
    ¬ (∀ (forcing coefficient : ℕ → ℝ),
      (∀ time, 0 ≤ coefficient time ∧ coefficient time ≤ 1) →
      (∑ time ∈ Finset.range 2, forcing time) = 0 →
      -∑ time ∈ Finset.range 2,
          survivalProduct coefficient 0 time * forcing time ≤ 0) := by
  intro himplication
  obtain ⟨forcing, coefficient, hcoefficient, hsum, hweighted⟩ :=
    exists_zero_sum_with_prescribed_adverse_survivalWeight 1
  have hle := himplication forcing coefficient hcoefficient hsum
  rw [hweighted] at hle
  norm_num at hle

end Math
