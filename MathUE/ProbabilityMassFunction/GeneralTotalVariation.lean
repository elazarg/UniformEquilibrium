/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.ProbabilityMassFunction.TotalVariation

/-!
# Total variation for arbitrary probability mass functions

The finite-state `pmfTV` interface uses a finite sum.  Discrete stopping laws
live on `Option Nat`, so this file records the equivalent non-overlap formula
with a `tsum`.  It also isolates the estimate obtained by distinguishing one
cemetery atom from all finite atoms.
-/

noncomputable section

namespace Math
namespace Probability

/-- Total variation of arbitrary PMFs, written as one minus their common
overlap mass. -/
def pmfGeneralTV {Omega : Type*} (mu nu : PMF Omega) : Real :=
  1 - ∑' omega, min ((mu omega).toReal) ((nu omega).toReal)

private theorem summable_overlap {Omega : Type*} (mu nu : PMF Omega) :
    Summable (fun omega => min ((mu omega).toReal) ((nu omega).toReal)) := by
  exact Summable.of_nonneg_of_le
    (fun _ => le_min ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
    (fun _ => min_le_left _ _) (pmf_toReal_summable mu)

theorem pmfGeneralTV_nonneg {Omega : Type*} (mu nu : PMF Omega) :
    0 <= pmfGeneralTV mu nu := by
  unfold pmfGeneralTV
  rw [sub_nonneg]
  simpa [pmf_toReal_tsum_one mu] using
    (summable_overlap mu nu).tsum_le_tsum
      (fun omega => min_le_left ((mu omega).toReal) ((nu omega).toReal))
      (pmf_toReal_summable mu)

theorem pmfGeneralTV_symm {Omega : Type*} (mu nu : PMF Omega) :
    pmfGeneralTV mu nu = pmfGeneralTV nu mu := by
  unfold pmfGeneralTV
  congr 2
  funext omega
  exact min_comm _ _

/-- A bounded test function changes its expectation by at most twice its
absolute bound times total variation. -/
theorem abs_expect_sub_le_two_mul_bound_mul_pmfGeneralTV
    {Omega : Type*} (mu nu : PMF Omega) (f : Omega -> Real) {M : Real}
    (hbound : forall omega, |f omega| <= M) :
    |expect mu f - expect nu f| <= 2 * M * pmfGeneralTV mu nu := by
  exact abs_expect_sub_le_two_mul_bound_mul_one_sub_overlap mu nu f hbound

/-- Binding an arbitrary discrete source law through a finite-valued Markov
kernel contracts general total variation. -/
theorem pmfTV_bind_le_pmfGeneralTV {Alpha Beta : Type*} [Fintype Beta]
    (kernel : Alpha -> PMF Beta) (mu nu : PMF Alpha) :
    pmfTV (mu.bind kernel) (nu.bind kernel) <= pmfGeneralTV mu nu := by
  let witness : Beta -> Real :=
    pmfPositiveVariationWitness (mu.bind kernel) (nu.bind kernel) 1
  let averaged : Alpha -> Real := fun a => expect (kernel a) witness
  let centered : Alpha -> Real := fun a => averaged a - 1 / 2
  have hw0 : forall b, 0 <= witness b := fun b =>
    pmfPositiveVariationWitness_nonneg
      (mu.bind kernel) (nu.bind kernel) zero_le_one b
  have hw1 : forall b, witness b <= 1 := fun b =>
    pmfPositiveVariationWitness_le
      (mu.bind kernel) (nu.bind kernel) zero_le_one b
  have ha0 : forall a, 0 <= averaged a := fun a =>
    expect_nonneg (kernel a) witness hw0
  have ha1 : forall a, averaged a <= 1 := by
    intro a
    simpa [averaged] using
      expect_mono (kernel a) witness (fun _ => 1) hw1
  have hc : forall a, |centered a| <= 1 / 2 := by
    intro a
    rw [abs_le]
    constructor <;> dsimp only [centered] <;> linarith [ha0 a, ha1 a]
  have hvariation :=
    abs_expect_sub_le_two_mul_bound_mul_pmfGeneralTV mu nu centered hc
  have havg_mu : Summable (fun a => (mu a).toReal * averaged a) :=
    expect_summable_of_bounded mu averaged fun a => by
      rw [abs_of_nonneg (ha0 a)]
      exact ha1 a
  have havg_nu : Summable (fun a => (nu a).toReal * averaged a) :=
    expect_summable_of_bounded nu averaged fun a => by
      rw [abs_of_nonneg (ha0 a)]
      exact ha1 a
  have hcenter_mu : expect mu centered = expect mu averaged - 1 / 2 := by
    have h := expect_add_of_summable mu averaged (fun _ => -(1 / 2))
      havg_mu ((pmf_toReal_summable mu).mul_right (-(1 / 2)))
    simpa only [centered, sub_eq_add_neg, expect_const] using h
  have hcenter_nu : expect nu centered = expect nu averaged - 1 / 2 := by
    have h := expect_add_of_summable nu averaged (fun _ => -(1 / 2))
      havg_nu ((pmf_toReal_summable nu).mul_right (-(1 / 2)))
    simpa only [centered, sub_eq_add_neg, expect_const] using h
  calc
    pmfTV (mu.bind kernel) (nu.bind kernel) =
        expect mu averaged - expect nu averaged := by
      rw [show pmfTV (mu.bind kernel) (nu.bind kernel) =
          expect (mu.bind kernel) witness - expect (nu.bind kernel) witness by
        symm
        simpa [witness] using
          expect_sub_pmfPositiveVariationWitness
            (mu.bind kernel) (nu.bind kernel) 1]
      rw [expect_bind, expect_bind]
    _ <= |expect mu centered - expect nu centered| := by
      rw [hcenter_mu, hcenter_nu]
      have heq :
          (expect mu averaged - 1 / 2) - (expect nu averaged - 1 / 2) =
            expect mu averaged - expect nu averaged := by ring
      rw [heq]
      exact le_abs_self _
    _ <= 2 * (1 / 2) * pmfGeneralTV mu nu := hvariation
    _ = pmfGeneralTV mu nu := by ring

/-- If all but one atom are grouped together, total variation is at most the
sum of the two masses outside the distinguished atom. -/
theorem pmfGeneralTV_le_one_sub_apply_add_one_sub_apply
    {Omega : Type*} (mu nu : PMF Omega) (cemetery : Omega) :
    pmfGeneralTV mu nu <=
      (1 - (mu cemetery).toReal) + (1 - (nu cemetery).toReal) := by
  let overlap : Omega -> Real := fun omega =>
    min ((mu omega).toReal) ((nu omega).toReal)
  have hoverlapNonneg : forall omega, 0 <= overlap omega := fun omega =>
    le_min ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  have hoverlapSummable : Summable overlap := summable_overlap mu nu
  have hsingle : overlap cemetery <= ∑' omega, overlap omega := by
    exact hoverlapSummable.le_tsum cemetery fun omega _ => hoverlapNonneg omega
  have hmuOne : (mu cemetery).toReal <= 1 :=
    ENNReal.toReal_mono ENNReal.one_ne_top (PMF.coe_le_one mu cemetery)
  have hnuOne : (nu cemetery).toReal <= 1 :=
    ENNReal.toReal_mono ENNReal.one_ne_top (PMF.coe_le_one nu cemetery)
  have hmin :
      (mu cemetery).toReal + (nu cemetery).toReal - 1 <=
        overlap cemetery := by
    dsimp only [overlap]
    apply le_min <;> linarith
  unfold pmfGeneralTV
  change 1 - ∑' omega, overlap omega <= _
  linarith

end Probability
end Math
