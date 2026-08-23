/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.Probability

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
