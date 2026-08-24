/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.Probability.DiscreteHazardMixture

/-!
# Reconstructing a discrete hazard from its stopping law

Every probability law on `Option Nat` is the first-stop law of a scalar
hazard.  The `none` atom is the probability of never stopping.  The hazard at
time `n` is the mass at `some n`, divided by the mass which has survived all
earlier dates; after survival has reached zero its value is immaterial and is
set to zero.
-/

noncomputable section

open scoped BigOperators

namespace Math.Probability.DiscreteHazard

open Filter Math.Probability Math.ProbabilityMassFunction

/-- The coding of `Never` by zero and finite time `n` by `n + 1`. -/
def optionNatEquivNat : Option ℕ ≃ ℕ where
  toFun
    | none => 0
    | some n => n + 1
  invFun
    | 0 => none
    | n + 1 => some n
  left_inv choice := by cases choice <;> simp
  right_inv code := by cases code <;> simp

namespace StoppingLaw

/-- Probability mass at one finite stopping date. -/
def finiteMass (law : PMF (Option ℕ)) (time : ℕ) : ℝ :=
  (law (some time)).toReal

/-- Probability mass remaining after all dates strictly before `cutoff`. -/
def survival (law : PMF (Option ℕ)) (cutoff : ℕ) : ℝ :=
  1 - ∑ time ∈ Finset.range cutoff, finiteMass law time

theorem finiteMass_nonneg (law : PMF (Option ℕ)) (time : ℕ) :
    0 ≤ finiteMass law time :=
  ENNReal.toReal_nonneg

private theorem summable_encoded (law : PMF (Option ℕ)) :
    Summable fun code : ℕ => (law (optionNatEquivNat.symm code)).toReal := by
  exact (optionNatEquivNat.symm.summable_iff).2 (pmf_toReal_summable law)

theorem none_add_tsum_finiteMass (law : PMF (Option ℕ)) :
    (law none).toReal + ∑' time, finiteMass law time = 1 := by
  have htotal := pmf_toReal_tsum_one law
  have hcode : (∑' code : ℕ,
      (law (optionNatEquivNat.symm code)).toReal) = 1 := by
    exact (optionNatEquivNat.symm.tsum_eq
      (fun choice => (law choice).toReal)).trans htotal
  rw [(summable_encoded law).tsum_eq_zero_add] at hcode
  simpa [optionNatEquivNat, finiteMass] using hcode

theorem sum_finiteMass_le_one (law : PMF (Option ℕ)) (cutoff : ℕ) :
    (∑ time ∈ Finset.range cutoff, finiteMass law time) ≤ 1 := by
  have hsummable : Summable (finiteMass law) := by
    change Summable (fun time : ℕ => (law (some time)).toReal)
    exact (pmf_toReal_summable law).comp_injective (Option.some_injective ℕ)
  have hprefix := hsummable.sum_le_tsum (Finset.range cutoff)
    (fun time _ => finiteMass_nonneg law time)
  have hnone := ENNReal.toReal_nonneg (a := law none)
  have htotal := none_add_tsum_finiteMass law
  linarith

theorem survival_nonneg (law : PMF (Option ℕ)) (cutoff : ℕ) :
    0 ≤ survival law cutoff := by
  rw [survival, sub_nonneg]
  exact sum_finiteMass_le_one law cutoff

@[simp] theorem survival_zero (law : PMF (Option ℕ)) :
    survival law 0 = 1 := by simp [survival]

theorem survival_succ (law : PMF (Option ℕ)) (time : ℕ) :
    survival law (time + 1) = survival law time - finiteMass law time := by
  rw [survival, survival, Finset.sum_range_succ]
  ring

theorem finiteMass_le_survival (law : PMF (Option ℕ)) (time : ℕ) :
    finiteMass law time ≤ survival law time := by
  have hnext := survival_nonneg law (time + 1)
  rw [survival_succ law] at hnext
  linarith

/-- The conditional hazard reconstructed from a complete stopping law. -/
def toScalarHazard (law : PMF (Option ℕ)) : ScalarHazard where
  stop time := if survival law time = 0 then 0
    else finiteMass law time / survival law time
  stop_nonneg time := by
    split_ifs
    · exact le_rfl
    · exact div_nonneg (finiteMass_nonneg law time)
        (survival_nonneg law time)
  stop_le_one time := by
    split_ifs with hzero
    · norm_num
    · exact (div_le_one
        ((survival_nonneg law time).lt_of_ne' hzero)).2
          (finiteMass_le_survival law time)

theorem toScalarHazard_survival (law : PMF (Option ℕ)) (cutoff : ℕ) :
    (toScalarHazard law).survival 0 cutoff = survival law cutoff := by
  induction cutoff with
  | zero => simp [ScalarHazard.survival_zero]
  | succ time ih =>
      rw [ScalarHazard.survival_succ, ih]
      simp only [Nat.zero_add]
      by_cases hzero : survival law time = 0
      · have hnextLe : survival law (time + 1) ≤ survival law time := by
          rw [survival_succ law]
          exact sub_le_self _ (finiteMass_nonneg law time)
        have hnext : survival law (time + 1) = 0 := by
          linarith [survival_nonneg law (time + 1)]
        simp [toScalarHazard, hzero, hnext]
      · rw [show (toScalarHazard law).stop time =
            finiteMass law time / survival law time by
          simp [toScalarHazard, hzero]]
        rw [survival_succ law]
        field_simp [hzero]

theorem toScalarHazard_stopMass (law : PMF (Option ℕ)) (time : ℕ) :
    (toScalarHazard law).stopMass time = finiteMass law time := by
  rw [ScalarHazard.stopMass_eq_survival_sub_succ,
    toScalarHazard_survival, toScalarHazard_survival,
    survival_succ]
  ring

theorem tendsto_survival_none (law : PMF (Option ℕ)) :
    Tendsto (survival law) atTop (nhds (law none).toReal) := by
  have hsummable : Summable (finiteMass law) := by
    change Summable (fun time : ℕ => (law (some time)).toReal)
    exact (pmf_toReal_summable law).comp_injective (Option.some_injective ℕ)
  have hfinite := hsummable.hasSum.tendsto_sum_nat
  have htotal := none_add_tsum_finiteMass law
  have hsub : Tendsto
      (fun cutoff : ℕ => 1 -
        ∑ time ∈ Finset.range cutoff, finiteMass law time)
      atTop (nhds (1 - ∑' time, finiteMass law time)) :=
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1)).sub
      hfinite
  have hlimit : 1 - ∑' time, finiteMass law time = (law none).toReal := by
    linarith
  rw [← hlimit]
  exact hsub

theorem toScalarHazard_neverMass (law : PMF (Option ℕ)) :
    (toScalarHazard law).neverMass = (law none).toReal := by
  have heq : (toScalarHazard law).survival 0 = survival law := by
    funext cutoff
    exact toScalarHazard_survival law cutoff
  have hhazard := (toScalarHazard law).tendsto_survival_neverMass
  rw [heq] at hhazard
  exact tendsto_nhds_unique hhazard (tendsto_survival_none law)

/-- Reconstruction is exact at the level of the complete stopping law. -/
@[simp] theorem stoppingLaw_toScalarHazard (law : PMF (Option ℕ)) :
    (toScalarHazard law).stoppingLaw = law := by
  apply Math.ProbabilityMassFunction.eq_of_forall_toReal_eq
  intro choice
  cases choice with
  | none => simp [toScalarHazard_neverMass]
  | some time => simp [toScalarHazard_stopMass, finiteMass]

end StoppingLaw
end Math.Probability.DiscreteHazard
