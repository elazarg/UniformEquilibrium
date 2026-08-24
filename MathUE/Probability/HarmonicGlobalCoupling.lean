/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.Probability.HarmonicVisitEpoch
import MathUE.Probability.SwitchedPotentialCalculus
import MathUE.ProbabilityMassFunction.TotalVariation

/-!
# Global contraction for bounded backward-harmonic Markov values

The two statewise renewal factorizations in `HarmonicStateAccount` are false.
This file records a genuinely coupled finite-state building block instead.
If all rows of a homogeneous kernel have pairwise total-variation distance at
most one fixed `rho < 1`, the whole Markov operator contracts spatial span.
A bounded backward orbit cannot survive that contraction: its span is zero at
every time.  Harmonicity then also makes the common value independent of time,
so the expected space-time variation is exactly zero.

This settles the strict-mixing recurrent-class regime.  It is not Simon's
global cardinality lemma: periodic recurrent classes and transient decoding
still require a coupled decomposition.
-/

namespace Math.Probability

noncomputable section

variable {Omega : Type*} [Fintype Omega] [Nonempty Omega]

/-- Pairwise row contraction in total variation, with an explicit strict
coefficient.  Unlike a state-owned renewal budget, this compares the entire
Markov operator across all source states at once. -/
def HasStrictDobrushinContraction
    (kernel : Omega -> PMF Omega) : Prop :=
  exists rho : Real, 0 <= rho /\ rho < 1 /\
    forall first second, pmfTV (kernel first) (kernel second) <= rho

/-- Some positive iterate of the kernel has a strict global Dobrushin
coefficient.  This is the natural interface for a primitive recurrent class:
the original rows need not overlap after one step. -/
def HasEventuallyStrictDobrushinContraction
    (kernel : Omega -> PMF Omega) : Prop :=
  exists block : Nat, 0 < block /\
    HasStrictDobrushinContraction (Math.PMFIter.iter kernel block)

theorem abs_sub_le_finiteSpan (f : Omega -> Real) (first second : Omega) :
    |f first - f second| <= finiteSpan f := by
  rw [abs_le]
  constructor
  · have hmax := le_finiteMax f second
    have hmin := finiteMin_le f first
    dsimp only [finiteSpan]
    linarith
  · have hmax := le_finiteMax f first
    have hmin := finiteMin_le f second
    dsimp only [finiteSpan]
    linarith

theorem finiteSpan_le_of_pairwise {f : Omega -> Real} {bound : Real}
    (pairwise : forall first second, |f first - f second| <= bound) :
    finiteSpan f <= bound := by
  let values : Finset Real := Finset.univ.image f
  have hvalues : values.Nonempty := Finset.univ_nonempty.image f
  have hmin := Finset.min'_mem values hvalues
  have hmax := Finset.max'_mem values hvalues
  obtain ⟨first, _, hfirst⟩ := Finset.mem_image.mp hmax
  obtain ⟨second, _, hsecond⟩ := Finset.mem_image.mp hmin
  change Finset.univ.sup' Finset.univ_nonempty f -
      Finset.univ.inf' Finset.univ_nonempty f <= bound
  have hmaxEq : Finset.univ.sup' Finset.univ_nonempty f = values.max' hvalues := by
    apply le_antisymm
    · apply Finset.sup'_le
      intro state _
      exact Finset.le_max' values (f state)
        (Finset.mem_image.mpr ⟨state, Finset.mem_univ state, rfl⟩)
    · rw [← hfirst]
      exact Finset.le_sup' f (Finset.mem_univ first)
  have hminEq : Finset.univ.inf' Finset.univ_nonempty f = values.min' hvalues := by
    apply le_antisymm
    · rw [← hsecond]
      exact Finset.inf'_le f (Finset.mem_univ second)
    · apply Finset.le_inf'
      intro state _
      exact Finset.min'_le values (f state)
        (Finset.mem_image.mpr ⟨state, Finset.mem_univ state, rfl⟩)
  rw [hmaxEq, hminEq, ← hfirst, ← hsecond]
  exact (le_abs_self (f first - f second)).trans (pairwise first second)

theorem finiteSpan_le_one_of_mem_Icc {f : Omega -> Real}
    (range : forall state, f state ∈ Set.Icc (0 : Real) 1) :
    finiteSpan f <= 1 := by
  apply finiteSpan_le_of_pairwise
  intro first second
  rw [abs_le]
  constructor <;> linarith [(range first).1, (range first).2,
    (range second).1, (range second).2]

theorem finiteSpan_eq_zero_iff (f : Omega -> Real) :
    finiteSpan f = 0 <-> forall first second, f first = f second := by
  constructor
  · intro hspan first second
    have hpair := abs_sub_le_finiteSpan f first second
    rw [hspan] at hpair
    have habs : |f first - f second| = 0 :=
      le_antisymm hpair (abs_nonneg _)
    exact sub_eq_zero.mp (abs_eq_zero.mp habs)
  · intro hconstant
    have base := Classical.arbitrary Omega
    have hfun : f = fun _ => f base := by
      funext state
      exact hconstant state base
    rw [hfun, finiteSpan, finiteMax_const, finiteMin_const, sub_self]

/-- A strict total-variation contraction of the kernel contracts the spatial
span of every finite observable. -/
theorem finiteSpan_expect_kernel_le
    (kernel : Omega -> PMF Omega) {rho : Real}
    (rows : forall first second,
      pmfTV (kernel first) (kernel second) <= rho)
    (f : Omega -> Real) :
    finiteSpan (fun state => expect (kernel state) f) <= rho * finiteSpan f := by
  apply finiteSpan_le_of_pairwise
  intro first second
  calc
    |expect (kernel first) f - expect (kernel second) f| <=
        finiteSpan f * pmfTV (kernel first) (kernel second) :=
      abs_expect_sub_le_pairwise_mul_pmfTV
        (kernel first) (kernel second) f (abs_sub_le_finiteSpan f)
    _ <= finiteSpan f * rho :=
      mul_le_mul_of_nonneg_left (rows first second) (finiteSpan_nonneg f)
    _ = rho * finiteSpan f := mul_comm _ _

/-- Iterating backward harmonicity exposes an arbitrary power of the strict
global contraction coefficient. -/
theorem finiteSpan_backwardHarmonic_le_pow
    (kernel : Omega -> PMF Omega) (value : Omega -> Nat -> Real)
    (harmonic : forall state time,
      value state time = expect (kernel state) (fun successor =>
        value successor (time + 1)))
    {rho : Real}
    (rows : forall first second,
      pmfTV (kernel first) (kernel second) <= rho)
    (rho_nonneg : 0 <= rho) (time steps : Nat) :
    finiteSpan (fun state => value state time) <=
      rho ^ steps * finiteSpan (fun state => value state (time + steps)) := by
  induction steps generalizing time with
  | zero => simp
  | succ steps ih =>
      have hone : finiteSpan (fun state => value state time) <=
          rho * finiteSpan (fun state => value state (time + 1)) := by
        have hfun : (fun state => value state time) =
            fun state => expect (kernel state) (fun successor =>
              value successor (time + 1)) := by
          funext state
          exact harmonic state time
        rw [hfun]
        exact finiteSpan_expect_kernel_le kernel rows _
      have htail := ih (time + 1)
      calc
        finiteSpan (fun state => value state time) <=
            rho * finiteSpan (fun state => value state (time + 1)) := hone
        _ <= rho * (rho ^ steps *
            finiteSpan (fun state => value state (time + 1 + steps))) :=
          mul_le_mul_of_nonneg_left htail rho_nonneg
        _ = rho ^ (steps + 1) *
            finiteSpan (fun state => value state (time + (steps + 1))) := by
          have htime : time + 1 + steps = time + (steps + 1) := by omega
          rw [htime, pow_succ]
          ring

omit [Nonempty Omega] in
/-- Backward harmonicity composes through every fixed number of steps. -/
theorem backwardHarmonic_eq_expect_iter
    (kernel : Omega -> PMF Omega) (value : Omega -> Nat -> Real)
    (harmonic : forall state time,
      value state time = expect (kernel state) (fun successor =>
        value successor (time + 1)))
    (state : Omega) (time steps : Nat) :
    value state time = expect (Math.PMFIter.iter kernel steps state)
      (fun successor => value successor (time + steps)) := by
  induction steps generalizing state time with
  | zero => simp
  | succ steps ih =>
      rw [harmonic state time]
      conv_lhs =>
        enter [2, successor]
        rw [ih successor (time + 1)]
      rw [← expect_bind]
      change
        expect (Math.PMFIter.iter kernel (steps + 1) state)
            (fun successor => value successor (time + 1 + steps)) =
          expect (Math.PMFIter.iter kernel (steps + 1) state)
            (fun successor => value successor (time + (steps + 1)))
      apply congrArg
      funext successor
      congr 1
      omega

/-- In the strict-mixing regime, a bounded backward-harmonic orbit has zero
spatial span at every time. -/
theorem finiteSpan_backwardHarmonic_eq_zero_of_strictDobrushin
    (kernel : Omega -> PMF Omega) (value : Omega -> Nat -> Real)
    (contraction : HasStrictDobrushinContraction kernel)
    (bounded : forall state time, value state time ∈ Set.Icc (0 : Real) 1)
    (harmonic : forall state time,
      value state time = expect (kernel state) (fun successor =>
        value successor (time + 1)))
    (time : Nat) :
    finiteSpan (fun state => value state time) = 0 := by
  obtain ⟨rho, rho_nonneg, rho_lt_one, rows⟩ := contraction
  apply le_antisymm
  · apply ge_of_tendsto'
      (tendsto_pow_atTop_nhds_zero_of_lt_one rho_nonneg rho_lt_one)
    intro steps
    calc
      finiteSpan (fun state => value state time) <=
          rho ^ steps * finiteSpan (fun state => value state (time + steps)) :=
        finiteSpan_backwardHarmonic_le_pow kernel value harmonic rows rho_nonneg time steps
      _ <= rho ^ steps * 1 :=
        mul_le_mul_of_nonneg_left
          (finiteSpan_le_one_of_mem_Icc (fun state => bounded state (time + steps)))
          (pow_nonneg rho_nonneg steps)
      _ = rho ^ steps := mul_one _
  · exact finiteSpan_nonneg _

/-- A bounded backward orbit also has zero spatial span when strict mixing
appears only after a positive fixed number of kernel steps. -/
theorem finiteSpan_backwardHarmonic_eq_zero_of_eventuallyStrictDobrushin
    (kernel : Omega -> PMF Omega) (value : Omega -> Nat -> Real)
    (contraction : HasEventuallyStrictDobrushinContraction kernel)
    (bounded : forall state time, value state time ∈ Set.Icc (0 : Real) 1)
    (harmonic : forall state time,
      value state time = expect (kernel state) (fun successor =>
        value successor (time + 1)))
    (time : Nat) :
    finiteSpan (fun state => value state time) = 0 := by
  obtain ⟨block, _block_pos, blockContraction⟩ := contraction
  let blockValue : Omega -> Nat -> Real := fun state index =>
    value state (time + index * block)
  have blockBounded : forall state index,
      blockValue state index ∈ Set.Icc (0 : Real) 1 := by
    intro state index
    exact bounded state (time + index * block)
  have blockHarmonic : forall state index,
      blockValue state index =
        expect (Math.PMFIter.iter kernel block state) (fun successor =>
          blockValue successor (index + 1)) := by
    intro state index
    have hiter := backwardHarmonic_eq_expect_iter kernel value harmonic
      state (time + index * block) block
    simpa [blockValue, Nat.add_mul, Nat.add_assoc] using hiter
  simpa [blockValue] using
    finiteSpan_backwardHarmonic_eq_zero_of_strictDobrushin
      (Math.PMFIter.iter kernel block) blockValue blockContraction
      blockBounded blockHarmonic 0

/-- Strict global row contraction leaves only one constant backward-harmonic
orbit.  In particular every one-step increment is exactly zero. -/
theorem backwardHarmonic_eq_successor_of_strictDobrushin
    (kernel : Omega -> PMF Omega) (value : Omega -> Nat -> Real)
    (contraction : HasStrictDobrushinContraction kernel)
    (bounded : forall state time, value state time ∈ Set.Icc (0 : Real) 1)
    (harmonic : forall state time,
      value state time = expect (kernel state) (fun successor =>
        value successor (time + 1))) :
    forall state successor time,
      value successor (time + 1) = value state time := by
  intro state successor time
  have hconstant := (finiteSpan_eq_zero_iff
    (fun current => value current (time + 1))).mp
      (finiteSpan_backwardHarmonic_eq_zero_of_strictDobrushin
        kernel value contraction bounded harmonic (time + 1))
  calc
    value successor (time + 1) = value state (time + 1) :=
      hconstant successor state
    _ = expect (kernel state) (fun _ => value state (time + 1)) :=
      (expect_const (kernel state) (value state (time + 1))).symm
    _ = expect (kernel state) (fun next => value next (time + 1)) := by
      apply congrArg
      funext next
      exact hconstant state next
    _ = value state time := (harmonic state time).symm

/-- Eventual strict mixing gives the same exact one-step constancy; the block
iterate is used only to kill spatial span, while the original harmonic
equation identifies adjacent times. -/
theorem backwardHarmonic_eq_successor_of_eventuallyStrictDobrushin
    (kernel : Omega -> PMF Omega) (value : Omega -> Nat -> Real)
    (contraction : HasEventuallyStrictDobrushinContraction kernel)
    (bounded : forall state time, value state time ∈ Set.Icc (0 : Real) 1)
    (harmonic : forall state time,
      value state time = expect (kernel state) (fun successor =>
        value successor (time + 1))) :
    forall state successor time,
      value successor (time + 1) = value state time := by
  intro state successor time
  have hconstant := (finiteSpan_eq_zero_iff
    (fun current => value current (time + 1))).mp
      (finiteSpan_backwardHarmonic_eq_zero_of_eventuallyStrictDobrushin
        kernel value contraction bounded harmonic (time + 1))
  calc
    value successor (time + 1) = value state (time + 1) :=
      hconstant successor state
    _ = expect (kernel state) (fun _ => value state (time + 1)) :=
      (expect_const (kernel state) (value state (time + 1))).symm
    _ = expect (kernel state) (fun next => value next (time + 1)) := by
      apply congrArg
      funext next
      exact hconstant state next
    _ = value state time := (harmonic state time).symm

/-- The globally coupled strict-mixing regime has exactly zero finite
space-time variation, hence satisfies Simon's bound with maximal slack. -/
theorem finiteExpectedSpaceTimeMarkovVariation_eq_zero_of_strictDobrushin
    (initial : Omega) (kernel : Omega -> PMF Omega)
    (value : Omega -> Nat -> Real)
    (contraction : HasStrictDobrushinContraction kernel)
    (harmonic : IsUnitIntervalBackwardMarkovHarmonic kernel value)
    (horizon : Nat) :
    finiteExpectedSpaceTimeMarkovVariation initial kernel value horizon = 0 := by
  have hincrement := backwardHarmonic_eq_successor_of_strictDobrushin
    kernel value contraction harmonic.1 harmonic.2
  rw [finiteExpectedSpaceTimeMarkovVariation, expectedDecisionVariation]
  apply Finset.sum_eq_zero
  intro round _
  rw [expect_eq_sum]
  apply Finset.sum_eq_zero
  intro history _
  cases round with
  | zero => simp
  | succ time =>
      apply mul_eq_zero.mpr
      right
      rw [expect_eq_sum]
      apply Finset.sum_eq_zero
      intro successor _
      simp only [spaceTimeMarkovScore_succ, abs_eq_zero, mul_eq_zero]
      right
      exact sub_eq_zero.mpr
        (hincrement (history (Fin.last time)) successor time)

/-- The eventual strict-mixing regime likewise has zero global variation. -/
theorem finiteExpectedSpaceTimeMarkovVariation_eq_zero_of_eventuallyStrictDobrushin
    (initial : Omega) (kernel : Omega -> PMF Omega)
    (value : Omega -> Nat -> Real)
    (contraction : HasEventuallyStrictDobrushinContraction kernel)
    (harmonic : IsUnitIntervalBackwardMarkovHarmonic kernel value)
    (horizon : Nat) :
    finiteExpectedSpaceTimeMarkovVariation initial kernel value horizon = 0 := by
  have hincrement := backwardHarmonic_eq_successor_of_eventuallyStrictDobrushin
    kernel value contraction harmonic.1 harmonic.2
  rw [finiteExpectedSpaceTimeMarkovVariation, expectedDecisionVariation]
  apply Finset.sum_eq_zero
  intro round _
  rw [expect_eq_sum]
  apply Finset.sum_eq_zero
  intro history _
  cases round with
  | zero => simp
  | succ time =>
      apply mul_eq_zero.mpr
      right
      rw [expect_eq_sum]
      apply Finset.sum_eq_zero
      intro successor _
      simp only [spaceTimeMarkovScore_succ, abs_eq_zero, mul_eq_zero]
      right
      exact sub_eq_zero.mpr
        (hincrement (history (Fin.last time)) successor time)

end

end Math.Probability
