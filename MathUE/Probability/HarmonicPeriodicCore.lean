/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.Probability.FiniteClosedCoreReach
import MathUE.Probability.HarmonicGlobalCoupling

/-!
# Periodic closed cores of finite homogeneous Markov kernels

A recurrent class need not mix in one step: a deterministic cycle is the
basic obstruction.  The correct finite-dimensional object is a phase
decomposition.  One step sends all successors of a core state to one common
next phase, while one fixed kernel iterate preserves each phase and strictly
contracts its rows in total variation.

This file proves that every bounded backward-harmonic value has zero
one-step variation on such a core.  Thus the recurrent contribution to
Simon's homogeneous-chain variation vanishes.  The remaining contribution
comes only from transitions whose source is transient; bounding that part by
the sharp state-cardinality constant remains separate.
-/

namespace Math.Probability

noncomputable section

variable {Omega Phase : Type*} [Fintype Omega] [DecidableEq Omega]
  [DecidableEq Phase]

/-- Concrete periodic mixing data on a closed subset of a finite kernel.
The fields concern support and row contraction, not the desired variation
bound. -/
structure PeriodicClosedCoreMixing
    (kernel : Omega -> PMF Omega) (core : Finset Omega) where
  phase : Omega -> Phase
  block : Nat
  block_pos : 0 < block
  rho : Phase -> Real
  rho_nonneg : forall label, 0 <= rho label
  rho_lt_one : forall label, rho label < 1
  closed : IsClosedCore kernel (core : Set Omega)
  successor_phase : forall {source}, source ∈ core ->
    forall {first second}, first ∈ (kernel source).support ->
      second ∈ (kernel source).support -> phase first = phase second
  block_preserves_phase : forall {source}, source ∈ core ->
    forall {destination},
      destination ∈ (Math.PMFIter.iter kernel block source).support ->
        destination ∈ core /\ phase destination = phase source
  row_tv_le : forall {first second}, first ∈ core -> second ∈ core ->
    phase first = phase second ->
      pmfTV (Math.PMFIter.iter kernel block first)
        (Math.PMFIter.iter kernel block second) <= rho (phase first)

/-- A periodic mixing package with an existentially chosen phase-label type. -/
structure PeriodicClosedCoreMixingPackage
    (kernel : Omega -> PMF Omega) (core : Finset Omega) where
  Phase : Type
  instDecidableEqPhase : DecidableEq Phase
  mixing : PeriodicClosedCoreMixing (Phase := Phase) kernel core

/-- Exact source-native finite-chain principle used by the global argument.
The support graph chooses its own phase-label type.  This is a graph-period/
primitive-power proposition about closed communicating classes; it mentions
neither harmonic values nor a variation bound. -/
def FiniteClosedClassPeriodicMixingPrinciple
    (Omega : Type*) [Fintype Omega] [DecidableEq Omega] : Prop :=
  forall (kernel : Omega -> PMF Omega) (initial : Omega),
    forall closedClass : ReachableClosedClass kernel initial,
      Nonempty (PeriodicClosedCoreMixingPackage kernel closedClass.states)

/-- The states in one displayed phase of the closed core. -/
def PeriodicClosedCoreMixing.Fiber
    {kernel : Omega -> PMF Omega} {core : Finset Omega}
    (mixing : PeriodicClosedCoreMixing (Phase := Phase) kernel core)
    (label : Phase) :=
  {state : Omega // state ∈ core /\ mixing.phase state = label}

noncomputable instance PeriodicClosedCoreMixing.instFintypeFiber
    {kernel : Omega -> PMF Omega} {core : Finset Omega}
    (mixing : PeriodicClosedCoreMixing (Phase := Phase) kernel core)
    (label : Phase) : Fintype (mixing.Fiber label) :=
  Fintype.subtype
    (core.filter fun state => mixing.phase state = label)
    (fun state => by simp)

namespace PeriodicClosedCoreMixing

variable {kernel : Omega -> PMF Omega} {core : Finset Omega}
  (mixing : PeriodicClosedCoreMixing (Phase := Phase) kernel core)

omit [DecidableEq Omega] in
theorem finiteSpan_expect_block_le
    (label : Phase) [Nonempty (mixing.Fiber label)]
    (f : Omega -> Real) :
    finiteSpan (fun state : mixing.Fiber label =>
      expect (Math.PMFIter.iter kernel mixing.block state.1) f) <=
        mixing.rho label *
          finiteSpan (fun state : mixing.Fiber label => f state.1) := by
  classical
  apply finiteSpan_le_of_pairwise
  intro first second
  have hfirstCore : first.1 ∈ core := first.2.1
  have hsecondCore : second.1 ∈ core := second.2.1
  have hphase : mixing.phase first.1 = mixing.phase second.1 :=
    first.2.2.trans second.2.2.symm
  calc
    |expect (Math.PMFIter.iter kernel mixing.block first.1) f -
        expect (Math.PMFIter.iter kernel mixing.block second.1) f| <=
      finiteSpan (fun state : mixing.Fiber label => f state.1) *
        pmfTV (Math.PMFIter.iter kernel mixing.block first.1)
          (Math.PMFIter.iter kernel mixing.block second.1) := by
        apply abs_expect_sub_le_pairwise_on_common_support_mul_pmfTV
          (P := fun state => state ∈ core /\ mixing.phase state = label)
        · intro state hstate
          have hsupport : state ∈
              (Math.PMFIter.iter kernel mixing.block first.1).support := by
            simpa [PMF.mem_support_iff] using hstate
          exact mixing.block_preserves_phase hfirstCore hsupport |>.imp_right
            (fun equality => equality.trans first.2.2)
        · intro state hstate
          have hsupport : state ∈
              (Math.PMFIter.iter kernel mixing.block second.1).support := by
            simpa [PMF.mem_support_iff] using hstate
          exact mixing.block_preserves_phase hsecondCore hsupport |>.imp_right
            (fun equality => equality.trans second.2.2)
        · intro firstState hfirst secondState hsecond
          exact abs_sub_le_finiteSpan
            (fun state : mixing.Fiber label => f state.1)
            ⟨firstState, hfirst⟩ ⟨secondState, hsecond⟩
    _ <= finiteSpan (fun state : mixing.Fiber label => f state.1) *
        mixing.rho label :=
      mul_le_mul_of_nonneg_left (by
        simpa [first.2.2] using
          mixing.row_tv_le hfirstCore hsecondCore hphase)
        (finiteSpan_nonneg _)
    _ = mixing.rho label *
        finiteSpan (fun state : mixing.Fiber label => f state.1) :=
      mul_comm _ _

omit [DecidableEq Omega] in
theorem finiteSpan_value_le_pow
    (value : Omega -> Nat -> Real)
    (harmonic : forall state time,
      value state time = expect (kernel state) (fun successor =>
        value successor (time + 1)))
    (label : Phase) [Nonempty (mixing.Fiber label)]
    (time steps : Nat) :
    finiteSpan (fun state : mixing.Fiber label => value state.1 time) <=
      mixing.rho label ^ steps *
        finiteSpan (fun state : mixing.Fiber label =>
          value state.1 (time + steps * mixing.block)) := by
  induction steps generalizing time with
  | zero => simp
  | succ steps ih =>
      have hone : finiteSpan (fun state : mixing.Fiber label =>
          value state.1 time) <=
          mixing.rho label * finiteSpan (fun state : mixing.Fiber label =>
            value state.1 (time + mixing.block)) := by
        have hfun : (fun state : mixing.Fiber label => value state.1 time) =
            fun state => expect
              (Math.PMFIter.iter kernel mixing.block state.1)
              (fun successor => value successor (time + mixing.block)) := by
          funext state
          exact backwardHarmonic_eq_expect_iter kernel value harmonic
            state.1 time mixing.block
        rw [hfun]
        exact mixing.finiteSpan_expect_block_le label _
      have htail := ih (time + mixing.block)
      calc
        finiteSpan (fun state : mixing.Fiber label => value state.1 time) <=
            mixing.rho label * finiteSpan (fun state : mixing.Fiber label =>
              value state.1 (time + mixing.block)) := hone
        _ <= mixing.rho label *
            (mixing.rho label ^ steps *
              finiteSpan (fun state : mixing.Fiber label =>
                value state.1
                  (time + mixing.block + steps * mixing.block))) :=
          mul_le_mul_of_nonneg_left htail (mixing.rho_nonneg label)
        _ = mixing.rho label ^ (steps + 1) *
            finiteSpan (fun state : mixing.Fiber label =>
              value state.1 (time + (steps + 1) * mixing.block)) := by
          rw [pow_succ]
          have htime : time + mixing.block + steps * mixing.block =
              time + (steps + 1) * mixing.block := by
            rw [Nat.add_mul]
            omega
          rw [htime]
          ring

omit [DecidableEq Omega] in
theorem finiteSpan_value_eq_zero
    (value : Omega -> Nat -> Real)
    (bounded : forall state time, value state time ∈ Set.Icc (0 : Real) 1)
    (harmonic : forall state time,
      value state time = expect (kernel state) (fun successor =>
        value successor (time + 1)))
    (label : Phase) [Nonempty (mixing.Fiber label)] (time : Nat) :
    finiteSpan (fun state : mixing.Fiber label => value state.1 time) = 0 := by
  apply le_antisymm
  · apply ge_of_tendsto'
      (tendsto_pow_atTop_nhds_zero_of_lt_one
        (mixing.rho_nonneg label) (mixing.rho_lt_one label))
    intro steps
    calc
      finiteSpan (fun state : mixing.Fiber label => value state.1 time) <=
          mixing.rho label ^ steps *
            finiteSpan (fun state : mixing.Fiber label =>
              value state.1 (time + steps * mixing.block)) :=
        mixing.finiteSpan_value_le_pow value harmonic label time steps
      _ <= mixing.rho label ^ steps * 1 :=
        mul_le_mul_of_nonneg_left
          (finiteSpan_le_one_of_mem_Icc (fun state =>
            bounded state.1 (time + steps * mixing.block)))
          (pow_nonneg (mixing.rho_nonneg label) steps)
      _ = mixing.rho label ^ steps := mul_one _
  · exact finiteSpan_nonneg _

omit [DecidableEq Omega] in
/-- States in the same recurrent phase have the same value at every time. -/
theorem value_eq_of_same_phase
    (value : Omega -> Nat -> Real)
    (bounded : forall state time, value state time ∈ Set.Icc (0 : Real) 1)
    (harmonic : forall state time,
      value state time = expect (kernel state) (fun successor =>
        value successor (time + 1)))
    {first second : Omega} (hfirst : first ∈ core)
    (hsecond : second ∈ core)
    (hphase : mixing.phase first = mixing.phase second)
    (time : Nat) :
    value first time = value second time := by
  classical
  let label := mixing.phase first
  letI : Nonempty (mixing.Fiber label) :=
    ⟨⟨first, hfirst, rfl⟩⟩
  have hzero := mixing.finiteSpan_value_eq_zero
    value bounded harmonic label time
  have hconstant := (finiteSpan_eq_zero_iff
    (fun state : mixing.Fiber label => value state.1 time)).mp hzero
  exact hconstant ⟨first, hfirst, rfl⟩
    ⟨second, hsecond, hphase.symm⟩

omit [DecidableEq Omega] in
include mixing in
/-- Every supported one-step transition whose source is in the periodic
closed core carries exactly zero backward-harmonic increment. -/
theorem value_successor_eq_of_mem_core
    (value : Omega -> Nat -> Real)
    (bounded : forall state time, value state time ∈ Set.Icc (0 : Real) 1)
    (harmonic : forall state time,
      value state time = expect (kernel state) (fun successor =>
        value successor (time + 1)))
    {source successor : Omega} (hsource : source ∈ core)
    (hsuccessor : successor ∈ (kernel source).support) (time : Nat) :
    value successor (time + 1) = value source time := by
  classical
  obtain ⟨fallback, hfallback⟩ := (kernel source).support_nonempty
  have hsuccessorCore := mixing.closed hsource hsuccessor
  have hfallbackCore := mixing.closed hsource hfallback
  have hsame : forall next, next ∈ (kernel source).support ->
      value next (time + 1) = value successor (time + 1) := by
    intro next hnext
    exact mixing.value_eq_of_same_phase value bounded harmonic
      (mixing.closed hsource hnext) hsuccessorCore
      (mixing.successor_phase hsource hnext hsuccessor) (time + 1)
  calc
    value successor (time + 1) =
        expect (kernel source) (fun _ => value successor (time + 1)) :=
      (expect_const (kernel source) _).symm
    _ = expect (kernel source) (fun next => value next (time + 1)) := by
      rw [expect_eq_sum, expect_eq_sum]
      apply Finset.sum_congr rfl
      intro next _
      by_cases hnext : next ∈ (kernel source).support
      · rw [hsame next hnext]
      · have hzero : kernel source next = 0 := by
          simpa [PMF.mem_support_iff] using hnext
        simp [hzero]
    _ = value source time := (harmonic source time).symm

end PeriodicClosedCoreMixing

/-! ## Isolation of the transient contribution -/

omit [DecidableEq Omega] [DecidableEq Phase] in
/-- Finite expected variation is the sum of the ordinary current-state
marginals applied to the one-step conditional variation. -/
theorem finiteExpectedSpaceTimeMarkovVariation_eq_sum_iter_conditional
    (initial : Omega) (kernel : Omega -> PMF Omega)
    (value : Omega -> Nat -> Real) (horizon : Nat) :
    finiteExpectedSpaceTimeMarkovVariation initial kernel value horizon =
      ∑ time ∈ Finset.range horizon,
        expect (Math.PMFIter.iter kernel time initial) (fun source =>
          expect (kernel source) (fun successor =>
            |value successor (time + 1) - value source time|)) := by
  induction horizon with
  | zero => simp [finiteExpectedSpaceTimeMarkovVariation,
      expectedDecisionVariation]
  | succ horizon ih =>
      rw [finiteExpectedSpaceTimeMarkovVariation,
        expectedDecisionVariation, Finset.sum_range_succ]
      change
        (∑ k ∈ Finset.range (horizon + 1),
          expect
            (adaptiveHistoryLaw
              (homogeneousMarkovStep initial kernel) k)
            (fun history =>
              expect (homogeneousMarkovStep initial kernel k history)
                (fun successor =>
                  |spaceTimeMarkovScore value k history successor|))) +
          expect
            (adaptiveHistoryLaw
              (homogeneousMarkovStep initial kernel) (horizon + 1))
            (fun history =>
              expect
                (homogeneousMarkovStep initial kernel (horizon + 1) history)
                (fun successor =>
                  |spaceTimeMarkovScore value (horizon + 1) history successor|)) = _
      rw [← expectedDecisionVariation,
        ← finiteExpectedSpaceTimeMarkovVariation, ih,
        Finset.sum_range_succ]
      congr 1
      have hmarginal := expect_adaptiveHistoryLaw_homogeneous_last
        initial kernel horizon (fun source =>
          expect (kernel source) (fun successor =>
            |value successor (horizon + 1) - value source horizon|))
      rw [← hmarginal]
      apply congrArg
      funext history
      rfl

omit [DecidableEq Omega] in
/-- On a displayed periodic closed core, conditional variation is zero at
core sources and at most one at transient sources. -/
theorem PeriodicClosedCoreMixing.conditionalVariation_le_transientCharge
    {kernel : Omega -> PMF Omega} {core : Finset Omega}
    (mixing : PeriodicClosedCoreMixing (Phase := Phase) kernel core)
    (value : Omega -> Nat -> Real)
    (bounded : forall state time, value state time ∈ Set.Icc (0 : Real) 1)
    (harmonic : forall state time,
      value state time = expect (kernel state) (fun successor =>
        value successor (time + 1)))
    (source : Omega) (time : Nat) :
    expect (kernel source) (fun successor =>
      |value successor (time + 1) - value source time|) <=
        transientCharge (core : Set Omega) source := by
  classical
  by_cases hsource : source ∈ core
  · rw [transientCharge_of_mem hsource]
    rw [expect_eq_sum]
    apply Finset.sum_nonpos
    intro successor _
    by_cases hsuccessor : successor ∈ (kernel source).support
    · rw [mixing.value_successor_eq_of_mem_core
        value bounded harmonic hsource hsuccessor time]
      simp
    · have hzero : kernel source successor = 0 := by
        simpa [PMF.mem_support_iff] using hsuccessor
      simp [hzero]
  · rw [transientCharge_of_not_mem hsource]
    calc
      expect (kernel source) (fun successor =>
          |value successor (time + 1) - value source time|) <=
          expect (kernel source) (fun _ => (1 : Real)) := by
        apply expect_mono
        intro successor
        rw [abs_le]
        constructor <;>
          linarith [(bounded successor (time + 1)).1,
            (bounded successor (time + 1)).2,
            (bounded source time).1, (bounded source time).2]
      _ = 1 := expect_const _ _

omit [DecidableEq Omega] in
/-- Periodic recurrent phases contribute no variation.  Every finite global
variation prefix is bounded by the expected number of transient source
visits over the same prefix. -/
theorem PeriodicClosedCoreMixing.finiteExpectedVariation_le_transientOccupation
    {kernel : Omega -> PMF Omega} {core : Finset Omega}
    (mixing : PeriodicClosedCoreMixing (Phase := Phase) kernel core)
    (initial : Omega) (value : Omega -> Nat -> Real)
    (harmonic : IsUnitIntervalBackwardMarkovHarmonic kernel value)
    (horizon : Nat) :
    finiteExpectedSpaceTimeMarkovVariation initial kernel value horizon <=
      ∑ time ∈ Finset.range horizon,
        expect (Math.PMFIter.iter kernel time initial)
          (transientCharge (core : Set Omega)) := by
  rw [finiteExpectedSpaceTimeMarkovVariation_eq_sum_iter_conditional]
  apply Finset.sum_le_sum
  intro time _
  apply expect_mono
  intro source
  exact mixing.conditionalVariation_le_transientCharge
    value harmonic.1 harmonic.2 source time

omit [DecidableEq Omega] in
/-- Combining the periodic-core decomposition with the existing hitting-time
Poisson certificate leaves one explicit transient constant.  Replacing this
quantity by the sharp state-cardinality budget is exactly the remaining
global problem; no statewise renewal factorization is used here. -/
theorem PeriodicClosedCoreMixing.finiteExpectedVariation_le_transiencePotential
    {kernel : Omega -> PMF Omega} {core : Finset Omega}
    (mixing : PeriodicClosedCoreMixing (Phase := Phase) kernel core)
    (certificate : ClosedCoreTransienceCertificate
      kernel (core : Set Omega))
    (initial : Omega) (value : Omega -> Nat -> Real)
    (harmonic : IsUnitIntervalBackwardMarkovHarmonic kernel value)
    (horizon : Nat) :
    finiteExpectedSpaceTimeMarkovVariation initial kernel value horizon <=
      (certificate.horizon : Real) / certificate.minorization := by
  exact (mixing.finiteExpectedVariation_le_transientOccupation
    initial value harmonic horizon).trans
      (certificate.total_transientOccupation_le horizon initial)

/-! ## Exact periodic barrier -/

namespace TogglePeriodicBarrier

def kernel (state : Bool) : PMF Bool :=
  PMF.pure (!state)

def iterState : Nat -> Bool -> Bool
  | 0, state => state
  | steps + 1, state => iterState steps (!state)

theorem iter_kernel (steps : Nat) (state : Bool) :
    Math.PMFIter.iter kernel steps state = PMF.pure (iterState steps state) := by
  induction steps generalizing state with
  | zero => simp [iterState]
  | succ steps ih =>
      rw [Math.PMFIter.iter_succ]
      simp [kernel, ih, iterState]

theorem iterState_true_eq_not_false (steps : Nat) :
    iterState steps true = !(iterState steps false) := by
  induction steps with
  | zero => rfl
  | succ steps ih =>
      simp only [iterState, Bool.not_true, Bool.not_false]
      rw [ih]
      simp

theorem iter_rows_tv_eq_one (steps : Nat) :
    pmfTV (Math.PMFIter.iter kernel steps false)
      (Math.PMFIter.iter kernel steps true) = 1 := by
  rw [iter_kernel, iter_kernel, pmfTV_bool_eq_abs_apply_true,
    iterState_true_eq_not_false]
  cases iterState steps false <;> simp

/-- No power of the two-cycle mixes the whole recurrent class.  This is the
formal obstruction to replacing periodic phases by one global Dobrushin
argument. -/
theorem not_eventuallyStrictDobrushin :
    ¬HasEventuallyStrictDobrushinContraction kernel := by
  rintro ⟨block, _block_pos, rho, _rho_nonneg, rho_lt_one, rows⟩
  have hrow := rows false true
  rw [iter_rows_tv_eq_one block] at hrow
  linarith

/-- The same chain has an exact phase decomposition: two steps preserve each
singleton phase, and contraction inside a singleton is zero. -/
def periodicMixing :
    PeriodicClosedCoreMixing (Phase := Bool) kernel Finset.univ where
  phase := id
  block := 2
  block_pos := by norm_num
  rho := fun _ => 0
  rho_nonneg := fun _ => le_rfl
  rho_lt_one := fun _ => by norm_num
  closed := by
    intro _ _ destination _
    exact Finset.mem_univ destination
  successor_phase := by
    intro source _ first second hfirst hsecond
    simp [kernel] at hfirst hsecond
    change first = second
    exact hfirst.trans hsecond.symm
  block_preserves_phase := by
    intro source _ destination hdestination
    rw [iter_kernel] at hdestination
    have hdest : destination = source := by
      simpa [iterState, PMF.mem_support_iff] using hdestination
    subst destination
    exact ⟨Finset.mem_univ _, rfl⟩
  row_tv_le := by
    intro first second _ _ hphase
    change first = second at hphase
    subst second
    simp

/-- Thus the periodic-core theorem proves zero variation on a genuinely
periodic class even though no whole-class mixing iterate exists. -/
theorem finiteExpectedVariation_eq_zero
    (initial : Bool) (value : Bool -> Nat -> Real)
    (harmonic : IsUnitIntervalBackwardMarkovHarmonic kernel value)
    (horizon : Nat) :
    finiteExpectedSpaceTimeMarkovVariation initial kernel value horizon = 0 := by
  apply le_antisymm
  · have hbound := periodicMixing.finiteExpectedVariation_le_transientOccupation
      initial value harmonic horizon
    change finiteExpectedSpaceTimeMarkovVariation initial kernel value horizon <=
      ∑ time ∈ Finset.range horizon,
        expect (Math.PMFIter.iter kernel time initial)
          (transientCharge ((Finset.univ : Finset Bool) : Set Bool)) at hbound
    have hcharge :
        transientCharge ((Finset.univ : Finset Bool) : Set Bool) =
          fun _ => (0 : Real) := by
      funext state
      cases state <;> simp [transientCharge]
    rw [hcharge] at hbound
    simpa using hbound
  · exact finiteExpectedSpaceTimeMarkovVariation_nonneg
      initial kernel value horizon

end TogglePeriodicBarrier

end

end Math.Probability
