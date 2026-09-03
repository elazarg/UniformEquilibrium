/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.ControllerTester.ForwardLedger
import UniformEquilibrium.Quitting.Terminal.TailCompression.ElementaryNeverCoupling
import MathUE.ProbabilityMassFunction.Simplex

/-!
# Exact tester-flow and Bellman duality

This module packages the scalar stopping problem faced by one player against
a supplied chronology of opponent product marginals.  Feasible flows retain
the live, stop, and continue masses separately.  Bellman supersolutions retain
the opponent-survival transversality condition explicitly.

The distinguished dual witness is the literal all-behavior best-response
value of every reached suffix.  Thus the construction never replaces a
calendar-dependent behavioral deviation by a stationary strategy.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Nonnegative live, stop, and continue masses for one tester. -/
structure QuittingTesterFlow where
  live : ℕ → ℝ
  stop : ℕ → ℝ
  carry : ℕ → ℝ

@[ext] theorem QuittingTesterFlow.ext
    {first second : QuittingTesterFlow}
    (hlive : first.live = second.live)
    (hstop : first.stop = second.stop)
    (hcarry : first.carry = second.carry) : first = second := by
  cases first
  cases second
  simp_all

/-- Exact flow constraints against the opponents of `who`. -/
def QuittingTesterFlow.IsFeasible
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (flow : QuittingTesterFlow) : Prop :=
  flow.live 0 = 1 ∧
    (∀ time, 0 ≤ flow.live time) ∧
    (∀ time, 0 ≤ flow.stop time) ∧
    (∀ time, 0 ≤ flow.carry time) ∧
    (∀ time, flow.stop time + flow.carry time = flow.live time) ∧
    (∀ time, flow.live (time + 1) =
      quittingTesterOpponentContinueMass (roots time) who *
        flow.carry time)

/-- Opponent survival from date zero to a cutoff. -/
def quittingTesterOpponentSurvival
    (roots : ℕ → ι → PMF Bool) (who : ι) (cutoff : ℕ) : ℝ :=
  quittingOpponentSurvivalWeight roots who 0 cutoff

/-- One-stage payoff contribution carried by a tester flow. -/
def quittingTesterFlowPayoffTerm
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (flow : QuittingTesterFlow) (time : ℕ) : ℝ :=
  flow.stop time * quittingTesterQuitValue reward (roots time) who +
    flow.carry time *
      quittingTesterContinueContribution reward (roots time) who

/-- Infinite tester payoff, once absolute summability has been established. -/
def quittingTesterFlowPayoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (flow : QuittingTesterFlow) : ℝ :=
  ∑' time, quittingTesterFlowPayoffTerm reward roots who flow time

/-- Flow mass consumed by either stopping or opponent absorption. -/
def quittingTesterFlowConsumed
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (flow : QuittingTesterFlow) (time : ℕ) : ℝ :=
  flow.stop time + flow.carry time *
    (1 - quittingTesterOpponentContinueMass (roots time) who)

theorem QuittingTesterFlow.IsFeasible.carry_le_live
    {roots : ℕ → ι → PMF Bool} {who : ι} {flow : QuittingTesterFlow}
    (hflow : flow.IsFeasible roots who) (time : ℕ) :
    flow.carry time ≤ flow.live time := by
  rw [← hflow.2.2.2.2.1 time]
  exact le_add_of_nonneg_left (hflow.2.2.1 time)

theorem QuittingTesterFlow.IsFeasible.live_le_opponentSurvival
    {roots : ℕ → ι → PMF Bool} {who : ι} {flow : QuittingTesterFlow}
    (hflow : flow.IsFeasible roots who) (time : ℕ) :
    flow.live time ≤ quittingTesterOpponentSurvival roots who time := by
  induction time with
  | zero => simpa [quittingTesterOpponentSurvival,
      quittingOpponentSurvivalWeight] using hflow.1.le
  | succ time ih =>
      rw [hflow.2.2.2.2.2 time]
      unfold quittingTesterOpponentSurvival
      rw [quittingOpponentSurvivalWeight_succ]
      simp only [Nat.zero_add]
      have hmass : 0 ≤ quittingTesterOpponentContinueMass (roots time) who :=
        quittingRootOpponentContinueMass_nonneg (roots time) who
      calc
        quittingTesterOpponentContinueMass (roots time) who *
            flow.carry time ≤
          quittingTesterOpponentContinueMass (roots time) who *
            flow.live time :=
          mul_le_mul_of_nonneg_left (hflow.carry_le_live time) hmass
        _ ≤ quittingTesterOpponentContinueMass (roots time) who *
            quittingOpponentSurvivalWeight roots who 0 time :=
          mul_le_mul_of_nonneg_left ih hmass
        _ = quittingOpponentSurvivalWeight roots who 0 time *
            quittingFixedOpponentsContinueMass roots who time := by
          unfold quittingTesterOpponentContinueMass
            quittingFixedOpponentsContinueMass
            quittingRootOpponentContinueMass
          ring

theorem QuittingTesterFlow.IsFeasible.sum_consumed
    {roots : ℕ → ι → PMF Bool} {who : ι} {flow : QuittingTesterFlow}
    (hflow : flow.IsFeasible roots who) (cutoff : ℕ) :
    (∑ time ∈ Finset.range cutoff,
      quittingTesterFlowConsumed roots who flow time) =
        1 - flow.live cutoff := by
  induction cutoff with
  | zero => simp [quittingTesterFlowConsumed, hflow.1]
  | succ cutoff ih =>
      rw [Finset.sum_range_succ, ih, hflow.2.2.2.2.2 cutoff]
      rw [← hflow.2.2.2.2.1 cutoff]
      unfold quittingTesterFlowConsumed
      ring

theorem QuittingTesterFlow.IsFeasible.consumed_nonneg
    {roots : ℕ → ι → PMF Bool} {who : ι} {flow : QuittingTesterFlow}
    (hflow : flow.IsFeasible roots who) (time : ℕ) :
    0 ≤ quittingTesterFlowConsumed roots who flow time := by
  unfold quittingTesterFlowConsumed
  exact add_nonneg (hflow.2.2.1 time)
    (mul_nonneg (hflow.2.2.2.1 time)
      (sub_nonneg.mpr
        (quittingRootOpponentContinueMass_le_one (roots time) who)))

theorem QuittingTesterFlow.IsFeasible.summable_consumed
    {roots : ℕ → ι → PMF Bool} {who : ι} {flow : QuittingTesterFlow}
    (hflow : flow.IsFeasible roots who) :
    Summable (quittingTesterFlowConsumed roots who flow) := by
  apply summable_of_sum_range_le (c := 1) hflow.consumed_nonneg
  intro cutoff
  rw [hflow.sum_consumed cutoff]
  linarith [hflow.2.1 cutoff]

theorem QuittingTesterFlow.IsFeasible.abs_payoffTerm_le
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {roots : ℕ → ι → PMF Bool} {who : ι} {flow : QuittingTesterFlow}
    (hflow : flow.IsFeasible roots who) (time : ℕ) :
    |quittingTesterFlowPayoffTerm reward roots who flow time| ≤
      quittingRewardBound reward *
        quittingTesterFlowConsumed roots who flow time := by
  have hstop := abs_quittingTesterQuitValue_le reward (roots time) who
  have hcarry := abs_quittingTesterContinueContribution_le
    reward (roots time) who
  have htriangle := abs_add_le
    (flow.stop time * quittingTesterQuitValue reward (roots time) who)
    (flow.carry time *
      quittingTesterContinueContribution reward (roots time) who)
  unfold quittingTesterFlowPayoffTerm
  calc
    |_ + _| ≤
        |flow.stop time * quittingTesterQuitValue reward (roots time) who| +
          |flow.carry time *
            quittingTesterContinueContribution reward (roots time) who| :=
      htriangle
    _ = flow.stop time *
          |quittingTesterQuitValue reward (roots time) who| +
        flow.carry time *
          |quittingTesterContinueContribution reward (roots time) who| := by
      rw [abs_mul, abs_mul, abs_of_nonneg (hflow.2.2.1 time),
        abs_of_nonneg (hflow.2.2.2.1 time)]
    _ ≤ flow.stop time * quittingRewardBound reward +
        flow.carry time * (quittingRewardBound reward *
          (1 - quittingTesterOpponentContinueMass (roots time) who)) :=
      add_le_add
        (mul_le_mul_of_nonneg_left hstop (hflow.2.2.1 time))
        (mul_le_mul_of_nonneg_left hcarry (hflow.2.2.2.1 time))
    _ = quittingRewardBound reward *
        quittingTesterFlowConsumed roots who flow time := by
      unfold quittingTesterFlowConsumed
      ring

theorem QuittingTesterFlow.IsFeasible.summable_payoffTerm
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {roots : ℕ → ι → PMF Bool} {who : ι} {flow : QuittingTesterFlow}
    (hflow : flow.IsFeasible roots who) :
    Summable (quittingTesterFlowPayoffTerm reward roots who flow) := by
  have hmajor : Summable (fun time => quittingRewardBound reward *
      quittingTesterFlowConsumed roots who flow time) :=
    hflow.summable_consumed.mul_left (quittingRewardBound reward)
  apply Summable.of_norm_bounded hmajor
  intro time
  simpa [Real.norm_eq_abs] using
    (hflow.abs_payoffTerm_le (reward := reward) time)

/-- A bounded Bellman supersolution with the exact deleted-survival
transversality condition. -/
structure QuittingTesterBellmanDual
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) where
  value : ℕ → ℝ
  bounded : ∃ bound, ∀ time, |value time| ≤ bound
  quit_le : ∀ time,
    quittingTesterQuitValue reward (roots time) who ≤ value time
  continue_le : ∀ time,
    quittingTesterContinueContribution reward (roots time) who +
        quittingTesterOpponentContinueMass (roots time) who *
          value (time + 1) ≤ value time
  transversality : 0 ≤ Filter.liminf
    (fun time => quittingTesterOpponentSurvival roots who time * value time)
      Filter.atTop

theorem QuittingTesterBellmanDual.finite_weak_duality
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {roots : ℕ → ι → PMF Bool} {who : ι}
    {flow : QuittingTesterFlow} (hflow : flow.IsFeasible roots who)
    (dual : QuittingTesterBellmanDual reward roots who) (cutoff : ℕ) :
    (∑ time ∈ Finset.range cutoff,
        quittingTesterFlowPayoffTerm reward roots who flow time) +
      flow.live cutoff * dual.value cutoff ≤ dual.value 0 := by
  induction cutoff with
  | zero => simp [hflow.1]
  | succ cutoff ih =>
      have hsplit := hflow.2.2.2.2.1 cutoff
      have hnext := hflow.2.2.2.2.2 cutoff
      have hstop := mul_le_mul_of_nonneg_left (dual.quit_le cutoff)
        (hflow.2.2.1 cutoff)
      have hcarry := mul_le_mul_of_nonneg_left (dual.continue_le cutoff)
        (hflow.2.2.2.1 cutoff)
      rw [Finset.sum_range_succ]
      unfold quittingTesterFlowPayoffTerm
      calc
        (∑ time ∈ Finset.range cutoff,
              quittingTesterFlowPayoffTerm reward roots who flow time) +
            (flow.stop cutoff *
                quittingTesterQuitValue reward (roots cutoff) who +
              flow.carry cutoff *
                quittingTesterContinueContribution reward
                  (roots cutoff) who) +
            flow.live (cutoff + 1) * dual.value (cutoff + 1) =
          (∑ time ∈ Finset.range cutoff,
              quittingTesterFlowPayoffTerm reward roots who flow time) +
            (flow.stop cutoff *
                quittingTesterQuitValue reward (roots cutoff) who +
              flow.carry cutoff *
                (quittingTesterContinueContribution reward
                    (roots cutoff) who +
                  quittingTesterOpponentContinueMass (roots cutoff) who *
                    dual.value (cutoff + 1))) := by
          rw [hnext]
          ring
        _ ≤ (∑ time ∈ Finset.range cutoff,
              quittingTesterFlowPayoffTerm reward roots who flow time) +
            (flow.stop cutoff * dual.value cutoff +
              flow.carry cutoff * dual.value cutoff) := by
          gcongr
        _ = (∑ time ∈ Finset.range cutoff,
              quittingTesterFlowPayoffTerm reward roots who flow time) +
            flow.live cutoff * dual.value cutoff := by
          rw [← hsplit]
          ring
        _ ≤ dual.value 0 := ih

theorem QuittingTesterBellmanDual.eventually_neg_lt_live_mul
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {roots : ℕ → ι → PMF Bool} {who : ι}
    {flow : QuittingTesterFlow} (hflow : flow.IsFeasible roots who)
    (dual : QuittingTesterBellmanDual reward roots who)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ time in Filter.atTop, -ε < flow.live time * dual.value time := by
  obtain ⟨bound, hbound⟩ := dual.bounded
  have hbound0 : 0 ≤ bound := by
    exact (abs_nonneg (dual.value 0)).trans (hbound 0)
  have hsurvivalLower : ∀ time,
      -bound ≤ quittingTesterOpponentSurvival roots who time *
        dual.value time := by
    intro time
    have hL0 := quittingOpponentSurvivalWeight_nonneg roots who 0 time
    have hL1 := quittingOpponentSurvivalWeight_le_one roots who 0 time
    have hw := (abs_le.mp (hbound time)).1
    by_cases hw0 : 0 ≤ dual.value time
    · exact (neg_nonpos.mpr hbound0).trans (mul_nonneg hL0 hw0)
    · have hmul : dual.value time ≤
          quittingTesterOpponentSurvival roots who time * dual.value time := by
        have := mul_le_mul_of_nonneg_right hL1 (neg_nonneg.mpr (le_of_not_ge hw0))
        simpa [quittingTesterOpponentSurvival] using this
      exact hw.trans hmul
  have hlim : -ε < Filter.liminf
      (fun time => quittingTesterOpponentSurvival roots who time *
        dual.value time) Filter.atTop :=
    (neg_lt_zero.mpr hε).trans_le dual.transversality
  have heventually := Filter.eventually_lt_of_lt_liminf hlim
    (Filter.isBoundedUnder_of_eventually_ge
      (Filter.Eventually.of_forall hsurvivalLower))
  filter_upwards [heventually] with time htime
  have hy0 := hflow.2.1 time
  have hyL := hflow.live_le_opponentSurvival time
  by_cases hw0 : 0 ≤ dual.value time
  · exact (neg_lt_zero.mpr hε).trans_le (mul_nonneg hy0 hw0)
  · have hcompare : quittingTesterOpponentSurvival roots who time *
        dual.value time ≤ flow.live time * dual.value time :=
      mul_le_mul_of_nonpos_right hyL (le_of_not_ge hw0)
    exact htime.trans_le hcompare

/-- Literal weak duality for every feasible infinite flow and every bounded
transversal Bellman supersolution. -/
theorem quittingTesterFlowPayoff_le_dual
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {roots : ℕ → ι → PMF Bool} {who : ι}
    {flow : QuittingTesterFlow} (hflow : flow.IsFeasible roots who)
    (dual : QuittingTesterBellmanDual reward roots who) :
    quittingTesterFlowPayoff reward roots who flow ≤ dual.value 0 := by
  apply le_of_forall_pos_le_add
  intro ε hε
  have hpartial := hflow.summable_payoffTerm (reward := reward)
  apply le_of_tendsto hpartial.hasSum.tendsto_sum_nat
  filter_upwards [dual.eventually_neg_lt_live_mul hflow hε] with cutoff hboundary
  have hfinite := dual.finite_weak_duality hflow cutoff
  linarith

/-- The exact tester flow induced by an arbitrary calendar-dependent hazard. -/
def quittingTesterHazardFlow
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (hazard : ℕ → PMF Bool) : QuittingTesterFlow where
  live := fun time => quittingTesterOpponentSurvival roots who time *
    quittingHazardSurvival hazard time
  stop := fun time => quittingTesterOpponentSurvival roots who time *
    quittingHazardSurvival hazard time * (hazard time true).toReal
  carry := fun time => quittingTesterOpponentSurvival roots who time *
    quittingHazardSurvival hazard time * (hazard time false).toReal

theorem quittingTesterHazardFlow_isFeasible
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (hazard : ℕ → PMF Bool) :
    (quittingTesterHazardFlow roots who hazard).IsFeasible roots who := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [quittingTesterHazardFlow, quittingTesterOpponentSurvival,
      quittingOpponentSurvivalWeight]
  · intro time
    exact mul_nonneg
      (quittingOpponentSurvivalWeight_nonneg roots who 0 time)
      (quittingHazardSurvival_nonneg hazard time)
  · intro time
    exact mul_nonneg (mul_nonneg
      (quittingOpponentSurvivalWeight_nonneg roots who 0 time)
      (quittingHazardSurvival_nonneg hazard time)) ENNReal.toReal_nonneg
  · intro time
    exact mul_nonneg (mul_nonneg
      (quittingOpponentSurvivalWeight_nonneg roots who 0 time)
      (quittingHazardSurvival_nonneg hazard time)) ENNReal.toReal_nonneg
  · intro time
    have hsum : (hazard time true).toReal +
        (hazard time false).toReal = 1 := by
      simpa [Fintype.sum_bool] using pmf_toReal_sum_one (hazard time)
    simp only [quittingTesterHazardFlow]
    rw [← mul_add, hsum, mul_one]
  · intro time
    simp only [quittingTesterHazardFlow]
    unfold quittingTesterOpponentSurvival
    rw [quittingOpponentSurvivalWeight_succ,
      quittingHazardSurvival_succ]
    simp only [Nat.zero_add]
    unfold quittingTesterOpponentContinueMass
      quittingFixedOpponentsContinueMass quittingRootOpponentContinueMass
    ring

theorem QuittingTesterFlow.IsFeasible.stop_le_live
    {roots : ℕ → ι → PMF Bool} {who : ι} {flow : QuittingTesterFlow}
    (hflow : flow.IsFeasible roots who) (time : ℕ) :
    flow.stop time ≤ flow.live time := by
  rw [← hflow.2.2.2.2.1 time]
  exact le_add_of_nonneg_right (hflow.2.2.2.1 time)

/-- Conditional hazard obtained by dividing stop mass by live mass, with an
arbitrary Continue choice after extinction. -/
def quittingTesterFlowHazard
    {roots : ℕ → ι → PMF Bool} {who : ι} (flow : QuittingTesterFlow)
    (hflow : flow.IsFeasible roots who) (time : ℕ) : PMF Bool :=
  if hy : flow.live time = 0 then PMF.pure false
  else Math.ProbabilityMassFunction.bernoulliBool
    (flow.stop time / flow.live time)
    (div_nonneg (hflow.2.2.1 time) (hflow.2.1 time))
    ((div_le_one (lt_of_le_of_ne (hflow.2.1 time) (Ne.symm hy))).2
      (hflow.stop_le_live time))

theorem quittingTesterFlowHazard_true
    {roots : ℕ → ι → PMF Bool} {who : ι} {flow : QuittingTesterFlow}
    (hflow : flow.IsFeasible roots who) (time : ℕ) :
    (quittingTesterFlowHazard flow hflow time true).toReal =
      if flow.live time = 0 then 0 else
        flow.stop time / flow.live time := by
  by_cases hy : flow.live time = 0
  · simp [quittingTesterFlowHazard, hy]
  · simp [quittingTesterFlowHazard, hy]

theorem quittingTesterFlowHazard_false
    {roots : ℕ → ι → PMF Bool} {who : ι} {flow : QuittingTesterFlow}
    (hflow : flow.IsFeasible roots who) (time : ℕ) :
    (quittingTesterFlowHazard flow hflow time false).toReal =
      if flow.live time = 0 then 1 else
        flow.carry time / flow.live time := by
  by_cases hy : flow.live time = 0
  · simp [quittingTesterFlowHazard, hy]
  · simp only [if_neg hy]
    rw [quittingTesterFlowHazard, dif_neg hy,
      Math.ProbabilityMassFunction.bernoulliBool_false_toReal]
    have hsplit := hflow.2.2.2.2.1 time
    field_simp [hy]
    linarith

/-- Conditional hazards purify every feasible tester flow exactly, including
after zero live mass. -/
theorem quittingTesterHazardFlow_flowHazard
    {roots : ℕ → ι → PMF Bool} {who : ι} (flow : QuittingTesterFlow)
    (hflow : flow.IsFeasible roots who) :
    quittingTesterHazardFlow roots who
      (quittingTesterFlowHazard flow hflow) = flow := by
  have hlive : ∀ time,
      (quittingTesterHazardFlow roots who
        (quittingTesterFlowHazard flow hflow)).live time = flow.live time := by
    intro time
    induction time with
    | zero =>
        change 1 * 1 = flow.live 0
        simpa using hflow.1.symm
    | succ time ih =>
        rw [(quittingTesterHazardFlow_isFeasible roots who
          (quittingTesterFlowHazard flow hflow)).2.2.2.2.2 time,
          hflow.2.2.2.2.2 time]
        congr 1
        change
          (quittingTesterHazardFlow roots who
              (quittingTesterFlowHazard flow hflow)).live time *
                (quittingTesterFlowHazard flow hflow time false).toReal =
            flow.carry time
        rw [ih]
        rw [quittingTesterFlowHazard_false hflow time]
        by_cases hy : flow.live time = 0
        · have hk : flow.carry time = 0 := by
            have hsplit := hflow.2.2.2.2.1 time
            have hs0 := hflow.2.2.1 time
            have hk0 := hflow.2.2.2.1 time
            linarith
          simp [hy, hk]
        · simp only [if_neg hy]
          field_simp
  apply QuittingTesterFlow.ext
  · funext time
    exact hlive time
  · funext time
    change
      (quittingTesterHazardFlow roots who
          (quittingTesterFlowHazard flow hflow)).live time *
            (quittingTesterFlowHazard flow hflow time true).toReal =
        flow.stop time
    rw [hlive]
    rw [quittingTesterFlowHazard_true hflow time]
    by_cases hy : flow.live time = 0
    · have hs : flow.stop time = 0 := by
        have hsplit := hflow.2.2.2.2.1 time
        have hs0 := hflow.2.2.1 time
        have hk0 := hflow.2.2.2.1 time
        linarith
      simp [hy, hs]
    · simp only [if_neg hy]
      field_simp
  · funext time
    change
      (quittingTesterHazardFlow roots who
          (quittingTesterFlowHazard flow hflow)).live time *
            (quittingTesterFlowHazard flow hflow time false).toReal =
        flow.carry time
    rw [hlive]
    rw [quittingTesterFlowHazard_false hflow time]
    by_cases hy : flow.live time = 0
    · have hk : flow.carry time = 0 := by
        have hsplit := hflow.2.2.2.2.1 time
        have hs0 := hflow.2.2.1 time
        have hk0 := hflow.2.2.2.1 time
        linarith
      simp [hy, hk]
    · simp only [if_neg hy]
      field_simp

theorem quittingFiniteRootPayoff_eq_sum_testerTerms
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (hazard : ℕ → PMF Bool) : ∀ start fuel,
    quittingFiniteRootPayoff reward roots who hazard start fuel =
      ∑ offset ∈ Finset.range fuel,
        (quittingOpponentSurvivalWeight roots who start offset *
          quittingFiniteOwnContinueWeight hazard start offset) *
        ((hazard (start + offset) true).toReal *
            quittingTesterQuitValue reward (roots (start + offset)) who +
          (hazard (start + offset) false).toReal *
            quittingTesterContinueContribution reward
              (roots (start + offset)) who) := by
  intro start fuel
  rw [quittingFiniteRootPayoff_eq_hazardValue]
  induction fuel generalizing start with
  | zero => simp [quittingFiniteHazardValue]
  | succ fuel ih =>
      rw [quittingFiniteHazardValue, ih, Finset.sum_range_succ']
      have htail :
          (hazard start false).toReal *
              quittingFixedOpponentsContinueMass roots who start *
              (∑ offset ∈ Finset.range fuel,
                (quittingOpponentSurvivalWeight roots who (start + 1) offset *
                  quittingFiniteOwnContinueWeight hazard (start + 1) offset) *
                ((hazard ((start + 1) + offset) true).toReal *
                    quittingTesterQuitValue reward
                      (roots ((start + 1) + offset)) who +
                  (hazard ((start + 1) + offset) false).toReal *
                    quittingTesterContinueContribution reward
                      (roots ((start + 1) + offset)) who)) =
            ∑ offset ∈ Finset.range fuel,
              (quittingOpponentSurvivalWeight roots who start (offset + 1) *
                quittingFiniteOwnContinueWeight hazard start (offset + 1)) *
              ((hazard (start + (offset + 1)) true).toReal *
                  quittingTesterQuitValue reward
                    (roots (start + (offset + 1))) who +
                (hazard (start + (offset + 1)) false).toReal *
                  quittingTesterContinueContribution reward
                    (roots (start + (offset + 1))) who) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro offset _
        rw [quittingOpponentSurvivalWeight_succ_left]
        simp only [quittingFiniteOwnContinueWeight, Nat.add_assoc]
        ring
      rw [← htail]
      simp only [Nat.add_zero, quittingOpponentSurvivalWeight,
        quittingFiniteOwnContinueWeight]
      unfold quittingTesterQuitValue quittingTesterContinueContribution
      rw [quittingRootQuitPayoff_eq_fixedOpponentsQuitValue]
      rw [quittingRootContinuePayoff_eq_fixedOpponents]
      simp only [Pi.zero_apply, mul_zero, add_zero]
      ring

theorem quittingFiniteOwnContinueWeight_zero_eq_hazardSurvival
    (hazard : ℕ → PMF Bool) (time : ℕ) :
    quittingFiniteOwnContinueWeight hazard 0 time =
      quittingHazardSurvival hazard time := by
  rw [quittingFiniteOwnContinueWeight_eq_hazardWeight_last,
    quittingFiniteHazardWeight_last, quittingHazardSurvival_eq_prod]
  simp only [Nat.zero_add]

theorem quittingFiniteRootPayoff_eq_sum_hazardFlow
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (hazard : ℕ → PMF Bool) (cutoff : ℕ) :
    quittingFiniteRootPayoff reward roots who hazard 0 cutoff =
      ∑ time ∈ Finset.range cutoff,
        quittingTesterFlowPayoffTerm reward roots who
          (quittingTesterHazardFlow roots who hazard) time := by
  rw [quittingFiniteRootPayoff_eq_sum_testerTerms]
  apply Finset.sum_congr rfl
  intro time _
  rw [quittingFiniteOwnContinueWeight_zero_eq_hazardSurvival]
  simp only [Nat.zero_add, quittingTesterFlowPayoffTerm,
    quittingTesterHazardFlow]
  unfold quittingTesterOpponentSurvival
  ring

/-- The explicit flow series is exactly the terminal payoff of its inducing
calendar-dependent hazard. -/
theorem quittingTesterHazardFlow_payoff_eq_terminalValue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (hazard : ℕ → PMF Bool) :
    quittingTesterFlowPayoff reward roots who
        (quittingTesterHazardFlow roots who hazard) =
      quittingRootSequenceHazardTerminalValue reward roots who hazard 0 := by
  have hsum := QuittingTesterFlow.IsFeasible.summable_payoffTerm
    (quittingTesterHazardFlow_isFeasible roots who hazard) (reward := reward)
  have hflowLimit := hsum.hasSum.tendsto_sum_nat
  have hterminal := tendsto_quittingFiniteRootPayoff_terminal
    reward roots who hazard 0
  rw [show (fun cutoff => quittingFiniteRootPayoff reward roots who hazard 0 cutoff) =
      fun cutoff => ∑ time ∈ Finset.range cutoff,
        quittingTesterFlowPayoffTerm reward roots who
          (quittingTesterHazardFlow roots who hazard) time by
    funext cutoff
    exact quittingFiniteRootPayoff_eq_sum_hazardFlow
      reward roots who hazard cutoff] at hterminal
  unfold quittingRootSequenceHazardTerminalValue
    quittingRootSequenceTerminalValue
  exact tendsto_nhds_unique hflowLimit hterminal

/-- Tester flow of one deterministic finite stopping date, or of Never. -/
def quittingTesterPureTimeFlow
    (roots : ℕ → ι → PMF Bool) (who : ι) (quitTime : Option ℕ) :
    QuittingTesterFlow :=
  quittingTesterHazardFlow roots who (quittingPureTimeHazard quitTime)

theorem quittingTesterPureTimeFlow_isFeasible
    (roots : ℕ → ι → PMF Bool) (who : ι) (quitTime : Option ℕ) :
    (quittingTesterPureTimeFlow roots who quitTime).IsFeasible roots who :=
  quittingTesterHazardFlow_isFeasible roots who _

theorem quittingTesterPureTimeFlow_payoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (quitTime : Option ℕ) :
    quittingTesterFlowPayoff reward roots who
        (quittingTesterPureTimeFlow roots who quitTime) =
      quittingRootSequencePureTimeTerminalValue reward roots who quitTime 0 :=
  quittingTesterHazardFlow_payoff_eq_terminalValue reward roots who _

/-- Literal behavioral best-response value at every reached live suffix. -/
def quittingTesterTailBestResponseValue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (time : ℕ) : ℝ :=
  quittingContinuationBestResponseValue reward
    (quittingRootSequenceProfile reward roots time) who

/-- The literal suffix best-response values satisfy the exact Bellman
maximum recursion. -/
theorem quittingTesterTailBestResponseValue_eq_max
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (time : ℕ) :
    quittingTesterTailBestResponseValue reward roots who time =
      max (quittingTesterQuitValue reward (roots time) who)
        (quittingTesterContinueContribution reward (roots time) who +
          quittingTesterOpponentContinueMass (roots time) who *
            quittingTesterTailBestResponseValue reward roots who (time + 1)) := by
  unfold quittingTesterTailBestResponseValue
  rw [quittingRootSequenceProfile_eq_rootThenContinuation,
    quittingContinuationBestResponseValue_rootThenContinuation_eq_max]
  congr 1
  · rw [quittingRootQuitPayoff_eq_fixedOpponentsQuitValue]
    rfl
  · rw [quittingRootContinuePayoff_eq_fixedOpponents]
    unfold quittingTesterContinueContribution
    rw [quittingRootContinuePayoff_eq_fixedOpponents]
    simp only [Function.update_self, Pi.zero_apply, mul_zero, add_zero]
    rfl

theorem abs_quittingTesterTailBestResponseValue_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (time : ℕ) :
    |quittingTesterTailBestResponseValue reward roots who time| ≤
      quittingRewardBound reward := by
  exact abs_quittingContinuationBestResponseValue_le reward
    (quittingRootSequenceProfile reward roots time) who
    (abs_reward_le_quittingRewardBound reward)

theorem quittingRootSequencePureTimeTerminalValue_none_le_tailBestResponse
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (time : ℕ) :
    quittingRootSequencePureTimeTerminalValue reward roots who none time ≤
      quittingTesterTailBestResponseValue reward roots who time := by
  let profile := quittingRootSequenceProfile reward roots time
  have hbest := quittingTerminalPayoff_update_le_continuationBestResponseValue
    reward profile who (quittingPureTimeBehaviorStrategy reward who none)
  rw [quittingTerminalPayoff_update_pureTimeBehaviorStrategy] at hbest
  have hroot : quittingProfileLiveRoot reward profile =
      fun offset => roots (time + offset) := by
    dsimp [profile]
    rw [quittingRootSequenceProfile_eq_shift,
      quittingProfileLiveRoot_quittingRootSequenceProfile_zero]
  rw [hroot] at hbest
  have hupdate :
      quittingRootSequenceUpdate
        (fun suffix => roots (time + suffix)) who
          (quittingPureTimeHazard none) =
        (fun offset => quittingRootSequenceUpdate roots who
          (quittingPureTimeHazard none) (time + offset)) := by
    funext offset player
    by_cases hp : player = who
    · subst player
      simp [quittingRootSequenceUpdate]
    · simp [quittingRootSequenceUpdate, hp]
  unfold quittingRootSequencePureTimeTerminalValue
    quittingRootSequenceHazardTerminalValue at hbest ⊢
  rw [quittingRootSequenceTerminalValue_eq_shift]
  rw [hupdate] at hbest
  simpa [quittingTesterTailBestResponseValue, profile] using hbest

theorem tendsto_zero_quittingRootSequencePureTimeTerminalValue_none_of_positive
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (hpositive : 0 < quittingOpponentSurvivalLimit roots who 0) :
    Tendsto (fun time =>
      quittingRootSequencePureTimeTerminalValue reward roots who none time)
      Filter.atTop (nhds 0) := by
  let bound := quittingRewardBound reward
  have hratio := tendsto_quittingOpponentSurvivalLimitRatio_one roots who
    (quittingOpponentSurvivalLimit roots who 0)
    (tendsto_quittingOpponentSurvivalLimit roots who 0) hpositive
  have hmajor : Tendsto (fun time => bound *
      (1 - quittingOpponentSurvivalLimit roots who 0 /
        quittingOpponentSurvivalWeight roots who 0 time))
      Filter.atTop (nhds 0) := by
    have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) Filter.atTop (nhds 1) :=
      tendsto_const_nhds
    simpa using (hone.sub hratio).const_mul bound
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hdom : ∀ time,
      ‖quittingRootSequencePureTimeTerminalValue
        reward roots who none time‖ ≤ bound *
        (1 - quittingOpponentSurvivalLimit roots who 0 /
          quittingOpponentSurvivalWeight roots who 0 time) := by
    intro time
    have hbound := abs_quittingRootSequencePureTimeTerminalValue_none_le
      reward roots who time (abs_reward_le_quittingRewardBound reward)
    rw [quittingLiveMassLimit_opponentOnly_rootSequenceProfile_eq_ratio
      reward roots who time hpositive] at hbound
    simpa [Real.norm_eq_abs, bound] using hbound
  exact squeeze_zero (fun time => norm_nonneg _) hdom hmajor

/-- The literal suffix best-response values satisfy the exact deleted-clock
transversality condition, including the positive-survival branch. -/
theorem quittingTesterTailBestResponseValue_transversality
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) :
    0 ≤ Filter.liminf (fun time =>
      quittingTesterOpponentSurvival roots who time *
        quittingTesterTailBestResponseValue reward roots who time)
      Filter.atTop := by
  let limit := quittingOpponentSurvivalLimit roots who 0
  have hlimit : Tendsto (quittingTesterOpponentSurvival roots who)
      Filter.atTop (nhds limit) := by
    change Tendsto (quittingOpponentSurvivalWeight roots who 0)
      Filter.atTop (nhds (quittingOpponentSurvivalLimit roots who 0))
    exact tendsto_quittingOpponentSurvivalLimit roots who 0
  by_cases hzero : limit = 0
  · have hproduct : Tendsto (fun time =>
        quittingTesterOpponentSurvival roots who time *
          quittingTesterTailBestResponseValue reward roots who time)
        Filter.atTop (nhds 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      have hdom : ∀ time,
          ‖quittingTesterOpponentSurvival roots who time *
              quittingTesterTailBestResponseValue reward roots who time‖ ≤
            quittingTesterOpponentSurvival roots who time *
              quittingRewardBound reward := by
        intro time
        rw [Real.norm_eq_abs, abs_mul]
        unfold quittingTesterOpponentSurvival
        rw [abs_of_nonneg (quittingOpponentSurvivalWeight_nonneg
          roots who 0 time)]
        exact mul_le_mul_of_nonneg_left
          (abs_quittingTesterTailBestResponseValue_le
            reward roots who time)
          (quittingOpponentSurvivalWeight_nonneg roots who 0 time)
      have hmajor := hlimit.const_mul (quittingRewardBound reward)
      have hmajor' : Tendsto (fun time =>
          quittingTesterOpponentSurvival roots who time *
            quittingRewardBound reward) Filter.atTop (nhds 0) := by
        simpa [hzero, mul_comm] using hmajor
      exact squeeze_zero (fun time => norm_nonneg _) hdom hmajor'
    rw [hproduct.liminf_eq]
  · have hpositive : 0 < limit :=
      lt_of_le_of_ne (quittingOpponentSurvivalLimit_nonneg roots who 0)
        (Ne.symm hzero)
    let never := fun time =>
      quittingRootSequencePureTimeTerminalValue reward roots who none time
    have hnever : Tendsto never Filter.atTop (nhds 0) := by
      exact tendsto_zero_quittingRootSequencePureTimeTerminalValue_none_of_positive
        reward roots who hpositive
    have hneverProduct : Tendsto (fun time =>
        quittingTesterOpponentSurvival roots who time * never time)
        Filter.atTop (nhds 0) := by
      simpa using hlimit.mul hnever
    have hle : ∀ time,
        quittingTesterOpponentSurvival roots who time * never time ≤
          quittingTesterOpponentSurvival roots who time *
            quittingTesterTailBestResponseValue reward roots who time := by
      intro time
      exact mul_le_mul_of_nonneg_left
        (quittingRootSequencePureTimeTerminalValue_none_le_tailBestResponse
          reward roots who time)
        (quittingOpponentSurvivalWeight_nonneg roots who 0 time)
    have hneverLower : ∀ time, -quittingRewardBound reward ≤
        quittingTesterOpponentSurvival roots who time * never time := by
      intro time
      have hL0 := quittingOpponentSurvivalWeight_nonneg roots who 0 time
      have hL1 := quittingOpponentSurvivalWeight_le_one roots who 0 time
      have hn : |never time| ≤ quittingRewardBound reward := by
        simpa [never, quittingRootSequencePureTimeTerminalValue,
          quittingRootSequenceHazardTerminalValue,
          quittingRootSequenceTerminalValue] using
          (abs_quittingTerminalPayoff_le_quittingRewardBound reward
            (quittingRootSequenceProfile reward
              (quittingRootSequenceUpdate roots who
                (quittingPureTimeHazard none)) time) who)
      have hbound0 := quittingRewardBound_nonneg reward
      by_cases hn0 : 0 ≤ never time
      · exact (neg_nonpos.mpr hbound0).trans (mul_nonneg hL0 hn0)
      · have hmul : never time ≤
            quittingTesterOpponentSurvival roots who time * never time := by
          have := mul_le_mul_of_nonneg_right hL1
            (neg_nonneg.mpr (le_of_not_ge hn0))
          simpa [quittingTesterOpponentSurvival] using this
        exact (abs_le.mp hn).1.trans hmul
    have hcapUpper : ∀ time,
        quittingTesterOpponentSurvival roots who time *
            quittingTesterTailBestResponseValue reward roots who time ≤
          quittingRewardBound reward := by
      intro time
      have hL0 := quittingOpponentSurvivalWeight_nonneg roots who 0 time
      have hL1 := quittingOpponentSurvivalWeight_le_one roots who 0 time
      have hcap := abs_quittingTesterTailBestResponseValue_le
        reward roots who time
      by_cases hcap0 : 0 ≤ quittingTesterTailBestResponseValue
          reward roots who time
      · calc
          quittingTesterOpponentSurvival roots who time *
              quittingTesterTailBestResponseValue reward roots who time ≤
            1 * quittingTesterTailBestResponseValue reward roots who time :=
              mul_le_mul_of_nonneg_right hL1 hcap0
          _ ≤ quittingRewardBound reward := by
            simpa using (abs_le.mp hcap).2
      · exact (mul_nonpos_of_nonneg_of_nonpos hL0
          (le_of_not_ge hcap0)).trans (quittingRewardBound_nonneg reward)
    rw [← hneverProduct.liminf_eq]
    exact Filter.liminf_le_liminf (Filter.Eventually.of_forall hle)
      (Filter.isBoundedUnder_of_eventually_ge
        (Filter.Eventually.of_forall hneverLower))
      (Filter.isCoboundedUnder_ge_of_eventually_le Filter.atTop
        (Filter.Eventually.of_forall hcapUpper))

/-- The true suffix-cap sequence is a bounded feasible dual witness. -/
def quittingTesterTailBestResponseDual
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) :
    QuittingTesterBellmanDual reward roots who where
  value := quittingTesterTailBestResponseValue reward roots who
  bounded := ⟨quittingRewardBound reward,
    abs_quittingTesterTailBestResponseValue_le reward roots who⟩
  quit_le := fun time => by
    rw [quittingTesterTailBestResponseValue_eq_max]
    exact le_max_left _ _
  continue_le := fun time => by
    rw [quittingTesterTailBestResponseValue_eq_max
      reward roots who time]
    apply le_max_right
  transversality :=
    quittingTesterTailBestResponseValue_transversality reward roots who

/-- Supremum of explicit tester-flow payoffs. -/
def quittingTesterPrimalValue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) : ℝ :=
  sSup (Set.range fun flow :
    {flow : QuittingTesterFlow // flow.IsFeasible roots who} =>
      quittingTesterFlowPayoff reward roots who flow.1)

/-- Infimum of initial values of bounded transversal Bellman duals. -/
def quittingTesterDualValue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) : ℝ :=
  sInf (Set.range fun dual : QuittingTesterBellmanDual reward roots who =>
    dual.value 0)

theorem quittingTesterTailBestResponseValue_zero_eq_sSup_pureTime
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) :
    quittingTesterTailBestResponseValue reward roots who 0 =
      sSup (Set.range fun quitTime : Option ℕ =>
        quittingRootSequencePureTimeTerminalValue
          reward roots who quitTime 0) := by
  unfold quittingTesterTailBestResponseValue
    quittingContinuationBestResponseValue
  rw [sSup_range_quittingTerminalPayoff_update_eq_pureTime]
  apply congrArg sSup
  congr 1
  funext quitTime
  rw [quittingTerminalPayoff_update_pureTimeBehaviorStrategy,
    quittingProfileLiveRoot_quittingRootSequenceProfile_zero]

theorem quittingTesterPrimalValue_eq_tailBestResponse
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) :
    quittingTesterPrimalValue reward roots who =
      quittingTesterTailBestResponseValue reward roots who 0 := by
  let tailDual := quittingTesterTailBestResponseDual reward roots who
  let primalSet : Set ℝ := Set.range fun flow :
      {flow : QuittingTesterFlow // flow.IsFeasible roots who} =>
    quittingTesterFlowPayoff reward roots who flow.1
  have hprimalNonempty : primalSet.Nonempty := by
    refine ⟨quittingTesterFlowPayoff reward roots who
      (quittingTesterPureTimeFlow roots who none), ?_⟩
    exact ⟨⟨quittingTesterPureTimeFlow roots who none,
      quittingTesterPureTimeFlow_isFeasible roots who none⟩, rfl⟩
  have hprimalUpper : ∀ value ∈ primalSet,
      value ≤ quittingTesterTailBestResponseValue reward roots who 0 := by
    rintro value ⟨flow, rfl⟩
    exact quittingTesterFlowPayoff_le_dual flow.property tailDual
  have hprimalBound : BddAbove primalSet :=
    ⟨quittingTesterTailBestResponseValue reward roots who 0, hprimalUpper⟩
  apply le_antisymm
  · unfold quittingTesterPrimalValue
    exact csSup_le hprimalNonempty hprimalUpper
  · rw [quittingTesterTailBestResponseValue_zero_eq_sSup_pureTime]
    apply csSup_le
    · exact ⟨quittingRootSequencePureTimeTerminalValue
        reward roots who none 0, ⟨none, rfl⟩⟩
    · rintro value ⟨quitTime, rfl⟩
      change quittingRootSequencePureTimeTerminalValue
        reward roots who quitTime 0 ≤ _
      rw [← quittingTesterPureTimeFlow_payoff]
      unfold quittingTesterPrimalValue
      apply le_csSup hprimalBound
      exact ⟨⟨quittingTesterPureTimeFlow roots who quitTime,
        quittingTesterPureTimeFlow_isFeasible roots who quitTime⟩, rfl⟩

theorem quittingTesterDualValue_eq_tailBestResponse
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) :
    quittingTesterDualValue reward roots who =
      quittingTesterTailBestResponseValue reward roots who 0 := by
  let dualSet : Set ℝ := Set.range fun dual :
      QuittingTesterBellmanDual reward roots who => dual.value 0
  have hdualNonempty : dualSet.Nonempty := by
    exact ⟨(quittingTesterTailBestResponseDual reward roots who).value 0,
      ⟨quittingTesterTailBestResponseDual reward roots who, rfl⟩⟩
  have hdualLower : ∀ value ∈ dualSet,
      quittingTesterTailBestResponseValue reward roots who 0 ≤ value := by
    rintro value ⟨dual, rfl⟩
    rw [← quittingTesterPrimalValue_eq_tailBestResponse]
    unfold quittingTesterPrimalValue
    apply csSup_le
    · exact ⟨quittingTesterFlowPayoff reward roots who
        (quittingTesterPureTimeFlow roots who none),
          ⟨⟨quittingTesterPureTimeFlow roots who none,
            quittingTesterPureTimeFlow_isFeasible roots who none⟩, rfl⟩⟩
    · rintro payoff ⟨flow, rfl⟩
      exact quittingTesterFlowPayoff_le_dual flow.property dual
  have hdualBound : BddBelow dualSet :=
    ⟨quittingTesterTailBestResponseValue reward roots who 0, hdualLower⟩
  apply le_antisymm
  · unfold quittingTesterDualValue
    apply csInf_le hdualBound
    exact ⟨quittingTesterTailBestResponseDual reward roots who, rfl⟩
  · unfold quittingTesterDualValue
    exact le_csInf hdualNonempty hdualLower

/-- Exact tester-flow/Bellman strong duality.  The common value is the
literal all-behavior best-response cap; no maximizing flow or greedy policy
is asserted. -/
theorem quittingTester_primal_eq_dual_eq_behavioralCap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) :
    quittingTesterPrimalValue reward roots who =
        quittingTesterDualValue reward roots who ∧
      quittingTesterDualValue reward roots who =
        quittingContinuationBestResponseValue reward
          (quittingRootSequenceProfile reward roots 0) who := by
  constructor
  · rw [quittingTesterPrimalValue_eq_tailBestResponse,
      quittingTesterDualValue_eq_tailBestResponse]
  · rw [quittingTesterDualValue_eq_tailBestResponse]
    rfl

end GameTheory
