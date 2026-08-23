/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.Probability.SurvivalWeightedReachedHistoryAccount
import UniformEquilibrium.Quitting.Boundary.Exceptional.InfiniteLTG
import UniformEquilibrium.Quitting.Root.TerminalSemanticPair

/-!
# Opponent-Green account for literal terminal debt

A literal sequence of quitting roots has an actual behavioral continuation at
every live date.  Its terminal deviation debt is charged by the coordinate
Nash defect computed against that actual continuation payoff.  The remaining
debt is transported with the probability that every opponent Continues.

Iterating this one-step inequality gives a finite opponent-Green account.  A
uniform reward bound controls the terminal term, and vanishing opponent
survival removes it.  Local errors proportional to opponent absorption are
therefore paid once rather than once per live date.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Terminal deviation debt of the literal root-sequence tail starting at
`start`. -/
def quittingRootSequenceTerminalDebt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (start : ℕ) : ℝ :=
  quittingTerminalDeviationDebt reward
    (quittingRootSequenceProfile reward roots start) who

/-- Nash defect of the root at `time`, computed against the prescribed payoff
of the literal continuation beginning at `time + 1`. -/
def quittingRootSequenceActualCoordinateDefect
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (time : ℕ) : ℝ :=
  quittingRootCoordinateNashDefect reward
    (fun player ↦ quittingTerminalPayoff reward
      (quittingRootSequenceProfile reward roots (time + 1)) player)
    (roots time) who

/-- The generic reached-history weight at the shifted opponent-Continue
factors is the established opponent-survival weight. -/
theorem reachedHistoryWeight_opponentContinue_eq_quittingOpponentSurvivalWeight
    (roots : ℕ → ι → PMF Bool) (who : ι) (start : ℕ) :
    ∀ fuel,
      reachedHistoryWeight
          (fun offset ↦ quittingRootOpponentContinueMass
            (roots (start + offset)) who) fuel =
        quittingOpponentSurvivalWeight roots who start fuel := by
  intro fuel
  induction fuel with
  | zero => simp [quittingOpponentSurvivalWeight]
  | succ fuel ih =>
      rw [reachedHistoryWeight_succ, ih,
        quittingOpponentSurvivalWeight_succ]
      rfl

/-- Actual root-sequence debt obeys the one-step coordinate-defect account
with deleted-player survival. -/
theorem quittingRootSequenceTerminalDebt_le_actualCoordinateDefect_add
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (time : ℕ) :
    quittingRootSequenceTerminalDebt reward roots who time ≤
      quittingRootSequenceActualCoordinateDefect reward roots who time +
        quittingRootOpponentContinueMass (roots time) who *
          quittingRootSequenceTerminalDebt reward roots who (time + 1) := by
  rw [quittingRootSequenceTerminalDebt,
    quittingRootSequenceProfile_eq_rootThenContinuation]
  exact
    quittingTerminalDeviationDebt_rootThenContinuation_le_coordinateDefect_add
      reward (roots time)
        (quittingRootSequenceProfile reward roots (time + 1)) who

/-- Finite opponent-Green telescope for the actual terminal debts and actual
continuation-payoff coordinate defects of one literal root sequence. -/
theorem quittingRootSequenceTerminalDebt_le_opponentGreenDefectSum_add_tail
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (start fuel : ℕ) :
    quittingRootSequenceTerminalDebt reward roots who start ≤
      (∑ offset ∈ Finset.range fuel,
        quittingOpponentSurvivalWeight roots who start offset *
          quittingRootSequenceActualCoordinateDefect reward roots who
            (start + offset)) +
      quittingOpponentSurvivalWeight roots who start fuel *
        quittingRootSequenceTerminalDebt reward roots who (start + fuel) := by
  let survival : ℕ → ℝ := fun offset ↦
    quittingRootOpponentContinueMass (roots (start + offset)) who
  let defect : ℕ → ℝ := fun offset ↦
    quittingRootSequenceActualCoordinateDefect reward roots who (start + offset)
  let debt : ℕ → ℝ := fun offset ↦
    quittingRootSequenceTerminalDebt reward roots who (start + offset)
  have haccount : ∀ offset,
      debt offset ≤ defect offset + 0 + survival offset * debt (offset + 1) := by
    intro offset
    dsimp [debt, defect, survival]
    simpa only [add_zero, Nat.add_assoc] using
      quittingRootSequenceTerminalDebt_le_actualCoordinateDefect_add
        reward roots who (start + offset)
  have htelescope :=
    debt_zero_le_sum_reachedHistoryWeight_mul_defectError_add
      survival defect (fun _ ↦ 0) debt haccount
      (fun offset ↦ quittingRootOpponentContinueMass_nonneg
        (roots (start + offset)) who) fuel
  have hweight : ∀ offset,
      reachedHistoryWeight survival offset =
        quittingOpponentSurvivalWeight roots who start offset := by
    exact
      reachedHistoryWeight_opponentContinue_eq_quittingOpponentSurvivalWeight
        roots who start
  simpa only [debt, defect, hweight, add_zero, mul_zero] using htelescope

/-- A uniform terminal-reward bound bounds every literal terminal deviation
debt by twice that reward bound. -/
theorem quittingRootSequenceTerminalDebt_le_two_mul
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (start : ℕ)
    (M : ℝ) (hreward : ∀ terminal player, |reward terminal player| ≤ M) :
    quittingRootSequenceTerminalDebt reward roots who start ≤ 2 * M := by
  have hbest := abs_quittingContinuationBestResponseValue_le reward
    (quittingRootSequenceProfile reward roots start) who hreward
  have hpayoff := abs_quittingTerminalPayoff_le reward
    (quittingRootSequenceProfile reward roots start) who hreward
  unfold quittingRootSequenceTerminalDebt quittingTerminalDeviationDebt
  linarith [le_of_abs_le hbest, neg_le_of_abs_le hpayoff]

/-- Finite opponent-Green account with the terminal debt replaced by its
uniform reward bound. -/
theorem quittingRootSequenceTerminalDebt_le_opponentGreenDefectSum_add_boundedTail
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (start fuel : ℕ) (M : ℝ)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M) :
    quittingRootSequenceTerminalDebt reward roots who start ≤
      (∑ offset ∈ Finset.range fuel,
        quittingOpponentSurvivalWeight roots who start offset *
          quittingRootSequenceActualCoordinateDefect reward roots who
            (start + offset)) +
      2 * M * quittingOpponentSurvivalWeight roots who start fuel := by
  have hfinite :=
    quittingRootSequenceTerminalDebt_le_opponentGreenDefectSum_add_tail
      reward roots who start fuel
  have htail := mul_le_mul_of_nonneg_left
    (quittingRootSequenceTerminalDebt_le_two_mul
      reward roots who (start + fuel) M hreward)
    (quittingOpponentSurvivalWeight_nonneg roots who start fuel)
  linarith

/-- Under vanishing opponent survival, every positive tolerance is achieved
by one finite opponent-Green partial sum. -/
theorem quittingRootSequenceTerminalDebt_le_opponentGreenDefectSum_add_epsilon
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (start : ℕ)
    (M : ℝ) (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hgreen : Tendsto (quittingOpponentSurvivalWeight roots who start)
      atTop (nhds 0)) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ fuel,
      quittingRootSequenceTerminalDebt reward roots who start ≤
        (∑ offset ∈ Finset.range fuel,
          quittingOpponentSurvivalWeight roots who start offset *
            quittingRootSequenceActualCoordinateDefect reward roots who
              (start + offset)) + epsilon := by
  have htail : Tendsto (fun fuel ↦
      2 * M * quittingOpponentSurvivalWeight roots who start fuel)
      atTop (nhds 0) := by
    simpa only [mul_zero] using hgreen.const_mul (2 * M)
  have heventually : ∀ᶠ fuel in atTop,
      2 * M * quittingOpponentSurvivalWeight roots who start fuel < epsilon :=
    (tendsto_order.1 htail).2 epsilon hepsilon
  obtain ⟨threshold, hthreshold⟩ := eventually_atTop.1 heventually
  refine ⟨threshold, ?_⟩
  have hfinite :=
    quittingRootSequenceTerminalDebt_le_opponentGreenDefectSum_add_boundedTail
      reward roots who start threshold M hreward
  linarith [hthreshold threshold le_rfl]

/-- If the finite opponent-Green defect sums are bounded above, vanishing
opponent survival bounds the initial debt by their real supremum. -/
theorem quittingRootSequenceTerminalDebt_le_csSup_opponentGreenDefectSum
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (start : ℕ)
    (M : ℝ) (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hgreen : Tendsto (quittingOpponentSurvivalWeight roots who start)
      atTop (nhds 0))
    (hbounded : BddAbove (Set.range fun fuel ↦
      ∑ offset ∈ Finset.range fuel,
        quittingOpponentSurvivalWeight roots who start offset *
          quittingRootSequenceActualCoordinateDefect reward roots who
            (start + offset))) :
    quittingRootSequenceTerminalDebt reward roots who start ≤
      sSup (Set.range fun fuel ↦
        ∑ offset ∈ Finset.range fuel,
          quittingOpponentSurvivalWeight roots who start offset *
            quittingRootSequenceActualCoordinateDefect reward roots who
              (start + offset)) := by
  apply le_of_forall_pos_le_add
  intro epsilon hepsilon
  obtain ⟨fuel, hfuel⟩ :=
    quittingRootSequenceTerminalDebt_le_opponentGreenDefectSum_add_epsilon
      reward roots who start M hreward hgreen hepsilon
  have hpartial :
      (∑ offset ∈ Finset.range fuel,
        quittingOpponentSurvivalWeight roots who start offset *
          quittingRootSequenceActualCoordinateDefect reward roots who
            (start + offset)) ≤
        sSup (Set.range fun length ↦
          ∑ offset ∈ Finset.range length,
            quittingOpponentSurvivalWeight roots who start offset *
              quittingRootSequenceActualCoordinateDefect reward roots who
                (start + offset)) :=
    le_csSup hbounded ⟨fuel, rfl⟩
  linarith

/-- Extended-real interpretation without a boundedness premise: either the
finite Green sums are unbounded, or their real supremum bounds the debt. -/
theorem quittingRootSequenceTerminalDebt_greenDefectSum_unbounded_or_le_csSup
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (start : ℕ)
    (M : ℝ) (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hgreen : Tendsto (quittingOpponentSurvivalWeight roots who start)
      atTop (nhds 0)) :
    ¬ BddAbove (Set.range fun fuel ↦
        ∑ offset ∈ Finset.range fuel,
          quittingOpponentSurvivalWeight roots who start offset *
            quittingRootSequenceActualCoordinateDefect reward roots who
              (start + offset)) ∨
      quittingRootSequenceTerminalDebt reward roots who start ≤
        sSup (Set.range fun fuel ↦
          ∑ offset ∈ Finset.range fuel,
            quittingOpponentSurvivalWeight roots who start offset *
              quittingRootSequenceActualCoordinateDefect reward roots who
                (start + offset)) := by
  by_cases hbounded : BddAbove (Set.range fun fuel ↦
      ∑ offset ∈ Finset.range fuel,
        quittingOpponentSurvivalWeight roots who start offset *
          quittingRootSequenceActualCoordinateDefect reward roots who
            (start + offset))
  · right
    exact quittingRootSequenceTerminalDebt_le_csSup_opponentGreenDefectSum
      reward roots who start M hreward hgreen hbounded
  · exact Or.inl hbounded

/-- Finite paid-hazard form of the opponent-Green account.  The varying local
rate is bounded by `etaBound`; the residual `remainder` remains Green-weighted. -/
theorem quittingRootSequenceTerminalDebt_le_paidHazard_add_tail
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (eta remainder : ℕ → ℝ) (etaBound : ℝ) (start fuel : ℕ)
    (heta : ∀ time, eta time ≤ etaBound)
    (hdefect : ∀ time,
      quittingRootSequenceActualCoordinateDefect reward roots who time ≤
        eta time *
            (1 - quittingRootOpponentContinueMass (roots time) who) +
          remainder time) :
    quittingRootSequenceTerminalDebt reward roots who start ≤
      etaBound *
          (1 - quittingOpponentSurvivalWeight roots who start fuel) +
        (∑ offset ∈ Finset.range fuel,
          quittingOpponentSurvivalWeight roots who start offset *
            remainder (start + offset)) +
        quittingOpponentSurvivalWeight roots who start fuel *
          quittingRootSequenceTerminalDebt reward roots who (start + fuel) := by
  have hfinite :=
    quittingRootSequenceTerminalDebt_le_opponentGreenDefectSum_add_tail
      reward roots who start fuel
  have hterm (offset : ℕ) :
      quittingOpponentSurvivalWeight roots who start offset *
          quittingRootSequenceActualCoordinateDefect reward roots who
            (start + offset) ≤
        etaBound *
            (quittingOpponentSurvivalWeight roots who start offset *
              (1 - quittingRootOpponentContinueMass
                (roots (start + offset)) who)) +
          quittingOpponentSurvivalWeight roots who start offset *
            remainder (start + offset) := by
    have hweight := quittingOpponentSurvivalWeight_nonneg
      roots who start offset
    have hdefectScaled := mul_le_mul_of_nonneg_left
      (hdefect (start + offset)) hweight
    have hhazard : 0 ≤
        quittingOpponentSurvivalWeight roots who start offset *
          (1 - quittingRootOpponentContinueMass
            (roots (start + offset)) who) :=
      mul_nonneg hweight (sub_nonneg.mpr
        (quittingRootOpponentContinueMass_le_one _ _))
    have hetaScaled := mul_le_mul_of_nonneg_right
      (heta (start + offset)) hhazard
    linarith
  have hsum :
      (∑ offset ∈ Finset.range fuel,
        quittingOpponentSurvivalWeight roots who start offset *
          quittingRootSequenceActualCoordinateDefect reward roots who
            (start + offset)) ≤
        (∑ offset ∈ Finset.range fuel,
          (etaBound *
              (quittingOpponentSurvivalWeight roots who start offset *
                (1 - quittingRootOpponentContinueMass
                  (roots (start + offset)) who)) +
            quittingOpponentSurvivalWeight roots who start offset *
              remainder (start + offset))) := by
    exact Finset.sum_le_sum fun offset _ ↦ hterm offset
  have hhazard :
      (∑ offset ∈ Finset.range fuel,
        quittingOpponentSurvivalWeight roots who start offset *
          (1 - quittingRootOpponentContinueMass
            (roots (start + offset)) who)) =
        1 - quittingOpponentSurvivalWeight roots who start fuel := by
    simpa only [quittingFixedOpponentsContinueMass,
      quittingRootOpponentContinueMass] using
      sum_quittingOpponentSurvivalWeight_mul_one_sub_continueMass
        roots who start fuel
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, hhazard] at hsum
  linarith

/-- With bounded rewards, the finite paid-hazard account has the explicit
terminal error `2 * M` times opponent survival. -/
theorem quittingRootSequenceTerminalDebt_le_paidHazard_add_boundedTail
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (eta remainder : ℕ → ℝ) (etaBound : ℝ) (start fuel : ℕ)
    (M : ℝ) (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (heta : ∀ time, eta time ≤ etaBound)
    (hdefect : ∀ time,
      quittingRootSequenceActualCoordinateDefect reward roots who time ≤
        eta time *
            (1 - quittingRootOpponentContinueMass (roots time) who) +
          remainder time) :
    quittingRootSequenceTerminalDebt reward roots who start ≤
      etaBound *
          (1 - quittingOpponentSurvivalWeight roots who start fuel) +
        (∑ offset ∈ Finset.range fuel,
          quittingOpponentSurvivalWeight roots who start offset *
            remainder (start + offset)) +
        2 * M * quittingOpponentSurvivalWeight roots who start fuel := by
  have hfinite := quittingRootSequenceTerminalDebt_le_paidHazard_add_tail
    reward roots who eta remainder etaBound start fuel heta hdefect
  have htail := mul_le_mul_of_nonneg_left
    (quittingRootSequenceTerminalDebt_le_two_mul
      reward roots who (start + fuel) M hreward)
    (quittingOpponentSurvivalWeight_nonneg roots who start fuel)
  linarith

/-- Infinite paid-hazard corollary.  Vanishing opponent survival removes the
bounded tail; a bounded family of residual Green sums contributes only its
supremum. -/
theorem quittingRootSequenceTerminalDebt_le_etaBound_add_csSup_remainder
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (eta remainder : ℕ → ℝ) (etaBound : ℝ) (start : ℕ)
    (M : ℝ) (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hetaBound : 0 ≤ etaBound) (heta : ∀ time, eta time ≤ etaBound)
    (hdefect : ∀ time,
      quittingRootSequenceActualCoordinateDefect reward roots who time ≤
        eta time *
            (1 - quittingRootOpponentContinueMass (roots time) who) +
          remainder time)
    (hgreen : Tendsto (quittingOpponentSurvivalWeight roots who start)
      atTop (nhds 0))
    (hbounded : BddAbove (Set.range fun fuel ↦
      ∑ offset ∈ Finset.range fuel,
        quittingOpponentSurvivalWeight roots who start offset *
          remainder (start + offset))) :
    quittingRootSequenceTerminalDebt reward roots who start ≤
      etaBound + sSup (Set.range fun fuel ↦
        ∑ offset ∈ Finset.range fuel,
          quittingOpponentSurvivalWeight roots who start offset *
            remainder (start + offset)) := by
  apply le_of_forall_pos_le_add
  intro epsilon hepsilon
  have htail : Tendsto (fun fuel ↦
      2 * M * quittingOpponentSurvivalWeight roots who start fuel)
      atTop (nhds 0) := by
    simpa only [mul_zero] using hgreen.const_mul (2 * M)
  have heventually : ∀ᶠ fuel in atTop,
      2 * M * quittingOpponentSurvivalWeight roots who start fuel < epsilon :=
    (tendsto_order.1 htail).2 epsilon hepsilon
  obtain ⟨fuel, hfuel⟩ := eventually_atTop.1 heventually
  have hfinite := quittingRootSequenceTerminalDebt_le_paidHazard_add_boundedTail
    reward roots who eta remainder etaBound start fuel M hreward heta hdefect
  have hweight := quittingOpponentSurvivalWeight_nonneg roots who start fuel
  have hetaTerm : etaBound *
      (1 - quittingOpponentSurvivalWeight roots who start fuel) ≤ etaBound := by
    nlinarith
  have hpartial :
      (∑ offset ∈ Finset.range fuel,
        quittingOpponentSurvivalWeight roots who start offset *
          remainder (start + offset)) ≤
        sSup (Set.range fun length ↦
          ∑ offset ∈ Finset.range length,
            quittingOpponentSurvivalWeight roots who start offset *
              remainder (start + offset)) :=
    le_csSup hbounded ⟨fuel, rfl⟩
  linarith [hfuel fuel le_rfl]

/-- Unconditional extended interpretation of the paid-hazard conclusion:
either the residual Green sums are unbounded, or their real supremum plus the
hazard budget bounds the debt. -/
theorem quittingRootSequenceTerminalDebt_remainderSum_unbounded_or_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (eta remainder : ℕ → ℝ) (etaBound : ℝ) (start : ℕ)
    (M : ℝ) (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hetaBound : 0 ≤ etaBound) (heta : ∀ time, eta time ≤ etaBound)
    (hdefect : ∀ time,
      quittingRootSequenceActualCoordinateDefect reward roots who time ≤
        eta time *
            (1 - quittingRootOpponentContinueMass (roots time) who) +
          remainder time)
    (hgreen : Tendsto (quittingOpponentSurvivalWeight roots who start)
      atTop (nhds 0)) :
    ¬ BddAbove (Set.range fun fuel ↦
        ∑ offset ∈ Finset.range fuel,
          quittingOpponentSurvivalWeight roots who start offset *
            remainder (start + offset)) ∨
      quittingRootSequenceTerminalDebt reward roots who start ≤
        etaBound + sSup (Set.range fun fuel ↦
          ∑ offset ∈ Finset.range fuel,
            quittingOpponentSurvivalWeight roots who start offset *
              remainder (start + offset)) := by
  by_cases hbounded : BddAbove (Set.range fun fuel ↦
      ∑ offset ∈ Finset.range fuel,
        quittingOpponentSurvivalWeight roots who start offset *
          remainder (start + offset))
  · right
    exact quittingRootSequenceTerminalDebt_le_etaBound_add_csSup_remainder
      reward roots who eta remainder etaBound start M hreward hetaBound heta
        hdefect hgreen hbounded
  · exact Or.inl hbounded

end GameTheory
