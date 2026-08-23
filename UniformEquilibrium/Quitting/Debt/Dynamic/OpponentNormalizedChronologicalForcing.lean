/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Debt.Dynamic.NashBellmanChronologicalForcing
import UniformEquilibrium.Quitting.Paths.HazardScaledResidualCompiler

/-!
# Opponent-absorption-normalized chronological forcing

An exact bounded policy-evaluation spine need not be a Nash spine.  Its
diagonal one-row semantic debt is the nonnegative pure-action Bellman gap.
If that gap is bounded by `eta` times opponent absorption at every row, the
generated cap secants telescope it on every suffix.  This gives both a
chronological debt-shadowing certificate and the existing direct
deleted-clock residual certificate, using the same literal roots.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability
open scoped BigOperators Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Diagonal semantic debt of one root against the next prescribed value. -/
def quittingDiagonalPrefixGap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (value : ℕ → Payoff ι) (roots : ℕ → ι → PMF Bool)
    (time : ℕ) (who : ι) : ℝ :=
  quittingTerminalSemanticDebt
    (quittingTerminalSemanticPrefix reward (roots time)
      (value (time + 1), value (time + 1))) who

/-- The diagonal prefix gap is exactly the standard one-step prescribed
residual when the current value obeys exact policy evaluation. -/
theorem quittingDiagonalPrefixGap_eq_prescribedOneStepResidual
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (value : ℕ → Payoff ι) (roots : ℕ → ι → PMF Bool)
    (hpolicy : ∀ time,
      value time = quittingRootSuccessorPayoff reward
        (value (time + 1)) (roots time))
    (time : ℕ) (who : ι) :
    quittingDiagonalPrefixGap reward value roots time who =
      quittingPrescribedOneStepResidual reward roots who
        (fun stage => value stage who) time := by
  unfold quittingDiagonalPrefixGap quittingTerminalSemanticDebt
    quittingTerminalSemanticPrefix quittingPrescribedOneStepResidual
    quittingLiveBellmanValue
  dsimp only
  rw [quittingRootQuitPayoff_eq_fixedOpponentsQuitValue
      reward roots who (value (time + 1)) time,
    quittingRootContinuePayoff_eq_fixedOpponents
      reward roots who (Function.update (value (time + 1)) who
        (value (time + 1) who)) time,
    Function.update_eq_self,
    ← congrFun (hpolicy time) who]

/-- Every diagonal prefix gap is nonnegative. -/
theorem quittingDiagonalPrefixGap_nonneg
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (value : ℕ → Payoff ι) (roots : ℕ → ι → PMF Bool)
    (hpolicy : ∀ time,
      value time = quittingRootSuccessorPayoff reward
        (value (time + 1)) (roots time))
    (time : ℕ) (who : ι) :
    0 ≤ quittingDiagonalPrefixGap reward value roots time who := by
  rw [quittingDiagonalPrefixGap_eq_prescribedOneStepResidual
    reward value roots hpolicy]
  apply quittingPrescribedOneStepResidual_nonneg
  intro stage
  exact congrFun (hpolicy stage) who

namespace QuittingChronologicalDebtData

/-- Exact policy evaluation alone kills the prescribed defect of diagonal
chronological data; no root-Nash hypothesis is needed. -/
@[simp] theorem ofNashBellmanSpine_prescribedDefect_of_policy
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (value : ℕ → Payoff ι) (roots : ℕ → ι → PMF Bool)
    (hpolicy : ∀ time,
      value time = quittingRootSuccessorPayoff reward
        (value (time + 1)) (roots time))
    (time : ℕ) :
    (ofNashBellmanSpine reward value roots).prescribedDefect reward time = 0 := by
  funext who
  unfold prescribedDefect
  rw [ofNashBellmanSpine_candidateSuccessorPair,
    ofNashBellmanSpine_root]
  change value time who -
    quittingRootSuccessorPayoff reward (value (time + 1))
      (roots time) who = 0
  rw [congrFun (hpolicy time) who]
  ring

/-- The direct-debt defect of diagonal chronological data is the negative
diagonal prefix gap. -/
@[simp] theorem ofNashBellmanSpine_directDebtDefect_eq_neg_gap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (value : ℕ → Payoff ι) (roots : ℕ → ι → PMF Bool)
    (time : ℕ) (who : ι) :
    (ofNashBellmanSpine reward value roots).directDebtDefect reward time who =
      -quittingDiagonalPrefixGap reward value roots time who := by
  unfold directDebtDefect quittingDiagonalPrefixGap
  rw [ofNashBellmanSpine_candidateSuccessorPair,
    ofNashBellmanSpine_root]
  simp [quittingTerminalSemanticDebt]

end QuittingChronologicalDebtData

/-- **Opponent-normalized chronological compiler.**  The normalized diagonal
gap pays every adverse direct-debt forcing suffix by an exact survival
telescope. -/
theorem nonempty_quittingChronologicalDebtShadowingCertificate_of_normalizedGap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (value : ℕ → Payoff ι) (roots : ℕ → ι → PMF Bool)
    (bound eta : ℝ) (heta : 0 < eta)
    (hbound : ∀ time who, |value time who| ≤ bound)
    (hpolicy : ∀ time,
      value time = quittingRootSuccessorPayoff reward
        (value (time + 1)) (roots time))
    (hnormalized : ∀ time who,
      quittingDiagonalPrefixGap reward value roots time who ≤
        eta * (1 - quittingRootOpponentContinueMass (roots time) who))
    (hjoint : ∀ start,
      Tendsto
        (Math.survivalProduct
          (fun time => quittingStationaryContinueMass (roots time)) start)
        atTop (nhds 0))
    (hopponent : ∀ who start,
      Tendsto
        (Math.survivalProduct
          (fun time => quittingRootOpponentContinueMass (roots time) who)
          start) atTop (nhds 0)) :
    Nonempty (QuittingChronologicalDebtShadowingCertificate reward eta) := by
  let data := QuittingChronologicalDebtData.ofNashBellmanSpine
    reward value roots
  refine ⟨{
    data := data
    eta_pos := heta
    debt_nonneg := by intro time who; simp [data]
    prescribed_bounded := ⟨bound, by
      intro time who
      simpa [data] using hbound time who⟩
    debt_bounded := ⟨0, by intro time who; simp [data]⟩
    secant_nonneg := by
      intro time who
      exact QuittingChronologicalDebtData.ofNashBellmanSpine_secant_nonneg
        reward value roots time who
    secant_le_opponentContinue := by
      intro time who
      exact
        QuittingChronologicalDebtData.ofNashBellmanSpine_secant_le_opponentContinue
          reward value roots time who
    secant_generated := by
      intro time who
      exact QuittingChronologicalDebtData.ofNashBellmanSpine_secant_generated
        reward value roots time who
    prescribed_discrepancy := ?_
    adverse_direct_forcing := ?_
    joint_survival := by intro start; simpa [data] using hjoint start
    opponent_survival := by
      intro who start
      simpa [data] using hopponent who start
    initial_debt_le := by intro who; simp [data, heta.le] }⟩
  · intro who start length
    have hzero : ∀ time, data.prescribedDefect reward time = 0 := by
      intro time
      exact
        QuittingChronologicalDebtData.ofNashBellmanSpine_prescribedDefect_of_policy
          reward value roots hpolicy time
    simp [hzero, heta.le]
  · intro who start slack hslack
    filter_upwards [] with length
    have hsec0 : ∀ time, 0 ≤ data.secant time who := fun time =>
      QuittingChronologicalDebtData.ofNashBellmanSpine_secant_nonneg
        reward value roots time who
    have hsecOpponent : ∀ time,
        data.secant time who ≤
          quittingRootOpponentContinueMass (roots time) who := fun time =>
      QuittingChronologicalDebtData.ofNashBellmanSpine_secant_le_opponentContinue
        reward value roots time who
    have hsec1 : ∀ time, data.secant time who ≤ 1 := fun time =>
      (hsecOpponent time).trans
        (quittingRootOpponentContinueMass_le_one (roots time) who)
    have hterm : ∀ offset ∈ Finset.range length,
        Math.survivalProduct (fun time => data.secant time who) start offset *
            quittingDiagonalPrefixGap reward value roots
              (start + offset) who ≤
          eta * (Math.survivalProduct
            (fun time => data.secant time who) start offset *
              (1 - data.secant (start + offset) who)) := by
      intro offset _
      let weight := Math.survivalProduct
        (fun time => data.secant time who) start offset
      have hweight0 : 0 ≤ weight :=
        Math.survivalProduct_nonneg _ hsec0 start offset
      have hgap := hnormalized (start + offset) who
      have habsorption :
          1 - quittingRootOpponentContinueMass
              (roots (start + offset)) who ≤
            1 - data.secant (start + offset) who :=
        sub_le_sub_left (hsecOpponent (start + offset)) 1
      have heta0 : 0 ≤ eta := heta.le
      calc
        weight * quittingDiagonalPrefixGap reward value roots
            (start + offset) who ≤
            weight * (eta * (1 - quittingRootOpponentContinueMass
              (roots (start + offset)) who)) :=
          mul_le_mul_of_nonneg_left hgap hweight0
        _ ≤ weight * (eta * (1 - data.secant (start + offset) who)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left habsorption heta0) hweight0
        _ = eta * (weight * (1 - data.secant
            (start + offset) who)) := by ring
    calc
      -∑ offset ∈ Finset.range length,
          Math.survivalProduct (fun time => data.secant time who) start offset *
            data.directDebtDefect reward (start + offset) who =
        ∑ offset ∈ Finset.range length,
          Math.survivalProduct (fun time => data.secant time who) start offset *
            quittingDiagonalPrefixGap reward value roots
              (start + offset) who := by
          simp [data,
            QuittingChronologicalDebtData.ofNashBellmanSpine_directDebtDefect_eq_neg_gap]
      _ ≤ ∑ offset ∈ Finset.range length,
          eta * (Math.survivalProduct
            (fun time => data.secant time who) start offset *
              (1 - data.secant (start + offset) who)) :=
        Finset.sum_le_sum hterm
      _ = eta * (1 - Math.survivalProduct
          (fun time => data.secant time who) start length) := by
        rw [← Finset.mul_sum,
          Math.sum_survivalProduct_mul_one_sub]
      _ ≤ eta := by
        have hsurvival0 := Math.survivalProduct_nonneg
          (fun time => data.secant time who) hsec0 start length
        nlinarith
      _ ≤ eta + slack := le_add_of_nonneg_right hslack.le

/-- Adapter to the already checked direct deleted-clock residual compiler.
This route needs only opponent survival, not joint survival. -/
def quittingInfinitePathHazardScaledResidualCertificate_of_normalizedGap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (value : ℕ → Payoff ι) (roots : ℕ → ι → PMF Bool)
    (bound eta : ℝ)
    (hbound : ∀ time who, |value time who| ≤ bound)
    (hpolicy : ∀ time,
      value time = quittingRootSuccessorPayoff reward
        (value (time + 1)) (roots time))
    (hnormalized : ∀ time who,
      quittingDiagonalPrefixGap reward value roots time who ≤
        eta * (1 - quittingRootOpponentContinueMass (roots time) who))
    (hopponent : ∀ who start,
      Tendsto (quittingOpponentSurvivalWeight roots who start)
        atTop (nhds 0)) :
    QuittingInfinitePathHazardScaledResidualCertificate
      reward (value 0) eta bound where
  roots := roots
  value := value
  value_zero := rfl
  survival := hopponent
  value_bound := hbound
  policy := hpolicy
  residual_le := by
    intro time who
    rw [← quittingDiagonalPrefixGap_eq_prescribedOneStepResidual
      reward value roots hpolicy]
    change quittingDiagonalPrefixGap reward value roots time who ≤
      eta * (1 - quittingRootOpponentContinueMass (roots time) who)
    exact hnormalized time who

/-- Direct all-behavior consumer for one normalized-gap spine. -/
theorem isAsymptoticNash_and_delivers_of_normalizedGap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (value : ℕ → Payoff ι) (roots : ℕ → ι → PMF Bool)
    (bound eta : ℝ)
    (hbound : ∀ time who, |value time who| ≤ bound)
    (hreward : ∀ terminal who, |reward terminal who| ≤ bound)
    (hpolicy : ∀ time,
      value time = quittingRootSuccessorPayoff reward
        (value (time + 1)) (roots time))
    (hnormalized : ∀ time who,
      quittingDiagonalPrefixGap reward value roots time who ≤
        eta * (1 - quittingRootOpponentContinueMass (roots time) who))
    (hopponent : ∀ who start,
      Tendsto (quittingOpponentSurvivalWeight roots who start)
        atTop (nhds 0)) :
    (quittingGame reward).IsεAsymptoticNash
        (quittingTerminalPayoff reward) eta
        (quittingInfinitePathProfile reward roots) ∧
      quittingTerminalPayoff reward
        (quittingInfinitePathProfile reward roots) = value 0 := by
  exact
    (quittingInfinitePathHazardScaledResidualCertificate_of_normalizedGap
      reward value roots bound eta hbound hpolicy hnormalized
        hopponent).isεAsymptoticNash_and_delivers reward (value 0) hreward

end GameTheory
