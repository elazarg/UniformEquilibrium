/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Debt.Dynamic.DynamicDebtCapBridge
import UniformEquilibrium.Quitting.Debt.Dynamic.PunishmentFloorViolation

/-!
# Positive-debt self-loop limits of exact dynamic-debt tails

Summable absorption controls coordinatewise value variation along a boxed
exact-debt tail, while exact debt is monotone and bounded. A positive-debt
all-Continue self-loop limit dominates its singleton reward and behavioral
punishment floor on every positive-debt coordinate.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

namespace QuittingDynamicDebtTail

variable (tail : ℕ → QuittingDebtPoint ι)

/-- One-stage prescribed-value motion is controlled by joint absorption. -/
theorem abs_value_succ_sub_le_two_mul_absorptionMass
    (hvalueBound : ∀ time who,
      |(tail time).1.1 who| ≤ quittingRewardBound reward)
    (hedge : ∀ time,
      IsQuittingDynamicDebtEdge reward (tail time) (tail (time + 1)))
    (time : ℕ) (who : ι) :
    |(tail (time + 1)).1.1 who - (tail time).1.1 who| ≤
      2 * quittingRewardBound reward *
        quittingDynamicDebtTailAbsorptionCharge tail time := by
  rw [congrFun (hedge time).1.1 who]
  simpa [abs_sub_comm, quittingDynamicDebtTailAbsorptionCharge,
      quittingDynamicDebtTailRoots] using
    (abs_quittingRootSuccessorPayoff_sub_tail_le_two_mul_absorptionMass
      reward (tail (time + 1)).1.1
        (quittingDynamicDebtTailRoots tail time) who
        (quittingRewardBound reward)
        (abs_reward_le_quittingRewardBound reward)
        (hvalueBound (time + 1) who))

/-- Summable absorption makes every prescribed-value coordinate have
summable absolute increments. -/
theorem summable_abs_value_succ_sub
    (hvalueBound : ∀ time who,
      |(tail time).1.1 who| ≤ quittingRewardBound reward)
    (hedge : ∀ time,
      IsQuittingDynamicDebtEdge reward (tail time) (tail (time + 1)))
    (hsummable : Summable (quittingDynamicDebtTailAbsorptionCharge tail))
    (who : ι) :
    Summable (fun time ↦
      |(tail (time + 1)).1.1 who - (tail time).1.1 who|) :=
  Summable.of_nonneg_of_le (fun _ ↦ abs_nonneg _)
    (fun time ↦
      QuittingDynamicDebtTail.abs_value_succ_sub_le_two_mul_absorptionMass
        tail hvalueBound hedge time who)
    (hsummable.mul_left (2 * quittingRewardBound reward))

/-- Exact dynamic debt is monotone in chronological time. -/
theorem monotone_debt
    (hdebtNonneg : ∀ time, 0 ≤ (tail time).2)
    (hedge : ∀ time,
      IsQuittingDynamicDebtEdge reward (tail time) (tail (time + 1)))
    (who : ι) :
    Monotone (fun time ↦ (tail time).2 who) := by
  apply monotone_nat_of_le_succ
  intro time
  rw [(hedge time).2 who]
  exact quittingDynamicDebtUpdate_le_successor
    reward (tail time) (tail (time + 1)) (hedge time).1
      (hdebtNonneg (time + 1)) who

omit [DecidableEq ι] in
/-- Every debt coordinate is bounded above by its positive singleton cap. -/
theorem bddAbove_range_debt
    (hdebtCap : ∀ time,
      (tail time).2 ≤ quittingPositiveSingletonDebtCap reward)
    (who : ι) :
    BddAbove (Set.range fun time ↦ (tail time).2 who) := by
  refine ⟨quittingPositiveSingletonDebtCap reward who, ?_⟩
  rintro _ ⟨time, rfl⟩
  exact hdebtCap time who

/-- Pure Quit gives a solo-reward lower estimate controlled by opponent
absorption. -/
theorem soloReward_sub_opponentHazard_le_value
    (hedge : ∀ time,
      IsQuittingDynamicDebtEdge reward (tail time) (tail (time + 1)))
    (time : ℕ) (who : ι) :
    quittingSoloReward reward who who -
        2 * quittingRewardBound reward *
          quittingRootOpponentAbsorptionMass
            (quittingDynamicDebtTailRoots tail time) who ≤
      (tail time).1.1 who := by
  have hest :=
    abs_quittingRootQuitPayoff_sub_singletonReward_le_two_mul_opponentAbsorptionMass
      reward (tail (time + 1)).1.1
        (quittingDynamicDebtTailRoots tail time) who
        (quittingRewardBound reward)
        (abs_reward_le_quittingRewardBound reward)
  have hnash : IsεQuittingRootNash reward (tail (time + 1)).1.1 0
      (quittingDynamicDebtTailRoots tail time) :=
    (isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash
      reward (tail (time + 1)).1.1
        (quittingDynamicDebtTailRoots tail time)).1 (hedge time).1.2
  have hquit := quittingRootQuitPayoff_le_successor_of_isZeroNash
    reward (tail (time + 1)).1.1
      (quittingDynamicDebtTailRoots tail time) who hnash
  have hcurrent := congrFun (hedge time).1.1 who
  have hpair := abs_le.mp hest
  simp only [quittingDynamicDebtTailRoots] at hquit hpair
  rw [← hcurrent] at hquit
  have hsolo : quittingSoloReward reward who who =
      reward (quittingSingletonTerminal who) who := rfl
  rw [hsolo]
  simp only [quittingDynamicDebtTailRoots]
  linarith [hpair.1, hcurrent]

end QuittingDynamicDebtTail

/-- A positive-debt all-Continue boundary state selected from an exact tail. -/
structure QuittingPositiveDebtSelfLoopLimit
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) where
  value : Payoff ι
  debt : Payoff ι
  owner : ι
  ownerDebt_pos : 0 < debt owner
  state_mem :
    (((value, quittingAllContinueSimplexRoot), debt) : QuittingDebtPoint ι) ∈
      quittingDebtBox reward
  exactSelfLoop :
    IsQuittingDynamicDebtEdge reward
      ((value, quittingAllContinueSimplexRoot), debt)
      ((value, quittingAllContinueSimplexRoot), debt)

namespace QuittingPositiveDebtSelfLoopLimit

/-- Positive limiting debt is bounded by the corresponding strictly positive
own singleton reward. -/
theorem debt_le_soloReward_of_debt_pos
    (limit : QuittingPositiveDebtSelfLoopLimit reward) (who : ι)
    (hdebtPos : 0 < limit.debt who) :
    limit.debt who ≤ reward (quittingSingletonTerminal who) who := by
  have hdebtCap := limit.state_mem.2.2 who
  unfold quittingPositiveSingletonDebtCap at hdebtCap
  rcases lt_max_iff.mp (lt_of_lt_of_le hdebtPos hdebtCap) with
    hzero | hsolo
  · exact (lt_irrefl 0 hzero).elim
  · simpa [max_eq_right hsolo.le] using hdebtCap

/-- Every own singleton reward is dominated by its prescribed self-loop
value. -/
theorem soloReward_le_value
    (limit : QuittingPositiveDebtSelfLoopLimit reward) (who : ι) :
    reward (quittingSingletonTerminal who) who ≤ limit.value who := by
  have hquit :=
    quittingRootQuitPayoff_le_currentValue_of_nashBellmanEdge
      reward (limit.value, quittingAllContinueSimplexRoot)
        (limit.value, quittingAllContinueSimplexRoot)
        limit.exactSelfLoop.1 who
  simpa [quittingRootOfSimplex_allContinueSimplexRoot] using hquit

/-- Positive limiting debt is no larger than its prescribed value. -/
theorem debt_le_value_of_debt_pos
    (limit : QuittingPositiveDebtSelfLoopLimit reward) (who : ι)
    (hdebtPos : 0 < limit.debt who) :
    limit.debt who ≤ limit.value who :=
  (limit.debt_le_soloReward_of_debt_pos who hdebtPos).trans
    (limit.soloReward_le_value who)

/-- Every positive-debt coordinate lies above its behavioral punishment floor
at the self-loop. -/
theorem punishmentValue_le_value_of_debt_pos
    (limit : QuittingPositiveDebtSelfLoopLimit reward) (who : ι)
    (hdebtPos : 0 < limit.debt who) :
    quittingPunishmentValue reward who ≤ limit.value who := by
  have hsoloPos : 0 < reward (quittingSingletonTerminal who) who :=
    hdebtPos.trans_le (limit.debt_le_soloReward_of_debt_pos who hdebtPos)
  have hsoloLe := limit.soloReward_le_value who
  have hpunishment := quittingPunishmentValue_le_max_solo reward who
  rw [QuittingSureSetOwnerRepair.quittingSetReward_of_nonempty reward
    (Finset.singleton_nonempty who) who] at hpunishment
  change quittingPunishmentValue reward who ≤
    max (reward (quittingSingletonTerminal who) who) 0 at hpunishment
  rw [max_eq_left hsoloPos.le] at hpunishment
  exact hpunishment.trans hsoloLe

/-- The marked positive-debt coordinate lies above its punishment floor. -/
theorem punishmentValue_le_ownerValue
    (limit : QuittingPositiveDebtSelfLoopLimit reward) :
    quittingPunishmentValue reward limit.owner ≤ limit.value limit.owner :=
  limit.punishmentValue_le_value_of_debt_pos
    limit.owner limit.ownerDebt_pos

/-- If a boxed exact-debt tail converges to the supplied self-loop in value
and debt, then every positive-debt coordinate is already floor-safe at every
finite date. -/
theorem punishmentValue_le_tailValue_of_debt_pos
    (limit : QuittingPositiveDebtSelfLoopLimit reward)
    (tail : ℕ → QuittingDebtPoint ι)
    (hdebtNonneg : ∀ time, 0 ≤ (tail time).2)
    (hedge : ∀ time,
      IsQuittingDynamicDebtEdge reward (tail time) (tail (time + 1)))
    (hvalue : ∀ who, Tendsto (fun time ↦ (tail time).1.1 who) atTop
      (nhds (limit.value who)))
    (hdebt : ∀ who, Tendsto (fun time ↦ (tail time).2 who) atTop
      (nhds (limit.debt who)))
    (who : ι) (time : ℕ) (hdebtPos : 0 < (tail time).2 who) :
    quittingPunishmentValue reward who ≤ (tail time).1.1 who := by
  by_contra hnot
  push Not at hnot
  have hdebtMono := QuittingDynamicDebtTail.monotone_debt
    tail hdebtNonneg hedge who
  have hlimitDebt : (tail time).2 who ≤ limit.debt who := by
    apply ge_of_tendsto (hdebt who)
    filter_upwards [eventually_ge_atTop time] with later hlater
    exact hdebtMono hlater
  have hlimitDebtPos : 0 < limit.debt who :=
    hdebtPos.trans_le hlimitDebt
  have hlimitFloor :=
    limit.punishmentValue_le_value_of_debt_pos who hlimitDebtPos
  have hlimitValueLe : limit.value who ≤ (tail time).1.1 who := by
    apply le_of_tendsto (hvalue who)
    filter_upwards [eventually_ge_atTop time] with later hlater
    have hgap := quittingDynamicDebtTail_punishmentGap_mono
      tail hedge who hnot later hlater
    linarith
  linarith

end QuittingPositiveDebtSelfLoopLimit

end GameTheory
