/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Boundary.Analytic.ChargeTangent
import UniformEquilibrium.Quitting.Cycles.ConditionedFloorViability
import UniformEquilibrium.Quitting.Cycles.ConditionedTangentSeam

/-!
# Punishment-slack thresholds for conditioned tangents

A negative ordinary tangent can survive as a negative conditioned delivery
gap, expose a conditioned floor violation, or be financed by the surviving
phantom share of the boundary's floor slack. This module states the exact
pointwise alternative and its uncovered-budget consequence.

It also records that exact affine-shrink coefficient transport cannot return
to the unshrunk scale at a finite date unless it started there. These are
generic accounting results and use no terminal exploitability witness.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-! ## A finite affine reset is impossible -/

omit [Fintype ι] [DecidableEq ι] in
/-- **No finite affine return.**  If exact coefficient transport is preserved
through a finite block and the terminal scale is the unshrunk scale `1`, then
the initial scale was already `1`.  No positivity assumptions are needed: this
is the exact telescoping boundary-share invariant. -/
theorem quittingConditionedAffineShrink_initialScale_eq_one_of_finiteReturn
    (alpha scale : ℕ → ℝ)
    (htransport : ∀ time,
      (1 - scale time * alpha time) * (1 - scale (time + 1)) =
        1 - scale time)
    (fuel : ℕ) (hreturn : scale fuel = 1) :
    scale 0 = 1 := by
  have hinvariant :=
    quittingConditionedAffineShrink_survival_mul_complement
      alpha scale htransport fuel
  rw [hreturn, sub_self, mul_zero] at hinvariant
  linarith

omit [Fintype ι] [DecidableEq ι] in
/-- Strict initial shrinking and an exact finite return to the unshrunk tail
are incompatible. -/
theorem not_quittingConditionedAffineShrink_finiteReturn_of_initial_lt_one
    (alpha scale : ℕ → ℝ)
    (htransport : ∀ time,
      (1 - scale time * alpha time) * (1 - scale (time + 1)) =
        1 - scale time)
    (fuel : ℕ) (hinitial : scale 0 < 1) :
    scale fuel ≠ 1 := by
  intro hreturn
  have := quittingConditionedAffineShrink_initialScale_eq_one_of_finiteReturn
    alpha scale htransport fuel hreturn
  linarith

/-! ## The pointwise punishment-slack threshold -/

omit [DecidableEq ι] in
/-- A negative ordinary tangent has three possible readings.  It is a genuine
negative conditioned delivery gap; the conditioned continuation is below its
floor; or its whole magnitude is paid by the surviving phantom share of the
boundary's floor slack. -/
theorem conditionedGap_neg_or_conditionedFloorViolation_or_tangentFunding
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι)
    (boundary floor : Payoff ι) (time : ℕ) (who : ι)
    (hnext : 0 < quittingTailEventualAbsorption roots (time + 1))
    (htangent :
      quittingRootConditionalAbsorbingDelivery reward (roots time) who -
        value (time + 1) who < 0) :
    (quittingRootConditionalAbsorbingDelivery reward (roots time) who -
        quittingTailConditionedValue roots value boundary (time + 1) who < 0) ∨
      (quittingTailConditionedValue roots value boundary (time + 1) who <
        floor who) ∨
      -(quittingRootConditionalAbsorbingDelivery reward (roots time) who -
          value (time + 1) who) ≤
        quittingJointSurvivalLimit roots (time + 1) *
          (boundary who - floor who) := by
  rcases conditionedGap_neg_or_strictPhantomFunding_of_tangent_neg
      (reward := reward) roots value boundary time who hnext htangent with
    hgap | ⟨-, hbelowBoundary, hfunding⟩
  · exact Or.inl hgap
  · by_cases hfloor :
      quittingTailConditionedValue roots value boundary (time + 1) who <
        floor who
    · exact Or.inr (Or.inl hfloor)
    · right
      right
      have hfloorSafe : floor who ≤
          quittingTailConditionedValue roots value boundary (time + 1) who :=
        le_of_not_gt hfloor
      have hgapLe :
          boundary who -
              quittingTailConditionedValue roots value boundary
                (time + 1) who ≤
            boundary who - floor who := by
        linarith
      exact hfunding.trans <| mul_le_mul_of_nonneg_left hgapLe
        (quittingJointSurvivalLimit_nonneg roots (time + 1))

omit [DecidableEq ι] in
/-- If the tangent magnitude exceeds the available phantom punishment budget,
then either the negative gap survives conditioning or the conditioned state
violates punishment rationality. -/
theorem conditionedGap_neg_or_conditionedFloorViolation_of_tangent_gt_funding
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι)
    (boundary floor : Payoff ι) (time : ℕ) (who : ι)
    (hnext : 0 < quittingTailEventualAbsorption roots (time + 1))
    (htangent :
      quittingRootConditionalAbsorbingDelivery reward (roots time) who -
        value (time + 1) who < 0)
    (huncovered :
      quittingJointSurvivalLimit roots (time + 1) *
          (boundary who - floor who) <
        -(quittingRootConditionalAbsorbingDelivery reward (roots time) who -
          value (time + 1) who)) :
    (quittingRootConditionalAbsorbingDelivery reward (roots time) who -
        quittingTailConditionedValue roots value boundary (time + 1) who < 0) ∨
      quittingTailConditionedValue roots value boundary (time + 1) who <
        floor who := by
  rcases conditionedGap_neg_or_conditionedFloorViolation_or_tangentFunding
      (reward := reward) roots value boundary floor time who hnext htangent with
    hgap | hfloor | hfunding
  · exact Or.inl hgap
  · exact Or.inr hfloor
  · linarith

/-! ## The limiting packet threshold -/

namespace QuittingChargeTangentData

/-- The packet's punishment admissibility threshold is exactly its boundary
slack.  The singleton mixture is the boundary plus the tangent, so a negative
tangent is individually rational precisely when its magnitude fits inside
`boundary - punishment`. -/
theorem punishmentValue_le_singletonMixture_iff_neg_tangent_le_slack
    (data : QuittingChargeTangentData reward) (who : ι) :
    quittingPunishmentValue reward who ≤
        quittingSingletonMixture reward data.mass who ↔
      -data.tangent who ≤
        data.boundary who - quittingPunishmentValue reward who := by
  rw [data.tangent_eq who]
  constructor <;> intro h <;> linarith

end QuittingChargeTangentData


end GameTheory
