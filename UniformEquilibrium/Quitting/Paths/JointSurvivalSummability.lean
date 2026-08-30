/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Boundary.Repair.JointComplementarity
import UniformEquilibrium.Quitting.Terminal.TailCompression.ElementaryCaps

/-!
# Summability under positive joint survival

Positive limiting joint survival bounds the unweighted one-stage absorption
clock by a summable geometric budget.  This path-level fact is independent of
any compactification or classification data.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability

variable {ι : Type} [Fintype ι]

/-- Positive limiting joint survival forces summability of the entire
one-stage joint absorption clock. -/
theorem summable_quittingRootAbsorptionMass_of_jointSurvivalLimit_pos
    (roots : ℕ → ι → PMF Bool) (start : ℕ)
    (hpositive : 0 < quittingJointSurvivalLimit roots start) :
    Summable (fun time => quittingRootAbsorptionMass (roots time)) := by
  let charge : ℕ → ℝ := fun offset =>
    quittingRootAbsorptionMass (roots (start + offset))
  have hchargeNonneg : ∀ offset, 0 ≤ charge offset := by
    intro offset
    exact sub_nonneg.mpr
      (quittingStationaryContinueMass_le_one (roots (start + offset)))
  have htail : Summable charge := by
    apply summable_of_sum_range_le
      (c := 1 / quittingJointSurvivalLimit roots start) hchargeNonneg
    intro fuel
    have hweighted :
        quittingJointSurvivalLimit roots start *
            (∑ offset ∈ Finset.range fuel, charge offset) <=
          1 - quittingJointSurvivalWeight roots start fuel := by
      rw [Finset.mul_sum]
      calc
        (∑ offset ∈ Finset.range fuel,
            quittingJointSurvivalLimit roots start * charge offset) ≤
            ∑ offset ∈ Finset.range fuel,
              quittingJointSurvivalWeight roots start offset *
                (1 - quittingStationaryContinueMass
                  (roots (start + offset))) := by
          apply Finset.sum_le_sum
          intro offset _
          apply mul_le_mul_of_nonneg_right
          . exact le_quittingJointSurvivalWeight_of_tendsto roots start
              (tendsto_quittingJointSurvivalLimit roots start) offset
          . exact hchargeNonneg offset
        _ = 1 - quittingJointSurvivalWeight roots start fuel :=
          sum_quittingJointSurvivalWeight_mul_one_sub_continueMass
            roots start fuel
    apply (le_div_iff₀ hpositive).2
    calc
      (∑ offset ∈ Finset.range fuel, charge offset) *
          quittingJointSurvivalLimit roots start =
          quittingJointSurvivalLimit roots start *
            (∑ offset ∈ Finset.range fuel, charge offset) := by ring
      _ ≤ 1 - quittingJointSurvivalWeight roots start fuel := hweighted
      _ ≤ 1 := by
        linarith [quittingJointSurvivalWeight_nonneg roots start fuel]
  have hshift : Summable (fun offset =>
      quittingRootAbsorptionMass (roots (offset + start))) := by
    simpa [charge, Nat.add_comm] using htail
  exact (summable_nat_add_iff
    (f := fun time => quittingRootAbsorptionMass (roots time)) start).1 hshift

end GameTheory
