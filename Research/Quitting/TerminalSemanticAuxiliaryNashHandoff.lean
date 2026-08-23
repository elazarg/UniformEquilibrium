/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticCapNashDebtSupport
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticAuxiliaryNashBudget

/-!
# Boundary handoff and overtilt corollaries

The auxiliary-cap budget has two useful sharp consequences.  On the closed
boundary of the minimum-debt cube, every coordinate estimate is an equality:
the normalized debt vector is transported by joint survival and the singleton
absorption distribution.  Beyond that boundary, collision mass is paid by the
positive part of the cap overtilt.

The collision parameter in this file is always the unconditional one-stage
probability of two or more quitters.  No conditional collision ratio is used.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-! ## Exact boundary handoff -/

/-- On the boundary obtained by lowering every cap coordinate by the total
minimum debt, the prefix estimate is sharp in every coordinate. -/
theorem minimumTerminalSemantic_boundaryNash_debt_handoff
    (pair : QuittingTerminalSemanticPair ι)
    (root : ι → PMF Bool)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum pair ≤
        quittingTerminalSemanticDebtSum candidate)
    (hpositive : 0 < quittingTerminalSemanticDebtSum pair)
    (hnash : IsεQuittingRootNash reward
      (pair.2 - fun _ => quittingTerminalSemanticDebtSum pair) 0 root)
    (who : ι) :
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPrefix reward root pair) who =
      quittingStationaryContinueMass root *
          quittingTerminalSemanticDebt pair who +
      quittingRootCoalitionMass root {who} *
          quittingTerminalSemanticDebtSum pair := by
  let prefixed := quittingTerminalSemanticPrefix reward root pair
  let debt := quittingTerminalSemanticDebtSum pair
  have hdebtNonneg : 0 ≤ debt := hpositive.le
  have hcoordinate : ∀ player,
      quittingTerminalSemanticDebt prefixed player ≤
        quittingStationaryContinueMass root *
            quittingTerminalSemanticDebt pair player +
          quittingRootCoalitionMass root {player} * debt := by
    intro player
    exact quittingTerminalSemanticDebt_prefix_le_auxiliaryNash
      (reward := reward) pair (fun _ => debt) root player hdebtNonneg hnash
  have hcritical := minimumTerminalSemantic_auxiliaryNash_criticalFace
    (reward := reward) pair (fun _ => debt) root hpair hminimum hpositive
      (fun _ => hdebtNonneg) (fun _ => le_rfl) hnash
  have habsorption :=
    QuittingFiniteRootWindow.quittingRootAbsorptionMass_eq_sum_singletonMass_add_collisionMass
      root
  have hmass : quittingStationaryContinueMass root +
      (∑ player, quittingRootCoalitionMass root {player}) = 1 := by
    unfold quittingRootAbsorptionMass at habsorption
    rw [hcritical.1, add_zero] at habsorption
    linarith
  have hsumRight :
      (∑ player, (quittingStationaryContinueMass root *
            quittingTerminalSemanticDebt pair player +
          quittingRootCoalitionMass root {player} * debt)) = debt := by
    unfold debt quittingTerminalSemanticDebtSum
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
    calc
      quittingStationaryContinueMass root *
            (∑ player, quittingTerminalSemanticDebt pair player) +
          (∑ player, quittingRootCoalitionMass root {player}) *
            (∑ player, quittingTerminalSemanticDebt pair player) =
        (quittingStationaryContinueMass root +
            ∑ player, quittingRootCoalitionMass root {player}) *
          (∑ player, quittingTerminalSemanticDebt pair player) := by ring
      _ = ∑ player, quittingTerminalSemanticDebt pair player := by rw [hmass, one_mul]
  have hprefixed : prefixed ∈ quittingTerminalSemanticCarrier reward :=
    quittingTerminalSemanticPrefix_mem_carrier
      reward root pair hpair
  have hsumLeftLower : debt ≤
      ∑ player, quittingTerminalSemanticDebt prefixed player := by
    exact hminimum prefixed hprefixed
  have hsumLeftUpper :
      (∑ player, quittingTerminalSemanticDebt prefixed player) ≤ debt := by
    rw [← hsumRight]
    exact Finset.sum_le_sum fun player _ => hcoordinate player
  have hsumEq :
      (∑ player, quittingTerminalSemanticDebt prefixed player) =
        ∑ player, (quittingStationaryContinueMass root *
            quittingTerminalSemanticDebt pair player +
          quittingRootCoalitionMass root {player} * debt) := by
    rw [hsumRight]
    exact le_antisymm hsumLeftUpper hsumLeftLower
  exact (Finset.sum_eq_sum_iff_of_le
    (s := (Finset.univ : Finset ι))
    (fun player _ => hcoordinate player)).mp hsumEq who (Finset.mem_univ who)

/-- The preceding handoff, normalized by the positive minimum debt.  The
coefficient of `player` is its one-stage singleton absorption mass. -/
theorem minimumTerminalSemantic_boundaryNash_normalizedDebt_handoff
    (pair : QuittingTerminalSemanticPair ι)
    (root : ι → PMF Bool)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum pair ≤
        quittingTerminalSemanticDebtSum candidate)
    (hpositive : 0 < quittingTerminalSemanticDebtSum pair)
    (hnash : IsεQuittingRootNash reward
      (pair.2 - fun _ => quittingTerminalSemanticDebtSum pair) 0 root)
    (who : ι) :
    quittingTerminalSemanticDebt
          (quittingTerminalSemanticPrefix reward root pair) who /
        quittingTerminalSemanticDebtSum pair =
      quittingStationaryContinueMass root *
          (quittingTerminalSemanticDebt pair who /
            quittingTerminalSemanticDebtSum pair) +
        quittingRootCoalitionMass root {who} := by
  rw [minimumTerminalSemantic_boundaryNash_debt_handoff
    (reward := reward) pair root hpair hminimum hpositive hnash who]
  field_simp [ne_of_gt hpositive]

/-! ## Collision is paid by cap overtilt -/

/-- At a positive minimum, collision absorption is bounded by the
singleton-weighted positive overtilt beyond the closed debt cube. -/
theorem minimumTerminalSemantic_collision_mul_debtSum_le_positiveOvertilt
    (pair : QuittingTerminalSemanticPair ι)
    (shift : Payoff ι) (root : ι → PMF Bool)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum pair ≤
        quittingTerminalSemanticDebtSum candidate)
    (hshift : ∀ who, 0 ≤ shift who)
    (hnash : IsεQuittingRootNash reward (pair.2 - shift) 0 root) :
    quittingTerminalSemanticDebtSum pair * quittingRootCollisionMass root ≤
      ∑ who, quittingRootCoalitionMass root {who} *
        max (shift who - quittingTerminalSemanticDebtSum pair) 0 := by
  have hbudget := minimumTerminalSemantic_auxiliaryNash_budget
    (reward := reward) pair shift root hpair hminimum hshift hnash
  have hsumNeg :
      (∑ who, quittingRootCoalitionMass root {who} *
          (quittingTerminalSemanticDebtSum pair - shift who)) =
        -(∑ who, quittingRootCoalitionMass root {who} *
          (shift who - quittingTerminalSemanticDebtSum pair)) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro who _
    ring
  rw [hsumNeg] at hbudget
  calc
    quittingTerminalSemanticDebtSum pair * quittingRootCollisionMass root ≤
        ∑ who, quittingRootCoalitionMass root {who} *
          (shift who - quittingTerminalSemanticDebtSum pair) := by
      linarith
    _ ≤ ∑ who, quittingRootCoalitionMass root {who} *
          max (shift who - quittingTerminalSemanticDebtSum pair) 0 := by
      apply Finset.sum_le_sum
      intro who _
      exact mul_le_mul_of_nonneg_left (le_max_left _ _)
        (MarkedAbsorptionCylinder.quittingRootCoalitionMass_nonneg root {who})

/-- Uniform overtilt form: if every cap shift is at most `debt + epsilon`,
then an unconditional collision mass `rho` costs at least `debt * rho` of
overtilt. -/
theorem minimumTerminalSemantic_collisionScale_le_uniformOvertilt
    (pair : QuittingTerminalSemanticPair ι)
    (shift : Payoff ι) (root : ι → PMF Bool)
    (rho epsilon : ℝ)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum pair ≤
        quittingTerminalSemanticDebtSum candidate)
    (hshift : ∀ who, 0 ≤ shift who)
    (hnash : IsεQuittingRootNash reward (pair.2 - shift) 0 root)
    (hrho : rho ≤ quittingRootCollisionMass root)
    (hepsilon : 0 ≤ epsilon)
    (hupper : ∀ who,
      shift who ≤ quittingTerminalSemanticDebtSum pair + epsilon) :
    quittingTerminalSemanticDebtSum pair * rho ≤ epsilon := by
  have hbudget := minimumTerminalSemantic_auxiliaryNash_budget
    (reward := reward) pair shift root hpair hminimum hshift hnash
  have hcoordinateDebtNonneg : ∀ who,
      0 ≤ quittingTerminalSemanticDebt pair who :=
    quittingTerminalSemanticDebt_nonneg_of_mem_carrier
      reward hpair
  have hdebtNonneg : 0 ≤ quittingTerminalSemanticDebtSum pair := by
    unfold quittingTerminalSemanticDebtSum
    exact Finset.sum_nonneg fun who _ => hcoordinateDebtNonneg who
  have hcollisionLower :
      quittingTerminalSemanticDebtSum pair * rho ≤
        quittingTerminalSemanticDebtSum pair * quittingRootCollisionMass root :=
    mul_le_mul_of_nonneg_left hrho hdebtNonneg
  have hsingletonUpper :
      (∑ who, quittingRootCoalitionMass root {who} *
          (shift who - quittingTerminalSemanticDebtSum pair)) ≤
        epsilon * (∑ who, quittingRootCoalitionMass root {who}) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro who _
    have hshiftBound :
        shift who - quittingTerminalSemanticDebtSum pair ≤ epsilon := by
      linarith [hupper who]
    simpa [mul_comm] using mul_le_mul_of_nonneg_left hshiftBound
      (MarkedAbsorptionCylinder.quittingRootCoalitionMass_nonneg root {who})
  have hsingletonMassLe :
      (∑ who, quittingRootCoalitionMass root {who}) ≤ 1 := by
    have habsorption :=
      QuittingFiniteRootWindow.quittingRootAbsorptionMass_eq_sum_singletonMass_add_collisionMass
        root
    have hcollisionNonneg := quittingRootCollisionMass_nonneg root
    unfold quittingRootAbsorptionMass at habsorption
    have hcontinueNonneg := quittingStationaryContinueMass_nonneg root
    linarith
  have hscaledLe :
      epsilon * (∑ who, quittingRootCoalitionMass root {who}) ≤ epsilon :=
    mul_le_of_le_one_right hepsilon hsingletonMassLe
  have hsumNeg :
      (∑ who, quittingRootCoalitionMass root {who} *
          (quittingTerminalSemanticDebtSum pair - shift who)) =
        -(∑ who, quittingRootCoalitionMass root {who} *
          (shift who - quittingTerminalSemanticDebtSum pair)) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro who _
    ring
  rw [hsumNeg] at hbudget
  calc
    quittingTerminalSemanticDebtSum pair * rho ≤
        quittingTerminalSemanticDebtSum pair *
          quittingRootCollisionMass root := hcollisionLower
    _ ≤ ∑ who, quittingRootCoalitionMass root {who} *
          (shift who - quittingTerminalSemanticDebtSum pair) := by linarith
    _ ≤ epsilon * (∑ who, quittingRootCoalitionMass root {who}) :=
      hsingletonUpper
    _ ≤ epsilon := hscaledLe

/-! ## A fixed complementary-debt consequence near the minimum -/

/-- A fixed player's singleton mass times the complementary debt is bounded
by the semantic excess above a global minimum. -/
theorem terminalSemantic_singletonMass_mul_complementaryDebt_le_excess
    (base pair : QuittingTerminalSemanticPair ι)
    (root : ι → PMF Bool) (who : ι)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum base ≤
        quittingTerminalSemanticDebtSum candidate)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hnash : IsεQuittingRootNash reward pair.1 0 root) :
    quittingRootCoalitionMass root {who} *
        (quittingTerminalSemanticDebtSum pair -
          quittingTerminalSemanticDebt pair who) ≤
      quittingTerminalSemanticDebtSum pair -
        quittingTerminalSemanticDebtSum base := by
  have hbudget := terminalSemantic_exactNash_nearMinimum_support_budget
    (reward := reward) base pair root hminimum hpair hnash
  have hdebtNonneg : ∀ player,
      0 ≤ quittingTerminalSemanticDebt pair player :=
    quittingTerminalSemanticDebt_nonneg_of_mem_carrier
      reward hpair
  have hcomplementNonneg : ∀ player,
      0 ≤ quittingTerminalSemanticDebtSum pair -
        quittingTerminalSemanticDebt pair player := by
    intro player
    unfold quittingTerminalSemanticDebtSum
    exact sub_nonneg.mpr (Finset.single_le_sum
      (fun candidate _ => hdebtNonneg candidate) (Finset.mem_univ player))
  have hdebtSumNonneg : 0 ≤ quittingTerminalSemanticDebtSum pair := by
    unfold quittingTerminalSemanticDebtSum
    exact Finset.sum_nonneg fun player _ => hdebtNonneg player
  have hcollisionTermNonneg :
      0 ≤ quittingTerminalSemanticDebtSum pair *
        quittingRootCollisionMass root :=
    mul_nonneg hdebtSumNonneg (quittingRootCollisionMass_nonneg root)
  have htermNonneg : ∀ player ∈ (Finset.univ : Finset ι),
      0 ≤ quittingRootCoalitionMass root {player} *
        (quittingTerminalSemanticDebtSum pair -
          quittingTerminalSemanticDebt pair player) := by
    intro player _
    exact mul_nonneg
      (MarkedAbsorptionCylinder.quittingRootCoalitionMass_nonneg root {player})
      (hcomplementNonneg player)
  have hsingleLeSum :
      quittingRootCoalitionMass root {who} *
          (quittingTerminalSemanticDebtSum pair -
            quittingTerminalSemanticDebt pair who) ≤
        ∑ player, quittingRootCoalitionMass root {player} *
          (quittingTerminalSemanticDebtSum pair -
            quittingTerminalSemanticDebt pair player) :=
    Finset.single_le_sum htermNonneg (Finset.mem_univ who)
  linarith

end GameTheory
