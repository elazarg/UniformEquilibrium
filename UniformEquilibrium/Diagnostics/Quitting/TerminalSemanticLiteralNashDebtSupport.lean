/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticOwnStrategyTransport
import UniformEquilibrium.Quitting.Cycles.PeriodOneTangentAtlas

/-!
# Literal Nash support at minimum terminal debt

At a minimum-total-debt terminal semantic pair, paid own-strategy transport
turns the hidden continuation-option budget into the familiar absorption
support functional. For every product root, collision mass is charged by total
debt and each singleton mass is charged by the complementary debt. Their sum
is bounded by the root's literal one-stage Nash defect.

This is a quantitative extension of the exact-Nash support geometry. In
particular, an approximately Nash root with appreciable absorption must put
singleton mass on a player carrying nearly all terminal debt, unless total
debt itself is small.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- At a minimum-total-debt semantic pair, collision and complementary
singleton debt are bounded by the literal root Nash defect. -/
theorem minimumTerminalSemantic_literalNash_support_budget
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι) (root : ι → PMF Bool)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum pair ≤
        quittingTerminalSemanticDebtSum candidate) :
    quittingTerminalSemanticDebtSum pair *
          quittingRootCollisionMass root +
        ∑ who, quittingRootCoalitionMass root {who} *
          (quittingTerminalSemanticDebtSum pair -
            quittingTerminalSemanticDebt pair who) ≤
      quittingRootTotalNashDefect reward pair.1 root := by
  have htransport :=
    minimumTerminalSemantic_absorptionDebt_sub_quitOptionBudget_le_literalDefectSum
      reward pair root hpair hminimum
  have habsorption :=
    QuittingFiniteRootWindow.quittingRootAbsorptionMass_eq_sum_singletonMass_add_collisionMass
      root
  rw [habsorption] at htransport
  unfold quittingRootOpponentContinueMass at htransport
  simp_rw [quittingRootCoalitionMass_singleton_eq_opponentContinue_mul_quit]
    at htransport ⊢
  calc
    quittingTerminalSemanticDebtSum pair *
          quittingRootCollisionMass root +
        ∑ who,
          (quittingStationaryContinueMass
                (Function.update root who (PMF.pure false)) *
              (root who true).toReal) *
            (quittingTerminalSemanticDebtSum pair -
              quittingTerminalSemanticDebt pair who) =
        ((∑ who,
              quittingStationaryContinueMass
                  (Function.update root who (PMF.pure false)) *
                (root who true).toReal) +
            quittingRootCollisionMass root) *
              quittingTerminalSemanticDebtSum pair -
          ∑ who,
            quittingStationaryContinueMass
                (Function.update root who (PMF.pure false)) *
              (root who true).toReal *
                quittingTerminalSemanticDebt pair who := by
      simp_rw [mul_sub]
      rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
      ring
    _ ≤ quittingRootTotalNashDefect reward pair.1 root := htransport

/-- Total debt times collision mass is bounded by literal root defect. -/
theorem minimumTerminalSemantic_debtSum_mul_collisionMass_le_literalDefect
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι) (root : ι → PMF Bool)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum pair ≤
        quittingTerminalSemanticDebtSum candidate) :
    quittingTerminalSemanticDebtSum pair * quittingRootCollisionMass root ≤
      quittingRootTotalNashDefect reward pair.1 root := by
  have hbudget := minimumTerminalSemantic_literalNash_support_budget
    reward pair root hpair hminimum
  have hdebt : ∀ who,
      quittingTerminalSemanticDebt pair who ≤
        quittingTerminalSemanticDebtSum pair := by
    intro who
    unfold quittingTerminalSemanticDebtSum
    exact Finset.single_le_sum
      (fun player _ =>
        quittingTerminalSemanticDebt_nonneg_of_mem_carrier reward hpair player)
      (Finset.mem_univ who)
  have hsingleton : 0 ≤
      ∑ who, quittingRootCoalitionMass root {who} *
        (quittingTerminalSemanticDebtSum pair -
          quittingTerminalSemanticDebt pair who) := by
    exact Finset.sum_nonneg fun who _ => mul_nonneg
      (MarkedAbsorptionCylinder.quittingRootCoalitionMass_nonneg root {who})
      (sub_nonneg.mpr (hdebt who))
  linarith

/-- If `kappa` is below total debt and every complementary debt, then
`kappa` times the full absorption mass is bounded by literal root defect. -/
theorem minimumTerminalSemantic_kappa_mul_absorption_le_literalDefect
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι) (root : ι → PMF Bool)
    (kappa : ℝ)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum pair ≤
        quittingTerminalSemanticDebtSum candidate)
    (hkappaTotal : kappa ≤ quittingTerminalSemanticDebtSum pair)
    (hkappaComplement : ∀ who,
      kappa ≤ quittingTerminalSemanticDebtSum pair -
        quittingTerminalSemanticDebt pair who) :
    kappa * quittingRootAbsorptionMass root ≤
      quittingRootTotalNashDefect reward pair.1 root := by
  have hbudget := minimumTerminalSemantic_literalNash_support_budget
    reward pair root hpair hminimum
  have hcollision :
      kappa * quittingRootCollisionMass root ≤
        quittingTerminalSemanticDebtSum pair *
          quittingRootCollisionMass root :=
    mul_le_mul_of_nonneg_right hkappaTotal
      (quittingRootCollisionMass_nonneg root)
  have hsingleton :
      (∑ who, quittingRootCoalitionMass root {who} * kappa) ≤
        ∑ who, quittingRootCoalitionMass root {who} *
          (quittingTerminalSemanticDebtSum pair -
            quittingTerminalSemanticDebt pair who) := by
    apply Finset.sum_le_sum
    intro who _
    exact mul_le_mul_of_nonneg_left (hkappaComplement who)
      (MarkedAbsorptionCylinder.quittingRootCoalitionMass_nonneg root {who})
  have habsorption :=
    QuittingFiniteRootWindow.quittingRootAbsorptionMass_eq_sum_singletonMass_add_collisionMass
      root
  calc
    kappa * quittingRootAbsorptionMass root =
        kappa * quittingRootCollisionMass root +
          ∑ who, quittingRootCoalitionMass root {who} * kappa := by
      rw [habsorption, ← Finset.sum_mul]
      ring
    _ ≤ quittingTerminalSemanticDebtSum pair *
          quittingRootCollisionMass root +
        ∑ who, quittingRootCoalitionMass root {who} *
          (quittingTerminalSemanticDebtSum pair -
            quittingTerminalSemanticDebt pair who) :=
      add_le_add hcollision hsingleton
    _ ≤ quittingRootTotalNashDefect reward pair.1 root := hbudget

/-- An `epsilon`-Nash root satisfies the same absorption bound with total
error `card ι * epsilon`. -/
theorem minimumTerminalSemantic_kappa_mul_absorption_le_card_mul_of_isεNash
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι) (root : ι → PMF Bool)
    (kappa ε : ℝ)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum pair ≤
        quittingTerminalSemanticDebtSum candidate)
    (hkappaTotal : kappa ≤ quittingTerminalSemanticDebtSum pair)
    (hkappaComplement : ∀ who,
      kappa ≤ quittingTerminalSemanticDebtSum pair -
        quittingTerminalSemanticDebt pair who)
    (hnash : IsεQuittingRootNash reward pair.1 ε root) :
    kappa * quittingRootAbsorptionMass root ≤ Fintype.card ι * ε :=
  (minimumTerminalSemantic_kappa_mul_absorption_le_literalDefect
    reward pair root kappa hpair hminimum hkappaTotal hkappaComplement).trans
      (quittingRootTotalNashDefect_le_card_mul_of_isεQuittingRootNash
        reward pair.1 root ε hnash)

/-- If literal root defect is smaller than `kappa` times absorption, some
player carries all but less than `kappa` of the total debt. -/
theorem exists_complementaryDebt_lt_of_literalDefect_lt_kappa_mul_absorption
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι) (root : ι → PMF Bool)
    (kappa : ℝ)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum pair ≤
        quittingTerminalSemanticDebtSum candidate)
    (hkappaTotal : kappa ≤ quittingTerminalSemanticDebtSum pair)
    (hstrict : quittingRootTotalNashDefect reward pair.1 root <
      kappa * quittingRootAbsorptionMass root) :
    ∃ who,
      quittingTerminalSemanticDebtSum pair -
          quittingTerminalSemanticDebt pair who <
        kappa := by
  by_contra hnone
  have hcomplement : ∀ who,
      kappa ≤ quittingTerminalSemanticDebtSum pair -
        quittingTerminalSemanticDebt pair who := by
    intro who
    exact le_of_not_gt fun hlt => hnone ⟨who, hlt⟩
  have hbound := minimumTerminalSemantic_kappa_mul_absorption_le_literalDefect
    reward pair root kappa hpair hminimum hkappaTotal hcomplement
  exact (not_lt_of_ge hbound) hstrict

/-- Quantitative owner selection for an approximately Nash absorbing root. -/
theorem exists_complementaryDebt_lt_of_card_mul_lt_kappa_mul_absorption
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι) (root : ι → PMF Bool)
    (kappa ε : ℝ)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum pair ≤
        quittingTerminalSemanticDebtSum candidate)
    (hkappaTotal : kappa ≤ quittingTerminalSemanticDebtSum pair)
    (hnash : IsεQuittingRootNash reward pair.1 ε root)
    (hstrict : Fintype.card ι * ε <
      kappa * quittingRootAbsorptionMass root) :
    ∃ who,
      quittingTerminalSemanticDebtSum pair -
          quittingTerminalSemanticDebt pair who <
        kappa := by
  apply exists_complementaryDebt_lt_of_literalDefect_lt_kappa_mul_absorption
    reward pair root kappa hpair hminimum hkappaTotal
  exact (quittingRootTotalNashDefect_le_card_mul_of_isεQuittingRootNash
    reward pair.1 root ε hnash).trans_lt hstrict

end GameTheory
