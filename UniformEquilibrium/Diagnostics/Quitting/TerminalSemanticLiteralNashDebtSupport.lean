/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticOwnStrategyTransport
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPlateauNashMoat
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

open Filter Set Math.Probability Math.PMFProduct
open scoped Topology

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

/-! ## Executable realization -/

/-- The behavioral deviation which replaces the displayed root marginal by
the better pure endpoint and then resumes the original continuation. -/
def quittingRootBestEndpointBehaviorDeviation
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (continuation : (quittingGame reward).BehaviorProfile)
    (root : ι → PMF Bool) (who : ι) :
    (quittingGame reward).BehaviorStrategy who :=
  let tail : Payoff ι := fun player =>
    quittingTerminalPayoff reward continuation player
  quittingRootAndContinuationDeviation reward
    (PMF.pure (quittingRootBestEndpointAction reward tail root who))
    (continuation who)

/-- The executable better-endpoint deviation at a root/continuation splice
gains exactly the literal root coordinate Nash defect. -/
theorem quittingTerminalPayoff_rootBestEndpointDeviation_sub_eq_literalDefect
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (continuation : (quittingGame reward).BehaviorProfile)
    (root : ι → PMF Bool) (who : ι) :
    quittingTerminalPayoff reward
          (Function.update
            (quittingRootThenContinuationProfile reward root continuation)
            who
            (quittingRootBestEndpointBehaviorDeviation
              reward continuation root who)) who -
        quittingTerminalPayoff reward
          (quittingRootThenContinuationProfile reward root continuation) who =
      quittingRootCoordinateNashDefect reward
        (fun player => quittingTerminalPayoff reward continuation player)
        root who := by
  let tail : Payoff ι := fun player =>
    quittingTerminalPayoff reward continuation player
  let action := quittingRootBestEndpointAction reward tail root who
  have hdeviation :=
    quittingTerminalPayoff_update_rootAndContinuationDeviation_eq
      reward root continuation who (PMF.pure action) (continuation who)
  have hcontinuation : Function.update continuation who (continuation who) =
      continuation := Function.update_eq_self who continuation
  rw [hcontinuation] at hdeviation
  have htail : Function.update tail who (tail who) = tail :=
    Function.update_eq_self who tail
  change quittingTerminalPayoff reward
      (Function.update
        (quittingRootThenContinuationProfile reward root continuation) who
        (quittingRootAndContinuationDeviation reward (PMF.pure action)
          (continuation who))) who = _ at hdeviation
  rw [htail] at hdeviation
  rw [quittingRootBestEndpointBehaviorDeviation]
  change _ - _ = quittingRootCoordinateNashDefect reward tail root who
  rw [hdeviation, quittingTerminalPayoff_rootThenContinuation_eq]
  exact quittingRootSuccessorPayoff_bestEndpoint_sub_eq_coordinateNashDefect
    reward tail root who

/-- A positive literal root defect at a carrier point persists at some
executable continuation profile realizing that point. -/
theorem exists_profile_literalRootDefect_pos_of_mem_carrier
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι)
    (root : ι → PMF Bool) (who : ι)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hdefect : 0 <
      quittingRootCoordinateNashDefect reward pair.1 root who) :
    ∃ continuation : (quittingGame reward).BehaviorProfile,
      0 < quittingRootCoordinateNashDefect reward
        (fun player => quittingTerminalPayoff reward continuation player)
        root who := by
  obtain ⟨profiles, hprofiles⟩ :=
    exists_terminalProfile_sequence_tendsto_semanticPair reward pair hpair
  have hpayoff : Tendsto
      (fun n => (quittingTerminalSemanticPair reward (profiles n)).1)
      atTop (𝓝 pair.1) :=
    continuous_fst.continuousAt.tendsto.comp hprofiles
  have hdefectTendsto : Tendsto
      (fun n => quittingRootCoordinateNashDefect reward
        (quittingTerminalSemanticPair reward (profiles n)).1 root who)
      atTop
      (𝓝 (quittingRootCoordinateNashDefect reward pair.1 root who)) :=
    (continuous_quittingRootCoordinateNashDefect_fixedRoot
      reward root who).continuousAt.tendsto.comp hpayoff
  have heventually : ∀ᶠ n in atTop,
      0 < quittingRootCoordinateNashDefect reward
        (quittingTerminalSemanticPair reward (profiles n)).1 root who :=
    hdefectTendsto.eventually (Ioi_mem_nhds hdefect)
  obtain ⟨n, hn⟩ := heventually.exists
  exact ⟨profiles n, hn⟩

/-- A positive carrier-level literal defect yields a concrete profitable
behavior deviation from an executable root/continuation splice. -/
theorem exists_executable_rootBestEndpointGain_pos_of_mem_carrier
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι)
    (root : ι → PMF Bool) (who : ι)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hdefect : 0 <
      quittingRootCoordinateNashDefect reward pair.1 root who) :
    ∃ continuation : (quittingGame reward).BehaviorProfile,
      0 < quittingTerminalPayoff reward
            (Function.update
              (quittingRootThenContinuationProfile reward root continuation)
              who
              (quittingRootBestEndpointBehaviorDeviation
                reward continuation root who)) who -
          quittingTerminalPayoff reward
            (quittingRootThenContinuationProfile reward root continuation) who := by
  obtain ⟨continuation, hcontinuation⟩ :=
    exists_profile_literalRootDefect_pos_of_mem_carrier
      reward pair root who hpair hdefect
  refine ⟨continuation, ?_⟩
  rw [quittingTerminalPayoff_rootBestEndpointDeviation_sub_eq_literalDefect]
  exact hcontinuation

/-- Positive collision/complementary-debt support at a minimum carrier point
produces an executable profitable root deviation. -/
theorem exists_executable_rootBestEndpointGain_pos_of_minimum_of_support_pos
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι) (root : ι → PMF Bool)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum pair ≤
        quittingTerminalSemanticDebtSum candidate)
    (hsupport : 0 <
      quittingTerminalSemanticDebtSum pair *
            quittingRootCollisionMass root +
          ∑ who, quittingRootCoalitionMass root {who} *
            (quittingTerminalSemanticDebtSum pair -
              quittingTerminalSemanticDebt pair who)) :
    ∃ (who : ι)
        (continuation : (quittingGame reward).BehaviorProfile),
      0 < quittingTerminalPayoff reward
            (Function.update
              (quittingRootThenContinuationProfile reward root continuation)
              who
              (quittingRootBestEndpointBehaviorDeviation
                reward continuation root who)) who -
          quittingTerminalPayoff reward
            (quittingRootThenContinuationProfile reward root continuation) who := by
  have hbudget := minimumTerminalSemantic_literalNash_support_budget
    reward pair root hpair hminimum
  have htotal : 0 < quittingRootTotalNashDefect reward pair.1 root :=
    hsupport.trans_le hbudget
  unfold quittingRootTotalNashDefect at htotal
  obtain ⟨who, _, hwho⟩ := (Finset.sum_pos_iff_of_nonneg fun player _ =>
    quittingRootCoordinateNashDefect_nonneg reward pair.1 root player).mp htotal
  obtain ⟨continuation, hgain⟩ :=
    exists_executable_rootBestEndpointGain_pos_of_mem_carrier
      reward pair root who hpair hwho
  exact ⟨who, continuation, hgain⟩

/-- The singleton-option strictness criterion directly yields an executable
profitable root deviation at a realizing continuation profile. -/
theorem exists_executable_rootBestEndpointGain_pos_of_minimum_of_optionMass_lt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι) (root : ι → PMF Bool)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum pair ≤
        quittingTerminalSemanticDebtSum candidate)
    (owner : ι) (hdebt : 0 < quittingTerminalSemanticDebt pair owner)
    (hmass : quittingRootOpponentContinueMass root owner *
        (root owner true).toReal < quittingRootAbsorptionMass root) :
    ∃ (who : ι)
        (continuation : (quittingGame reward).BehaviorProfile),
      0 < quittingTerminalPayoff reward
            (Function.update
              (quittingRootThenContinuationProfile reward root continuation)
              who
              (quittingRootBestEndpointBehaviorDeviation
                reward continuation root who)) who -
          quittingTerminalPayoff reward
            (quittingRootThenContinuationProfile reward root continuation) who := by
  obtain ⟨who, hwho⟩ :=
    exists_literalDefect_pos_of_minimum_of_debt_pos_of_optionMass_lt_absorption
      reward pair root hpair hminimum owner hdebt hmass
  obtain ⟨continuation, hgain⟩ :=
    exists_executable_rootBestEndpointGain_pos_of_mem_carrier
      reward pair root who hpair hwho
  exact ⟨who, continuation, hgain⟩

end GameTheory
