/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.ProbabilityMassFunction.Bool
import UniformEquilibrium.Quitting.Debt.Dynamic.BudgetStableCompatiblePacketIteration
import UniformEquilibrium.Quitting.Stationary.Root

/-!
# Vacuity of the bare budget-stable packet interface

The bare packet-system structure is inhabited for every reward table exactly
when the player type has at least two elements.  The witness repeats one
stationary half-Quit root, uses zero seam and availability costs, and annotates
its sole port by the root's actual terminal semantic pair.

Thus inhabitance of this interface alone is not a source theorem and has no
uniform-equilibrium consequence.  Mathematical content must enter through an
adapter tying the system's ports and annotations to the intended sources.
-/

noncomputable section

namespace GameTheory

open Math
open scoped BigOperators

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The bare budget-stable packet interface is inhabited exactly for player
types with at least two elements, independently of the reward table. -/
theorem nonempty_quittingBudgetStablePacketSystem_iff_two_le_card
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    Nonempty (QuittingBudgetStablePacketSystem reward) ↔
      2 ≤ Fintype.card ι := by
  constructor
  · rintro ⟨system⟩
    have : 1 < Fintype.card ι :=
      Fintype.one_lt_card_iff.mpr
        ⟨system.first, system.second, system.labels_ne⟩
    omega
  · intro hcard
    have hone : 1 < Fintype.card ι := by omega
    obtain ⟨first, second, hne⟩ := Fintype.one_lt_card_iff.mp hone
    let root : ι → PMF Bool := fun _ => PMF.uniformOfFintype Bool
    let profile := quittingStationaryProfile reward root
    let pair := quittingTerminalSemanticPair reward profile
    let bound := 2 * quittingRewardBound reward
    have hrewardBound : ∀ S who,
        |reward S who| ≤ quittingRewardBound reward :=
      abs_reward_le_quittingRewardBound reward
    have hM : 0 ≤ quittingRewardBound reward :=
      quittingRewardBound_nonneg reward
    have hfixed : pair = quittingTerminalSemanticPrefix reward root pair := by
      have hsplice := quittingTerminalSemanticPair_rootThenContinuation
        reward root profile
      rw [quittingRootThenContinuationProfile_stationary] at hsplice
      exact hsplice
    refine ⟨{
      Port := PUnit
      annotation := fun _ => pair
      radius := fun _ => 1
      radius_pos := fun _ => by norm_num
      omega := fun _ => 0
      chi := fun _ => 0
      omega_nonneg := fun _ => le_rfl
      chi_nonneg := fun _ => le_rfl
      kappa := 1 / 2
      kappa_pos := by norm_num
      first := first
      second := second
      labels_ne := hne
      bound := bound
      packetAvailable := ?_
      cost_sublinear := ?_
    }⟩
    · intro source scale hscale hlegal
      refine ⟨{
        length := 1
        length_pos := by omega
        roots := fun _ => root
        candidate := fun _ => pair
        successor := source
        exact_step := ?_
        entrance_anchor := rfl
        prescribed_endpoint := by simp
        total_endpoint := by simp
        first_hazard := ?_
        second_hazard := ?_
        radius_successor := by simp
        debt_nonneg := ?_
        prescribed_bounded := ?_
        debt_bounded := ?_
      }⟩
      · intro offset hoffset
        have hoffsetZero : offset = 0 := by omega
        subst offset
        exact hfixed
      · simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
        unfold quittingMarginalQuitHazard root
        norm_num [PMF.uniformOfFintype_apply]
        linarith
      · simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
        unfold quittingMarginalQuitHazard root
        norm_num [PMF.uniformOfFintype_apply]
        linarith
      · intro offset _ who
        exact quittingTerminalDeviationDebt_nonneg reward profile who
      · intro offset _ who
        have hpayoff : |pair.1 who| ≤ quittingRewardBound reward :=
          abs_quittingTerminalPayoff_le_quittingRewardBound
            reward profile who
        dsimp only [bound]
        linarith
      · intro offset _ who
        have hpayoff : |pair.1 who| ≤ quittingRewardBound reward :=
          abs_quittingTerminalPayoff_le_quittingRewardBound
            reward profile who
        have hcap : |pair.2 who| ≤ quittingRewardBound reward :=
          abs_quittingContinuationBestResponseValue_le
            reward profile who hrewardBound
        dsimp only [bound]
        exact (abs_sub _ _).trans (by linarith)
    · intro epsilon hepsilon delta hdelta
      refine ⟨delta / 2, by linarith, by linarith, ?_⟩
      simp
      exact mul_nonneg hepsilon.le (by linarith)

end GameTheory
