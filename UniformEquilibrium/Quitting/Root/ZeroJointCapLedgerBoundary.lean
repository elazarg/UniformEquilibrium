/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import UniformEquilibrium.Quitting.Root.FiniteWordWeightedCapDefectLedger
import UniformEquilibrium.Quitting.Terminal.TerminalExploitabilityUniformPayoff
import MathUE.Topology.FiniteLabelSubsequence

/-! # Zero-joint cap ledgers and the fixed aggregate payer

All ledgers below are computed from actual complete behavioral suffix caps.
A fixed payer is an aggregate obstruction on the same profiles, not a
uniformly defective row, a paid chronological edge, or a renewable source.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem quittingFiniteWordPlayerCapDefectLedger_le_debt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : List (ι → PMF Bool)) (tail : (quittingGame reward).BehaviorProfile) (who : ι) :
    quittingFiniteWordPlayerCapDefectLedger reward roots tail who ≤
      quittingTerminalDeviationDebt reward
        (quittingLiteralRootStackProfile reward roots tail) who := by
  rw [quittingTerminalDeviationDebt_literalRootStack_eq_playerLedger_add]
  exact le_add_of_nonneg_right (mul_nonneg (quittingLiteralRootStackJointSurvival_nonneg roots)
    (quittingTerminalDeviationDebt_nonneg reward tail who))

/-- No inner block cancels the outer reached ledger. -/
theorem quittingFiniteWordPlayerCapDefectLedger_outer_le_append
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (first second : List (ι → PMF Bool)) (tail : (quittingGame reward).BehaviorProfile) (who : ι) :
    quittingFiniteWordPlayerCapDefectLedger reward first
      (quittingLiteralRootStackProfile reward second tail) who ≤
        quittingFiniteWordPlayerCapDefectLedger reward (first ++ second) tail who := by
  rw [quittingFiniteWordPlayerCapDefectLedger_append]
  exact le_add_of_nonneg_right (mul_nonneg (quittingLiteralRootStackJointSurvival_nonneg first)
    (quittingFiniteWordPlayerCapDefectLedger_nonneg reward second tail who))

/-- Exact Nash against every actual suffix cap makes the ledger zero. -/
theorem quittingFiniteWordPlayerCapDefectLedger_eq_zero_of_capNash
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : List (ι → PMF Bool)) (tail : (quittingGame reward).BehaviorProfile)
    (hstack : IsQuittingCapNashRootStack reward roots tail) (who : ι) :
    quittingFiniteWordPlayerCapDefectLedger reward roots tail who = 0 := by
  have hledger := quittingTerminalDeviationDebt_literalRootStack_eq_playerLedger_add
    reward roots tail who
  rw [quittingTerminalDeviationDebt_capNashRootStack_eq roots tail who hstack] at hledger
  change quittingLiteralRootStackJointSurvival roots *
      quittingTerminalDeviationDebt reward tail who = _ at hledger
  linarith

/-- The final tail debt is uniformly bounded by the reward table and is
therefore erased by vanishing joint survival, regardless of deleted clocks. -/
theorem jointSurvival_mul_tailDebt_tendsto_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → List (ι → PMF Bool)) (tails : ℕ → (quittingGame reward).BehaviorProfile)
    (hjoint : Tendsto (fun index ↦ quittingLiteralRootStackJointSurvival (roots index))
      atTop (nhds 0)) (who : ι) :
    Tendsto (fun index ↦ quittingLiteralRootStackJointSurvival (roots index) *
      quittingTerminalDeviationDebt reward (tails index) who) atTop (nhds 0) := by
  apply squeeze_zero
    (fun index ↦ mul_nonneg (quittingLiteralRootStackJointSurvival_nonneg _)
      (quittingTerminalDeviationDebt_nonneg reward (tails index) who))
    (fun index ↦ mul_le_mul_of_nonneg_left
      (quittingTerminalDeviationDebt_le_two_mul_bound reward (tails index) who
        (quittingRewardBound reward) (abs_reward_le_quittingRewardBound reward))
      (quittingLiteralRootStackJointSurvival_nonneg _))
  simpa using hjoint.mul_const (2 * quittingRewardBound reward)

/-- At zero joint reach, vanishing playerwise reached ledgers is exactly
vanishing complete behavioral terminal exploitability. -/
theorem terminalExploitability_tendsto_zero_iff_playerLedger_tendsto_zero [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → List (ι → PMF Bool)) (tails : ℕ → (quittingGame reward).BehaviorProfile)
    (hjoint : Tendsto (fun index ↦ quittingLiteralRootStackJointSurvival (roots index))
      atTop (nhds 0)) :
    Tendsto (fun index ↦ quittingTerminalExploitability reward
      (quittingLiteralRootStackProfile reward (roots index) (tails index))) atTop (nhds 0) ↔
    ∀ who, Tendsto (fun index ↦ quittingFiniteWordPlayerCapDefectLedger reward
      (roots index) (tails index) who) atTop (nhds 0) := by
  constructor
  · intro hexploit who
    exact squeeze_zero
      (fun index ↦ quittingFiniteWordPlayerCapDefectLedger_nonneg reward _ _ who)
      (fun index ↦ (quittingFiniteWordPlayerCapDefectLedger_le_debt reward _ _ who).trans
        (quittingTerminalDeviationDebt_le_exploitability reward _ who)) hexploit
  · intro hledger
    have hdebt : ∀ who, Tendsto (fun index ↦ quittingTerminalDeviationDebt reward
        (quittingLiteralRootStackProfile reward (roots index) (tails index)) who)
        atTop (nhds 0) := by
      intro who
      simpa only [quittingTerminalDeviationDebt_literalRootStack_eq_playerLedger_add, add_zero]
        using (hledger who).add (jointSurvival_mul_tailDebt_tendsto_zero
          reward roots tails hjoint who)
    have hsum := tendsto_finsetSum Finset.univ (fun who _ ↦ hdebt who)
    simp only [Finset.sum_const_zero] at hsum
    apply squeeze_zero (fun index ↦ quittingTerminalExploitability_nonneg reward _) _ hsum
    intro index
    rw [quittingTerminalExploitability_eq_max_debt]
    apply QuittingBoundaryHolonomy.finitePlayerMax_le
    intro who
    exact Finset.single_le_sum (fun player _ ↦
      quittingTerminalDeviationDebt_nonneg reward _ player) (Finset.mem_univ who)

/-- The vanishing ledger condition has the existing unrestricted terminal
consumer; it is not asserted for an arbitrary input word producer. -/
theorem exists_uniformPayoff_of_zeroJoint_playerLedgers [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → List (ι → PMF Bool)) (tails : ℕ → (quittingGame reward).BehaviorProfile)
    (hjoint : Tendsto (fun index ↦ quittingLiteralRootStackJointSurvival (roots index))
      atTop (nhds 0))
    (hledger : ∀ who, Tendsto (fun index ↦ quittingFiniteWordPlayerCapDefectLedger reward
      (roots index) (tails index) who) atTop (nhds 0)) :
    ∃ payoff : Payoff ι, (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  have hexploit := (terminalExploitability_tendsto_zero_iff_playerLedger_tendsto_zero
    reward roots tails hjoint).2 hledger
  apply quittingGame_exists_uniformEquilibriumPayoff_of_terminalExploitability_all_errors
  intro error herror
  obtain ⟨index, hindex⟩ := (hexploit.eventually (gt_mem_nhds herror)).exists
  exact ⟨quittingLiteralRootStackProfile reward (roots index) (tails index), hindex⟩

/-- Two positive deleted-clock limits cannot coexist on one zero-joint
sequence. A change of player labels across ranks does not alter this fact. -/
theorem not_two_positive_deletedClock_limits_of_joint_zero
    (roots : ℕ → List (ι → PMF Bool)) (first second : ι) (hne : first ≠ second)
    {firstLimit secondLimit : ℝ} (hfirst : 0 < firstLimit) (hsecond : 0 < secondLimit)
    (hjoint : Tendsto (fun index ↦ quittingLiteralRootStackJointSurvival (roots index))
      atTop (nhds 0))
    (hfirstLimit : Tendsto (fun index ↦ quittingLiteralRootStackOpponentSurvival
      (roots index) first) atTop (nhds firstLimit))
    (hsecondLimit : Tendsto (fun index ↦ quittingLiteralRootStackOpponentSurvival
      (roots index) second) atTop (nhds secondLimit)) : False := by
  have hle := le_of_tendsto_of_tendsto' (hfirstLimit.mul hsecondLimit) hjoint
    (fun index ↦ mul_opponentSurvival_le_jointSurvival_of_ne (roots index) hne)
  exact (not_le_of_gt (mul_pos hfirst hsecond)) hle

/-- Serial blocks screened away from different hosts screen every deepest
tail cap. This leaves the nonnegative outer ledger intact. -/
theorem fullyScreened_append_of_distinct_hosts
    (first second : ℕ → List (ι → PMF Bool)) (firstHost secondHost : ι)
    (hne : firstHost ≠ secondHost)
    (hfirst : ∀ who, who ≠ firstHost → Tendsto
      (fun index ↦ quittingLiteralRootStackOpponentSurvival (first index) who) atTop (nhds 0))
    (hsecond : ∀ who, who ≠ secondHost → Tendsto
      (fun index ↦ quittingLiteralRootStackOpponentSurvival (second index) who) atTop (nhds 0)) :
    IsQuittingFiniteWordFullyScreened (fun index ↦ first index ++ second index) := by
  intro who
  simp only [quittingLiteralRootStackOpponentSurvival_append]
  by_cases hwho : who = firstHost
  · subst who
    apply squeeze_zero
      (fun index ↦ mul_nonneg (quittingLiteralRootStackOpponentSurvival_nonneg _ _)
        (quittingLiteralRootStackOpponentSurvival_nonneg _ _)) _ (hsecond firstHost hne)
    intro index
    exact mul_le_of_le_one_left (quittingLiteralRootStackOpponentSurvival_nonneg _ _)
      (quittingLiteralRootStackOpponentSurvival_le_one _ _)
  · apply squeeze_zero
      (fun index ↦ mul_nonneg (quittingLiteralRootStackOpponentSurvival_nonneg _ _)
        (quittingLiteralRootStackOpponentSurvival_nonneg _ _)) _ (hfirst who hwho)
    intro index
    exact mul_le_of_le_one_right (quittingLiteralRootStackOpponentSurvival_nonneg _ _)
      (quittingLiteralRootStackOpponentSurvival_le_one _ _)

omit [DecidableEq ι] in
/-- Rotating host labels have one fixed label on a strict subsequence. -/
theorem exists_fixedHost_subsequence (host : ℕ → ι) :
    ∃ fixedHost : ι, ∃ select : ℕ → ℕ,
      StrictMono select ∧ ∀ index, host (select index) = fixedHost := by
  exact Math.exists_fixed_label_on_strictMono_subsequence host

/-- Full screening of the deepest tail does not cancel a persistent outer
ledger on those same concatenated profiles. -/
theorem fullyScreened_append_and_not_exploitability_tendsto_zero_of_outerLedger
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (first second : ℕ → List (ι → PMF Bool))
    (tails : ℕ → (quittingGame reward).BehaviorProfile)
    (firstHost secondHost payer : ι) (hne : firstHost ≠ secondHost)
    (hfirst : ∀ who, who ≠ firstHost → Tendsto
      (fun index ↦ quittingLiteralRootStackOpponentSurvival (first index) who) atTop (nhds 0))
    (hsecond : ∀ who, who ≠ secondHost → Tendsto
      (fun index ↦ quittingLiteralRootStackOpponentSurvival (second index) who) atTop (nhds 0))
    {margin : ℝ} (hmargin : 0 < margin)
    (hledger : ∀ᶠ index in atTop, margin ≤
      quittingFiniteWordPlayerCapDefectLedger reward (first index)
        (quittingLiteralRootStackProfile reward (second index) (tails index)) payer) :
    IsQuittingFiniteWordFullyScreened (fun index ↦ first index ++ second index) ∧
    ¬ Tendsto (fun index ↦ quittingTerminalExploitability reward
      (quittingLiteralRootStackProfile reward (first index ++ second index) (tails index)))
      atTop (nhds 0) := by
  refine ⟨fullyScreened_append_of_distinct_hosts first second firstHost secondHost
    hne hfirst hsecond, ?_⟩
  intro hzero
  have hlower : ∀ᶠ index in atTop, margin ≤ quittingTerminalExploitability reward
      (quittingLiteralRootStackProfile reward (first index ++ second index) (tails index)) := by
    filter_upwards [hledger] with index hindex
    exact hindex.trans ((quittingFiniteWordPlayerCapDefectLedger_outer_le_append
      reward (first index) (second index) (tails index) payer).trans
        ((quittingFiniteWordPlayerCapDefectLedger_le_debt reward _ _ payer).trans
          (quittingTerminalDeviationDebt_le_exploitability reward _ payer)))
  exact (not_le_of_gt hmargin) (ge_of_tendsto hzero hlower)

/-- The global lower debt bound survives as an eventual lower bound on the
aggregate ledger, with arbitrarily small loss. -/
theorem eventually_minimum_sub_gap_le_capLedger
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → List (ι → PMF Bool)) (tails : ℕ → (quittingGame reward).BehaviorProfile)
    (minimum : ℝ)
    (hminimum : ∀ profile : (quittingGame reward).BehaviorProfile,
      minimum ≤ quittingTerminalSemanticDebtSum (quittingTerminalSemanticPair reward profile))
    (hjoint : Tendsto (fun index ↦ quittingLiteralRootStackJointSurvival (roots index))
      atTop (nhds 0)) {gap : ℝ} (hgap : 0 < gap) :
    ∀ᶠ index in atTop, minimum - gap ≤
      quittingFiniteWordWeightedCapDefectLedger reward (roots index) (tails index) := by
  have htransport := tendsto_finsetSum Finset.univ
    (fun who _ ↦ jointSurvival_mul_tailDebt_tendsto_zero reward roots tails hjoint who)
  simp only [Finset.sum_const_zero] at htransport
  filter_upwards [htransport.eventually (gt_mem_nhds hgap)] with index hindex
  have hwhole := hminimum
    (quittingLiteralRootStackProfile reward (roots index) (tails index))
  rw [quittingTerminalSemanticDebtSum_literalRootStack_eq_weightedLedger_add] at hwhole
  have hid : quittingCapNashStackContinueProduct (roots index) *
      quittingTerminalSemanticDebtSum (quittingTerminalSemanticPair reward (tails index)) =
      ∑ who, quittingLiteralRootStackJointSurvival (roots index) *
        quittingTerminalDeviationDebt reward (tails index) who := by
    simp only [quittingTerminalSemanticDebtSum, Finset.mul_sum]
    rfl
  rw [hid] at hwhole
  linarith

/-- Literal lower-limit form of the minimum obstruction. -/
theorem minimum_le_liminf_capLedger
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → List (ι → PMF Bool)) (tails : ℕ → (quittingGame reward).BehaviorProfile)
    (minimum : ℝ)
    (hminimum : ∀ profile : (quittingGame reward).BehaviorProfile,
      minimum ≤ quittingTerminalSemanticDebtSum (quittingTerminalSemanticPair reward profile))
    (hjoint : Tendsto (fun index ↦ quittingLiteralRootStackJointSurvival (roots index))
      atTop (nhds 0)) :
    minimum ≤ liminf (fun index ↦ quittingFiniteWordWeightedCapDefectLedger reward
      (roots index) (tails index)) atTop := by
  have hupper : ∀ index, quittingFiniteWordWeightedCapDefectLedger reward
      (roots index) (tails index) ≤ ∑ _who : ι, 2 * quittingRewardBound reward := by
    intro index
    rw [quittingFiniteWordWeightedCapDefectLedger_eq_sum_playerLedger]
    apply Finset.sum_le_sum
    intro who _
    exact (quittingFiniteWordPlayerCapDefectLedger_le_debt reward _ _ who).trans
      (quittingTerminalDeviationDebt_le_two_mul_bound reward _ who
        (quittingRewardBound reward) (abs_reward_le_quittingRewardBound reward))
  apply (le_liminf_iff' (isCoboundedUnder_ge_of_le atTop hupper)
    (isBoundedUnder_of ⟨0, fun index ↦
      quittingFiniteWordWeightedCapDefectLedger_nonneg reward (roots index) (tails index)⟩)).2
  intro value hvalue
  have h := eventually_minimum_sub_gap_le_capLedger reward roots tails minimum hminimum hjoint
    (sub_pos.mpr hvalue)
  simpa only [sub_sub_cancel] using h

/-- Four-player finite pigeonhole fixes one aggregate payer on a strict
subsequence. It does not select a row with a rank-uniform defect. -/
theorem exists_fixed_capLedger_payer_subsequence [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hplayers : Fintype.card ι = 4)
    (roots : ℕ → List (ι → PMF Bool)) (tails : ℕ → (quittingGame reward).BehaviorProfile)
    (minimum : ℝ) (hpositive : 0 < minimum)
    (hminimum : ∀ profile : (quittingGame reward).BehaviorProfile,
      minimum ≤ quittingTerminalSemanticDebtSum (quittingTerminalSemanticPair reward profile))
    (hjoint : Tendsto (fun index ↦ quittingLiteralRootStackJointSurvival (roots index))
      atTop (nhds 0)) :
    (∀ᶠ index in atTop, minimum / 2 ≤
      quittingFiniteWordWeightedCapDefectLedger reward (roots index) (tails index)) ∧
    ∃ who : ι, ∃ select : ℕ → ℕ, StrictMono select ∧ ∀ index,
      minimum / 8 ≤ quittingFiniteWordPlayerCapDefectLedger reward
        (roots (select index)) (tails (select index)) who := by
  have hhalf := eventually_minimum_sub_gap_le_capLedger reward roots tails minimum hminimum hjoint
    (half_pos hpositive)
  have hhalf' : ∀ᶠ index in atTop, minimum / 2 ≤
      quittingFiniteWordWeightedCapDefectLedger reward (roots index) (tails index) := by
    have hid : minimum - minimum / 2 = minimum / 2 := by ring
    simpa only [hid] using hhalf
  refine ⟨hhalf', ?_⟩
  have hpayers : ∀ᶠ index in atTop, ∃ who, minimum / 8 ≤
      quittingFiniteWordPlayerCapDefectLedger reward (roots index) (tails index) who := by
    filter_upwards [hhalf'] with index hindex
    by_contra hnot
    push Not at hnot
    have hsum := Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
      (fun who (_ : who ∈ Finset.univ) ↦ hnot who)
    rw [← quittingFiniteWordWeightedCapDefectLedger_eq_sum_playerLedger] at hsum
    simp only [Finset.sum_const, Finset.card_univ, hplayers, nsmul_eq_mul] at hsum
    norm_num at hsum
    linarith
  obtain ⟨who, hwho⟩ := frequently_exists.mp hpayers.frequently
  obtain ⟨select, hselect, hpay⟩ := extraction_of_frequently_atTop hwho
  exact ⟨who, select, hselect, hpay⟩

/-- The no-uniform-payoff hypothesis itself supplies the positive global
minimum; any displayed literal zero-joint source then supplies a fixed payer. -/
theorem exists_positive_minimum_and_fixed_capLedger_payer_of_no_uniformPayoff [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hplayers : Fintype.card ι = 4)
    (hno : ¬ ∃ payoff : Payoff ι, (quittingGame reward).IsUniformEquilibriumPayoff none payoff)
    (roots : ℕ → List (ι → PMF Bool)) (tails : ℕ → (quittingGame reward).BehaviorProfile)
    (hjoint : Tendsto (fun index ↦ quittingLiteralRootStackJointSurvival (roots index))
      atTop (nhds 0)) :
    ∃ pair ∈ quittingTerminalSemanticCarrier reward,
      0 < quittingTerminalSemanticDebtSum pair ∧
      (∀ candidate ∈ quittingTerminalSemanticCarrier reward,
        quittingTerminalSemanticDebtSum pair ≤ quittingTerminalSemanticDebtSum candidate) ∧
      (∀ᶠ index in atTop, quittingTerminalSemanticDebtSum pair / 2 ≤
        quittingFiniteWordWeightedCapDefectLedger reward (roots index) (tails index)) ∧
      ∃ who : ι, ∃ select : ℕ → ℕ, StrictMono select ∧ ∀ index,
        quittingTerminalSemanticDebtSum pair / 8 ≤ quittingFiniteWordPlayerCapDefectLedger reward
          (roots (select index)) (tails (select index)) who := by
  obtain ⟨pair, _, hpair, _, hmin, ⟨who, hwho⟩, _⟩ :=
    exists_positive_minimumTerminalSemanticDebt_face_of_no_uniformPayoff reward hno
  have hpos : 0 < quittingTerminalSemanticDebtSum pair := by
    apply hwho.trans_le
    exact Finset.single_le_sum (fun player _ ↦
      quittingTerminalSemanticDebt_nonneg_of_mem_carrier reward hpair player) (Finset.mem_univ who)
  obtain ⟨hhalf, hpayer⟩ := exists_fixed_capLedger_payer_subsequence reward hplayers roots tails
    (quittingTerminalSemanticDebtSum pair) hpos
    (fun profile ↦ hmin _ (subset_closure (Set.mem_range_self profile))) hjoint
  exact ⟨pair, hpair, hpos, hmin, hhalf, hpayer⟩

end GameTheory
