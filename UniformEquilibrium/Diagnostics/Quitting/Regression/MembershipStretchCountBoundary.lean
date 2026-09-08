import UniformEquilibrium.Diagnostics.Quitting.SaturatedMembershipPureVertex
import MathUE.PMFProduct.FiniteFubini

/-!
# Complete-table boundaries for the saturated losing-owner count

The successful example and the critical-half example are literal four-player
reward tables. Every unspecified owner membership pair and every own singleton
is zero. The displayed pure and mixed debts use actual root-then-Never profiles
and unrestricted behavioral-deviation caps, not only a local action game.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.PMFProduct

/-- The two supplied examples differ only in these preferred directions and active pairs. -/
def membershipCountExamplePreferred (critical : Bool) : Fin 4 → Bool :=
  ![false, false, true, !critical]

def membershipCountExampleActiveOpponents (critical : Bool) : Fin 4 → Finset (Fin 4) :=
  if critical then ![{1, 2}, {0, 2, 3}, {0, 1}, {0, 1}]
  else ![{1}, {0}, {0, 1}, {0, 1}]

/-- Assign plus one to the preferred endpoint and minus one to its opposite on
the specified owner pair; assign zero to every other reward coordinate. -/
def membershipCountExampleReward (critical : Bool)
    (terminal : {S : Finset (Fin 4) // S.Nonempty}) (who : Fin 4) : ℝ :=
  if terminal.1.erase who = membershipCountExampleActiveOpponents critical who then
    if decide (who ∈ terminal.1) = membershipCountExamplePreferred critical who then 1 else -1
  else 0

theorem membershipCountExampleReward_abs_le_one (critical : Bool)
    (terminal : {S : Finset (Fin 4) // S.Nonempty}) (who : Fin 4) :
    |membershipCountExampleReward critical terminal who| ≤ 1 := by
  unfold membershipCountExampleReward
  split_ifs <;> norm_num

theorem membershipCountExampleReward_ownSingleton_eq_zero (critical : Bool) (who : Fin 4) :
    membershipCountExampleReward critical (quittingSingletonTerminal who) who = 0 := by
  fin_cases who <;> cases critical <;>
    simp +decide [membershipCountExampleReward]

def membershipCountExampleGap (critical : Bool) (who : Fin 4) (left right : Bool) : ℝ :=
  if (if critical then ![left && !right, left && right, !right, !left]
      else ![!left && !right, !left && !right, !right, !left]) who then 2 else 0

theorem membershipCountExample_directedGap (critical : Bool) (who : Fin 4) (left right : Bool) :
    quittingDirectedMembershipGap (membershipCountExampleReward critical) who
      (membershipCountExamplePreferred critical who) ![true, true, left, right] =
        membershipCountExampleGap critical who left right := by
  fin_cases who <;> cases left <;> cases right <;> cases critical <;>
    simp +decide [quittingDirectedMembershipGap, quittingRootPayoff,
      membershipCountExampleReward, membershipCountExampleGap]
  all_goals norm_num

def membershipCountExamplePureDebt
    (critical : Bool) (who : Fin 4) (left right : Bool) : ℝ :=
  if (if critical then ![left && !right, left && right, !left && !right, !left && right]
      else ![!left && !right, !left && !right, !left && !right, !left && !right]) who
    then 2 else 0

theorem membershipCountExample_pureRoot_debt
    (critical : Bool) (who : Fin 4) (left right : Bool) :
    quittingTerminalDeviationDebt (membershipCountExampleReward critical)
      (quittingOneDateThenNeverProfile (membershipCountExampleReward critical)
        (fun player => PMF.pure (![true, true, left, right] player))) who =
          membershipCountExamplePureDebt critical who left right := by
  have hnonneg : 0 ≤ quittingDirectedMembershipGap (membershipCountExampleReward critical) who
      (membershipCountExamplePreferred critical who) ![true, true, left, right] := by
    rw [membershipCountExample_directedGap]
    unfold membershipCountExampleGap
    split_ifs <;> norm_num
  have hscreen : ∃ opponent : Fin 4, opponent ≠ who ∧
      ![true, true, left, right] opponent = true := by
    by_cases hwho : who = 0
    · subst who
      exact ⟨1, by decide, rfl⟩
    · exact ⟨0, Ne.symm hwho, rfl⟩
  obtain ⟨opponent, hne, hquit⟩ := hscreen
  rw [quittingTerminalDeviationDebt_pureRoot_eq_losingMembershipGap
    (membershipCountExampleReward critical) _ who
      (membershipCountExamplePreferred critical who) hne hquit hnonneg,
    membershipCountExample_directedGap]
  fin_cases who <;> cases left <;> cases right <;> cases critical <;>
    simp [membershipCountExampleGap, membershipCountExamplePreferred,
      membershipCountExamplePureDebt]

theorem membershipCountExample_allNever_debt_eq_zero (critical : Bool) (who : Fin 4) :
    quittingTerminalDeviationDebt (membershipCountExampleReward critical)
      (quittingAlwaysContinueProfile (membershipCountExampleReward critical)) who = 0 := by
  rw [quittingTerminalDeviationDebt,
    quittingContinuationBestResponseValue_quittingAlwaysContinueProfile,
    quittingTerminalPayoff_quittingAlwaysContinue,
    membershipCountExampleReward_ownSingleton_eq_zero]
  norm_num

def membershipCountExampleRoot (critical : Bool) : Fin 4 → PMF Bool :=
  ![PMF.pure true, PMF.pure true,
    bernoulliBoolEquiv ⟨(1 : ℝ) / 2, by constructor <;> norm_num⟩,
    if critical then bernoulliBoolEquiv ⟨(1 : ℝ) / 2, by constructor <;> norm_num⟩
    else bernoulliBoolEquiv ⟨(3 : ℝ) / 4, by constructor <;> norm_num⟩]

/-- Exact four-vertex expectation of the prescribed independent root. -/
theorem membershipCountExampleRoot_expect (critical : Bool) (observable : (Fin 4 → Bool) → ℝ) :
    expect (pmfPi (membershipCountExampleRoot critical)) observable =
      if critical then (1 : ℝ) / 4 *
        (observable ![true, true, false, false] + observable ![true, true, false, true] +
          observable ![true, true, true, false] + observable ![true, true, true, true])
      else (1 : ℝ) / 8 * observable ![true, true, false, false] +
        (3 : ℝ) / 8 * observable ![true, true, false, true] +
        (1 : ℝ) / 8 * observable ![true, true, true, false] +
        (3 : ℝ) / 8 * observable ![true, true, true, true] := by
  rw [expect_pmfPi_fin4]
  cases critical <;>
    simp [membershipCountExampleRoot, expect_eq_sum]
  all_goals ring

theorem membershipCountExample_mixedRoot_debt (critical : Bool) (who : Fin 4) :
    quittingTerminalDeviationDebt (membershipCountExampleReward critical)
      (quittingOneDateThenNeverProfile (membershipCountExampleReward critical)
        (membershipCountExampleRoot critical)) who =
          if critical then (1 : ℝ) / 2 else (1 : ℝ) / 4 := by
  have hbest : 0 ≤ expect (pmfPi (membershipCountExampleRoot critical))
      (quittingDirectedMembershipGap (membershipCountExampleReward critical) who
        (membershipCountExamplePreferred critical who)) := by
    rw [membershipCountExampleRoot_expect]
    simp_rw [membershipCountExample_directedGap]
    fin_cases who <;> cases critical <;> norm_num [membershipCountExampleGap]
  have hscreen : ∃ opponent : Fin 4, opponent ≠ who ∧
      (membershipCountExampleRoot critical opponent true).toReal = 1 := by
    by_cases hwho : who = 0
    · subst who
      exact ⟨1, by decide, by simp [membershipCountExampleRoot]⟩
    · exact ⟨0, Ne.symm hwho, by simp [membershipCountExampleRoot]⟩
  obtain ⟨opponent, hne, hsure⟩ := hscreen
  rw [quittingTerminalDeviationDebt_oneDateThenNever_eq_expect_losingMembershipGap
    (membershipCountExampleReward critical) (membershipCountExampleRoot critical) who
      (membershipCountExamplePreferred critical who) hne hsure hbest,
    membershipCountExampleRoot_expect]
  simp_rw [membershipCountExample_directedGap]
  fin_cases who <;> cases critical <;>
    norm_num [membershipCountExampleGap, membershipCountExamplePreferred]

theorem membershipCountExample_pure_losingOwnerCount (critical left right : Bool) :
    (quittingSaturatedLosingOwnerCount (membershipCountExampleReward critical)
      (membershipCountExamplePreferred critical) ![true, true, left, right] : ℝ) =
        if critical then 1 else if !left && !right then 4 else 0 := by
  have hsaturated (who : Fin 4) :
      quittingDirectedMembershipGap (membershipCountExampleReward critical) who
        (membershipCountExamplePreferred critical who) ![true, true, left, right] = 0 ∨
      quittingDirectedMembershipGap (membershipCountExampleReward critical) who
        (membershipCountExamplePreferred critical who) ![true, true, left, right] = 2 := by
    rw [membershipCountExample_directedGap]
    unfold membershipCountExampleGap
    split_ifs <;> simp
  have h := sum_losingMembershipGap_eq_two_mul_count (membershipCountExampleReward critical)
    (membershipCountExamplePreferred critical) ![true, true, left, right] hsaturated
  simp_rw [membershipCountExample_directedGap] at h
  cases critical <;> cases left <;> cases right <;>
    norm_num [Fin.sum_univ_succ, membershipCountExamplePreferred, membershipCountExampleGap] at h ⊢
  all_goals linarith

theorem membershipCountExample_expected_losingOwnerCount (critical : Bool) :
    expect (pmfPi (membershipCountExampleRoot critical))
      (fun action => (quittingSaturatedLosingOwnerCount (membershipCountExampleReward critical)
        (membershipCountExamplePreferred critical) action : ℝ)) =
          if critical then 1 else (1 : ℝ) / 2 := by
  rw [membershipCountExampleRoot_expect]
  simp_rw [membershipCountExample_pure_losingOwnerCount]
  cases critical <;> norm_num

/-- Every supported optional vertex other than `00` has zero full debt in the successful table. -/
theorem membershipCountExample_successful_pureRoot_zeroDebt (left right : Bool)
    (hnotBothFalse : left = true ∨ right = true) (who : Fin 4) :
    quittingTerminalDeviationDebt (membershipCountExampleReward false)
      (quittingOneDateThenNeverProfile (membershipCountExampleReward false)
        (fun player => PMF.pure (![true, true, left, right] player))) who = 0 := by
  rw [membershipCountExample_pureRoot_debt]
  fin_cases who <;> cases left <;> cases right <;>
    simp_all [membershipCountExamplePureDebt]

/-- The critical table has exactly the four pure debt vectors in the packet. -/
theorem membershipCountExample_critical_pureDebtVector (left right : Bool) :
    (fun who => quittingTerminalDeviationDebt (membershipCountExampleReward true)
      (quittingOneDateThenNeverProfile (membershipCountExampleReward true)
        (fun player => PMF.pure (![true, true, left, right] player))) who) =
      if left then
        (if right then ![0, 2, 0, 0] else ![2, 0, 0, 0])
      else (if right then ![0, 0, 0, 2] else ![0, 0, 2, 0]) := by
  funext who
  rw [membershipCountExample_pureRoot_debt]
  fin_cases who <;> cases left <;> cases right <;> simp [membershipCountExamplePureDebt]

/-- The critical-half mixed root ties every debt at one half, but every supported
deterministic root has a nonzero full debt. Thus the strict count threshold matters. -/
theorem membershipCountExample_critical_half_does_not_force_supported_zeroDebt :
    (∀ who, quittingTerminalDeviationDebt (membershipCountExampleReward true)
      (quittingOneDateThenNeverProfile (membershipCountExampleReward true)
        (membershipCountExampleRoot true)) who = (1 : ℝ) / 2) ∧
    ¬∃ action ∈ (pmfPi (membershipCountExampleRoot true)).support,
      ∀ who, quittingTerminalDeviationDebt (membershipCountExampleReward true)
        (quittingOneDateThenNeverProfile (membershipCountExampleReward true)
          (fun player => PMF.pure (action player))) who = 0 := by
  constructor
  · intro who
    exact membershipCountExample_mixedRoot_debt true who
  · rintro ⟨action, hsupport, hzero⟩
    have hfirst : action 0 = true := quittingRoot_supported_action_eq_true_of_sure
      (membershipCountExampleRoot true) 0 (by simp [membershipCountExampleRoot]) action hsupport
    have hsecond : action 1 = true := quittingRoot_supported_action_eq_true_of_sure
      (membershipCountExampleRoot true) 1 (by simp [membershipCountExampleRoot]) action hsupport
    have haction : action = ![true, true, action 2, action 3] := by
      funext who
      fin_cases who
      · exact hfirst
      · exact hsecond
      · rfl
      · rfl
    have hsum : (∑ who, quittingTerminalDeviationDebt (membershipCountExampleReward true)
        (quittingOneDateThenNeverProfile (membershipCountExampleReward true)
          (fun player => PMF.pure (action player))) who) = 2 := by
      rw [haction]
      simp_rw [membershipCountExample_pureRoot_debt]
      cases action 2 <;> cases action 3 <;>
        norm_num [Fin.sum_univ_succ, membershipCountExamplePureDebt]
    simp_rw [hzero] at hsum
    norm_num at hsum

/-- Actual all-Never strictly improves the maximum debt of either displayed mixed root. -/
theorem membershipCountExample_allNever_strictly_better (critical : Bool) :
    quittingTerminalExploitability (membershipCountExampleReward critical)
      (quittingAlwaysContinueProfile (membershipCountExampleReward critical)) <
    quittingTerminalExploitability (membershipCountExampleReward critical)
      (quittingOneDateThenNeverProfile (membershipCountExampleReward critical)
        (membershipCountExampleRoot critical)) := by
  have hnever : quittingTerminalExploitability (membershipCountExampleReward critical)
      (quittingAlwaysContinueProfile (membershipCountExampleReward critical)) ≤ 0 := by
    rw [quittingTerminalExploitability_eq_max_debt]
    apply QuittingBoundaryHolonomy.finitePlayerMax_le
    intro who
    exact le_of_eq (membershipCountExample_allNever_debt_eq_zero critical who)
  have hpositive : 0 < quittingTerminalDeviationDebt (membershipCountExampleReward critical)
      (quittingOneDateThenNeverProfile (membershipCountExampleReward critical)
        (membershipCountExampleRoot critical)) 0 := by
    rw [membershipCountExample_mixedRoot_debt]
    cases critical <;> norm_num
  exact hnever.trans_lt (hpositive.trans_le
    (quittingTerminalDeviationDebt_le_exploitability _ _ 0))

theorem membershipCountExample_mixedRoot_not_global_minimum (critical : Bool) :
    ¬∀ candidate : (quittingGame (membershipCountExampleReward critical)).BehaviorProfile,
      quittingTerminalExploitability (membershipCountExampleReward critical)
        (quittingOneDateThenNeverProfile (membershipCountExampleReward critical)
          (membershipCountExampleRoot critical)) ≤
      quittingTerminalExploitability (membershipCountExampleReward critical) candidate := by
  intro hminimum
  exact (not_le_of_gt (membershipCountExample_allNever_strictly_better critical))
    (hminimum (quittingAlwaysContinueProfile (membershipCountExampleReward critical)))

end GameTheory
