import UniformEquilibrium.Diagnostics.Quitting.ScreenedMembershipDebt
import MathUE.PMFProduct.Bool
import MathUE.ProbabilityMassFunction.BoundedSupportAverage

/-!
# A supported pure vertex from saturated membership gaps

The product law is used only to select an actual deterministic vertex.
Every directed gap on its support is zero or two. Total full debt below two
forces a supported draw with no losing owner. The result is generic in the
finite player type; the four-player strict-half bound is a later input.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Every supported draw preserves a sure Quit marginal. -/
theorem quittingRoot_supported_action_eq_true_of_sure
    (root : ι → PMF Bool) (who : ι) (hsure : (root who true).toReal = 1)
    (action : ι → Bool) (hsupport : action ∈ (pmfPi root).support) :
    action who = true := by
  apply eq_of_mem_support_pmfPi_update_pure root who true
  rwa [← eq_pure_true_of_true_toReal_eq_one (root who) hsure, Function.update_eq_self]

/-- A pure root with a quitting opponent has exactly its losing directed gap as full debt. -/
theorem quittingTerminalDeviationDebt_pureRoot_eq_losingMembershipGap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (action : ι → Bool) (who : ι) (preferred : Bool) {opponent : ι}
    (hne : opponent ≠ who) (hquit : action opponent = true)
    (hgap : 0 ≤ quittingDirectedMembershipGap reward who preferred action) :
    quittingTerminalDeviationDebt reward
        (quittingOneDateThenNeverProfile reward (fun player => PMF.pure (action player))) who =
      if action who = preferred then 0
      else quittingDirectedMembershipGap reward who preferred action := by
  have hsure : ((fun player => PMF.pure (action player)) opponent true).toReal = 1 := by
    simp [hquit]
  have hbest : 0 ≤ expect (pmfPi (fun player => PMF.pure (action player)))
      (quittingDirectedMembershipGap reward who preferred) := by
    simpa only [pmfPi_pure, expect_pure] using hgap
  simpa only [pmfPi_pure, expect_pure] using
    quittingTerminalDeviationDebt_oneDateThenNever_eq_expect_losingMembershipGap
      reward (fun player => PMF.pure (action player)) who preferred hne hsure hbest

/-- Count the owners playing the losing action on an edge whose directed gap is two. -/
def quittingSaturatedLosingOwnerCount
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (preferred action : ι → Bool) : ℕ :=
  (Finset.univ.filter (fun who => action who ≠ preferred who ∧
    quittingDirectedMembershipGap reward who (preferred who) action = 2)).card

theorem quittingSaturatedLosingOwnerCount_le_card
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (preferred action : ι → Bool) :
    quittingSaturatedLosingOwnerCount reward preferred action ≤ Fintype.card ι := by
  exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq Finset.card_univ

/-- The losing-gap sum is exactly twice the integer count at a saturated draw. -/
theorem sum_losingMembershipGap_eq_two_mul_count
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (preferred action : ι → Bool)
    (hsaturated : ∀ who,
      quittingDirectedMembershipGap reward who (preferred who) action = 0 ∨
        quittingDirectedMembershipGap reward who (preferred who) action = 2) :
    (∑ who, if action who = preferred who then 0
      else quittingDirectedMembershipGap reward who (preferred who) action) =
      2 * (quittingSaturatedLosingOwnerCount reward preferred action : ℝ) := by
  have hcount : (quittingSaturatedLosingOwnerCount reward preferred action : ℝ) =
      ∑ who, if action who ≠ preferred who ∧
          quittingDirectedMembershipGap reward who (preferred who) action = 2
        then (1 : ℝ) else 0 := by
    rw [quittingSaturatedLosingOwnerCount, Finset.card_eq_sum_ones]
    simp only [Nat.cast_sum, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro who _
    split_ifs <;> norm_num
  rw [hcount, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro who _
  by_cases haction : action who = preferred who
  · simp [haction]
  · rcases hsaturated who with hzero | htwo
    · simp [haction, hzero]
    · simp [haction, htwo]

/-- Positive-probability saturated pure draws contain an exact full-debt-zero vertex
when the original product root has total full debt below two. -/
theorem exists_supported_pureRoot_zeroDebt_of_saturatedGaps
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (preferred : ι → Bool)
    (hscreen : ∀ who, ∃ opponent, opponent ≠ who ∧ (root opponent true).toReal = 1)
    (hsaturated : ∀ who action, action ∈ (pmfPi root).support →
      quittingDirectedMembershipGap reward who (preferred who) action = 0 ∨
        quittingDirectedMembershipGap reward who (preferred who) action = 2)
    (hdebt : (∑ who, quittingTerminalDeviationDebt reward
      (quittingOneDateThenNeverProfile reward root) who) < 2) :
    ∃ action ∈ (pmfPi root).support,
      ∀ who, quittingTerminalDeviationDebt reward
        (quittingOneDateThenNeverProfile reward
          (fun player => PMF.pure (action player))) who = 0 := by
  let losing : ι → (ι → Bool) → ℝ := fun who action =>
    if action who = preferred who then 0
    else quittingDirectedMembershipGap reward who (preferred who) action
  have hnonneg (who : ι) (action : ι → Bool) (hsupport : action ∈ (pmfPi root).support) :
      0 ≤ quittingDirectedMembershipGap reward who (preferred who) action := by
    rcases hsaturated who action hsupport with hzero | htwo
    · rw [hzero]
    · rw [htwo]
      norm_num
  have hdebtIdentity (who : ι) : quittingTerminalDeviationDebt reward
        (quittingOneDateThenNeverProfile reward root) who = expect (pmfPi root) (losing who) := by
    obtain ⟨opponent, hne, hsure⟩ := hscreen who
    exact quittingTerminalDeviationDebt_oneDateThenNever_eq_expect_of_supported_coherent
      reward root who (preferred who) hne hsure (hnonneg who)
  have hexpectSum : expect (pmfPi root) (fun action => ∑ who, losing who action) =
      ∑ who, quittingTerminalDeviationDebt reward
        (quittingOneDateThenNeverProfile reward root) who := by
    simp_rw [hdebtIdentity]
    exact (expect_sum_comm (pmfPi root) losing).symm
  have hpointwise (action : ι → Bool) (hsupport : action ∈ (pmfPi root).support) :
      (∑ who, losing who action) =
        2 * (quittingSaturatedLosingOwnerCount reward preferred action : ℝ) :=
    sum_losingMembershipGap_eq_two_mul_count reward preferred action
      (fun who => hsaturated who action hsupport)
  have hcountExpectation : 2 * expect (pmfPi root)
      (fun action => (quittingSaturatedLosingOwnerCount reward preferred action : ℝ)) < 2 := by
    rw [← expect_const_mul]
    rw [← Math.ProbabilityMassFunction.expect_congr_on_support
      (pmfPi root) (fun action => ∑ who, losing who action)
      (fun action => 2 * (quittingSaturatedLosingOwnerCount reward preferred action : ℝ))
      hpointwise]
    rwa [hexpectSum]
  have hbound (action : ι → Bool) :
      |(quittingSaturatedLosingOwnerCount reward preferred action : ℝ)| ≤
        (Fintype.card ι : ℝ) := by
    rw [abs_of_nonneg (Nat.cast_nonneg _)]
    exact_mod_cast quittingSaturatedLosingOwnerCount_le_card reward preferred action
  obtain ⟨action, hsupport, hsmall⟩ :=
    Math.ProbabilityMassFunction.exists_mem_support_le_expect (pmfPi root)
      (fun action => (quittingSaturatedLosingOwnerCount reward preferred action : ℝ)) hbound
  have hcountLt : (quittingSaturatedLosingOwnerCount reward preferred action : ℝ) < 1 := by
    linarith
  have hcountZero : quittingSaturatedLosingOwnerCount reward preferred action = 0 := by
    have hnat : quittingSaturatedLosingOwnerCount reward preferred action < 1 := by
      exact_mod_cast hcountLt
    omega
  refine ⟨action, hsupport, ?_⟩
  intro who
  obtain ⟨opponent, hne, hsure⟩ := hscreen who
  rw [quittingTerminalDeviationDebt_pureRoot_eq_losingMembershipGap
    reward action who (preferred who) hne
      (quittingRoot_supported_action_eq_true_of_sure root opponent hsure action hsupport)
      (hnonneg who action hsupport)]
  by_cases haction : action who = preferred who
  · rw [if_pos haction]
  · rw [if_neg haction]
    rcases hsaturated who action hsupport with hzero | htwo
    · exact hzero
    · have hmem : who ∈ Finset.univ.filter (fun player => action player ≠ preferred player ∧
          quittingDirectedMembershipGap reward player (preferred player) action = 2) := by
        simp [haction, htwo]
      have hempty := Finset.card_eq_zero.mp hcountZero
      rw [hempty] at hmem
      exact (Finset.notMem_empty who hmem).elim

end GameTheory
