/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Research.Quitting.OneDateNeverNashDebtHierarchy
import UniformEquilibrium.Diagnostics.Quitting.FiniteDeadlineTimingNashDebt

/-!
# Finite-deadline timing Nash debt in the escape-aware hierarchy

The literal finite timing laws from the universal production theorem are
actual finite-clock centers. Their diagonal midpoints therefore give zero
hierarchy objective whenever half of every coordinate debt fits in the final
radius.

For normalized Fin4 rewards, the three-date `24 / 59` debt bound proves that
every positive hierarchy level through `59` has lower value zero. The
hierarchy's compression hypothesis remains explicit in this Research
consumer.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.ProbabilityMassFunction Math.Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

private theorem semanticPair_finiteDeadlineTimingProfile_mem_reachable
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (deadline : ℕ)
    (mixed : ι → PMF (QuittingFiniteDeadlineTimingAction deadline)) :
    quittingTerminalSemanticPair reward
        (quittingFiniteDeadlineTimingProfile reward deadline mixed) ∈
      quittingFiniteClockSemanticReachable reward deadline := by
  let laws : ι → PMF (Option ℕ) := fun who =>
    (quittingFiniteDeadlineTimingLaw (mixed who)).toPMF
  refine ⟨laws, ?_, ?_⟩
  · intro who choice hchoice
    cases choice with
    | none => exact Or.inl rfl
    | some time =>
        by_cases htime : time < deadline
        · exact Or.inr ⟨time, htime, rfl⟩
        · exfalso
          apply hchoice
          exact quittingFiniteDeadlineTimingLaw_some_eq_zero_of_le
            (mixed who) (Nat.le_of_not_gt htime)
  · rfl

private theorem semanticPair_twoDateTimingProfile_mem_reachable
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (mixed : ι → PMF QuittingTwoDateTimingAction) :
    quittingTerminalSemanticPair reward
        (quittingTwoDateTimingProfile reward mixed) ∈
      quittingFiniteClockSemanticReachable reward 2 := by
  let laws : ι → PMF (Option ℕ) := fun who =>
    (quittingTwoDateTimingLaw (mixed who)).toPMF
  refine ⟨laws, ?_, ?_⟩
  · intro who choice hchoice
    cases choice with
    | none => exact Or.inl rfl
    | some time =>
        by_cases htime : time < 2
        · exact Or.inr ⟨time, htime, rfl⟩
        · exfalso
          apply hchoice
          exact quittingTwoDateTimingLaw_some_eq_zero_of_two_le
            (mixed who) (Nat.le_of_not_gt htime)
  · rfl

/-- Any actual finite-clock profile gives a data-sensitive zero hierarchy
certificate whenever its diagonal midpoint fits in the final radius. -/
theorem escapeAwareQuantileClockLower_eq_zero_of_reachableProfile_debt_radius
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hcompression : HasEscapeAwareQuantileClockCompression reward)
    (profile : (quittingGame reward).BehaviorProfile)
    (clockBound : ℕ)
    (hreachable : quittingTerminalSemanticPair reward profile ∈
      quittingFiniteClockSemanticReachable reward clockBound)
    (hsupport : ∀ level, 0 < level →
      clockBound ≤ quantileClockSupport ι level)
    {horizon : ℕ}
    (hradius : ∀ who,
      quittingTerminalDeviationDebt reward profile who / 2 ≤
        quantileClockRadius ι horizon) :
    escapeAwareQuantileClockLower reward hcompression horizon = 0 := by
  let pair := quittingTerminalSemanticPair reward profile
  let midpoint := semanticPairDiagonalMidpoint pair
  have hmidWithin : semanticPairWithin (quantileClockRadius ι horizon)
      midpoint pair := by
    apply semanticPairWithin_diagonalMidpoint
    intro who
    change 0 ≤ quittingTerminalDeviationDebt reward profile who ∧
      quittingTerminalDeviationDebt reward profile who / 2 ≤
        quantileClockRadius ι horizon
    exact ⟨quittingTerminalDeviationDebt_nonneg reward profile who,
      hradius who⟩
  have hmid : midpoint ∈
      (escapeAwareQuantileClockSystem reward hcompression).nestedOuter horizon := by
    intro level hlevel hlevelHorizon
    change Metric.infDist midpoint
        (quittingFiniteClockSemanticCenter reward
          (quantileClockSupport ι level)) ≤ quantileClockRadius ι level
    have hpairCenter : pair ∈ quittingFiniteClockSemanticCenter reward
        (quantileClockSupport ι level) := by
      exact quittingFiniteClockSemanticReachable_mono reward
        (hsupport level hlevel) hreachable
    calc
      Metric.infDist midpoint
          (quittingFiniteClockSemanticCenter reward
            (quantileClockSupport ι level)) ≤ dist midpoint pair :=
        Metric.infDist_le_dist_of_mem hpairCenter
      _ ≤ quantileClockRadius ι horizon := dist_le_of_semanticPairWithin
        (quantileClockRadius_nonneg ι horizon) hmidWithin
      _ ≤ quantileClockRadius ι level :=
        quantileClockRadius_anti_of_pos hlevel hlevelHorizon
  apply le_antisymm
  · unfold escapeAwareQuantileClockLower
    apply csInf_le
    · refine ⟨0, ?_⟩
      rintro value ⟨candidate, -, rfl⟩
      exact quittingTerminalSemanticExploitability_nonneg candidate
    · refine ⟨midpoint, hmid, ?_⟩
      exact semanticExploitability_diagonalMidpoint_eq_zero pair
  · exact escapeAwareQuantileClockLower_nonneg reward hcompression horizon

/-- Scaled-bound counterpart of the actual-profile midpoint certificate. -/
theorem escapeAwareQuantileClockLowerAtBound_eq_zero_of_reachableProfile_debt_radius
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (bound : ℝ) (hbound : 0 ≤ bound)
    (hcompression : HasEscapeAwareQuantileClockCompressionAtBound reward bound)
    (profile : (quittingGame reward).BehaviorProfile)
    (clockBound : ℕ)
    (hreachable : quittingTerminalSemanticPair reward profile ∈
      quittingFiniteClockSemanticReachable reward clockBound)
    (hsupport : ∀ level, 0 < level →
      clockBound ≤ quantileClockSupport ι level)
    {horizon : ℕ}
    (hradius : ∀ who,
      quittingTerminalDeviationDebt reward profile who / 2 ≤
        quantileClockScaledRadius ι bound horizon) :
    escapeAwareQuantileClockLowerAtBound reward bound hbound hcompression
        horizon = 0 := by
  let pair := quittingTerminalSemanticPair reward profile
  let midpoint := semanticPairDiagonalMidpoint pair
  have hmidWithin : semanticPairWithin
      (quantileClockScaledRadius ι bound horizon) midpoint pair := by
    apply semanticPairWithin_diagonalMidpoint
    intro who
    change 0 ≤ quittingTerminalDeviationDebt reward profile who ∧
      quittingTerminalDeviationDebt reward profile who / 2 ≤
        quantileClockScaledRadius ι bound horizon
    exact ⟨quittingTerminalDeviationDebt_nonneg reward profile who,
      hradius who⟩
  have hmid : midpoint ∈
      (escapeAwareQuantileClockSystemAtBound
        reward bound hbound hcompression).nestedOuter horizon := by
    intro level hlevel hlevelHorizon
    change Metric.infDist midpoint
        (quittingFiniteClockSemanticCenter reward
          (quantileClockSupport ι level)) ≤
            quantileClockScaledRadius ι bound level
    have hpairCenter : pair ∈ quittingFiniteClockSemanticCenter reward
        (quantileClockSupport ι level) := by
      exact quittingFiniteClockSemanticReachable_mono reward
        (hsupport level hlevel) hreachable
    calc
      Metric.infDist midpoint
          (quittingFiniteClockSemanticCenter reward
            (quantileClockSupport ι level)) ≤ dist midpoint pair :=
        Metric.infDist_le_dist_of_mem hpairCenter
      _ ≤ quantileClockScaledRadius ι bound horizon :=
        dist_le_of_semanticPairWithin
          (quantileClockScaledRadius_nonneg ι hbound horizon) hmidWithin
      _ ≤ quantileClockScaledRadius ι bound level := by
        unfold quantileClockScaledRadius
        exact mul_le_mul_of_nonneg_left
          (quantileClockRadius_anti_of_pos hlevel hlevelHorizon) hbound
  apply le_antisymm
  · unfold escapeAwareQuantileClockLowerAtBound
    apply csInf_le
    · refine ⟨0, ?_⟩
      rintro value ⟨candidate, -, rfl⟩
      exact quittingTerminalSemanticExploitability_nonneg candidate
    · refine ⟨midpoint, hmid, ?_⟩
      exact semanticExploitability_diagonalMidpoint_eq_zero pair
  · exact escapeAwareQuantileClockLowerAtBound_nonneg
      reward bound hbound hcompression horizon

/-- A finite timing profile gives a data-sensitive zero hierarchy
certificate whenever its diagonal midpoint fits in the final radius. -/
theorem escapeAwareQuantileClockLower_eq_zero_of_finiteDeadlineTiming_debt_radius
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hcompression : HasEscapeAwareQuantileClockCompression reward)
    (deadline : ℕ)
    (mixed : ι → PMF (QuittingFiniteDeadlineTimingAction deadline))
    (hsupport : ∀ level, 0 < level →
      deadline ≤ quantileClockSupport ι level)
    {horizon : ℕ}
    (hradius : ∀ who,
      quittingTerminalDeviationDebt reward
          (quittingFiniteDeadlineTimingProfile reward deadline mixed) who / 2 ≤
        quantileClockRadius ι horizon) :
    escapeAwareQuantileClockLower reward hcompression horizon = 0 := by
  apply escapeAwareQuantileClockLower_eq_zero_of_reachableProfile_debt_radius
    reward hcompression
      (quittingFiniteDeadlineTimingProfile reward deadline mixed) deadline
  · exact semanticPair_finiteDeadlineTimingProfile_mem_reachable
      reward deadline mixed
  · exact hsupport
  · exact hradius

/-- If `12 / 59` times the reward bound fits in the final radius, the
universal three-date producer makes the hierarchy lower value zero. -/
theorem escapeAwareQuantileClockLower_eq_zero_of_threeDate_radius
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hcompression : HasEscapeAwareQuantileClockCompression reward)
    {bound : ℝ} (hbound : 0 ≤ bound)
    (hreward : ∀ terminal player, |reward terminal player| ≤ bound)
    (hsupport : ∀ level, 0 < level → 3 ≤ quantileClockSupport ι level)
    {horizon : ℕ}
    (hradius : bound * (12 / 59) ≤ quantileClockRadius ι horizon) :
    escapeAwareQuantileClockLower reward hcompression horizon = 0 := by
  obtain ⟨mixed, _hnash, _hcertificate, hdebt⟩ :=
    exists_threeDateTimingNash_terminalDebt_le_twentyFour_div_fiftyNine
      reward hbound hreward
  apply
    escapeAwareQuantileClockLower_eq_zero_of_finiteDeadlineTiming_debt_radius
      reward hcompression 3 mixed hsupport
  intro who
  have hwho := (hdebt who).2
  linarith

/-- If one quarter of the reward bound fits in the final radius, the sharp
two-date producer makes the hierarchy lower value zero. -/
theorem escapeAwareQuantileClockLower_eq_zero_of_twoDate_radius
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hcompression : HasEscapeAwareQuantileClockCompression reward)
    {bound : ℝ} (hbound : 0 ≤ bound)
    (hreward : ∀ terminal player, |reward terminal player| ≤ bound)
    (hsupport : ∀ level, 0 < level → 2 ≤ quantileClockSupport ι level)
    {horizon : ℕ}
    (hradius : bound / 4 ≤ quantileClockRadius ι horizon) :
    escapeAwareQuantileClockLower reward hcompression horizon = 0 := by
  obtain ⟨mixed, _hnash, _hcertificate, hdebt⟩ :=
    exists_twoDateTimingNash_terminalDebt_le_half reward hbound hreward
  apply escapeAwareQuantileClockLower_eq_zero_of_reachableProfile_debt_radius
    reward hcompression (quittingTwoDateTimingProfile reward mixed) 2
  · exact semanticPair_twoDateTimingProfile_mem_reachable reward mixed
  · exact hsupport
  · intro who
    have hwho := (hdebt who).2
    linarith

/-- For normalized Fin4 rewards, every positive hierarchy level through `59`
has lower value zero. -/
theorem escapeAwareQuantileClockLower_finFour_eq_zero_of_le_fiftyNine
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hcompression : HasEscapeAwareQuantileClockCompression reward)
    (hreward : ∀ terminal player, |reward terminal player| ≤ 1)
    {horizon : ℕ} (hpositive : 0 < horizon) (hle : horizon ≤ 59) :
    escapeAwareQuantileClockLower reward hcompression horizon = 0 := by
  apply escapeAwareQuantileClockLower_eq_zero_of_threeDate_radius
    reward hcompression (bound := 1) (by norm_num) hreward
  · intro level hlevel
    simp only [quantileClockSupport, Fintype.card_fin]
    omega
  · have hhorizon : 0 < (horizon : ℝ) := by exact_mod_cast hpositive
    simp only [quantileClockRadius, Fintype.card_fin, Nat.reduceSubDiff,
      one_mul]
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < 59) hhorizon).2
    have hleReal : (horizon : ℝ) ≤ 59 := by exact_mod_cast hle
    norm_num
    nlinarith

/-- Canonical normalized Fin4 form of the three-date hierarchy cutoff.  The
compression certificate is supplied by the general normalized-table
constructor, rather than retained as an extra input. -/
theorem escapeAwareQuantileClockLower_finFour_normalized_eq_zero_of_le_fiftyNine
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hreward : ∀ terminal player, |reward terminal player| ≤ 1)
    {horizon : ℕ} (hpositive : 0 < horizon) (hle : horizon ≤ 59) :
    escapeAwareQuantileClockLower reward
        (hasEscapeAwareQuantileClockCompression_of_normalized reward hreward)
        horizon = 0 := by
  exact escapeAwareQuantileClockLower_finFour_eq_zero_of_le_fiftyNine
    reward (hasEscapeAwareQuantileClockCompression_of_normalized reward hreward)
    hreward hpositive hle

/-- Strongest canonical Fin4 cutoff: for an arbitrary reward table, the
reward-bound-scaled hierarchy has lower value zero through level `59`, with
both the bound and compression certificate supplied canonically. -/
theorem
    escapeAwareQuantileClockLowerAtRewardBound_finFour_eq_zero_of_le_fiftyNine
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    {horizon : ℕ} (hpositive : 0 < horizon) (hle : horizon ≤ 59) :
    escapeAwareQuantileClockLowerAtBound reward
        (quittingRewardBound reward) (quittingRewardBound_nonneg reward)
        (hasEscapeAwareQuantileClockCompressionAtRewardBound reward)
        horizon = 0 := by
  obtain ⟨mixed, _hnash, _hcertificate, hdebt⟩ :=
    exists_threeDateTimingNash_terminalDebt_le_twentyFour_div_fiftyNine
      reward (quittingRewardBound_nonneg reward)
      (abs_reward_le_quittingRewardBound reward)
  apply
    escapeAwareQuantileClockLowerAtBound_eq_zero_of_reachableProfile_debt_radius
      reward (quittingRewardBound reward) (quittingRewardBound_nonneg reward)
      (hasEscapeAwareQuantileClockCompressionAtRewardBound reward)
      (quittingFiniteDeadlineTimingProfile reward 3 mixed) 3
  · exact semanticPair_finiteDeadlineTimingProfile_mem_reachable
      reward 3 mixed
  · intro level hlevel
    simp only [quantileClockSupport, Fintype.card_fin]
    omega
  · intro who
    have hwho := (hdebt who).2
    have hhorizon : 0 < (horizon : ℝ) := by exact_mod_cast hpositive
    have hleReal : (horizon : ℝ) ≤ 59 := by exact_mod_cast hle
    simp only [quantileClockScaledRadius, quantileClockRadius,
      Fintype.card_fin, Nat.reduceSubDiff]
    have hradius : 12 / 59 ≤ (12 : ℝ) / horizon := by
      apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < 59) hhorizon).2
      nlinarith
    have hscaled := mul_le_mul_of_nonneg_left hradius
      (quittingRewardBound_nonneg reward)
    nlinarith

/-- The sharp two-date producer independently proves zero lower value through
level `48` for normalized Fin4 rewards. -/
theorem escapeAwareQuantileClockLower_finFour_eq_zero_of_le_fortyEight
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hcompression : HasEscapeAwareQuantileClockCompression reward)
    (hreward : ∀ terminal player, |reward terminal player| ≤ 1)
    {horizon : ℕ} (hpositive : 0 < horizon) (hle : horizon ≤ 48) :
    escapeAwareQuantileClockLower reward hcompression horizon = 0 := by
  apply escapeAwareQuantileClockLower_eq_zero_of_twoDate_radius
    reward hcompression (bound := 1) (by norm_num) hreward
  · intro level hlevel
    simp only [quantileClockSupport, Fintype.card_fin]
    omega
  · have hhorizon : 0 < (horizon : ℝ) := by exact_mod_cast hpositive
    simp only [quantileClockRadius, Fintype.card_fin, Nat.reduceSubDiff,
      one_div]
    apply (le_div_iff₀ hhorizon).2
    have hleReal : (horizon : ℝ) ≤ 48 := by exact_mod_cast hle
    norm_num
    nlinarith

end GameTheory
