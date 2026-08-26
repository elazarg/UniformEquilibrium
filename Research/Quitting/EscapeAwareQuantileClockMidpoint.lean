/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Research.Quitting.EscapeAwareQuantileClockHierarchy

/-!
# Diagonal-midpoint certificates for the escape-aware quantile hierarchy

A terminal-semantic pair can be moved to its diagonal midpoint at a cost of
one half of each coordinate debt. This module packages the resulting generic
zero-lower certificates for actual finite-clock reachable profiles.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.ProbabilityMassFunction Math.Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

def semanticPairDiagonalMidpoint
    (pair : QuittingTerminalSemanticPair ι) :
    QuittingTerminalSemanticPair ι :=
  (fun who => (pair.1 who + pair.2 who) / 2,
    fun who => (pair.1 who + pair.2 who) / 2)

omit [Fintype ι] [DecidableEq ι] in
theorem semanticPairWithin_diagonalMidpoint
    {pair : QuittingTerminalSemanticPair ι} {radius : ℝ}
    (hdebt : ∀ who, 0 ≤ quittingTerminalSemanticDebt pair who ∧
      quittingTerminalSemanticDebt pair who / 2 ≤ radius) :
    semanticPairWithin radius (semanticPairDiagonalMidpoint pair) pair := by
  constructor
  · intro who
    have h := hdebt who
    dsimp [semanticPairDiagonalMidpoint, quittingTerminalSemanticDebt] at h ⊢
    rw [abs_of_nonneg (by linarith)]
    linarith
  · intro who
    have h := hdebt who
    dsimp [semanticPairDiagonalMidpoint, quittingTerminalSemanticDebt] at h ⊢
    rw [abs_of_nonpos (by linarith)]
    linarith

omit [DecidableEq ι] in
theorem semanticExploitability_diagonalMidpoint_eq_zero
    [Nonempty ι] (pair : QuittingTerminalSemanticPair ι) :
    quittingTerminalSemanticExploitability
        (semanticPairDiagonalMidpoint pair) = 0 := by
  apply le_antisymm
  · apply QuittingBoundaryHolonomy.finitePlayerMax_le
    intro who
    simp [semanticPairDiagonalMidpoint, quittingTerminalSemanticDebt]
  · exact quittingTerminalSemanticExploitability_nonneg _

omit [DecidableEq ι] in
theorem quantileClockRadius_anti_of_pos
    {first second : ℕ} (hfirst : 0 < first) (hle : first ≤ second) :
    quantileClockRadius ι second ≤ quantileClockRadius ι first := by
  have hfirstReal : 0 < (first : ℝ) := by exact_mod_cast hfirst
  have hsecondReal : 0 < (second : ℝ) := by
    exact_mod_cast hfirst.trans_le hle
  unfold quantileClockRadius
  apply (div_le_div_iff₀ hsecondReal hfirstReal).2
  have hnum : 0 ≤ (((Fintype.card ι * (Fintype.card ι - 1) : ℕ) : ℝ)) := by
    positivity
  exact mul_le_mul_of_nonneg_left (by exact_mod_cast hle) hnum

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

end GameTheory
