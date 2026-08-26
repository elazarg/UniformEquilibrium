/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Research.Quitting.EscapeAwareQuantileClockHierarchy
import UniformEquilibrium.Quitting.Root.OneDateNeverNashDebt

/-!
# One-date Nash debt in the escape-aware hierarchy

The diagonal midpoint of the universal one-date-then-Never semantic pair has
zero debt. Whenever half of the universal debt bound fits inside the final
quantile-clock radius, the same midpoint belongs to every preceding outer
neighborhood, so the nested lower value is exactly zero.

This Research consumer retains the hierarchy's explicit conditional
compression hypothesis. The unconditional all-behavior debt theorem remains
in the production root module.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.ProbabilityMassFunction Math.Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

private theorem semanticPair_oneDateThenNever_mem_reachable_one
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) :
    quittingTerminalSemanticPair reward
        (quittingOneDateThenNeverProfile reward root) ∈
      quittingFiniteClockSemanticReachable reward 1 := by
  let word : Fin 1 → QuittingRootSimplex ι := fun _ player =>
    stdSimplexEquiv (root player)
  have hprofile : quittingFiniteClockWordProfile reward 1 word =
      quittingOneDateThenNeverProfile reward root := by
    funext player time history
    cases time with
    | zero =>
        simp [quittingFiniteClockWordProfile, quittingRootSequenceProfile,
          quittingFiniteClockRoots, word, quittingOneDateThenNeverProfile,
          quittingRootOfSimplex]
    | succ time =>
        simp [quittingFiniteClockWordProfile, quittingRootSequenceProfile,
          quittingFiniteClockRoots, quittingOneDateThenNeverProfile,
          quittingRootThenContinuationProfile, quittingAlwaysContinueProfile,
          StochasticGame.stationaryBehaviorProfile, quittingAllContinueRoot]
        rfl
  rw [← hprofile,
    quittingTerminalSemanticPair_finiteClockWordProfile_eq_fold]
  exact quittingFiniteClockSemanticFold_mem_reachable reward 1 word

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

/-- A selected one-date root gives an exact data-sensitive hierarchy
certificate: if half of each actual player debt fits in the final radius, the
lower value is zero. No root-selection or maximum-debt hypothesis is hidden. -/
theorem escapeAwareQuantileClockLower_eq_zero_of_oneDateRoot_debt_radius
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hcompression : HasEscapeAwareQuantileClockCompression reward)
    (root : ι → PMF Bool) {horizon : ℕ}
    (hradius : ∀ who,
      quittingTerminalDeviationDebt reward
          (quittingOneDateThenNeverProfile reward root) who / 2 ≤
        quantileClockRadius ι horizon) :
    escapeAwareQuantileClockLower reward hcompression horizon = 0 := by
  let pair := quittingTerminalSemanticPair reward
    (quittingOneDateThenNeverProfile reward root)
  let midpoint := semanticPairDiagonalMidpoint pair
  have hpairOne : pair ∈ quittingFiniteClockSemanticReachable reward 1 := by
    exact semanticPair_oneDateThenNever_mem_reachable_one reward root
  have hmidWithin : semanticPairWithin (quantileClockRadius ι horizon)
      midpoint pair := by
    apply semanticPairWithin_diagonalMidpoint
    intro who
    change 0 ≤ quittingTerminalDeviationDebt reward
          (quittingOneDateThenNeverProfile reward root) who ∧
        quittingTerminalDeviationDebt reward
            (quittingOneDateThenNeverProfile reward root) who / 2 ≤
          quantileClockRadius ι horizon
    exact ⟨quittingTerminalDeviationDebt_nonneg reward
      (quittingOneDateThenNeverProfile reward root) who, hradius who⟩
  have hmid : midpoint ∈
      (escapeAwareQuantileClockSystem reward hcompression).nestedOuter horizon := by
    intro level hlevel hlevelHorizon
    change Metric.infDist midpoint
        (quittingFiniteClockSemanticCenter reward
          (quantileClockSupport ι level)) ≤ quantileClockRadius ι level
    have hsupport : 1 ≤ quantileClockSupport ι level := by
      simp [quantileClockSupport]
    have hpairCenter : pair ∈ quittingFiniteClockSemanticCenter reward
        (quantileClockSupport ι level) := by
      exact quittingFiniteClockSemanticReachable_mono reward hsupport hpairOne
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

/-- If half the universal one-date debt bound fits in the final hierarchy
radius, the escape-aware lower value is exactly zero. -/
theorem escapeAwareQuantileClockLower_eq_zero_of_oneDate_radius
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hcompression : HasEscapeAwareQuantileClockCompression reward)
    {bound : ℝ} (hbound_nonneg : 0 ≤ bound)
    (hreward : ∀ terminal player, |reward terminal player| ≤ bound)
    {horizon : ℕ} (hradius : bound / 3 ≤ quantileClockRadius ι horizon) :
    escapeAwareQuantileClockLower reward hcompression horizon = 0 := by
  obtain ⟨root, -, hdebt⟩ :=
    exists_oneDateThenNever_terminalDebt_le_two_thirds
      reward hbound_nonneg hreward
  apply escapeAwareQuantileClockLower_eq_zero_of_oneDateRoot_debt_radius
    reward hcompression root
  intro who
  have hwho := (hdebt who).2
  linarith

/-- For four players with rewards bounded by one, every positive hierarchy
level through `36` has lower value zero. -/
theorem escapeAwareQuantileClockLower_finFour_eq_zero_of_le_thirtySix
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hcompression : HasEscapeAwareQuantileClockCompression reward)
    (hreward : ∀ terminal player, |reward terminal player| ≤ 1)
    {horizon : ℕ} (hpositive : 0 < horizon) (hle : horizon ≤ 36) :
    escapeAwareQuantileClockLower reward hcompression horizon = 0 := by
  apply escapeAwareQuantileClockLower_eq_zero_of_oneDate_radius
    reward hcompression (bound := 1) (by norm_num) hreward
  have hhorizon : 0 < (horizon : ℝ) := by exact_mod_cast hpositive
  simp only [quantileClockRadius, Fintype.card_fin, Nat.reduceSubDiff]
  apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < 3) hhorizon).2
  norm_num
  exact_mod_cast hle

/-- For normalized four-player rewards, the canonical common-quantile
compression discharges the hierarchy premise in the universal level-`36`
zero-lower result. -/
theorem escapeAwareQuantileClockLower_finFour_normalized_eq_zero_of_le_thirtySix
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hreward : ∀ terminal player, |reward terminal player| ≤ 1)
    {horizon : ℕ} (hpositive : 0 < horizon) (hle : horizon ≤ 36) :
    escapeAwareQuantileClockLower reward
      (hasEscapeAwareQuantileClockCompression_of_normalized reward hreward)
      horizon = 0 :=
  escapeAwareQuantileClockLower_finFour_eq_zero_of_le_thirtySix
    reward
    (hasEscapeAwareQuantileClockCompression_of_normalized reward hreward)
    hreward hpositive hle

end GameTheory
