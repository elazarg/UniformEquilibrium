/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.Topology.NestedOuterApproximation
import Research.Quitting.EscapeAwareQuantileClockTransport

/-!
# Escape-aware finite-clock outer hierarchy

This module owns the topological consequences of active common-quantile
compression: literal finite-clock density in the terminal semantic carrier,
continuous-objective infimum identities, nested outer systems, certified
lower/upper values, quantitative brackets, convergence, and Fin4
specializations.

Finite-clock reconstruction lives in
Research.Quitting.FiniteClockTerminalSemantics; payoff and cap transport live
in Research.Quitting.EscapeAwareQuantileClockTransport. This file does not
encode a semialgebraic or real-closed-field presentation of the finite centers.
-/

noncomputable section

namespace GameTheory

open Filter Set Math.Probability Math.ProbabilityMassFunction Math.PMFProduct Math.Topology
open QuittingBoundaryHolonomy
open QuittingSureSetOwnerRepair
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem dist_le_of_semanticPairWithin
    {radius : ℝ} (hradius : 0 ≤ radius)
    {first second : QuittingTerminalSemanticPair ι}
    (hwithin : semanticPairWithin radius first second) :
    dist first second ≤ radius := by
  rw [Prod.dist_eq]
  apply max_le
  · rw [dist_pi_le_iff hradius]
    intro who
    simpa only [Real.dist_eq] using hwithin.1 who
  · rw [dist_pi_le_iff hradius]
    intro who
    simpa only [Real.dist_eq] using hwithin.2 who

omit [DecidableEq ι] in
theorem semanticPairWithin_dist
    (first second : QuittingTerminalSemanticPair ι) :
    semanticPairWithin (dist first second) first second := by
  constructor
  · intro who
    have hfirst : dist first.1 second.1 ≤ dist first second := by
      rw [Prod.dist_eq]
      exact le_max_left _ _
    rw [← Real.dist_eq]
    exact ((dist_pi_le_iff dist_nonneg).mp hfirst) who
  · intro who
    have hsecond : dist first.2 second.2 ≤ dist first second := by
      rw [Prod.dist_eq]
      exact le_max_right _ _
    rw [← Real.dist_eq]
    exact ((dist_pi_le_iff dist_nonneg).mp hsecond) who

/-! ## Literal finite-clock density -/

/-- Directed union of literal finite-clock semantic pairs along the canonical
cofinal support sequence.  Membership retains an actual independent stopping-
law profile; this is not a closure-defined set. -/
def quittingCofinalFiniteClockSemanticPairs
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    Set (QuittingTerminalSemanticPair ι) :=
  ⋃ level : ℕ, quittingFiniteClockSemanticReachable reward
    (quantileClockSupport ι (level + 1))

theorem quittingCofinalFiniteClockSemanticPairs_nonempty
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    (quittingCofinalFiniteClockSemanticPairs reward).Nonempty := by
  obtain ⟨pair, hpair⟩ := quittingFiniteClockSemanticReachable_nonempty
    reward (quantileClockSupport ι 1)
  exact ⟨pair, Set.mem_iUnion.mpr ⟨0, by simpa using hpair⟩⟩

theorem quittingCofinalFiniteClockSemanticPairs_subset_carrier
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    quittingCofinalFiniteClockSemanticPairs reward ⊆
      quittingTerminalSemanticCarrier reward := by
  rintro pair hpair
  obtain ⟨level, hpair⟩ := Set.mem_iUnion.mp hpair
  exact quittingFiniteClockSemanticReachable_subset_carrier
    reward (quantileClockSupport ι (level + 1)) hpair

/-- For one executable source profile, its canonical compressed semantic pairs
converge at the explicit cofinal clock levels. -/
theorem tendsto_quittingQuantileClockCompressed_semanticPair
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) :
    Tendsto (fun level => quittingTerminalSemanticPair reward
        (quittingQuantileClockCompressedProfile reward profile (level + 1)))
      atTop (nhds (quittingTerminalSemanticPair reward profile)) := by
  rw [Metric.tendsto_atTop]
  intro epsilon hepsilon
  have hradius := (quantileClockScaledRadius_tendsto_zero ι
    (quittingRewardBound reward)).comp (tendsto_add_atTop_nat 1)
  obtain ⟨threshold, hthreshold⟩ :=
    (Metric.tendsto_atTop.mp hradius) epsilon hepsilon
  refine ⟨threshold, fun level hlevel => ?_⟩
  rw [dist_comm]
  exact lt_of_le_of_lt
    (dist_le_of_semanticPairWithin
      (quantileClockScaledRadius_nonneg ι
        (quittingRewardBound_nonneg reward) (level + 1))
      (hasEscapeAwareQuantileClockCompressionAtRewardBound reward
        profile (level + 1) (Nat.zero_lt_succ level)))
    (by
      simpa [Real.dist_eq, abs_of_nonneg
        (quantileClockScaledRadius_nonneg ι
          (quittingRewardBound_nonneg reward) (level + 1))] using
        hthreshold level hlevel)

/-- Every carrier point is a sequential limit of literal finite-clock pairs,
with the `level`th pair realized at exactly the canonical cofinal support
`quantileClockSupport ι (level + 1)`.  The conclusion does not realize the
limit point itself by a profile. -/
theorem exists_cofinalFiniteClockSemanticPair_sequence_tendsto
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward) :
    ∃ approximants : ℕ → QuittingTerminalSemanticPair ι,
      (∀ level, approximants level ∈
        quittingFiniteClockSemanticReachable reward
          (quantileClockSupport ι (level + 1))) ∧
      Tendsto approximants atTop (nhds pair) := by
  obtain ⟨profiles, hprofiles⟩ :=
    exists_terminalProfile_sequence_tendsto_semanticPair reward pair hpair
  let approximants := fun level => quittingTerminalSemanticPair reward
    (quittingQuantileClockCompressedProfile reward
      (profiles level) (level + 1))
  refine ⟨approximants, ?_, ?_⟩
  · intro level
    exact quittingQuantileClockCompressed_semanticPair_mem_reachable
      reward (profiles level) (level + 1)
  · apply tendsto_iff_dist_tendsto_zero.mpr
    have hsourceDist : Tendsto
        (fun level => dist
          (quittingTerminalSemanticPair reward (profiles level)) pair)
        atTop (nhds 0) :=
      tendsto_iff_dist_tendsto_zero.mp hprofiles
    have hradius : Tendsto
        (fun level => quantileClockScaledRadius ι
          (quittingRewardBound reward) (level + 1))
        atTop (nhds 0) :=
      (quantileClockScaledRadius_tendsto_zero ι
        (quittingRewardBound reward)).comp (tendsto_add_atTop_nat 1)
    apply squeeze_zero'
      (g := fun level => quantileClockScaledRadius ι
        (quittingRewardBound reward) (level + 1) +
          dist (quittingTerminalSemanticPair reward (profiles level)) pair)
    · exact Eventually.of_forall fun _ => dist_nonneg
    · exact Eventually.of_forall fun level => by
        calc
          dist (approximants level) pair ≤
              dist (approximants level)
                  (quittingTerminalSemanticPair reward (profiles level)) +
                dist (quittingTerminalSemanticPair reward (profiles level))
                  pair := dist_triangle _ _ _
          _ ≤ quantileClockScaledRadius ι
                  (quittingRewardBound reward) (level + 1) +
                dist (quittingTerminalSemanticPair reward (profiles level))
                  pair := by
              gcongr
              rw [dist_comm]
              exact dist_le_of_semanticPairWithin
                (quantileClockScaledRadius_nonneg ι
                  (quittingRewardBound_nonneg reward) (level + 1))
                (hasEscapeAwareQuantileClockCompressionAtRewardBound reward
                  (profiles level) (level + 1) (Nat.zero_lt_succ level))
    · simpa using hradius.add hsourceDist

/-- Literal finite-clock semantic pairs are dense in the full compact carrier.
This equality is only a closure statement. -/
theorem closure_quittingCofinalFiniteClockSemanticPairs_eq_carrier
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    closure (quittingCofinalFiniteClockSemanticPairs reward) =
      quittingTerminalSemanticCarrier reward := by
  apply Set.Subset.antisymm
  · exact closure_minimal
      (quittingCofinalFiniteClockSemanticPairs_subset_carrier reward)
      (quittingTerminalSemanticCarrier_isCompact reward).isClosed
  · intro pair hpair
    obtain ⟨approximants, hlevels, htendsto⟩ :=
      exists_cofinalFiniteClockSemanticPair_sequence_tendsto
        reward pair hpair
    apply mem_closure_iff_seq_limit.mpr
    refine ⟨approximants, ?_, htendsto⟩
    intro level
    exact Set.mem_iUnion.mpr ⟨level, hlevels level⟩

/-- Every continuous real score has the same infimum on the literal cofinal
finite-clock union and on the full compact semantic carrier. -/
theorem sInf_image_quittingCofinalFiniteClockSemanticPairs_eq_carrier
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (score : QuittingTerminalSemanticPair ι → ℝ)
    (hscore : Continuous score) :
    sInf (score '' quittingCofinalFiniteClockSemanticPairs reward) =
      sInf (score '' quittingTerminalSemanticCarrier reward) := by
  apply sInf_image_eq_of_subset_closure_eq
    (quittingCofinalFiniteClockSemanticPairs_nonempty reward)
    (quittingCofinalFiniteClockSemanticPairs_subset_carrier reward)
    (closure_quittingCofinalFiniteClockSemanticPairs_eq_carrier reward)
    score hscore
  exact (quittingTerminalSemanticCarrier_isCompact reward).image hscore
    |>.bddBelow

variable [Nonempty ι]

/-- Continuous terminal exploitability has the same infimum on literal
finite-clock profiles as on all behavioral profiles. -/
theorem sInf_image_quittingCofinalFiniteClockSemanticExploitability
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    sInf (quittingTerminalSemanticExploitability ''
        quittingCofinalFiniteClockSemanticPairs reward) =
      quittingTerminalExploitabilityInf reward := by
  rw [sInf_image_quittingCofinalFiniteClockSemanticPairs_eq_carrier
    reward quittingTerminalSemanticExploitability
    continuous_quittingTerminalSemanticExploitability]
  have hattainableNonempty :
      (quittingAttainableTerminalSemanticPairs reward).Nonempty := by
    exact ⟨quittingTerminalSemanticPair reward
        (quittingAlwaysContinueProfile reward),
      quittingAlwaysContinueProfile reward, rfl⟩
  have hcarrierInf :
      sInf (quittingTerminalSemanticExploitability ''
          quittingAttainableTerminalSemanticPairs reward) =
        sInf (quittingTerminalSemanticExploitability ''
          quittingTerminalSemanticCarrier reward) := by
    apply sInf_image_eq_of_subset_closure_eq
      hattainableNonempty subset_closure rfl
      quittingTerminalSemanticExploitability
      continuous_quittingTerminalSemanticExploitability
    exact (quittingTerminalSemanticCarrier_isCompact reward).image
      continuous_quittingTerminalSemanticExploitability |>.bddBelow
  rw [← hcarrierInf]
  unfold quittingTerminalExploitabilityInf
  congr 1
  ext value
  constructor
  · rintro ⟨pair, ⟨profile, rfl⟩, rfl⟩
    exact ⟨profile,
      quittingTerminalSemanticExploitability_pair reward profile⟩
  · rintro ⟨profile, rfl⟩
    exact ⟨quittingTerminalSemanticPair reward profile,
      ⟨profile, rfl⟩,
      quittingTerminalSemanticExploitability_pair reward profile⟩

omit [DecidableEq ι] in
theorem quittingTerminalSemanticExploitability_nonneg
    (pair : QuittingTerminalSemanticPair ι) :
    0 ≤ quittingTerminalSemanticExploitability pair := by
  let who : ι := Classical.choice inferInstance
  exact (le_max_left 0 _).trans
    (le_finitePlayerMax
      (fun player => max 0 (quittingTerminalSemanticDebt pair player)) who)

omit [DecidableEq ι] in
theorem abs_quittingTerminalSemanticExploitability_sub_le
    (first second : QuittingTerminalSemanticPair ι) :
    |quittingTerminalSemanticExploitability first -
        quittingTerminalSemanticExploitability second| ≤
      2 * dist first second := by
  let radius := dist first second
  have hradius : 0 ≤ radius := dist_nonneg
  have hwithin : semanticPairWithin radius first second :=
    semanticPairWithin_dist first second
  have hdebt : ∀ who,
      |quittingTerminalSemanticDebt first who -
          quittingTerminalSemanticDebt second who| ≤ 2 * radius := by
    intro who
    unfold quittingTerminalSemanticDebt
    rw [show (first.2 who - first.1 who) -
        (second.2 who - second.1 who) =
      (first.2 who - second.2 who) -
        (first.1 who - second.1 who) by ring]
    calc
      |(first.2 who - second.2 who) -
          (first.1 who - second.1 who)| ≤
          |first.2 who - second.2 who| +
            |first.1 who - second.1 who| := by
        exact abs_sub _ _
      _ ≤ radius + radius := add_le_add (hwithin.2 who) (hwithin.1 who)
      _ = 2 * radius := by ring
  have hforward : quittingTerminalSemanticExploitability first ≤
      quittingTerminalSemanticExploitability second + 2 * radius := by
    unfold quittingTerminalSemanticExploitability
    apply finitePlayerMax_le
    intro who
    calc
      max 0 (quittingTerminalSemanticDebt first who) ≤
          max 0 (quittingTerminalSemanticDebt second who) + 2 * radius := by
        have hmax := abs_max_sub_max_le_max
          0 (quittingTerminalSemanticDebt first who)
          0 (quittingTerminalSemanticDebt second who)
        have hsigned : max 0 (quittingTerminalSemanticDebt first who) -
            max 0 (quittingTerminalSemanticDebt second who) ≤
            2 * radius := by
          refine (le_abs_self _).trans (hmax.trans ?_)
          simpa using hdebt who
        linarith
      _ ≤ finitePlayerMax
          (fun player => max 0
            (quittingTerminalSemanticDebt second player)) + 2 * radius :=
        by
          simpa [add_comm] using add_le_add_right (le_finitePlayerMax
            (fun player => max 0
              (quittingTerminalSemanticDebt second player)) who) (2 * radius)
  have hbackward : quittingTerminalSemanticExploitability second ≤
      quittingTerminalSemanticExploitability first + 2 * radius := by
    unfold quittingTerminalSemanticExploitability
    apply finitePlayerMax_le
    intro who
    calc
      max 0 (quittingTerminalSemanticDebt second who) ≤
          max 0 (quittingTerminalSemanticDebt first who) + 2 * radius := by
        have hmax := abs_max_sub_max_le_max
          0 (quittingTerminalSemanticDebt second who)
          0 (quittingTerminalSemanticDebt first who)
        have hsigned : max 0 (quittingTerminalSemanticDebt second who) -
            max 0 (quittingTerminalSemanticDebt first who) ≤
            2 * radius := by
          refine (le_abs_self _).trans (hmax.trans ?_)
          simpa [abs_sub_comm] using hdebt who
        linarith
      _ ≤ finitePlayerMax
          (fun player => max 0
            (quittingTerminalSemanticDebt first player)) + 2 * radius :=
        by
          simpa [add_comm] using add_le_add_right (le_finitePlayerMax
            (fun player => max 0
              (quittingTerminalSemanticDebt first player)) who) (2 * radius)
  rw [abs_le]
  constructor <;> dsimp [radius] at * <;> linarith

/-- Topological hierarchy system generated by the exact finite-clock centers.
Its only non-structural input is the named common-quantile compression
proposition. -/
def escapeAwareQuantileClockSystem
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hcompression : HasEscapeAwareQuantileClockCompression reward) :
    NestedOuterApproximation (QuittingTerminalSemanticPair ι) where
  attainable := quittingAttainableTerminalSemanticPairs reward
  center level := quittingFiniteClockSemanticCenter reward
    (quantileClockSupport ι level)
  radius := quantileClockRadius ι
  attainable_nonempty := by
    exact ⟨quittingTerminalSemanticPair reward
        (quittingAlwaysContinueProfile reward),
      quittingAlwaysContinueProfile reward, rfl⟩
  center_nonempty level := quittingFiniteClockSemanticCenter_nonempty reward _
  center_compact level := quittingFiniteClockSemanticCenter_isCompact reward _
  center_subset_closure level := by
    simpa only [quittingTerminalSemanticCarrier] using
      quittingFiniteClockSemanticCenter_subset_carrier reward _
  radius_nonneg := quantileClockRadius_nonneg ι
  radius_tendsto_zero := quantileClockRadius_tendsto_zero ι
  attainable_infDist_le := by
    rintro pair ⟨profile, rfl⟩ level hlevel
    exact (Metric.infDist_le_dist_of_mem
      (quittingQuantileClockCompressed_semanticPair_mem_reachable
        reward profile level)).trans
      (dist_le_of_semanticPairWithin
        (quantileClockRadius_nonneg ι level)
        (hcompression profile level hlevel))

/-- Finite-clock outer-approximation system at an explicit absolute terminal
reward bound. -/
def escapeAwareQuantileClockSystemAtBound
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (bound : ℝ) (hbound : 0 ≤ bound)
    (hcompression : HasEscapeAwareQuantileClockCompressionAtBound
      reward bound) :
    NestedOuterApproximation (QuittingTerminalSemanticPair ι) where
  attainable := quittingAttainableTerminalSemanticPairs reward
  center level := quittingFiniteClockSemanticCenter reward
    (quantileClockSupport ι level)
  radius := quantileClockScaledRadius ι bound
  attainable_nonempty := by
    exact ⟨quittingTerminalSemanticPair reward
        (quittingAlwaysContinueProfile reward),
      quittingAlwaysContinueProfile reward, rfl⟩
  center_nonempty level := quittingFiniteClockSemanticCenter_nonempty reward _
  center_compact level := quittingFiniteClockSemanticCenter_isCompact reward _
  center_subset_closure level := by
    simpa only [quittingTerminalSemanticCarrier] using
      quittingFiniteClockSemanticCenter_subset_carrier reward _
  radius_nonneg := quantileClockScaledRadius_nonneg ι hbound
  radius_tendsto_zero := quantileClockScaledRadius_tendsto_zero ι bound
  attainable_infDist_le := by
    rintro pair ⟨profile, rfl⟩ level hlevel
    exact (Metric.infDist_le_dist_of_mem
      (quittingQuantileClockCompressed_semanticPair_mem_reachable
        reward profile level)).trans
      (dist_le_of_semanticPairWithin
        (quantileClockScaledRadius_nonneg ι hbound level)
        (hcompression profile level hlevel))

/-- Outer hierarchy at a finite level. -/
def escapeAwareQuantileClockOuter
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hcompression : HasEscapeAwareQuantileClockCompression reward)
    (level : ℕ) : Set (QuittingTerminalSemanticPair ι) :=
  (escapeAwareQuantileClockSystem reward hcompression).nestedOuter level

/-- Scaled outer hierarchy at a finite level. -/
def escapeAwareQuantileClockOuterAtBound
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (bound : ℝ) (hbound : 0 ≤ bound)
    (hcompression : HasEscapeAwareQuantileClockCompressionAtBound
      reward bound)
    (level : ℕ) : Set (QuittingTerminalSemanticPair ι) :=
  (escapeAwareQuantileClockSystemAtBound
    reward bound hbound hcompression).nestedOuter level

omit [Nonempty ι] in
/-- The nested hierarchy converges exactly to the terminal semantic carrier,
including carrier points not realized by one behavior profile. -/
theorem iInter_escapeAwareQuantileClockOuter_eq_carrier
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hcompression : HasEscapeAwareQuantileClockCompression reward) :
    (⋂ level, escapeAwareQuantileClockOuter reward hcompression level) =
      quittingTerminalSemanticCarrier reward := by
  simpa only [escapeAwareQuantileClockOuter,
    escapeAwareQuantileClockSystem, quittingTerminalSemanticCarrier] using
    (escapeAwareQuantileClockSystem reward hcompression).iInter_nestedOuter

omit [Nonempty ι] in
/-- Under normalized rewards, the canonical finite-clock outer hierarchy
unconditionally converges to the full terminal semantic carrier. -/
theorem iInter_escapeAwareQuantileClockOuter_normalized_eq_carrier
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hreward : ∀ terminal player, |reward terminal player| ≤ 1) :
    (⋂ level, escapeAwareQuantileClockOuter reward
      (hasEscapeAwareQuantileClockCompression_of_normalized reward hreward)
      level) = quittingTerminalSemanticCarrier reward :=
  iInter_escapeAwareQuantileClockOuter_eq_carrier reward
    (hasEscapeAwareQuantileClockCompression_of_normalized reward hreward)

omit [Nonempty ι] in
/-- At every nonnegative explicit reward bound, the scaled finite-clock outer
hierarchy converges exactly to the terminal semantic carrier. -/
theorem iInter_escapeAwareQuantileClockOuterAtBound_eq_carrier
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (bound : ℝ) (hbound : 0 ≤ bound)
    (hcompression : HasEscapeAwareQuantileClockCompressionAtBound
      reward bound) :
    (⋂ level, escapeAwareQuantileClockOuterAtBound reward bound hbound
      hcompression level) = quittingTerminalSemanticCarrier reward := by
  simpa only [escapeAwareQuantileClockOuterAtBound,
    escapeAwareQuantileClockSystemAtBound,
    quittingTerminalSemanticCarrier] using
    (escapeAwareQuantileClockSystemAtBound
      reward bound hbound hcompression).iInter_nestedOuter

omit [Nonempty ι] in
/-- The canonical reward bound gives an unconditional finite-clock outer
hierarchy for every finite quitting reward table. -/
theorem iInter_escapeAwareQuantileClockOuterAtRewardBound_eq_carrier
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    (⋂ level, escapeAwareQuantileClockOuterAtBound reward
      (quittingRewardBound reward) (quittingRewardBound_nonneg reward)
      (hasEscapeAwareQuantileClockCompressionAtRewardBound reward) level) =
        quittingTerminalSemanticCarrier reward :=
  iInter_escapeAwareQuantileClockOuterAtBound_eq_carrier reward
    (quittingRewardBound reward) (quittingRewardBound_nonneg reward)
    (hasEscapeAwareQuantileClockCompressionAtRewardBound reward)

/-- Certified lower objective over the finite outer hierarchy. -/
def escapeAwareQuantileClockLower
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hcompression : HasEscapeAwareQuantileClockCompression reward)
    (level : ℕ) : ℝ :=
  (escapeAwareQuantileClockSystem reward hcompression).lowerValue
    quittingTerminalSemanticExploitability level

/-- Upper objective over the closed finite-clock center. -/
def escapeAwareQuantileClockUpper
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hcompression : HasEscapeAwareQuantileClockCompression reward)
    (level : ℕ) : ℝ :=
  (escapeAwareQuantileClockSystem reward hcompression).upperValue
    quittingTerminalSemanticExploitability level

/-- Certified lower objective over the scaled finite outer hierarchy. -/
def escapeAwareQuantileClockLowerAtBound
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (bound : ℝ) (hbound : 0 ≤ bound)
    (hcompression : HasEscapeAwareQuantileClockCompressionAtBound
      reward bound)
    (level : ℕ) : ℝ :=
  (escapeAwareQuantileClockSystemAtBound
    reward bound hbound hcompression).lowerValue
      quittingTerminalSemanticExploitability level

/-- Upper objective over the finite-clock center, paired with the scaled
outer hierarchy. -/
def escapeAwareQuantileClockUpperAtBound
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (bound : ℝ) (hbound : 0 ≤ bound)
    (hcompression : HasEscapeAwareQuantileClockCompressionAtBound
      reward bound)
    (level : ℕ) : ℝ :=
  (escapeAwareQuantileClockSystemAtBound
    reward bound hbound hcompression).upperValue
      quittingTerminalSemanticExploitability level

theorem escapeAwareQuantileClockLowerAtBound_nonneg
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (bound : ℝ) (hbound : 0 ≤ bound)
    (hcompression : HasEscapeAwareQuantileClockCompressionAtBound
      reward bound)
    (level : ℕ) :
    0 ≤ escapeAwareQuantileClockLowerAtBound
      reward bound hbound hcompression level := by
  exact (escapeAwareQuantileClockSystemAtBound
    reward bound hbound hcompression).floor_le_lowerValue
      quittingTerminalSemanticExploitability
      quittingTerminalSemanticExploitability_nonneg level

/-- The scaled finite-clock upper value is attained by one literal product
stopping-law semantic pair. -/
theorem exists_finiteClockSemanticPair_exploitability_eq_upperAtBound
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (bound : ℝ) (hbound : 0 ≤ bound)
    (hcompression : HasEscapeAwareQuantileClockCompressionAtBound
      reward bound)
    (level : ℕ) :
    ∃ pair ∈ quittingFiniteClockSemanticReachable reward
        (quantileClockSupport ι level),
      quittingTerminalSemanticExploitability pair =
        escapeAwareQuantileClockUpperAtBound
          reward bound hbound hcompression level := by
  exact NestedOuterApproximation.exists_mem_center_score_eq_upperValue
    (escapeAwareQuantileClockSystemAtBound
      reward bound hbound hcompression)
    quittingTerminalSemanticExploitability
    continuous_quittingTerminalSemanticExploitability level

/-- Every finite outer lower bound is nonnegative. -/
theorem escapeAwareQuantileClockLower_nonneg
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hcompression : HasEscapeAwareQuantileClockCompression reward)
    (level : ℕ) :
    0 ≤ escapeAwareQuantileClockLower reward hcompression level := by
  exact (escapeAwareQuantileClockSystem reward hcompression).floor_le_lowerValue
    quittingTerminalSemanticExploitability
    quittingTerminalSemanticExploitability_nonneg level

/-- Every finite-clock upper value is nonnegative. -/
theorem escapeAwareQuantileClockUpper_nonneg
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hcompression : HasEscapeAwareQuantileClockCompression reward)
    (level : ℕ) :
    0 ≤ escapeAwareQuantileClockUpper reward hcompression level := by
  exact (escapeAwareQuantileClockSystem reward hcompression).floor_le_upperValue
    quittingTerminalSemanticExploitability
    quittingTerminalSemanticExploitability_nonneg level

/-- The finite-clock upper value is attained by one literal finite-clock
semantic pair, hence by an actual independent stopping-law profile retaining
its Never atoms. -/
theorem exists_finiteClockSemanticPair_exploitability_eq_upper
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hcompression : HasEscapeAwareQuantileClockCompression reward)
    (level : ℕ) :
    ∃ pair ∈ quittingFiniteClockSemanticReachable reward
        (quantileClockSupport ι level),
      quittingTerminalSemanticExploitability pair =
        escapeAwareQuantileClockUpper reward hcompression level := by
  exact NestedOuterApproximation.exists_mem_center_score_eq_upperValue
    (escapeAwareQuantileClockSystem reward hcompression)
    quittingTerminalSemanticExploitability
    continuous_quittingTerminalSemanticExploitability level

theorem escapeAwareQuantileClock_attainableInf_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hcompression : HasEscapeAwareQuantileClockCompression reward) :
    (escapeAwareQuantileClockSystem reward hcompression).attainableInf
        quittingTerminalSemanticExploitability =
      quittingTerminalExploitabilityInf reward := by
  unfold NestedOuterApproximation.attainableInf
    quittingTerminalExploitabilityInf
  congr 1
  ext value
  constructor
  · rintro ⟨pair, ⟨profile, rfl⟩, rfl⟩
    exact ⟨profile, quittingTerminalSemanticExploitability_pair reward profile⟩
  · rintro ⟨profile, rfl⟩
    exact ⟨quittingTerminalSemanticPair reward profile,
      ⟨profile, rfl⟩,
      quittingTerminalSemanticExploitability_pair reward profile⟩

theorem escapeAwareQuantileClockAtBound_attainableInf_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (bound : ℝ) (hbound : 0 ≤ bound)
    (hcompression : HasEscapeAwareQuantileClockCompressionAtBound
      reward bound) :
    NestedOuterApproximation.attainableInf
        (escapeAwareQuantileClockSystemAtBound
          reward bound hbound hcompression)
        quittingTerminalSemanticExploitability =
      quittingTerminalExploitabilityInf reward := by
  unfold NestedOuterApproximation.attainableInf
    quittingTerminalExploitabilityInf
  congr 1
  ext value
  constructor
  · rintro ⟨pair, ⟨profile, rfl⟩, rfl⟩
    exact ⟨profile, quittingTerminalSemanticExploitability_pair reward profile⟩
  · rintro ⟨profile, rfl⟩
    exact ⟨quittingTerminalSemanticPair reward profile,
      ⟨profile, rfl⟩,
      quittingTerminalSemanticExploitability_pair reward profile⟩

/-- Every outer lower value is below the true executable exploitability
infimum, including the unconstrained level zero. -/
theorem escapeAwareQuantileClockLower_le_exploitabilityInf
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hcompression : HasEscapeAwareQuantileClockCompression reward)
    (level : ℕ) :
    escapeAwareQuantileClockLower reward hcompression level ≤
      quittingTerminalExploitabilityInf reward := by
  have hle := NestedOuterApproximation.lowerValue_le_attainableInf
    (escapeAwareQuantileClockSystem reward hcompression)
    quittingTerminalSemanticExploitability
    quittingTerminalSemanticExploitability_nonneg level
  rwa [escapeAwareQuantileClock_attainableInf_eq reward hcompression] at hle

/-- Quantitative lower/upper bracket from the analytic compression input.
The factor `2` is the exact metric modulus of terminal exploitability. -/
theorem escapeAwareQuantileClock_quantitative_bracket
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hcompression : HasEscapeAwareQuantileClockCompression reward)
    {level : ℕ} (hlevel : 0 < level) :
    escapeAwareQuantileClockLower reward hcompression level ≤
        quittingTerminalExploitabilityInf reward ∧
      quittingTerminalExploitabilityInf reward ≤
        escapeAwareQuantileClockUpper reward hcompression level ∧
      escapeAwareQuantileClockUpper reward hcompression level -
          escapeAwareQuantileClockLower reward hcompression level ≤
        2 * quantileClockRadius ι level := by
  have hbracket :=
    (escapeAwareQuantileClockSystem reward hcompression).quantitative_bracket
      quittingTerminalSemanticExploitability
      (floor := 0) (modulus := 2)
      quittingTerminalSemanticExploitability_nonneg
      continuous_quittingTerminalSemanticExploitability
      (by norm_num)
      abs_quittingTerminalSemanticExploitability_sub_le hlevel
  rw [escapeAwareQuantileClock_attainableInf_eq reward hcompression] at hbracket
  change escapeAwareQuantileClockLower reward hcompression level ≤
        quittingTerminalExploitabilityInf reward ∧
      quittingTerminalExploitabilityInf reward ≤
        escapeAwareQuantileClockUpper reward hcompression level ∧
      escapeAwareQuantileClockUpper reward hcompression level -
          escapeAwareQuantileClockLower reward hcompression level ≤
        2 * quantileClockRadius ι level at hbracket
  exact hbracket

/-- The normalized common-quantile producer discharges the analytic premise
of the general finite-player lower/upper bracket. -/
theorem escapeAwareQuantileClock_normalized_quantitative_bracket
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hreward : ∀ terminal player, |reward terminal player| ≤ 1)
    {level : ℕ} (hlevel : 0 < level) :
    escapeAwareQuantileClockLower reward
          (hasEscapeAwareQuantileClockCompression_of_normalized reward hreward)
          level ≤ quittingTerminalExploitabilityInf reward ∧
      quittingTerminalExploitabilityInf reward ≤
        escapeAwareQuantileClockUpper reward
          (hasEscapeAwareQuantileClockCompression_of_normalized reward hreward)
          level ∧
      escapeAwareQuantileClockUpper reward
            (hasEscapeAwareQuantileClockCompression_of_normalized reward hreward)
            level -
          escapeAwareQuantileClockLower reward
            (hasEscapeAwareQuantileClockCompression_of_normalized reward hreward)
            level ≤
        2 * quantileClockRadius ι level :=
  escapeAwareQuantileClock_quantitative_bracket reward
    (hasEscapeAwareQuantileClockCompression_of_normalized reward hreward)
    hlevel

/-- Quantitative lower/upper bracket for an explicit terminal-reward bound.
The objective gap is twice the scaled semantic radius. -/
theorem escapeAwareQuantileClockAtBound_quantitative_bracket
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (bound : ℝ) (hbound : 0 ≤ bound)
    (hcompression : HasEscapeAwareQuantileClockCompressionAtBound
      reward bound)
    {level : ℕ} (hlevel : 0 < level) :
    escapeAwareQuantileClockLowerAtBound reward bound hbound hcompression
          level ≤ quittingTerminalExploitabilityInf reward ∧
      quittingTerminalExploitabilityInf reward ≤
        escapeAwareQuantileClockUpperAtBound reward bound hbound hcompression
          level ∧
      escapeAwareQuantileClockUpperAtBound reward bound hbound hcompression
            level -
          escapeAwareQuantileClockLowerAtBound reward bound hbound hcompression
            level ≤
        2 * quantileClockScaledRadius ι bound level := by
  have hbracket :=
    NestedOuterApproximation.quantitative_bracket
        (escapeAwareQuantileClockSystemAtBound
          reward bound hbound hcompression)
        quittingTerminalSemanticExploitability
        (floor := 0) (modulus := 2)
        quittingTerminalSemanticExploitability_nonneg
        continuous_quittingTerminalSemanticExploitability
        (by norm_num)
        abs_quittingTerminalSemanticExploitability_sub_le hlevel
  rw [escapeAwareQuantileClockAtBound_attainableInf_eq
    reward bound hbound hcompression] at hbracket
  change escapeAwareQuantileClockLowerAtBound reward bound hbound hcompression
          level ≤ quittingTerminalExploitabilityInf reward ∧
      quittingTerminalExploitabilityInf reward ≤
        escapeAwareQuantileClockUpperAtBound reward bound hbound hcompression
          level ∧
      escapeAwareQuantileClockUpperAtBound reward bound hbound hcompression
            level -
          escapeAwareQuantileClockLowerAtBound reward bound hbound hcompression
            level ≤
        2 * quantileClockScaledRadius ι bound level at hbracket
  exact hbracket

/-- Every finite quitting reward table has the scaled finite-clock bracket at
its canonical absolute reward bound. -/
theorem escapeAwareQuantileClockAtRewardBound_quantitative_bracket
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {level : ℕ} (hlevel : 0 < level) :
    escapeAwareQuantileClockLowerAtBound reward
          (quittingRewardBound reward) (quittingRewardBound_nonneg reward)
          (hasEscapeAwareQuantileClockCompressionAtRewardBound reward)
          level ≤ quittingTerminalExploitabilityInf reward ∧
      quittingTerminalExploitabilityInf reward ≤
        escapeAwareQuantileClockUpperAtBound reward
          (quittingRewardBound reward) (quittingRewardBound_nonneg reward)
          (hasEscapeAwareQuantileClockCompressionAtRewardBound reward)
          level ∧
      escapeAwareQuantileClockUpperAtBound reward
            (quittingRewardBound reward) (quittingRewardBound_nonneg reward)
            (hasEscapeAwareQuantileClockCompressionAtRewardBound reward)
            level -
          escapeAwareQuantileClockLowerAtBound reward
            (quittingRewardBound reward) (quittingRewardBound_nonneg reward)
            (hasEscapeAwareQuantileClockCompressionAtRewardBound reward)
            level ≤
        2 * quantileClockScaledRadius ι (quittingRewardBound reward) level :=
  escapeAwareQuantileClockAtBound_quantitative_bracket reward
    (quittingRewardBound reward) (quittingRewardBound_nonneg reward)
    (hasEscapeAwareQuantileClockCompressionAtRewardBound reward) hlevel

/-- On the zero-infimum branch, the scaled hierarchy supplies an actual
finite-clock product profile at the scaled objective rate. -/
theorem exists_finiteClockSemanticPair_exploitability_le_of_inf_eq_zeroAtBound
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (bound : ℝ) (hbound : 0 ≤ bound)
    (hcompression : HasEscapeAwareQuantileClockCompressionAtBound
      reward bound)
    {level : ℕ} (hlevel : 0 < level)
    (hinf : quittingTerminalExploitabilityInf reward = 0) :
    ∃ pair ∈ quittingFiniteClockSemanticReachable reward
        (quantileClockSupport ι level),
      quittingTerminalSemanticExploitability pair ≤
        2 * quantileClockScaledRadius ι bound level := by
  obtain ⟨pair, hpair, hpairValue⟩ :=
    exists_finiteClockSemanticPair_exploitability_eq_upperAtBound
      reward bound hbound hcompression level
  obtain ⟨hlower, -, hgap⟩ :=
    escapeAwareQuantileClockAtBound_quantitative_bracket
      reward bound hbound hcompression hlevel
  have hlowerNonneg := escapeAwareQuantileClockLowerAtBound_nonneg
    reward bound hbound hcompression level
  refine ⟨pair, hpair, ?_⟩
  rw [hpairValue]
  linarith

/-- The certified interval has nonnegative width at every positive level. -/
theorem escapeAwareQuantileClock_gap_nonneg
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hcompression : HasEscapeAwareQuantileClockCompression reward)
    {level : ℕ} (hlevel : 0 < level) :
    0 ≤ escapeAwareQuantileClockUpper reward hcompression level -
      escapeAwareQuantileClockLower reward hcompression level := by
  obtain ⟨hlower, hupper, -⟩ :=
    escapeAwareQuantileClock_quantitative_bracket reward hcompression hlevel
  linarith

/-- The finite-clock upper certificate converges from above at the same
explicit rate. -/
theorem escapeAwareQuantileClockUpper_sub_exploitabilityInf
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hcompression : HasEscapeAwareQuantileClockCompression reward)
    {level : ℕ} (hlevel : 0 < level) :
    0 ≤ escapeAwareQuantileClockUpper reward hcompression level -
        quittingTerminalExploitabilityInf reward ∧
      escapeAwareQuantileClockUpper reward hcompression level -
          quittingTerminalExploitabilityInf reward ≤
        2 * quantileClockRadius ι level := by
  obtain ⟨hlower, hupper, hgap⟩ :=
    escapeAwareQuantileClock_quantitative_bracket reward hcompression hlevel
  constructor <;> linarith

/-- On the zero-infimum branch, an actual finite-clock product profile attains
the advertised quantitative exploitability upper bound. -/
theorem exists_finiteClockSemanticPair_exploitability_le_of_inf_eq_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hcompression : HasEscapeAwareQuantileClockCompression reward)
    {level : ℕ} (hlevel : 0 < level)
    (hinf : quittingTerminalExploitabilityInf reward = 0) :
    ∃ pair ∈ quittingFiniteClockSemanticReachable reward
        (quantileClockSupport ι level),
      quittingTerminalSemanticExploitability pair ≤
        2 * quantileClockRadius ι level := by
  obtain ⟨pair, hpair, hpairValue⟩ :=
    exists_finiteClockSemanticPair_exploitability_eq_upper
      reward hcompression level
  refine ⟨pair, hpair, ?_⟩
  rw [hpairValue]
  obtain ⟨-, hupper⟩ :=
    escapeAwareQuantileClockUpper_sub_exploitabilityInf
      reward hcompression hlevel
  linarith

/-- The lower certificates converge to the exact executable exploitability
infimum at the quantitative compression rate. -/
theorem tendsto_escapeAwareQuantileClockLower
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hcompression : HasEscapeAwareQuantileClockCompression reward) :
    Tendsto (escapeAwareQuantileClockLower reward hcompression) atTop
      (𝓝 (quittingTerminalExploitabilityInf reward)) := by
  have herror : Tendsto (fun level =>
      quittingTerminalExploitabilityInf reward -
        escapeAwareQuantileClockLower reward hcompression level)
      atTop (𝓝 0) := by
    apply squeeze_zero' (g := fun level => 2 * quantileClockRadius ι level)
    · exact Eventually.of_forall fun level => sub_nonneg.mpr
        (escapeAwareQuantileClockLower_le_exploitabilityInf
          reward hcompression level)
    · filter_upwards [eventually_gt_atTop 0] with level hlevel
      obtain ⟨-, hupper, hgap⟩ :=
        escapeAwareQuantileClock_quantitative_bracket
          reward hcompression hlevel
      linarith
    · simpa only [mul_zero] using
        (quantileClockRadius_tendsto_zero ι).const_mul 2
  have hconstant : Tendsto
      (fun _ : ℕ => quittingTerminalExploitabilityInf reward) atTop
      (𝓝 (quittingTerminalExploitabilityInf reward)) :=
    tendsto_const_nhds
  simpa only [sub_sub_cancel, sub_zero] using hconstant.sub herror

/-- The supremum of all finite lower certificates is the exact executable
exploitability infimum. -/
theorem sSup_range_escapeAwareQuantileClockLower
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hcompression : HasEscapeAwareQuantileClockCompression reward) :
    sSup (Set.range (escapeAwareQuantileClockLower reward hcompression)) =
      quittingTerminalExploitabilityInf reward := by
  have hle : ∀ level, escapeAwareQuantileClockLower reward hcompression level ≤
      quittingTerminalExploitabilityInf reward :=
    escapeAwareQuantileClockLower_le_exploitabilityInf reward hcompression
  have hbdd : BddAbove
      (Set.range (escapeAwareQuantileClockLower reward hcompression)) :=
    ⟨quittingTerminalExploitabilityInf reward, by
      rintro value ⟨level, rfl⟩
      exact hle level⟩
  apply le_antisymm
  · exact csSup_le (Set.range_nonempty _) (by
      rintro value ⟨level, rfl⟩
      exact hle level)
  · apply le_of_tendsto'
      (tendsto_escapeAwareQuantileClockLower reward hcompression)
    intro level
    exact le_csSup hbdd (Set.mem_range_self level)

/-- The support and radius constants specialize literally to the Fin4 packet. -/
theorem quantileClockSupport_fin4 (level : ℕ) :
    quantileClockSupport (Fin 4) level = 8 * level + 1 := by
  simp [quantileClockSupport]

theorem quantileClockRadius_fin4 (level : ℕ) :
    quantileClockRadius (Fin 4) level = 12 / (level : ℝ) := by
  simp [quantileClockRadius]

theorem quantileClockScaledRadius_fin4 (bound : ℝ) (level : ℕ) :
    quantileClockScaledRadius (Fin 4) bound level =
      12 * bound / (level : ℝ) := by
  rw [quantileClockScaledRadius, quantileClockRadius_fin4]
  ring

/-- Fin4 bracket with the advertised `24 / level` gap. -/
theorem escapeAwareQuantileClock_fin4_quantitative_bracket
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hcompression : HasEscapeAwareQuantileClockCompression reward)
    {level : ℕ} (hlevel : 0 < level) :
    escapeAwareQuantileClockLower reward hcompression level ≤
        quittingTerminalExploitabilityInf reward ∧
      quittingTerminalExploitabilityInf reward ≤
        escapeAwareQuantileClockUpper reward hcompression level ∧
      escapeAwareQuantileClockUpper reward hcompression level -
          escapeAwareQuantileClockLower reward hcompression level ≤
        24 / (level : ℝ) := by
  obtain ⟨hlower, hupper, hgap⟩ :=
    escapeAwareQuantileClock_quantitative_bracket reward hcompression hlevel
  refine ⟨hlower, hupper, hgap.trans_eq ?_⟩
  rw [quantileClockRadius_fin4]
  ring

/-- Unconditional normalized Fin4 bracket with support `8 * level + 1`,
semantic radius `12 / level`, and objective gap `24 / level`. -/
theorem escapeAwareQuantileClock_fin4_normalized_quantitative_bracket
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hreward : ∀ terminal player, |reward terminal player| ≤ 1)
    {level : ℕ} (hlevel : 0 < level) :
    escapeAwareQuantileClockLower reward
          (hasEscapeAwareQuantileClockCompression_of_normalized reward hreward)
          level ≤ quittingTerminalExploitabilityInf reward ∧
      quittingTerminalExploitabilityInf reward ≤
        escapeAwareQuantileClockUpper reward
          (hasEscapeAwareQuantileClockCompression_of_normalized reward hreward)
          level ∧
      escapeAwareQuantileClockUpper reward
            (hasEscapeAwareQuantileClockCompression_of_normalized reward hreward)
            level -
          escapeAwareQuantileClockLower reward
            (hasEscapeAwareQuantileClockCompression_of_normalized reward hreward)
            level ≤
        24 / (level : ℝ) :=
  escapeAwareQuantileClock_fin4_quantitative_bracket reward
    (hasEscapeAwareQuantileClockCompression_of_normalized reward hreward)
    hlevel

/-- Fin4 bracket for an arbitrary explicit absolute reward bound. -/
theorem escapeAwareQuantileClock_fin4AtBound_quantitative_bracket
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (bound : ℝ) (hbound : 0 ≤ bound)
    (hcompression : HasEscapeAwareQuantileClockCompressionAtBound
      reward bound)
    {level : ℕ} (hlevel : 0 < level) :
    escapeAwareQuantileClockLowerAtBound reward bound hbound hcompression
          level ≤ quittingTerminalExploitabilityInf reward ∧
      quittingTerminalExploitabilityInf reward ≤
        escapeAwareQuantileClockUpperAtBound reward bound hbound hcompression
          level ∧
      escapeAwareQuantileClockUpperAtBound reward bound hbound hcompression
            level -
          escapeAwareQuantileClockLowerAtBound reward bound hbound hcompression
            level ≤
        24 * bound / (level : ℝ) := by
  obtain ⟨hlower, hupper, hgap⟩ :=
    escapeAwareQuantileClockAtBound_quantitative_bracket
      reward bound hbound hcompression hlevel
  refine ⟨hlower, hupper, hgap.trans_eq ?_⟩
  rw [quantileClockScaledRadius_fin4]
  ring

/-- Every Fin4 reward table has the finite-clock bracket with its canonical
absolute reward bound. -/
theorem escapeAwareQuantileClock_fin4AtRewardBound_quantitative_bracket
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    {level : ℕ} (hlevel : 0 < level) :
    escapeAwareQuantileClockLowerAtBound reward
          (quittingRewardBound reward) (quittingRewardBound_nonneg reward)
          (hasEscapeAwareQuantileClockCompressionAtRewardBound reward)
          level ≤ quittingTerminalExploitabilityInf reward ∧
      quittingTerminalExploitabilityInf reward ≤
        escapeAwareQuantileClockUpperAtBound reward
          (quittingRewardBound reward) (quittingRewardBound_nonneg reward)
          (hasEscapeAwareQuantileClockCompressionAtRewardBound reward)
          level ∧
      escapeAwareQuantileClockUpperAtBound reward
            (quittingRewardBound reward) (quittingRewardBound_nonneg reward)
            (hasEscapeAwareQuantileClockCompressionAtRewardBound reward)
            level -
          escapeAwareQuantileClockLowerAtBound reward
            (quittingRewardBound reward) (quittingRewardBound_nonneg reward)
            (hasEscapeAwareQuantileClockCompressionAtRewardBound reward)
            level ≤
        24 * quittingRewardBound reward / (level : ℝ) :=
  escapeAwareQuantileClock_fin4AtBound_quantitative_bracket reward
    (quittingRewardBound reward) (quittingRewardBound_nonneg reward)
    (hasEscapeAwareQuantileClockCompressionAtRewardBound reward) hlevel

/-- Fin4 zero-infimum branch: an actual finite-clock product profile has the
advertised `24 / level` exploitability bound. -/
theorem exists_fin4_finiteClockSemanticPair_exploitability_le_of_inf_eq_zero
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hcompression : HasEscapeAwareQuantileClockCompression reward)
    {level : ℕ} (hlevel : 0 < level)
    (hinf : quittingTerminalExploitabilityInf reward = 0) :
    ∃ pair ∈ quittingFiniteClockSemanticReachable reward (8 * level + 1),
      quittingTerminalSemanticExploitability pair ≤ 24 / (level : ℝ) := by
  obtain ⟨pair, hpair, hbound⟩ :=
    exists_finiteClockSemanticPair_exploitability_le_of_inf_eq_zero
      reward hcompression hlevel hinf
  rw [quantileClockSupport_fin4] at hpair
  refine ⟨pair, hpair, hbound.trans_eq ?_⟩
  rw [quantileClockRadius_fin4]
  ring

/-- On the normalized Fin4 zero-infimum branch, the finite-clock upper witness
is an actual product stopping-law semantic pair with the advertised rate. -/
theorem exists_fin4_finiteClockSemanticPair_exploitability_le_of_normalized_inf_eq_zero
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hreward : ∀ terminal player, |reward terminal player| ≤ 1)
    {level : ℕ} (hlevel : 0 < level)
    (hinf : quittingTerminalExploitabilityInf reward = 0) :
    ∃ pair ∈ quittingFiniteClockSemanticReachable reward (8 * level + 1),
      quittingTerminalSemanticExploitability pair ≤ 24 / (level : ℝ) :=
  exists_fin4_finiteClockSemanticPair_exploitability_le_of_inf_eq_zero
    reward
    (hasEscapeAwareQuantileClockCompression_of_normalized reward hreward)
    hlevel hinf

end GameTheory
