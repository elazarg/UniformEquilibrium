/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.LinearProgramming.StrongComplementarity

/-!
# Finite closed-trap perturbations

This module isolates the game-independent core of a standard finite-state
policy-improvement argument.  On a region closed under every positive
transition, its indicator is harmonic for each transition row based in the
region and subharmonic elsewhere.  Consequently a positive multiple of the
indicator may be added to a feasible gain whenever the bias rows have enough
slack on that region.

The module also records the two finite-dimensional facts used with this
perturbation: finitely many positive slacks have a common positive lower
bound, and a zero-gap primal--dual pair rules out a strictly better feasible
primal point.
-/

noncomputable section

open scoped BigOperators

namespace Math
namespace LinearProgramming

/-- A zero-gap feasible primal--dual pair makes its primal component optimal.
Strong complementarity is more than is needed, but is a convenient packaged
source of the three hypotheses. -/
theorem IsStrongComplementaryPair.minPrimalValue_le_of_feasible
    {Row Col : Type*} [Fintype Row] [Fintype Col]
    {A : Row → Col → ℝ} {b : Row → ℝ} {c : Col → ℝ}
    {x : Col → ℝ} {y : Row → ℝ}
    (h : IsStrongComplementaryPair A b c x y)
    {candidate : Col → ℝ} (hcandidate : MinPrimalFeasible A b candidate) :
    minPrimalValue c x ≤ minPrimalValue c candidate := by
  calc
    minPrimalValue c x = maxDualValue b y := h.2.2.1
    _ ≤ minPrimalValue c candidate := min_weak_duality hcandidate h.2.1

namespace ClosedTrapPerturbation

/-- A finite nonempty family of positive reals has a common positive lower
bound. -/
theorem exists_uniformPositiveLowerBound
    {Index : Type*} [Fintype Index] [Nonempty Index]
    (slack : Index → ℝ) (hpos : ∀ index, 0 < slack index) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ index, ε ≤ slack index := by
  classical
  let margin := Finset.univ.inf' Finset.univ_nonempty slack
  have hmargin_pos : 0 < margin :=
    (Finset.lt_inf'_iff Finset.univ_nonempty).2 fun index _ ↦ hpos index
  refine ⟨margin / 2, by linarith, ?_⟩
  intro index
  have hmargin_le : margin ≤ slack index :=
    Finset.inf'_le slack (Finset.mem_univ index)
  linarith

variable {State Action : Type*} [Fintype State]

/-- The real indicator of a state predicate. -/
def indicator (region : State → Prop) [DecidablePred region] (state : State) : ℝ :=
  if region state then 1 else 0

omit [Fintype State] in
theorem indicator_nonneg
    (region : State → Prop) [DecidablePred region] (state : State) :
    0 ≤ indicator region state := by
  simp only [indicator]
  split <;> norm_num

/-- A stochastic row based in a positively closed region has indicator
expectation one. -/
theorem sum_mul_indicator_eq_one
    (transition : State → Action → State → ℝ)
    (region : State → Prop) [DecidablePred region]
    (htrans_nonneg : ∀ source action destination,
      0 ≤ transition source action destination)
    (htrans_sum : ∀ source action,
      (∑ destination, transition source action destination) = 1)
    (hclosed : ∀ {source destination} (action : Action),
      region source → 0 < transition source action destination →
        region destination)
    {source : State} (action : Action) (hsource : region source) :
    (∑ destination,
      transition source action destination * indicator region destination) = 1 := by
  calc
    (∑ destination,
        transition source action destination * indicator region destination) =
        ∑ destination, transition source action destination := by
      apply Finset.sum_congr rfl
      intro destination _
      by_cases hzero : transition source action destination = 0
      · simp [hzero]
      · have hpositive : 0 < transition source action destination :=
          lt_of_le_of_ne (htrans_nonneg source action destination) (Ne.symm hzero)
        simp [indicator, hclosed action hsource hpositive]
    _ = 1 := htrans_sum source action

/-- Every nonnegative transition row has nonnegative indicator expectation. -/
theorem sum_mul_indicator_nonneg
    (transition : State → Action → State → ℝ)
    (region : State → Prop) [DecidablePred region]
    (htrans_nonneg : ∀ source action destination,
      0 ≤ transition source action destination)
    (source : State) (action : Action) :
    0 ≤ ∑ destination,
      transition source action destination * indicator region destination := by
  exact Finset.sum_nonneg fun destination _ ↦
    mul_nonneg (htrans_nonneg source action destination)
      (indicator_nonneg region destination)

/-- Adding a nonnegative multiple of a closed-region indicator preserves
every subharmonic gain row. -/
theorem add_indicator_preserves_gain
    (transition : State → Action → State → ℝ)
    (region : State → Prop) [DecidablePred region]
    (gain : State → ℝ) {ε : ℝ} (hε : 0 ≤ ε)
    (htrans_nonneg : ∀ source action destination,
      0 ≤ transition source action destination)
    (htrans_sum : ∀ source action,
      (∑ destination, transition source action destination) = 1)
    (hclosed : ∀ {source destination} (action : Action),
      region source → 0 < transition source action destination →
        region destination)
    (hgain : ∀ source action,
      gain source ≤
        ∑ destination, transition source action destination * gain destination) :
    ∀ source action,
      gain source + ε * indicator region source ≤
        ∑ destination, transition source action destination *
          (gain destination + ε * indicator region destination) := by
  intro source action
  have hexpand :
      (∑ destination, transition source action destination *
          (gain destination + ε * indicator region destination)) =
        (∑ destination,
          transition source action destination * gain destination) +
        ε * (∑ destination,
          transition source action destination * indicator region destination) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro destination _
    ring
  rw [hexpand]
  by_cases hsource : region source
  · rw [sum_mul_indicator_eq_one transition region htrans_nonneg
      htrans_sum hclosed action hsource]
    simp [indicator, hsource]
    exact hgain source action
  · have hindicator_expect :=
      sum_mul_indicator_nonneg transition region htrans_nonneg source action
    simp only [indicator, if_neg hsource, mul_zero, add_zero]
    exact (hgain source action).trans (le_add_of_nonneg_right
      (mul_nonneg hε hindicator_expect))

omit [Fintype State] in
/-- If a base inequality has at least `ε` slack on a region, adding
`ε` times that region's indicator to its left side preserves it. -/
theorem add_indicator_le_of_region_le_slack
    (region : State → Prop) [DecidablePred region]
    (lhs rhs : State → Action → ℝ) {ε : ℝ}
    (hbase : ∀ state action, lhs state action ≤ rhs state action)
    (hslack : ∀ state, region state → ∀ action,
      ε ≤ rhs state action - lhs state action) :
    ∀ state action,
      lhs state action + ε * indicator region state ≤ rhs state action := by
  intro state action
  by_cases hstate : region state
  · simp only [indicator, if_pos hstate, mul_one]
    linarith [hslack state hstate action]
  · simp only [indicator, if_neg hstate, mul_zero, add_zero]
    exact hbase state action

/-- A positive indicator bump on a nonempty region strictly raises the sum
of the gain coordinates. -/
theorem sum_lt_sum_add_indicator
    (region : State → Prop) [DecidablePred region]
    (gain : State → ℝ) {ε : ℝ} (hε : 0 < ε)
    (hnonempty : ∃ state, region state) :
    (∑ state, gain state) <
      ∑ state, (gain state + ε * indicator region state) := by
  have hsum_pos : 0 < ∑ state, ε * indicator region state := by
    obtain ⟨witness, hwitness⟩ := hnonempty
    apply Finset.sum_pos'
    · intro state _
      exact mul_nonneg hε.le (indicator_nonneg region state)
    · refine ⟨witness, Finset.mem_univ witness, ?_⟩
      simp [indicator, hwitness, hε]
  calc
    (∑ state, gain state) <
        (∑ state, gain state) +
          ∑ state, ε * indicator region state := by linarith
    _ = ∑ state, (gain state + ε * indicator region state) := by
      rw [Finset.sum_add_distrib]

end ClosedTrapPerturbation
end LinearProgramming
end Math
