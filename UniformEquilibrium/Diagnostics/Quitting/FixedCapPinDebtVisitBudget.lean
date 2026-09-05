/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.FixedCapPinApproximateRootDebtExpenditure

/-!
# Visit budgets for a fixed cap-pin chamber

The approximate one-step expenditure theorem telescopes along literal prefix
chains. For chains with arbitrary source reconstruction, the only additional
term is the positive replenishment of the named debt coordinate. That
replenishment is bounded by the coordinatewise semantic seam.
-/

noncomputable section

namespace GameTheory

open Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- One semantic pair lies in the fixed player's cap-pin chamber at scale
`gamma` when the named debt has that floor and the cap is within `gamma / 4`
of the singleton reward. -/
def IsFixedCapPinAt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι) (player : ι)
    (gamma : ℝ) : Prop :=
  gamma ≤ quittingTerminalSemanticDebt pair player ∧
    |pair.2 player - reward (quittingSingletonTerminal player) player| ≤
      gamma / 4

instance instDecidableIsFixedCapPinAt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι) (player : ι)
    (gamma : ℝ) : Decidable (IsFixedCapPinAt reward pair player gamma) := by
  unfold IsFixedCapPinAt
  infer_instance

/-- Positive replenishment of one named debt coordinate between an arbitrary
prefixed pair and the next reconstructed source pair. -/
def quittingTerminalSemanticDebtReplenishment
    (source prefixed : QuittingTerminalSemanticPair ι) (player : ι) : ℝ :=
  max 0 (quittingTerminalSemanticDebt source player -
    quittingTerminalSemanticDebt prefixed player)

omit [Fintype ι] [DecidableEq ι] in
/-- Positive debt replenishment is bounded by the sum of the named prescribed
payoff and cap seams. -/
theorem quittingTerminalSemanticDebtReplenishment_le_coordinateSeam
    (source prefixed : QuittingTerminalSemanticPair ι) (player : ι) :
    quittingTerminalSemanticDebtReplenishment source prefixed player ≤
      |source.1 player - prefixed.1 player| +
        |source.2 player - prefixed.2 player| := by
  have habs := abs_quittingTerminalSemanticDebt_sub_le source prefixed player
  unfold quittingTerminalSemanticDebtReplenishment
  exact (max_le (by positivity) (le_abs_self _)).trans habs

omit [Fintype ι] [DecidableEq ι] in
/-- Re-entry into a reconstructed source increases the named debt by at most
its positive replenishment. -/
theorem quittingTerminalSemanticDebt_le_prefixed_add_replenishment
    (source prefixed : QuittingTerminalSemanticPair ι) (player : ι) :
    quittingTerminalSemanticDebt source player ≤
      quittingTerminalSemanticDebt prefixed player +
        quittingTerminalSemanticDebtReplenishment source prefixed player := by
  unfold quittingTerminalSemanticDebtReplenishment
  by_cases horder : quittingTerminalSemanticDebt source player ≤
      quittingTerminalSemanticDebt prefixed player
  · rw [max_eq_left (sub_nonpos.mpr horder), add_zero]
    exact horder
  · rw [max_eq_right (sub_nonneg.mpr (le_of_not_ge horder))]
    linarith

/-- At one approximate root, the named debt plus the fixed expenditure on a
cap-pin visit is bounded by the source debt plus root error. -/
theorem approximateRoot_prefixDebt_add_capPinExpenditure_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι)
    (root : ι → PMF Bool) (player : ι) {M gamma error : ℝ}
    (hM : 0 < M) (hgamma : 0 < gamma)
    (hreward : ∀ terminal who, |reward terminal who| ≤ M)
    (hvalue : |pair.1 player| ≤ M)
    (hdebt : 0 ≤ quittingTerminalSemanticDebt pair player)
    (hnash : IsεQuittingRootNash reward pair.1 error root) :
    quittingTerminalSemanticDebt
          (quittingTerminalSemanticPrefix reward root pair) player +
        (if IsFixedCapPinAt reward pair player gamma then
          min (gamma / 2) (gamma ^ 2 / (16 * M)) else 0) ≤
      quittingTerminalSemanticDebt pair player + error := by
  by_cases hpin : IsFixedCapPinAt reward pair player gamma
  · rw [if_pos hpin]
    have hdrop := fixedCapPin_approximateRoot_coordinateDebtDrop
      reward pair root player hM hgamma hreward hvalue hpin.1 hpin.2 hnash
    linarith
  · rw [if_neg hpin, add_zero]
    exact approximateRoot_prefixDebt_le_debt_add_error
      reward pair root player error hdebt hnash

/-- Finite telescoping budget for visits to one fixed cap-pin chamber along a
literal approximate-Nash prefix chain. -/
theorem fixedCapPin_prefixChain_visitExpenditure_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : ℕ → QuittingTerminalSemanticPair ι)
    (root : ℕ → ι → PMF Bool) (error : ℕ → ℝ)
    (player : ι) {M gamma : ℝ}
    (hM : 0 < M) (hgamma : 0 < gamma)
    (hreward : ∀ terminal who, |reward terminal who| ≤ M)
    (hvalue : ∀ index, |(pair index).1 player| ≤ M)
    (hdebt : ∀ index, 0 ≤ quittingTerminalSemanticDebt (pair index) player)
    (hnash : ∀ index,
      IsεQuittingRootNash reward (pair index).1 (error index) (root index))
    (hprefix : ∀ index,
      pair (index + 1) =
        quittingTerminalSemanticPrefix reward (root index) (pair index))
    (steps : ℕ) :
    quittingTerminalSemanticDebt (pair steps) player +
        (∑ index ∈ Finset.range steps,
          if IsFixedCapPinAt reward (pair index) player gamma then
            min (gamma / 2) (gamma ^ 2 / (16 * M)) else 0) ≤
      quittingTerminalSemanticDebt (pair 0) player +
        ∑ index ∈ Finset.range steps, error index := by
  induction steps with
  | zero => simp
  | succ steps inductionHypothesis =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      have hstep := approximateRoot_prefixDebt_add_capPinExpenditure_le
        reward (pair steps) (root steps) player hM hgamma hreward
          (hvalue steps) (hdebt steps) (hnash steps)
      rw [← hprefix steps] at hstep
      linarith

/-- The number of cap-pin visits in a finite literal prefix chain, times the
fixed drop, is bounded by initial named debt plus accumulated root error. -/
theorem fixedCapPin_prefixChain_visitCount_mul_drop_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : ℕ → QuittingTerminalSemanticPair ι)
    (root : ℕ → ι → PMF Bool) (error : ℕ → ℝ)
    (player : ι) {M gamma : ℝ}
    (hM : 0 < M) (hgamma : 0 < gamma)
    (hreward : ∀ terminal who, |reward terminal who| ≤ M)
    (hvalue : ∀ index, |(pair index).1 player| ≤ M)
    (hdebt : ∀ index, 0 ≤ quittingTerminalSemanticDebt (pair index) player)
    (hnash : ∀ index,
      IsεQuittingRootNash reward (pair index).1 (error index) (root index))
    (hprefix : ∀ index,
      pair (index + 1) =
        quittingTerminalSemanticPrefix reward (root index) (pair index))
    (steps : ℕ) :
    ((Finset.filter
        (fun index ↦ IsFixedCapPinAt reward (pair index) player gamma)
        (Finset.range steps)).card : ℝ) *
        min (gamma / 2) (gamma ^ 2 / (16 * M)) ≤
      quittingTerminalSemanticDebt (pair 0) player +
        ∑ index ∈ Finset.range steps, error index := by
  have hbudget := fixedCapPin_prefixChain_visitExpenditure_le
    reward pair root error player hM hgamma hreward hvalue hdebt hnash hprefix steps
  have hfinal := hdebt steps
  have hsum :
      (∑ index ∈ Finset.range steps,
          if IsFixedCapPinAt reward (pair index) player gamma then
            min (gamma / 2) (gamma ^ 2 / (16 * M)) else 0) =
        ((Finset.filter
          (fun index ↦ IsFixedCapPinAt reward (pair index) player gamma)
          (Finset.range steps)).card : ℝ) *
            min (gamma / 2) (gamma ^ 2 / (16 * M)) := by
    classical
    rw [← Finset.sum_filter]
    simp [mul_comm]
  rw [hsum] at hbudget
  linarith

/-- Finite visit budget with arbitrary source reconstruction. Every re-entry
is charged by the positive replenishment of the named debt coordinate. -/
theorem fixedCapPin_reentry_visitCount_mul_drop_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source prefixed : ℕ → QuittingTerminalSemanticPair ι)
    (root : ℕ → ι → PMF Bool) (error : ℕ → ℝ)
    (player : ι) {M gamma : ℝ}
    (hM : 0 < M) (hgamma : 0 < gamma)
    (hreward : ∀ terminal who, |reward terminal who| ≤ M)
    (hvalue : ∀ index, |(source index).1 player| ≤ M)
    (hdebt : ∀ index, 0 ≤ quittingTerminalSemanticDebt (source index) player)
    (hnash : ∀ index,
      IsεQuittingRootNash reward (source index).1 (error index) (root index))
    (hprefix : ∀ index,
      prefixed index =
        quittingTerminalSemanticPrefix reward (root index) (source index))
    (steps : ℕ) :
    ((Finset.filter
        (fun index ↦ IsFixedCapPinAt reward (source index) player gamma)
        (Finset.range steps)).card : ℝ) *
        min (gamma / 2) (gamma ^ 2 / (16 * M)) ≤
      quittingTerminalSemanticDebt (source 0) player +
        ∑ index ∈ Finset.range steps,
          (error index + quittingTerminalSemanticDebtReplenishment
            (source (index + 1)) (prefixed index) player) := by
  have hstep : ∀ index,
      quittingTerminalSemanticDebt (source (index + 1)) player +
          (if IsFixedCapPinAt reward (source index) player gamma then
            min (gamma / 2) (gamma ^ 2 / (16 * M)) else 0) ≤
        quittingTerminalSemanticDebt (source index) player +
          (error index + quittingTerminalSemanticDebtReplenishment
            (source (index + 1)) (prefixed index) player) := by
    intro index
    have hrootStep := approximateRoot_prefixDebt_add_capPinExpenditure_le
      reward (source index) (root index) player hM hgamma hreward
        (hvalue index) (hdebt index) (hnash index)
    rw [← hprefix index] at hrootStep
    have hreentry := quittingTerminalSemanticDebt_le_prefixed_add_replenishment
      (source (index + 1)) (prefixed index) player
    linarith
  have hbudget :
      quittingTerminalSemanticDebt (source steps) player +
          (∑ index ∈ Finset.range steps,
            if IsFixedCapPinAt reward (source index) player gamma then
              min (gamma / 2) (gamma ^ 2 / (16 * M)) else 0) ≤
        quittingTerminalSemanticDebt (source 0) player +
          ∑ index ∈ Finset.range steps,
            (error index + quittingTerminalSemanticDebtReplenishment
              (source (index + 1)) (prefixed index) player) := by
    induction steps with
    | zero => simp
    | succ steps inductionHypothesis =>
        rw [Finset.sum_range_succ, Finset.sum_range_succ]
        linarith [hstep steps]
  have hfinal := hdebt steps
  have hsum :
      (∑ index ∈ Finset.range steps,
          if IsFixedCapPinAt reward (source index) player gamma then
            min (gamma / 2) (gamma ^ 2 / (16 * M)) else 0) =
        ((Finset.filter
          (fun index ↦ IsFixedCapPinAt reward (source index) player gamma)
          (Finset.range steps)).card : ℝ) *
            min (gamma / 2) (gamma ^ 2 / (16 * M)) := by
    classical
    rw [← Finset.sum_filter]
    simp [mul_comm]
  rw [hsum] at hbudget
  linarith

/-- The arbitrary-reentry visit budget can be paid directly by the sum of
the named prescribed-payoff and cap seams. -/
theorem fixedCapPin_reentry_visitCount_mul_drop_le_coordinateSeams
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source prefixed : ℕ → QuittingTerminalSemanticPair ι)
    (root : ℕ → ι → PMF Bool) (error : ℕ → ℝ)
    (player : ι) {M gamma : ℝ}
    (hM : 0 < M) (hgamma : 0 < gamma)
    (hreward : ∀ terminal who, |reward terminal who| ≤ M)
    (hvalue : ∀ index, |(source index).1 player| ≤ M)
    (hdebt : ∀ index, 0 ≤ quittingTerminalSemanticDebt (source index) player)
    (hnash : ∀ index,
      IsεQuittingRootNash reward (source index).1 (error index) (root index))
    (hprefix : ∀ index,
      prefixed index =
        quittingTerminalSemanticPrefix reward (root index) (source index))
    (steps : ℕ) :
    ((Finset.filter
        (fun index ↦ IsFixedCapPinAt reward (source index) player gamma)
        (Finset.range steps)).card : ℝ) *
        min (gamma / 2) (gamma ^ 2 / (16 * M)) ≤
      quittingTerminalSemanticDebt (source 0) player +
        ∑ index ∈ Finset.range steps,
          (error index +
            |(source (index + 1)).1 player - (prefixed index).1 player| +
            |(source (index + 1)).2 player - (prefixed index).2 player|) := by
  have hledger := fixedCapPin_reentry_visitCount_mul_drop_le
    reward source prefixed root error player hM hgamma hreward hvalue hdebt
      hnash hprefix steps
  have hsum :
      (∑ index ∈ Finset.range steps,
          (error index + quittingTerminalSemanticDebtReplenishment
            (source (index + 1)) (prefixed index) player)) ≤
        ∑ index ∈ Finset.range steps,
          (error index +
            |(source (index + 1)).1 player - (prefixed index).1 player| +
            |(source (index + 1)).2 player - (prefixed index).2 player|) := by
    apply Finset.sum_le_sum
    intro index _
    have hseam := quittingTerminalSemanticDebtReplenishment_le_coordinateSeam
      (source (index + 1)) (prefixed index) player
    linarith
  linarith

/-! ## Summable-error finite-visit consequences -/

/-- A uniform bound on all truncated visit counts, with a positive charge per
visit, makes the full visit set finite and gives the floor-cardinality bound. -/
private theorem finite_visitSet_and_ncard_le_floor
    (visit : ℕ → Prop) [DecidablePred visit] (error : ℕ → ℝ)
    (initial drop : ℝ) (hdrop : 0 < drop) (herror : ∀ index, 0 ≤ error index)
    (hsummable : Summable error)
    (hcount : ∀ steps,
      ((Finset.filter visit (Finset.range steps)).card : ℝ) * drop ≤
        initial + ∑ index ∈ Finset.range steps, error index) :
    Set.Finite {index | visit index} ∧
      Set.ncard {index | visit index} ≤
        ⌊(initial + ∑' index, error index) / drop⌋₊ := by
  let charged : ℕ → ℝ := fun index => if visit index then drop else 0
  have hcharged_nonneg : ∀ index, 0 ≤ charged index := by
    intro index
    simp only [charged]
    split <;> positivity
  have hpartial : ∀ steps,
      ∑ index ∈ Finset.range steps, charged index ≤
        initial + ∑' index, error index := by
    intro steps
    have herrorSum := hsummable.sum_le_tsum (Finset.range steps)
      (fun index _ => herror index)
    have hchargedSum :
        (∑ index ∈ Finset.range steps, charged index) =
          ((Finset.filter visit (Finset.range steps)).card : ℝ) * drop := by
      rw [← Finset.sum_filter]
      simp
    rw [hchargedSum]
    linarith [hcount steps, herrorSum]
  have hchargedSummable : Summable charged :=
    summable_of_sum_range_le hcharged_nonneg hpartial
  have hchargedZero := hchargedSummable.tendsto_atTop_zero
  have heventually : Filter.Eventually (fun index => charged index < drop) Filter.atTop := by
    have hopen : Set.Iio drop ∈ nhds (0 : ℝ) := Iio_mem_nhds hdrop
    exact hchargedZero.eventually hopen
  obtain ⟨cutoff, hcutoff⟩ := (Filter.eventually_atTop.1 heventually)
  have hvisits_subset : {index | visit index} ⊆ (↑(Finset.range cutoff) : Set ℕ) := by
    intro index hvisit
    by_contra hout
    have hcut := hcutoff index (Nat.le_of_not_gt (by simpa using hout))
    change visit index at hvisit
    unfold charged at hcut
    rw [if_pos hvisit] at hcut
    exact (lt_irrefl drop) hcut
  have hfinite : Set.Finite {index | visit index} :=
    (Finset.finite_toSet (Finset.range cutoff)).subset hvisits_subset
  constructor
  · exact hfinite
  · have hratio_nonneg : 0 ≤ (initial + ∑' index, error index) / drop := by
      have hzero := hpartial 0
      simp only [Finset.sum_range] at hzero
      exact div_nonneg hzero hdrop.le
    obtain ⟨steps, hsteps⟩ := hfinite.toFinset.exists_nat_subset_range
    have hfilter :
        Finset.filter visit (Finset.range steps) = hfinite.toFinset := by
      ext index
      simp only [Finset.mem_filter, Finset.mem_range, Set.Finite.mem_toFinset,
        Set.mem_setOf_eq]
      constructor
      · exact fun h => h.2
      · intro hvisit
        exact ⟨Finset.mem_range.mp (hsteps (hfinite.mem_toFinset.mpr hvisit)), hvisit⟩
    have herrorSum := hsummable.sum_le_tsum (Finset.range steps)
      (fun index _ => herror index)
    have hmul :
        ((Finset.filter visit (Finset.range steps)).card : ℝ) * drop ≤
          initial + ∑' index, error index := by
      linarith [hcount steps, herrorSum]
    rw [hfilter, ← Set.ncard_eq_toFinset_card _ hfinite] at hmul
    apply (Nat.le_floor_iff hratio_nonneg).2
    exact (le_div_iff₀ hdrop).2 hmul

/-- Summable root error makes a fixed cap-pin chamber occur only finitely
often along a literal prefix chain, with an initial-debt floor-cardinality bound. -/
theorem fixedCapPin_prefixChain_visitSet_finite_and_ncard_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : ℕ → QuittingTerminalSemanticPair ι)
    (root : ℕ → ι → PMF Bool) (error : ℕ → ℝ)
    (player : ι) {M gamma : ℝ}
    (hM : 0 < M) (hgamma : 0 < gamma)
    (hreward : ∀ terminal who, |reward terminal who| ≤ M)
    (hvalue : ∀ index, |(pair index).1 player| ≤ M)
    (hdebt : ∀ index, 0 ≤ quittingTerminalSemanticDebt (pair index) player)
    (herror : ∀ index, 0 ≤ error index) (hsummable : Summable error)
    (hnash : ∀ index,
      IsεQuittingRootNash reward (pair index).1 (error index) (root index))
    (hprefix : ∀ index,
      pair (index + 1) =
        quittingTerminalSemanticPrefix reward (root index) (pair index)) :
    Set.Finite {index | IsFixedCapPinAt reward (pair index) player gamma} ∧
      Set.ncard {index | IsFixedCapPinAt reward (pair index) player gamma} ≤
        ⌊(quittingTerminalSemanticDebt (pair 0) player + ∑' index, error index) /
          min (gamma / 2) (gamma ^ 2 / (16 * M))⌋₊ := by
  apply finite_visitSet_and_ncard_le_floor _ error _ _
  · exact lt_min (half_pos hgamma) (div_pos (sq_pos_of_pos hgamma) (by positivity))
  · exact herror
  · exact hsummable
  · exact fixedCapPin_prefixChain_visitCount_mul_drop_le reward pair root error player
      hM hgamma hreward hvalue hdebt hnash hprefix

/-- For a chain starting at a point of the semantic carrier, the initial
debt in the summable-error visit budget is bounded by `2 * M`. -/
theorem fixedCapPin_carrierPrefixChain_visitSet_finite_and_ncard_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : ℕ → QuittingTerminalSemanticPair ι)
    (root : ℕ → ι → PMF Bool) (error : ℕ → ℝ)
    (player : ι) {M gamma : ℝ}
    (hM : 0 < M) (hgamma : 0 < gamma)
    (hreward : ∀ terminal who, |reward terminal who| ≤ M)
    (hpair0 : pair 0 ∈ quittingTerminalSemanticCarrier reward)
    (hvalue : ∀ index, |(pair index).1 player| ≤ M)
    (hdebt : ∀ index, 0 ≤ quittingTerminalSemanticDebt (pair index) player)
    (herror : ∀ index, 0 ≤ error index) (hsummable : Summable error)
    (hnash : ∀ index,
      IsεQuittingRootNash reward (pair index).1 (error index) (root index))
    (hprefix : ∀ index,
      pair (index + 1) =
        quittingTerminalSemanticPrefix reward (root index) (pair index)) :
    Set.Finite {index | IsFixedCapPinAt reward (pair index) player gamma} ∧
      Set.ncard {index | IsFixedCapPinAt reward (pair index) player gamma} ≤
        ⌊(2 * M + ∑' index, error index) /
          min (gamma / 2) (gamma ^ 2 / (16 * M))⌋₊ := by
  have hbox := quittingTerminalSemanticCarrier_mem_box reward (pair 0) hreward hpair0
  have hinitial : quittingTerminalSemanticDebt (pair 0) player ≤ 2 * M := by
    unfold quittingTerminalSemanticDebt
    linarith [hbox.1.1 player, hbox.2.2 player]
  apply finite_visitSet_and_ncard_le_floor _ error (2 * M) _
  · exact lt_min (half_pos hgamma) (div_pos (sq_pos_of_pos hgamma) (by positivity))
  · exact herror
  · exact hsummable
  · intro steps
    have h := fixedCapPin_prefixChain_visitCount_mul_drop_le reward pair root error player
      hM hgamma hreward hvalue hdebt hnash hprefix steps
    linarith

/-- Summable root error and summable positive debt replenishment permit only
finitely many returns to a fixed cap-pin chamber after arbitrary re-entry. -/
theorem fixedCapPin_reentry_visitSet_finite_and_ncard_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source prefixed : ℕ → QuittingTerminalSemanticPair ι)
    (root : ℕ → ι → PMF Bool) (error : ℕ → ℝ)
    (player : ι) {M gamma : ℝ}
    (hM : 0 < M) (hgamma : 0 < gamma)
    (hreward : ∀ terminal who, |reward terminal who| ≤ M)
    (hvalue : ∀ index, |(source index).1 player| ≤ M)
    (hdebt : ∀ index, 0 ≤ quittingTerminalSemanticDebt (source index) player)
    (herror : ∀ index, 0 ≤ error index) (herrorSummable : Summable error)
    (hreplenishmentSummable : Summable (fun index =>
      quittingTerminalSemanticDebtReplenishment
        (source (index + 1)) (prefixed index) player))
    (hnash : ∀ index,
      IsεQuittingRootNash reward (source index).1 (error index) (root index))
    (hprefix : ∀ index,
      prefixed index =
        quittingTerminalSemanticPrefix reward (root index) (source index)) :
    Set.Finite {index | IsFixedCapPinAt reward (source index) player gamma} ∧
      Set.ncard {index | IsFixedCapPinAt reward (source index) player gamma} ≤
        ⌊(quittingTerminalSemanticDebt (source 0) player +
            ∑' index, (error index + quittingTerminalSemanticDebtReplenishment
              (source (index + 1)) (prefixed index) player)) /
          min (gamma / 2) (gamma ^ 2 / (16 * M))⌋₊ := by
  let cost : ℕ → ℝ := fun index =>
    error index + quittingTerminalSemanticDebtReplenishment
      (source (index + 1)) (prefixed index) player
  apply finite_visitSet_and_ncard_le_floor _ cost _ _
  · exact lt_min (half_pos hgamma) (div_pos (sq_pos_of_pos hgamma) (by positivity))
  · intro index
    dsimp [cost]
    exact add_nonneg (herror index) (by
      unfold quittingTerminalSemanticDebtReplenishment
      positivity)
  · exact herrorSummable.add hreplenishmentSummable
  · exact fixedCapPin_reentry_visitCount_mul_drop_le reward source prefixed root error
      player hM hgamma hreward hvalue hdebt hnash hprefix

/-- When the first reconstructed source belongs to the semantic carrier, the
arbitrary-reentry budget starts from the uniform bound `2 * M`. -/
theorem fixedCapPin_carrierReentry_visitSet_finite_and_ncard_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source prefixed : ℕ → QuittingTerminalSemanticPair ι)
    (root : ℕ → ι → PMF Bool) (error : ℕ → ℝ)
    (player : ι) {M gamma : ℝ}
    (hM : 0 < M) (hgamma : 0 < gamma)
    (hreward : ∀ terminal who, |reward terminal who| ≤ M)
    (hsource0 : source 0 ∈ quittingTerminalSemanticCarrier reward)
    (hvalue : ∀ index, |(source index).1 player| ≤ M)
    (hdebt : ∀ index, 0 ≤ quittingTerminalSemanticDebt (source index) player)
    (herror : ∀ index, 0 ≤ error index) (herrorSummable : Summable error)
    (hreplenishmentSummable : Summable (fun index =>
      quittingTerminalSemanticDebtReplenishment
        (source (index + 1)) (prefixed index) player))
    (hnash : ∀ index,
      IsεQuittingRootNash reward (source index).1 (error index) (root index))
    (hprefix : ∀ index,
      prefixed index =
        quittingTerminalSemanticPrefix reward (root index) (source index)) :
    Set.Finite {index | IsFixedCapPinAt reward (source index) player gamma} ∧
      Set.ncard {index | IsFixedCapPinAt reward (source index) player gamma} ≤
        ⌊(2 * M + ∑' index,
            (error index + quittingTerminalSemanticDebtReplenishment
              (source (index + 1)) (prefixed index) player)) /
          min (gamma / 2) (gamma ^ 2 / (16 * M))⌋₊ := by
  let cost : ℕ → ℝ := fun index =>
    error index + quittingTerminalSemanticDebtReplenishment
      (source (index + 1)) (prefixed index) player
  have hbox := quittingTerminalSemanticCarrier_mem_box reward (source 0) hreward hsource0
  have hinitial : quittingTerminalSemanticDebt (source 0) player ≤ 2 * M := by
    unfold quittingTerminalSemanticDebt
    linarith [hbox.1.1 player, hbox.2.2 player]
  apply finite_visitSet_and_ncard_le_floor _ cost (2 * M) _
  · exact lt_min (half_pos hgamma) (div_pos (sq_pos_of_pos hgamma) (by positivity))
  · intro index
    exact add_nonneg (herror index)
      (by unfold quittingTerminalSemanticDebtReplenishment; positivity)
  · exact herrorSummable.add hreplenishmentSummable
  · intro steps
    have h := fixedCapPin_reentry_visitCount_mul_drop_le reward source prefixed root
      error player hM hgamma hreward hvalue hdebt hnash hprefix steps
    dsimp [cost]
    linarith

/-- The arbitrary-reentry finite-visit conclusion also follows directly from
summability of the coordinatewise prescribed-payoff and cap seams. -/
theorem fixedCapPin_reentry_visitSet_finite_and_ncard_le_coordinateSeams
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source prefixed : ℕ → QuittingTerminalSemanticPair ι)
    (root : ℕ → ι → PMF Bool) (error : ℕ → ℝ)
    (player : ι) {M gamma : ℝ}
    (hM : 0 < M) (hgamma : 0 < gamma)
    (hreward : ∀ terminal who, |reward terminal who| ≤ M)
    (hvalue : ∀ index, |(source index).1 player| ≤ M)
    (hdebt : ∀ index, 0 ≤ quittingTerminalSemanticDebt (source index) player)
    (herror : ∀ index, 0 ≤ error index) (herrorSummable : Summable error)
    (hpayoffSeamSummable : Summable (fun index =>
      |(source (index + 1)).1 player - (prefixed index).1 player|))
    (hcapSeamSummable : Summable (fun index =>
      |(source (index + 1)).2 player - (prefixed index).2 player|))
    (hnash : ∀ index,
      IsεQuittingRootNash reward (source index).1 (error index) (root index))
    (hprefix : ∀ index,
      prefixed index =
        quittingTerminalSemanticPrefix reward (root index) (source index)) :
    Set.Finite {index | IsFixedCapPinAt reward (source index) player gamma} ∧
      Set.ncard {index | IsFixedCapPinAt reward (source index) player gamma} ≤
        ⌊(quittingTerminalSemanticDebt (source 0) player +
            ∑' index, (error index +
              |(source (index + 1)).1 player - (prefixed index).1 player| +
              |(source (index + 1)).2 player - (prefixed index).2 player|)) /
          min (gamma / 2) (gamma ^ 2 / (16 * M))⌋₊ := by
  let cost : ℕ → ℝ := fun index =>
    error index +
      |(source (index + 1)).1 player - (prefixed index).1 player| +
      |(source (index + 1)).2 player - (prefixed index).2 player|
  apply finite_visitSet_and_ncard_le_floor _ cost _ _
  · exact lt_min (half_pos hgamma) (div_pos (sq_pos_of_pos hgamma) (by positivity))
  · intro index
    dsimp [cost]
    exact add_nonneg (add_nonneg (herror index) (abs_nonneg _)) (abs_nonneg _)
  · exact (herrorSummable.add hpayoffSeamSummable).add hcapSeamSummable
  · exact fixedCapPin_reentry_visitCount_mul_drop_le_coordinateSeams reward source
      prefixed root error player hM hgamma hreward hvalue hdebt hnash hprefix

end GameTheory
