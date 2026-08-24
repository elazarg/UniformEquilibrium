/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Divergent vanishing schedules with summable sublinear cost

A nonnegative cost admits a vanishing, nonsummable scale schedule with
arbitrarily small total cost exactly when it has arbitrarily small positive
scales whose cost-to-scale ratio is arbitrarily small.  The forward
construction repeats each selected scale enough times to contribute at least
one unit of scale mass, while assigning it a geometric cost-rate budget.

The equivalence below is explicitly about schedules tending to zero.  It does
not assert necessity for arbitrary iterations: a constant legal zero-cost
scale may diverge without probing the behavior of the cost near zero.
-/

noncomputable section

open Filter Topology
open scoped BigOperators

namespace Math

/-- Operational sublinearity along positive scales tending to zero. -/
def IsOperationallySublinearCost (cost : ℝ → ℝ) : Prop :=
  ∀ epsilon, 0 < epsilon → ∀ delta, 0 < delta →
    ∃ scale, 0 < scale ∧ scale < delta ∧ cost scale ≤ epsilon * scale

/-! ## A generic positive-length block calendar -/

/-- Left endpoint of a consecutive variable-length block calendar. -/
def variableBlockStart (length : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | block + 1 => variableBlockStart length block + length block

private theorem exists_variableBlock_upper
    (length : ℕ → ℕ) (hpositive : ∀ block, 0 < length block) (time : ℕ) :
    ∃ block, time < variableBlockStart length (block + 1) := by
  refine ⟨time, ?_⟩
  have hstart : time ≤ variableBlockStart length time := by
    induction time with
    | zero => rfl
    | succ time ih =>
        rw [variableBlockStart]
        have hpos := hpositive time
        omega
  rw [variableBlockStart]
  have hpos := hpositive time
  omega

/-- The block containing a calendar time. -/
def variableBlockIndex
    (length : ℕ → ℕ) (hpositive : ∀ block, 0 < length block)
    (time : ℕ) : ℕ :=
  Nat.find (exists_variableBlock_upper length hpositive time)

theorem variableBlockIndex_upper
    (length : ℕ → ℕ) (hpositive : ∀ block, 0 < length block)
    (time : ℕ) :
    time < variableBlockStart length
      (variableBlockIndex length hpositive time + 1) :=
  Nat.find_spec (exists_variableBlock_upper length hpositive time)

theorem variableBlockStart_strictMono
    (length : ℕ → ℕ) (hpositive : ∀ block, 0 < length block) :
    StrictMono (variableBlockStart length) := by
  apply strictMono_nat_of_lt_succ
  intro block
  rw [variableBlockStart]
  have hpos := hpositive block
  omega

theorem variableBlockIndex_eq_of_mem
    (length : ℕ → ℕ) (hpositive : ∀ block, 0 < length block)
    (block time : ℕ)
    (hlower : variableBlockStart length block ≤ time)
    (hupper : time < variableBlockStart length (block + 1)) :
    variableBlockIndex length hpositive time = block := by
  apply le_antisymm
  · exact Nat.find_min'
      (exists_variableBlock_upper length hpositive time) hupper
  · by_contra hnot
    have hlt : variableBlockIndex length hpositive time < block := by omega
    have hsucc : variableBlockIndex length hpositive time + 1 ≤ block := by omega
    have hmono := (variableBlockStart_strictMono length hpositive).monotone hsucc
    have hcanonical := variableBlockIndex_upper length hpositive time
    omega

theorem variableBlockIndex_start_add
    (length : ℕ → ℕ) (hpositive : ∀ block, 0 < length block)
    (block offset : ℕ) (hoffset : offset < length block) :
    variableBlockIndex length hpositive
      (variableBlockStart length block + offset) = block := by
  apply variableBlockIndex_eq_of_mem length hpositive block
  · omega
  · rw [variableBlockStart]
    omega

theorem variableBlockIndex_tendsto_atTop
    (length : ℕ → ℕ) (hpositive : ∀ block, 0 < length block) :
    Tendsto (variableBlockIndex length hpositive) atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro block
  refine ⟨variableBlockStart length block, ?_⟩
  intro time htime
  by_contra hnot
  have hindex : variableBlockIndex length hpositive time < block := by omega
  have hstep : variableBlockIndex length hpositive time + 1 ≤ block := by omega
  have hmono := (variableBlockStart_strictMono length hpositive).monotone hstep
  have hupper := variableBlockIndex_upper length hpositive time
  omega

/-- Flatten one constant scalar value on each positive-length block. -/
def flattenVariableBlocks
    (length : ℕ → ℕ) (hpositive : ∀ block, 0 < length block)
    (value : ℕ → ℝ) (time : ℕ) : ℝ :=
  value (variableBlockIndex length hpositive time)

/-- Block-prefix sums of a flattened constant-on-block stream. -/
theorem sum_flattenVariableBlocks_to_start
    (length : ℕ → ℕ) (hpositive : ∀ block, 0 < length block)
    (value : ℕ → ℝ) (blocks : ℕ) :
    (∑ time ∈ Finset.range (variableBlockStart length blocks),
        flattenVariableBlocks length hpositive value time) =
      ∑ block ∈ Finset.range blocks, (length block : ℝ) * value block := by
  induction blocks with
  | zero => simp [variableBlockStart]
  | succ blocks ih =>
      rw [variableBlockStart, Finset.sum_range_add, ih,
        Finset.sum_range_succ]
      congr 1
      calc
        (∑ offset ∈ Finset.range (length blocks),
            flattenVariableBlocks length hpositive value
              (variableBlockStart length blocks + offset)) =
            ∑ _offset ∈ Finset.range (length blocks), value blocks := by
          apply Finset.sum_congr rfl
          intro offset hoffset
          unfold flattenVariableBlocks
          rw [variableBlockIndex_start_add length hpositive blocks offset
            (Finset.mem_range.mp hoffset)]
        _ = (length blocks : ℝ) * value blocks := by
          simp [nsmul_eq_mul]

private theorem summable_flattenVariableBlocks_of_summable_blockCost
    (length : ℕ → ℕ) (hpositive : ∀ block, 0 < length block)
    (value : ℕ → ℝ) (hvalue : ∀ block, 0 ≤ value block)
    (hblock : Summable (fun block => (length block : ℝ) * value block)) :
    Summable (flattenVariableBlocks length hpositive value) := by
  apply summable_of_sum_range_le
  · intro time
    exact hvalue _
  · intro horizon
    have hsubset : horizon ≤ variableBlockStart length (horizon + 1) := by
      exact (Nat.le_succ horizon).trans
        ((variableBlockStart_strictMono length hpositive).id_le (horizon + 1))
    calc
      (∑ time ∈ Finset.range horizon,
          flattenVariableBlocks length hpositive value time) ≤
          ∑ time ∈ Finset.range (variableBlockStart length (horizon + 1)),
            flattenVariableBlocks length hpositive value time := by
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hsubset)
          (fun time _ _ => hvalue _)
      _ = ∑ block ∈ Finset.range (horizon + 1),
          (length block : ℝ) * value block :=
        sum_flattenVariableBlocks_to_start length hpositive value (horizon + 1)
      _ ≤ ∑' block, (length block : ℝ) * value block :=
        hblock.sum_le_tsum _ (fun block _ => mul_nonneg (Nat.cast_nonneg _) (hvalue _))

/-! ## Budgeted divergent schedules -/

/-- A positive, vanishing scale schedule with divergent total scale and a
summable cost bounded by `budget`.  `cap` is a strict pointwise scale cap. -/
structure BudgetedDivergentCostSchedule
    (cost : ℝ → ℝ) (budget cap : ℝ) where
  scale : ℕ → ℝ
  scale_pos : ∀ time, 0 < scale time
  scale_lt_cap : ∀ time, scale time < cap
  scale_tendsto_zero : Tendsto scale atTop (nhds 0)
  scale_not_summable : ¬Summable scale
  cost_summable : Summable (fun time => cost (scale time))
  cost_tsum_le : ∑' time, cost (scale time) ≤ budget

namespace BudgetedDivergentCostSchedule

variable {cost : ℝ → ℝ} {budget cap : ℝ}

/-- Removing a finite prefix preserves vanishing and divergent scale, and
the summable cost tail remains available. -/
theorem drop (schedule : BudgetedDivergentCostSchedule cost budget cap)
    (start : ℕ) :
    Tendsto (fun time => schedule.scale (start + time)) atTop (nhds 0) ∧
      ¬Summable (fun time => schedule.scale (start + time)) ∧
      Summable (fun time => cost (schedule.scale (start + time))) := by
  refine ⟨?_, ?_, ?_⟩
  · change Tendsto (schedule.scale ∘ fun time => start + time) atTop (nhds 0)
    have hshift : Tendsto (fun time => start + time) atTop atTop := by
      simpa only [Nat.add_comm] using tendsto_add_atTop_nat start
    exact schedule.scale_tendsto_zero.comp hshift
  · intro hsummable
    have hshift : Summable (fun time => schedule.scale (time + start)) := by
      simpa [Nat.add_comm] using hsummable
    exact schedule.scale_not_summable ((summable_nat_add_iff start).1 hshift)
  · simpa [Nat.add_comm] using
      (summable_nat_add_iff start).2 schedule.cost_summable

end BudgetedDivergentCostSchedule

private noncomputable def selectedSublinearScale
    (cost : ℝ → ℝ) (hsublinear : IsOperationallySublinearCost cost)
    {budget cap : ℝ} (hbudget : 0 < budget) (hcap : 0 < cap)
    (n : ℕ) : ℝ :=
  Classical.choose (hsublinear
    (budget / 2 ^ (n + 2)) (by positivity)
    (min cap (1 / ((n + 1 : ℕ) : ℝ))) (by positivity))

private theorem selectedSublinearScale_spec
    (cost : ℝ → ℝ) (hsublinear : IsOperationallySublinearCost cost)
    {budget cap : ℝ} (hbudget : 0 < budget) (hcap : 0 < cap) (n : ℕ) :
    0 < selectedSublinearScale cost hsublinear hbudget hcap n ∧
      selectedSublinearScale cost hsublinear hbudget hcap n < cap ∧
      selectedSublinearScale cost hsublinear hbudget hcap n <
        1 / ((n + 1 : ℕ) : ℝ) ∧
      cost (selectedSublinearScale cost hsublinear hbudget hcap n) ≤
        (budget / 2 ^ (n + 2)) *
          selectedSublinearScale cost hsublinear hbudget hcap n := by
  have hspec := Classical.choose_spec (hsublinear
    (budget / 2 ^ (n + 2)) (by positivity)
    (min cap (1 / ((n + 1 : ℕ) : ℝ))) (by positivity))
  exact ⟨hspec.1, hspec.2.1.trans_le (min_le_left _ _),
    hspec.2.1.trans_le (min_le_right _ _), hspec.2.2⟩

private noncomputable def sublinearScaleRepetitions
    (cost : ℝ → ℝ) (hsublinear : IsOperationallySublinearCost cost)
    {budget cap : ℝ} (hbudget : 0 < budget) (hcap : 0 < cap)
    (n : ℕ) : ℕ :=
  Nat.ceil (1 / selectedSublinearScale cost hsublinear hbudget hcap n)

private theorem sublinearScaleRepetitions_pos
    (cost : ℝ → ℝ) (hsublinear : IsOperationallySublinearCost cost)
    {budget cap : ℝ} (hbudget : 0 < budget) (hcap : 0 < cap) (n : ℕ) :
    0 < sublinearScaleRepetitions cost hsublinear hbudget hcap n := by
  unfold sublinearScaleRepetitions
  rw [Nat.ceil_pos]
  exact one_div_pos.mpr
    (selectedSublinearScale_spec cost hsublinear hbudget hcap n).1

private theorem one_le_repetitions_mul_scale
    (cost : ℝ → ℝ) (hsublinear : IsOperationallySublinearCost cost)
    {budget cap : ℝ} (hbudget : 0 < budget) (hcap : 0 < cap) (n : ℕ) :
    1 ≤ (sublinearScaleRepetitions cost hsublinear hbudget hcap n : ℝ) *
      selectedSublinearScale cost hsublinear hbudget hcap n := by
  let scale := selectedSublinearScale cost hsublinear hbudget hcap n
  have hscale : 0 < scale :=
    (selectedSublinearScale_spec cost hsublinear hbudget hcap n).1
  have hceil : 1 / scale ≤
      (Nat.ceil (1 / scale) : ℝ) := Nat.le_ceil _
  have hmul := mul_le_mul_of_nonneg_right hceil hscale.le
  have hinv : (1 / scale) * scale = 1 := by
    field_simp
  rw [hinv] at hmul
  simpa [scale, sublinearScaleRepetitions] using hmul

private theorem repetitions_mul_scale_lt_two
    (cost : ℝ → ℝ) (hsublinear : IsOperationallySublinearCost cost)
    {budget cap : ℝ} (hbudget : 0 < budget) (hcap : 0 < cap) (n : ℕ) :
    (sublinearScaleRepetitions cost hsublinear hbudget hcap n : ℝ) *
        selectedSublinearScale cost hsublinear hbudget hcap n < 2 := by
  let scale := selectedSublinearScale cost hsublinear hbudget hcap n
  have hspec := selectedSublinearScale_spec cost hsublinear hbudget hcap n
  have hscale : 0 < scale := hspec.1
  have hscaleOne : scale < 1 := hspec.2.2.1.trans_le (by
    have hdenom : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.succ_pos n
    rw [one_div]
    exact (inv_le_one₀ (by positivity)).2 hdenom)
  have hceil : (Nat.ceil (1 / scale) : ℝ) < 1 / scale + 1 :=
    Nat.ceil_lt_add_one (one_div_nonneg.mpr hscale.le)
  have hmul := mul_lt_mul_of_pos_right hceil hscale
  have hsimplify : (1 / scale + 1) * scale = 1 + scale := by
    rw [add_mul, one_div_mul_cancel hscale.ne', one_mul]
  rw [hsimplify] at hmul
  simpa [scale, sublinearScaleRepetitions] using hmul.trans (by linarith)

/-- Operational sublinearity constructs a divergent vanishing schedule below
any positive cap and with total cost below any positive budget. -/
theorem exists_budgetedDivergentCostSchedule
    (cost : ℝ → ℝ) (hcost : ∀ scale, 0 ≤ cost scale)
    (hsublinear : IsOperationallySublinearCost cost)
    {budget cap : ℝ} (hbudget : 0 < budget) (hcap : 0 < cap) :
    Nonempty (BudgetedDivergentCostSchedule cost budget cap) := by
  let stageScale := selectedSublinearScale cost hsublinear hbudget hcap
  let repetitions := sublinearScaleRepetitions cost hsublinear hbudget hcap
  have hrepetitions : ∀ n, 0 < repetitions n :=
    sublinearScaleRepetitions_pos cost hsublinear hbudget hcap
  let scale := flattenVariableBlocks repetitions hrepetitions stageScale
  have hstagePos : ∀ n, 0 < stageScale n := fun n =>
    (selectedSublinearScale_spec cost hsublinear hbudget hcap n).1
  have hstageCap : ∀ n, stageScale n < cap := fun n =>
    (selectedSublinearScale_spec cost hsublinear hbudget hcap n).2.1
  have hstageZero : Tendsto stageScale atTop (nhds 0) := by
    have hupper : Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1))
        atTop (nhds 0) := tendsto_one_div_add_atTop_nhds_zero_nat
    apply squeeze_zero'
    · exact Filter.Eventually.of_forall fun n => (hstagePos n).le
    · exact Filter.Eventually.of_forall fun n =>
        (selectedSublinearScale_spec cost hsublinear hbudget hcap n).2.2.1.le
    · simpa only [Nat.cast_add, Nat.cast_one] using hupper
  have hscalePos : ∀ time, 0 < scale time := fun time => hstagePos _
  have hscaleCap : ∀ time, scale time < cap := fun time => hstageCap _
  have hscaleZero : Tendsto scale atTop (nhds 0) :=
    hstageZero.comp (variableBlockIndex_tendsto_atTop repetitions hrepetitions)
  have hscaleNotSummable : ¬Summable scale := by
    intro hsummable
    have hpartialBound : ∀ blocks : ℕ,
        (blocks : ℝ) ≤ ∑' time, scale time := by
      intro blocks
      calc
        (blocks : ℝ) = ∑ _block ∈ Finset.range blocks, (1 : ℝ) := by simp
        _ ≤ ∑ block ∈ Finset.range blocks,
            (repetitions block : ℝ) * stageScale block := by
          exact Finset.sum_le_sum fun block _ =>
            one_le_repetitions_mul_scale cost hsublinear hbudget hcap block
        _ = ∑ time ∈ Finset.range (variableBlockStart repetitions blocks),
            scale time := by
          symm
          exact sum_flattenVariableBlocks_to_start repetitions hrepetitions
            stageScale blocks
        _ ≤ ∑' time, scale time :=
          hsummable.sum_le_tsum _ (fun time _ => (hscalePos time).le)
    obtain ⟨blocks, hblocks⟩ := exists_nat_gt (∑' time, scale time)
    exact (not_lt_of_ge (hpartialBound blocks)) hblocks
  have hblockCost : ∀ n,
      (repetitions n : ℝ) * cost (stageScale n) ≤
        budget * (1 / 2 : ℝ) ^ (n + 1) := by
    intro n
    have hselected :=
      (selectedSublinearScale_spec cost hsublinear hbudget hcap n).2.2.2
    have hrep0 : 0 ≤ (repetitions n : ℝ) := Nat.cast_nonneg _
    have hmul := mul_le_mul_of_nonneg_left hselected hrep0
    have hmass := repetitions_mul_scale_lt_two
      cost hsublinear hbudget hcap n
    have hrate : 0 ≤ budget / 2 ^ (n + 2) := by positivity
    calc
      (repetitions n : ℝ) * cost (stageScale n) ≤
          (budget / 2 ^ (n + 2)) *
            ((repetitions n : ℝ) * stageScale n) := by
        simpa [stageScale, repetitions, mul_assoc, mul_left_comm, mul_comm]
          using hmul
      _ ≤ (budget / 2 ^ (n + 2)) * 2 :=
        mul_le_mul_of_nonneg_left hmass.le hrate
      _ = budget * (1 / 2 : ℝ) ^ (n + 1) := by
        rw [div_pow]
        field_simp
        ring
  have hgeom : Summable (fun n : ℕ => budget * (1 / 2 : ℝ) ^ (n + 1)) := by
    have hbase : Summable (fun n : ℕ => (1 / 2 : ℝ) ^ n) :=
      summable_geometric_of_norm_lt_one (by norm_num)
    have hshift : Summable (fun n : ℕ => (1 / 2 : ℝ) ^ (n + 1)) := by
      simpa [pow_succ', mul_comm] using hbase.mul_left (1 / 2 : ℝ)
    exact hshift.mul_left budget
  have hblockCostSummable : Summable
      (fun n => (repetitions n : ℝ) * cost (stageScale n)) :=
    Summable.of_nonneg_of_le
      (fun n => mul_nonneg (Nat.cast_nonneg _) (hcost _)) hblockCost hgeom
  have hcostSummable : Summable (fun time => cost (scale time)) := by
    exact summable_flattenVariableBlocks_of_summable_blockCost
      repetitions hrepetitions (fun n => cost (stageScale n))
      (fun n => hcost _) hblockCostSummable
  have hcostTsum : ∑' time, cost (scale time) ≤ budget := by
    have hprefix : ∀ horizon,
        (∑ time ∈ Finset.range horizon, cost (scale time)) ≤ budget := by
      intro horizon
      have hsubset : horizon ≤ variableBlockStart repetitions (horizon + 1) := by
        exact (Nat.le_succ horizon).trans
          ((variableBlockStart_strictMono repetitions hrepetitions).id_le
            (horizon + 1))
      calc
        (∑ time ∈ Finset.range horizon, cost (scale time)) ≤
            ∑ time ∈ Finset.range (variableBlockStart repetitions (horizon + 1)),
              cost (scale time) := by
          exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hsubset)
            (fun time _ _ => hcost _)
        _ = ∑ block ∈ Finset.range (horizon + 1),
            (repetitions block : ℝ) * cost (stageScale block) :=
          sum_flattenVariableBlocks_to_start repetitions hrepetitions
            (fun n => cost (stageScale n)) (horizon + 1)
        _ ≤ ∑ block ∈ Finset.range (horizon + 1),
            budget * (1 / 2 : ℝ) ^ (block + 1) :=
          Finset.sum_le_sum fun block _ => hblockCost block
        _ ≤ ∑' block, budget * (1 / 2 : ℝ) ^ (block + 1) :=
          hgeom.sum_le_tsum _ (fun block _ => by positivity)
        _ = budget := by
          have hshiftSum : (∑' block : ℕ, (1 / 2 : ℝ) ^ (block + 1)) = 1 := by
            rw [show (fun block : ℕ => (1 / 2 : ℝ) ^ (block + 1)) =
                fun block => (1 / 2 : ℝ) * (1 / 2 : ℝ) ^ block by
              funext block
              rw [pow_succ']]
            rw [tsum_mul_left,
              tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
            norm_num
          rw [tsum_mul_left, hshiftSum, mul_one]
    exact Real.tsum_le_of_sum_range_le (fun time => hcost _) hprefix
  exact ⟨{
    scale := scale
    scale_pos := hscalePos
    scale_lt_cap := hscaleCap
    scale_tendsto_zero := hscaleZero
    scale_not_summable := hscaleNotSummable
    cost_summable := hcostSummable
    cost_tsum_le := hcostTsum }⟩

/-- A vanishing divergent schedule with summable nonnegative cost forces the
operational small-ratio condition. -/
theorem isOperationallySublinearCost_of_schedule
    (cost : ℝ → ℝ) (_hcost : ∀ scale, 0 ≤ cost scale)
    (scale : ℕ → ℝ) (hscalePos : ∀ time, 0 < scale time)
    (hscaleZero : Tendsto scale atTop (nhds 0))
    (hscaleNotSummable : ¬Summable scale)
    (hcostSummable : Summable (fun time => cost (scale time))) :
    IsOperationallySublinearCost cost := by
  intro epsilon hepsilon delta hdelta
  have heventually : ∀ᶠ time : ℕ in atTop, scale time < delta :=
    (tendsto_order.1 hscaleZero).2 delta hdelta
  by_contra hnot
  push Not at hnot
  rcases eventually_atTop.1 heventually with ⟨start, hstart⟩
  have htailLe : ∀ time,
      epsilon * scale (start + time) ≤ cost (scale (start + time)) := by
    intro time
    exact (hnot (scale (start + time)) (hscalePos _) (hstart _ (by omega))).le
  have hscaledSummable : Summable (fun time => epsilon * scale (start + time)) :=
    Summable.of_nonneg_of_le
      (fun time => mul_nonneg hepsilon.le (hscalePos _).le) htailLe
      (by simpa [Nat.add_comm] using
        (summable_nat_add_iff start).2 hcostSummable)
  have htailSummable : Summable (fun time => scale (start + time)) := by
    have := hscaledSummable.mul_left (epsilon⁻¹)
    simpa [hepsilon.ne', mul_assoc] using this
  have hshift : Summable (fun time => scale (time + start)) := by
    simpa [Nat.add_comm] using htailSummable
  exact hscaleNotSummable ((summable_nat_add_iff start).1 hshift)

/-- Exact operational criterion, explicitly restricted to schedules tending
to zero.  The forward direction additionally gives arbitrary total-cost and
pointwise-scale budgets. -/
theorem isOperationallySublinearCost_iff_exists_vanishing_schedule
    (cost : ℝ → ℝ) (hcost : ∀ scale, 0 ≤ cost scale) :
    IsOperationallySublinearCost cost ↔
      ∃ scale : ℕ → ℝ,
        (∀ time, 0 < scale time) ∧
        Tendsto scale atTop (nhds 0) ∧
        ¬Summable scale ∧
        Summable (fun time => cost (scale time)) := by
  constructor
  · intro hsublinear
    obtain ⟨schedule⟩ := exists_budgetedDivergentCostSchedule
      cost hcost hsublinear (budget := 1) (cap := 1) zero_lt_one zero_lt_one
    exact ⟨schedule.scale, schedule.scale_pos, schedule.scale_tendsto_zero,
      schedule.scale_not_summable, schedule.cost_summable⟩
  · rintro ⟨scale, hpos, hzero, hdiverges, hsummable⟩
    exact isOperationallySublinearCost_of_schedule
      cost hcost scale hpos hzero hdiverges hsummable

end Math
