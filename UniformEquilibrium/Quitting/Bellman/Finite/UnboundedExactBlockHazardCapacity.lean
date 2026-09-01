/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.CompactFiniteChargedReturn
import UniformEquilibrium.Quitting.Bellman.Finite.NashBellmanSpine

/-!
# Unbounded finite exact Nash--Bellman hazard capacity

An exact finite Nash--Bellman block is a positive-length finite prefix of the
exact backward correspondence, with every displayed annotation in a supplied
carrier.  Its hazard charge is the literal sum of all marginal Quit
probabilities `(root who true).toReal` before the terminal annotation.

Unbounded finite capacity means that these block charges are not bounded
above.  Compactness then supplies, at every positive metric scale, one block
with two close ordered annotations separated by hazard charge at least one.
The proof reuses the game-independent compact charged-return theorem after
normalizing each stage charge by the number of players.

The capacity in this module ranges over all supplied finite blocks.  It is not
a source-trace capacity and no approximate-equilibrium, AKRS, or hard-residual
producer for it is asserted.  This module also does not concatenate returned
blocks or construct a uniform-equilibrium payoff.
-/

noncomputable section

namespace GameTheory

open Math.ProbabilityMassFunction
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A positive-length finite exact Nash--Bellman block whose displayed
annotations all lie in `carrier`.  Values after `horizon` are merely padding;
only the displayed prefix and its exact edges are part of the block. -/
structure QuittingFiniteExactNashBellmanBlock
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (carrier : Set (QuittingNashBellmanPoint ι)) where
  horizon : ℕ
  horizon_pos : 0 < horizon
  state : ℕ → QuittingNashBellmanPoint ι
  state_mem : ∀ time, time ≤ horizon → state time ∈ carrier
  edge : ∀ time, time < horizon →
    IsQuittingNashBellmanEdge reward (state time) (state (time + 1))

namespace QuittingFiniteExactNashBellmanBlock

variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
  {carrier : Set (QuittingNashBellmanPoint ι)}

/-- Extend a finite block by its terminal annotation.  This padding is used
only to apply sequence-form compactness lemmas. -/
def paddedState
    (block : QuittingFiniteExactNashBellmanBlock reward carrier)
    (time : ℕ) : QuittingNashBellmanPoint ι :=
  block.state (min time block.horizon)

theorem paddedState_mem
    (block : QuittingFiniteExactNashBellmanBlock reward carrier)
    (time : ℕ) : block.paddedState time ∈ carrier := by
  exact block.state_mem _ (Nat.min_le_right _ _)

theorem paddedState_eq_of_le
    (block : QuittingFiniteExactNashBellmanBlock reward carrier)
    {time : ℕ} (htime : time ≤ block.horizon) :
    block.paddedState time = block.state time := by
  simp [paddedState, Nat.min_eq_left htime]

/-- The literal mixed root stored in a block annotation. -/
def root (block : QuittingFiniteExactNashBellmanBlock reward carrier)
    (time : ℕ) : ι → PMF Bool :=
  quittingRootOfSimplex (block.state time).2

/-- The displayed value at a nonterminal block stage is the exact Bellman
successor payoff of its stored root and next displayed value. -/
theorem value_eq_successor
    (block : QuittingFiniteExactNashBellmanBlock reward carrier)
    {time : ℕ} (htime : time < block.horizon) :
    (block.state time).1 = quittingRootSuccessorPayoff reward
      (block.state (time + 1)).1 (block.root time) :=
  (block.edge time htime).1

/-- Every displayed nonterminal block root is an exact one-stage Nash root
against the next displayed value. -/
theorem root_isZeroNash
    (block : QuittingFiniteExactNashBellmanBlock reward carrier)
    {time : ℕ} (htime : time < block.horizon) :
    IsεQuittingRootNash reward (block.state (time + 1)).1 0
      (block.root time) := by
  exact (isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash
    reward (block.state (time + 1)).1 (block.root time)).1
      (block.edge time htime).2

/-- One player's literal marginal Quit probability at a block stage. -/
def marginalQuitHazard
    (block : QuittingFiniteExactNashBellmanBlock reward carrier)
    (time : ℕ) (who : ι) : ℝ :=
  (block.root time who true).toReal

/-- Total marginal Quit probability at one block stage. -/
def stageHazardCharge
    (block : QuittingFiniteExactNashBellmanBlock reward carrier)
    (time : ℕ) : ℝ :=
  ∑ who, block.marginalQuitHazard time who

/-- Total marginal Quit hazard on the positive-length displayed block. -/
def hazardCharge
    (block : QuittingFiniteExactNashBellmanBlock reward carrier) : ℝ :=
  ∑ time ∈ Finset.range block.horizon, block.stageHazardCharge time

/-- Literal marginal-Quit hazard accumulated between two prefix indices. -/
def hazardChargeBetween
    (block : QuittingFiniteExactNashBellmanBlock reward carrier)
    (first second : ℕ) : ℝ :=
  (∑ time ∈ Finset.range second, block.stageHazardCharge time) -
    ∑ time ∈ Finset.range first, block.stageHazardCharge time

theorem marginalQuitHazard_nonneg
    (block : QuittingFiniteExactNashBellmanBlock reward carrier)
    (time : ℕ) (who : ι) :
    0 ≤ block.marginalQuitHazard time who :=
  ENNReal.toReal_nonneg

theorem marginalQuitHazard_le_one
    (block : QuittingFiniteExactNashBellmanBlock reward carrier)
    (time : ℕ) (who : ι) :
    block.marginalQuitHazard time who ≤ 1 := by
  exact ENNReal.toReal_mono ENNReal.one_ne_top
    (PMF.coe_le_one (block.root time who) true)

theorem stageHazardCharge_nonneg
    (block : QuittingFiniteExactNashBellmanBlock reward carrier)
    (time : ℕ) : 0 ≤ block.stageHazardCharge time := by
  exact Finset.sum_nonneg fun who _ =>
    block.marginalQuitHazard_nonneg time who

theorem stageHazardCharge_le_card
    (block : QuittingFiniteExactNashBellmanBlock reward carrier)
    (time : ℕ) :
    block.stageHazardCharge time ≤ (Fintype.card ι : ℝ) := by
  calc
    block.stageHazardCharge time ≤ ∑ _who : ι, (1 : ℝ) := by
      exact Finset.sum_le_sum fun who _ =>
        block.marginalQuitHazard_le_one time who
    _ = (Fintype.card ι : ℝ) := by simp

theorem hazardCharge_nonneg
    (block : QuittingFiniteExactNashBellmanBlock reward carrier) :
    0 ≤ block.hazardCharge := by
  exact Finset.sum_nonneg fun time _ => block.stageHazardCharge_nonneg time

end QuittingFiniteExactNashBellmanBlock

/-- Finite exact blocks have uniformly bounded hazard capacity when their
literal total hazard charges form a bounded-above subset of `ℝ`. -/
def HasBoundedFiniteExactNashBellmanHazardCapacity
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (carrier : Set (QuittingNashBellmanPoint ι)) : Prop :=
  BddAbove (Set.range fun block :
    QuittingFiniteExactNashBellmanBlock reward carrier =>
      block.hazardCharge)

/-- Finite exact blocks have unbounded hazard capacity when no uniform real
upper bound controls all literal block charges. -/
def HasUnboundedFiniteExactNashBellmanHazardCapacity
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (carrier : Set (QuittingNashBellmanPoint ι)) : Prop :=
  ¬HasBoundedFiniteExactNashBellmanHazardCapacity reward carrier

theorem hasBoundedFiniteExactNashBellmanHazardCapacity_iff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (carrier : Set (QuittingNashBellmanPoint ι)) :
    HasBoundedFiniteExactNashBellmanHazardCapacity reward carrier ↔
      ∃ bound : ℝ, ∀ block :
          QuittingFiniteExactNashBellmanBlock reward carrier,
        block.hazardCharge ≤ bound := by
  constructor
  · rintro ⟨bound, hbound⟩
    exact ⟨bound, fun block => hbound ⟨block, rfl⟩⟩
  · rintro ⟨bound, hbound⟩
    refine ⟨bound, ?_⟩
    rintro _ ⟨block, rfl⟩
    exact hbound block

theorem hasUnboundedFiniteExactNashBellmanHazardCapacity_iff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (carrier : Set (QuittingNashBellmanPoint ι)) :
    HasUnboundedFiniteExactNashBellmanHazardCapacity reward carrier ↔
      ∀ bound : ℝ, ∃ block :
          QuittingFiniteExactNashBellmanBlock reward carrier,
        bound < block.hazardCharge := by
  rw [HasUnboundedFiniteExactNashBellmanHazardCapacity,
    HasBoundedFiniteExactNashBellmanHazardCapacity, not_bddAbove_iff]
  simp only [Set.exists_range_iff]

/-- One compact near-return extracted from unbounded finite exact-block hazard
capacity.  The two annotations belong to the same positive-length exact block,
and the intervening literal marginal-Quit hazard is at least one. -/
structure QuittingFiniteExactNashBellmanHazardReturn
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (carrier : Set (QuittingNashBellmanPoint ι)) (radius : ℝ) where
  block : QuittingFiniteExactNashBellmanBlock reward carrier
  first : ℕ
  second : ℕ
  first_lt_second : first < second
  second_le_horizon : second ≤ block.horizon
  dist_lt : dist (block.state first) (block.state second) < radius
  one_le_hazardCharge_sub :
    1 ≤ block.hazardChargeBetween first second

/-- Unbounded exact-block hazard capacity in a compact annotation carrier
produces a positive-charge near-return at every positive metric radius. -/
theorem nonempty_finiteExactNashBellmanHazardReturn_of_unboundedCapacity
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (carrier : Set (QuittingNashBellmanPoint ι))
    (hcarrier : IsCompact carrier)
    (hcapacity :
      HasUnboundedFiniteExactNashBellmanHazardCapacity reward carrier)
    (radius : ℝ) (hradius : 0 < radius) :
    Nonempty (QuittingFiniteExactNashBellmanHazardReturn
      reward carrier radius) := by
  classical
  obtain ⟨threshold, hthreshold0, hreturn⟩ :=
    Math.exists_charge_threshold_for_close_pair_of_compact
      carrier hcarrier radius hradius
  have hcardPos : 0 < (Fintype.card ι : ℝ) := by
    exact_mod_cast Fintype.card_pos
  obtain ⟨block, hlarge⟩ :=
    (hasUnboundedFiniteExactNashBellmanHazardCapacity_iff
      reward carrier).mp hcapacity
      (threshold * (Fintype.card ι : ℝ))
  let normalizedCharge : ℕ → ℝ := fun time =>
    block.stageHazardCharge time / (Fintype.card ι : ℝ)
  have hnormalized0 : ∀ time, 0 ≤ normalizedCharge time := by
    intro time
    exact div_nonneg (block.stageHazardCharge_nonneg time) hcardPos.le
  have hnormalized1 : ∀ time, normalizedCharge time ≤ 1 := by
    intro time
    exact (div_le_one hcardPos).2 (block.stageHazardCharge_le_card time)
  have hnormalizedLarge :
      threshold ≤ ∑ time ∈ Finset.range block.horizon,
        normalizedCharge time := by
    rw [show (∑ time ∈ Finset.range block.horizon,
        normalizedCharge time) =
      block.hazardCharge / (Fintype.card ι : ℝ) by
        simp [normalizedCharge,
          QuittingFiniteExactNashBellmanBlock.hazardCharge,
          Finset.sum_div]]
    exact (le_div_iff₀ hcardPos).2 hlarge.le
  obtain ⟨first, second, hfirst, hsecond, hdist, hgap⟩ :=
    hreturn block.paddedState normalizedCharge block.horizon
      block.paddedState_mem
      hnormalized0 hnormalized1 hnormalizedLarge
  have hfirstLe : first ≤ block.horizon := hfirst.le.trans hsecond
  have hdist' : dist (block.state first) (block.state second) < radius := by
    simpa [block.paddedState_eq_of_le hfirstLe,
      block.paddedState_eq_of_le hsecond] using hdist
  have hgapNormalized :
      1 ≤
        (∑ time ∈ Finset.range second, block.stageHazardCharge time) /
            (Fintype.card ι : ℝ) -
          (∑ time ∈ Finset.range first, block.stageHazardCharge time) /
            (Fintype.card ι : ℝ) := by
    simpa [normalizedCharge, Finset.sum_div] using hgap
  rw [← sub_div] at hgapNormalized
  have hgapCard :
      (Fintype.card ι : ℝ) ≤
        (∑ time ∈ Finset.range second, block.stageHazardCharge time) -
          ∑ time ∈ Finset.range first, block.stageHazardCharge time := by
    simpa using (le_div_iff₀ hcardPos).mp hgapNormalized
  have honeCard : (1 : ℝ) ≤ Fintype.card ι := by
    exact_mod_cast Fintype.card_pos
  exact ⟨{
    block := block
    first := first
    second := second
    first_lt_second := hfirst
    second_le_horizon := hsecond
    dist_lt := hdist'
    one_le_hazardCharge_sub := honeCard.trans hgapCard
  }⟩

end GameTheory
