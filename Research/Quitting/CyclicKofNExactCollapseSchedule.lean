/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Research.Quitting.CyclicKofNPrimitiveBlocks
import Research.Quitting.CyclicKofNQuittingSchedule

/-!
# Exact-collapse `K/N` quitting schedules

This file packages the arithmetic converse as a literal quitting-game
support clock.  For factored parameters

`K = k*d`, `N = n*d`, `0 < k < n`,

the construction has exactly `K` positive hazards at every stage, exactly
`N` players, translation stabilizer `d`, and minimal distinct-block period
`n = N/d`.

The common positive hazard is arbitrary.  Thus the theorem controls support
and interaction degree while leaving the payoff-specific Bellman or
circulation equations to a separate certificate.
-/

namespace GameTheory

namespace CyclicKofNExactCollapseSchedule

open StochasticGame Math.Probability Math.PMFProduct
open CyclicKofNArithmetic CyclicKofNFiberLift
  CyclicKofNPrimitiveBlocks CyclicKofNQuittingSchedule
open scoped Pointwise BigOperators

noncomputable section

/-- The canonical block realizing collapse factor `d`. -/
def exactCollapseBlock (n k d : ℕ) [NeZero d] :
    Finset (ZMod n × ZMod d) :=
  fiberLift (H := ZMod d) (initialBlock n k)

/-- The public quitting schedule attached to the exact-collapse block. -/
def exactCollapseSchedule (n k d : ℕ) [NeZero n] [NeZero d] :
    QuittingKActiveSchedule (ZMod n × ZMod d)
      (exactCollapseBlock n k d).card :=
  cyclicSchedule (exactCollapseBlock n k d)

/-- Common-positive-hazard roots on the exact-collapse schedule. -/
def exactCollapseRoots (n k d : ℕ) [NeZero n] [NeZero d]
    (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) :
    ℕ → (ZMod n × ZMod d) → PMF Bool :=
  cyclicRoots (exactCollapseBlock n k d) β hβ0 hβ1

theorem card_exactCollapseBlock {n k d : ℕ} [NeZero n] [NeZero d]
    (hk : k ≤ n) :
    (exactCollapseBlock n k d).card = k * d := by
  simp [exactCollapseBlock, card_fiberLift, card_initialBlock hk]

theorem card_exactCollapsePopulation (n d : ℕ) [NeZero n] [NeZero d] :
    Fintype.card (ZMod n × ZMod d) = n * d := by simp

/-- The constructed block has exact collapse factor `d`. -/
theorem card_stabilizer_exactCollapseBlock
    {n k d : ℕ} [NeZero n] [NeZero d]
    (hkpos : 0 < k) (hkproper : k < n) :
    Fintype.card
        (AddAction.stabilizer (ZMod n × ZMod d)
          (exactCollapseBlock n k d)) = d := by
  unfold exactCollapseBlock
  rw [card_stabilizer_fiberLift_of_primitive (initialBlock n k)]
  · simp
  · exact initialBlock_stabilizer_card_eq_one hkpos hkproper

/-- The number of distinct public blocks is exactly `n = N/d`. -/
theorem card_translationPhase_exactCollapseBlock
    {n k d : ℕ} [NeZero n] [NeZero d]
    (hkpos : 0 < k) (hkproper : k < n) :
    Fintype.card (TranslationPhase (exactCollapseBlock n k d)) = n := by
  unfold exactCollapseBlock
  rw [card_translationPhase_fiberLift,
    card_translationPhase_initialBlock hkpos hkproper]

/-- Every stage has exactly `k*d` scheduled active players. -/
theorem card_exactCollapseSchedule_active
    {n k d : ℕ} [NeZero n] [NeZero d]
    (hk : k ≤ n) (time : ℕ) :
    ((exactCollapseSchedule n k d).active time).card = k * d := by
  calc
    ((exactCollapseSchedule n k d).active time).card =
        (exactCollapseBlock n k d).card :=
      card_cyclicSchedule_active (exactCollapseBlock n k d) time
    _ = k * d := card_exactCollapseBlock hk

/-- The schedule has exact period `n`; this is the full orbit rather than an
unreduced period with duplicate blocks. -/
theorem exactCollapseSchedule_active_add_period
    {n k d : ℕ} [NeZero n] [NeZero d]
    (hkpos : 0 < k) (hkproper : k < n) (time : ℕ) :
    (exactCollapseSchedule n k d).active (time + n) =
      (exactCollapseSchedule n k d).active time := by
  have hperiod := cyclicSchedule_active_add_period
    (exactCollapseBlock n k d) time
  rwa [card_translationPhase_exactCollapseBlock hkpos hkproper] at hperiod

/-- Every distinct active block occurs within the exact `n`-phase period. -/
theorem exactCollapseSchedule_covers_translationPhase
    {n k d : ℕ} [NeZero n] [NeZero d]
    (hkpos : 0 < k) (hkproper : k < n)
    (B : TranslationPhase (exactCollapseBlock n k d)) :
    ∃ time < n,
      (exactCollapseSchedule n k d).active time = orbitSchedule
        (exactCollapseBlock n k d) B := by
  obtain ⟨time, htime, hclock⟩ :=
    translationClock_surjective_period (exactCollapseBlock n k d) B
  refine ⟨time, ?_, ?_⟩
  · rwa [card_translationPhase_exactCollapseBlock hkpos hkproper] at htime
  · change orbitSchedule (exactCollapseBlock n k d)
      (translationClock (exactCollapseBlock n k d) time) =
        orbitSchedule (exactCollapseBlock n k d) B
    rw [hclock]

/-- With positive common hazard, every root has exactly `k*d` positive
quitting coordinates. -/
theorem card_positiveHazardSupport_exactCollapseRoots
    {n k d : ℕ} [NeZero n] [NeZero d]
    (hk : k ≤ n) (β : ℝ) (hβ1 : β ≤ 1)
    (hβpos : 0 < β) (time : ℕ) :
    (quittingPositiveHazardSupport
      (exactCollapseRoots n k d β hβpos.le hβ1 time)).card = k * d := by
  calc
    (quittingPositiveHazardSupport
      (exactCollapseRoots n k d β hβpos.le hβ1 time)).card =
        (exactCollapseBlock n k d).card :=
      card_positiveHazardSupport_cyclicRoots
        (exactCollapseBlock n k d) β hβ1 hβpos time
    _ = k * d := card_exactCollapseBlock hk

/-- The behavioral root sequence itself has exact period `n`. -/
theorem exactCollapseRoots_add_period
    {n k d : ℕ} [NeZero n] [NeZero d]
    (hkpos : 0 < k) (hkproper : k < n)
    (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (time : ℕ) :
    exactCollapseRoots n k d β hβ0 hβ1 (time + n) =
      exactCollapseRoots n k d β hβ0 hβ1 time := by
  have hperiod := cyclicRoots_add_period
    (exactCollapseBlock n k d) β hβ0 hβ1 time
  rwa [card_translationPhase_exactCollapseBlock hkpos hkproper] at hperiod

/-- The roots respect the exact-collapse public support schedule. -/
theorem exactCollapseRoots_respects_schedule
    (n k d : ℕ) [NeZero n] [NeZero d]
    (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) :
    IsQuittingActiveScheduleRoot (exactCollapseSchedule n k d)
      (exactCollapseRoots n k d β hβ0 hβ1) :=
  cyclicRoots_respects_schedule (exactCollapseBlock n k d) β hβ0 hβ1

/-- Bellman interaction order for the exact-collapse schedule is its exact
stage support size `k*d`, regardless of the ambient size `n*d`. -/
theorem exactBellmanSpine_degree_exactCollapseBlock
    {n k d : ℕ} [NeZero n] [NeZero d]
    (reward : {S : Finset (ZMod n × ZMod d) // S.Nonempty} →
      Payoff (ZMod n × ZMod d))
    (value : ℕ → Payoff (ZMod n × ZMod d))
    (roots : ℕ → (ZMod n × ZMod d) → PMF Bool)
    (hsupport : IsQuittingActiveScheduleRoot
      (exactCollapseSchedule n k d) roots)
    (hspine : IsCanonicalExactQuittingNashBellmanSpine reward value roots)
    (time : ℕ) (who : ZMod n × ZMod d) :
    value time who = value (time + 1) who +
      ∑ degree ∈ Finset.range ((exactCollapseBlock n k d).card + 1),
        quittingActiveMobiusLayer reward (value (time + 1))
          ((exactCollapseSchedule n k d).active time)
          (roots time) who degree := by
  exact exactBellmanSpine_value_eq_next_add_sum_layers_of_cyclicSchedule
    reward value roots (exactCollapseBlock n k d)
      hsupport hspine time who

end

end CyclicKofNExactCollapseSchedule

end GameTheory
