/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Bellman.Finite.PunishmentFloorChargedRelation
import UniformEquilibrium.Quitting.Bellman.Finite.UnboundedExactBlockHazardCapacity
import UniformEquilibrium.Quitting.Root.OpponentCoalitionMass

/-!
# Full-box exact-predecessor absorption budget

The full boxed charged relation orients an exact predecessor edge from its
tail to its predecessor.  The finite exact-block capacity interface uses the
opposite chronological indexing.  This file reverses every literal finite
charged path into a finite exact Nash--Bellman block and compares the path's
joint-absorption charge with the block's total marginal-Quit hazard.

Consequently, a common bound on all finite exact-block hazards gives a finite
budget and the canonical bounded budget-to-go potential on the full boxed
relation.  No punishment-floor reachability, source construction, or
horizontal strategy update is assumed.
-/

noncomputable section

namespace GameTheory

open Math.ChargedPathBudget

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

namespace QuittingFullBoxExactPredecessorPath

private abbrev BoxState
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :=
  QuittingPunishmentFloorBoxState reward

private abbrev BoxRelation
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :=
  quittingPunishmentFloorBoxChargedRelation reward

/-- Read a full-box predecessor path in the reverse order used by finite
exact Nash--Bellman blocks.  Values after the horizon are harmless padding.
-/
def reversedState : {source target : BoxState reward} →
    (BoxRelation reward).Path source target → ℕ → BoxState reward
  | _, _, .nil state, _ => state
  | _, _, .cons edge rest, time =>
      if time ≤ rest.length then reversedState rest time else edge.tail

@[simp] theorem reversedState_nil (state : BoxState reward) (time : ℕ) :
    reversedState (ChargedRelation.Path.nil state :
      (BoxRelation reward).Path state state) time = state := rfl

@[simp] theorem reversedState_cons
    (edge : QuittingPunishmentFloorBoxEdge reward)
    {target : BoxState reward}
    (rest : (BoxRelation reward).Path
      ((BoxRelation reward).tgt edge) target) (time : ℕ) :
    reversedState (ChargedRelation.Path.cons edge rest) time =
      if time ≤ rest.length then reversedState rest time else edge.tail := rfl

/-- The reversed block starts at the target of the charged path. -/
@[simp] theorem reversedState_zero
    {source target : BoxState reward}
    (path : (BoxRelation reward).Path source target) :
    reversedState path 0 = target := by
  induction path with
  | nil state => rfl
  | cons edge rest ih =>
      simpa only [reversedState_cons, Nat.zero_le, if_true] using ih

/-- The reversed block ends at the source of the charged path. -/
@[simp] theorem reversedState_length
    {source target : BoxState reward}
    (path : (BoxRelation reward).Path source target) :
    reversedState path path.length = source := by
  induction path with
  | nil state => rfl
  | cons edge rest ih =>
      simp only [ChargedRelation.Path.length_cons, reversedState_cons]
      rw [if_neg (Nat.not_succ_le_self _)]
      rfl

/-- Adjacent reversed states are literal exact Nash--Bellman edges. -/
theorem exactEdge
    {source target : BoxState reward}
    (path : (BoxRelation reward).Path source target)
    (time : ℕ) (htime : time < path.length) :
    IsQuittingNashBellmanEdge reward
      (reversedState path time).1
      (reversedState path (time + 1)).1 := by
  induction path generalizing time with
  | nil state => simp at htime
  | cons edge rest ih =>
      simp only [ChargedRelation.Path.length_cons] at htime
      by_cases hbefore : time < rest.length
      · have htimeLe : time ≤ rest.length := hbefore.le
        have hnextLe : time + 1 ≤ rest.length := hbefore
        simpa only [reversedState_cons, if_pos htimeLe, if_pos hnextLe]
          using ih time hbefore
      · have htimeEq : time = rest.length := by omega
        subst time
        simp only [reversedState_cons, if_pos le_rfl,
          if_neg (Nat.not_succ_le_self _)]
        rw [reversedState_length]
        exact edge.exactEdge

/-- Reverse a positive-length full-box path into the existing finite exact
Nash--Bellman block interface. -/
def toFiniteExactNashBellmanBlock
    {source target : BoxState reward}
    (path : (BoxRelation reward).Path source target)
    (hpositive : 0 < path.length) :
    QuittingFiniteExactNashBellmanBlock reward
      (quittingNashBellmanBox (quittingRewardBound reward)) where
  horizon := path.length
  horizon_pos := hpositive
  state time := (reversedState path time).1
  state_mem time _ := (reversedState path time).2
  edge time htime := exactEdge path time htime

/-- Total marginal-Quit hazard of the reversed states before the path's
source endpoint.  Unlike the finite-block wrapper, this also covers the
empty path. -/
def reversedMarginalHazardCharge
    {source target : BoxState reward}
    (path : (BoxRelation reward).Path source target) : ℝ :=
  ∑ time ∈ Finset.range path.length,
    ∑ who, ((quittingRootOfSimplex (reversedState path time).1.2) who true).toReal

/-- Joint absorption along a full-box path is bounded by the marginal hazard
of the same roots read in reverse chronological order. -/
theorem chargeSum_le_reversedMarginalHazardCharge
    {source target : BoxState reward}
    (path : (BoxRelation reward).Path source target) :
    path.chargeSum ≤ reversedMarginalHazardCharge path := by
  induction path with
  | nil state => simp [reversedMarginalHazardCharge]
  | cons edge rest ih =>
      have hprefix :
          (∑ time ∈ Finset.range rest.length,
            ∑ who,
              ((quittingRootOfSimplex
                (reversedState (ChargedRelation.Path.cons edge rest) time).1.2)
                  who true).toReal) =
            reversedMarginalHazardCharge rest := by
        rw [reversedMarginalHazardCharge]
        apply Finset.sum_congr rfl
        intro time htime
        rw [reversedState_cons, if_pos (Finset.mem_range.mp htime).le]
      have hlast :
          (∑ who,
            ((quittingRootOfSimplex
              (reversedState (ChargedRelation.Path.cons edge rest)
                rest.length).1.2) who true).toReal) =
            ∑ who, (edge.root who true).toReal := by
        rw [reversedState_cons, if_pos le_rfl, reversedState_length]
        rfl
      rw [reversedMarginalHazardCharge,
        ChargedRelation.Path.length_cons, Finset.sum_range_succ, hprefix, hlast]
      simp only [ChargedRelation.Path.chargeSum_cons]
      change edge.absorptionCharge + rest.chargeSum ≤
        reversedMarginalHazardCharge rest +
          ∑ who, (edge.root who true).toReal
      have habsorption :=
        quittingRootAbsorptionMass_le_sum_quitProbability edge.root
      change edge.absorptionCharge ≤ ∑ who, (edge.root who true).toReal at habsorption
      linarith

/-- The joint-absorption charge of a full-box path is at most the total
marginal-Quit hazard of its reversed finite exact block. -/
theorem chargeSum_le_hazardCharge_toFiniteExactNashBellmanBlock
    {source target : BoxState reward}
    (path : (BoxRelation reward).Path source target)
    (hpositive : 0 < path.length) :
    path.chargeSum ≤
      (toFiniteExactNashBellmanBlock path hpositive).hazardCharge := by
  exact chargeSum_le_reversedMarginalHazardCharge path

end QuittingFullBoxExactPredecessorPath

open QuittingFullBoxExactPredecessorPath

/-- Bounded marginal-hazard capacity for all finite exact Nash--Bellman
blocks bounds the joint-absorption charge of every path in the full boxed
exact-predecessor relation. -/
theorem quittingFullBoxExactPredecessor_hasFiniteBudget_of_boundedHazardCapacity
    (hcapacity : HasBoundedFiniteExactNashBellmanHazardCapacity reward
      (quittingNashBellmanBox (quittingRewardBound reward))) :
    (quittingPunishmentFloorBoxChargedRelation reward).HasFiniteBudget := by
  rw [hasBoundedFiniteExactNashBellmanHazardCapacity_iff] at hcapacity
  obtain ⟨bound, hbound⟩ := hcapacity
  refine ⟨max bound 0, ?_⟩
  rintro charge ⟨source, target, path, rfl⟩
  by_cases hpositive : 0 < path.length
  · exact
      (chargeSum_le_hazardCharge_toFiniteExactNashBellmanBlock path hpositive)
        |>.trans (hbound _)
        |>.trans (le_max_left _ _)
  · have hzero : path.length = 0 := by omega
    cases path with
    | nil state => exact le_max_right _ _
    | cons edge rest => simp at hzero

/-- Under bounded exact-block hazard capacity, the canonical budget-to-go on
the full boxed predecessor relation is a bounded potential. -/
theorem quittingFullBoxExactPredecessor_value_isBoundedPotential_of_boundedHazardCapacity
    (hcapacity : HasBoundedFiniteExactNashBellmanHazardCapacity reward
      (quittingNashBellmanBox (quittingRewardBound reward))) :
    (quittingPunishmentFloorBoxChargedRelation reward).IsBoundedPotential
      (quittingPunishmentFloorBoxChargedRelation reward).value := by
  exact (quittingPunishmentFloorBoxChargedRelation reward).value_isBoundedPotential
    (quittingFullBoxExactPredecessor_hasFiniteBudget_of_boundedHazardCapacity
      hcapacity)

end GameTheory
