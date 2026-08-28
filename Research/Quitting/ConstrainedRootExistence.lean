/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors.
-/

import Research.Quitting.ConstrainedRootNormalWork
import UniformEquilibrium.ProofView.Concepts.Existence.CompactNash
import UniformEquilibrium.Quitting.Bellman.Finite.NashBellmanSpine
import UniformEquilibrium.Quitting.Stationary.HeterogeneousConstrainedFaceNash

/-!
# Compact existence of constrained arbitrary-tail quitting roots

This module supplies the existence step deliberately omitted from the normal-
work ledger.  It builds the compact product game on the literal intervals
`[lower who, 1]` for an arbitrary prescribed continuation payoff.  The result
is one constrained product root, not a chronology, cancellation rule, or
orientation of the cross-coordinate debt flow.
-/

noncomputable section

namespace GameTheory

open Set Math.Probability Math.ProbabilityMassFunction Math.PMFProduct

variable {iota : Type} [Fintype iota] [DecidableEq iota]

/-- Boolean simplex coordinate whose Quit mass is the supplied interval
point. -/
def quittingConstrainedRateSimplex {lower : ℝ}
    (hlower0 : 0 ≤ lower) (rate : Set.Icc lower 1) : stdSimplex ℝ Bool := by
  refine ⟨fun action => if action then rate.1 else 1 - rate.1, ?_⟩
  constructor
  · intro action
    cases action <;> simp <;>
      linarith [hlower0, rate.property.1, rate.property.2]
  · rw [Fintype.sum_bool]
    simp

/-- PMF presentation of one constrained rate. -/
def quittingConstrainedRateMarginal {lower : ℝ}
    (hlower0 : 0 ≤ lower) (rate : Set.Icc lower 1) : PMF Bool :=
  (stdSimplexEquiv (α := Bool)).symm
    (quittingConstrainedRateSimplex hlower0 rate)

@[simp] theorem quittingConstrainedRateMarginal_true_toReal
    {lower : ℝ} (hlower0 : 0 ≤ lower) (rate : Set.Icc lower 1) :
    (quittingConstrainedRateMarginal hlower0 rate true).toReal = rate.1 := by
  rw [quittingConstrainedRateMarginal, stdSimplexEquiv_symm_apply,
    ofVector_toReal]
  rfl

@[simp] theorem quittingConstrainedRateMarginal_false_toReal
    {lower : ℝ} (hlower0 : 0 ≤ lower) (rate : Set.Icc lower 1) :
    (quittingConstrainedRateMarginal hlower0 rate false).toReal =
      1 - rate.1 := by
  rw [quittingConstrainedRateMarginal, stdSimplexEquiv_symm_apply,
    ofVector_toReal]
  rfl

/-- Product root represented by a profile of constrained real rates. -/
def quittingConstrainedRoot (lower : Payoff iota)
    (hlower0 : ∀ who, 0 ≤ lower who)
    (profile : ∀ who, Set.Icc (lower who) 1) : iota → PMF Bool :=
  fun who => quittingConstrainedRateMarginal (hlower0 who) (profile who)

omit [Fintype iota] [DecidableEq iota] in
@[simp] theorem quittingConstrainedRoot_true_toReal
    (lower : Payoff iota) (hlower0 : ∀ who, 0 ≤ lower who)
    (profile : ∀ who, Set.Icc (lower who) 1)
    (who : iota) :
    (quittingConstrainedRoot lower hlower0 profile who true).toReal =
      (profile who).1 :=
  quittingConstrainedRateMarginal_true_toReal (hlower0 who) (profile who)

omit [Fintype iota] [DecidableEq iota] in
@[simp] theorem quittingConstrainedRoot_false_toReal
    (lower : Payoff iota) (hlower0 : ∀ who, 0 ≤ lower who)
    (profile : ∀ who, Set.Icc (lower who) 1)
    (who : iota) :
    (quittingConstrainedRoot lower hlower0 profile who false).toReal =
      1 - (profile who).1 :=
  quittingConstrainedRateMarginal_false_toReal (hlower0 who) (profile who)

omit [Fintype iota] in
/-- Updating one interval coordinate updates exactly the corresponding PMF
marginal. -/
theorem quittingConstrainedRoot_update
    (lower : Payoff iota) (hlower0 : ∀ who, 0 ≤ lower who)
    (profile : ∀ who, Set.Icc (lower who) 1)
    (who : iota) (rate : Set.Icc (lower who) 1) :
    quittingConstrainedRoot lower hlower0
        (Function.update profile who rate) =
      Function.update (quittingConstrainedRoot lower hlower0 profile) who
        (quittingConstrainedRateMarginal (hlower0 who) rate) := by
  funext player
  by_cases hplayer : player = who
  · subst player
    simp [quittingConstrainedRoot]
  · simp [quittingConstrainedRoot, Function.update_of_ne hplayer]

/-- The constrained-rate simplex coordinate varies continuously. -/
theorem continuous_quittingConstrainedRateSimplex
    (lower : ℝ) (hlower0 : 0 ≤ lower) :
    Continuous (quittingConstrainedRateSimplex hlower0 :
      Set.Icc lower 1 → stdSimplex ℝ Bool) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro action
  cases action
  · change Continuous fun rate : Set.Icc lower 1 => 1 - rate.1
    fun_prop
  · change Continuous fun rate : Set.Icc lower 1 => rate.1
    fun_prop

omit [Fintype iota] [DecidableEq iota] in
/-- The product simplex associated with a constrained-rate profile varies
continuously. -/
theorem continuous_quittingConstrainedRootSimplex
    (lower : Payoff iota) (hlower0 : ∀ who, 0 ≤ lower who) :
    Continuous fun profile : ∀ who, Set.Icc (lower who) 1 =>
      fun who => quittingConstrainedRateSimplex
        (hlower0 who) (profile who) := by
  apply continuous_pi
  intro who
  exact (continuous_quittingConstrainedRateSimplex
    (lower who) (hlower0 who)).comp
    (continuous_apply who)

/-- Compact continuous game whose payoffs are the literal arbitrary-tail
one-row quitting payoffs on the player-dependent box `[lower, 1]`. -/
def quittingLowerBoundTailGame
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (tail lower : Payoff iota) (hlower0 : ∀ who, 0 ≤ lower who)
    (hlower1 : ∀ who, lower who ≤ 1) :
    CompactBarycentricGame where
  Player := iota
  Strategy := fun who => Set.Icc (lower who) 1
  compactStrategy := fun _ => inferInstance
  nonemptyStrategy := fun who => ⟨⟨lower who, le_rfl, hlower1 who⟩⟩
  payoff := fun profile who =>
    quittingRootExpectedPayoff reward tail
      (quittingConstrainedRoot lower hlower0 profile) who
  payoffContinuous := fun who => by
    let simplexMap := fun profile : ∀ player, Set.Icc (lower player) 1 =>
      fun player => quittingConstrainedRateSimplex
        (hlower0 player) (profile player)
    have hmap : Continuous fun profile : ∀ player, Set.Icc (lower player) 1 =>
        (tail, simplexMap profile) :=
      continuous_const.prodMk
        (continuous_quittingConstrainedRootSimplex lower hlower0)
    have hcontinuous :=
      (continuous_quittingRootExpectedPayoff_simplex reward who).comp hmap
    change Continuous fun profile =>
      quittingRootExpectedPayoff reward tail
        (quittingRootOfSimplex (simplexMap profile)) who at hcontinuous
    exact hcontinuous.congr fun profile => by
      congr 2
  barycenter := fun who n weight point =>
    heterogeneousRateBarycenter (lower who) (hlower1 who) n weight point
  barycenterContinuous := fun who n point =>
    continuous_heterogeneousRateBarycenter (lower who) (hlower1 who) n point
  payoffBarycentric := by
    intro profile who n weight point
    simp only [quittingConstrainedRoot_update]
    rw [quittingRootExpectedPayoff_update_eq_endpointMix]
    simp_rw [quittingRootExpectedPayoff_update_eq_endpointMix]
    simp only [quittingConstrainedRateMarginal_true_toReal,
      quittingConstrainedRateMarginal_false_toReal]
    unfold heterogeneousRateBarycenter
    change
      (∑ action, weight action * (point action).1) *
            quittingRootQuitPayoff reward tail
              (quittingConstrainedRoot lower hlower0 profile) who +
          (1 - ∑ action, weight action * (point action).1) *
            quittingRootContinuePayoff reward tail
              (quittingConstrainedRoot lower hlower0 profile) who =
        ∑ action, weight action *
          ((point action).1 * quittingRootQuitPayoff reward tail
              (quittingConstrainedRoot lower hlower0 profile) who +
            (1 - (point action).1) *
              quittingRootContinuePayoff reward tail
                (quittingConstrainedRoot lower hlower0 profile) who)
    have hpoint : ∀ action,
        weight action *
            ((point action).1 * quittingRootQuitPayoff reward tail
                (quittingConstrainedRoot lower hlower0 profile) who +
              (1 - (point action).1) *
                quittingRootContinuePayoff reward tail
                  (quittingConstrainedRoot lower hlower0 profile) who) =
          (weight action * (point action).1) *
              quittingRootQuitPayoff reward tail
                (quittingConstrainedRoot lower hlower0 profile) who +
            (weight action * (1 - (point action).1)) *
              quittingRootContinuePayoff reward tail
                (quittingConstrainedRoot lower hlower0 profile) who := by
      intro action
      ring
    rw [Finset.sum_congr rfl (fun action _ => hpoint action),
      Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul]
    have hcomplement :
        (∑ action, weight action * (1 - (point action).1)) =
          1 - ∑ action, weight action * (point action).1 := by
      simp_rw [mul_sub, mul_one]
      rw [Finset.sum_sub_distrib]
      have hweight : (∑ action, weight action) = 1 := weight.property.2
      linarith
    rw [hcomplement]

/-- An exact lower-bound constrained quitting root exists over every literal
continuation payoff. -/
theorem exists_quittingLowerBoundConstrainedRoot
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (tail lower : Payoff iota)
    (hlower0 : ∀ who, 0 ≤ lower who)
    (hlower1 : ∀ who, lower who ≤ 1) :
    ∃ root : iota → PMF Bool,
      IsQuittingLowerBoundConstrainedRoot reward tail lower root := by
  obtain ⟨profile, hnash⟩ :=
    (quittingLowerBoundTailGame reward tail lower hlower0 hlower1).exists_nash
  let root := quittingConstrainedRoot lower hlower0 profile
  refine ⟨root, ?_, ?_⟩
  · intro who
    simpa [root] using (profile who).property.1
  · intro who
    let upper : Set.Icc (lower who) 1 := ⟨1, hlower1 who, le_rfl⟩
    let lowerPoint : Set.Icc (lower who) 1 :=
      ⟨lower who, le_rfl, hlower1 who⟩
    have htoUpper := sub_nonpos.mpr (hnash who upper)
    have htoLower := sub_nonpos.mpr (hnash who lowerPoint)
    dsimp only [quittingLowerBoundTailGame] at htoUpper htoLower
    rw [quittingConstrainedRoot_update] at htoUpper htoLower
    change quittingRootExpectedPayoff reward tail
          (Function.update root who
            (quittingConstrainedRateMarginal (hlower0 who) upper)) who -
        quittingRootExpectedPayoff reward tail root who ≤ 0 at htoUpper
    change quittingRootExpectedPayoff reward tail
          (Function.update root who
            (quittingConstrainedRateMarginal (hlower0 who) lowerPoint)) who -
        quittingRootExpectedPayoff reward tail root who ≤ 0 at htoLower
    have hupperDifference := quittingRootExpectedPayoff_update_sub_successorPayoff
      reward tail root who
        (quittingConstrainedRateMarginal (hlower0 who) upper)
    have hlowerDifference := quittingRootExpectedPayoff_update_sub_successorPayoff
      reward tail root who
        (quittingConstrainedRateMarginal (hlower0 who) lowerPoint)
    unfold quittingRootSuccessorPayoff at hupperDifference hlowerDifference
    rw [hupperDifference] at htoUpper
    rw [hlowerDifference] at htoLower
    have hrootTrue : (root who true).toReal = (profile who).1 := by
      simp [root]
    rw [hrootTrue] at htoUpper htoLower
    dsimp only [upper, lowerPoint] at htoUpper htoLower
    simp only [quittingConstrainedRateMarginal_true_toReal] at htoUpper
    simp only [quittingConstrainedRateMarginal_true_toReal] at htoLower
    have hcomplementarity := Math.lowerBoundComplementarity_of_endpoint_bounds
      (lower who) (profile who).1
        (quittingRootEndpointDifference reward tail root who)
        (profile who).property.1 (profile who).property.2
        htoUpper htoLower
    simpa [root] using hcomplementarity

/-- Source-faithful form: the constrained root prefixes the supplied actual
tail, and its semantic pair is literally the semantic prefix used by the
normal-work ledger. -/
theorem exists_actual_quittingLowerBoundConstrainedPrefix
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (continuation : (quittingGame reward).BehaviorProfile)
    (lower : Payoff iota)
    (hlower0 : ∀ who, 0 ≤ lower who)
    (hlower1 : ∀ who, lower who ≤ 1) :
    ∃ root : iota → PMF Bool,
      IsQuittingLowerBoundConstrainedRoot reward
          (fun who => quittingTerminalPayoff reward continuation who)
          lower root ∧
        quittingTerminalSemanticPair reward
            (quittingRootThenContinuationProfile reward root continuation) =
          quittingTerminalSemanticPrefix reward root
            (quittingTerminalSemanticPair reward continuation) := by
  obtain ⟨root, hroot⟩ := exists_quittingLowerBoundConstrainedRoot
    reward (fun who => quittingTerminalPayoff reward continuation who)
      lower hlower0 hlower1
  exact ⟨root, hroot,
    quittingTerminalSemanticPair_rootThenContinuation reward root continuation⟩

end GameTheory
