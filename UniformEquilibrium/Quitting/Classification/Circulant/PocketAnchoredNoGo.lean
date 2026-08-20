/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.Periodicity
import UniformEquilibrium.Quitting.Classification.Circulant.Trichotomy
import UniformEquilibrium.Quitting.Cycles.AnchoredCyclicPatience

/-!
# No anchored cyclic patience system on an open-pocket circulant table

For a table whose normalized solo matrix is circulant, both margin conditions
of `Research/Quitting/AnchoredCyclicPatience.lean` read off the same group
difference.  Writing `s = w_{k+1} - w_k` for the step taken at phase `k`,
successor patience says `margin s ≤ 0` and predecessor patience, applied to the
same pair in the other direction, says `margin (-s) ≥ 0`.  A step is therefore
admissible only where the margin vector is nonpositive at `s` and nonnegative
at `-s`.

On five players no step at all survives in the *open pocket* — the sign pattern
in which both neighbour margins are negative and both distant margins are
positive.  There `margin s ≤ 0` rules out the two distant steps and
`margin (-s) ≥ 0` rules out the two neighbour steps, so every step vanishes and
the schedule never changes its quitter.  A constant schedule is then excluded by
the tolerance lemma: the player one step ahead of that quitter would have to
have a nonnegative margin against it, and in the open pocket that margin is one
of the two negative neighbour margins.

The surplus plays no part in this argument, and neither does the period, the
support size, or uniformity of the survival vector.

## What the emptiness statement does and does not say

Everything here is about `QuittingAnchoredCyclicPatienceSystem`, whose patience
field is the vanishing-hazard reading of a player's incentive not to quit.  At a
fixed hazard that incentive compares against the mixture
`spectatorQuitNowValue`, which sits strictly below the solo self payoff whenever
pair rows pay their members strictly less than their solo self payoffs.  On such
a table the structure is a strictly stronger demand than the fixed-hazard
comparison, and its emptiness carries no information about which behaviour
profiles the table admits.  The two demands coincide on tables whose pair rows
pay their members exactly their solo self payoffs.

## Main definitions

* `IsOpenPocketMargin` — the five-player open-pocket sign pattern

## Main results

* `step_margin_nonpos` and `step_margin_neg_nonneg` — the two margin
  conditions written on the step of a circulant table
* `step_eq_zero_of_isOpenPocketMargin` — in the open pocket only the zero step
  carries both margin signs
* `isEmpty_anchoredCyclicPatienceSystem_of_isOpenPocketMargin` — no anchored
  cyclic patience system exists over an open-pocket circulant table, at any
  period
-/

noncomputable section

namespace GameTheory
namespace QuittingLCPClassification

open Math Math.LinearProgramming

variable {ι : Type} [Fintype ι] [DecidableEq ι] [AddCommGroup ι]
  {reward : {S : Finset ι // S.Nonempty} → Payoff ι} {margin : ι → ℝ}
  {m : ℕ} [NeZero m]

/-! ## The two margin conditions on a step -/

/-- Successor patience of an anchored cyclic patience system on a circulant
table: the step taken at a phase has nonpositive margin. -/
theorem step_margin_nonpos (h : HasCirculantSoloMatrix reward margin)
    (system : QuittingAnchoredCyclicPatienceSystem reward m) (k : Fin m) :
    margin (system.order (k + 1) - system.order k) ≤ 0 := by
  have hstep := system.successor_margin_nonpos k
  rw [h] at hstep
  exact hstep

/-- Predecessor patience of an anchored cyclic patience system on a circulant
table: the reversed step has nonnegative margin. -/
theorem step_margin_neg_nonneg (h : HasCirculantSoloMatrix reward margin)
    (system : QuittingAnchoredCyclicPatienceSystem reward m) (k : Fin m) :
    0 ≤ margin (-(system.order (k + 1) - system.order k)) := by
  have hstep := system.predecessor_margin_nonneg k
  rw [h] at hstep
  rw [neg_sub]
  exact hstep

/-! ## The five-player open pocket -/

/-- The open pocket of five-player circulant margins: both neighbour margins
are strictly negative and both distant margins are strictly positive.

Strictness at the two distant distances is what `step_eq_zero_of_isOpenPocketMargin`
consumes, and it cannot be relaxed to nonnegativity.  On a face where a distant
margin vanishes, the step at that distance has nonpositive margin and its
reverse — the other distant distance — has nonnegative margin, so that step
passes both patience conditions and the schedule may move.  Strictness at the
two neighbour distances is the negativity of the pocket itself. -/
def IsOpenPocketMargin (margin : ZMod 5 → ℝ) : Prop :=
  margin 1 < 0 ∧ margin 4 < 0 ∧ 0 < margin 2 ∧ 0 < margin 3

/-- Every element of the five-element cyclic group is one of its five
numerals. -/
theorem zmod_five_eq_or (s : ZMod 5) : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 := by
  revert s
  decide

/-- **Only the zero step carries both margin signs in the open pocket.**  A
group element whose margin is nonpositive and whose negative has nonnegative
margin is zero. -/
theorem step_eq_zero_of_isOpenPocketMargin {margin : ZMod 5 → ℝ}
    (hpocket : IsOpenPocketMargin margin) {s : ZMod 5} (hforward : margin s ≤ 0)
    (hbackward : 0 ≤ margin (-s)) : s = 0 := by
  obtain ⟨hone, hfour, htwo, hthree⟩ := hpocket
  rcases zmod_five_eq_or s with rfl | rfl | rfl | rfl | rfl
  · rfl
  · rw [show -(1 : ZMod 5) = 4 from by decide] at hbackward
    linarith
  · linarith
  · linarith
  · rw [show -(4 : ZMod 5) = 1 from by decide] at hbackward
    linarith

/-- **No anchored cyclic patience system over an open-pocket circulant
table.**  Every step of the schedule vanishes, so the schedule has a single
quitter throughout, and the player one step ahead of that quitter contradicts
the tolerance lemma.

The emptiness is that of the anchored structure, whose patience field demands
each phase value be at or above the solo self payoff.  It is not a statement
about the behaviour profiles of the table. -/
theorem isEmpty_anchoredCyclicPatienceSystem_of_isOpenPocketMargin
    {reward : {S : Finset (ZMod 5) // S.Nonempty} → Payoff (ZMod 5)}
    {margin : ZMod 5 → ℝ} (h : HasCirculantSoloMatrix reward margin)
    (hpocket : IsOpenPocketMargin margin) (m : ℕ) [NeZero m] :
    IsEmpty (QuittingAnchoredCyclicPatienceSystem reward m) := by
  constructor
  intro system
  have hsucc : ∀ k : Fin m, system.order (k + 1) = system.order k := by
    intro k
    have hzero := step_eq_zero_of_isOpenPocketMargin hpocket
      (step_margin_nonpos h system k) (step_margin_neg_nonneg h system k)
    exact sub_eq_zero.mp hzero
  obtain ⟨quitter, hquitter⟩ := exists_const_of_cyclic_succ_eq hsucc
  obtain ⟨phase, hphase⟩ := system.exists_margin_nonneg (quitter + 1)
  rw [h, hquitter phase] at hphase
  have hval : quitter - (quitter + 1) = (4 : ZMod 5) := by
    have hneg : quitter - (quitter + 1) = -1 := by ring
    rw [hneg]
    decide
  rw [rowCirculant_apply, hval] at hphase
  linarith [hpocket.2.1]

end QuittingLCPClassification
end GameTheory
