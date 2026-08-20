/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegime.AnchoredCyclicScreen
import UniformEquilibrium.Quitting.Cycles.AnchoredCyclicScreen
import UniformEquilibrium.Quitting.Classification.ImmediateSingletonCollision
import UniformEquilibrium.Quitting.Classification.PreemptionCycle

/-!
# Consecutive phases of an anchored solo-periodic schedule

`IsExactAnchoredSoloPeriodic` and `IsεExactAnchoredSoloPeriodic`
(`UniformEquilibrium/Quitting/Cycles/AnchoredSoloPeriodic.lean`) read the
one-stage endpoint Nash condition of a single-quitter periodic schedule phase
by phase.  This module couples two *consecutive* phases: the successor of a
phase is itself the scheduled quitter one step later, so the spectator floor
at a phase can be evaluated at the next phase's own quitter.

At exactness the coupling is an equality.  The indifference anchor
`anchor_of_isExactAnchoredSoloPeriodic` and the renewal
`quittingAnchoredCyclicOnPathValue_renewal` make each scheduled player's
on-path value equal to its own solo exit already at its own phase
(`quittingAnchoredCyclicOnPathValue_scheduled_of_isExactAnchoredSoloPeriodic`),
so the successor enters the predecessor's spectator floor with zero
continuation surplus and the floor degenerates to a comparison of two rows of
the table:

`r_succ({pred, succ}) ≤ r_succ({pred})`

(`quittingSoloCollisionPenalty_nonpos_of_isExactAnchoredSoloPeriodic` and its
unfolded form `pairReward_le_soloReward_of_isExactAnchoredSoloPeriodic`).
Consecutive distinctness of the two scheduled players is the only structural
hypothesis; the schedule may repeat a player elsewhere in its period.

Two consequences read the comparison against the leaf data of the quitting
counterexample question.  On an edge of the strict solo-preemption relation
`QuittingSoloPreempts` the successor's collision row sits a full margin below
its own solo row
(`QuittingSoloPreempts.pairReward_add_gap_le_of_isExactAnchoredSoloPeriodic`),
and a `QuittingImmediateSingletonCollision` whose owner and collider are
consecutive scheduled players contradicts exactness outright at every interior
hazard vector
(`not_isExactAnchoredSoloPeriodic_of_immediateSingletonCollision_on_edge`).

At accuracy `ε` the successor's continuation surplus is no longer zero, but
its own hazard still prices it: `q * surplus ≤ (1 - q) * ε`
(`hazard_mul_continuationSurplus_scheduled_le_of_isεExactAnchoredSoloPeriodic`).
Multiplying the predecessor's spectator floor by that hazard clears the
denominator and leaves the branch-free product bound

`p * q * (r_succ({pred, succ}) - r_succ({pred})) ≤ ε`

(`hazard_mul_hazard_mul_soloCollisionPenalty_le_of_isεExactAnchoredSoloPeriodic`),
with no case split on which of the two hazards is small and no positivity
hypothesis on either.  The two accuracies enter with coefficients `q` and
`(1 - p) * (1 - q)`, which sum to `1 - p * (1 - q) ≤ 1`, so a single scalar
accuracy is not doubled.  Read against a collision certificate this is
`hazard_mul_hazard_mul_margin_le_of_isεExactAnchoredSoloPeriodic`: an
attractive collision on a consecutive edge forces the product of the two
adjacent hazards to vanish with the accuracy, while leaving either hazard
alone unconstrained.
-/

noncomputable section

namespace GameTheory

open StochasticGame

variable {ι : Type} [Fintype ι] [DecidableEq ι] {m : ℕ}

/-! ## The scheduled player's own value at exactness -/

/-- **The scheduled quitter's value is its solo exit already at its own
phase.**  The indifference anchor pins the next phase's value of the scheduled
player, and the renewal at that phase mixes that value with the same solo
reward, so the mixture returns it unchanged. -/
theorem quittingAnchoredCyclicOnPathValue_scheduled_of_isExactAnchoredSoloPeriodic
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {w : Fin m → ι} {hazard : Fin m → ℝ}
    {h0 : ∀ k, 0 ≤ hazard k} {h1 : ∀ k, hazard k ≤ 1}
    (hexact : IsExactAnchoredSoloPeriodic reward w hazard h0 h1)
    (hpos : ∀ k, 0 < hazard k) (hlt : ∀ k, hazard k < 1) (phase : Fin m) :
    quittingAnchoredCyclicOnPathValue reward w hazard h0 h1 phase (w phase) =
      reward (quittingSingletonTerminal (w phase)) (w phase) := by
  have hrenewal := quittingAnchoredCyclicOnPathValue_renewal reward w hazard h0 h1
    phase (w phase)
  have hanchor := anchor_of_isExactAnchoredSoloPeriodic hexact hpos hlt phase
  rw [hrenewal, ← hanchor]
  ring

/-- **The scheduled quitter's continuation surplus is priced by its own
hazard.**  The renewal factors the surplus at a phase through the surplus at
the next phase, and the upper anchor bound caps the latter by `ε`. -/
theorem hazard_mul_continuationSurplus_scheduled_le_of_isεExactAnchoredSoloPeriodic
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι} {ε : ℝ}
    {w : Fin m → ι} {hazard : Fin m → ℝ}
    {h0 : ∀ k, 0 ≤ hazard k} {h1 : ∀ k, hazard k ≤ 1}
    (hexact : IsεExactAnchoredSoloPeriodic reward ε w hazard h0 h1)
    (phase : Fin m) :
    hazard phase *
        quittingContinuationSurplus reward
          (quittingAnchoredCyclicOnPathValue reward w hazard h0 h1 phase)
          (w phase) ≤
      (1 - hazard phase) * ε := by
  have hrenewal := quittingAnchoredCyclicOnPathValue_renewal reward w hazard h0 h1
    phase (w phase)
  have hupper := anchorUpperBound_of_isεExactAnchoredSoloPeriodic hexact phase
  have hsurvive : (0 : ℝ) ≤ 1 - hazard phase := by linarith [h1 phase]
  unfold quittingContinuationSurplus
  have hfactor : hazard phase *
        (quittingAnchoredCyclicOnPathValue reward w hazard h0 h1 phase (w phase) -
          reward (quittingSingletonTerminal (w phase)) (w phase)) =
      (1 - hazard phase) *
        (hazard phase *
          (quittingAnchoredCyclicOnPathValue reward w hazard h0 h1
              (finRotate m phase) (w phase) -
            reward (quittingSingletonTerminal (w phase)) (w phase))) := by
    rw [hrenewal]; ring
  rw [hfactor]
  exact mul_le_mul_of_nonneg_left hupper hsurvive

/-! ## The pair-row no-go on a consecutive edge -/

/-- **The exact pair-row no-go.**  At an exact schedule with interior hazards,
the player scheduled next has nothing to gain from joining its predecessor's
solo exit: its collision penalty against that predecessor is nonpositive. -/
theorem quittingSoloCollisionPenalty_nonpos_of_isExactAnchoredSoloPeriodic
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {w : Fin m → ι} {hazard : Fin m → ℝ}
    {h0 : ∀ k, 0 ≤ hazard k} {h1 : ∀ k, hazard k ≤ 1}
    (hexact : IsExactAnchoredSoloPeriodic reward w hazard h0 h1)
    (hpos : ∀ k, 0 < hazard k) (hlt : ∀ k, hazard k < 1) (phase : Fin m)
    (hne : w (finRotate m phase) ≠ w phase) :
    quittingSoloCollisionPenalty reward (w phase) (w (finRotate m phase)) ≤ 0 := by
  have hfloor := spectatorFloor_of_isExactAnchoredSoloPeriodic hexact phase hne
  have hsuccessor :=
    quittingAnchoredCyclicOnPathValue_scheduled_of_isExactAnchoredSoloPeriodic
      hexact hpos hlt (finRotate m phase)
  rw [hsuccessor] at hfloor
  unfold quittingSoloCollisionPenalty
  nlinarith [hfloor, hpos phase]

/-- The pair-row no-go read off the table: on a consecutive edge of an exact
schedule with interior hazards, the successor's joined row is at most its
row at the predecessor's solo exit. -/
theorem pairReward_le_soloReward_of_isExactAnchoredSoloPeriodic
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {w : Fin m → ι} {hazard : Fin m → ℝ}
    {h0 : ∀ k, 0 ≤ hazard k} {h1 : ∀ k, hazard k ≤ 1}
    (hexact : IsExactAnchoredSoloPeriodic reward w hazard h0 h1)
    (hpos : ∀ k, 0 < hazard k) (hlt : ∀ k, hazard k < 1) (phase : Fin m)
    (hne : w (finRotate m phase) ≠ w phase) :
    reward ⟨{w phase, w (finRotate m phase)},
          Finset.insert_nonempty (w phase) {w (finRotate m phase)}⟩
        (w (finRotate m phase)) ≤
      reward (quittingSingletonTerminal (w phase)) (w (finRotate m phase)) := by
  have h := quittingSoloCollisionPenalty_nonpos_of_isExactAnchoredSoloPeriodic
    hexact hpos hlt phase hne
  unfold quittingSoloCollisionPenalty at h
  linarith

/-! ## The branch-free product bound at accuracy `ε` -/

/-- **The branch-free product bound.**  At accuracy `ε` the product of two
adjacent hazards with the successor's collision penalty against its
predecessor is at most `ε`.  Neither hazard is assumed positive and no case
distinction is made between them: the successor's own hazard clears the
denominator that the approximate anchor would otherwise introduce. -/
theorem hazard_mul_hazard_mul_soloCollisionPenalty_le_of_isεExactAnchoredSoloPeriodic
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι} {ε : ℝ}
    {w : Fin m → ι} {hazard : Fin m → ℝ}
    {h0 : ∀ k, 0 ≤ hazard k} {h1 : ∀ k, hazard k ≤ 1}
    (hexact : IsεExactAnchoredSoloPeriodic reward ε w hazard h0 h1) (hε : 0 ≤ ε)
    (phase : Fin m) (hne : w (finRotate m phase) ≠ w phase) :
    hazard phase * hazard (finRotate m phase) *
        quittingSoloCollisionPenalty reward (w phase) (w (finRotate m phase)) ≤ ε := by
  have hfloor := spectatorFloor_of_isεExactAnchoredSoloPeriodic hexact phase hne
  have hsurplus :=
    hazard_mul_continuationSurplus_scheduled_le_of_isεExactAnchoredSoloPeriodic
      hexact (finRotate m phase)
  unfold quittingContinuationSurplus at hsurplus
  unfold quittingSoloCollisionPenalty
  have hp0 := h0 phase
  have hp1 := h1 phase
  have hq0 := h0 (finRotate m phase)
  have hq1 := h1 (finRotate m phase)
  have hscaled := mul_le_mul_of_nonneg_left hfloor hq0
  have hcarry := mul_le_mul_of_nonneg_left hsurplus (by linarith : (0 : ℝ) ≤ 1 - hazard phase)
  nlinarith [hscaled, hcarry, mul_nonneg hp0 (mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - hazard
    (finRotate m phase)) hε)]

/-! ## Reading the bound against the counterexample leaf data -/

/-- **A preemption edge forces its collision row a full margin below solo.**
On a consecutive edge of an exact schedule that is also a strict
solo-preemption edge, the successor's joined row lies at least `gap` below its
own solo exit. -/
theorem QuittingSoloPreempts.pairReward_add_gap_le_of_isExactAnchoredSoloPeriodic
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι} {gap : ℝ}
    {w : Fin m → ι} {hazard : Fin m → ℝ}
    {h0 : ∀ k, 0 ≤ hazard k} {h1 : ∀ k, hazard k ≤ 1}
    (hexact : IsExactAnchoredSoloPeriodic reward w hazard h0 h1)
    (hpos : ∀ k, 0 < hazard k) (hlt : ∀ k, hazard k < 1) (phase : Fin m)
    (hedge : QuittingSoloPreempts reward gap (w phase) (w (finRotate m phase))) :
    reward ⟨{w phase, w (finRotate m phase)},
            Finset.insert_nonempty (w phase) {w (finRotate m phase)}⟩
          (w (finRotate m phase)) + gap ≤
      reward (quittingSingletonTerminal (w (finRotate m phase)))
        (w (finRotate m phase)) := by
  have hrow := pairReward_le_soloReward_of_isExactAnchoredSoloPeriodic hexact hpos
    hlt phase hedge.1
  have hpreempt := hedge.2
  simp only [quittingSoloReward, quittingSingletonTerminal] at hrow hpreempt ⊢
  linarith

/-- **No exact schedule places an immediate singleton collision on a
consecutive edge.**  If the owner and the collider of a
`QuittingImmediateSingletonCollision` with a positive margin are scheduled at
consecutive phases in that order, no interior hazard vector makes the schedule
exact. -/
theorem not_isExactAnchoredSoloPeriodic_of_immediateSingletonCollision_on_edge
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι} {margin : ℝ}
    {w : Fin m → ι} {hazard : Fin m → ℝ}
    {h0 : ∀ k, 0 ≤ hazard k} {h1 : ∀ k, hazard k ≤ 1}
    (certificate : QuittingImmediateSingletonCollision reward margin)
    (hmargin : 0 < margin) (hpos : ∀ k, 0 < hazard k) (hlt : ∀ k, hazard k < 1)
    (phase : Fin m) (howner : w phase = certificate.owner)
    (hcollider : w (finRotate m phase) = certificate.collider) :
    ¬ IsExactAnchoredSoloPeriodic reward w hazard h0 h1 := by
  intro hexact
  have hne : w (finRotate m phase) ≠ w phase := by
    rw [howner, hcollider]
    exact certificate.collider_ne_owner
  have hrow := pairReward_le_soloReward_of_isExactAnchoredSoloPeriodic hexact hpos
    hlt phase hne
  rw [howner, hcollider] at hrow
  have hgain := certificate.collider_gain_floor
  simp only [quittingSoloReward, quittingSingletonCollisionReward,
    quittingSingletonTerminal] at hrow hgain
  linarith

/-- **The quantitative edge restriction.**  If the owner and the collider of a
`QuittingImmediateSingletonCollision` are scheduled at consecutive phases in
that order, the product of the two adjacent hazards with the collision margin
is capped by the accuracy.  At `ε = 0` this is
`not_isExactAnchoredSoloPeriodic_of_immediateSingletonCollision_on_edge` again,
and along a family with vanishing accuracy it forces the product of the two
hazards to vanish whenever the margin is positive. -/
theorem hazard_mul_hazard_mul_margin_le_of_isεExactAnchoredSoloPeriodic
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι} {ε margin : ℝ}
    {w : Fin m → ι} {hazard : Fin m → ℝ}
    {h0 : ∀ k, 0 ≤ hazard k} {h1 : ∀ k, hazard k ≤ 1}
    (certificate : QuittingImmediateSingletonCollision reward margin)
    (hexact : IsεExactAnchoredSoloPeriodic reward ε w hazard h0 h1) (hε : 0 ≤ ε)
    (phase : Fin m) (howner : w phase = certificate.owner)
    (hcollider : w (finRotate m phase) = certificate.collider) :
    hazard phase * hazard (finRotate m phase) * margin ≤ ε := by
  have hne : w (finRotate m phase) ≠ w phase := by
    rw [howner, hcollider]
    exact certificate.collider_ne_owner
  have hbound :=
    hazard_mul_hazard_mul_soloCollisionPenalty_le_of_isεExactAnchoredSoloPeriodic
      hexact hε phase hne
  have hgain := certificate.collider_gain_floor
  have hpenalty : margin ≤
      quittingSoloCollisionPenalty reward (w phase) (w (finRotate m phase)) := by
    rw [howner, hcollider]
    simp only [quittingSoloCollisionPenalty, quittingSoloReward,
      quittingSingletonCollisionReward, quittingSingletonTerminal] at hgain ⊢
    linarith
  have hproduct : 0 ≤ hazard phase * hazard (finRotate m phase) :=
    mul_nonneg (h0 phase) (h0 (finRotate m phase))
  nlinarith [hbound, hpenalty, hproduct]

end GameTheory
