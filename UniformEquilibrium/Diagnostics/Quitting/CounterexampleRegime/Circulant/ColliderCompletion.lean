/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegime.Circulant.ConstantStepCycle
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegime.Circulant.TrichotomyClosure
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegime.SoloExitPreferenceScreen
import UniformEquilibrium.Quitting.Classification.Circulant.ColliderCompletion

/-!
# The collider completion, against the counterexample regime

`UniformEquilibrium/Quitting/Classification/Circulant/ColliderCompletion.lean`
supplies the collider completion's rows, its join margins, the sure-exit
screen at an adjacent pair, the `R₀` certificate of the pocket branch, and the
solo-exit preference screen, all without reference to
`QuittingCounterexampleRegime`.  This module reads the family against the
regime: the firing-step and three-negative-margin branches, the pocket floors,
the neighbour pocket, the census up to the distant pocket, and the
solo-exit-preference exclusion, now unconditional because
`isEmpty_quittingCounterexampleRegime_of_cappedJointExit` no longer carries an
existence-law hypothesis — the Solan-Vieille law it once needed is proved in
`UniformEquilibrium/Quitting/Classification/Existence/PerfectSequenceExtraction.lean`.

## Main results

* `isEmpty_counterexampleRegime_colliderFiringStep` — a firing step closes a
  collider completion of positive margin sum
* `isEmpty_counterexampleRegime_colliderThreeNegative` — three negative margins
  are closed with no further hypothesis
* `isEmpty_counterexampleRegime_colliderPocket` — a pocket collider table
  satisfying the floor carries no counterexample regime
* `isEmpty_counterexampleRegime_colliderPocket_of_not_sureExit` — the same
  conclusion from failure of the sure-exit property at one adjacent pair
* `isEmpty_counterexampleRegime_colliderNeighbourFace` — a margin vector with
  `m 1 = 0` inside the equilibrium region and outside the `R₀` one
* `isEmpty_counterexampleRegime_colliderNeighbourPocket` — the neighbour pocket
  closes with no further hypothesis
* `isEmpty_counterexampleRegime_or_distantPocket` — the census: the distant
  pocket of positive margin sum is the whole residual
* `isEmpty_counterexampleRegime_colliderCompletion_closure` — the census read
  as a sufficient condition
* `isEmpty_counterexampleRegime_colliderUnitSolo` — the unconditional
  solo-exit-preference exclusion
-/

noncomputable section

namespace GameTheory
namespace CirculantColliderCompletion

open CirculantConstantStepCycle CirculantTrichotomyClosure QuittingLCPClassification
open QuittingSureSetOwnerRepair

variable {s low : ℝ} {m : ZMod 5 → ℝ}

/-! ## The firing-step branch -/


/-- **A firing step closes a collider completion.**  A five-player collider
table of positive margin sum, nonnegative solo self value and joint value no
larger than it carries no counterexample regime as soon as some step fires. -/
theorem isEmpty_counterexampleRegime_colliderFiringStep
    (hm0 : m 0 = 0) (hs : 0 ≤ s) (hls : low ≤ s) (hsum : 0 < ∑ e, m e)
    {c : ZMod 5} (hfire : IsFiringStep m c) :
    IsEmpty (QuittingCounterexampleRegime (colliderReward s low m)) :=
  isEmpty_counterexampleRegime_of_isFiringStep
    (isCirculantPairTable_colliderReward s low m hm0) hs hsum hfire
    fun k _ => colliderJoin_nonpos hls (k * c)

/-- **Three negative margins close a collider completion.**  A five-player
collider table of positive margin sum whose only nonnegative nonzero distance
is `g` carries no counterexample regime, the witness being the constant-step
cyclic profile of step `4 * g`.  No screen on the larger coalitions and no
regime hypothesis enters. -/
theorem isEmpty_counterexampleRegime_colliderThreeNegative
    (hm0 : m 0 = 0) (hs : 0 ≤ s) (hls : low ≤ s) (hsum : 0 < ∑ e, m e)
    {g : ZMod 5} (hgm : 0 ≤ m g)
    (hother : ∀ e : ZMod 5, e ≠ 0 → e ≠ g → m e < 0) :
    IsEmpty (QuittingCounterexampleRegime (colliderReward s low m)) :=
  isEmpty_counterexampleRegime_of_unique_nonneg
    (isCirculantPairTable_colliderReward s low m hm0) hs hsum hgm hother
    fun d _ => colliderJoin_nonpos hls d

/-! ## The pocket floors -/

/-- **The step-four floors of a pocket collider table.**  A five-player
collider table with `m 1 ≤ 0`, `m 4 < 0`, `0 ≤ m 2`, `0 ≤ m 3`, positive margin
sum, nonnegative solo self value, and `low - s ≤ m 1` carries no counterexample
regime: the step-four constant-step cyclic profile is an exact equilibrium at
an anchor root.

Only the step's own margin `m 4` has to be strictly negative, that being what
places the anchor root strictly inside the unit interval.  The neighbour margin
`m 1` enters only through the two middle floors, where a nonpositive `m 1` and
a survival factor below one give `q * m 1 ≥ m 1` and `q ^ 2 * m 1 ≥ m 1`, so
the region is closed along the face `m 1 = 0`. -/
theorem isEmpty_counterexampleRegime_colliderPocket
    (hm0 : m 0 = 0) (hs : 0 ≤ s)
    (hm1 : m 1 ≤ 0) (hm4 : m 4 < 0) (hm2 : 0 ≤ m 2) (hm3 : 0 ≤ m 3)
    (hsum : 0 < m 1 + m 2 + m 3 + m 4) (hfloor : low - s ≤ m 1) :
    IsEmpty (QuittingCounterexampleRegime (colliderReward s low m)) := by
  have hsum' : 0 < ∑ e, m e := by
    have hfive : (∑ e : ZMod 5, m e) = m 0 + m 1 + m 2 + m 3 + m 4 :=
      Fin.sum_univ_five (fun e : ZMod 5 => m e)
    rw [hfive, hm0]
    linarith
  obtain ⟨q, hq, hroot⟩ :=
    exists_stepAnchor_root m (c := 4) hm0 (by decide) hm4 hsum'
  have hq0 : 0 < q := hq.1
  have hq1 : q < 1 := hq.2
  have hq2 : q ^ 2 < 1 := by nlinarith
  refine isEmpty_counterexampleRegime_constantStep
    (c' := 1) (isCirculantPairTable_colliderReward s low m hm0) (by decide) hs
    hq0.le hq1 hroot ?_ ?_ ?_ ?_
  · rw [colliderJoin_four]
  · rw [show (2 : ZMod 5) * 4 = 3 from by decide,
      show (3 : ZMod 5) * 4 = 2 from by decide,
      show (4 : ZMod 5) * 4 = 1 from by decide,
      colliderJoin_of_ne s low (by decide)]
    nlinarith
  · rw [show (3 : ZMod 5) * 4 = 2 from by decide,
      show (4 : ZMod 5) * 4 = 1 from by decide,
      colliderJoin_of_ne s low (by decide)]
    nlinarith
  · rw [show (4 : ZMod 5) * 4 = 1 from by decide,
      colliderJoin_of_ne s low (by decide)]
    exact hfloor

/-- **The collider-completion pocket carries no counterexample regime.**  A
five-player collider table in the pocket whose adjacent pair at some player
fails the sure-exit property admits the step-four constant-step cyclic
equilibrium, so it has a uniform-equilibrium payoff. -/
theorem isEmpty_counterexampleRegime_colliderPocket_of_not_sureExit
    (hm0 : m 0 = 0) (hs : 0 ≤ s) (hlow : low ≤ 0)
    (hm1 : m 1 ≤ 0) (hm4 : m 4 < 0) (hm2 : 0 ≤ m 2) (hm3 : 0 ≤ m 3)
    (hsum : 0 < m 1 + m 2 + m 3 + m 4) (y : ZMod 5)
    (hno : ¬ IsQuittingSureExitSet (colliderReward s low m) {y, y + 1}) :
    IsEmpty (QuittingCounterexampleRegime (colliderReward s low m)) :=
  isEmpty_counterexampleRegime_colliderPocket hm0 hs hm1 hm4 hm2 hm3 hsum
    (lt_margin_one_of_not_isQuittingSureExitSet s low m hm4.le hlow y hno).le

/-- **The equilibrium region reaches the face `m 1 = 0`.**  The collider
completion of `neighbourFaceMargin` at any nonnegative solo self value and any
joint value no larger than it carries no counterexample regime, even though its
neighbour margin vanishes and the strict pocket sign condition of
`isR0Matrix_normalizedSoloMatrix_colliderPocket` therefore fails. -/
theorem isEmpty_counterexampleRegime_colliderNeighbourFace (hs : 0 ≤ s)
    (hls : low ≤ s) :
    IsEmpty (QuittingCounterexampleRegime
      (colliderReward s low neighbourFaceMargin)) :=
  isEmpty_counterexampleRegime_colliderPocket neighbourFaceMargin_zero hs
    (le_of_eq neighbourFaceMargin_one)
    (by rw [neighbourFaceMargin_four]; norm_num)
    (by rw [neighbourFaceMargin_two]; norm_num)
    (by rw [neighbourFaceMargin_three]; norm_num)
    (by rw [neighbourFaceMargin_one, neighbourFaceMargin_two,
      neighbourFaceMargin_three, neighbourFaceMargin_four]; norm_num)
    (by rw [neighbourFaceMargin_one]; linarith)

/-! ## The census -/

/-- **The neighbour pocket carries no counterexample regime.**  Either some
adjacent pair of the table is a sure exit set, and then its own row is a
uniform-equilibrium payoff outright, or no adjacent pair is, and then the
sure-exit failure supplies the step-four floor and the constant-step cyclic
profile fires.  Nothing beyond the pocket signs and a positive margin sum is
needed, and the neighbour margin `m 1` may vanish. -/
theorem isEmpty_counterexampleRegime_colliderNeighbourPocket
    (hm0 : m 0 = 0) (hs : 0 ≤ s) (hlow : low ≤ 0)
    (hm1 : m 1 ≤ 0) (hm4 : m 4 < 0) (hm2 : 0 ≤ m 2) (hm3 : 0 ≤ m 3)
    (hsum : 0 < m 1 + m 2 + m 3 + m 4) :
    IsEmpty (QuittingCounterexampleRegime (colliderReward s low m)) := by
  by_cases hsure : IsQuittingSureExitSet (colliderReward s low m) {0, 0 + 1}
  · exact ⟨fun regime => regime.not_exists_uniformEquilibriumPayoff
      ⟨_, isUniformEquilibriumPayoff_setReward_of_isQuittingSureExitSet _ hsure⟩⟩
  · exact isEmpty_counterexampleRegime_colliderPocket_of_not_sureExit hm0 hs hlow
      hm1 hm4 hm2 hm3 hsum 0 hsure

/-- **The census of the collider completion.**  A five-player collider table
with nonnegative solo self value and nonpositive joint value either carries no
counterexample regime, or has positive margin sum with its negative margins
exactly at the two distant distances.  That distant pocket is the whole
residual of the family. -/
theorem isEmpty_counterexampleRegime_or_distantPocket
    (hm0 : m 0 = 0) (hs : 0 ≤ s) (hlow : low ≤ 0) :
    IsEmpty (QuittingCounterexampleRegime (colliderReward s low m)) ∨
      (0 < m 1 + m 2 + m 3 + m 4 ∧ m 2 < 0 ∧ m 3 < 0 ∧ 0 ≤ m 4 ∧ 0 ≤ m 1) := by
  have hfive : (∑ e : ZMod 5, m e) = m 0 + m 1 + m 2 + m 3 + m 4 :=
    Fin.sum_univ_five (fun e : ZMod 5 => m e)
  rcases isEmpty_counterexampleRegime_or_isComplementaryPocketMargin
      (isCirculantPairTable_colliderReward s low m hm0) hs
      (fun d _ => colliderJoin_nonpos (hlow.trans hs) d) with
    hempty | ⟨hsum, hpocket⟩
  · exact Or.inl hempty
  · rw [hfive, hm0] at hsum
    rcases neighbour_or_distant_of_isComplementaryPocketMargin hpocket with
      ⟨hm1, hm4, hm2, hm3⟩ | ⟨hm2, hm3, hm4, hm1⟩
    · exact Or.inl (isEmpty_counterexampleRegime_colliderNeighbourPocket hm0 hs
        hlow hm1.le hm4 hm2 hm3 (by linarith))
    · exact Or.inr ⟨by linarith, hm2, hm3, hm4, hm1⟩

/-- **The settled branches of the collider completion.**  A five-player
collider table with nonnegative solo self value and nonpositive joint value
carries no counterexample regime as soon as its margin sum is nonpositive or
one of the two distant margins is nonnegative. -/
theorem isEmpty_counterexampleRegime_colliderCompletion_closure
    (hm0 : m 0 = 0) (hs : 0 ≤ s) (hlow : low ≤ 0)
    (hcase : m 1 + m 2 + m 3 + m 4 ≤ 0 ∨ 0 ≤ m 2 ∨ 0 ≤ m 3) :
    IsEmpty (QuittingCounterexampleRegime (colliderReward s low m)) := by
  rcases isEmpty_counterexampleRegime_or_distantPocket hm0 hs hlow with
    hempty | ⟨hsum, hm2, hm3, -, -⟩
  · exact hempty
  · rcases hcase with h | h | h <;> linarith

/-! ## The solo-exit preference screen

The collider completion satisfies the two assumptions of
`isEmpty_quittingCounterexampleRegime_of_cappedJointExit` as soon as `s = 1`
and `low ≤ 1`: its singleton row pays `s` on the diagonal, so it has unit solo
exit, and it pays no member of a joint exit more than `s`, so its joint exit is
capped.  So the collider completion has no counterexample regime whatever its
margin vector, with no margin-sum, firing-step, or sure-exit hypothesis at
all. -/

/-- **Every unit-solo, capped-joint collider completion is in no
counterexample regime.** -/
theorem isEmpty_counterexampleRegime_colliderUnitSolo
    (hm0 : m 0 = 0) (hs : s = 1) (hlow : low ≤ 1) :
    IsEmpty (QuittingCounterexampleRegime (colliderReward s low m)) :=
  isEmpty_quittingCounterexampleRegime_of_cappedJointExit
    (colliderReward_unitSoloExit hm0 hs)
    (colliderReward_cappedJointExit hm0 hs.le hlow)

end CirculantColliderCompletion
end GameTheory
