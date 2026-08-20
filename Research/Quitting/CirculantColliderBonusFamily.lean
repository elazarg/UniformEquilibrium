/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.CubicAnchorRoot
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegime.Circulant.ColliderCompletion
import UniformEquilibrium.Quitting.Classification.Circulant.ColliderCompletion

/-!
# Raising the collider: a one-parameter family of five-player circulant tables

The collider completion of `Research/Quitting/CirculantColliderCompletion.lean`
pays a player its solo self value when it quits together with exactly its
predecessor, so its join margin at distance four is zero.  That is the exact
boundary of the step-four constant-step cycle, whose floor at the shallowest
elapsed phase asks the join margin at the step itself to be nonpositive.

`colliderBonusReward` adds a real `bonus` to the collider row and nothing else.
Its join margin vector is `bonus` at distance four and `low - s` elsewhere, so
`bonus = 0` is the collider completion and `bonus > 0` is the smallest
perturbation that breaks the step-four floor.

`candidateReward` is the resulting family at the margin vector
`candidateMargin = (-1/2, 2, 1, -2)`, solo self value one and joint value
`-2`.  Its margins are in the neighbour pocket of
`Research/Quitting/CirculantTrichotomyClosure.lean`, with margin sum `1/2`.

Two exact statements delimit the family from below.

* For `bonus ≤ 0` the step-four cycle closes it, through the neighbour-pocket
  producer at the cap `m 1`: the two caps read `-3 ≤ -1/2`, and the only
  demand the bonus touches is `J 4 ≤ 0`.
* For `bonus > 0` *no* constant-step cyclic profile closes it at all, at any
  step and any anchor root.  Step four loses its shallowest floor and step one
  its deepest, both to the raised join margin; steps two and three have no
  anchor root in the unit interval, their anchors being bounded below by `1/2`
  and by `19/27 - 1/2` respectively.  Both bounds come from the
  square-plus-affine certificate of `MathUE/CubicAnchorRoot.lean`.

So `bonus ≤ 0` is exactly the region the constant-step producer closes on this
margin vector.  A second producer, the stationary all-quitter block of
`Research/Quitting/CirculantColliderBonusStationary.lean`, closes the family
from above; `Research/Quitting/CirculantColliderBonusWindow.lean` identifies
exactly which bonuses that one reaches.

## Main definitions

* `colliderBonusReward`, `colliderBonusJoin` — the raised-collider completion
  and its join margin vector
* `candidateMargin`, `candidateReward` — the one-parameter family

## Main results

* `isCirculantPairTable_colliderBonusReward` — the singleton and pair rows
* `isEmpty_counterexampleRegime_candidateReward_of_nonpos` — the family is
  closed for `bonus ≤ 0`
* `stepAnchor_candidateMargin_two_pos`, `stepAnchor_candidateMargin_three_pos`
  — the two root-free anchors
* `not_constantStepFloors_candidateMargin_of_pos` — for `bonus > 0` no step
  and no anchor root satisfy the constant-step obligations
-/

noncomputable section

namespace GameTheory
namespace CirculantColliderBonus

open CirculantConstantStepCycle CirculantTrichotomyClosure
open CirculantColliderCompletion

/-! ## The raised collider -/

variable (s low bonus : ℝ) (m : ZMod 5 → ℝ)

/-- The collider completion with the collider row raised by `bonus`: a player
quitting together with exactly its predecessor is paid `s + bonus`, and every
other row is the collider completion's. -/
def colliderBonusReward : {S : Finset (ZMod 5) // S.Nonempty} → Payoff (ZMod 5) :=
  fun S who =>
    colliderReward s low m S who +
      if S.1 = ({who - 1, who} : Finset (ZMod 5)) then bonus else 0

/-- The join margin vector of the raised-collider completion. -/
def colliderBonusJoin : ZMod 5 → ℝ :=
  fun d => if d = 4 then bonus else low - s

@[simp] theorem colliderBonusJoin_four :
    colliderBonusJoin s low bonus 4 = bonus := by
  rw [colliderBonusJoin, if_pos rfl]

theorem colliderBonusJoin_of_ne {d : ZMod 5} (hd : d ≠ 4) :
    colliderBonusJoin s low bonus d = low - s := by
  rw [colliderBonusJoin, if_neg hd]

/-- The raised-collider completion is the collider completion at zero bonus. -/
theorem colliderBonusReward_zero :
    colliderBonusReward s low 0 m = colliderReward s low m := by
  funext S who
  rw [colliderBonusReward]
  by_cases h : S.1 = ({who - 1, who} : Finset (ZMod 5)) <;> simp [h]

/-- A singleton is never a collider pair. -/
theorem singletonTerminal_ne_collider (owner who : ZMod 5) :
    (quittingSingletonTerminal owner).1 ≠ ({who - 1, who} : Finset (ZMod 5)) := by
  revert owner who
  decide

/-- The singleton rows are unchanged. -/
@[simp] theorem colliderBonusReward_singleton (owner who : ZMod 5) :
    colliderBonusReward s low bonus m (quittingSingletonTerminal owner) who =
      s + m (owner - who) := by
  rw [colliderBonusReward, colliderReward_singleton,
    if_neg (singletonTerminal_ne_collider owner who), add_zero]

/-- The two-element rows are the circulant rows of the raised join margin
vector. -/
theorem colliderBonusReward_pair {owner who : ZMod 5} (hne : owner ≠ who) :
    colliderBonusReward s low bonus m
        ⟨{owner, who}, Finset.insert_nonempty owner {who}⟩ who =
      s + colliderBonusJoin s low bonus (owner - who) := by
  have hkey : (({owner, who} : Finset (ZMod 5)) = {who - 1, who}) ↔
      owner - who = 4 := by
    revert hne
    revert owner who
    decide
  rw [colliderBonusReward, colliderReward_pair s low m hne, colliderBonusJoin]
  by_cases h : owner - who = 4
  · rw [if_pos (hkey.mpr h), if_pos h, h, colliderJoin_four]
    ring
  · rw [if_neg (fun hcontra ↦ h (hkey.mp hcontra)), if_neg h,
      colliderJoin_of_ne s low h]
    ring

/-- The raised-collider completion has the rotation-symmetric singleton and
pair rows required by the constant-step producer. -/
theorem isCirculantPairTable_colliderBonusReward (hm0 : m 0 = 0) :
    IsCirculantPairTable (colliderBonusReward s low bonus m) s m
      (colliderBonusJoin s low bonus) :=
  ⟨hm0, colliderBonusReward_singleton s low bonus m,
    fun _ _ hne ↦ colliderBonusReward_pair s low bonus m hne⟩

/-! ## The candidate margin vector -/

/-- The margin vector `(-1/2, 2, 1, -2)` of the family, of margin sum `1/2`
and in the neighbour pocket. -/
def candidateMargin : ZMod 5 → ℝ :=
  fun d =>
    if d = 1 then -1 / 2 else if d = 2 then 2 else if d = 3 then 1
    else if d = 4 then -2 else 0

@[simp] theorem candidateMargin_zero : candidateMargin 0 = 0 := by
  rw [candidateMargin, if_neg (by decide), if_neg (by decide), if_neg (by decide),
    if_neg (by decide)]

@[simp] theorem candidateMargin_one : candidateMargin 1 = -1 / 2 := by
  rw [candidateMargin, if_pos rfl]

@[simp] theorem candidateMargin_two : candidateMargin 2 = 2 := by
  rw [candidateMargin, if_neg (by decide), if_pos rfl]

@[simp] theorem candidateMargin_three : candidateMargin 3 = 1 := by
  rw [candidateMargin, if_neg (by decide), if_neg (by decide), if_pos rfl]

@[simp] theorem candidateMargin_four : candidateMargin 4 = -2 := by
  rw [candidateMargin, if_neg (by decide), if_neg (by decide), if_neg (by decide),
    if_pos rfl]

theorem sum_candidateMargin : (∑ e : ZMod 5, candidateMargin e) = 1 / 2 := by
  rw [show (∑ e : ZMod 5, candidateMargin e) =
    candidateMargin 0 + candidateMargin 1 + candidateMargin 2 + candidateMargin 3 +
      candidateMargin 4 from Fin.sum_univ_five (fun e : ZMod 5 => candidateMargin e)]
  norm_num

/-- The one-parameter family: the raised-collider completion of
`candidateMargin` at solo self value one and joint value `-2`. -/
def candidateReward (bonus : ℝ) :
    {S : Finset (ZMod 5) // S.Nonempty} → Payoff (ZMod 5) :=
  colliderBonusReward 1 (-2) bonus candidateMargin

theorem isCirculantPairTable_candidateReward (bonus : ℝ) :
    IsCirculantPairTable (candidateReward bonus) 1 candidateMargin
      (colliderBonusJoin 1 (-2) bonus) :=
  isCirculantPairTable_colliderBonusReward 1 (-2) bonus candidateMargin
    candidateMargin_zero

/-! ## The closed region below -/

/-- **The family is closed for a nonpositive bonus.**  At `bonus ≤ 0` every
join margin is nonpositive, the two caps of the step-four neighbour-pocket
producer read `-3 ≤ -1/2`, and the cycle fires. -/
theorem exists_uniformEquilibriumPayoff_candidateReward_of_nonpos
    {bonus : ℝ} (hbonus : bonus ≤ 0) :
    ∃ payoff : Payoff (ZMod 5),
      (quittingGame (candidateReward bonus)).IsUniformEquilibriumPayoff none payoff := by
  have hone : colliderBonusJoin 1 (-2) bonus 1 = -3 := by
    rw [colliderBonusJoin_of_ne 1 (-2) bonus (by decide)]
    norm_num
  have htwo : colliderBonusJoin 1 (-2) bonus 2 = -3 := by
    rw [colliderBonusJoin_of_ne 1 (-2) bonus (by decide)]
    norm_num
  have hthree : colliderBonusJoin 1 (-2) bonus 3 = -3 := by
    rw [colliderBonusJoin_of_ne 1 (-2) bonus (by decide)]
    norm_num
  refine exists_uniformEquilibriumPayoff_of_neighbourPocket
    (isCirculantPairTable_candidateReward bonus) zero_le_one
    (by norm_num) (by norm_num) (by norm_num)
    (by rw [sum_candidateMargin]; norm_num)
    (by rw [hthree]; norm_num)
    (by rw [colliderBonusJoin_four]; exact hbonus)
    (by rw [hone]; norm_num) (by rw [htwo]; norm_num)

/-- The closed region below, as emptiness of the counterexample regime. -/
theorem isEmpty_counterexampleRegime_candidateReward_of_nonpos
    {bonus : ℝ} (hbonus : bonus ≤ 0) :
    IsEmpty (QuittingCounterexampleRegime (candidateReward bonus)) :=
  ⟨fun regime => regime.not_exists_uniformEquilibriumPayoff
    (exists_uniformEquilibriumPayoff_candidateReward_of_nonpos hbonus)⟩

/-! ## Sharpness: the two root-free anchors -/

/-- The step-two anchor of the candidate margins, read as an anchor cubic. -/
theorem stepAnchor_candidateMargin_two (q : ℝ) :
    stepAnchor candidateMargin 2 q = Math.cubicAnchor 2 (-2) (-1 / 2) 1 q := by
  rw [stepAnchor, show (2 : ZMod 5) * 2 = 4 from by decide,
    show (3 : ZMod 5) * 2 = 1 from by decide,
    show (4 : ZMod 5) * 2 = 3 from by decide,
    candidateMargin_two, candidateMargin_four, candidateMargin_one,
    candidateMargin_three]

/-- The step-three anchor of the candidate margins, read as an anchor cubic. -/
theorem stepAnchor_candidateMargin_three (q : ℝ) :
    stepAnchor candidateMargin 3 q = Math.cubicAnchor 1 (-1 / 2) (-2) 2 q := by
  rw [stepAnchor, show (2 : ZMod 5) * 3 = 1 from by decide,
    show (3 : ZMod 5) * 3 = 4 from by decide,
    show (4 : ZMod 5) * 3 = 2 from by decide,
    candidateMargin_three, candidateMargin_one, candidateMargin_four,
    candidateMargin_two]

/-- **The step-two anchor is root free.**  On the unit interval
`2 - 2q - q²/2 + q³` equals `(q + 3/2)(q - 1)² + 1/2`, so the
square-plus-affine certificate of `MathUE/CubicAnchorRoot.lean` bounds it below
by `1/2`. -/
theorem stepAnchor_candidateMargin_two_pos {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    1 / 2 ≤ stepAnchor candidateMargin 2 q := by
  rw [stepAnchor_candidateMargin_two]
  have hbound := Math.cubicAnchor_ge_of_square_add_affine
    (a := 2) (b := -2) (c := -1 / 2) (d := 1) (k := 1) (r := 3 / 2) (t := 1)
    (lin₀ := 1 / 2) (lin₁ := 0) (fun β ↦ by rw [Math.cubicAnchor]; ring)
    (by norm_num) (by norm_num) hq0 hq1
  refine le_trans (le_of_eq ?_) hbound
  norm_num

/-- **The step-three anchor is root free.**  On the unit interval
`1 - q/2 - 2q² + 2q³` equals `2 (q + 1/3)(q - 2/3)² + 19/27 - q/2`, so the same
certificate bounds it below by the smaller endpoint value of the affine
remainder. -/
theorem stepAnchor_candidateMargin_three_pos {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    19 / 27 - 1 / 2 ≤ stepAnchor candidateMargin 3 q := by
  rw [stepAnchor_candidateMargin_three]
  have hbound := Math.cubicAnchor_ge_of_square_add_affine
    (a := 1) (b := -1 / 2) (c := -2) (d := 2) (k := 2) (r := 1 / 3) (t := 2 / 3)
    (lin₀ := 19 / 27) (lin₁ := -(1 / 2)) (fun β ↦ by rw [Math.cubicAnchor]; ring)
    (by norm_num) (by norm_num) hq0 hq1
  refine le_trans (le_of_eq ?_) hbound
  norm_num

/-! ## Sharpness: no constant-step cycle above -/

/-- **A positive bonus blocks every constant-step cycle.**  For `bonus > 0` no
step of the five-cycle and no anchor root in the unit interval satisfy the
five obligations of
`Research/Quitting/CirculantConstantStepCycle.lean`'s producer.

Step four loses the floor at its shallowest elapsed phase, which reads the
raised join margin against zero; step one loses the floor at its deepest
phase, which reads the same join margin against `m 4 = -2`; and steps two and
three have no anchor root at all. -/
theorem not_constantStepFloors_candidateMargin_of_pos
    {bonus : ℝ} (hbonus : 0 < bonus) {c : ZMod 5} (hc : c ≠ 0)
    {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    ¬ (stepAnchor candidateMargin c q = 0 ∧
        colliderBonusJoin 1 (-2) bonus c ≤ 0 ∧
        colliderBonusJoin 1 (-2) bonus (2 * c) ≤
          candidateMargin (2 * c) + q * candidateMargin (3 * c) +
            q ^ 2 * candidateMargin (4 * c) ∧
        colliderBonusJoin 1 (-2) bonus (3 * c) ≤
          candidateMargin (3 * c) + q * candidateMargin (4 * c) ∧
        colliderBonusJoin 1 (-2) bonus (4 * c) ≤ candidateMargin (4 * c)) := by
  rintro ⟨hroot, hfloor₁, -, -, hfloor₄⟩
  rcases zmod_five_cases c with h | h | h | h | h
  · exact hc h
  · rw [h, show (4 : ZMod 5) * 1 = 4 from by decide, colliderBonusJoin_four,
      candidateMargin_four] at hfloor₄
    linarith
  · have := stepAnchor_candidateMargin_two_pos hq0.le hq1.le
    rw [h] at hroot
    linarith
  · have := stepAnchor_candidateMargin_three_pos hq0.le hq1.le
    rw [h] at hroot
    linarith
  · rw [h, colliderBonusJoin_four] at hfloor₁
    linarith

end CirculantColliderBonus
end GameTheory
