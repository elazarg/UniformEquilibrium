/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.LinearProgramming.CirculantPocketR0
import UniformEquilibrium.Quitting.Classification.Circulant.TrichotomyClosure
import UniformEquilibrium.Quitting.Classification.SoloExitPreference
import UniformEquilibrium.Quitting.Paths.SureExitSet

/-!
# The collider completion of a five-player circulant quitting table

Fix a solo self value `s`, a joint value `low`, and a margin vector
`m : ZMod 5 → ℝ` with `m 0 = 0`.  The *collider completion* `colliderReward`
is the five-player quitting table

* `r who {owner} = s + m (owner - who)` — the circulant singleton rows;
* `r who S = 0` when `who ∉ S` and `S` has at least two members;
* `r who S = s` when `S = {who - 1, who}` — the *collider* row: a player is
  paid its solo self value when it quits together with exactly its
  predecessor;
* `r who S = low` for every other membership in a coalition of size at least
  two.

So the adjacent pair `{i, i + 1}` pays its owner `i` the value `low` and its
collider `i + 1` the value `s`, while every other joint exit pays its members
`low`.  The join margins of this completion are `0` at distance four and
`low - s` at every other nonzero distance.

The main results run the constant-step producer of
`UniformEquilibrium/Quitting/Classification/Circulant/ConstantStepCycle.lean`.
All join margins of the completion are nonpositive as soon as `low ≤ s`, which
is exactly the input the firing-step branch of
`UniformEquilibrium/Quitting/Classification/Circulant/TrichotomyClosure.lean`
consumes, so every margin vector of positive sum whose negative margins are not
one complementary pair is closed outright.  In the *neighbour pocket* —
`m 1 ≤ 0`, `m 4 < 0`, `0 ≤ m 2`, `0 ≤ m 3`, positive margin sum — no step
fires, and the step-four floors of the producer reduce instead to the single
inequality `low - s ≤ m 1`, which the failure of the sure-exit property at an
adjacent pair supplies.  Should no adjacent pair fail it, the pair's own row is
a uniform-equilibrium payoff, so that pocket closes either way.

Only the margin of the step itself has to be strictly negative there, so the
equilibrium region includes the face `m 1 = 0`, on which the `R₀` certificate
of `MathUE/LinearProgramming/CirculantPocketR0.lean` is unavailable.

What remains of the family is therefore the distant pocket `m 2 < 0`,
`m 3 < 0`, `0 ≤ m 1`, `0 ≤ m 4` of positive margin sum, and nothing else.  The
census against `QuittingCounterexampleRegime` is read off in
`UniformEquilibrium/Diagnostics/Quitting/CounterexampleRegime/Circulant/ColliderCompletion.lean`.

## Main definitions

* `colliderReward` — the completed table
* `colliderJoin` — its join margin vector
* `neighbourFaceMargin` — a margin vector with `m 1 = 0`, inside the
  equilibrium region and outside the `R₀` one

## Main results

* `isCirculantPairTable_colliderReward` — the singleton and pair rows
* `colliderJoin_nonpos` — every join margin is nonpositive when `low ≤ s`
* `isQuittingSureExitSet_adjacent_of_le` — an adjacent pair is a sure exit set
  as soon as `m 1 ≤ low - s`, `m 4 ≤ 0` and `low ≤ 0`
* `isR0Matrix_normalizedSoloMatrix_colliderPocket` — the pocket branch is `R₀`
* `colliderReward_unitSoloExit` and `colliderReward_cappedJointExit` — the
  solo-exit preference screen
-/

noncomputable section

namespace GameTheory
namespace CirculantColliderCompletion

open CirculantConstantStepCycle CirculantTrichotomyClosure QuittingLCPClassification
open QuittingSureSetOwnerRepair

/-! ## Adjacent pairs of the five-cycle -/

theorem card_adjacent (y : ZMod 5) : ({y, y + 1} : Finset (ZMod 5)).card = 2 := by
  revert y
  decide

theorem erase_adjacent_left (y : ZMod 5) :
    ({y, y + 1} : Finset (ZMod 5)).erase y = {y + 1} := by
  revert y
  decide

theorem erase_adjacent_right (y : ZMod 5) :
    ({y, y + 1} : Finset (ZMod 5)).erase (y + 1) = {y} := by
  revert y
  decide

theorem adjacent_ne_collider_left (y : ZMod 5) :
    ({y, y + 1} : Finset (ZMod 5)) ≠ {y - 1, y} := by
  revert y
  decide

theorem adjacent_eq_collider_right (y : ZMod 5) :
    ({y, y + 1} : Finset (ZMod 5)) = {y + 1 - 1, y + 1} := by
  revert y
  decide

theorem sub_succ_self (y : ZMod 5) : y - (y + 1) = 4 := by
  revert y
  decide

theorem card_insert_adjacent {y j : ZMod 5}
    (hj : j ∉ ({y, y + 1} : Finset (ZMod 5))) :
    (insert j ({y, y + 1} : Finset (ZMod 5))).card = 3 := by
  revert hj
  revert j
  revert y
  decide

theorem insert_adjacent_ne_collider {y j : ZMod 5}
    (hj : j ∉ ({y, y + 1} : Finset (ZMod 5))) :
    insert j ({y, y + 1} : Finset (ZMod 5)) ≠ {j - 1, j} := by
  revert hj
  revert j
  revert y
  decide

/-! ## The table -/

/-- The collider completion of the circulant singleton rows of `m`: outsiders
of a joint exit are paid zero, a player quitting together with exactly its
predecessor is paid its solo self value, and every other member of a joint
exit is paid `low`. -/
def colliderReward (s low : ℝ) (m : ZMod 5 → ℝ) :
    {S : Finset (ZMod 5) // S.Nonempty} → Payoff (ZMod 5) :=
  fun S who =>
    if S.1.card = 1 then s + ∑ owner ∈ S.1, m (owner - who)
    else if who ∉ S.1 then 0
    else if S.1 = ({who - 1, who} : Finset (ZMod 5)) then s
    else low

/-- The join margin vector of the collider completion: a player joining the
quitter one step ahead of it is the collider and keeps its solo self value, and
every other joiner drops to `low`. -/
def colliderJoin (s low : ℝ) : ZMod 5 → ℝ :=
  fun d => if d = 4 then 0 else low - s

@[simp] theorem colliderJoin_four (s low : ℝ) : colliderJoin s low 4 = 0 := by
  rw [colliderJoin, if_pos rfl]

theorem colliderJoin_of_ne (s low : ℝ) {d : ZMod 5} (hd : d ≠ 4) :
    colliderJoin s low d = low - s := by
  rw [colliderJoin, if_neg hd]

variable (s low : ℝ) (m : ZMod 5 → ℝ)

/-- The singleton rows are the circulant rows of `m`. -/
@[simp] theorem colliderReward_singleton (owner who : ZMod 5) :
    colliderReward s low m (quittingSingletonTerminal owner) who =
      s + m (owner - who) := by
  rw [colliderReward, if_pos (by simp [quittingSingletonTerminal])]
  simp [quittingSingletonTerminal]

/-- An outsider of a joint exit is paid zero. -/
theorem colliderReward_of_notMem (S : {S : Finset (ZMod 5) // S.Nonempty})
    (hcard : S.1.card ≠ 1) (who : ZMod 5) (hwho : who ∉ S.1) :
    colliderReward s low m S who = 0 := by
  rw [colliderReward, if_neg hcard, if_pos hwho]

/-- A member of a joint exit other than its own collider pair is paid
`low`. -/
theorem colliderReward_of_mem (S : {S : Finset (ZMod 5) // S.Nonempty})
    (hcard : S.1.card ≠ 1) (who : ZMod 5) (hwho : who ∈ S.1)
    (hcollider : S.1 ≠ ({who - 1, who} : Finset (ZMod 5))) :
    colliderReward s low m S who = low := by
  rw [colliderReward, if_neg hcard, if_neg (by simpa using hwho), if_neg hcollider]

/-- The collider row: a player quitting together with exactly its predecessor
keeps its solo self value. -/
theorem colliderReward_collider (who : ZMod 5) :
    colliderReward s low m
        ⟨{who - 1, who}, Finset.insert_nonempty (who - 1) {who}⟩ who = s := by
  have hcard : ¬ (({who - 1, who} : Finset (ZMod 5)).card = 1) := by
    revert who
    decide
  rw [colliderReward, if_neg hcard, if_neg (by simp), if_pos rfl]

/-- The two-element rows are the circulant rows of the join margin vector. -/
theorem colliderReward_pair {owner who : ZMod 5} (hne : owner ≠ who) :
    colliderReward s low m
        ⟨{owner, who}, Finset.insert_nonempty owner {who}⟩ who =
      s + colliderJoin s low (owner - who) := by
  have hcard : ¬ (({owner, who} : Finset (ZMod 5)).card = 1) := by
    revert hne
    revert owner who
    decide
  have hkey : (({owner, who} : Finset (ZMod 5)) = {who - 1, who}) ↔
      owner - who = 4 := by
    revert hne
    revert owner who
    decide
  rw [colliderReward, if_neg hcard, if_neg (by simp)]
  by_cases hcollider : owner - who = 4
  · rw [if_pos (hkey.mpr hcollider), hcollider, colliderJoin_four, add_zero]
  · rw [if_neg (fun hcontra ↦ hcollider (hkey.mp hcontra)),
      colliderJoin_of_ne s low hcollider]
    ring

/-- The collider completion has the rotation-symmetric singleton and pair rows
required by the constant-step producer. -/
theorem isCirculantPairTable_colliderReward (hm0 : m 0 = 0) :
    IsCirculantPairTable (colliderReward s low m) s m (colliderJoin s low) :=
  ⟨hm0, colliderReward_singleton s low m,
    fun _ _ hne ↦ colliderReward_pair s low m hne⟩

/-! ## The rows read through the set-reward convention -/

theorem quittingSetReward_singleton (x who : ZMod 5) :
    quittingSetReward (colliderReward s low m) {x} who = s + m (x - who) := by
  rw [quittingSetReward_of_nonempty _ (Finset.singleton_nonempty x)]
  exact colliderReward_singleton s low m x who

theorem quittingSetReward_adjacent_owner (y : ZMod 5) :
    quittingSetReward (colliderReward s low m) {y, y + 1} y = low := by
  rw [quittingSetReward_of_nonempty _ (Finset.insert_nonempty y {y + 1})]
  refine colliderReward_of_mem s low m _ ?_ y (by simp) (adjacent_ne_collider_left y)
  rw [card_adjacent]
  decide

theorem quittingSetReward_adjacent_collider (y : ZMod 5) :
    quittingSetReward (colliderReward s low m) {y, y + 1} (y + 1) = s := by
  rw [quittingSetReward_of_nonempty _ (Finset.insert_nonempty y {y + 1}),
    colliderReward, if_neg (by rw [card_adjacent]; decide), if_neg (by simp),
    if_pos (adjacent_eq_collider_right y)]

theorem quittingSetReward_adjacent_outsider {y j : ZMod 5}
    (hj : j ∉ ({y, y + 1} : Finset (ZMod 5))) :
    quittingSetReward (colliderReward s low m) {y, y + 1} j = 0 := by
  rw [quittingSetReward_of_nonempty _ (Finset.insert_nonempty y {y + 1})]
  refine colliderReward_of_notMem s low m _ ?_ j hj
  rw [card_adjacent]
  decide

theorem quittingSetReward_insert_adjacent {y j : ZMod 5}
    (hj : j ∉ ({y, y + 1} : Finset (ZMod 5))) :
    quittingSetReward (colliderReward s low m) (insert j {y, y + 1}) j = low := by
  rw [quittingSetReward_of_nonempty _ (Finset.insert_nonempty j _)]
  refine colliderReward_of_mem s low m _ ?_ j (Finset.mem_insert_self _ _)
    (insert_adjacent_ne_collider hj)
  rw [card_insert_adjacent hj]
  decide

/-! ## The sure-exit screen at an adjacent pair -/

/-- **When an adjacent pair is a sure exit set.**  At an adjacent pair of a
collider table the three available membership toggles are the owner stepping
out, worth `s + m 1` against `low`; the collider stepping out, worth `s + m 4`
against `s`; and an outsider joining, worth `low` against `0`.  All three are
unprofitable exactly under the displayed sign conditions. -/
theorem isQuittingSureExitSet_adjacent_of_le (hm4 : m 4 ≤ 0) (hlow : low ≤ 0)
    (hle : m 1 ≤ low - s) (y : ZMod 5) :
    IsQuittingSureExitSet (colliderReward s low m) {y, y + 1} := by
  constructor
  · intro member hmem
    have hy : member = y ∨ member = y + 1 := by simpa using hmem
    rcases hy with hy | hy <;> subst hy
    · rw [erase_adjacent_left, quittingSetReward_singleton,
        quittingSetReward_adjacent_owner, show member + 1 - member = 1 from by ring]
      linarith
    · rw [erase_adjacent_right, quittingSetReward_singleton,
        quittingSetReward_adjacent_collider, sub_succ_self y]
      linarith
  · intro outsider hout
    rw [quittingSetReward_insert_adjacent s low m hout,
      quittingSetReward_adjacent_outsider s low m hout]
    exact hlow

/-- **The sure-exit screen supplies the step-four floor.**  If the adjacent
pair at some player is not a sure exit set, while the distance-four margin and
the joint value are negative, then `low - s < m 1`. -/
theorem lt_margin_one_of_not_isQuittingSureExitSet
    (hm4 : m 4 ≤ 0) (hlow : low ≤ 0) (y : ZMod 5)
    (hno : ¬ IsQuittingSureExitSet (colliderReward s low m) {y, y + 1}) :
    low - s < m 1 := by
  rcases lt_or_ge (low - s) (m 1) with hlt | hge
  · exact hlt
  · exact absurd (isQuittingSureExitSet_adjacent_of_le s low m hm4 hlow hge y) hno

/-! ## The pocket -/

variable {s low m}

/-! ## The firing-step branch -/

/-- **The join margins of a collider completion are nonpositive.**  The join
margin is zero at distance four and `low - s` at every other distance, so a
joint value no larger than the solo self value makes all of them nonpositive:
exactly the input the firing-step branch of
`UniformEquilibrium/Quitting/Classification/Circulant/TrichotomyClosure.lean`
consumes. -/
theorem colliderJoin_nonpos (hls : low ≤ s) (d : ZMod 5) :
    colliderJoin s low d ≤ 0 := by
  by_cases hd : d = 4
  · rw [hd, colliderJoin_four]
  · rw [colliderJoin_of_ne s low hd]
    linarith

/-! ## The pocket floors -/

/-- **The pocket branch is `R₀`.**  The normalized solo matrix of a pocket
collider table admits only the zero solution of its homogeneous linear
complementarity problem. -/
theorem isR0Matrix_normalizedSoloMatrix_colliderPocket
    (hm0 : m 0 = 0) (hm1 : m 1 < 0) (hm4 : m 4 < 0) (hm2 : 0 ≤ m 2) (hm3 : 0 ≤ m 3)
    (hsum : 0 < m 1 + m 2 + m 3 + m 4) :
    Math.LinearProgramming.IsR0Matrix
      (normalizedSoloMatrix (colliderReward s low m)) := by
  rw [hasCirculantSoloMatrix_of_isCirculantPairTable
    (isCirculantPairTable_colliderReward s low m hm0)]
  exact Math.LinearProgramming.isR0Matrix_rowCirculant_pentagon_pocket hm0 hm1 hm4
    hm2 hm3 hsum

/-! ## A margin vector on the face `m 1 = 0`

The step-four equilibrium region of `isEmpty_counterexampleRegime_colliderPocket`
asks only `m 1 ≤ 0`, whereas the pocket sign condition of
`isR0Matrix_normalizedSoloMatrix_colliderPocket` — inherited from
`Math.LinearProgramming.isR0Matrix_rowCirculant_pentagon_pocket` — asks
`m 1 < 0`.  The margin vector below inhabits the difference: it satisfies every
hypothesis of the equilibrium theorem and has `m 1 = 0`, so the `R₀` route is
unavailable for it.  Whether its normalized solo matrix is nevertheless `R₀` by
some other argument is not decided here. -/

/-- The margin vector `(m 1, m 2, m 3, m 4) = (0, 1, 1, -1)`, on the face
`m 1 = 0` of the neighbour pocket. -/
def neighbourFaceMargin : ZMod 5 → ℝ :=
  fun d => if d = 2 then 1 else if d = 3 then 1 else if d = 4 then -1 else 0

@[simp] theorem neighbourFaceMargin_zero : neighbourFaceMargin 0 = 0 := by
  rw [neighbourFaceMargin, if_neg (by decide), if_neg (by decide),
    if_neg (by decide)]

@[simp] theorem neighbourFaceMargin_one : neighbourFaceMargin 1 = 0 := by
  rw [neighbourFaceMargin, if_neg (by decide), if_neg (by decide),
    if_neg (by decide)]

@[simp] theorem neighbourFaceMargin_two : neighbourFaceMargin 2 = 1 := by
  rw [neighbourFaceMargin, if_pos rfl]

@[simp] theorem neighbourFaceMargin_three : neighbourFaceMargin 3 = 1 := by
  rw [neighbourFaceMargin, if_neg (by decide), if_pos rfl]

@[simp] theorem neighbourFaceMargin_four : neighbourFaceMargin 4 = -1 := by
  rw [neighbourFaceMargin, if_neg (by decide), if_neg (by decide), if_pos rfl]

/-! ## The solo-exit preference screen

The collider completion pays no member of a joint exit more than the solo self
value `s`, and its own singleton row pays `s` on the diagonal.  So the whole
family sits inside the two assumptions of the quitting existence theorem of
Solan and Vieille, *Quitting games*, Math. Oper. Res. 26 (2001), Theorem 1.2,
as soon as `s = 1` and `low ≤ 1`.  No margin hypothesis is needed: the margin
vector only controls singleton rows for nonmembers, which those assumptions do
not constrain.

The screen therefore covers the family with no margin-sum, firing-step, or
sure-exit hypothesis at all — unlike the exclusions elsewhere in this family,
which all carry one.
-/

/-- The collider completion has unit solo exit exactly at solo self value
one. -/
theorem colliderReward_unitSoloExit (hm0 : m 0 = 0) (hs : s = 1) :
    QuittingUnitSoloExit (colliderReward s low m) := by
  intro who
  show colliderReward s low m (quittingSingletonTerminal who) who = 1
  rw [colliderReward_singleton, sub_self, hm0, add_zero, hs]

/-- The collider completion caps joint exits as soon as both the solo self
value and the joint value are at most one. -/
theorem colliderReward_cappedJointExit (hm0 : m 0 = 0) (hs : s ≤ 1)
    (hlow : low ≤ 1) : QuittingCappedJointExit (colliderReward s low m) := by
  refine quittingCappedJointExit_of_solo_of_larger (fun who ↦ ?_)
    (fun S who hmem hcard ↦ ?_)
  · show colliderReward s low m (quittingSingletonTerminal who) who ≤ 1
    rw [colliderReward_singleton, sub_self, hm0, add_zero]
    exact hs
  · by_cases hcollider : S.1 = ({who - 1, who} : Finset (ZMod 5))
    · rw [colliderReward, if_neg hcard, if_neg (by simpa using hmem),
        if_pos hcollider]
      exact hs
    · rw [colliderReward_of_mem s low m S hcard who hmem hcollider]
      exact hlow

end CirculantColliderCompletion
end GameTheory
