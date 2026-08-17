/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Cycles.AnchoredSoloPeriodic
import UniformEquilibrium.Quitting.Examples.SolanVieilleBoundaryTable
import MathUE.Periodicity

/-!
# No exact anchored solo-periodic profile on the Solan–Vieille table

On the table of Solan and Vieille, *Quitting games*,
Math. Oper. Res. 26 (2001), Section 3, fixed in `boundaryReward`, no
`IsExactAnchoredSoloPeriodic` profile exists, for any period, any schedule of
designated quitters with repetitions allowed, and any family of interior
hazards: `not_isExactAnchoredSoloPeriodic_boundaryReward`.

The scope of that statement is exactly the exact one-quitter-per-stage
anchored periodic class.  It denies exactness, at accuracy zero, of profiles
in which a single scheduled player randomizes at each stage while all others
continue surely.  It says nothing about approximate equilibria, and nothing
about profiles in which at most one player quits per stage without being
anchored in this sense.

The argument uses three features of the table.  Every solo exit pays its own
owner `1` and every two-player row pays each of its two members `1`, so the
value of quitting immediately is `1` for every player at every phase; the
exactness conditions therefore read as the floor `1 ≤ U` on all on-path
values together with the anchor `U = 1` at each scheduled quitter.  A solo
exit pays the opposite pair `0`, which excludes a cross-pair predecessor, and
pays the owner's own partner `4`, which excludes a partner predecessor.  The
schedule is then constant, and a constant schedule drives the on-path value
of an opposite-pair player below the floor.
-/

noncomputable section

namespace GameTheory

namespace SolanVieilleBoundary

open StochasticGame

/-! ## The Solan–Vieille table -/

/-- Every two-player exit of the Solan–Vieille table pays each of its two
members exactly `1`, as does every solo exit. -/
theorem boundaryReward_pair_eq_one (owner who : Player) :
    boundaryReward ⟨{owner, who}, Finset.insert_nonempty owner {who}⟩ who = 1 := by
  fin_cases owner <;> fin_cases who <;> rfl

/-- The opposite-pair partner of a player. -/
def crossPartner : Player → Player := ![2, 2, 0, 0]

/-- A solo exit pays the opposite pair `0`. -/
theorem boundaryReward_solo_crossPartner (owner : Player) :
    boundaryReward (quittingSingletonTerminal owner) (crossPartner owner) = 0 := by
  fin_cases owner <;> rfl

/-- A solo exit pays its owner's own-pair partner `4`. -/
theorem boundaryReward_solo_partner {owner who : Player}
    (hne : owner ≠ who) (hpair : owner.val / 2 = who.val / 2) :
    boundaryReward (quittingSingletonTerminal owner) who = 4 := by
  have h := soloReward_eval owner who
  rw [if_neg hne, if_pos hpair] at h
  exact h

/-- A solo exit pays the opposite pair `0`. -/
theorem boundaryReward_solo_cross {owner who : Player}
    (hpair : owner.val / 2 ≠ who.val / 2) :
    boundaryReward (quittingSingletonTerminal owner) who = 0 := by
  have hne : owner ≠ who := fun h ↦ hpair (by rw [h])
  have h := soloReward_eval owner who
  rw [if_neg hne, if_neg hpair] at h
  exact h

/-! ## The no-go -/

/-- **No exact anchored solo-periodic profile on the Solan–Vieille table.**
For every period, every schedule of designated quitters (repetitions allowed)
and every family of interior hazards, the one-quitter-per-stage exactness
system is infeasible. -/
theorem not_isExactAnchoredSoloPeriodic_boundaryReward
    {m : ℕ} [NeZero m] (w : Fin m → Player) (hazard : Fin m → ℝ)
    (h0 : ∀ k, 0 ≤ hazard k) (h1 : ∀ k, hazard k ≤ 1)
    (hpos : ∀ k, 0 < hazard k) (hlt : ∀ k, hazard k < 1) :
    ¬ IsExactAnchoredSoloPeriodic boundaryReward w hazard h0 h1 := by
  intro hexact
  set U := quittingAnchoredCyclicOnPathValue boundaryReward w hazard h0 h1 with hUdef
  have hself : ∀ x : Player, boundaryReward (quittingSingletonTerminal x) x = 1 :=
    fun x ↦ soloReward_self x
  have hren : ∀ (phase : Fin m) (who : Player),
      U phase who =
        hazard phase * boundaryReward (quittingSingletonTerminal (w phase)) who +
          (1 - hazard phase) * U (finRotate m phase) who :=
    quittingAnchoredCyclicOnPathValue_renewal boundaryReward w hazard h0 h1
  have hanchor : ∀ phase : Fin m, U (finRotate m phase) (w phase) = 1 := by
    intro phase
    rw [hUdef, ← anchor_of_isExactAnchoredSoloPeriodic hexact hpos hlt phase]
    exact hself (w phase)
  have hown : ∀ phase : Fin m, U phase (w phase) = 1 := by
    intro phase
    rw [hren phase (w phase), hanchor phase, hself (w phase)]
    ring
  have hfloor : ∀ (phase : Fin m) (who : Player), 1 ≤ U phase who := by
    intro phase who
    by_cases hne : who = w phase
    · rw [hne]
      exact (hown phase).ge
    · have h := spectatorFloor_of_isExactAnchoredSoloPeriodic hexact phase hne
      rw [boundaryReward_pair_eq_one, hself who] at h
      rw [hren phase who]
      linarith
  have hstep : ∀ phase : Fin m, w (finRotate m phase) = w phase := by
    intro phase
    by_contra hne
    by_cases hpair : (w phase).val / 2 = (w (finRotate m phase)).val / 2
    · have hfour :
          boundaryReward (quittingSingletonTerminal (w (finRotate m phase))) (w phase) = 4 :=
        boundaryReward_solo_partner hne hpair.symm
      have hr := hren (finRotate m phase) (w phase)
      rw [hfour] at hr
      have hq : 0 < 1 - hazard (finRotate m phase) := sub_pos.mpr (hlt _)
      have hmul :
          (1 - hazard (finRotate m phase)) * 1 ≤
            (1 - hazard (finRotate m phase)) *
              U (finRotate m (finRotate m phase)) (w phase) :=
        mul_le_mul_of_nonneg_left (hfloor _ (w phase)) hq.le
      linarith [hanchor phase, hpos (finRotate m phase)]
    · have hcross :
          boundaryReward (quittingSingletonTerminal (w phase))
            (w (finRotate m phase)) = 0 :=
        boundaryReward_solo_cross hpair
      have hr := hren phase (w (finRotate m phase))
      rw [hcross, hown (finRotate m phase)] at hr
      linarith [hfloor phase (w (finRotate m phase)), hpos phase]
  have hmpos : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  set origin : Fin m := ⟨0, hmpos⟩ with horigin
  haveI : Nonempty (Fin m) := ⟨origin⟩
  set z : Player := crossPartner (w origin) with hz
  have hsucc : ∀ k : Fin m, w (k + 1) = w k := by
    intro k
    simpa using hstep k
  obtain ⟨designated, hdesignated⟩ := Math.exists_const_of_cyclic_succ_eq hsucc
  have hzero : ∀ phase : Fin m,
      boundaryReward (quittingSingletonTerminal (w phase)) z = 0 := by
    intro phase
    rw [(hdesignated phase).trans (hdesignated origin).symm, hz]
    exact boundaryReward_solo_crossPartner (w origin)
  obtain ⟨peak, hpeak⟩ := Finite.exists_max fun phase : Fin m ↦ U phase z
  have hr := hren peak z
  rw [hzero peak] at hr
  have hq : 0 < 1 - hazard peak := sub_pos.mpr (hlt peak)
  have hmul :
      (1 - hazard peak) * U (finRotate m peak) z ≤ (1 - hazard peak) * U peak z :=
    mul_le_mul_of_nonneg_left (hpeak (finRotate m peak)) hq.le
  have hfl := hfloor peak z
  nlinarith [hpos peak]

/-- The Solan–Vieille table admits no exact anchored solo-periodic profile of
any period. -/
theorem not_exists_exactAnchoredSoloPeriodic_boundaryReward :
    ¬ ∃ (m : ℕ) (_ : NeZero m) (w : Fin m → Player) (hazard : Fin m → ℝ)
        (h0 : ∀ k, 0 ≤ hazard k) (h1 : ∀ k, hazard k ≤ 1),
        (∀ k, 0 < hazard k) ∧ (∀ k, hazard k < 1) ∧
          IsExactAnchoredSoloPeriodic boundaryReward w hazard h0 h1 := by
  rintro ⟨m, hm, w, hazard, h0, h1, hpos, hlt, hexact⟩
  exact not_isExactAnchoredSoloPeriodic_boundaryReward w hazard h0 h1 hpos hlt hexact

end SolanVieilleBoundary

end GameTheory
