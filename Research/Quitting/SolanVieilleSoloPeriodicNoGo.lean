/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Research.Quitting.AnchoredCyclicScreen
import UniformEquilibrium.Quitting.Examples.SolanVieilleBoundaryTable
import UniformEquilibrium.Quitting.Cycles.SingletonArcCycle

/-!
# No single-quitter periodic profile is exactly anchored on the Solan–Vieille table

An *exact anchored solo-periodic profile* is a cyclic schedule of designated
quitters, one per stage, each mixing with an interior hazard while every other
player continues, whose one-stage root is exactly endpoint Nash against the
on-path continuation value of the next phase.  `IsExactAnchoredSoloPeriodic`
states that property for a general reward table.

On the table of Solan and Vieille, *Quitting games*,
Math. Oper. Res. 26 (2001), Section 3, fixed in
`GameTheory.SolanVieilleBoundary.boundaryReward`, no such profile exists, for
any period, any schedule with repetitions, and any interior hazards:
`not_isExactAnchoredSoloPeriodic_boundaryReward`.

The argument uses three features of that table.  Every solo exit pays its own
owner `1` and every two-player row pays each of its two members `1`, so the
value of quitting immediately is `1` for every player at every phase; the
exactness conditions therefore read as the floor `1 ≤ U` on all on-path values
together with the anchor `U = 1` at each scheduled quitter.  A solo exit pays
the opposite pair `0`, which excludes a cross-pair predecessor, and pays the
owner's own partner `4`, which excludes a partner predecessor.  The schedule
is then constant, and a constant schedule drives the on-path value of an
opposite-pair player below the floor.
-/

noncomputable section

namespace GameTheory

namespace SolanVieilleSoloPeriodic

open StochasticGame SolanVieilleBoundary

/-! ## A cyclic schedule fixed by the rotation is constant -/

/-- A function on phases that is invariant under the cyclic successor is
constant. -/
theorem eq_of_forall_finRotate_eq {m : ℕ} {α : Type*} {f : Fin m → α}
    (hstep : ∀ k : Fin m, f (finRotate m k) = f k) (k l : Fin m) : f k = f l := by
  have hzero : ∀ (j : ℕ) (hj : j < m), f ⟨j, hj⟩ = f ⟨0, by omega⟩ := by
    intro j
    induction j with
    | zero => intro _; rfl
    | succ n ih =>
      intro hj
      have hn : n < m := Nat.lt_of_succ_lt hj
      have hrot : finRotate m ⟨n, hn⟩ = ⟨n + 1, hj⟩ := by
        apply Fin.ext
        rw [coe_finRotate_eq_succ_mod]
        exact Nat.mod_eq_of_lt hj
      calc f ⟨n + 1, hj⟩ = f (finRotate m ⟨n, hn⟩) := by rw [hrot]
        _ = f ⟨n, hn⟩ := hstep _
        _ = _ := ih hn
  have hk := hzero k.val k.isLt
  have hl := hzero l.val l.isLt
  simpa using hk.trans hl.symm

/-! ## Exact anchored solo-periodic profiles -/

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- An exact anchored solo-periodic profile: at every phase the scheduled
player `w phase` mixes with hazard `hazard phase` while every other player
continues, and the resulting one-stage root is exactly endpoint Nash against
the on-path continuation value of the next phase. -/
def IsExactAnchoredSoloPeriodic
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) {m : ℕ}
    (w : Fin m → ι) (hazard : Fin m → ℝ)
    (h0 : ∀ k, 0 ≤ hazard k) (h1 : ∀ k, hazard k ≤ 1) : Prop :=
  ∀ phase : Fin m,
    IsεQuittingRootEndpointNash reward
      (quittingAnchoredCyclicOnPathValue reward w hazard h0 h1 (finRotate m phase))
      0 (quittingAnchoredCyclicCycle w hazard h0 h1 phase)

/-- Exactness in the sense of `IsExactAnchoredSoloPeriodic` is exactly the
statement that at every phase no player gains by any deviation of the
one-stage root against the on-path continuation value of the next phase. -/
theorem isExactAnchoredSoloPeriodic_iff_rootNash
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) {m : ℕ}
    (w : Fin m → ι) (hazard : Fin m → ℝ)
    (h0 : ∀ k, 0 ≤ hazard k) (h1 : ∀ k, hazard k ≤ 1) :
    IsExactAnchoredSoloPeriodic reward w hazard h0 h1 ↔
      ∀ phase : Fin m,
        IsεQuittingRootNash reward
          (quittingAnchoredCyclicOnPathValue reward w hazard h0 h1 (finRotate m phase))
          0 (quittingAnchoredCyclicCycle w hazard h0 h1 phase) :=
  forall_congr' fun _ ↦
    isεQuittingRootEndpointNash_iff_isεQuittingRootNash _ _ _ _

/-- The indifference anchor: at every phase the scheduled quitter's own solo
exit value equals the on-path continuation value of the next phase. -/
theorem anchor_of_isExactAnchoredSoloPeriodic
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι} {m : ℕ}
    {w : Fin m → ι} {hazard : Fin m → ℝ}
    {h0 : ∀ k, 0 ≤ hazard k} {h1 : ∀ k, hazard k ≤ 1}
    (hexact : IsExactAnchoredSoloPeriodic reward w hazard h0 h1)
    (hpos : ∀ k, 0 < hazard k) (hlt : ∀ k, hazard k < 1) (phase : Fin m) :
    reward (quittingSingletonTerminal (w phase)) (w phase) =
      quittingAnchoredCyclicOnPathValue reward w hazard h0 h1
        (finRotate m phase) (w phase) := by
  have hroot : quittingAnchoredCyclicCycle w hazard h0 h1 phase =
      quittingSoloMixedRoot (w phase)
        (quittingHazardCoin (hazard phase) (h0 phase) (h1 phase)) := rfl
  have h := hexact phase (w phase)
  rw [hroot] at h
  rw [quittingRootEndpointDifference,
    quittingRootQuitPayoff_soloMixedRoot_self,
    quittingRootContinuePayoff_soloMixedRoot_self] at h
  simp only [quittingSoloMixedRoot_self, quittingHazardCoin_true_toReal,
    quittingHazardCoin_false_toReal, neg_zero] at h
  have hp := hpos phase
  have hq : 0 < 1 - hazard phase := sub_pos.mpr (hlt phase)
  have hle : reward (quittingSingletonTerminal (w phase)) (w phase) -
      quittingAnchoredCyclicOnPathValue reward w hazard h0 h1
        (finRotate m phase) (w phase) ≤ 0 := by nlinarith [h.1]
  have hge : 0 ≤ reward (quittingSingletonTerminal (w phase)) (w phase) -
      quittingAnchoredCyclicOnPathValue reward w hazard h0 h1
        (finRotate m phase) (w phase) := by nlinarith [h.2]
  linarith

/-- The spectator floor: no player other than the scheduled quitter gains by
quitting at that phase. -/
theorem spectatorFloor_of_isExactAnchoredSoloPeriodic
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι} {m : ℕ}
    {w : Fin m → ι} {hazard : Fin m → ℝ}
    {h0 : ∀ k, 0 ≤ hazard k} {h1 : ∀ k, hazard k ≤ 1}
    (hexact : IsExactAnchoredSoloPeriodic reward w hazard h0 h1)
    (phase : Fin m) {who : ι} (hne : who ≠ w phase) :
    hazard phase *
          reward ⟨{w phase, who}, Finset.insert_nonempty (w phase) {who}⟩ who +
        (1 - hazard phase) * reward (quittingSingletonTerminal who) who ≤
      hazard phase * reward (quittingSingletonTerminal (w phase)) who +
        (1 - hazard phase) *
          quittingAnchoredCyclicOnPathValue reward w hazard h0 h1
            (finRotate m phase) who := by
  have hroot : quittingAnchoredCyclicCycle w hazard h0 h1 phase =
      quittingSoloMixedRoot (w phase)
        (quittingHazardCoin (hazard phase) (h0 phase) (h1 phase)) := rfl
  have h := (hexact phase who).1
  rw [hroot] at h
  rw [quittingRootEndpointDifference,
    quittingRootQuitPayoff_soloMixedRoot_of_ne _ _ hne,
    quittingRootContinuePayoff_soloMixedRoot_of_ne _ _ hne] at h
  rw [quittingSoloMixedRoot_of_ne hne] at h
  simp only [PMF.pure_apply_self, ENNReal.toReal_one,
    one_mul, quittingHazardCoin_true_toReal, quittingHazardCoin_false_toReal] at h
  linarith

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
  have hzero : ∀ phase : Fin m,
      boundaryReward (quittingSingletonTerminal (w phase)) z = 0 := by
    intro phase
    rw [eq_of_forall_finRotate_eq hstep phase origin, hz]
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

end SolanVieilleSoloPeriodic

end GameTheory
