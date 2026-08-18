/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Research.Quitting.AnchoredCyclicScreen
import UniformEquilibrium.Quitting.Examples.SolanVieilleBoundarySoloPeriodicNoGo
import MathUE.Periodicity

/-!
# A quantitative solo-periodic gap for the Solan–Vieille table

On the table of Solan and Vieille, *Quitting games*,
Math. Oper. Res. 26 (2001), Section 3, fixed in `boundaryReward`, an
anchored solo-periodic profile cannot be `ε`-exact unless the product of two
of its own hazards is at most `ε * (1 + h)` with `h` the second of the two:
`exists_hazard_product_le_mul_one_add_of_isεExactAnchoredSoloPeriodic`.  With a
uniform floor `q` and a uniform ceiling `Q` on the hazards this reads
`q ^ 2 ≤ ε * (1 + Q)` (`sq_le_mul_one_add_of_isεExactAnchoredSoloPeriodic`), so
the defect of the anchored system is bounded below by `q ^ 2 / (1 + Q)`,
uniformly over every period and every schedule with repetitions.  Since every
hazard is at most `1`, the readable form `q ^ 2 ≤ 2 * ε`
(`sq_le_two_mul_of_isεExactAnchoredSoloPeriodic`) is the ceiling-free
corollary.

The bound is the accuracy of the one-stage anchored system
`IsεExactAnchoredSoloPeriodic`, not the terminal exploitability of the
induced behavior profile; the two differ because one-stage defects accumulate
along the play.

Underneath the three branches sits a floor that holds for every anchored
`ε`-exact profile on this table, with no condition on the hazards: quitting on
the spot pays every player exactly `1` here, so no on-path value falls below
`1 - ε` (`one_sub_le_onPathValue_of_isεExactAnchoredSoloPeriodic`).  At accuracy
zero the floor is `1` (`one_le_onPathValue_of_isExactAnchoredSoloPeriodic`).

The three branches of the argument each contribute a bound of their own, and
`one_le_or_exists_consecutiveHazardBound_of_isεExactAnchoredSoloPeriodic`
records all three separately.  A constant schedule forces `1 ≤ ε` outright:
the opposite pair's on-path value is driven below the floor whatever the
hazards are.  At a phase where the schedule changes, a partner successor
forces `3 * h * h' ≤ ε * (1 + h)` and a cross-pair successor forces
`h * h' ≤ ε * (1 + h' - h)`, with `h` and `h'` the hazards at that phase and
its successor; it is those two branches that degrade as the hazards go to
zero.  Only the constant branch uses hazard positivity, and a schedule with a
vanishing hazard satisfies the product bound trivially, so the product bound
itself asks nothing of the hazards beyond the unit interval.
-/

noncomputable section

namespace GameTheory

namespace SolanVieilleBoundary

open StochasticGame

/-- **The one-stage floor on the Solan–Vieille table.**  Quitting on the spot
pays every player exactly `1` there, alone or alongside the scheduled quitter,
so no on-path coordinate of an `ε`-exact anchored solo-periodic profile falls
below `1 - ε`.  Neither hazard positivity nor any condition on the schedule
enters. -/
theorem one_sub_le_onPathValue_of_isεExactAnchoredSoloPeriodic
    {m : ℕ} {w : Fin m → Player} {hazard : Fin m → ℝ}
    {h0 : ∀ k, 0 ≤ hazard k} {h1 : ∀ k, hazard k ≤ 1} {ε : ℝ}
    (hexact : IsεExactAnchoredSoloPeriodic boundaryReward ε w hazard h0 h1)
    (phase : Fin m) (who : Player) :
    1 - ε ≤
      quittingAnchoredCyclicOnPathValue boundaryReward w hazard h0 h1 phase who :=
  sub_le_quittingAnchoredCyclicOnPathValue_of_flatQuitRow (soloReward_self who)
    hexact phase fun _ ↦ boundaryReward_pair_eq_one (w phase) who

/-- **The three branches of the solo-periodic gap, with their own constants.**
Either the accuracy is already at least `1`, which is what a constant schedule
forces, or at some phase the hazard `h` there and the hazard `h'` at its
cyclic successor satisfy one of two bounds: `3 * h * h' ≤ ε * (1 + h)`, forced
when the successor is the pair partner of the scheduled quitter, or
`h * h' ≤ ε * (1 + h' - h)`, forced when it belongs to the opposite pair. -/
theorem one_le_or_exists_consecutiveHazardBound_of_isεExactAnchoredSoloPeriodic
    {m : ℕ} [NeZero m] (w : Fin m → Player) (hazard : Fin m → ℝ)
    (h0 : ∀ k, 0 ≤ hazard k) (h1 : ∀ k, hazard k ≤ 1)
    (hpos : ∀ k, 0 < hazard k) {ε : ℝ} (hε : 0 ≤ ε)
    (hexact : IsεExactAnchoredSoloPeriodic boundaryReward ε w hazard h0 h1) :
    1 ≤ ε ∨ ∃ phase : Fin m,
      3 * hazard phase * hazard (finRotate m phase) ≤
          ε * (1 + hazard phase) ∨
        hazard phase * hazard (finRotate m phase) ≤
          ε * (1 + hazard (finRotate m phase) - hazard phase) := by
  set U := quittingAnchoredCyclicOnPathValue boundaryReward w hazard h0 h1 with hU
  have hself : ∀ x : Player, boundaryReward (quittingSingletonTerminal x) x = 1 :=
    fun x ↦ soloReward_self x
  have hren : ∀ (phase : Fin m) (who : Player),
      U phase who =
        hazard phase *
            boundaryReward (quittingSingletonTerminal (w phase)) who +
          (1 - hazard phase) * U (finRotate m phase) who :=
    quittingAnchoredCyclicOnPathValue_renewal boundaryReward w hazard h0 h1
  have hup : ∀ phase : Fin m,
      hazard phase * (U (finRotate m phase) (w phase) - 1) ≤ ε := by
    intro phase
    have h := anchorUpperBound_of_isεExactAnchoredSoloPeriodic hexact phase
    rwa [hself] at h
  have hfloor : ∀ (phase : Fin m) (who : Player), 1 - ε ≤ U phase who :=
    one_sub_le_onPathValue_of_isεExactAnchoredSoloPeriodic hexact
  have hown : ∀ phase : Fin m, hazard phase * (U phase (w phase) - 1) ≤ ε := by
    intro phase
    have hr := hren phase (w phase)
    rw [hself] at hr
    have hfac : hazard phase * (U phase (w phase) - 1) =
        (1 - hazard phase) *
          (hazard phase * (U (finRotate m phase) (w phase) - 1)) := by
      rw [hr]; ring
    rw [hfac]
    rcases le_or_gt 0
        (hazard phase * (U (finRotate m phase) (w phase) - 1)) with hsgn | hsgn
    · nlinarith [hup phase, h0 phase]
    · nlinarith [h1 phase]
  by_cases hconst : ∀ phase : Fin m, w (finRotate m phase) = w phase
  · left
    have hmpos : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
    let origin : Fin m := ⟨0, hmpos⟩
    haveI : Nonempty (Fin m) := ⟨origin⟩
    have hsucc : ∀ k : Fin m, w (k + 1) = w k := fun k ↦ by simpa using hconst k
    obtain ⟨designated, hdesignated⟩ := Math.exists_const_of_cyclic_succ_eq hsucc
    have hzero : ∀ phase : Fin m,
        boundaryReward (quittingSingletonTerminal (w phase))
          (crossPartner (w origin)) = 0 := by
      intro phase
      rw [(hdesignated phase).trans (hdesignated origin).symm]
      exact boundaryReward_solo_crossPartner (w origin)
    obtain ⟨peak, hpeak⟩ :=
      Finite.exists_max fun phase : Fin m ↦ U phase (crossPartner (w origin))
    have hr := hren peak (crossPartner (w origin))
    rw [hzero peak] at hr
    have hle := hpeak (finRotate m peak)
    have hfl := hfloor peak (crossPartner (w origin))
    nlinarith [hpos peak, h1 peak, hle, hr, hfl,
      mul_nonneg (by linarith [h1 peak] : (0 : ℝ) ≤ 1 - hazard peak)
        (by linarith : (0 : ℝ) ≤ U peak (crossPartner (w origin)) -
          U (finRotate m peak) (crossPartner (w origin)))]
  · right
    simp only [not_forall] at hconst
    obtain ⟨phase, hphase⟩ := hconst
    refine ⟨phase, ?_⟩
    by_cases hpair : (w phase).val / 2 = (w (finRotate m phase)).val / 2
    · left
      have hfour : boundaryReward
          (quittingSingletonTerminal (w (finRotate m phase))) (w phase) = 4 :=
        boundaryReward_solo_partner hphase hpair.symm
      have hr := hren (finRotate m phase) (w phase)
      rw [hfour] at hr
      have hfl := hfloor (finRotate m (finRotate m phase)) (w phase)
      have hanch := hup phase
      have hstep : 3 * hazard (finRotate m phase) - ε ≤
          U (finRotate m phase) (w phase) - 1 := by
        nlinarith [hr, hfl, h1 (finRotate m phase), hε,
          mul_nonneg (h0 (finRotate m phase)) hε,
          mul_nonneg
            (by linarith [h1 (finRotate m phase)] :
              (0 : ℝ) ≤ 1 - hazard (finRotate m phase))
            (by linarith :
              (0 : ℝ) ≤ U (finRotate m (finRotate m phase)) (w phase) - (1 - ε))]
      have hstep2 : hazard phase * (3 * hazard (finRotate m phase) - ε) ≤ ε :=
        le_trans (mul_le_mul_of_nonneg_left hstep (h0 phase)) hanch
      linarith [hstep2]
    · right
      have hcross : boundaryReward (quittingSingletonTerminal (w phase))
          (w (finRotate m phase)) = 0 :=
        boundaryReward_solo_cross hpair
      have hr := hren phase (w (finRotate m phase))
      rw [hcross] at hr
      have hfl := hfloor phase (w (finRotate m phase))
      have hanch := hown (finRotate m phase)
      have hs : 1 - ε ≤ (1 - hazard phase) *
          U (finRotate m phase) (w (finRotate m phase)) := by linarith
      have hmul1 : hazard (finRotate m phase) * (1 - ε) ≤
          hazard (finRotate m phase) *
            ((1 - hazard phase) *
              U (finRotate m phase) (w (finRotate m phase))) :=
        mul_le_mul_of_nonneg_left hs (h0 (finRotate m phase))
      have hmul2 : (1 - hazard phase) *
            (hazard (finRotate m phase) *
              U (finRotate m phase) (w (finRotate m phase))) ≤
          (1 - hazard phase) * (ε + hazard (finRotate m phase)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by linarith [h1 phase])
        linarith
      linarith [hmul1, hmul2]

/-- **The quantitative solo-periodic gap.**  Two of the profile's own hazards
have product at most `ε * (1 + h)` with `h` the second of the two.  Hazard
positivity is not needed: a vanishing hazard satisfies the bound at once. -/
theorem exists_hazard_product_le_mul_one_add_of_isεExactAnchoredSoloPeriodic
    {m : ℕ} [NeZero m] (w : Fin m → Player) (hazard : Fin m → ℝ)
    (h0 : ∀ k, 0 ≤ hazard k) (h1 : ∀ k, hazard k ≤ 1) {ε : ℝ} (hε : 0 ≤ ε)
    (hexact : IsεExactAnchoredSoloPeriodic boundaryReward ε w hazard h0 h1) :
    ∃ j k : Fin m, hazard j * hazard k ≤ ε * (1 + hazard k) := by
  by_cases hvanish : ∃ k : Fin m, hazard k = 0
  · obtain ⟨k, hk⟩ := hvanish
    exact ⟨k, k, by rw [hk]; simpa using hε⟩
  · push Not at hvanish
    have hpos : ∀ k, 0 < hazard k := fun k ↦ (h0 k).lt_of_ne (hvanish k).symm
    rcases one_le_or_exists_consecutiveHazardBound_of_isεExactAnchoredSoloPeriodic
        w hazard h0 h1 hpos hε hexact with hone | ⟨phase, hbranch⟩
    · obtain ⟨origin⟩ : Nonempty (Fin m) :=
        ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne m)⟩⟩
      refine ⟨origin, origin, ?_⟩
      linarith [h0 origin, h1 origin, hone,
        mul_nonneg (le_trans zero_le_one hone) (h0 origin),
        mul_le_mul_of_nonneg_right (h1 origin) (h0 origin)]
    · refine ⟨phase, finRotate m phase, ?_⟩
      rcases hbranch with hpartner | hcross
      · linarith [hpartner, mul_nonneg hε (h0 (finRotate m phase)),
          mul_le_mul_of_nonneg_left (h1 phase) hε]
      · linarith [hcross, mul_nonneg hε (h0 phase)]

/-- With a uniform floor `q` and a uniform ceiling `Q` on the hazards the gap
is uniform over the whole class: every period, every schedule with
repetitions, every hazard family inside `[q, Q]`. -/
theorem sq_le_mul_one_add_of_isεExactAnchoredSoloPeriodic
    {m : ℕ} [NeZero m] (w : Fin m → Player) (hazard : Fin m → ℝ)
    (h0 : ∀ k, 0 ≤ hazard k) (h1 : ∀ k, hazard k ≤ 1) {ε q Q : ℝ} (hε : 0 ≤ ε)
    (hq : 0 ≤ q) (hfloor : ∀ k, q ≤ hazard k) (hceiling : ∀ k, hazard k ≤ Q)
    (hexact : IsεExactAnchoredSoloPeriodic boundaryReward ε w hazard h0 h1) :
    q ^ 2 ≤ ε * (1 + Q) := by
  obtain ⟨j, k, hjk⟩ :=
    exists_hazard_product_le_mul_one_add_of_isεExactAnchoredSoloPeriodic
      w hazard h0 h1 hε hexact
  have hsq : q ^ 2 ≤ hazard j * hazard k := by
    have hmul := mul_le_mul (hfloor j) (hfloor k) hq (le_trans hq (hfloor j))
    linarith [hmul]
  have hup : ε * (1 + hazard k) ≤ ε * (1 + Q) :=
    mul_le_mul_of_nonneg_left (by linarith [hceiling k]) hε
  linarith

/-- The ceiling-free reading: every hazard is at most `1`, so the sharp bound
`sq_le_mul_one_add_of_isεExactAnchoredSoloPeriodic` implies `q ^ 2 ≤ 2 * ε`. -/
theorem sq_le_two_mul_of_isεExactAnchoredSoloPeriodic
    {m : ℕ} [NeZero m] (w : Fin m → Player) (hazard : Fin m → ℝ)
    (h0 : ∀ k, 0 ≤ hazard k) (h1 : ∀ k, hazard k ≤ 1) {ε q : ℝ} (hε : 0 ≤ ε)
    (hq : 0 ≤ q) (hfloor : ∀ k, q ≤ hazard k)
    (hexact : IsεExactAnchoredSoloPeriodic boundaryReward ε w hazard h0 h1) :
    q ^ 2 ≤ 2 * ε := by
  have hstep := sq_le_mul_one_add_of_isεExactAnchoredSoloPeriodic w hazard h0 h1
    hε hq hfloor h1 hexact
  linarith

/-- The contrapositive: below the quantitative threshold no anchored
solo-periodic profile is `ε`-exact. -/
theorem not_isεExactAnchoredSoloPeriodic_of_mul_one_add_lt_sq
    {m : ℕ} [NeZero m] (w : Fin m → Player) (hazard : Fin m → ℝ)
    (h0 : ∀ k, 0 ≤ hazard k) (h1 : ∀ k, hazard k ≤ 1) {ε q Q : ℝ} (hε : 0 ≤ ε)
    (hq : 0 ≤ q) (hfloor : ∀ k, q ≤ hazard k) (hceiling : ∀ k, hazard k ≤ Q)
    (hsmall : ε * (1 + Q) < q ^ 2) :
    ¬ IsεExactAnchoredSoloPeriodic boundaryReward ε w hazard h0 h1 := by
  intro hexact
  have := sq_le_mul_one_add_of_isεExactAnchoredSoloPeriodic w hazard h0 h1 hε hq
    hfloor hceiling hexact
  linarith

/-- The exact no-go is the case `ε = 0` of the quantitative bound, and holds
without any strict upper bound on the hazards. -/
theorem not_isExactAnchoredSoloPeriodic_of_quantitativeGap
    {m : ℕ} [NeZero m] (w : Fin m → Player) (hazard : Fin m → ℝ)
    (h0 : ∀ k, 0 ≤ hazard k) (h1 : ∀ k, hazard k ≤ 1)
    (hpos : ∀ k, 0 < hazard k) :
    ¬ IsExactAnchoredSoloPeriodic boundaryReward w hazard h0 h1 := by
  intro hexact
  obtain ⟨j, k, hjk⟩ :=
    exists_hazard_product_le_mul_one_add_of_isεExactAnchoredSoloPeriodic
      w hazard h0 h1 le_rfl hexact
  nlinarith [hpos j, hpos k]

/-- **The exact floor.**  At accuracy zero the one-stage floor is the quit-now
value itself: every on-path coordinate of an exact anchored solo-periodic
profile on this table is at least `1`.  Exactness is available only where some
hazard vanishes (`not_isExactAnchoredSoloPeriodic_of_quantitativeGap`). -/
theorem one_le_onPathValue_of_isExactAnchoredSoloPeriodic
    {m : ℕ} {w : Fin m → Player} {hazard : Fin m → ℝ}
    {h0 : ∀ k, 0 ≤ hazard k} {h1 : ∀ k, hazard k ≤ 1}
    (hexact : IsExactAnchoredSoloPeriodic boundaryReward w hazard h0 h1)
    (phase : Fin m) (who : Player) :
    1 ≤
      quittingAnchoredCyclicOnPathValue boundaryReward w hazard h0 h1 phase who := by
  simpa using
    one_sub_le_onPathValue_of_isεExactAnchoredSoloPeriodic hexact phase who

end SolanVieilleBoundary

end GameTheory
