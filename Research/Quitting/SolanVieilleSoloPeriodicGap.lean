/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Examples.SolanVieilleBoundarySoloPeriodicNoGo
import MathUE.Periodicity

/-!
# A quantitative solo-periodic gap for the Solan–Vieille table

On the table of Solan and Vieille, *Quitting games*,
Math. Oper. Res. 26 (2001), Section 3, fixed in `boundaryReward`, an
anchored solo-periodic profile cannot be `ε`-exact unless `ε` is at least
half the product of two of its own hazards:
`exists_hazard_product_le_two_mul_of_isεExactAnchoredSoloPeriodic`.  With a
uniform floor `q` on the hazards this reads `q ^ 2 ≤ 2 * ε`
(`sq_le_two_mul_of_isεExactAnchoredSoloPeriodic`), so the defect of the
anchored system is bounded below by `q ^ 2 / 2`, uniformly over every period
and every schedule with repetitions.

The bound is the accuracy of the one-stage anchored system
`IsεExactAnchoredSoloPeriodic`, not the terminal exploitability of the
induced behavior profile; the two differ because one-stage defects accumulate
along the play.

The three branches of the argument each contribute a bound of their own.  A
constant schedule forces `1 ≤ ε` outright: the opposite pair's on-path value
is driven below the floor whatever the hazards are.  A cross-pair predecessor
and a partner predecessor each force a bound proportional to the product of
the two hazards at the phase where the schedule changes, and it is those two
branches that degrade as the hazards go to zero.
-/

noncomputable section

namespace GameTheory

namespace SolanVieilleBoundary

open StochasticGame

/-- **The quantitative solo-periodic gap.**  Two of the profile's own hazards
have product at most `2 * ε`. -/
theorem exists_hazard_product_le_two_mul_of_isεExactAnchoredSoloPeriodic
    {m : ℕ} [NeZero m] (w : Fin m → Player) (hazard : Fin m → ℝ)
    (h0 : ∀ k, 0 ≤ hazard k) (h1 : ∀ k, hazard k ≤ 1)
    (hpos : ∀ k, 0 < hazard k) {ε : ℝ} (hε : 0 ≤ ε)
    (hexact : IsεExactAnchoredSoloPeriodic boundaryReward ε w hazard h0 h1) :
    ∃ j k : Fin m, hazard j * hazard k ≤ 2 * ε := by
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
  have hfloor : ∀ (phase : Fin m) (who : Player), 1 - ε ≤ U phase who := by
    intro phase who
    by_cases hne : who = w phase
    · have hlo := anchorLowerBound_of_isεExactAnchoredSoloPeriodic hexact phase
      rw [hself] at hlo
      have hr := hren phase (w phase)
      rw [hself] at hr
      rw [hne]
      nlinarith [hlo, hr, h0 phase, h1 phase]
    · have h := spectatorFloor_of_isεExactAnchoredSoloPeriodic hexact phase hne
      rw [boundaryReward_pair_eq_one, hself who] at h
      rw [hren phase who]
      linarith
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
  · have hmpos : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
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
    have hone : 1 ≤ ε := by
      nlinarith [hpos peak, h1 peak, hle, hr, hfl,
        mul_nonneg (by linarith [h1 peak] : (0 : ℝ) ≤ 1 - hazard peak)
          (by linarith : (0 : ℝ) ≤ U peak (crossPartner (w origin)) -
            U (finRotate m peak) (crossPartner (w origin)))]
    exact ⟨origin, origin, by nlinarith [h0 origin, h1 origin]⟩
  · simp only [not_forall] at hconst
    obtain ⟨phase, hphase⟩ := hconst
    refine ⟨phase, finRotate m phase, ?_⟩
    by_cases hpair : (w phase).val / 2 = (w (finRotate m phase)).val / 2
    · have hfour : boundaryReward
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
      nlinarith [hstep2, h1 phase, h0 phase, hε]
    · have hcross : boundaryReward (quittingSingletonTerminal (w phase))
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
      nlinarith [hmul1, hmul2, h1 phase, h1 (finRotate m phase), hε, h0 phase,
        mul_nonneg hε (by linarith [h1 (finRotate m phase), h0 phase] :
          (0 : ℝ) ≤ 1 - hazard (finRotate m phase) + hazard phase)]

/-- With a uniform floor on the hazards the gap is uniform over the whole
class: every period, every schedule with repetitions, every hazard family
above the floor. -/
theorem sq_le_two_mul_of_isεExactAnchoredSoloPeriodic
    {m : ℕ} [NeZero m] (w : Fin m → Player) (hazard : Fin m → ℝ)
    (h0 : ∀ k, 0 ≤ hazard k) (h1 : ∀ k, hazard k ≤ 1)
    (hpos : ∀ k, 0 < hazard k) {ε q : ℝ} (hε : 0 ≤ ε) (hq : 0 ≤ q)
    (hfloor : ∀ k, q ≤ hazard k)
    (hexact : IsεExactAnchoredSoloPeriodic boundaryReward ε w hazard h0 h1) :
    q ^ 2 ≤ 2 * ε := by
  obtain ⟨j, k, hjk⟩ :=
    exists_hazard_product_le_two_mul_of_isεExactAnchoredSoloPeriodic
      w hazard h0 h1 hpos hε hexact
  nlinarith [hfloor j, hfloor k, hq]

/-- The contrapositive: below the quantitative threshold no anchored
solo-periodic profile is `ε`-exact. -/
theorem not_isεExactAnchoredSoloPeriodic_of_two_mul_lt_sq
    {m : ℕ} [NeZero m] (w : Fin m → Player) (hazard : Fin m → ℝ)
    (h0 : ∀ k, 0 ≤ hazard k) (h1 : ∀ k, hazard k ≤ 1)
    (hpos : ∀ k, 0 < hazard k) {ε q : ℝ} (hε : 0 ≤ ε) (hq : 0 ≤ q)
    (hfloor : ∀ k, q ≤ hazard k) (hsmall : 2 * ε < q ^ 2) :
    ¬ IsεExactAnchoredSoloPeriodic boundaryReward ε w hazard h0 h1 := by
  intro hexact
  have := sq_le_two_mul_of_isεExactAnchoredSoloPeriodic w hazard h0 h1 hpos hε hq
    hfloor hexact
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
    exists_hazard_product_le_two_mul_of_isεExactAnchoredSoloPeriodic
      w hazard h0 h1 hpos le_rfl hexact
  nlinarith [hpos j, hpos k]

end SolanVieilleBoundary

end GameTheory
