/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Research.Quitting.AnchoredCyclicRenewal
import Research.Quitting.AnchoredCyclicScreen
import UniformEquilibrium.Quitting.Cycles.SingletonArcCycle
import UniformEquilibrium.Quitting.Examples.SolanVieilleBoundarySoloPeriodicNoGo

/-!
# Terminal-level exploitability of solo-periodic profiles on the Solan–Vieille table

`SolanVieilleSoloPeriodicGap` bounds the accuracy of the one-stage anchored
system.  This module works at the terminal-payoff level instead, where the
bound is on the actual best-reply value of the induced behavior profile.

Two facts drive everything.  Quitting at the opening phase pays *exactly* `1`
to every player against every solo-periodic profile, whatever the schedule and
the hazards (`quittingAnchoredCyclicQuitValue_eq_one`): every solo exit pays
its owner `1` and every two-player exit pays each of its two members `1`, so
the value of quitting immediately does not depend on what the scheduled
quitter does.  And the four on-path values always sum to `5`
(`sum_onPathValue_eq_five`), because each solo exit distributes a total of
`1 + 4 + 0 + 0` across the four players.

Together these give `one_le_quittingBestReplyValue_anchoredCyclicProfile`: the
best-reply value is at least `1` for every player, so every player whose
on-path value falls below `1` is exploitable by the shortfall, and
`exists_onPathValue_le_half_min_pairSum` locates such a player as soon as the
two pairs' value sums are unbalanced.

The sum identity also delimits what this route can reach.  Since the four
on-path values sum to `5`, they can all equal `5 / 4`, and then quitting at
any phase loses `1 / 4` for every player.  A uniform terminal constant
therefore cannot come from stopping deviations alone; it requires the refusal
deviation, whose gain obeys a different recursion — one that grows at the
refusing player's own phases and decays at every other phase.
-/

noncomputable section

namespace GameTheory

namespace SolanVieilleBoundary

open StochasticGame

/-! ## Quitting at a phase pays exactly one -/

/-- **Flat quit-now.**  Against a solo-periodic profile on the Solan–Vieille
table, quitting at any phase pays exactly `1`, for every player and every
hazard. -/
theorem quittingAnchoredCyclicQuitValue_eq_one {m : ℕ}
    (w : Fin m → Player) (hazard : Fin m → ℝ) (phase : Fin m) (who : Player) :
    quittingAnchoredCyclicQuitValue boundaryReward w hazard phase who = 1 := by
  have hself : ∀ x : Player, boundaryReward (quittingSingletonTerminal x) x = 1 :=
    fun x ↦ soloReward_self x
  unfold quittingAnchoredCyclicQuitValue
  by_cases h : who = w phase
  · rw [if_pos h]
    exact hself who
  · rw [if_neg h, boundaryReward_pair_eq_one, hself who]
    ring

/-- Every player's best-reply value against a solo-periodic profile is at
least `1`. -/
theorem one_le_quittingBestReplyValue_anchoredCyclicProfile {m : ℕ} [NeZero m]
    (w : Fin m → Player) (hazard : Fin m → ℝ)
    (h0 : ∀ k, 0 ≤ hazard k) (h1 : ∀ k, hazard k ≤ 1) (who : Player) :
    1 ≤ quittingBestReplyValue boundaryReward
      (quittingAnchoredCyclicProfile boundaryReward w hazard h0 h1) who := by
  have hsup := sSup_range_quittingTerminalPayoff_update_anchoredCyclicProfile
    boundaryReward w hazard h0 h1 who
  have hcap := quittingAnchoredCyclicQuitValue_le_responseCap boundaryReward w
    hazard h0 h1 who
  rw [quittingAnchoredCyclicQuitValue_eq_one] at hcap
  show (1 : ℝ) ≤ ⨆ deviation, _
  rw [show (⨆ deviation : (quittingGame boundaryReward).BehaviorStrategy who,
      quittingTerminalPayoff boundaryReward
        (Function.update
          (quittingAnchoredCyclicProfile boundaryReward w hazard h0 h1) who
          deviation) who) =
      sSup (Set.range fun deviation :
          (quittingGame boundaryReward).BehaviorStrategy who ↦
        quittingTerminalPayoff boundaryReward
          (Function.update
            (quittingAnchoredCyclicProfile boundaryReward w hazard h0 h1) who
            deviation) who) from rfl, hsup]
  exact hcap

/-! ## The four on-path values always sum to five -/

/-- Every solo exit of the table distributes a total of `5` across the four
players. -/
theorem sum_soloReward_eq_five (owner : Player) :
    ∑ who : Player, boundaryReward (quittingSingletonTerminal owner) who = 5 := by
  have heval : ∀ o k : Player,
      boundaryReward (quittingSingletonTerminal o) k =
        if o = k then 1 else if o.val / 2 = k.val / 2 then 4 else 0 :=
    fun o k ↦ soloReward_eval o k
  fin_cases owner <;> simp [Fin.sum_univ_four, heval] <;> norm_num

/-- **The playerwise sum identity.**  The four on-path values of a
solo-periodic profile sum to `5` at every phase. -/
theorem sum_onPathValue_eq_five {m : ℕ} [NeZero m]
    (w : Fin m → Player) (hazard : Fin m → ℝ)
    (h0 : ∀ k, 0 ≤ hazard k) (h1 : ∀ k, hazard k ≤ 1)
    (hpos : ∀ k, 0 < hazard k) (phase : Fin m) :
    ∑ who : Player,
        quittingAnchoredCyclicOnPathValue boundaryReward w hazard h0 h1
          phase who = 5 := by
  set U := quittingAnchoredCyclicOnPathValue boundaryReward w hazard h0 h1 with hU
  set D : Fin m → ℝ := fun k ↦ (∑ who : Player, U k who) - 5 with hD
  have hstep : ∀ k : Fin m, D k = (1 - hazard k) * D (finRotate m k) := by
    intro k
    have hren : ∀ who : Player, U k who =
        hazard k * boundaryReward (quittingSingletonTerminal (w k)) who +
          (1 - hazard k) * U (finRotate m k) who :=
      fun who ↦ quittingAnchoredCyclicOnPathValue_renewal boundaryReward w hazard
        h0 h1 k who
    have hsum : ∑ who : Player, U k who =
        hazard k * (∑ who : Player,
            boundaryReward (quittingSingletonTerminal (w k)) who) +
          (1 - hazard k) * ∑ who : Player, U (finRotate m k) who := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun who _ ↦ hren who
    rw [sum_soloReward_eq_five] at hsum
    simp only [hD]
    linarith
  haveI : Nonempty (Fin m) := ⟨phase⟩
  obtain ⟨peak, hpeak⟩ := Finite.exists_max D
  obtain ⟨dip, hdip⟩ := Finite.exists_min D
  have hupper : D peak ≤ 0 := by
    have h := hstep peak
    have := hpeak (finRotate m peak)
    nlinarith [hpos peak, h1 peak,
      mul_nonneg (by linarith [h1 peak] : (0 : ℝ) ≤ 1 - hazard peak)
        (by linarith : (0 : ℝ) ≤ D peak - D (finRotate m peak))]
  have hlower : 0 ≤ D dip := by
    have h := hstep dip
    have := hdip (finRotate m dip)
    nlinarith [hpos dip, h1 dip,
      mul_nonneg (by linarith [h1 dip] : (0 : ℝ) ≤ 1 - hazard dip)
        (by linarith : (0 : ℝ) ≤ D (finRotate m dip) - D dip)]
  have hzero : D phase = 0 := le_antisymm
    (le_trans (hpeak phase) hupper) (le_trans hlower (hdip phase))
  simp only [hD] at hzero
  linarith

/-! ## Locating an exploitable player -/

/-- Some player's on-path value is at most half the smaller of the two pairs'
value sums, hence is exploitable by the shortfall below `1`. -/
theorem exists_onPathValue_le_half_min_pairSum {m : ℕ} [NeZero m]
    (w : Fin m → Player) (hazard : Fin m → ℝ)
    (h0 : ∀ k, 0 ≤ hazard k) (h1 : ∀ k, hazard k ≤ 1) (phase : Fin m) :
    ∃ who : Player,
      2 * quittingAnchoredCyclicOnPathValue boundaryReward w hazard h0 h1
          phase who ≤
        min (quittingAnchoredCyclicOnPathValue boundaryReward w hazard h0 h1
              phase 0 +
            quittingAnchoredCyclicOnPathValue boundaryReward w hazard h0 h1
              phase 1)
          (quittingAnchoredCyclicOnPathValue boundaryReward w hazard h0 h1
              phase 2 +
            quittingAnchoredCyclicOnPathValue boundaryReward w hazard h0 h1
              phase 3) := by
  set U := quittingAnchoredCyclicOnPathValue boundaryReward w hazard h0 h1 phase
    with hU
  rcases le_total (U 0 + U 1) (U 2 + U 3) with hcase | hcase
  · rcases le_total (U 0) (U 1) with h | h
    · exact ⟨0, by rw [min_eq_left hcase]; linarith⟩
    · exact ⟨1, by rw [min_eq_left hcase]; linarith⟩
  · rcases le_total (U 2) (U 3) with h | h
    · exact ⟨2, by rw [min_eq_right hcase]; linarith⟩
    · exact ⟨3, by rw [min_eq_right hcase]; linarith⟩

/-- **The terminal gap in the unbalanced regime.**  If one of the two pairs
carries value sum at most `2 * (1 - γ)` at the opening phase, then some player
gains at least `γ` over the on-path value. -/
theorem exists_onPathValue_add_le_bestReplyValue {m : ℕ} [NeZero m]
    (w : Fin m → Player) (hazard : Fin m → ℝ)
    (h0 : ∀ k, 0 ≤ hazard k) (h1 : ∀ k, hazard k ≤ 1) {γ : ℝ}
    (hpair : min (quittingAnchoredCyclicOnPathValue boundaryReward w hazard h0 h1
            (quittingAnchoredCyclicStart m) 0 +
          quittingAnchoredCyclicOnPathValue boundaryReward w hazard h0 h1
            (quittingAnchoredCyclicStart m) 1)
        (quittingAnchoredCyclicOnPathValue boundaryReward w hazard h0 h1
            (quittingAnchoredCyclicStart m) 2 +
          quittingAnchoredCyclicOnPathValue boundaryReward w hazard h0 h1
            (quittingAnchoredCyclicStart m) 3) ≤ 2 * (1 - γ)) :
    ∃ who : Player,
      quittingTerminalPayoff boundaryReward
          (quittingAnchoredCyclicProfile boundaryReward w hazard h0 h1) who + γ ≤
        quittingBestReplyValue boundaryReward
          (quittingAnchoredCyclicProfile boundaryReward w hazard h0 h1) who := by
  obtain ⟨who, hwho⟩ := exists_onPathValue_le_half_min_pairSum w hazard h0 h1
    (quittingAnchoredCyclicStart m)
  refine ⟨who, ?_⟩
  have hbest := one_le_quittingBestReplyValue_anchoredCyclicProfile w hazard h0 h1 who
  have hpay : quittingTerminalPayoff boundaryReward
      (quittingAnchoredCyclicProfile boundaryReward w hazard h0 h1) who =
      quittingAnchoredCyclicOnPathValue boundaryReward w hazard h0 h1
        (quittingAnchoredCyclicStart m) who := by
    rw [quittingTerminalPayoff_anchoredCyclicProfile]
  rw [hpay]
  linarith

/-- **The ceiling of the stopping route.**  Some player's on-path value is at
most `5 / 4`, and no better bound follows from the sum identity alone: the
four values can all equal `5 / 4`.  Since quitting pays exactly `1`, stopping
deviations alone therefore yield no positive uniform terminal gap. -/
theorem exists_onPathValue_le_five_fourths {m : ℕ} [NeZero m]
    (w : Fin m → Player) (hazard : Fin m → ℝ)
    (h0 : ∀ k, 0 ≤ hazard k) (h1 : ∀ k, hazard k ≤ 1)
    (hpos : ∀ k, 0 < hazard k) (phase : Fin m) :
    ∃ who : Player,
      quittingAnchoredCyclicOnPathValue boundaryReward w hazard h0 h1
        phase who ≤ 5 / 4 := by
  obtain ⟨who, hwho⟩ := exists_onPathValue_le_half_min_pairSum w hazard h0 h1 phase
  have hsum := sum_onPathValue_eq_five w hazard h0 h1 hpos phase
  rw [Fin.sum_univ_four] at hsum
  refine ⟨who, ?_⟩
  have hleft := min_le_left
    (quittingAnchoredCyclicOnPathValue boundaryReward w hazard h0 h1 phase 0 +
      quittingAnchoredCyclicOnPathValue boundaryReward w hazard h0 h1 phase 1)
    (quittingAnchoredCyclicOnPathValue boundaryReward w hazard h0 h1 phase 2 +
      quittingAnchoredCyclicOnPathValue boundaryReward w hazard h0 h1 phase 3)
  have hright := min_le_right
    (quittingAnchoredCyclicOnPathValue boundaryReward w hazard h0 h1 phase 0 +
      quittingAnchoredCyclicOnPathValue boundaryReward w hazard h0 h1 phase 1)
    (quittingAnchoredCyclicOnPathValue boundaryReward w hazard h0 h1 phase 2 +
      quittingAnchoredCyclicOnPathValue boundaryReward w hazard h0 h1 phase 3)
  linarith

/-! ## The refusal deviation and its recursion

Refusal against an anchored cyclic profile is the same schedule with the
refuser's own phases carrying hazard zero
(`quittingAnchoredCyclicRefusalHazard`), so the refusal value obeys the same
renewal system as the on-path value.  Subtracting the two renewals gives a
recursion for the gain with two branches.
-/

/-- The refusal gain `D^k = R^k - U^k` at the refuser's own coordinate. -/
def refusalGain {m : ℕ} (w : Fin m → Player) (hazard : Fin m → ℝ)
    (h0 : ∀ k, 0 ≤ hazard k) (h1 : ∀ k, hazard k ≤ 1) (refuser : Player)
    (phase : Fin m) : ℝ :=
  quittingAnchoredCyclicOnPathValue boundaryReward w
      (quittingAnchoredCyclicRefusalHazard w hazard refuser)
      (quittingAnchoredCyclicRefusalHazard_nonneg h0 w refuser)
      (quittingAnchoredCyclicRefusalHazard_le_one h1 w refuser) phase refuser -
    quittingAnchoredCyclicOnPathValue boundaryReward w hazard h0 h1 phase refuser

/-- **Own-phase growth.**  At each phase scheduling the refuser, the refusal
gain increases by the hazard times the excess of the next phase's on-path
value over the refuser's own solo exit value. -/
theorem refusalGain_of_eq {m : ℕ} (w : Fin m → Player) (hazard : Fin m → ℝ)
    (h0 : ∀ k, 0 ≤ hazard k) (h1 : ∀ k, hazard k ≤ 1) {refuser : Player}
    {phase : Fin m} (h : w phase = refuser) :
    refusalGain w hazard h0 h1 refuser phase =
      refusalGain w hazard h0 h1 refuser (finRotate m phase) +
        hazard phase *
          (quittingAnchoredCyclicOnPathValue boundaryReward w hazard h0 h1
            (finRotate m phase) refuser - 1) := by
  have hzero : quittingAnchoredCyclicRefusalHazard w hazard refuser phase = 0 := by
    unfold quittingAnchoredCyclicRefusalHazard
    rw [if_pos h]
  have hR := quittingAnchoredCyclicOnPathValue_renewal boundaryReward w
    (quittingAnchoredCyclicRefusalHazard w hazard refuser)
    (quittingAnchoredCyclicRefusalHazard_nonneg h0 w refuser)
    (quittingAnchoredCyclicRefusalHazard_le_one h1 w refuser) phase refuser
  rw [hzero] at hR
  have hself : boundaryReward (quittingSingletonTerminal refuser) refuser = 1 :=
    soloReward_self refuser
  have hU := quittingAnchoredCyclicOnPathValue_renewal boundaryReward w hazard
    h0 h1 phase refuser
  rw [h, hself] at hU
  unfold refusalGain
  linarith

/-- **Off-phase decay.**  At every other phase the refusal gain is scaled by
the survival probability. -/
theorem refusalGain_of_ne {m : ℕ} (w : Fin m → Player) (hazard : Fin m → ℝ)
    (h0 : ∀ k, 0 ≤ hazard k) (h1 : ∀ k, hazard k ≤ 1) {refuser : Player}
    {phase : Fin m} (h : w phase ≠ refuser) :
    refusalGain w hazard h0 h1 refuser phase =
      (1 - hazard phase) *
        refusalGain w hazard h0 h1 refuser (finRotate m phase) := by
  have hkeep : quittingAnchoredCyclicRefusalHazard w hazard refuser phase =
      hazard phase := by
    unfold quittingAnchoredCyclicRefusalHazard
    rw [if_neg h]
  have hR := quittingAnchoredCyclicOnPathValue_renewal boundaryReward w
    (quittingAnchoredCyclicRefusalHazard w hazard refuser)
    (quittingAnchoredCyclicRefusalHazard_nonneg h0 w refuser)
    (quittingAnchoredCyclicRefusalHazard_le_one h1 w refuser) phase refuser
  rw [hkeep] at hR
  have hU := quittingAnchoredCyclicOnPathValue_renewal boundaryReward w hazard
    h0 h1 phase refuser
  unfold refusalGain
  rw [hR, hU]
  ring

/-! ## Telescoping around the cycle -/

/-- Survival accumulated over `n` steps from `phase`, counting only the phases
at which the refuser is not the scheduled quitter. -/
def refusalWeight {m : ℕ} (w : Fin m → Player) (hazard : Fin m → ℝ)
    (refuser : Player) : Fin m → ℕ → ℝ
  | _, 0 => 1
  | phase, (n + 1) =>
      (if w phase = refuser then 1 else 1 - hazard phase) *
        refusalWeight w hazard refuser (finRotate m phase) n

/-- Drift accumulated over `n` steps from `phase`: the weighted excess of the
on-path value over the refuser's solo exit value at the refuser's own
phases. -/
def refusalDrift {m : ℕ} (w : Fin m → Player) (hazard : Fin m → ℝ)
    (h0 : ∀ k, 0 ≤ hazard k) (h1 : ∀ k, hazard k ≤ 1) (refuser : Player) :
    Fin m → ℕ → ℝ
  | _, 0 => 0
  | phase, (n + 1) =>
      (if w phase = refuser then
          hazard phase *
            (quittingAnchoredCyclicOnPathValue boundaryReward w hazard h0 h1
              (finRotate m phase) refuser - 1)
        else 0) +
        (if w phase = refuser then 1 else 1 - hazard phase) *
          refusalDrift w hazard h0 h1 refuser (finRotate m phase) n

/-- **The telescoped recursion.**  Unrolling `n` steps splits the refusal gain
into accumulated drift plus surviving weight times the gain `n` steps on. -/
theorem refusalGain_telescope {m : ℕ} (w : Fin m → Player) (hazard : Fin m → ℝ)
    (h0 : ∀ k, 0 ≤ hazard k) (h1 : ∀ k, hazard k ≤ 1) (refuser : Player) :
    ∀ (n : ℕ) (phase : Fin m),
      refusalGain w hazard h0 h1 refuser phase =
        refusalDrift w hazard h0 h1 refuser phase n +
          refusalWeight w hazard refuser phase n *
            refusalGain w hazard h0 h1 refuser ((finRotate m)^[n] phase) := by
  intro n
  induction n with
  | zero => intro phase; simp [refusalDrift, refusalWeight]
  | succ n ih =>
    intro phase
    rw [Function.iterate_succ_apply]
    by_cases h : w phase = refuser
    · rw [refusalGain_of_eq w hazard h0 h1 h, ih (finRotate m phase),
        refusalDrift, refusalWeight]
      simp only [if_pos h]
      ring
    · rw [refusalGain_of_ne w hazard h0 h1 h, ih (finRotate m phase),
        refusalDrift, refusalWeight]
      simp only [if_neg h]
      ring

/-- The `n`-step rotation of a phase is a shift modulo the period. -/
theorem val_iterate_finRotate {m : ℕ} (phase : Fin m) :
    ∀ n : ℕ, ((finRotate m)^[n] phase).val = (phase.val + n) % m := by
  intro n
  induction n with
  | zero => simpa using (Nat.mod_eq_of_lt phase.isLt).symm
  | succ n ih =>
    rw [Function.iterate_succ_apply', coe_finRotate_eq_succ_mod, ih,
      Nat.mod_add_mod, Nat.add_assoc]

/-- One full cycle of rotations is the identity. -/
theorem iterate_finRotate_period {m : ℕ} (phase : Fin m) :
    (finRotate m)^[m] phase = phase := by
  apply Fin.ext
  rw [val_iterate_finRotate, Nat.add_mod_right]
  exact Nat.mod_eq_of_lt phase.isLt

/-- **The cycle identity.**  Around one full cycle the refusal gain satisfies
`D * (1 - W) = Drift`, with `W` the survival weight of the refuser's absence
over one cycle and `Drift` the accumulated own-phase drift. -/
theorem refusalGain_mul_one_sub_weight {m : ℕ} (w : Fin m → Player)
    (hazard : Fin m → ℝ) (h0 : ∀ k, 0 ≤ hazard k) (h1 : ∀ k, hazard k ≤ 1)
    (refuser : Player) (phase : Fin m) :
    refusalGain w hazard h0 h1 refuser phase *
        (1 - refusalWeight w hazard refuser phase m) =
      refusalDrift w hazard h0 h1 refuser phase m := by
  have h := refusalGain_telescope w hazard h0 h1 refuser m phase
  rw [iterate_finRotate_period] at h
  linarith [h]

/-! ## Sign of the accumulated quantities -/

theorem refusalWeight_nonneg {m : ℕ} (w : Fin m → Player) {hazard : Fin m → ℝ}
    (h1 : ∀ k, hazard k ≤ 1) (refuser : Player) :
    ∀ (n : ℕ) (phase : Fin m), 0 ≤ refusalWeight w hazard refuser phase n := by
  intro n
  induction n with
  | zero => intro phase; simp [refusalWeight]
  | succ n ih =>
    intro phase
    rw [refusalWeight]
    refine mul_nonneg ?_ (ih _)
    split_ifs with h
    · norm_num
    · linarith [h1 phase]

theorem refusalWeight_le_one {m : ℕ} (w : Fin m → Player) {hazard : Fin m → ℝ}
    (h0 : ∀ k, 0 ≤ hazard k) (h1 : ∀ k, hazard k ≤ 1) (refuser : Player) :
    ∀ (n : ℕ) (phase : Fin m), refusalWeight w hazard refuser phase n ≤ 1 := by
  intro n
  induction n with
  | zero => intro phase; simp [refusalWeight]
  | succ n ih =>
    intro phase
    rw [refusalWeight]
    have hrec := ih (finRotate m phase)
    have hrec0 := refusalWeight_nonneg w h1 refuser n (finRotate m phase)
    split_ifs with h
    · linarith
    · nlinarith [h0 phase, h1 phase]

/-- If the refuser's on-path value never falls below its own solo exit value,
the accumulated drift is nonnegative. -/
theorem refusalDrift_nonneg {m : ℕ} (w : Fin m → Player) (hazard : Fin m → ℝ)
    (h0 : ∀ k, 0 ≤ hazard k) (h1 : ∀ k, hazard k ≤ 1) (refuser : Player)
    (hU : ∀ k : Fin m, 1 ≤ quittingAnchoredCyclicOnPathValue boundaryReward w
      hazard h0 h1 k refuser) :
    ∀ (n : ℕ) (phase : Fin m),
      0 ≤ refusalDrift w hazard h0 h1 refuser phase n := by
  intro n
  induction n with
  | zero => intro phase; simp [refusalDrift]
  | succ n ih =>
    intro phase
    rw [refusalDrift]
    refine add_nonneg ?_ (mul_nonneg ?_ (ih _))
    · split_ifs with h
      · exact mul_nonneg (h0 phase) (by linarith [hU (finRotate m phase)])
      · exact le_refl 0
    · split_ifs with h
      · norm_num
      · linarith [h1 phase]

/-- **The refusal gain dominates the accumulated drift.**  The cycle identity
divides the drift by the absorption deficit `1 - W ≤ 1`, so the gain is at
least the undivided drift. -/
theorem refusalDrift_le_refusalGain {m : ℕ} (w : Fin m → Player)
    (hazard : Fin m → ℝ) (h0 : ∀ k, 0 ≤ hazard k) (h1 : ∀ k, hazard k ≤ 1)
    (refuser : Player)
    (hU : ∀ k : Fin m, 1 ≤ quittingAnchoredCyclicOnPathValue boundaryReward w
      hazard h0 h1 k refuser)
    (phase : Fin m) (hW : refusalWeight w hazard refuser phase m < 1) :
    refusalDrift w hazard h0 h1 refuser phase m ≤
      refusalGain w hazard h0 h1 refuser phase := by
  have hid := refusalGain_mul_one_sub_weight w hazard h0 h1 refuser phase
  have hdr := refusalDrift_nonneg w hazard h0 h1 refuser hU m phase
  have hw0 := refusalWeight_nonneg w h1 refuser m phase
  nlinarith [hid, hdr, hw0, hW]

/-! ## The residual -/

/-- The uniform terminal gap for solo-periodic profiles on the Solan–Vieille
table: some player's best-reply value exceeds its on-path value by at least
`1 / 12`, for every period, every schedule with repetitions and every family
of interior hazards.  The constant is the small-hazard optimum over exit
distributions of the refusal gain; extracting it from
`refusalGain_mul_one_sub_weight` requires bounding the accumulated drift
against the absorption deficit, which is not carried out here. -/
def HasUniformSoloPeriodicTerminalGap : Prop :=
  ∀ (m : ℕ) (_ : NeZero m) (w : Fin m → Player) (hazard : Fin m → ℝ)
    (h0 : ∀ k, 0 ≤ hazard k) (h1 : ∀ k, hazard k ≤ 1),
    (∀ k, 0 < hazard k) →
      ∃ who : Player,
        quittingTerminalPayoff boundaryReward
            (quittingAnchoredCyclicProfile boundaryReward w hazard h0 h1) who +
            1 / 12 ≤
          quittingBestReplyValue boundaryReward
            (quittingAnchoredCyclicProfile boundaryReward w hazard h0 h1) who

end SolanVieilleBoundary

end GameTheory
