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
on-path values sum to `5`, they can all equal `5 / 4`, and then quitting at the
opening phase loses `1 / 4` for every player.  A uniform terminal constant
therefore cannot come from the opening quit alone; it needs the refusal
deviation, whose gain obeys a different recursion — one that grows at the
refusing player's own phases and decays at every other phase.

Refusal is available to the deviator:
`quittingAnchoredCyclicOnPathValue_refusalHazard_le_bestReplyValue` places the
zeroed on-path value below the best-reply value, and
`terminalPayoff_add_refusalGain_le_bestReplyValue` reads that as the refusal
gain being a terminal gain.

Two subclasses of the uniform statement are checked here.  A schedule omitting
some player pays that player exactly four times what it pays the player's own
pair partner (`onPathValue_eq_four_mul_of_forall_ne`), which together with the
sum identity already forces a gap of `1 / 12`
(`exists_terminalPayoff_add_twelfth_le_bestReplyValue_of_forall_ne`); a
schedule paying some player nothing at all forces the full gap `1`.  And on the
uniform four-cycle — period four, the schedule `0, 1, 2, 3`, one common
interior hazard — the renewal system solves explicitly and the refusal gain of
player `0` lies between `1 / 12` and `1 / 12 + 6 * p`
(`twelfth_le_bestReplyValue_sub_terminalPayoff_uniformFourCycle` and
`uniformFourCycleRefusalGain_le`).

The residual is therefore the schedules designating every player at least
once, isolated as `HasSurjectiveSoloPeriodicTerminalGap` and shown to be the
whole residual by `hasUniformSoloPeriodicTerminalGap_of_surjective`.  It cannot
be closed by quitting and refusing alone:
`not_forall_exists_quitValue_or_refusalValue_gap` exhibits a period-five
schedule on which both of those deviations gain at most `1 / 16`.
-/

noncomputable section

namespace GameTheory

/-! ## Refusal is one of the deviations -/

/-- **The refusal deviation is available.**  The best-reply value against an
anchored cyclic profile is at least the on-path value of the same schedule with
the deviator's own phases carrying hazard zero, which is what refusing to quit
forever pays (`quittingPeriodicWindowRefusalValue_anchoredCyclic`). -/
theorem quittingAnchoredCyclicOnPathValue_refusalHazard_le_bestReplyValue
    {ι : Type} [Fintype ι] [DecidableEq ι] {m : ℕ} [NeZero m]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (w : Fin m → ι) (hazard : Fin m → ℝ)
    (h0 : ∀ k, 0 ≤ hazard k) (h1 : ∀ k, hazard k ≤ 1) (who : ι) :
    quittingAnchoredCyclicOnPathValue reward w
        (quittingAnchoredCyclicRefusalHazard w hazard who)
        (quittingAnchoredCyclicRefusalHazard_nonneg h0 w who)
        (quittingAnchoredCyclicRefusalHazard_le_one h1 w who)
        (quittingAnchoredCyclicStart m) who ≤
      quittingBestReplyValue reward
        (quittingAnchoredCyclicProfile reward w hazard h0 h1) who := by
  have hsup := sSup_range_quittingTerminalPayoff_update_anchoredCyclicProfile
    reward w hazard h0 h1 who
  show _ ≤ ⨆ deviation, _
  rw [show (⨆ deviation : (quittingGame reward).BehaviorStrategy who,
      quittingTerminalPayoff reward
        (Function.update (quittingAnchoredCyclicProfile reward w hazard h0 h1)
          who deviation) who) =
      sSup (Set.range fun deviation :
          (quittingGame reward).BehaviorStrategy who ↦
        quittingTerminalPayoff reward
          (Function.update (quittingAnchoredCyclicProfile reward w hazard h0 h1)
            who deviation) who) from rfl, hsup]
  unfold quittingAnchoredCyclicResponseCap
    quittingPeriodicWindowBestResponseValue
  rw [← quittingPeriodicWindowRefusalValue_anchoredCyclic reward w hazard h0 h1
    (quittingAnchoredCyclicStart m) who]
  exact le_max_left _ _

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

/-! ## A contracted phase family vanishes -/

/-- **Strict contraction around the cycle forces zero.**  A phase-indexed
family reproduced at every phase by the survival factor of an interior hazard
vanishes identically: its maximum is nonpositive and its minimum
nonnegative. -/
theorem eq_zero_of_renewalDecay {m : ℕ} [NeZero m] {hazard : Fin m → ℝ}
    (h1 : ∀ k, hazard k ≤ 1) (hpos : ∀ k, 0 < hazard k) {D : Fin m → ℝ}
    (hstep : ∀ k, D k = (1 - hazard k) * D (finRotate m k)) (phase : Fin m) :
    D phase = 0 := by
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
  exact le_antisymm (le_trans (hpeak phase) hupper) (le_trans hlower (hdip phase))

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
  have hzero : D phase = 0 := eq_zero_of_renewalDecay h1 hpos hstep phase
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

/-- **The ceiling of the opening quit.**  Some player's on-path value is at
most `5 / 4`, and no better bound follows from the sum identity alone: the
four values can all equal `5 / 4`.  Since quitting at the opening phase pays
exactly `1`, that deviation alone yields no positive uniform terminal gap. -/
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

/-! ## Schedules that omit a player

A player never scheduled to quit is paid only through its own pair partner's
exits, which pay it `4` for every `1` they pay the partner.  Its on-path value
is therefore exactly four times the partner's at every phase, and the sum
identity then forces one of the four values below the quit-now value.
-/

theorem player_eq (z : Player) : z = 0 ∨ z = 1 ∨ z = 2 ∨ z = 3 := by
  revert z
  decide

/-- The own-pair partner of a player. -/
def pairPartner : Player → Player := ![1, 0, 3, 2]

theorem pairPartner_ne (who : Player) : pairPartner who ≠ who := by
  revert who
  decide

theorem val_div_two_pairPartner (who : Player) :
    (pairPartner who).val / 2 = who.val / 2 := by
  revert who
  decide

/-- A solo exit not owned by `absent` pays `absent` four times what it pays
`absent`'s own-pair partner: `4` against `1` at the partner's own exit, and
`0` against `0` at every exit of the opposite pair. -/
theorem boundaryReward_solo_eq_four_mul {owner absent partner : Player}
    (hpair : absent.val / 2 = partner.val / 2) (hne : absent ≠ partner)
    (howner : owner ≠ absent) :
    boundaryReward (quittingSingletonTerminal owner) absent =
      4 * boundaryReward (quittingSingletonTerminal owner) partner := by
  have heval : ∀ o k : Player,
      boundaryReward (quittingSingletonTerminal o) k =
        if o = k then 1 else if o.val / 2 = k.val / 2 then 4 else 0 :=
    fun o k ↦ soloReward_eval o k
  rw [heval owner absent, heval owner partner, if_neg howner]
  by_cases hcase : owner.val / 2 = absent.val / 2
  · have hval : owner = partner := by
      refine Fin.ext_iff.2 ?_
      have hlt0 := owner.isLt
      have hlt1 := absent.isLt
      have hlt2 := partner.isLt
      have hne0 : owner.val ≠ absent.val := fun h ↦ howner (Fin.ext_iff.2 h)
      have hne1 : absent.val ≠ partner.val := fun h ↦ hne (Fin.ext_iff.2 h)
      omega
    rw [if_pos hcase, if_pos hval]
    norm_num
  · have hne2 : owner ≠ partner := fun h ↦ hcase (by rw [h, hpair])
    rw [if_neg hcase, if_neg hne2, if_neg (fun h ↦ hcase (by rw [hpair]; exact h))]
    norm_num

/-- **The value of an unscheduled player.**  If the schedule never designates
`absent`, then at every phase `absent`'s on-path value is four times that of
its own-pair partner. -/
theorem onPathValue_eq_four_mul_of_forall_ne {m : ℕ} [NeZero m]
    (w : Fin m → Player) (hazard : Fin m → ℝ)
    (h0 : ∀ k, 0 ≤ hazard k) (h1 : ∀ k, hazard k ≤ 1) (hpos : ∀ k, 0 < hazard k)
    {absent partner : Player} (hpair : absent.val / 2 = partner.val / 2)
    (hne : absent ≠ partner) (hmiss : ∀ k, w k ≠ absent) (phase : Fin m) :
    quittingAnchoredCyclicOnPathValue boundaryReward w hazard h0 h1 phase absent =
      4 * quittingAnchoredCyclicOnPathValue boundaryReward w hazard h0 h1 phase
        partner := by
  set U := quittingAnchoredCyclicOnPathValue boundaryReward w hazard h0 h1 with hU
  have hzero : ∀ k : Fin m, U k absent - 4 * U k partner = 0 := by
    refine eq_zero_of_renewalDecay h1 hpos (fun k ↦ ?_)
    have hA := quittingAnchoredCyclicOnPathValue_renewal boundaryReward w hazard
      h0 h1 k absent
    have hB := quittingAnchoredCyclicOnPathValue_renewal boundaryReward w hazard
      h0 h1 k partner
    have hr := boundaryReward_solo_eq_four_mul hpair hne (hmiss k)
    rw [hr] at hA
    simp only [hU] at hA hB ⊢
    linarith
  linarith [hzero phase]

/-- **A player paid nothing by the schedule.**  If every scheduled exit pays
`who` zero, its on-path value vanishes at every phase. -/
theorem onPathValue_eq_zero_of_forall_reward_eq_zero {m : ℕ} [NeZero m]
    (w : Fin m → Player) (hazard : Fin m → ℝ)
    (h0 : ∀ k, 0 ≤ hazard k) (h1 : ∀ k, hazard k ≤ 1) (hpos : ∀ k, 0 < hazard k)
    {who : Player}
    (hzero : ∀ k, boundaryReward (quittingSingletonTerminal (w k)) who = 0)
    (phase : Fin m) :
    quittingAnchoredCyclicOnPathValue boundaryReward w hazard h0 h1 phase who =
      0 := by
  refine eq_zero_of_renewalDecay h1 hpos
    (D := fun k ↦ quittingAnchoredCyclicOnPathValue boundaryReward w hazard h0 h1
      k who) (fun k ↦ ?_) phase
  have hren := quittingAnchoredCyclicOnPathValue_renewal boundaryReward w hazard
    h0 h1 k who
  rw [hzero k] at hren
  linarith

/-- **A whole pair left out of the schedule is exploitable by one.**  A player
paid zero by every scheduled exit gains the full quit-now value. -/
theorem exists_terminalPayoff_add_one_le_bestReplyValue {m : ℕ} [NeZero m]
    (w : Fin m → Player) (hazard : Fin m → ℝ)
    (h0 : ∀ k, 0 ≤ hazard k) (h1 : ∀ k, hazard k ≤ 1) (hpos : ∀ k, 0 < hazard k)
    {who : Player}
    (hzero : ∀ k, boundaryReward (quittingSingletonTerminal (w k)) who = 0) :
    quittingTerminalPayoff boundaryReward
        (quittingAnchoredCyclicProfile boundaryReward w hazard h0 h1) who + 1 ≤
      quittingBestReplyValue boundaryReward
        (quittingAnchoredCyclicProfile boundaryReward w hazard h0 h1) who := by
  have hbest := one_le_quittingBestReplyValue_anchoredCyclicProfile w hazard h0 h1 who
  rw [quittingTerminalPayoff_anchoredCyclicProfile,
    onPathValue_eq_zero_of_forall_reward_eq_zero w hazard h0 h1 hpos hzero]
  linarith

/-- **Omitting a player already gives the gap.**  If the schedule never
designates some player, then some player's best-reply value exceeds its on-path
value by at least `1 / 12`. -/
theorem exists_terminalPayoff_add_twelfth_le_bestReplyValue_of_forall_ne
    {m : ℕ} [NeZero m] (w : Fin m → Player) (hazard : Fin m → ℝ)
    (h0 : ∀ k, 0 ≤ hazard k) (h1 : ∀ k, hazard k ≤ 1) (hpos : ∀ k, 0 < hazard k)
    {absent : Player} (hmiss : ∀ k, w k ≠ absent) :
    ∃ who : Player,
      quittingTerminalPayoff boundaryReward
          (quittingAnchoredCyclicProfile boundaryReward w hazard h0 h1) who +
          1 / 12 ≤
        quittingBestReplyValue boundaryReward
          (quittingAnchoredCyclicProfile boundaryReward w hazard h0 h1) who := by
  set U := quittingAnchoredCyclicOnPathValue boundaryReward w hazard h0 h1
    (quittingAnchoredCyclicStart m) with hU
  have hgap : ∀ z : Player, U z + 1 / 12 ≤ 1 →
      ∃ who : Player,
        quittingTerminalPayoff boundaryReward
            (quittingAnchoredCyclicProfile boundaryReward w hazard h0 h1) who +
            1 / 12 ≤
          quittingBestReplyValue boundaryReward
            (quittingAnchoredCyclicProfile boundaryReward w hazard h0 h1) who := by
    intro z hz
    refine ⟨z, ?_⟩
    have hbest := one_le_quittingBestReplyValue_anchoredCyclicProfile w hazard h0 h1 z
    rw [quittingTerminalPayoff_anchoredCyclicProfile]
    simp only [← hU]
    linarith
  have hfour := onPathValue_eq_four_mul_of_forall_ne w hazard h0 h1 hpos
    (val_div_two_pairPartner absent).symm (Ne.symm (pairPartner_ne absent)) hmiss
    (quittingAnchoredCyclicStart m)
  have hsum := sum_onPathValue_eq_five w hazard h0 h1 hpos
    (quittingAnchoredCyclicStart m)
  rw [Fin.sum_univ_four] at hsum
  simp only [← hU] at hfour hsum
  rcases le_total (U (pairPartner absent)) (11 / 12) with hcase | hcase
  · exact hgap (pairPartner absent) (by linarith)
  · have hsmall : ∀ i j : Player, U i + U j ≤ 5 / 12 →
        ∃ who : Player, U who + 1 / 12 ≤ 1 := by
      intro i j hij
      rcases le_total (U i) (U j) with hc | hc
      · exact ⟨i, by linarith⟩
      · exact ⟨j, by linarith⟩
    have hpick : ∃ who : Player, U who + 1 / 12 ≤ 1 := by
      rcases player_eq absent with rfl | rfl | rfl | rfl
      · rw [show pairPartner (0 : Player) = 1 from rfl] at hfour hcase
        exact hsmall 2 3 (by linarith)
      · rw [show pairPartner (1 : Player) = 0 from rfl] at hfour hcase
        exact hsmall 2 3 (by linarith)
      · rw [show pairPartner (2 : Player) = 3 from rfl] at hfour hcase
        exact hsmall 0 1 (by linarith)
      · rw [show pairPartner (3 : Player) = 2 from rfl] at hfour hcase
        exact hsmall 0 1 (by linarith)
    obtain ⟨who, hwho⟩ := hpick
    exact hgap who hwho

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

/-- **The refusal gain is a terminal gain.**  The best-reply value exceeds the
on-path payoff by at least the refusal gain at the opening phase. -/
theorem terminalPayoff_add_refusalGain_le_bestReplyValue {m : ℕ} [NeZero m]
    (w : Fin m → Player) (hazard : Fin m → ℝ)
    (h0 : ∀ k, 0 ≤ hazard k) (h1 : ∀ k, hazard k ≤ 1) (who : Player) :
    quittingTerminalPayoff boundaryReward
        (quittingAnchoredCyclicProfile boundaryReward w hazard h0 h1) who +
        refusalGain w hazard h0 h1 who (quittingAnchoredCyclicStart m) ≤
      quittingBestReplyValue boundaryReward
        (quittingAnchoredCyclicProfile boundaryReward w hazard h0 h1) who := by
  have hle := quittingAnchoredCyclicOnPathValue_refusalHazard_le_bestReplyValue
    boundaryReward w hazard h0 h1 who
  rw [quittingTerminalPayoff_anchoredCyclicProfile]
  unfold refusalGain
  linarith

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

/-- **The telescoped identity in divided form.**  Whenever the refuser's
absence does not survive a whole cycle, the refusal gain at a phase is the
accumulated own-phase drift over that cycle divided by the absorption
deficit. -/
theorem refusalGain_eq_drift_div {m : ℕ} (w : Fin m → Player)
    (hazard : Fin m → ℝ) (h0 : ∀ k, 0 ≤ hazard k) (h1 : ∀ k, hazard k ≤ 1)
    (refuser : Player) (phase : Fin m)
    (hW : refusalWeight w hazard refuser phase m ≠ 1) :
    refusalGain w hazard h0 h1 refuser phase =
      refusalDrift w hazard h0 h1 refuser phase m /
        (1 - refusalWeight w hazard refuser phase m) := by
  have hne : (1 : ℝ) - refusalWeight w hazard refuser phase m ≠ 0 :=
    fun h ↦ hW (by linarith)
  rw [eq_div_iff hne]
  exact refusalGain_mul_one_sub_weight w hazard h0 h1 refuser phase

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

/-! ## The uniform four-cycle

The schedule `0, 1, 2, 3` of period four carrying one common interior hazard
`p` is the smallest schedule visiting every player.  Writing `q = 1 - p`, the
renewal system solves in closed form: the opening on-path value of player `0`
is `(1 + 4 * q) / (1 + q + q ^ 2 + q ^ 3)` and its refusal value is
`4 / (1 + q + q ^ 2)`, because refusal deletes exactly one of the four exits
of the cycle.  Their difference is at least `1 / 12` and at most
`1 / 12 + 6 * p`, so on this family the refusal deviation delivers `1 / 12` and
nothing beyond it.
-/

/-- The scalar bound behind the uniform four-cycle gap: with `q` in the unit
interval, `4 / (1 + q + q ^ 2) - (1 + 4 * q) / (1 + q + q ^ 2 + q ^ 3)` is at
least `1 / 12`, with equality only at `q = 1`. -/
theorem twelfth_le_sub_of_fourCycleValues {q refusal onPath : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hrefusal : refusal * (1 + q + q ^ 2) = 4)
    (honPath : onPath * (1 + q + q ^ 2 + q ^ 3) = 1 + 4 * q) :
    1 / 12 ≤ refusal - onPath := by
  have hA : (0 : ℝ) < 1 + q + q ^ 2 := by nlinarith [sq_nonneg q]
  have hB : (0 : ℝ) < 1 + q + q ^ 2 + q ^ 3 := by
    nlinarith [sq_nonneg q, pow_nonneg hq0 3]
  have key : (refusal - onPath - 1 / 12) *
      (12 * ((1 + q + q ^ 2) * (1 + q + q ^ 2 + q ^ 3))) =
      (1 - q) * (35 + 21 * q + 6 * q ^ 2 + 3 * q ^ 3 + q ^ 4) := by
    linear_combination (12 * (1 + q + q ^ 2 + q ^ 3)) * hrefusal -
      (12 * (1 + q + q ^ 2)) * honPath
  have hnum : 0 ≤ (1 - q) * (35 + 21 * q + 6 * q ^ 2 + 3 * q ^ 3 + q ^ 4) :=
    mul_nonneg (by linarith)
      (by nlinarith [pow_nonneg hq0 2, pow_nonneg hq0 3, pow_nonneg hq0 4])
  nlinarith [key, hnum, mul_pos hA hB]

/-- The matching upper bound: on the uniform four-cycle the refusal gain
exceeds `1 / 12` by at most `6 * (1 - q)`, so it tends to `1 / 12` as the
hazard tends to zero. -/
theorem sub_le_twelfth_add_of_fourCycleValues {q refusal onPath : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hrefusal : refusal * (1 + q + q ^ 2) = 4)
    (honPath : onPath * (1 + q + q ^ 2 + q ^ 3) = 1 + 4 * q) :
    refusal - onPath ≤ 1 / 12 + 6 * (1 - q) := by
  have hq2 : q ^ 2 ≤ 1 := by nlinarith
  have hq3 : q ^ 3 ≤ 1 := by nlinarith
  have hq4 : q ^ 4 ≤ 1 := by nlinarith
  have hA1 : (1 : ℝ) ≤ 1 + q + q ^ 2 := by nlinarith [sq_nonneg q]
  have hB1 : (1 : ℝ) ≤ 1 + q + q ^ 2 + q ^ 3 := by
    nlinarith [sq_nonneg q, pow_nonneg hq0 3]
  have hAB : (1 : ℝ) ≤ (1 + q + q ^ 2) * (1 + q + q ^ 2 + q ^ 3) := by nlinarith
  have hc : (0 : ℝ) < 12 * ((1 + q + q ^ 2) * (1 + q + q ^ 2 + q ^ 3)) := by
    linarith
  have key : (refusal - onPath - 1 / 12) *
      (12 * ((1 + q + q ^ 2) * (1 + q + q ^ 2 + q ^ 3))) =
      (1 - q) * (35 + 21 * q + 6 * q ^ 2 + 3 * q ^ 3 + q ^ 4) := by
    linear_combination (12 * (1 + q + q ^ 2 + q ^ 3)) * hrefusal -
      (12 * (1 + q + q ^ 2)) * honPath
  have hfac : 0 ≤ (1 - q) *
      (72 * ((1 + q + q ^ 2) * (1 + q + q ^ 2 + q ^ 3)) -
        (35 + 21 * q + 6 * q ^ 2 + 3 * q ^ 3 + q ^ 4)) :=
    mul_nonneg (by linarith) (by linarith)
  have hle : (refusal - onPath - 1 / 12) *
      (12 * ((1 + q + q ^ 2) * (1 + q + q ^ 2 + q ^ 3))) ≤
      (6 * (1 - q)) * (12 * ((1 + q + q ^ 2) * (1 + q + q ^ 2 + q ^ 3))) := by
    rw [key]
    nlinarith [hfac]
  have := le_of_mul_le_mul_right hle hc
  linarith

/-- **The uniform four-cycle on-path value.**  Player `0`'s opening on-path
value against the period-four schedule `0, 1, 2, 3` at common hazard `p`. -/
theorem uniformFourCycleOnPathValue {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) :
    quittingAnchoredCyclicOnPathValue boundaryReward (id : Fin 4 → Player)
        (fun _ ↦ p) (fun _ ↦ hp0.le) (fun _ ↦ hp1) 0 0 *
      (1 + (1 - p) + (1 - p) ^ 2 + (1 - p) ^ 3) = 1 + 4 * (1 - p) := by
  have hren : ∀ k : Fin 4,
      quittingAnchoredCyclicOnPathValue boundaryReward (id : Fin 4 → Player)
          (fun _ ↦ p) (fun _ ↦ hp0.le) (fun _ ↦ hp1) k 0 =
        p * boundaryReward (quittingSingletonTerminal (id k)) 0 +
          (1 - p) * quittingAnchoredCyclicOnPathValue boundaryReward
            (id : Fin 4 → Player) (fun _ ↦ p) (fun _ ↦ hp0.le) (fun _ ↦ hp1)
            (finRotate 4 k) 0 :=
    fun k ↦ quittingAnchoredCyclicOnPathValue_renewal boundaryReward _ _ _ _ k 0
  have e0 := hren 0
  have e1 := hren 1
  have e2 := hren 2
  have e3 := hren 3
  simp only [id_eq] at e0 e1 e2 e3
  rw [show finRotate 4 (0 : Fin 4) = 1 from by decide,
    show boundaryReward (quittingSingletonTerminal (0 : Player)) 0 = 1 from rfl]
    at e0
  rw [show finRotate 4 (1 : Fin 4) = 2 from by decide,
    show boundaryReward (quittingSingletonTerminal (1 : Player)) 0 = 4 from rfl]
    at e1
  rw [show finRotate 4 (2 : Fin 4) = 3 from by decide,
    show boundaryReward (quittingSingletonTerminal (2 : Player)) 0 = 0 from rfl]
    at e2
  rw [show finRotate 4 (3 : Fin 4) = 0 from by decide,
    show boundaryReward (quittingSingletonTerminal (3 : Player)) 0 = 0 from rfl]
    at e3
  refine mul_left_cancel₀ (ne_of_gt hp0) ?_
  linear_combination e0 + (1 - p) * e1 + (1 - p) ^ 2 * e2 + (1 - p) ^ 3 * e3

/-- **The uniform four-cycle refusal value.**  Refusing to quit deletes the
single exit that player `0` owns, leaving a three-exit cycle. -/
theorem uniformFourCycleRefusalValue {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) :
    quittingAnchoredCyclicOnPathValue boundaryReward (id : Fin 4 → Player)
        (quittingAnchoredCyclicRefusalHazard (id : Fin 4 → Player) (fun _ ↦ p) 0)
        (quittingAnchoredCyclicRefusalHazard_nonneg (fun _ ↦ hp0.le) _ 0)
        (quittingAnchoredCyclicRefusalHazard_le_one (fun _ ↦ hp1) _ 0) 0 0 *
      (1 + (1 - p) + (1 - p) ^ 2) = 4 := by
  have hren : ∀ k : Fin 4,
      quittingAnchoredCyclicOnPathValue boundaryReward (id : Fin 4 → Player)
          (quittingAnchoredCyclicRefusalHazard (id : Fin 4 → Player)
            (fun _ ↦ p) 0)
          (quittingAnchoredCyclicRefusalHazard_nonneg (fun _ ↦ hp0.le) _ 0)
          (quittingAnchoredCyclicRefusalHazard_le_one (fun _ ↦ hp1) _ 0) k 0 =
        quittingAnchoredCyclicRefusalHazard (id : Fin 4 → Player)
              (fun _ ↦ p) 0 k *
            boundaryReward (quittingSingletonTerminal (id k)) 0 +
          (1 - quittingAnchoredCyclicRefusalHazard (id : Fin 4 → Player)
              (fun _ ↦ p) 0 k) *
            quittingAnchoredCyclicOnPathValue boundaryReward
              (id : Fin 4 → Player)
              (quittingAnchoredCyclicRefusalHazard (id : Fin 4 → Player)
                (fun _ ↦ p) 0)
              (quittingAnchoredCyclicRefusalHazard_nonneg (fun _ ↦ hp0.le) _ 0)
              (quittingAnchoredCyclicRefusalHazard_le_one (fun _ ↦ hp1) _ 0)
              (finRotate 4 k) 0 :=
    fun k ↦ quittingAnchoredCyclicOnPathValue_renewal boundaryReward _ _ _ _ k 0
  have hz : ∀ k : Fin 4, k ≠ 0 →
      quittingAnchoredCyclicRefusalHazard (id : Fin 4 → Player)
        (fun _ ↦ p) 0 k = p := by
    intro k hk
    unfold quittingAnchoredCyclicRefusalHazard
    simp only [id_eq]
    rw [if_neg hk]
  have hz0 : quittingAnchoredCyclicRefusalHazard (id : Fin 4 → Player)
      (fun _ ↦ p) 0 0 = 0 := by
    unfold quittingAnchoredCyclicRefusalHazard
    rw [if_pos (show id (0 : Fin 4) = 0 from rfl)]
  have e0 := hren 0
  have e1 := hren 1
  have e2 := hren 2
  have e3 := hren 3
  simp only [id_eq] at e0 e1 e2 e3
  rw [hz0, show finRotate 4 (0 : Fin 4) = 1 from by decide] at e0
  rw [hz 1 (by decide), show finRotate 4 (1 : Fin 4) = 2 from by decide,
    show boundaryReward (quittingSingletonTerminal (1 : Player)) 0 = 4 from rfl]
    at e1
  rw [hz 2 (by decide), show finRotate 4 (2 : Fin 4) = 3 from by decide,
    show boundaryReward (quittingSingletonTerminal (2 : Player)) 0 = 0 from rfl]
    at e2
  rw [hz 3 (by decide), show finRotate 4 (3 : Fin 4) = 0 from by decide,
    show boundaryReward (quittingSingletonTerminal (3 : Player)) 0 = 0 from rfl]
    at e3
  refine mul_left_cancel₀ (ne_of_gt hp0) ?_
  linear_combination e0 + e1 + (1 - p) * e2 + (1 - p) ^ 2 * e3

/-- **A checked terminal gap on the uniform four-cycle.**  Against the
period-four schedule `0, 1, 2, 3` at any common interior hazard, player `0`'s
best-reply value exceeds its on-path payoff by at least `1 / 12`. -/
theorem twelfth_le_bestReplyValue_sub_terminalPayoff_uniformFourCycle
    {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) :
    quittingTerminalPayoff boundaryReward
        (quittingAnchoredCyclicProfile boundaryReward (id : Fin 4 → Player)
          (fun _ ↦ p) (fun _ ↦ hp0.le) (fun _ ↦ hp1)) 0 + 1 / 12 ≤
      quittingBestReplyValue boundaryReward
        (quittingAnchoredCyclicProfile boundaryReward (id : Fin 4 → Player)
          (fun _ ↦ p) (fun _ ↦ hp0.le) (fun _ ↦ hp1)) 0 := by
  have hle := quittingAnchoredCyclicOnPathValue_refusalHazard_le_bestReplyValue
    boundaryReward (id : Fin 4 → Player) (fun _ ↦ p) (fun _ ↦ hp0.le)
    (fun _ ↦ hp1) 0
  rw [show quittingAnchoredCyclicStart 4 = (0 : Fin 4) from rfl] at hle
  have hgap := twelfth_le_sub_of_fourCycleValues (q := 1 - p) (by linarith)
    (by linarith) (uniformFourCycleRefusalValue hp0 hp1)
    (uniformFourCycleOnPathValue hp0 hp1)
  rw [quittingTerminalPayoff_anchoredCyclicProfile,
    show quittingAnchoredCyclicStart 4 = (0 : Fin 4) from rfl]
  linarith

/-- **The uniform four-cycle does not beat `1 / 12` by refusal.**  Player `0`'s
refusal gain on the four-cycle exceeds `1 / 12` by at most `6 * p`, so the
constant `1 / 12` is the best one the refusal deviation delivers uniformly over
this family. -/
theorem uniformFourCycleRefusalGain_le {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) :
    quittingAnchoredCyclicOnPathValue boundaryReward (id : Fin 4 → Player)
        (quittingAnchoredCyclicRefusalHazard (id : Fin 4 → Player) (fun _ ↦ p) 0)
        (quittingAnchoredCyclicRefusalHazard_nonneg (fun _ ↦ hp0.le) _ 0)
        (quittingAnchoredCyclicRefusalHazard_le_one (fun _ ↦ hp1) _ 0) 0 0 -
      quittingAnchoredCyclicOnPathValue boundaryReward (id : Fin 4 → Player)
        (fun _ ↦ p) (fun _ ↦ hp0.le) (fun _ ↦ hp1) 0 0 ≤ 1 / 12 + 6 * p := by
  have h := sub_le_twelfth_add_of_fourCycleValues (q := 1 - p) (by linarith)
    (by linarith) (uniformFourCycleRefusalValue hp0 hp1)
    (uniformFourCycleOnPathValue hp0 hp1)
  linarith

/-! ## Quitting now and refusing are not enough

The two deviations this module evaluates in closed form — quitting at the
opening phase, worth exactly `1`, and refusing forever, worth the zeroed
on-path value — do not between them certify the constant `1 / 12`.  The
period-five schedule `0, 2, 3, 2, 1` at hazards `1/4, 1/2, 1/3, 1/4, 1` has
opening on-path values `1, 19/16, 15/16, 15/8` and refusal values
`1, 16/13, 1, 15/8`, so every quit-now gain and every refusal gain is at most
`1 / 16`.  Any proof of `HasUniformSoloPeriodicTerminalGap` therefore has to
use the intermediate stops of `quittingPeriodicWindowBestPhaseStop` as well.
-/

/-- **One turn of a period-five cycle**, with the hazards and the singleton
rows read off by the supplied equations. -/
theorem onPathValue_five_turn (w : Fin 5 → Player) (hazard : Fin 5 → ℝ)
    (h0 : ∀ k, 0 ≤ hazard k) (h1 : ∀ k, hazard k ≤ 1) (who : Player)
    {p₀ p₁ p₂ p₃ p₄ a₀ a₁ a₂ a₃ a₄ : ℝ}
    (hp₀ : hazard 0 = p₀) (hp₁ : hazard 1 = p₁) (hp₂ : hazard 2 = p₂)
    (hp₃ : hazard 3 = p₃) (hp₄ : hazard 4 = p₄)
    (ha₀ : boundaryReward (quittingSingletonTerminal (w 0)) who = a₀)
    (ha₁ : boundaryReward (quittingSingletonTerminal (w 1)) who = a₁)
    (ha₂ : boundaryReward (quittingSingletonTerminal (w 2)) who = a₂)
    (ha₃ : boundaryReward (quittingSingletonTerminal (w 3)) who = a₃)
    (ha₄ : boundaryReward (quittingSingletonTerminal (w 4)) who = a₄) :
    quittingAnchoredCyclicOnPathValue boundaryReward w hazard h0 h1 0 who *
        (1 - (1 - p₀) * (1 - p₁) * (1 - p₂) * (1 - p₃) * (1 - p₄)) =
      p₀ * a₀ + (1 - p₀) * p₁ * a₁ + (1 - p₀) * (1 - p₁) * p₂ * a₂ +
        (1 - p₀) * (1 - p₁) * (1 - p₂) * p₃ * a₃ +
        (1 - p₀) * (1 - p₁) * (1 - p₂) * (1 - p₃) * p₄ * a₄ := by
  subst hp₀; subst hp₁; subst hp₂; subst hp₃; subst hp₄
  subst ha₀; subst ha₁; subst ha₂; subst ha₃; subst ha₄
  have hren : ∀ k : Fin 5,
      quittingAnchoredCyclicOnPathValue boundaryReward w hazard h0 h1 k who =
        hazard k * boundaryReward (quittingSingletonTerminal (w k)) who +
          (1 - hazard k) * quittingAnchoredCyclicOnPathValue boundaryReward w
            hazard h0 h1 (finRotate 5 k) who :=
    fun k ↦ quittingAnchoredCyclicOnPathValue_renewal boundaryReward w hazard
      h0 h1 k who
  have e0 := hren 0
  have e1 := hren 1
  have e2 := hren 2
  have e3 := hren 3
  have e4 := hren 4
  rw [show finRotate 5 (0 : Fin 5) = 1 from by decide] at e0
  rw [show finRotate 5 (1 : Fin 5) = 2 from by decide] at e1
  rw [show finRotate 5 (2 : Fin 5) = 3 from by decide] at e2
  rw [show finRotate 5 (3 : Fin 5) = 4 from by decide] at e3
  rw [show finRotate 5 (4 : Fin 5) = 0 from by decide] at e4
  linear_combination e0 + (1 - hazard 0) * e1 +
    (1 - hazard 0) * (1 - hazard 1) * e2 +
    (1 - hazard 0) * (1 - hazard 1) * (1 - hazard 2) * e3 +
    (1 - hazard 0) * (1 - hazard 1) * (1 - hazard 2) * (1 - hazard 3) * e4

/-- The period-five schedule on which quitting now and refusing both fall
short of `1 / 12`. -/
def shortfallSchedule : Fin 5 → Player := ![0, 2, 3, 2, 1]

/-- The hazards accompanying `shortfallSchedule`. -/
def shortfallHazard : Fin 5 → ℝ := ![1 / 4, 1 / 2, 1 / 3, 1 / 4, 1]

theorem shortfallHazard_pos : ∀ k, 0 < shortfallHazard k := by
  intro k
  fin_cases k <;> norm_num [shortfallHazard]

theorem shortfallHazard_nonneg : ∀ k, 0 ≤ shortfallHazard k :=
  fun k ↦ (shortfallHazard_pos k).le

theorem shortfallHazard_le_one : ∀ k, shortfallHazard k ≤ 1 := by
  intro k
  fin_cases k <;> norm_num [shortfallHazard]

/-- The singleton rows visited by `shortfallSchedule`. -/
theorem shortfallReward (k : Fin 5) (who : Player) :
    boundaryReward (quittingSingletonTerminal (shortfallSchedule k)) who =
      ![![1, 4, 0, 0], ![0, 0, 1, 4], ![0, 0, 4, 1], ![0, 0, 1, 4],
        ![4, 1, 0, 0]] k who := by
  fin_cases k <;> fin_cases who <;> rfl

/-- The four hazard vectors seen by the four refusers on
`shortfallSchedule`. -/
theorem shortfallRefusalHazard (who : Player) (k : Fin 5) :
    quittingAnchoredCyclicRefusalHazard shortfallSchedule shortfallHazard who
        k =
      ![![0, 1 / 2, 1 / 3, 1 / 4, 1], ![1 / 4, 1 / 2, 1 / 3, 1 / 4, 0],
        ![1 / 4, 0, 1 / 3, 0, 1], ![1 / 4, 1 / 2, 0, 1 / 4, 1]] who k := by
  fin_cases who <;> fin_cases k <;> rfl

/-- The four opening on-path values of `shortfallSchedule`: `1`, `19/16`,
`15/16` and `15/8`, summing to `5`. -/
theorem shortfallOnPathValue (who : Player) :
    quittingAnchoredCyclicOnPathValue boundaryReward shortfallSchedule
        shortfallHazard shortfallHazard_nonneg shortfallHazard_le_one 0 who =
      ![1, 19 / 16, 15 / 16, 15 / 8] who := by
  have q0 : shortfallHazard 0 = 1 / 4 := rfl
  have q1 : shortfallHazard 1 = 1 / 2 := rfl
  have q2 : shortfallHazard 2 = 1 / 3 := rfl
  have q3 : shortfallHazard 3 = 1 / 4 := rfl
  have q4 : shortfallHazard 4 = 1 := rfl
  have h := onPathValue_five_turn shortfallSchedule shortfallHazard
    shortfallHazard_nonneg shortfallHazard_le_one who q0 q1 q2 q3 q4
    (shortfallReward 0 who) (shortfallReward 1 who) (shortfallReward 2 who)
    (shortfallReward 3 who) (shortfallReward 4 who)
  rcases player_eq who with rfl | rfl | rfl | rfl <;>
    norm_num [Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons] at h ⊢ <;>
    linarith

/-- The four refusal values of `shortfallSchedule`: `1`, `16/13`, `1` and
`15/8`. -/
theorem shortfallRefusalValue (who : Player) :
    quittingAnchoredCyclicOnPathValue boundaryReward shortfallSchedule
        (quittingAnchoredCyclicRefusalHazard shortfallSchedule shortfallHazard
          who)
        (quittingAnchoredCyclicRefusalHazard_nonneg shortfallHazard_nonneg
          shortfallSchedule who)
        (quittingAnchoredCyclicRefusalHazard_le_one shortfallHazard_le_one
          shortfallSchedule who) 0 who =
      ![1, 16 / 13, 1, 15 / 8] who := by
  have h := onPathValue_five_turn shortfallSchedule
    (quittingAnchoredCyclicRefusalHazard shortfallSchedule shortfallHazard who)
    (quittingAnchoredCyclicRefusalHazard_nonneg shortfallHazard_nonneg _ who)
    (quittingAnchoredCyclicRefusalHazard_le_one shortfallHazard_le_one _ who)
    who (shortfallRefusalHazard who 0) (shortfallRefusalHazard who 1)
    (shortfallRefusalHazard who 2) (shortfallRefusalHazard who 3)
    (shortfallRefusalHazard who 4) (shortfallReward 0 who)
    (shortfallReward 1 who) (shortfallReward 2 who) (shortfallReward 3 who)
    (shortfallReward 4 who)
  rcases player_eq who with rfl | rfl | rfl | rfl <;>
    norm_num [Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons] at h ⊢ <;>
    linarith

/-- **Quitting now and refusing do not deliver `1 / 12`.**  On
`shortfallSchedule` no player's quit-now value or refusal value beats its
opening on-path value by `1 / 12`, so those two deviations alone cannot prove
`HasUniformSoloPeriodicTerminalGap`. -/
theorem not_forall_exists_quitValue_or_refusalValue_gap :
    ¬ ∀ (m : ℕ) (_ : NeZero m) (w : Fin m → Player) (hazard : Fin m → ℝ)
        (h0 : ∀ k, 0 ≤ hazard k) (h1 : ∀ k, hazard k ≤ 1),
        (∀ k, 0 < hazard k) →
          ∃ who : Player,
            quittingAnchoredCyclicOnPathValue boundaryReward w hazard h0 h1
                  (quittingAnchoredCyclicStart m) who + 1 / 12 ≤ 1 ∨
              quittingAnchoredCyclicOnPathValue boundaryReward w hazard h0 h1
                    (quittingAnchoredCyclicStart m) who + 1 / 12 ≤
                quittingAnchoredCyclicOnPathValue boundaryReward w
                  (quittingAnchoredCyclicRefusalHazard w hazard who)
                  (quittingAnchoredCyclicRefusalHazard_nonneg h0 w who)
                  (quittingAnchoredCyclicRefusalHazard_le_one h1 w who)
                  (quittingAnchoredCyclicStart m) who := by
  intro hall
  obtain ⟨who, hwho⟩ := hall 5 (by infer_instance) shortfallSchedule
    shortfallHazard shortfallHazard_nonneg shortfallHazard_le_one
    shortfallHazard_pos
  rw [show quittingAnchoredCyclicStart 5 = (0 : Fin 5) from rfl,
    shortfallOnPathValue who, shortfallRefusalValue who] at hwho
  rcases player_eq who with rfl | rfl | rfl | rfl <;>
    rcases hwho with h | h <;>
    norm_num [Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
      Matrix.tail_cons] at h

/-! ## The residual

Two of the three ingredients of the uniform statement are checked above.
Schedules omitting some player are settled at the stated constant by
`exists_terminalPayoff_add_twelfth_le_bestReplyValue_of_forall_ne`, and the
smallest schedule omitting none — the uniform four-cycle — is settled by
`twelfth_le_bestReplyValue_sub_terminalPayoff_uniformFourCycle`.  What remains
open is the general schedule visiting every player, stated as
`HasSurjectiveSoloPeriodicTerminalGap`; the reduction
`hasUniformSoloPeriodicTerminalGap_of_surjective` shows that it is the whole
residual.

The general case needs a deviation this module does not evaluate.  Bounding the
accumulated own-phase drift of `refusalDrift` against the absorption deficit
`1 - refusalWeight` in `refusalGain_mul_one_sub_weight` bounds the refusal gain
and nothing else, and `not_forall_exists_quitValue_or_refusalValue_gap` exhibits
a period-five schedule on which the refusal gain and the quit-now gain are both
at most `1 / 16`.  The remaining deviations are the intermediate stops of
`quittingPeriodicWindowBestPhaseStop`, which pay `1` at the phase reached and
so read the on-path value at phases other than the opening one.
-/

/-- The uniform terminal gap for solo-periodic profiles on the Solan–Vieille
table: some player's best-reply value exceeds its on-path value by at least
`1 / 12`, for every period, every schedule with repetitions and every family
of interior hazards.  No larger constant is delivered by the refusal
deviation: on the uniform four-cycle `uniformFourCycleRefusalGain_le` caps the
refusal gain by `1 / 12 + 6 * p`. -/
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

/-- The same gap restricted to schedules designating every player at least
once.  This is the residual of `HasUniformSoloPeriodicTerminalGap`: the
schedules omitting a player are already checked. -/
def HasSurjectiveSoloPeriodicTerminalGap : Prop :=
  ∀ (m : ℕ) (_ : NeZero m) (w : Fin m → Player) (hazard : Fin m → ℝ)
    (h0 : ∀ k, 0 ≤ hazard k) (h1 : ∀ k, hazard k ≤ 1),
    (∀ k, 0 < hazard k) → (∀ z : Player, ∃ k, w k = z) →
      ∃ who : Player,
        quittingTerminalPayoff boundaryReward
            (quittingAnchoredCyclicProfile boundaryReward w hazard h0 h1) who +
            1 / 12 ≤
          quittingBestReplyValue boundaryReward
            (quittingAnchoredCyclicProfile boundaryReward w hazard h0 h1) who

/-- **The residual is exactly the schedules visiting every player.**  A
schedule omitting one is settled by
`exists_terminalPayoff_add_twelfth_le_bestReplyValue_of_forall_ne`. -/
theorem hasUniformSoloPeriodicTerminalGap_of_surjective
    (hgap : HasSurjectiveSoloPeriodicTerminalGap) :
    HasUniformSoloPeriodicTerminalGap := by
  intro m hm w hazard h0 h1 hpos
  haveI := hm
  by_cases hsurj : ∀ z : Player, ∃ k, w k = z
  · exact hgap m hm w hazard h0 h1 hpos hsurj
  · push Not at hsurj
    obtain ⟨absent, hmiss⟩ := hsurj
    exact exists_terminalPayoff_add_twelfth_le_bestReplyValue_of_forall_ne w
      hazard h0 h1 hpos hmiss

end SolanVieilleBoundary

end GameTheory
