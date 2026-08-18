/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.AffineIterateTelescope
import MathUE.CyclicContraction
import MathUE.Finset.MinimalMemberSum
import Research.Quitting.AnchoredCyclicRenewal
import Research.Quitting.AnchoredCyclicScreen
import Research.Quitting.SolanVieilleSoloPeriodicGap
import UniformEquilibrium.Quitting.Cycles.SingletonArcCycle
import UniformEquilibrium.Quitting.Examples.SolanVieilleBoundarySoloPeriodicNoGo

/-!
# Terminal-level exploitability of solo-periodic profiles on the Solan–Vieille table

`SolanVieilleSoloPeriodicGap` bounds the accuracy of the one-stage anchored
system.  This module works at the terminal-payoff level instead, where the
bound is on the actual best-reply value of the induced behavior profile, and it
settles the terminal-gap constant `1 / 12` negatively.

Two facts drive the positive results.  Quitting at the opening phase pays
*exactly* `1` to every player against every solo-periodic profile, whatever the
schedule and the hazards (`quittingAnchoredCyclicQuitValue_eq_one`): every solo
exit pays its owner `1` and every two-player exit pays each of its two members
`1`.  And the four on-path values always sum to `5`
(`sum_onPathValue_eq_five`), because each solo exit distributes a total of
`1 + 4 + 0 + 0` across the four players.  Together these give
`one_le_quittingBestReplyValue_anchoredCyclicProfile`: the best-reply value is
at least `1` for every player, so a player whose on-path value falls below `1`
is exploitable by the shortfall.

The other deviation is refusal, which faces the same schedule with the
refuser's own phases carrying hazard zero.  It is available to the deviator
(`quittingAnchoredCyclicOnPathValue_refusalHazard_le_bestReplyValue`), its gain
is a terminal gain (`terminalPayoff_add_refusalGain_le_bestReplyValue`), and
once it dominates the quit-now value `1` at every phase it solves the
max-linear response recursion, so the whole behavioral supremum collapses onto
it (`quittingBestReplyValue_eq_refusalOnPathValue`).  Around one cycle the
refusal gain is the accumulated own-phase drift divided by the absorption
deficit (`refusalGain_eq_drift_div`), and dominates that drift whenever the
refuser's on-path value never falls below the quit-now value `1`
(`refusalDrift_le_refusalGain`).  Exactness of the one-stage anchored system
is one source of that floor
(`refusalDrift_le_refusalGain_of_isExactAnchoredSoloPeriodic`).

What holds for the class: a schedule omitting some player pays that player
exactly four times what it pays the player's own pair partner
(`onPathValue_eq_four_mul_of_forall_ne`), which with the sum identity forces a
gap of `1 / 12`
(`exists_terminalPayoff_add_twelfth_le_bestReplyValue_of_forall_ne`); a
schedule paying some player nothing at all forces the full gap `1`.

What fails is the constant itself.  `refutingSchedule` is a period-four
schedule designating every player, at interior hazards, on which every player's
best-reply value is its refusal value and every gap is strictly below `1 / 12`:
`not_hasSurjectiveSoloPeriodicTerminalGap` and
`not_hasUniformSoloPeriodicTerminalGap`.

Where the constant came from is recorded by the uniform four-cycle — period
four, the schedule `0, 1, 2, 3`, one common interior hazard `p` — whose renewal
system solves explicitly: the terminal gap there is at least `1 / 12`
(`twelfth_le_bestReplyValue_sub_terminalPayoff_uniformFourCycle`) and the
refusal gain at most `1 / 12 + 6 * p` (`uniformFourCycleRefusalGain_le`).  That
pair calibrates the constant on one family as its hazard tends to zero; it is
not uniform over schedules.
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
hazard: every solo exit pays its owner `1` and every two-player exit pays each
of its two members `1`. -/
theorem quittingAnchoredCyclicQuitValue_eq_one {m : ℕ}
    (w : Fin m → Player) (hazard : Fin m → ℝ) (phase : Fin m) (who : Player) :
    quittingAnchoredCyclicQuitValue boundaryReward w hazard phase who = 1 :=
  quittingAnchoredCyclicQuitValue_eq_of_flatQuitRow boundaryReward w hazard phase
    (soloReward_self who) fun _ ↦ boundaryReward_pair_eq_one (w phase) who

/-- Every player's best-reply value against a solo-periodic profile is at
least `1`. -/
theorem one_le_quittingBestReplyValue_anchoredCyclicProfile {m : ℕ} [NeZero m]
    (w : Fin m → Player) (hazard : Fin m → ℝ)
    (h0 : ∀ k, 0 ≤ hazard k) (h1 : ∀ k, hazard k ≤ 1) (who : Player) :
    1 ≤ quittingBestReplyValue boundaryReward
      (quittingAnchoredCyclicProfile boundaryReward w hazard h0 h1) who :=
  le_quittingBestReplyValue_of_flatQuitRow boundaryReward w hazard h0 h1
    (soloReward_self who)
    fun _ ↦ boundaryReward_pair_eq_one (w (quittingAnchoredCyclicStart m)) who

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
solo-periodic profile sum to `5` at every phase, as soon as one phase of the
cycle carries a positive hazard. -/
theorem sum_onPathValue_eq_five {m : ℕ} [NeZero m]
    (w : Fin m → Player) (hazard : Fin m → ℝ)
    (h0 : ∀ k, 0 ≤ hazard k) (h1 : ∀ k, hazard k ≤ 1)
    (hsome : ∃ k, 0 < hazard k) (phase : Fin m) :
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
  obtain ⟨positive, hpositive⟩ := hsome
  have hzero : D phase = 0 :=
    Math.eq_zero_of_eq_mul_finRotate (c := fun k ↦ 1 - hazard k)
      (fun k ↦ by linarith [h1 k]) (fun k ↦ by linarith [h0 k])
      ⟨positive, by linarith⟩ hstep phase
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
  classical
  set U := quittingAnchoredCyclicOnPathValue boundaryReward w hazard h0 h1 phase
    with hU
  obtain ⟨who, hwho⟩ := Math.Finset.exists_nsmul_le_forall_sum
    (size := 2)
    (parts := fun side : Bool ↦ if side then ({0, 1} : Finset Player) else {2, 3})
    (by decide) (by decide) U
  have htrue := hwho true
  have hfalse := hwho false
  rw [if_pos rfl, Finset.sum_pair (by decide), two_nsmul] at htrue
  rw [if_neg Bool.false_ne_true, Finset.sum_pair (by decide), two_nsmul] at hfalse
  exact ⟨who, le_min (by linarith) (by linarith)⟩

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
    (hsome : ∃ k, 0 < hazard k) (phase : Fin m) :
    ∃ who : Player,
      quittingAnchoredCyclicOnPathValue boundaryReward w hazard h0 h1
        phase who ≤ 5 / 4 := by
  obtain ⟨who, hwho⟩ := exists_onPathValue_le_half_min_pairSum w hazard h0 h1 phase
  have hsum := sum_onPathValue_eq_five w hazard h0 h1 hsome phase
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
    (h0 : ∀ k, 0 ≤ hazard k) (h1 : ∀ k, hazard k ≤ 1)
    (hsome : ∃ k, 0 < hazard k)
    {absent partner : Player} (hpair : absent.val / 2 = partner.val / 2)
    (hne : absent ≠ partner) (hmiss : ∀ k, w k ≠ absent) (phase : Fin m) :
    quittingAnchoredCyclicOnPathValue boundaryReward w hazard h0 h1 phase absent =
      4 * quittingAnchoredCyclicOnPathValue boundaryReward w hazard h0 h1 phase
        partner := by
  set U := quittingAnchoredCyclicOnPathValue boundaryReward w hazard h0 h1 with hU
  obtain ⟨positive, hpositive⟩ := hsome
  have hzero : ∀ k : Fin m, U k absent - 4 * U k partner = 0 := by
    refine Math.eq_zero_of_eq_mul_finRotate (c := fun k ↦ 1 - hazard k)
      (fun k ↦ by linarith [h1 k]) (fun k ↦ by linarith [h0 k])
      ⟨positive, by linarith⟩ (fun k ↦ ?_)
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
    (h0 : ∀ k, 0 ≤ hazard k) (h1 : ∀ k, hazard k ≤ 1)
    (hsome : ∃ k, 0 < hazard k) {who : Player}
    (hzero : ∀ k, boundaryReward (quittingSingletonTerminal (w k)) who = 0)
    (phase : Fin m) :
    quittingAnchoredCyclicOnPathValue boundaryReward w hazard h0 h1 phase who =
      0 := by
  obtain ⟨positive, hpositive⟩ := hsome
  refine Math.eq_zero_of_eq_mul_finRotate (c := fun k ↦ 1 - hazard k)
    (fun k ↦ by linarith [h1 k]) (fun k ↦ by linarith [h0 k])
    ⟨positive, by linarith⟩
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
    (h0 : ∀ k, 0 ≤ hazard k) (h1 : ∀ k, hazard k ≤ 1)
    (hsome : ∃ k, 0 < hazard k) {who : Player}
    (hzero : ∀ k, boundaryReward (quittingSingletonTerminal (w k)) who = 0) :
    quittingTerminalPayoff boundaryReward
        (quittingAnchoredCyclicProfile boundaryReward w hazard h0 h1) who + 1 ≤
      quittingBestReplyValue boundaryReward
        (quittingAnchoredCyclicProfile boundaryReward w hazard h0 h1) who := by
  have hbest := one_le_quittingBestReplyValue_anchoredCyclicProfile w hazard h0 h1 who
  rw [quittingTerminalPayoff_anchoredCyclicProfile,
    onPathValue_eq_zero_of_forall_reward_eq_zero w hazard h0 h1 hsome hzero]
  linarith

/-- **Omitting a player already gives the gap.**  If the schedule never
designates some player, then some player's best-reply value exceeds its on-path
value by at least `1 / 12`. -/
theorem exists_terminalPayoff_add_twelfth_le_bestReplyValue_of_forall_ne
    {m : ℕ} [NeZero m] (w : Fin m → Player) (hazard : Fin m → ℝ)
    (h0 : ∀ k, 0 ≤ hazard k) (h1 : ∀ k, hazard k ≤ 1)
    (hsome : ∃ k, 0 < hazard k)
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
  have hfour := onPathValue_eq_four_mul_of_forall_ne w hazard h0 h1 hsome
    (val_div_two_pairPartner absent).symm (Ne.symm (pairPartner_ne absent)) hmiss
    (quittingAnchoredCyclicStart m)
  have hsum := sum_onPathValue_eq_five w hazard h0 h1 hsome
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

/-- **The refusal family solves the response system.**  Quitting pays exactly
`1` at every phase of a solo-periodic profile on this table, so once the
refusal value dominates `1` at every phase it is a fixed point of the
max-linear response recursion `IsAnchoredCyclicResponseSolution`. -/
theorem isAnchoredCyclicResponseSolution_refusalOnPathValue {m : ℕ}
    (w : Fin m → Player) (hazard : Fin m → ℝ)
    (h0 : ∀ k, 0 ≤ hazard k) (h1 : ∀ k, hazard k ≤ 1)
    (hone : ∀ (k : Fin m) (who : Player),
      1 ≤ quittingAnchoredCyclicOnPathValue boundaryReward w
        (quittingAnchoredCyclicRefusalHazard w hazard who)
        (quittingAnchoredCyclicRefusalHazard_nonneg h0 w who)
        (quittingAnchoredCyclicRefusalHazard_le_one h1 w who) k who) :
    IsAnchoredCyclicResponseSolution boundaryReward w hazard
      (fun k who ↦ quittingAnchoredCyclicOnPathValue boundaryReward w
        (quittingAnchoredCyclicRefusalHazard w hazard who)
        (quittingAnchoredCyclicRefusalHazard_nonneg h0 w who)
        (quittingAnchoredCyclicRefusalHazard_le_one h1 w who) k who) := by
  intro phase who
  have hren := quittingAnchoredCyclicOnPathValue_renewal boundaryReward w
    (quittingAnchoredCyclicRefusalHazard w hazard who)
    (quittingAnchoredCyclicRefusalHazard_nonneg h0 w who)
    (quittingAnchoredCyclicRefusalHazard_le_one h1 w who) phase who
  show quittingAnchoredCyclicOnPathValue boundaryReward w _ _ _ phase who = _
  rw [quittingAnchoredCyclicQuitValue_eq_one,
    quittingAnchoredCyclicContinueValue_eq_refusalHazard, ← hren]
  exact (max_eq_right (hone phase who)).symm

/-- **The best reply is refusal.**  When the refusal value dominates the
quit-now value at every phase, and the deviator is a spectator at some phase
carrying positive hazard, the best-reply value against a solo-periodic profile
on this table is exactly the refusal value. -/
theorem quittingBestReplyValue_eq_refusalOnPathValue {m : ℕ} [NeZero m]
    (w : Fin m → Player) (hazard : Fin m → ℝ)
    (h0 : ∀ k, 0 ≤ hazard k) (h1 : ∀ k, hazard k ≤ 1)
    (hone : ∀ (k : Fin m) (who : Player),
      1 ≤ quittingAnchoredCyclicOnPathValue boundaryReward w
        (quittingAnchoredCyclicRefusalHazard w hazard who)
        (quittingAnchoredCyclicRefusalHazard_nonneg h0 w who)
        (quittingAnchoredCyclicRefusalHazard_le_one h1 w who) k who)
    (who : Player) (hspectator : ∃ k, w k ≠ who ∧ 0 < hazard k) :
    quittingBestReplyValue boundaryReward
        (quittingAnchoredCyclicProfile boundaryReward w hazard h0 h1) who =
      quittingAnchoredCyclicOnPathValue boundaryReward w
        (quittingAnchoredCyclicRefusalHazard w hazard who)
        (quittingAnchoredCyclicRefusalHazard_nonneg h0 w who)
        (quittingAnchoredCyclicRefusalHazard_le_one h1 w who)
        (quittingAnchoredCyclicStart m) who := by
  refine le_antisymm ?_
    (quittingAnchoredCyclicOnPathValue_refusalHazard_le_bestReplyValue
      boundaryReward w hazard h0 h1 who)
  have hcap := quittingAnchoredCyclicResponseCap_le_of_response_of_spectatorHazard
    w hazard h0 h1 _
    (isAnchoredCyclicResponseSolution_refusalOnPathValue w hazard h0 h1 hone) who
    hspectator
  have hsup := sSup_range_quittingTerminalPayoff_update_anchoredCyclicProfile
    boundaryReward w hazard h0 h1 who
  show (⨆ deviation, _) ≤ _
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

/-! ## Telescoping around the cycle

The refusal gain obeys a one-step affine recursion with two branches
(`refusalGain_step`), so it unrolls through the generic affine telescope of
`Math.iterateWeight` and `Math.iterateAccumulation`.
-/

/-- The one-step coefficient of the refusal recursion: the refuser's own
phases pass the gain through unchanged, and every other phase damps it by the
phase's survival probability. -/
def refusalCoefficient {m : ℕ} (w : Fin m → Player) (hazard : Fin m → ℝ)
    (refuser : Player) (phase : Fin m) : ℝ :=
  if w phase = refuser then 1 else 1 - hazard phase

/-- The one-step increment of the refusal recursion: the refuser's own phases
contribute the hazard times the excess of the next phase's on-path value over
the refuser's solo exit value, and every other phase contributes nothing. -/
def refusalIncrement {m : ℕ} (w : Fin m → Player) (hazard : Fin m → ℝ)
    (h0 : ∀ k, 0 ≤ hazard k) (h1 : ∀ k, hazard k ≤ 1) (refuser : Player)
    (phase : Fin m) : ℝ :=
  if w phase = refuser then
    hazard phase *
      (quittingAnchoredCyclicOnPathValue boundaryReward w hazard h0 h1
        (finRotate m phase) refuser - 1)
  else 0

/-- Survival accumulated over `n` steps from `phase`, counting only the phases
at which the refuser is not the scheduled quitter. -/
def refusalWeight {m : ℕ} (w : Fin m → Player) (hazard : Fin m → ℝ)
    (refuser : Player) : Fin m → ℕ → ℝ :=
  Math.iterateWeight (finRotate m) (refusalCoefficient w hazard refuser)

/-- Drift accumulated over `n` steps from `phase`: the weighted excess of the
on-path value over the refuser's solo exit value at the refuser's own
phases. -/
def refusalDrift {m : ℕ} (w : Fin m → Player) (hazard : Fin m → ℝ)
    (h0 : ∀ k, 0 ≤ hazard k) (h1 : ∀ k, hazard k ≤ 1) (refuser : Player) :
    Fin m → ℕ → ℝ :=
  Math.iterateAccumulation (finRotate m) (refusalCoefficient w hazard refuser)
    (refusalIncrement w hazard h0 h1 refuser)

/-- **The one-step recursion.**  The two branches of `refusalGain_of_eq` and
`refusalGain_of_ne` are one affine step with coefficient
`refusalCoefficient` and increment `refusalIncrement`. -/
theorem refusalGain_step {m : ℕ} (w : Fin m → Player) (hazard : Fin m → ℝ)
    (h0 : ∀ k, 0 ≤ hazard k) (h1 : ∀ k, hazard k ≤ 1) (refuser : Player)
    (phase : Fin m) :
    refusalGain w hazard h0 h1 refuser phase =
      refusalIncrement w hazard h0 h1 refuser phase +
        refusalCoefficient w hazard refuser phase *
          refusalGain w hazard h0 h1 refuser (finRotate m phase) := by
  unfold refusalIncrement refusalCoefficient
  by_cases h : w phase = refuser
  · rw [if_pos h, if_pos h, refusalGain_of_eq w hazard h0 h1 h]
    ring
  · rw [if_neg h, if_neg h, refusalGain_of_ne w hazard h0 h1 h]
    ring

/-- **The telescoped recursion.**  Unrolling `n` steps splits the refusal gain
into accumulated drift plus surviving weight times the gain `n` steps on. -/
theorem refusalGain_telescope {m : ℕ} (w : Fin m → Player) (hazard : Fin m → ℝ)
    (h0 : ∀ k, 0 ≤ hazard k) (h1 : ∀ k, hazard k ≤ 1) (refuser : Player) :
    ∀ (n : ℕ) (phase : Fin m),
      refusalGain w hazard h0 h1 refuser phase =
        refusalDrift w hazard h0 h1 refuser phase n +
          refusalWeight w hazard refuser phase n *
            refusalGain w hazard h0 h1 refuser ((finRotate m)^[n] phase) :=
  Math.eq_iterateAccumulation_add_iterateWeight_mul
    (refusalGain_step w hazard h0 h1 refuser)

/-- **The cycle identity.**  Around one full cycle the refusal gain satisfies
`D * (1 - W) = Drift`, with `W` the survival weight of the refuser's absence
over one cycle and `Drift` the accumulated own-phase drift. -/
theorem refusalGain_mul_one_sub_weight {m : ℕ} (w : Fin m → Player)
    (hazard : Fin m → ℝ) (h0 : ∀ k, 0 ≤ hazard k) (h1 : ∀ k, hazard k ≤ 1)
    (refuser : Player) (phase : Fin m) :
    refusalGain w hazard h0 h1 refuser phase *
        (1 - refusalWeight w hazard refuser phase m) =
      refusalDrift w hazard h0 h1 refuser phase m := by
  rw [mul_comm]
  exact Math.one_sub_iterateWeight_mul_of_iterate_eq
    (refusalGain_step w hazard h0 h1 refuser) (Math.iterate_finRotate_period phase)

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
        (1 - refusalWeight w hazard refuser phase m) :=
  Math.eq_iterateAccumulation_div_of_iterate_eq
    (refusalGain_step w hazard h0 h1 refuser) (Math.iterate_finRotate_period phase) hW

/-! ## Sign of the accumulated quantities -/

theorem refusalCoefficient_nonneg {m : ℕ} (w : Fin m → Player) {hazard : Fin m → ℝ}
    (h1 : ∀ k, hazard k ≤ 1) (refuser : Player) (phase : Fin m) :
    0 ≤ refusalCoefficient w hazard refuser phase := by
  unfold refusalCoefficient
  split_ifs with h
  · norm_num
  · linarith [h1 phase]

theorem refusalCoefficient_le_one {m : ℕ} (w : Fin m → Player) {hazard : Fin m → ℝ}
    (h0 : ∀ k, 0 ≤ hazard k) (refuser : Player) (phase : Fin m) :
    refusalCoefficient w hazard refuser phase ≤ 1 := by
  unfold refusalCoefficient
  split_ifs with h
  · exact le_refl 1
  · linarith [h0 phase]

theorem refusalWeight_nonneg {m : ℕ} (w : Fin m → Player) {hazard : Fin m → ℝ}
    (h1 : ∀ k, hazard k ≤ 1) (refuser : Player) :
    ∀ (n : ℕ) (phase : Fin m), 0 ≤ refusalWeight w hazard refuser phase n :=
  Math.iterateWeight_nonneg (refusalCoefficient_nonneg w h1 refuser)

theorem refusalWeight_le_one {m : ℕ} (w : Fin m → Player) {hazard : Fin m → ℝ}
    (h0 : ∀ k, 0 ≤ hazard k) (h1 : ∀ k, hazard k ≤ 1) (refuser : Player) :
    ∀ (n : ℕ) (phase : Fin m), refusalWeight w hazard refuser phase n ≤ 1 :=
  Math.iterateWeight_le_one (refusalCoefficient_nonneg w h1 refuser)
    (refusalCoefficient_le_one w h0 refuser)

/-- If the refuser's on-path value never falls below its own solo exit value,
every own-phase increment is nonnegative. -/
theorem refusalIncrement_nonneg {m : ℕ} (w : Fin m → Player) (hazard : Fin m → ℝ)
    (h0 : ∀ k, 0 ≤ hazard k) (h1 : ∀ k, hazard k ≤ 1) (refuser : Player)
    (hU : ∀ k : Fin m, 1 ≤ quittingAnchoredCyclicOnPathValue boundaryReward w
      hazard h0 h1 k refuser) (phase : Fin m) :
    0 ≤ refusalIncrement w hazard h0 h1 refuser phase := by
  unfold refusalIncrement
  split_ifs with h
  · exact mul_nonneg (h0 phase) (by linarith [hU (finRotate m phase)])
  · exact le_refl 0

/-- If the refuser's on-path value never falls below its own solo exit value,
the accumulated drift is nonnegative. -/
theorem refusalDrift_nonneg {m : ℕ} (w : Fin m → Player) (hazard : Fin m → ℝ)
    (h0 : ∀ k, 0 ≤ hazard k) (h1 : ∀ k, hazard k ≤ 1) (refuser : Player)
    (hU : ∀ k : Fin m, 1 ≤ quittingAnchoredCyclicOnPathValue boundaryReward w
      hazard h0 h1 k refuser) :
    ∀ (n : ℕ) (phase : Fin m),
      0 ≤ refusalDrift w hazard h0 h1 refuser phase n :=
  Math.iterateAccumulation_nonneg (refusalCoefficient_nonneg w h1 refuser)
    (refusalIncrement_nonneg w hazard h0 h1 refuser hU)

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

/-! ### Where the on-path floor comes from

The two statements above ask that the refuser's on-path value never fall below
the quit-now value `1`.  Exactness of the one-stage anchored system supplies
that floor on this table
(`one_le_onPathValue_of_isExactAnchoredSoloPeriodic`), and the floor is a
genuine restriction on the class: on `refutingSchedule` player `2`'s on-path
value is below `1` (`refutingOnPathValue`).  Exactness itself is available here
only where some hazard vanishes
(`not_isExactAnchoredSoloPeriodic_of_quantitativeGap`).
-/

/-- The accumulated drift of an exact anchored solo-periodic profile is
nonnegative. -/
theorem refusalDrift_nonneg_of_isExactAnchoredSoloPeriodic {m : ℕ}
    (w : Fin m → Player) (hazard : Fin m → ℝ)
    (h0 : ∀ k, 0 ≤ hazard k) (h1 : ∀ k, hazard k ≤ 1) (refuser : Player)
    (hexact : IsExactAnchoredSoloPeriodic boundaryReward w hazard h0 h1)
    (n : ℕ) (phase : Fin m) :
    0 ≤ refusalDrift w hazard h0 h1 refuser phase n :=
  refusalDrift_nonneg w hazard h0 h1 refuser
    (fun k ↦ one_le_onPathValue_of_isExactAnchoredSoloPeriodic hexact k refuser)
    n phase

/-- The refusal gain of an exact anchored solo-periodic profile dominates its
accumulated drift over one cycle. -/
theorem refusalDrift_le_refusalGain_of_isExactAnchoredSoloPeriodic {m : ℕ}
    (w : Fin m → Player) (hazard : Fin m → ℝ)
    (h0 : ∀ k, 0 ≤ hazard k) (h1 : ∀ k, hazard k ≤ 1) (refuser : Player)
    (hexact : IsExactAnchoredSoloPeriodic boundaryReward w hazard h0 h1)
    (phase : Fin m) (hW : refusalWeight w hazard refuser phase m < 1) :
    refusalDrift w hazard h0 h1 refuser phase m ≤
      refusalGain w hazard h0 h1 refuser phase :=
  refusalDrift_le_refusalGain w hazard h0 h1 refuser
    (fun k ↦ one_le_onPathValue_of_isExactAnchoredSoloPeriodic hexact k refuser)
    phase hW

/-! ## The uniform four-cycle

The schedule `0, 1, 2, 3` of period four carrying one common interior hazard
`p` is the smallest schedule visiting every player.  Writing `q = 1 - p`, the
renewal system solves in closed form: the opening on-path value of player `0`
is `(1 + 4 * q) / (1 + q + q ^ 2 + q ^ 3)` and its refusal value is
`4 / (1 + q + q ^ 2)`, because refusal deletes exactly one of the four exits
of the cycle.  Their difference is at least `1 / 12` and at most
`1 / 12 + 6 * p`, so on this family the refusal deviation delivers `1 / 12` and
nothing beyond it.

This is where the constant `1 / 12` is calibrated, and the calibration is
correct: the bounds below are sharp for this family in the small-hazard limit.
It does not carry to the class — `not_hasUniformSoloPeriodicTerminalGap`
refutes the same constant at fixed hazards on an interleaved schedule.
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

/-! ## The two propositions, and their refutation

Both are false.  `refutingSchedule` below designates every player, carries
interior hazards, and leaves every player short of `1 / 12` against every
behavioral deviation; since the restricted proposition only adds a hypothesis
to the unrestricted one, refuting the restricted one refutes both.  The
definitions are kept because `not_hasSurjectiveSoloPeriodicTerminalGap` and
`not_hasUniformSoloPeriodicTerminalGap` are statements about them.

The failure is not among the schedules omitting a player: those carry the
constant outright
(`exists_terminalPayoff_add_twelfth_le_bestReplyValue_of_forall_ne`).
-/

/-- The uniform terminal gap for solo-periodic profiles on the Solan–Vieille
table: some player's best-reply value exceeds its on-path value by at least
`1 / 12`, for every period, every schedule with repetitions and every family
of interior hazards.  It is false: `not_hasUniformSoloPeriodicTerminalGap`.
The constant is the one the uniform four-cycle calibrates as its hazard tends
to zero (`twelfth_le_bestReplyValue_sub_terminalPayoff_uniformFourCycle` and
`uniformFourCycleRefusalGain_le`). -/
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
once.  It is false: `not_hasSurjectiveSoloPeriodicTerminalGap`. -/
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

/-! ## The refuting witness

Both propositions are false.  On the period-four schedule `0, 2, 1, 3` at
hazards `3/16, 21/100, 7/40, 33/200` the opening on-path values are

`(8151200, 11037800, 6657612, 9854403) / 7140203`,

summing to `5`, and the refusal values are `442400/364631`, `80000/49497`,
`56628/56357` and `43680/30109`.  Every one of the sixteen refusal values is at
least `1`, so `quittingBestReplyValue_eq_refusalOnPathValue` identifies each
best-reply value with the refusal value, and all four gaps are strictly below
`1 / 12`, the largest being `4161768000/57485774353` at player `2`.

The schedule interleaves the two pairs.  In the pairs-adjacent order of the
uniform four-cycle each player's partner exit follows its own phase
immediately, and refusal moves absorption onto that exit efficiently; the
interleaved order with unequal hazards starves refusal while keeping every
on-path value near `1`, and `1 / 12` fails.
-/

/-- **The four renewal equations of a period-four cycle**, with the hazards and
the singleton rows read off by the supplied equations. -/
theorem onPathValue_four_system (w : Fin 4 → Player) (hazard : Fin 4 → ℝ)
    (h0 : ∀ k, 0 ≤ hazard k) (h1 : ∀ k, hazard k ≤ 1) (who : Player)
    {p₀ p₁ p₂ p₃ a₀ a₁ a₂ a₃ : ℝ}
    (hp₀ : hazard 0 = p₀) (hp₁ : hazard 1 = p₁) (hp₂ : hazard 2 = p₂)
    (hp₃ : hazard 3 = p₃)
    (ha₀ : boundaryReward (quittingSingletonTerminal (w 0)) who = a₀)
    (ha₁ : boundaryReward (quittingSingletonTerminal (w 1)) who = a₁)
    (ha₂ : boundaryReward (quittingSingletonTerminal (w 2)) who = a₂)
    (ha₃ : boundaryReward (quittingSingletonTerminal (w 3)) who = a₃) :
    quittingAnchoredCyclicOnPathValue boundaryReward w hazard h0 h1 0 who =
          p₀ * a₀ + (1 - p₀) * quittingAnchoredCyclicOnPathValue boundaryReward
            w hazard h0 h1 1 who ∧
        quittingAnchoredCyclicOnPathValue boundaryReward w hazard h0 h1 1 who =
          p₁ * a₁ + (1 - p₁) * quittingAnchoredCyclicOnPathValue boundaryReward
            w hazard h0 h1 2 who ∧
        quittingAnchoredCyclicOnPathValue boundaryReward w hazard h0 h1 2 who =
          p₂ * a₂ + (1 - p₂) * quittingAnchoredCyclicOnPathValue boundaryReward
            w hazard h0 h1 3 who ∧
      quittingAnchoredCyclicOnPathValue boundaryReward w hazard h0 h1 3 who =
        p₃ * a₃ + (1 - p₃) * quittingAnchoredCyclicOnPathValue boundaryReward
          w hazard h0 h1 0 who := by
  subst hp₀; subst hp₁; subst hp₂; subst hp₃
  subst ha₀; subst ha₁; subst ha₂; subst ha₃
  have hren : ∀ k : Fin 4,
      quittingAnchoredCyclicOnPathValue boundaryReward w hazard h0 h1 k who =
        hazard k * boundaryReward (quittingSingletonTerminal (w k)) who +
          (1 - hazard k) * quittingAnchoredCyclicOnPathValue boundaryReward w
            hazard h0 h1 (finRotate 4 k) who :=
    fun k ↦ quittingAnchoredCyclicOnPathValue_renewal boundaryReward w hazard
      h0 h1 k who
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h := hren 0
    rwa [show finRotate 4 (0 : Fin 4) = 1 from by decide] at h
  · have h := hren 1
    rwa [show finRotate 4 (1 : Fin 4) = 2 from by decide] at h
  · have h := hren 2
    rwa [show finRotate 4 (2 : Fin 4) = 3 from by decide] at h
  · have h := hren 3
    rwa [show finRotate 4 (3 : Fin 4) = 0 from by decide] at h

/-- The period-four schedule refuting both propositions.  It interleaves the
two pairs. -/
def refutingSchedule : Fin 4 → Player := ![0, 2, 1, 3]

/-- The hazards accompanying `refutingSchedule`. -/
def refutingHazard : Fin 4 → ℝ := ![3 / 16, 21 / 100, 7 / 40, 33 / 200]

theorem refutingSchedule_surjective (z : Player) : ∃ k, refutingSchedule k = z := by
  rcases player_eq z with rfl | rfl | rfl | rfl
  exacts [⟨0, rfl⟩, ⟨2, rfl⟩, ⟨1, rfl⟩, ⟨3, rfl⟩]

theorem refutingHazard_pos : ∀ k, 0 < refutingHazard k := by
  intro k
  fin_cases k <;> norm_num [refutingHazard]

theorem refutingHazard_nonneg : ∀ k, 0 ≤ refutingHazard k :=
  fun k ↦ (refutingHazard_pos k).le

theorem refutingHazard_le_one : ∀ k, refutingHazard k ≤ 1 := by
  intro k
  fin_cases k <;> norm_num [refutingHazard]

/-- Every player is a spectator at a phase carrying positive hazard. -/
theorem refutingSpectator (who : Player) :
    ∃ k, refutingSchedule k ≠ who ∧ 0 < refutingHazard k := by
  rcases player_eq who with rfl | rfl | rfl | rfl
  · exact ⟨1, by decide, refutingHazard_pos 1⟩
  · exact ⟨0, by decide, refutingHazard_pos 0⟩
  · exact ⟨0, by decide, refutingHazard_pos 0⟩
  · exact ⟨0, by decide, refutingHazard_pos 0⟩

/-- The singleton rows visited by `refutingSchedule`. -/
theorem refutingReward (k : Fin 4) (who : Player) :
    boundaryReward (quittingSingletonTerminal (refutingSchedule k)) who =
      ![![1, 4, 0, 0], ![0, 0, 1, 4], ![4, 1, 0, 0], ![0, 0, 4, 1]] k who := by
  fin_cases k <;> fin_cases who <;> rfl

/-- The four hazard vectors seen by the four refusers on
`refutingSchedule`. -/
theorem refutingRefusalHazard (who : Player) (k : Fin 4) :
    quittingAnchoredCyclicRefusalHazard refutingSchedule refutingHazard who k =
      ![![0, 21 / 100, 7 / 40, 33 / 200], ![3 / 16, 21 / 100, 0, 33 / 200],
        ![3 / 16, 0, 7 / 40, 33 / 200],
        ![3 / 16, 21 / 100, 7 / 40, 0]] who k := by
  fin_cases who <;> fin_cases k <;> rfl

/-- The four opening on-path values of `refutingSchedule`, summing to `5`. -/
theorem refutingOnPathValue (who : Player) :
    quittingAnchoredCyclicOnPathValue boundaryReward refutingSchedule
        refutingHazard refutingHazard_nonneg refutingHazard_le_one 0 who =
      ![8151200 / 7140203, 11037800 / 7140203, 6657612 / 7140203,
        9854403 / 7140203] who := by
  obtain ⟨e0, e1, e2, e3⟩ := onPathValue_four_system refutingSchedule
    refutingHazard refutingHazard_nonneg refutingHazard_le_one who
    (show refutingHazard 0 = 3 / 16 from rfl)
    (show refutingHazard 1 = 21 / 100 from rfl)
    (show refutingHazard 2 = 7 / 40 from rfl)
    (show refutingHazard 3 = 33 / 200 from rfl) (refutingReward 0 who)
    (refutingReward 1 who) (refutingReward 2 who) (refutingReward 3 who)
  rcases player_eq who with rfl | rfl | rfl | rfl <;>
    norm_num [Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
      Matrix.tail_cons] at e0 e1 e2 e3 ⊢ <;>
    linarith

/-- The sixteen refusal values of `refutingSchedule`, phase by phase. -/
theorem refutingRefusalValue (who : Player) (k : Fin 4) :
    quittingAnchoredCyclicOnPathValue boundaryReward refutingSchedule
        (quittingAnchoredCyclicRefusalHazard refutingSchedule refutingHazard
          who)
        (quittingAnchoredCyclicRefusalHazard_nonneg refutingHazard_nonneg
          refutingSchedule who)
        (quittingAnchoredCyclicRefusalHazard_le_one refutingHazard_le_one
          refutingSchedule who) k who =
      ![![442400 / 364631, 442400 / 364631, 560000 / 364631, 369404 / 364631],
        ![80000 / 49497, 52772 / 49497, 66800 / 49497, 66800 / 49497],
        ![56628 / 56357, 69696 / 56357, 69696 / 56357, 84480 / 56357],
        ![43680 / 30109, 53760 / 30109, 36036 / 30109,
          43680 / 30109]] who k := by
  obtain ⟨e0, e1, e2, e3⟩ := onPathValue_four_system refutingSchedule
    (quittingAnchoredCyclicRefusalHazard refutingSchedule refutingHazard who)
    (quittingAnchoredCyclicRefusalHazard_nonneg refutingHazard_nonneg
      refutingSchedule who)
    (quittingAnchoredCyclicRefusalHazard_le_one refutingHazard_le_one
      refutingSchedule who) who (refutingRefusalHazard who 0)
    (refutingRefusalHazard who 1) (refutingRefusalHazard who 2)
    (refutingRefusalHazard who 3) (refutingReward 0 who)
    (refutingReward 1 who) (refutingReward 2 who) (refutingReward 3 who)
  rcases player_eq who with rfl | rfl | rfl | rfl <;>
    rcases player_eq k with rfl | rfl | rfl | rfl <;>
    norm_num [Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
      Matrix.tail_cons] at e0 e1 e2 e3 ⊢ <;>
    linarith

/-- Refusal beats quitting now at every phase of `refutingSchedule`. -/
theorem one_le_refutingRefusalValue (k : Fin 4) (who : Player) :
    1 ≤ quittingAnchoredCyclicOnPathValue boundaryReward refutingSchedule
      (quittingAnchoredCyclicRefusalHazard refutingSchedule refutingHazard who)
      (quittingAnchoredCyclicRefusalHazard_nonneg refutingHazard_nonneg
        refutingSchedule who)
      (quittingAnchoredCyclicRefusalHazard_le_one refutingHazard_le_one
        refutingSchedule who) k who := by
  rw [refutingRefusalValue who k]
  rcases player_eq who with rfl | rfl | rfl | rfl <;>
    rcases player_eq k with rfl | rfl | rfl | rfl <;>
    norm_num [Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
      Matrix.tail_cons]

/-- **The best replies against the refuting witness.**  Each is the refusal
value. -/
theorem refutingBestReplyValue (who : Player) :
    quittingBestReplyValue boundaryReward
        (quittingAnchoredCyclicProfile boundaryReward refutingSchedule
          refutingHazard refutingHazard_nonneg refutingHazard_le_one) who =
      ![442400 / 364631, 80000 / 49497, 56628 / 56357, 43680 / 30109] who := by
  rw [quittingBestReplyValue_eq_refusalOnPathValue refutingSchedule
      refutingHazard refutingHazard_nonneg refutingHazard_le_one
      one_le_refutingRefusalValue who (refutingSpectator who),
    show quittingAnchoredCyclicStart 4 = (0 : Fin 4) from rfl,
    refutingRefusalValue who 0]
  rcases player_eq who with rfl | rfl | rfl | rfl <;>
    norm_num [Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
      Matrix.tail_cons]

/-- **The surjective terminal gap fails.**  On `refutingSchedule` no player's
best-reply value exceeds its on-path payoff by `1 / 12`. -/
theorem not_hasSurjectiveSoloPeriodicTerminalGap :
    ¬ HasSurjectiveSoloPeriodicTerminalGap := by
  intro hgap
  obtain ⟨who, hwho⟩ := hgap 4 (by infer_instance) refutingSchedule
    refutingHazard refutingHazard_nonneg refutingHazard_le_one
    refutingHazard_pos refutingSchedule_surjective
  rw [quittingTerminalPayoff_anchoredCyclicProfile,
    show quittingAnchoredCyclicStart 4 = (0 : Fin 4) from rfl,
    refutingOnPathValue who, refutingBestReplyValue who] at hwho
  rcases player_eq who with rfl | rfl | rfl | rfl <;>
    norm_num [Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
      Matrix.tail_cons] at hwho

/-- **The uniform terminal gap fails.**  `refutingSchedule` designates every
player, so it is an instance of the unrestricted statement as well. -/
theorem not_hasUniformSoloPeriodicTerminalGap :
    ¬ HasUniformSoloPeriodicTerminalGap := fun hgap ↦
  not_hasSurjectiveSoloPeriodicTerminalGap
    fun m hm w hazard h0 h1 hpos _ ↦ hgap m hm w hazard h0 h1 hpos

end SolanVieilleBoundary

end GameTheory
