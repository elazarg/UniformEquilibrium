/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Classification.Existence.ActiveOpponentDeviationTelescope
import UniformEquilibrium.Quitting.Classification.Existence.PerfectSequenceExtractionReduction

/-!
# Perfect-sequence extraction from the activity dichotomy

The closing arguments of Solan and Vieille, *Quitting games*, Math. Oper.
Res. 26 (2001), Theorem 1.2, in this development's root-sequence
vocabulary.

For a tolerance `ρ`, a root sequence is either `ρ`-active for every player —
from every stage and horizon, the plan's survival plus its survival-weighted
opponent absorption stays at least `ρ` — or some player has a quiet window:
a stage range over which the plan almost surely absorbs while its
survival-weighted opponent absorption stays below `ρ`.  In the active case
the deviation telescope caps every deviation of every player at `3 εr / ρ`.
In the quiet case, the window contains a stage where the quiet player
itself quits with positive probability, preceded only by opponent-silent
stages, so the window renormalizes into the quiet-window stationary repair
with error `εr + 4 M η` at `η = 3 ρ / (1 - ρ)`.

Choosing `ρ` and the row tolerance from the target tolerance proves the
perfect-sequence extraction step for every table with unit solo exit and
capped joint exit, and therefore — through the conditional reduction — the
existence law `QuittingCappedJointExitUniformεExistence` itself.
-/

noncomputable section

namespace GameTheory

open StochasticGame Filter Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The root-sequence global cap is monotone in its tolerance. -/
theorem IsεQuittingRootSequenceNash.mono
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {roots : ℕ → ι → PMF Bool} {ε ε' : ℝ}
    (h : IsεQuittingRootSequenceNash reward ε roots) (hle : ε ≤ ε') :
    IsεQuittingRootSequenceNash reward ε' roots := by
  intro who hazard
  have := h who hazard
  linarith

/-- Global activity is stable under restarting the sequence. Consequently,
the active-opponent deviation telescope certifies every tail rather than only
the profile starting at time zero. -/
theorem isεAsymptoticNash_quittingRootSequenceProfile_of_active
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (roots : ℕ → ι → PMF Bool)
    {εr δ ρ : ℝ} (hεr : 0 ≤ εr) (hδ0 : 0 < δ) (hρ0 : 0 < ρ)
    (hfloor : ∀ n, δ ≤ quittingRootAbsorptionMass (roots n))
    (hperfect : ∀ n, QuittingRowεPerfect reward
      (quittingRootSequenceTailVector reward roots (n + 1)) (roots n) εr)
    (hactive : ∀ (who : ι) (start fuel : ℕ),
      ρ ≤ quittingJointSurvivalWeight roots start fuel +
        ∑ t ∈ Finset.range fuel,
          quittingJointSurvivalWeight roots start t *
            quittingRootOpponentAbsorptionMass (roots (start + t)) who)
    (start : ℕ) :
    (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) (3 * εr / ρ)
      (quittingRootSequenceProfile reward roots start) := by
  let shifted : ℕ → ι → PMF Bool := fun n => roots (start + n)
  have hsurvivalShift : ∀ s fuel,
      quittingJointSurvivalWeight shifted s fuel =
        quittingJointSurvivalWeight roots (start + s) fuel := by
    intro s fuel
    rw [quittingJointSurvivalWeight_eq_prod,
      quittingJointSurvivalWeight_eq_prod]
    apply Finset.prod_congr rfl
    intro offset _
    simp [shifted, Nat.add_assoc]
  have htailShift : ∀ s,
      quittingRootSequenceTailVector reward shifted s =
        quittingRootSequenceTailVector reward roots (start + s) := by
    intro s
    have hprofile : quittingRootSequenceProfile reward shifted s =
        quittingRootSequenceProfile reward roots (start + s) := by
      funext player time history
      simp [quittingRootSequenceProfile, shifted, Nat.add_assoc]
    funext who
    unfold quittingRootSequenceTailVector quittingRootSequenceTerminalValue
    rw [hprofile]
  have hfloorShift : ∀ n,
      δ ≤ quittingRootAbsorptionMass (shifted n) := by
    intro n
    exact hfloor (start + n)
  have hperfectShift : ∀ n, QuittingRowεPerfect reward
      (quittingRootSequenceTailVector reward shifted (n + 1))
      (shifted n) εr := by
    intro n
    rw [htailShift]
    simpa [shifted, Nat.add_assoc] using hperfect (start + n)
  have hactiveShift : ∀ (who : ι) (s fuel : ℕ),
      ρ ≤ quittingJointSurvivalWeight shifted s fuel +
        ∑ t ∈ Finset.range fuel,
          quittingJointSurvivalWeight shifted s t *
            quittingRootOpponentAbsorptionMass (shifted (s + t)) who := by
    intro who s fuel
    have h := hactive who (start + s) fuel
    simpa [hsurvivalShift, shifted, Nat.add_assoc] using h
  have hnash := isεQuittingRootSequenceNash_of_active shifted hεr hδ0 hρ0
    hfloorShift hperfectShift hactiveShift
  have hprofile :=
    (isεQuittingRootSequenceNash_iff_isεAsymptoticNash reward
      (3 * εr / ρ) shifted).1 hnash
  rw [quittingRootSequenceProfile_eq_shift]
  simpa [shifted] using hprofile

/-- Global activity and vanishing survival from every restart certify every
tail, without requiring a uniform one-stage absorption floor. -/
theorem isεAsymptoticNash_quittingRootSequenceProfile_of_active_of_tendsto
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (roots : ℕ → ι → PMF Bool)
    {εr ρ : ℝ} (hεr : 0 ≤ εr) (hρ0 : 0 < ρ)
    (hvanish : ∀ start,
      Tendsto (quittingJointSurvivalWeight roots start) atTop (nhds 0))
    (hperfect : ∀ n, QuittingRowεPerfect reward
      (quittingRootSequenceTailVector reward roots (n + 1)) (roots n) εr)
    (hactive : ∀ (who : ι) (start fuel : ℕ),
      ρ ≤ quittingJointSurvivalWeight roots start fuel +
        ∑ t ∈ Finset.range fuel,
          quittingJointSurvivalWeight roots start t *
            quittingRootOpponentAbsorptionMass (roots (start + t)) who)
    (start : ℕ) :
    (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) (3 * εr / ρ)
      (quittingRootSequenceProfile reward roots start) := by
  let shifted : ℕ → ι → PMF Bool := fun n => roots (start + n)
  have hsurvivalShift : ∀ s fuel,
      quittingJointSurvivalWeight shifted s fuel =
        quittingJointSurvivalWeight roots (start + s) fuel := by
    intro s fuel
    rw [quittingJointSurvivalWeight_eq_prod,
      quittingJointSurvivalWeight_eq_prod]
    apply Finset.prod_congr rfl
    intro offset _
    simp [shifted, Nat.add_assoc]
  have htailShift : ∀ s,
      quittingRootSequenceTailVector reward shifted s =
        quittingRootSequenceTailVector reward roots (start + s) := by
    intro s
    have hprofile : quittingRootSequenceProfile reward shifted s =
        quittingRootSequenceProfile reward roots (start + s) := by
      funext player time history
      simp [quittingRootSequenceProfile, shifted, Nat.add_assoc]
    funext who
    unfold quittingRootSequenceTailVector quittingRootSequenceTerminalValue
    rw [hprofile]
  have hvanishShift : ∀ s,
      Tendsto (quittingJointSurvivalWeight shifted s) atTop (nhds 0) := by
    intro s
    have heq : quittingJointSurvivalWeight shifted s =
        quittingJointSurvivalWeight roots (start + s) := by
      funext fuel
      exact hsurvivalShift s fuel
    rw [heq]
    exact hvanish (start + s)
  have hperfectShift : ∀ n, QuittingRowεPerfect reward
      (quittingRootSequenceTailVector reward shifted (n + 1))
      (shifted n) εr := by
    intro n
    rw [htailShift]
    simpa [shifted, Nat.add_assoc] using hperfect (start + n)
  have hactiveShift : ∀ (who : ι) (s fuel : ℕ),
      ρ ≤ quittingJointSurvivalWeight shifted s fuel +
        ∑ t ∈ Finset.range fuel,
          quittingJointSurvivalWeight shifted s t *
            quittingRootOpponentAbsorptionMass (shifted (s + t)) who := by
    intro who s fuel
    have h := hactive who (start + s) fuel
    simpa [hsurvivalShift, shifted, Nat.add_assoc] using h
  have hnash := isεQuittingRootSequenceNash_of_active_of_tendsto shifted
    hεr hρ0 hvanishShift hperfectShift hactiveShift
  have hprofile :=
    (isεQuittingRootSequenceNash_iff_isεAsymptoticNash reward
      (3 * εr / ρ) shifted).1 hnash
  rw [quittingRootSequenceProfile_eq_shift]
  simpa [shifted] using hprofile

/-- **The quiet-window branch.**  If some player's survival-weighted
opponent absorption plus the plan's survival falls below `ρ ≤ 1/2` over some
window, then some window stage has that player quitting with positive
probability, its preceding window stages are opponent-silent, and the window
from that stage renormalizes to the quiet-window data at `η = 3ρ/(1-ρ)`. -/
theorem exists_quietWindow_anchor
    (roots : ℕ → ι → PMF Bool) (who : ι) {ρ : ℝ}
    (hρ0 : 0 < ρ) (hρhalf : ρ ≤ 1 / 2) (start fuel : ℕ)
    (hquiet : quittingJointSurvivalWeight roots start fuel +
        (∑ t ∈ Finset.range fuel,
          quittingJointSurvivalWeight roots start t *
            quittingRootOpponentAbsorptionMass (roots (start + t)) who) <
      ρ) :
    ∃ (anchor window : ℕ), 0 < window ∧
      0 < (roots anchor who true).toReal ∧
      2 * (∑ t ∈ Finset.range window,
          quittingJointSurvivalWeight roots anchor t *
            quittingRootOpponentAbsorptionMass (roots (anchor + t)) who) +
        quittingJointSurvivalWeight roots anchor window ≤
        3 * ρ / (1 - ρ) := by
  classical
  have hρ1 : ρ < 1 := by linarith
  have hone : 0 < 1 - ρ := by linarith
  set charge : ℕ → ℝ := fun t =>
    quittingJointSurvivalWeight roots start t *
      quittingRootOpponentAbsorptionMass (roots (start + t)) who
    with hcharge
  have hcharge0 : ∀ t, 0 ≤ charge t := fun t => mul_nonneg
    (quittingJointSurvivalWeight_nonneg roots start t)
    (quittingRootOpponentAbsorptionMass_nonneg _ _)
  have hchargeSum0 : 0 ≤ ∑ t ∈ Finset.range fuel, charge t :=
    Finset.sum_nonneg fun t _ => hcharge0 t
  have hjsw0 : 0 ≤ quittingJointSurvivalWeight roots start fuel :=
    quittingJointSurvivalWeight_nonneg roots start fuel
  -- a window stage where the player itself quits with positive probability
  have hexists : ∃ offset, offset < fuel ∧
      0 < (roots (start + offset) who true).toReal := by
    by_contra hno
    push Not at hno
    have hzero : ∀ offset, offset < fuel →
        (roots (start + offset) who true).toReal = 0 := by
      intro offset hoffset
      exact le_antisymm (hno offset hoffset) ENNReal.toReal_nonneg
    have hcongr : ∀ offset ∈ Finset.range fuel, charge offset =
        quittingJointSurvivalWeight roots start offset *
          quittingRootAbsorptionMass (roots (start + offset)) := by
      intro offset hoffset
      have hbalance := quitWeight_mul_opponentContinueMass_eq
        (roots (start + offset)) who
      rw [hzero offset (Finset.mem_range.mp hoffset), zero_mul] at hbalance
      have hmasses : quittingRootOpponentAbsorptionMass
          (roots (start + offset)) who =
          quittingRootAbsorptionMass (roots (start + offset)) := by
        linarith
      show quittingJointSurvivalWeight roots start offset *
          quittingRootOpponentAbsorptionMass (roots (start + offset)) who = _
      rw [hmasses]
    have htelescope := sum_jointSurvivalWeight_mul_absorptionMass roots
      start fuel
    rw [Finset.sum_congr rfl hcongr, htelescope] at hquiet
    linarith
  set anchorOffset := Nat.find hexists with hanchorOffset
  obtain ⟨hanchorLt, hanchorPos⟩ := Nat.find_spec hexists
  rw [← hanchorOffset] at hanchorLt hanchorPos
  have hquietPrefix : ∀ j, j < anchorOffset →
      (roots (start + j) who true).toReal = 0 := by
    intro j hj
    have hmin := Nat.find_min hexists hj
    push Not at hmin
    have hjfuel : j < fuel := by omega
    exact le_antisymm (hmin hjfuel) ENNReal.toReal_nonneg
  -- the prefix loses at most the quiet charge, so its survival exceeds `1-ρ`
  have hprefixSurvival : 1 - ρ ≤
      quittingJointSurvivalWeight roots start anchorOffset := by
    have hcongr : ∀ j ∈ Finset.range anchorOffset,
        quittingJointSurvivalWeight roots start j *
          quittingRootAbsorptionMass (roots (start + j)) = charge j := by
      intro j hj
      have hbalance := quitWeight_mul_opponentContinueMass_eq
        (roots (start + j)) who
      rw [hquietPrefix j (Finset.mem_range.mp hj), zero_mul] at hbalance
      have hmasses : quittingRootOpponentAbsorptionMass
          (roots (start + j)) who =
          quittingRootAbsorptionMass (roots (start + j)) := by linarith
      show quittingJointSurvivalWeight roots start j *
          quittingRootAbsorptionMass (roots (start + j)) =
        quittingJointSurvivalWeight roots start j *
          quittingRootOpponentAbsorptionMass (roots (start + j)) who
      rw [hmasses]
    have htelescope := sum_jointSurvivalWeight_mul_absorptionMass roots
      start anchorOffset
    have hsubset : (∑ j ∈ Finset.range anchorOffset, charge j) ≤
        ∑ j ∈ Finset.range fuel, charge j :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (by
          intro x hx
          exact Finset.mem_range.mpr
            (lt_of_lt_of_le (Finset.mem_range.mp hx) (le_of_lt hanchorLt)))
        (fun j _ _ => hcharge0 j)
    rw [Finset.sum_congr rfl hcongr] at htelescope
    linarith
  have hprefixPos : 0 < quittingJointSurvivalWeight roots start anchorOffset :=
    lt_of_lt_of_le hone hprefixSurvival
  refine ⟨start + anchorOffset, fuel - anchorOffset,
    Nat.sub_pos_of_lt hanchorLt, hanchorPos, ?_⟩
  set window := fuel - anchorOffset with hwindow
  -- renormalize the window survival
  have hsplitSurvival : quittingJointSurvivalWeight roots start fuel =
      quittingJointSurvivalWeight roots start anchorOffset *
        quittingJointSurvivalWeight roots (start + anchorOffset) window := by
    rw [show fuel = anchorOffset + window from
      (Nat.add_sub_cancel' hanchorLt.le).symm,
      quittingJointSurvivalWeight_add]
  have hwindowSurvival : quittingJointSurvivalWeight roots
      (start + anchorOffset) window ≤ ρ / (1 - ρ) := by
    have hjswWindow0 : 0 ≤ quittingJointSurvivalWeight roots
        (start + anchorOffset) window :=
      quittingJointSurvivalWeight_nonneg roots _ _
    rw [le_div_iff₀ hone]
    have hscaled := mul_le_mul_of_nonneg_left hprefixSurvival hjswWindow0
    calc quittingJointSurvivalWeight roots (start + anchorOffset) window *
        (1 - ρ) ≤
        quittingJointSurvivalWeight roots (start + anchorOffset) window *
          quittingJointSurvivalWeight roots start anchorOffset := by
          linarith [hscaled]
      _ = quittingJointSurvivalWeight roots start fuel := by
          rw [hsplitSurvival]; ring
      _ ≤ ρ := by linarith
  -- renormalize the window charge
  have hsplitCharge : quittingJointSurvivalWeight roots start anchorOffset *
      (∑ t ∈ Finset.range window,
        quittingJointSurvivalWeight roots (start + anchorOffset) t *
          quittingRootOpponentAbsorptionMass
            (roots (start + anchorOffset + t)) who) =
      ∑ t ∈ Finset.range window, charge (anchorOffset + t) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t _
    show quittingJointSurvivalWeight roots start anchorOffset *
        (quittingJointSurvivalWeight roots (start + anchorOffset) t *
          quittingRootOpponentAbsorptionMass
            (roots (start + anchorOffset + t)) who) =
      quittingJointSurvivalWeight roots start (anchorOffset + t) *
        quittingRootOpponentAbsorptionMass
          (roots (start + (anchorOffset + t))) who
    rw [show start + (anchorOffset + t) = start + anchorOffset + t from
      by omega, quittingJointSurvivalWeight_add roots start anchorOffset t]
    ring
  have hwindowCharge : (∑ t ∈ Finset.range window,
      quittingJointSurvivalWeight roots (start + anchorOffset) t *
        quittingRootOpponentAbsorptionMass
          (roots (start + anchorOffset + t)) who) ≤ ρ / (1 - ρ) := by
    have hwindowCharge0 : 0 ≤ ∑ t ∈ Finset.range window,
        quittingJointSurvivalWeight roots (start + anchorOffset) t *
          quittingRootOpponentAbsorptionMass
            (roots (start + anchorOffset + t)) who :=
      Finset.sum_nonneg fun t _ => mul_nonneg
        (quittingJointSurvivalWeight_nonneg roots _ t)
        (quittingRootOpponentAbsorptionMass_nonneg _ _)
    have hshifted : (∑ t ∈ Finset.range window,
        charge (anchorOffset + t)) ≤ ∑ j ∈ Finset.range fuel, charge j := by
      have hIco : (∑ t ∈ Finset.range window, charge (anchorOffset + t)) =
          ∑ j ∈ Finset.Ico anchorOffset fuel, charge j := by
        rw [Finset.sum_Ico_eq_sum_range, hwindow]
      rw [hIco, ← Finset.sum_range_add_sum_Ico charge
        (le_of_lt hanchorLt)]
      have hprefix0 : 0 ≤ ∑ j ∈ Finset.range anchorOffset, charge j :=
        Finset.sum_nonneg fun j _ => hcharge0 j
      linarith
    rw [le_div_iff₀ hone]
    calc (∑ t ∈ Finset.range window,
        quittingJointSurvivalWeight roots (start + anchorOffset) t *
          quittingRootOpponentAbsorptionMass
            (roots (start + anchorOffset + t)) who) * (1 - ρ) ≤
        (∑ t ∈ Finset.range window,
          quittingJointSurvivalWeight roots (start + anchorOffset) t *
            quittingRootOpponentAbsorptionMass
              (roots (start + anchorOffset + t)) who) *
          quittingJointSurvivalWeight roots start anchorOffset :=
          mul_le_mul_of_nonneg_left hprefixSurvival hwindowCharge0
      _ = ∑ t ∈ Finset.range window, charge (anchorOffset + t) := by
          rw [← hsplitCharge]; ring
      _ ≤ ∑ j ∈ Finset.range fuel, charge j := hshifted
      _ ≤ ρ := by linarith
  calc 2 * (∑ t ∈ Finset.range window,
      quittingJointSurvivalWeight roots (start + anchorOffset) t *
        quittingRootOpponentAbsorptionMass
          (roots (start + anchorOffset + t)) who) +
      quittingJointSurvivalWeight roots (start + anchorOffset) window ≤
      2 * (ρ / (1 - ρ)) + ρ / (1 - ρ) := by linarith
    _ = 3 * ρ / (1 - ρ) := by ring

/-- **Quantitative subgame dichotomy with terminating tails.** For every
target tolerance, a small enough row tolerance makes every perfect root
sequence whose survival vanishes after every restart either an approximate
terminal Nash profile after every restart or yields a stationary solo repair.
This is the production form of the activity argument in Solan--Vieille's
Lemmas 2.2 and 2.6. -/
theorem quittingPerfectSequenceSubgameDichotomy_of_soloExitPreference_of_tendsto
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (hunit : QuittingUnitSoloExit reward) :
    ∀ εout : ℝ, 0 < εout → ∃ εrow : ℝ, 0 < εrow ∧
      ∀ (roots : ℕ → ι → PMF Bool),
        (∀ start,
          Tendsto (quittingJointSurvivalWeight roots start) atTop (nhds 0)) →
        (∀ n, QuittingRowεPerfect reward
          (quittingRootSequenceTailVector reward roots (n + 1)) (roots n)
          εrow) →
        (∀ start,
          (quittingGame reward).IsεAsymptoticNash
            (quittingTerminalPayoff reward) εout
            (quittingRootSequenceProfile reward roots start)) ∨
          ∃ root : ι → PMF Bool,
            (quittingGame reward).IsεAsymptoticNash
              (quittingTerminalPayoff reward) εout
              (quittingStationaryProfile reward root) := by
  intro εout hεout
  set M := quittingRewardBound reward with hMdef
  have hM : 0 ≤ M := quittingRewardBound_nonneg reward
  have hreward : ∀ terminal player, |reward terminal player| ≤ M :=
    abs_reward_le_quittingRewardBound reward
  set ρ := min (1 / 2) (min (1 / (6 * M + 1)) (εout / (48 * M + 1)))
    with hρdef
  have hρ0 : 0 < ρ := by
    apply lt_min (by norm_num)
    exact lt_min (by positivity) (by positivity)
  have hρhalf : ρ ≤ 1 / 2 := min_le_left _ _
  have hρM : ρ ≤ 1 / (6 * M + 1) := le_trans (min_le_right _ _)
    (min_le_left _ _)
  have hρout : ρ ≤ εout / (48 * M + 1) := le_trans (min_le_right _ _)
    (min_le_right _ _)
  have hone : 0 < 1 - ρ := by linarith
  set η := 3 * ρ / (1 - ρ) with hηdef
  have hη0 : 0 ≤ η := by positivity
  have hη6ρ : η ≤ 6 * ρ := by
    rw [hηdef, div_le_iff₀ hone]
    nlinarith
  have hMη : M * η ≤ 1 := by
    have hscaled : M * η ≤ M * (6 * ρ) :=
      mul_le_mul_of_nonneg_left hη6ρ hM
    have hρbound : (6 * M + 1) * ρ ≤ 1 := by
      have := mul_le_mul_of_nonneg_left hρM
        (by linarith : (0 : ℝ) ≤ 6 * M + 1)
      rwa [mul_one_div, div_self (by linarith : (6 : ℝ) * M + 1 ≠ 0)]
        at this
    nlinarith
  have h4Mη : 4 * M * η ≤ εout / 2 := by
    have hscaled : 4 * M * η ≤ 24 * (M * ρ) := by nlinarith
    have hρbound : (48 * M + 1) * ρ ≤ εout := by
      have := mul_le_mul_of_nonneg_left hρout
        (by linarith : (0 : ℝ) ≤ 48 * M + 1)
      rwa [mul_div_cancel₀ εout (by linarith : (48 : ℝ) * M + 1 ≠ 0)]
        at this
    nlinarith
  refine ⟨min (εout / 2) (εout * ρ / 3), lt_min (by positivity)
    (by positivity), ?_⟩
  intro roots hvanish hperfect
  set εrow := min (εout / 2) (εout * ρ / 3) with hεrowdef
  have hεrow0 : 0 < εrow := lt_min (by positivity) (by positivity)
  by_cases hactive : ∀ (who : ι) (start fuel : ℕ),
      ρ ≤ quittingJointSurvivalWeight roots start fuel +
        ∑ t ∈ Finset.range fuel,
          quittingJointSurvivalWeight roots start t *
            quittingRootOpponentAbsorptionMass (roots (start + t)) who
  · have hsmall : 3 * εrow / ρ ≤ εout := by
      have hεrowρ : εrow ≤ εout * ρ / 3 := min_le_right _ _
      rw [div_le_iff₀ hρ0]
      nlinarith
    exact Or.inl fun start =>
      (isεAsymptoticNash_quittingRootSequenceProfile_of_active_of_tendsto
        roots hεrow0.le hρ0 hvanish hperfect hactive start).mono hsmall
  · push Not at hactive
    obtain ⟨who, start, fuel, hquiet⟩ := hactive
    obtain ⟨anchor, window, hwindow, hanchorPos, hη'⟩ :=
      exists_quietWindow_anchor roots who hρ0 hρhalf start fuel hquiet
    have hrepair := isεAsymptoticNash_soloStationary_of_quietWindow hunit
      roots who anchor window hεrow0.le hreward (hperfect anchor)
      hanchorPos hwindow (le_of_le_of_eq hη' hηdef.symm) hMη
    have hεrowHalf : εrow ≤ εout / 2 := min_le_left _ _
    have hsmall : εrow + 4 * M * η ≤ εout := by linarith
    exact Or.inr ⟨quittingSoloStationaryRoot who (roots anchor who),
      hrepair.mono hsmall⟩

/-- A uniform positive one-stage absorption floor implies the terminating-tail
hypothesis of the quantitative subgame dichotomy. -/
theorem quittingPerfectSequenceSubgameDichotomy_of_soloExitPreference
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (hunit : QuittingUnitSoloExit reward) :
    ∀ εout : ℝ, 0 < εout → ∃ εrow : ℝ, 0 < εrow ∧
      ∀ (roots : ℕ → ι → PMF Bool) (δ : ℝ), 0 < δ →
        (∀ n, δ ≤ quittingRootAbsorptionMass (roots n)) →
        (∀ n, QuittingRowεPerfect reward
          (quittingRootSequenceTailVector reward roots (n + 1)) (roots n)
          εrow) →
        (∀ start,
          (quittingGame reward).IsεAsymptoticNash
            (quittingTerminalPayoff reward) εout
            (quittingRootSequenceProfile reward roots start)) ∨
          ∃ root : ι → PMF Bool,
            (quittingGame reward).IsεAsymptoticNash
              (quittingTerminalPayoff reward) εout
              (quittingStationaryProfile reward root) := by
  intro εout hεout
  obtain ⟨εrow, hεrow, hdichotomy⟩ :=
    quittingPerfectSequenceSubgameDichotomy_of_soloExitPreference_of_tendsto
      hunit εout hεout
  refine ⟨εrow, hεrow, ?_⟩
  intro roots δ hδ0 hfloor hperfect
  have hδ1 : δ ≤ 1 := by
    have h0 := hfloor 0
    have h1 : quittingRootAbsorptionMass (roots 0) ≤ 1 := by
      unfold quittingRootAbsorptionMass
      linarith [quittingStationaryContinueMass_nonneg (roots 0)]
    linarith
  have hbase0 : 0 ≤ 1 - δ := by linarith
  have hbase1 : 1 - δ < 1 := by linarith
  have hvanish : ∀ start,
      Tendsto (quittingJointSurvivalWeight roots start) atTop (nhds 0) := by
    intro start
    exact squeeze_zero
      (fun fuel ↦ quittingJointSurvivalWeight_nonneg roots start fuel)
      (fun fuel ↦ quittingJointSurvivalWeight_le_pow roots hδ1 hfloor start fuel)
      (tendsto_pow_atTop_nhds_zero_of_lt_one hbase0 hbase1)
  exact hdichotomy roots hvanish hperfect

/-- **Perfect-sequence extraction under unit solo exit.** A uniformly
absorbing perfect sequence yields a terminal approximate equilibrium. Capped
joint exit is needed only to construct such sequences, not for extraction. -/
theorem quittingPerfectSequenceExtraction_of_soloExitPreference
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (hunit : QuittingUnitSoloExit reward) :
    QuittingPerfectSequenceExtraction reward := by
  intro εout hεout
  obtain ⟨εrow, hεrow0, hdichotomy⟩ :=
    quittingPerfectSequenceSubgameDichotomy_of_soloExitPreference
      hunit εout hεout
  refine ⟨εrow, hεrow0, ?_⟩
  intro roots δ hδ0 hfloor hperfect
  rcases hdichotomy roots δ hδ0 hfloor hperfect with hsequence | hstationary
  · exact ⟨quittingRootSequenceProfile reward roots 0, hsequence 0⟩
  · obtain ⟨root, hroot⟩ := hstationary
    exact ⟨quittingStationaryProfile reward root, hroot⟩

/-- **Periodic subgame-perfect sequence extraction.** Periodicity is
preserved in the active branch, while the stationary branch becomes a
constant period-one root sequence. -/
theorem quittingPeriodicPerfectSequenceSubgameExtraction_of_soloExitPreference
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (hunit : QuittingUnitSoloExit reward) :
    ∀ εout : ℝ, 0 < εout → ∃ εrow : ℝ, 0 < εrow ∧
      ∀ (roots : ℕ → ι → PMF Bool) (δ : ℝ) (period : ℕ), 0 < δ →
        0 < period →
        (∀ n, roots (n + period) = roots n) →
        (∀ n, δ ≤ quittingRootAbsorptionMass (roots n)) →
        (∀ n, QuittingRowεPerfect reward
          (quittingRootSequenceTailVector reward roots (n + 1)) (roots n)
          εrow) →
        ∃ resultRoots : ℕ → ι → PMF Bool,
          (∃ resultPeriod : ℕ, 0 < resultPeriod ∧
            ∀ n, resultRoots (n + resultPeriod) = resultRoots n) ∧
          ∀ start,
            (quittingGame reward).IsεAsymptoticNash
              (quittingTerminalPayoff reward) εout
              (quittingRootSequenceProfile reward resultRoots start) := by
  intro εout hεout
  obtain ⟨εrow, hεrow0, hdichotomy⟩ :=
    quittingPerfectSequenceSubgameDichotomy_of_soloExitPreference
      hunit εout hεout
  refine ⟨εrow, hεrow0, ?_⟩
  intro roots δ period hδ0 hperiod0 hperiodic hfloor hperfect
  rcases hdichotomy roots δ hδ0 hfloor hperfect with hsequence | hstationary
  · exact ⟨roots, ⟨period, hperiod0, hperiodic⟩, hsequence⟩
  · obtain ⟨root, hroot⟩ := hstationary
    refine ⟨fun _ => root, ⟨1, by norm_num, fun _ => rfl⟩, fun start => ?_⟩
    have hprofile : quittingRootSequenceProfile reward (fun _ => root) start =
        quittingStationaryProfile reward root := by
      funext player time history
      rfl
    rw [hprofile]
    exact hroot

/-- **Cyclic subgame-perfect terminal equilibrium.** Under the paper's solo
exit assumptions, every positive tolerance admits a periodic root sequence
whose every tail is a terminal approximate Nash profile. -/
theorem exists_cyclic_subgamePerfectTerminalNash_of_soloExitPreference
    [Nonempty ι] {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (hunit : QuittingUnitSoloExit reward)
    (hcap : QuittingCappedJointExit reward)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (roots : ℕ → ι → PMF Bool) (period : ℕ), 0 < period ∧
      (∀ n, roots (n + period) = roots n) ∧
      ∀ start,
        (quittingGame reward).IsεAsymptoticNash
          (quittingTerminalPayoff reward) ε
          (quittingRootSequenceProfile reward roots start) := by
  obtain ⟨εrow, hεrow0, hextract⟩ :=
    quittingPeriodicPerfectSequenceSubgameExtraction_of_soloExitPreference
      hunit ε hε
  obtain ⟨roots, δ, period, hδ0, hperiod0, hperiodic, hfloor, hperfect⟩ :=
    exists_periodic_quittingPerfectAbsorbingRootSequence_of_soloExitPreference
      hunit hcap hεrow0
  obtain ⟨resultRoots, ⟨resultPeriod, hresultPeriod0, hresultPeriodic⟩,
      hsubgame⟩ :=
    hextract roots δ period hδ0 hperiod0 hperiodic hfloor hperfect
  exact ⟨resultRoots, resultPeriod, hresultPeriod0, hresultPeriodic, hsubgame⟩

/-- **The Solan–Vieille existence law, unconditionally** (Solan and Vieille,
*Quitting games*, Math. Oper. Res. 26 (2001), Theorem 1.2, profile-level
form).  Every finite quitting game with unit solo exit and capped joint exit
has a uniform `ε`-equilibrium at every positive `ε`. -/
theorem quittingCappedJointExitUniformεExistence_holds :
    QuittingCappedJointExitUniformεExistence ι :=
  quittingCappedJointExitUniformεExistence_of_perfectSequenceExtraction
    fun _reward hunit _hcap =>
      quittingPerfectSequenceExtraction_of_soloExitPreference hunit

/-- **Solan–Vieille tables have a uniform-equilibrium payoff.**  One fixed
payoff target closes the quitting conjecture's notion for every table with
unit solo exit and capped joint exit. -/
theorem exists_uniformEquilibriumPayoff_of_soloExitPreference
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (hunit : QuittingUnitSoloExit reward)
    (hcap : QuittingCappedJointExit reward) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff :=
  exists_uniformEquilibriumPayoff_of_cappedJointExit
    quittingCappedJointExitUniformεExistence_holds hunit hcap

end GameTheory
