/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/
import UniformEquilibrium.Quitting.RewardBound
import FableThinSliceToken

/-!
# Separating the two debt minima and the ratio-chamber paid port

This file formalizes sections 9 and 10 of the note
`math/notes/SOCIAL_WEIGHT_REVIEW__CERTIFIED_THIN_SLICE_DEBT_TOKEN_ROTATION.md`,
in the scope confirmed by its two `PASS` reviews.

Throughout, the global exploitability certificate is the *hypothesis*
`FableCertifiedExploitabilityFloor reward eta` of `FableThinSliceToken`: every
actual behavior profile has some player whose semantic debt is at least `eta`.
Nothing here proves that any reward table has such a certificate.  Write
`M = quittingRewardBound reward` for the canonical finite reward scale.

The note's two infima
`eta = inf_sigma max_i d_i(sigma)` and `D_* = inf_sigma sum_i d_i(sigma)`
are handled in their equivalent per-profile forms: a certificate is the lower
bound defining `eta`, and a universally quantified lower bound on
`quittingTerminalSemanticDebtSum` is a lower bound on `D_*`.  No infimum is
assumed to be attained.

Results:

* **Approximate response.**  For every profile, mover and `zeta > 0` some
  behavioral replacement leaves the mover with debt below `zeta`.  This uses
  only that the behavioral cap is the supremum of the deviation payoffs; no
  cap attainment is asserted anywhere in this file.
* **Global debt bound.**  Every semantic debt coordinate of an actual profile
  is at most `2 * M`.
* **Per-profile exclusion (34)-(40).**  If `0 <= h` and
  `h ^ 2 + 4 * M * h - eta ^ 2 < 0`, then no actual profile has total debt at
  most `eta + h`.
* **Separation (33).**  Every actual profile has total debt at least
  `eta + (Real.sqrt (4 * M ^ 2 + eta ^ 2) - 2 * M)`, and that gap is strictly
  positive whenever `0 < eta`.
* **Ratio chamber (41)-(42).**  If an actual profile has total debt below
  `2 * eta`, then its maximal debt `a` strictly exceeds `eta`, and a
  replacement by that player with residual mover debt `e < eta` has total debt
  at least `S + (a - e) * (2 * eta - S) / (a - eta)`.  The exact-response form
  `e = 0` is the note's first bound in (42) and the `S`-form is its second.

The nonmover crossing step of section 10 is proved here *without* the note's
continuity/pigeonhole passage: the chord bound and the two-debtor bound are
both affine in the chord parameter, so only an affine limit at the crossing
parameter is needed, and that is the elementary lemma
`fableDebtMinima_affine_limit_nonneg`.

* **Attainment-free port.**  `fableDebtPort_exists_response_near_port`: the
  exact port bound is approached to any accuracy by actual behavioral
  replacements, with no best-response attainment hypothesis.  This is the
  correction requested in section 5 of the paired-hull review.

The carrier passage (47)-(55) of section 10 is *not* formalized here.  The
uniform attainment-free per-index bound the note's sequence argument would take
limits of is `fableDebtPort_exists_response_debtSum_le`; the limiting
statements (54)-(55) and the compactification producing a carrier target point
are not formalized, and no carrier minimum is used anywhere in this file.
-/

noncomputable section

namespace GameTheory

open StochasticGame QuittingBoundaryHolonomy

/-! ## 0. Real-arithmetic kernels

These lemmas carry all the analysis used below.  They mention no game data. -/

/-- An affine function of `theta` which is nonnegative strictly past `lo` is
nonnegative at `lo`.  This replaces the note's appeal to continuity at the
chord crossing parameter. -/
theorem fableDebtMinima_affine_limit_nonneg {lo c k : ℝ} (hlo : lo < 1)
    (hpast : ∀ theta : ℝ, lo < theta → theta ≤ 1 → 0 ≤ c + theta * k) :
    0 ≤ c + lo * k := by
  by_contra hneg
  rw [not_le] at hneg
  have hslack : 0 < -(c + lo * k) := by linarith
  have habs : (0 : ℝ) < 2 * (|k| + 1) := by positivity
  have hquotient : 0 < -(c + lo * k) / (2 * (|k| + 1)) := by positivity
  obtain ⟨eps, hepsDef⟩ :
      ∃ x : ℝ, x = min (1 - lo) (-(c + lo * k) / (2 * (|k| + 1))) := ⟨_, rfl⟩
  have hepsPos : 0 < eps := by
    rw [hepsDef]
    exact lt_min (by linarith) hquotient
  have hepsLe : eps ≤ 1 - lo := by
    rw [hepsDef]
    exact min_le_left _ _
  have hepsSmall : eps * (2 * (|k| + 1)) ≤ -(c + lo * k) := by
    rw [← le_div_iff₀ habs, hepsDef]
    exact min_le_right _ _
  have hmain := hpast (lo + eps) (by linarith) (by linarith)
  have hexpand : c + (lo + eps) * k = c + lo * k + eps * k := by ring
  rw [hexpand] at hmain
  have hkle : eps * k ≤ eps * (|k| + 1) :=
    mul_le_mul_of_nonneg_left (by linarith [le_abs_self k]) hepsPos.le
  linarith

/-- Solving the chord inequality at the mover's `eta` crossing parameter.  The
hypothesis is the note's (44)-(45) in affine form; the conclusion is the first
bound of (42) with a residual mover debt `e`. -/
theorem fableDebtPort_arith {eta a e s t : ℝ} (he : e < eta) (ha : eta < a)
    (hchord : ∀ theta : ℝ, (a - eta) / (a - e) < theta → theta ≤ 1 →
      (1 - theta) * a + theta * e + eta ≤ (1 - theta) * s + theta * t) :
    s + (a - e) * (2 * eta - s) / (a - eta) ≤ t := by
  have hgap : 0 < a - e := by linarith
  have hgapne : a - e ≠ 0 := ne_of_gt hgap
  have hden : 0 < a - eta := by linarith
  have hlo : (a - eta) / (a - e) < 1 := by
    rw [div_lt_one hgap]
    linarith
  have hpast : ∀ theta : ℝ, (a - eta) / (a - e) < theta → theta ≤ 1 →
      0 ≤ s - a - eta + theta * (t - s + a - e) := by
    intro theta hlow hhigh
    have hstep := hchord theta hlow hhigh
    linarith
  have hlimit := fableDebtMinima_affine_limit_nonneg hlo hpast
  have hscaled := mul_nonneg hlimit hgap.le
  have hrewrite : (s - a - eta + (a - eta) / (a - e) * (t - s + a - e)) * (a - e) =
      (s - a - eta) * (a - e) + (a - eta) / (a - e) * (a - e) * (t - s + a - e) := by
    ring
  have hcancel : (a - eta) / (a - e) * (a - e) = a - eta := by
    field_simp
  rw [hrewrite, hcancel] at hscaled
  have hquotient : (a - e) * (2 * eta - s) / (a - eta) ≤ t - s := by
    rw [div_le_iff₀ hden]
    nlinarith [hscaled]
  linarith

/-- The ratio monotonicity closing (42): `x / (x - eta)` decreases, so the
maximal-debt form of the port bound dominates its total-debt form. -/
theorem fableDebtPort_ratio_mono {eta a s : ℝ} (heta : 0 < eta) (ha : eta < a)
    (has : a ≤ s) (hs : s < 2 * eta) :
    s * (2 * eta - s) / (s - eta) ≤ a * (2 * eta - s) / (a - eta) := by
  have hs0 : 0 < s - eta := by linarith
  have ha0 : 0 < a - eta := by linarith
  rw [div_le_div_iff₀ hs0 ha0]
  nlinarith [mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * eta - s) heta.le)
    (by linarith : (0 : ℝ) ≤ s - a)]

/-- Weakening the residual mover debt in the port bound. -/
theorem fableDebtPort_response_mono {eta a e zeta s : ℝ} (ha : eta < a)
    (hez : e < zeta) (hs : s ≤ 2 * eta) :
    (a - zeta) * (2 * eta - s) / (a - eta) ≤ (a - e) * (2 * eta - s) / (a - eta) := by
  have hden : 0 < a - eta := by linarith
  rw [div_le_div_iff₀ hden hden]
  nlinarith [mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ zeta - e)
    (by linarith : (0 : ℝ) ≤ 2 * eta - s)) hden.le]

/-- A small enough residual mover debt loses at most `epsilon` of the exact
port bound. -/
theorem fableDebtPort_near_port_arith {eta a s zeta epsilon : ℝ} (ha : eta < a)
    (hs : s < 2 * eta) (hzeta : zeta ≤ epsilon * (a - eta) / (2 * eta - s)) :
    a * (2 * eta - s) / (a - eta) - epsilon ≤ (a - zeta) * (2 * eta - s) / (a - eta) := by
  have hden : 0 < a - eta := by linarith
  have hnum : 0 < 2 * eta - s := by linarith
  rw [le_div_iff₀ hnum] at hzeta
  have hdiff : a * (2 * eta - s) / (a - eta) - (a - zeta) * (2 * eta - s) / (a - eta) =
      zeta * (2 * eta - s) / (a - eta) := by
    ring
  have hbound : zeta * (2 * eta - s) / (a - eta) ≤ epsilon := by
    rw [div_le_iff₀ hden]
    linarith
  linarith

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## 1. Uniform debt bounds and approximate responses -/

/-- **U0'.**  Every semantic debt coordinate of an actual profile is bounded by
twice the canonical reward scale: the cap and the prescribed payoff are both
bounded by `quittingRewardBound reward`. -/
theorem fableDebtMinima_debt_le_two_mul_rewardBound
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι) :
    quittingTerminalSemanticDebt (quittingTerminalSemanticPair reward profile) who ≤
      2 * quittingRewardBound reward := by
  have hcap := le_of_abs_le (abs_quittingContinuationBestResponseValue_le reward profile who
    (abs_reward_le_quittingRewardBound reward))
  have hpayoff := neg_le_of_abs_le
    (abs_quittingTerminalPayoff_le_quittingRewardBound reward profile who)
  dsimp only [quittingTerminalSemanticDebt, quittingTerminalSemanticPair]
  linarith

/-- Total semantic debt of an actual profile is nonnegative. -/
theorem fableDebtMinima_debtSum_nonneg
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) :
    0 ≤ quittingTerminalSemanticDebtSum (quittingTerminalSemanticPair reward profile) := by
  unfold quittingTerminalSemanticDebtSum
  exact Finset.sum_nonneg fun who _ => fableThinSlice_debt_nonneg reward profile who

/-- Two distinct nonnegative debt coordinates are together bounded by the total
debt. -/
theorem fableDebtMinima_add_le_debtSum
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (first second : ι)
    (hne : first ≠ second) :
    quittingTerminalSemanticDebt (quittingTerminalSemanticPair reward profile) first +
        quittingTerminalSemanticDebt (quittingTerminalSemanticPair reward profile) second ≤
      quittingTerminalSemanticDebtSum (quittingTerminalSemanticPair reward profile) := by
  unfold quittingTerminalSemanticDebtSum
  have hsub : ∑ who ∈ ({first, second} : Finset ι),
        quittingTerminalSemanticDebt (quittingTerminalSemanticPair reward profile) who ≤
      ∑ who : ι, quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward profile) who :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun who _ _ => fableThinSlice_debt_nonneg reward profile who)
  rw [Finset.sum_pair hne] at hsub
  exact hsub

/-- **U0.**  Approximate behavioral best responses exist at every accuracy.
The behavioral cap is the supremum of the unilateral deviation payoffs over a
nonempty bounded-above range, and replacing the mover's own strategy leaves
that cap fixed, so a near-supremal deviation is a low-debt replacement.  No cap
attainment is asserted. -/
theorem fableDebtMinima_exists_response_debt_lt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (mover : ι)
    {zeta : ℝ} (hzeta : 0 < zeta) :
    ∃ target : (quittingGame reward).BehaviorStrategy mover,
      quittingTerminalSemanticDebt (quittingTerminalSemanticPair reward
        (Function.update profile mover target)) mover < zeta := by
  obtain ⟨target, htarget⟩ :=
    exists_quittingContinuation_deviation_ge_sub reward profile mover
      (δ := zeta / 2) (by linarith)
  refine ⟨target, ?_⟩
  have hcap := fableThinSlice_replacement_cap_eq reward profile mover target
  dsimp only [quittingTerminalSemanticDebt, quittingTerminalSemanticPair]
  rw [hcap]
  linarith

/-! ## 2. Chord packaging -/

/-- The complete stopping-law chord, packaged as an *actual* profile whose
mover coordinate is exactly affine and whose every coordinate lies below the
endpoint chord.  Both facts are consumed from `FableThinSliceToken`, which in
turn consumes the production convexity file. -/
theorem fableDebtMinima_exists_chord_profile
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (mover : ι)
    (target : (quittingGame reward).BehaviorStrategy mover)
    (theta : ℝ) (htheta0 : 0 ≤ theta) (htheta1 : theta ≤ 1) :
    ∃ chord : (quittingGame reward).BehaviorProfile,
      quittingTerminalSemanticDebt (quittingTerminalSemanticPair reward chord) mover =
          (1 - theta) * quittingTerminalSemanticDebt
              (quittingTerminalSemanticPair reward profile) mover +
            theta * quittingTerminalSemanticDebt (quittingTerminalSemanticPair reward
              (Function.update profile mover target)) mover ∧
        ∀ observer, quittingTerminalSemanticDebt
            (quittingTerminalSemanticPair reward chord) observer ≤
          (1 - theta) * quittingTerminalSemanticDebt
              (quittingTerminalSemanticPair reward profile) observer +
            theta * quittingTerminalSemanticDebt (quittingTerminalSemanticPair reward
              (Function.update profile mover target)) observer := by
  refine ⟨fableThinSliceChordProfile reward profile mover target theta htheta0 htheta1,
    fableThinSliceChord_debt_mover_eq reward profile mover target theta htheta0 htheta1,
    fun observer => ?_⟩
  exact fableThinSliceChord_debt_le reward profile mover target theta htheta0 htheta1 observer

omit [DecidableEq ι] in
/-- Total debt is bounded by the chord of the total debts, since every
coordinate is. -/
theorem fableDebtMinima_debtSum_le_of_chordwise
    (first second third : QuittingTerminalSemanticPair ι) (theta : ℝ)
    (hchord : ∀ who, quittingTerminalSemanticDebt first who ≤
      (1 - theta) * quittingTerminalSemanticDebt second who +
        theta * quittingTerminalSemanticDebt third who) :
    quittingTerminalSemanticDebtSum first ≤
      (1 - theta) * quittingTerminalSemanticDebtSum second +
        theta * quittingTerminalSemanticDebtSum third := by
  unfold quittingTerminalSemanticDebtSum
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun who _ => hchord who

/-- The certificate forbids a chord point all of whose coordinates are bounded
by chord values strictly below `eta`. -/
theorem fableDebtMinima_chord_not_all_lt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (eta : ℝ)
    (hcert : FableCertifiedExploitabilityFloor reward eta)
    (profile : (quittingGame reward).BehaviorProfile) (mover : ι)
    (target : (quittingGame reward).BehaviorStrategy mover)
    (theta : ℝ) (htheta0 : 0 ≤ theta) (htheta1 : theta ≤ 1)
    (hmover : (1 - theta) * quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward profile) mover +
        theta * quittingTerminalSemanticDebt (quittingTerminalSemanticPair reward
          (Function.update profile mover target)) mover < eta)
    (hother : ∀ observer, observer ≠ mover →
      (1 - theta) * quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward profile) observer +
        theta * quittingTerminalSemanticDebt (quittingTerminalSemanticPair reward
          (Function.update profile mover target)) observer < eta) :
    False := by
  obtain ⟨chord, hchordMover, hchordAll⟩ :=
    fableDebtMinima_exists_chord_profile reward profile mover target theta htheta0 htheta1
  obtain ⟨witness, hwitness⟩ := hcert chord
  by_cases hcase : witness = mover
  · subst hcase
    rw [hchordMover] at hwitness
    linarith
  · have hbound := (hchordAll witness).trans_lt (hother witness hcase)
    linarith

/-! ## 3. Section 9: the per-profile exclusion and the separation -/

/-- **U1**, the note's (34)-(40).  Under a certificate at scale `eta`, if
`0 <= h` and the quadratic condition `h ^ 2 + 4 * M * h - eta ^ 2 < 0` holds,
then no actual profile has total debt at most `eta + h`.

The chord parameter lives in the note's interval
`h / (eta + h) < theta < (eta - h) / (4 * M)`, which the quadratic condition
makes nonempty.  The nonmover coordinates are controlled by the chord bound
together with the global `2 * M` debt bound, not by a Lipschitz estimate. -/
theorem fableDebtMinima_add_lt_debtSum
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (eta h : ℝ) (heta : 0 < eta)
    (hh : 0 ≤ h)
    (hquad : h ^ 2 + 4 * quittingRewardBound reward * h - eta ^ 2 < 0)
    (hcert : FableCertifiedExploitabilityFloor reward eta)
    (profile : (quittingGame reward).BehaviorProfile) :
    eta + h < quittingTerminalSemanticDebtSum (quittingTerminalSemanticPair reward profile) := by
  by_contra hcontra
  rw [not_lt] at hcontra
  have hMnonneg := quittingRewardBound_nonneg reward
  obtain ⟨principal, hprincipal⟩ := hcert profile
  have hprincipalBound := fableDebtMinima_debt_le_two_mul_rewardBound reward profile principal
  have hMpos : 0 < quittingRewardBound reward := by linarith
  have hsourcePrincipal : quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward profile) principal ≤ eta + h :=
    (fableThinSlice_debt_le_debtSum reward profile principal).trans hcontra
  have hsourceOther : ∀ who, who ≠ principal →
      quittingTerminalSemanticDebt (quittingTerminalSemanticPair reward profile) who ≤ h :=
    fun who hwho => fableThinSlice_debt_le_of_ne_principal reward profile eta h principal
      hcontra hprincipal who hwho
  -- The note's interval (40) is nonempty.
  have hsum : (0 : ℝ) < eta + h := by linarith
  have hscale : (0 : ℝ) < 4 * quittingRewardBound reward := by linarith
  have hinterval : h / (eta + h) < (eta - h) / (4 * quittingRewardBound reward) := by
    rw [div_lt_div_iff₀ hsum hscale]
    nlinarith [hquad]
  obtain ⟨theta, hthetaLow, hthetaHigh⟩ := exists_between hinterval
  have hthetaPos : 0 < theta := lt_of_le_of_lt (div_nonneg hh hsum.le) hthetaLow
  rw [div_lt_iff₀ hsum] at hthetaLow
  rw [lt_div_iff₀ hscale] at hthetaHigh
  have hthetaLe : theta ≤ 1 := by nlinarith
  have hone : (0 : ℝ) ≤ 1 - theta := by linarith
  have hstrict : (1 - theta) * (eta + h) < eta := by linarith
  -- The accuracy of the mover's approximate response is chosen after `theta`.
  obtain ⟨zeta, hzetaDef⟩ : ∃ z : ℝ, z = (eta - (1 - theta) * (eta + h)) / 2 := ⟨_, rfl⟩
  have hzetaPos : 0 < zeta := by
    rw [hzetaDef]
    linarith
  obtain ⟨target, htarget⟩ :=
    fableDebtMinima_exists_response_debt_lt reward profile principal hzetaPos
  refine fableDebtMinima_chord_not_all_lt reward eta hcert profile principal target theta
    hthetaPos.le hthetaLe ?_ ?_
  · have hmoverSource := mul_le_mul_of_nonneg_left hsourcePrincipal hone
    have hmoverTarget := mul_le_mul_of_nonneg_left htarget.le hthetaPos.le
    have hshrink : theta * zeta ≤ zeta := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hthetaLe) hzetaPos.le]
    linarith
  · intro observer hobserver
    have hchordSource := mul_le_mul_of_nonneg_left (hsourceOther observer hobserver) hone
    have hchordTarget := mul_le_mul_of_nonneg_left
      (fableDebtMinima_debt_le_two_mul_rewardBound reward
        (Function.update profile principal target) observer) hthetaPos.le
    have hshrink : 0 ≤ theta * h := mul_nonneg hthetaPos.le hh
    have hhalf : 0 ≤ quittingRewardBound reward * theta :=
      mul_nonneg hMnonneg hthetaPos.le
    linarith

/-- **U2**, the note's boxed separation (33).  Under a certificate at scale
`eta`, every actual profile has total debt at least
`eta + (Real.sqrt (4 * M ^ 2 + eta ^ 2) - 2 * M)`.  Equivalently, the minimum
total debt exceeds the minimum maximum-coordinate debt by a fixed amount on the
reward scale. -/
theorem fableDebtMinima_sqrt_separation
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (eta : ℝ) (heta : 0 < eta)
    (hcert : FableCertifiedExploitabilityFloor reward eta)
    (profile : (quittingGame reward).BehaviorProfile) :
    eta + (Real.sqrt (4 * quittingRewardBound reward ^ 2 + eta ^ 2) -
        2 * quittingRewardBound reward) ≤
      quittingTerminalSemanticDebtSum (quittingTerminalSemanticPair reward profile) := by
  have hMnonneg := quittingRewardBound_nonneg reward
  obtain ⟨principal, hprincipal⟩ := hcert profile
  have hle := fableThinSlice_debt_le_debtSum reward profile principal
  have hgap : 0 ≤ quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPair reward profile) - eta := by linarith
  have hquad : 0 ≤ (quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward profile) - eta) ^ 2 +
      4 * quittingRewardBound reward * (quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward profile) - eta) - eta ^ 2 := by
    by_contra hneg
    rw [not_le] at hneg
    have hexclude :=
      fableDebtMinima_add_lt_debtSum reward eta _ heta hgap hneg hcert profile
    linarith
  have hnonneg : 0 ≤ quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPair reward profile) - eta +
      2 * quittingRewardBound reward := by linarith
  have hroot : Real.sqrt (4 * quittingRewardBound reward ^ 2 + eta ^ 2) ≤
      quittingTerminalSemanticDebtSum (quittingTerminalSemanticPair reward profile) - eta +
        2 * quittingRewardBound reward := by
    rw [Real.sqrt_le_left hnonneg]
    nlinarith [hquad]
  linarith

omit [DecidableEq ι] in
/-- The separation gap of (33) is strictly positive at a positive certificate
scale, for every reward table. -/
theorem fableDebtMinima_sqrt_separation_pos
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (eta : ℝ) (heta : 0 < eta) :
    0 < Real.sqrt (4 * quittingRewardBound reward ^ 2 + eta ^ 2) -
      2 * quittingRewardBound reward := by
  have hMnonneg := quittingRewardBound_nonneg reward
  have hlt : 2 * quittingRewardBound reward <
      Real.sqrt (4 * quittingRewardBound reward ^ 2 + eta ^ 2) := by
    rw [Real.lt_sqrt (by linarith)]
    nlinarith
  linarith

/-! ## 4. Section 10: the off-minimum paid port -/

/-- **U3, first part.**  The note's `a > eta`.  Below the two-debtor threshold
`S < 2 * eta`, a maximal debtor with an available replacement of residual debt
below `eta` has debt strictly above `eta`.

The proof is continuity-free: below the threshold every nonmover source debt is
already bounded by `S - eta < eta`, so a single explicit chord parameter pushes
every coordinate strictly below `eta`. -/
theorem fableDebtPort_lt_maxDebt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (eta : ℝ) (heta : 0 < eta)
    (hcert : FableCertifiedExploitabilityFloor reward eta)
    (profile : (quittingGame reward).BehaviorProfile) (mover : ι)
    (hmax : ∀ i, quittingTerminalSemanticDebt (quittingTerminalSemanticPair reward profile) i ≤
      quittingTerminalSemanticDebt (quittingTerminalSemanticPair reward profile) mover)
    (hthreshold : quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPair reward profile) < 2 * eta)
    (target : (quittingGame reward).BehaviorStrategy mover)
    (hresponse : quittingTerminalSemanticDebt (quittingTerminalSemanticPair reward
      (Function.update profile mover target)) mover < eta) :
    eta < quittingTerminalSemanticDebt (quittingTerminalSemanticPair reward profile) mover := by
  have hMnonneg := quittingRewardBound_nonneg reward
  obtain ⟨witness, hwitness⟩ := hcert profile
  have hge := hwitness.trans (hmax witness)
  rcases lt_or_eq_of_le hge with hlt | heq
  · exact hlt
  · exfalso
    have hmoverBound := fableDebtMinima_debt_le_two_mul_rewardBound reward profile mover
    have hMpos : 0 < quittingRewardBound reward := by linarith
    have hmoverLe := fableThinSlice_debt_le_debtSum reward profile mover
    have hsumNonneg := fableDebtMinima_debtSum_nonneg reward profile
    have hother : ∀ who, who ≠ mover →
        quittingTerminalSemanticDebt (quittingTerminalSemanticPair reward profile) who ≤
          quittingTerminalSemanticDebtSum (quittingTerminalSemanticPair reward profile) -
            eta :=
      fun who hwho => fableThinSlice_debt_le_of_ne_principal reward profile eta
        (quittingTerminalSemanticDebtSum (quittingTerminalSemanticPair reward profile) - eta)
        mover (by linarith) heq.le who hwho
    have hslack : (0 : ℝ) < 2 * eta - quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward profile) := by linarith
    have hscale : (0 : ℝ) < 4 * quittingRewardBound reward := by linarith
    obtain ⟨theta, hthetaPos, hthetaHigh⟩ := exists_between (div_pos hslack hscale)
    rw [lt_div_iff₀ hscale] at hthetaHigh
    have hthetaLe : theta ≤ 1 := by nlinarith
    refine fableDebtMinima_chord_not_all_lt reward eta hcert profile mover target theta
      hthetaPos.le hthetaLe ?_ ?_
    · rw [← heq]
      have hprod := mul_pos hthetaPos (sub_pos.mpr hresponse)
      linarith
    · intro observer hobserver
      have hchordSource := mul_le_mul_of_nonneg_left (hother observer hobserver)
        (by linarith : (0 : ℝ) ≤ 1 - theta)
      have hchordTarget := mul_le_mul_of_nonneg_left
        (fableDebtMinima_debt_le_two_mul_rewardBound reward
          (Function.update profile mover target) observer) hthetaPos.le
      have hshrink : 0 ≤ theta * (quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward profile) - eta) :=
        mul_nonneg hthetaPos.le (by linarith)
      have hhalf : 0 ≤ quittingRewardBound reward * theta :=
        mul_nonneg hMnonneg hthetaPos.le
      linarith

/-- The two-debtor bound at a chord point strictly past the mover's `eta`
crossing: a nonmover then carries debt at least `eta`, while the mover's own
debt is exactly the affine chord value, and total debt is bounded by the chord
of the endpoint totals. -/
theorem fableDebtPort_chord_two_debtor_bound
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (eta : ℝ)
    (hcert : FableCertifiedExploitabilityFloor reward eta)
    (profile : (quittingGame reward).BehaviorProfile) (mover : ι)
    (target : (quittingGame reward).BehaviorStrategy mover)
    (theta : ℝ) (htheta0 : 0 ≤ theta) (htheta1 : theta ≤ 1)
    (hcross : (1 - theta) * quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward profile) mover +
        theta * quittingTerminalSemanticDebt (quittingTerminalSemanticPair reward
          (Function.update profile mover target)) mover < eta) :
    (1 - theta) * quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward profile) mover +
        theta * quittingTerminalSemanticDebt (quittingTerminalSemanticPair reward
          (Function.update profile mover target)) mover + eta ≤
      (1 - theta) * quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward profile) +
        theta * quittingTerminalSemanticDebtSum (quittingTerminalSemanticPair reward
          (Function.update profile mover target)) := by
  obtain ⟨chord, hchordMover, hchordAll⟩ :=
    fableDebtMinima_exists_chord_profile reward profile mover target theta htheta0 htheta1
  obtain ⟨witness, hwitness⟩ := hcert chord
  have hne : witness ≠ mover := by
    rintro rfl
    rw [hchordMover] at hwitness
    linarith
  have hpair := fableDebtMinima_add_le_debtSum reward chord mover witness (Ne.symm hne)
  have hchordSum := fableDebtMinima_debtSum_le_of_chordwise _ _ _ theta hchordAll
  rw [hchordMover] at hpair
  linarith

/-- **U3, the port bound**, the note's (42) with a residual mover debt.  Under
a certificate at scale `eta`, an actual profile below the two-debtor threshold
and a maximal-debtor replacement whose residual mover debt is below `eta` have

`S + (a - e) * (2 * eta - S) / (a - eta) <= D(replacement)`,

where `S` is the source total debt, `a` the maximal source debt and `e` the
residual mover debt of the replacement.  No cap attainment is used. -/
theorem fableDebtPort_debtSum_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (eta : ℝ) (heta : 0 < eta)
    (hcert : FableCertifiedExploitabilityFloor reward eta)
    (profile : (quittingGame reward).BehaviorProfile) (mover : ι)
    (hmax : ∀ i, quittingTerminalSemanticDebt (quittingTerminalSemanticPair reward profile) i ≤
      quittingTerminalSemanticDebt (quittingTerminalSemanticPair reward profile) mover)
    (hthreshold : quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPair reward profile) < 2 * eta)
    (target : (quittingGame reward).BehaviorStrategy mover)
    (hresponse : quittingTerminalSemanticDebt (quittingTerminalSemanticPair reward
      (Function.update profile mover target)) mover < eta) :
    quittingTerminalSemanticDebtSum (quittingTerminalSemanticPair reward profile) +
        (quittingTerminalSemanticDebt (quittingTerminalSemanticPair reward profile) mover -
            quittingTerminalSemanticDebt (quittingTerminalSemanticPair reward
              (Function.update profile mover target)) mover) *
          (2 * eta - quittingTerminalSemanticDebtSum
            (quittingTerminalSemanticPair reward profile)) /
          (quittingTerminalSemanticDebt (quittingTerminalSemanticPair reward profile) mover -
            eta) ≤
      quittingTerminalSemanticDebtSum (quittingTerminalSemanticPair reward
        (Function.update profile mover target)) := by
  have hmaxDebt := fableDebtPort_lt_maxDebt reward eta heta hcert profile mover hmax
    hthreshold target hresponse
  refine fableDebtPort_arith hresponse hmaxDebt ?_
  intro theta hlow hhigh
  have hgap := sub_pos.mpr (hresponse.trans hmaxDebt)
  have hpositive := div_pos (sub_pos.mpr hmaxDebt) hgap
  have hthetaPos : 0 ≤ theta := le_of_lt (hpositive.trans hlow)
  rw [div_lt_iff₀ hgap] at hlow
  exact fableDebtPort_chord_two_debtor_bound reward eta hcert profile mover target theta
    hthetaPos hhigh (by linarith)

/-- **U3, exact-response form**, the first bound of the note's (42).  This is
the statement under an *explicit* exact best-response attainment hypothesis;
the general behavioral cap need not be attained. -/
theorem fableDebtPort_debtSum_le_of_exact
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (eta : ℝ) (heta : 0 < eta)
    (hcert : FableCertifiedExploitabilityFloor reward eta)
    (profile : (quittingGame reward).BehaviorProfile) (mover : ι)
    (hmax : ∀ i, quittingTerminalSemanticDebt (quittingTerminalSemanticPair reward profile) i ≤
      quittingTerminalSemanticDebt (quittingTerminalSemanticPair reward profile) mover)
    (hthreshold : quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPair reward profile) < 2 * eta)
    (target : (quittingGame reward).BehaviorStrategy mover)
    (hbest : quittingTerminalSemanticDebt (quittingTerminalSemanticPair reward
      (Function.update profile mover target)) mover = 0) :
    quittingTerminalSemanticDebtSum (quittingTerminalSemanticPair reward profile) +
        quittingTerminalSemanticDebt (quittingTerminalSemanticPair reward profile) mover *
          (2 * eta - quittingTerminalSemanticDebtSum
            (quittingTerminalSemanticPair reward profile)) /
          (quittingTerminalSemanticDebt (quittingTerminalSemanticPair reward profile) mover -
            eta) ≤
      quittingTerminalSemanticDebtSum (quittingTerminalSemanticPair reward
        (Function.update profile mover target)) := by
  have hport := fableDebtPort_debtSum_le reward eta heta hcert profile mover hmax hthreshold
    target (by rw [hbest]; exact heta)
  rw [hbest, sub_zero] at hport
  exact hport

/-- **U3, ratio form**, the second bound of the note's (42).  Under the same
explicit exact-attainment hypothesis, the port bound holds with the source
total debt in place of the maximal source debt. -/
theorem fableDebtPort_debtSum_le_of_exact_ratio
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (eta : ℝ) (heta : 0 < eta)
    (hcert : FableCertifiedExploitabilityFloor reward eta)
    (profile : (quittingGame reward).BehaviorProfile) (mover : ι)
    (hmax : ∀ i, quittingTerminalSemanticDebt (quittingTerminalSemanticPair reward profile) i ≤
      quittingTerminalSemanticDebt (quittingTerminalSemanticPair reward profile) mover)
    (hthreshold : quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPair reward profile) < 2 * eta)
    (target : (quittingGame reward).BehaviorStrategy mover)
    (hbest : quittingTerminalSemanticDebt (quittingTerminalSemanticPair reward
      (Function.update profile mover target)) mover = 0) :
    quittingTerminalSemanticDebtSum (quittingTerminalSemanticPair reward profile) +
        quittingTerminalSemanticDebtSum (quittingTerminalSemanticPair reward profile) *
          (2 * eta - quittingTerminalSemanticDebtSum
            (quittingTerminalSemanticPair reward profile)) /
          (quittingTerminalSemanticDebtSum (quittingTerminalSemanticPair reward profile) -
            eta) ≤
      quittingTerminalSemanticDebtSum (quittingTerminalSemanticPair reward
        (Function.update profile mover target)) := by
  have hport := fableDebtPort_debtSum_le_of_exact reward eta heta hcert profile mover hmax
    hthreshold target hbest
  have hmaxDebt := fableDebtPort_lt_maxDebt reward eta heta hcert profile mover hmax
    hthreshold target (by rw [hbest]; exact heta)
  have hmono := fableDebtPort_ratio_mono heta hmaxDebt
    (fableThinSlice_debt_le_debtSum reward profile mover) hthreshold
  linarith

/-- **The attainment-free packaging.**  For every accuracy `zeta` in
`(0, eta]`, some behavioral replacement by the maximal debtor has residual
mover debt below `zeta` and total debt at least
`S + (a - zeta) * (2 * eta - S) / (a - eta)`.

This is the uniform per-index content of the note's carrier passage (50)-(53).
The limiting statements (54)-(55), and the compactification producing a carrier
target point, are *not* formalized here. -/
theorem fableDebtPort_exists_response_debtSum_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (eta : ℝ) (heta : 0 < eta)
    (hcert : FableCertifiedExploitabilityFloor reward eta)
    (profile : (quittingGame reward).BehaviorProfile) (mover : ι)
    (hmax : ∀ i, quittingTerminalSemanticDebt (quittingTerminalSemanticPair reward profile) i ≤
      quittingTerminalSemanticDebt (quittingTerminalSemanticPair reward profile) mover)
    (hthreshold : quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPair reward profile) < 2 * eta)
    (zeta : ℝ) (hzeta : 0 < zeta) (hzetaLe : zeta ≤ eta) :
    ∃ target : (quittingGame reward).BehaviorStrategy mover,
      quittingTerminalSemanticDebt (quittingTerminalSemanticPair reward
          (Function.update profile mover target)) mover < zeta ∧
        quittingTerminalSemanticDebtSum (quittingTerminalSemanticPair reward profile) +
            (quittingTerminalSemanticDebt
                (quittingTerminalSemanticPair reward profile) mover - zeta) *
              (2 * eta - quittingTerminalSemanticDebtSum
                (quittingTerminalSemanticPair reward profile)) /
              (quittingTerminalSemanticDebt
                (quittingTerminalSemanticPair reward profile) mover - eta) ≤
          quittingTerminalSemanticDebtSum (quittingTerminalSemanticPair reward
            (Function.update profile mover target)) := by
  obtain ⟨target, htarget⟩ :=
    fableDebtMinima_exists_response_debt_lt reward profile mover hzeta
  have hresponse := htarget.trans_le hzetaLe
  have hport := fableDebtPort_debtSum_le reward eta heta hcert profile mover hmax hthreshold
    target hresponse
  have hmaxDebt := fableDebtPort_lt_maxDebt reward eta heta hcert profile mover hmax
    hthreshold target hresponse
  have hmono := fableDebtPort_response_mono hmaxDebt htarget hthreshold.le
  exact ⟨target, htarget, by linarith⟩

/-- **The attainment-free form of the note's boxed (42)/(46).**  Below the
two-debtor threshold, the exact port bound
`S + a * (2 * eta - S) / (a - eta)` is approached by actual behavioral
replacements of the maximal debtor to any accuracy `epsilon > 0`, with no
best-response attainment hypothesis.

This is the correction asked for in section 5 of the paired-hull review:
unrestricted stopping-law caps are not asserted to be attained. -/
theorem fableDebtPort_exists_response_near_port
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (eta : ℝ) (heta : 0 < eta)
    (hcert : FableCertifiedExploitabilityFloor reward eta)
    (profile : (quittingGame reward).BehaviorProfile) (mover : ι)
    (hmax : ∀ i, quittingTerminalSemanticDebt (quittingTerminalSemanticPair reward profile) i ≤
      quittingTerminalSemanticDebt (quittingTerminalSemanticPair reward profile) mover)
    (hthreshold : quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPair reward profile) < 2 * eta)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ target : (quittingGame reward).BehaviorStrategy mover,
      quittingTerminalSemanticDebt (quittingTerminalSemanticPair reward
          (Function.update profile mover target)) mover < eta ∧
        quittingTerminalSemanticDebtSum (quittingTerminalSemanticPair reward profile) +
            quittingTerminalSemanticDebt
                (quittingTerminalSemanticPair reward profile) mover *
              (2 * eta - quittingTerminalSemanticDebtSum
                (quittingTerminalSemanticPair reward profile)) /
              (quittingTerminalSemanticDebt
                (quittingTerminalSemanticPair reward profile) mover - eta) -
            epsilon ≤
          quittingTerminalSemanticDebtSum (quittingTerminalSemanticPair reward
            (Function.update profile mover target)) := by
  obtain ⟨seed, hseed⟩ := fableDebtMinima_exists_response_debt_lt reward profile mover heta
  have hmaxDebt := fableDebtPort_lt_maxDebt reward eta heta hcert profile mover hmax
    hthreshold seed hseed
  have hden : (0 : ℝ) < quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward profile) mover - eta := by linarith
  have hnum : (0 : ℝ) < 2 * eta - quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPair reward profile) := by linarith
  obtain ⟨zeta, hzetaDef⟩ : ∃ z : ℝ, z = min eta (epsilon * (quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward profile) mover - eta) /
    (2 * eta - quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPair reward profile))) := ⟨_, rfl⟩
  have hzetaPos : 0 < zeta := by
    rw [hzetaDef]
    exact lt_min heta (div_pos (mul_pos hepsilon hden) hnum)
  have hzetaLe : zeta ≤ eta := by
    rw [hzetaDef]
    exact min_le_left _ _
  have hzetaSmall : zeta ≤ epsilon * (quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward profile) mover - eta) /
    (2 * eta - quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPair reward profile)) := by
    rw [hzetaDef]
    exact min_le_right _ _
  obtain ⟨target, htarget, hport⟩ := fableDebtPort_exists_response_debtSum_le reward eta heta
    hcert profile mover hmax hthreshold zeta hzetaPos hzetaLe
  have hnear := fableDebtPort_near_port_arith hmaxDebt hthreshold hzetaSmall
  exact ⟨target, htarget.trans_le hzetaLe, by linarith⟩

end GameTheory
