/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Cycles.CompanionTransport
import UniformEquilibrium.Quitting.Bellman.Finite.BellmanTelescope
import MathUE.DirectedTransport.MaxAffine.Paths

/-!
# Signed max-affine transport of relaxed cycle gain

Fix a coordinate, a sequence of quitting roots, and a scalar prescribed-value
path satisfying `IsQuittingLivePrescribedValue`. Recenter each companion map
around the prescribed path. Its two branches have signed intercepts

`αₖ = (1 - pₖ) gₖ` and `βₖ = -pₖ gₖ`,

and slope equal to the opponents' one-stage survival probability. These data
form `quittingSignedCompanionLabel`; a finite backward recursion is exactly the
action of the chronological composite of these labels.

For a window of `m + 1` phases, the composite label has floor
`quittingSignedStopGap`, shift `quittingSignedContinueGap`, and slope
`quittingOpponentSurvivalWeight`. Thus the entire phasewise recursion reduces
to one scalar max-affine equation. When the survival product is below one, its
unique fixed discrepancy is

`max {stopGap, continueGap / (1 - survival)}`.

This quantity is `quittingRelaxedCycleGain`. The fixed-point identity and its
uniqueness require only prescribed-value consistency and cyclic wraparound;
no complementarity or Nash hypothesis enters the algebra. In particular,
`quittingRelaxedCycleGain_eq_zero_iff` characterizes exactly when the prescribed
base value is already fixed by the one-period companion composite.

The behavioral interpretation uses the pure-time extremality and periodic
Bellman theorems in `PeriodicPureTimeBellman`: for a periodic live-root
profile, the literal supremum over unilateral behavioral deviations is the
prescribed base value plus this gain.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.ProbabilityMassFunction

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## The two signed local weights -/

/-- The **stopping weight** `α_k = (1 - p_k) * g_k`: the signed excess of quitting
outright at phase `k`, relative to the prescribed value `prescribed k`, where
`g_k = quittingRootEndpointDifference reward (fun _ => prescribed (k + 1)) (roots k) who`
is the local gap between quitting and continuing. -/
def quittingSignedStopWeight
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (prescribed : ℕ → ℝ) (who : ι) (k : ℕ) : ℝ :=
  (1 - (roots k who true).toReal) *
    quittingRootEndpointDifference reward (fun _ => prescribed (k + 1)) (roots k) who

/-- The **continuation weight** `β_k = -p_k * g_k`: the signed excess charged for
continuing through phase `k` rather than matching the prescribed mixture there. -/
def quittingSignedContinueWeight
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (prescribed : ℕ → ℝ) (who : ι) (k : ℕ) : ℝ :=
  -(roots k who true).toReal *
    quittingRootEndpointDifference reward (fun _ => prescribed (k + 1)) (roots k) who

/-- The signed max-affine label of one companion step recentered around the
prescribed path. -/
def quittingSignedCompanionLabel
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (prescribed : ℕ → ℝ)
    (who : ι) (time : ℕ) : Math.MaxAffineTransport.Label :=
  ⟨(quittingSignedStopWeight reward roots prescribed who time : WithBot ℝ),
    quittingSignedContinueWeight reward roots prescribed who time,
    quittingRootDeletedContinueMass (roots time) who⟩

@[simp] theorem quittingSignedCompanionLabel_apply
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (prescribed : ℕ → ℝ)
    (who : ι) (time : ℕ) (discrepancy : ℝ) :
    (quittingSignedCompanionLabel reward roots prescribed who time).apply discrepancy =
      max (quittingSignedStopWeight reward roots prescribed who time)
        (quittingSignedContinueWeight reward roots prescribed who time +
          quittingRootDeletedContinueMass (roots time) who * discrepancy) := rfl

theorem quittingSignedCompanionLabel_slope_nonneg
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (prescribed : ℕ → ℝ)
    (who : ι) (time : ℕ) :
    0 ≤ (quittingSignedCompanionLabel reward roots prescribed who time).slope :=
  quittingRootDeletedContinueMass_nonneg (roots time) who

/-- Backward chronological signed labels of a companion window. -/
def quittingSignedCompanionLabelList
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (prescribed : ℕ → ℝ)
    (who : ι) (start : ℕ) : ℕ → List Math.MaxAffineTransport.Label
  | 0 => []
  | fuel + 1 =>
      quittingSignedCompanionLabelList reward roots prescribed who (start + 1) fuel ++
        [quittingSignedCompanionLabel reward roots prescribed who start]

/-! ## The finite unrolled stop and continuation excess -/

/-- The best signed excess obtainable by continuing for some `ℓ ≤ m` phases starting at
`k` and then stopping, i.e. `max_{0 ≤ ℓ ≤ m} H_{k,ℓ}` in the reported notation.  The
window has `m + 1` phases; `m` (rather than a `period` requiring `Nat` subtraction) is
the natural induction variable. -/
def quittingSignedStopGap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (prescribed : ℕ → ℝ) (who : ι) : ℕ → ℕ → ℝ
  | k, 0 => quittingSignedStopWeight reward roots prescribed who k
  | k, m + 1 =>
      max (quittingSignedStopWeight reward roots prescribed who k)
        (quittingSignedContinueWeight reward roots prescribed who k +
          quittingRootDeletedContinueMass (roots k) who *
            quittingSignedStopGap reward roots prescribed who (k + 1) m)

/-- The signed excess of continuing through all `m + 1` phases starting at `k`, i.e.
`B_k` in the reported notation. -/
def quittingSignedContinueGap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (prescribed : ℕ → ℝ) (who : ι) : ℕ → ℕ → ℝ
  | k, 0 => quittingSignedContinueWeight reward roots prescribed who k
  | k, m + 1 =>
      quittingSignedContinueWeight reward roots prescribed who k +
        quittingRootDeletedContinueMass (roots k) who *
          quittingSignedContinueGap reward roots prescribed who (k + 1) m

/-- Exact coefficient normal form of a nonempty signed companion window. -/
theorem quittingSignedCompanionLabelList_compList
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (prescribed : ℕ → ℝ)
    (who : ι) : ∀ (m k : ℕ),
    Math.MaxAffineTransport.Label.compList
        (quittingSignedCompanionLabelList reward roots prescribed who k (m + 1)) =
      ⟨(quittingSignedStopGap reward roots prescribed who k m : WithBot ℝ),
        quittingSignedContinueGap reward roots prescribed who k m,
        quittingOpponentSurvivalWeight roots who k (m + 1)⟩ := by
  intro m
  induction m with
  | zero =>
      intro k
      simp only [quittingSignedCompanionLabelList]
      rw [
        Math.MaxAffineTransport.Label.compList_append_singleton,
        Math.MaxAffineTransport.Label.compList_nil,
        Math.MaxAffineTransport.Label.comp_id]
      apply Math.MaxAffineTransport.Label.ext <;>
        simp [quittingSignedCompanionLabel, quittingSignedStopGap,
          quittingSignedContinueGap, quittingOpponentSurvivalWeight,
          quittingRootDeletedContinueMass_eq_fixedOpponents]
  | succ m ih =>
      intro k
      rw [quittingSignedCompanionLabelList,
        Math.MaxAffineTransport.Label.compList_append_singleton,
        ih (k + 1)]
      apply Math.MaxAffineTransport.Label.ext
      · simp only [Math.MaxAffineTransport.Label.floor_comp,
          quittingSignedCompanionLabel, Math.MaxAffineTransport.Label.pushFloor_coe,
          quittingSignedStopGap]
        rw [← WithBot.coe_sup]
      · simp only [Math.MaxAffineTransport.Label.shift_comp,
          quittingSignedCompanionLabel, quittingSignedContinueGap]
      · simp only [Math.MaxAffineTransport.Label.slope_comp,
          quittingSignedCompanionLabel]
        rw [quittingRootDeletedContinueMass_eq_fixedOpponents]
        exact (quittingOpponentSurvivalWeight_succ_left
          roots who k (m + 1)).symm

/-! ## The signed phasewise accumulation -/

/-- The **signed phasewise accumulation**, the reported `Q_{i,1}`: the larger of the best
finite stopping excess and the geometric continue-forever excess over the survival
product of a period of length `m + 1`. -/
def quittingRelaxedCycleGain
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (prescribed : ℕ → ℝ) (who : ι) (m : ℕ) : ℝ :=
  max (quittingSignedStopGap reward roots prescribed who 0 m)
    (quittingSignedContinueGap reward roots prescribed who 0 m /
      (1 - quittingOpponentSurvivalWeight roots who 0 (m + 1)))

/-! ## The per-step algebraic identity -/

/-- **One companion-map step, relative to the prescribed value.**  Purely algebraic:
consumes only the value recursion `hprescribed`, no complementarity or Nash hypothesis. -/
theorem quittingRootCompanionMap_sub_prescribed_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (prescribed : ℕ → ℝ)
    (hprescribed : IsQuittingLivePrescribedValue reward roots who prescribed)
    (k : ℕ) (c : ℝ) :
    quittingRootCompanionMap reward (roots k) who c - prescribed k =
      max (quittingSignedStopWeight reward roots prescribed who k)
        (quittingSignedContinueWeight reward roots prescribed who k +
          quittingRootDeletedContinueMass (roots k) who * (c - prescribed (k + 1))) := by
  have hp := hprescribed k
  rw [quittingRootSuccessorPayoff_eq_endpointMix, quittingRootQuitPayoff_eq_deletedQuitValue,
    quittingRootContinuePayoff_eq_deleted] at hp
  have hsum := quittingRoot_continueProbability_add_quitProbability (roots k) who
  have hqneg : (roots k who false).toReal = 1 - (roots k who true).toReal := by linarith
  rw [hqneg] at hp
  unfold quittingRootCompanionMap quittingSignedStopWeight quittingSignedContinueWeight
    quittingRootEndpointDifference
  rw [quittingRootQuitPayoff_eq_deletedQuitValue, quittingRootContinuePayoff_eq_deleted,
    ← max_sub_sub_right]
  congr 1
  · linear_combination -hp
  · linear_combination -hp

/-- One companion step recentered around the prescribed path is exactly the
action of its signed max-affine label. -/
theorem quittingRootCompanionMap_sub_prescribed_eq_signedLabel_apply
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (prescribed : ℕ → ℝ)
    (hprescribed : IsQuittingLivePrescribedValue reward roots who prescribed)
    (time : ℕ) (discrepancy : ℝ) :
    quittingRootCompanionMap reward (roots time) who
          (prescribed (time + 1) + discrepancy) - prescribed time =
      (quittingSignedCompanionLabel reward roots prescribed who time).apply
        discrepancy := by
  rw [quittingSignedCompanionLabel_apply]
  have hstep := quittingRootCompanionMap_sub_prescribed_eq
    reward roots who prescribed hprescribed time
      (prescribed (time + 1) + discrepancy)
  rw [show prescribed (time + 1) + discrepancy - prescribed (time + 1) =
    discrepancy by ring] at hstep
  exact hstep

/-! ## The finite unrolled identity -/

/-- **The finite unrolled identity.**  By induction on the window length `m + 1`: the
one-period companion composite, applied at any real continuation `c` and compared against
the prescribed value at the window's start, equals the signed max-affine expression built
from the stop and continuation gaps.  Purely algebraic; only `hprescribed` is used, no
complementarity or Nash hypothesis anywhere. -/
theorem quittingCompanionComposite_sub_prescribed_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (prescribed : ℕ → ℝ)
    (hprescribed : IsQuittingLivePrescribedValue reward roots who prescribed) :
    ∀ (m k : ℕ) (c : ℝ),
      quittingCompanionComposite reward roots who k (m + 1) c - prescribed k =
        max (quittingSignedStopGap reward roots prescribed who k m)
          (quittingSignedContinueGap reward roots prescribed who k m +
            quittingOpponentSurvivalWeight roots who k (m + 1) *
              (c - prescribed (k + (m + 1)))) := by
  intro m
  induction m with
  | zero =>
      intro k c
      have hstep := quittingRootCompanionMap_sub_prescribed_eq reward roots who prescribed
        hprescribed k c
      rw [quittingCompanionComposite_succ, quittingCompanionComposite_zero] at *
      rw [hstep]
      have hweight : quittingOpponentSurvivalWeight roots who k 1 =
          quittingRootDeletedContinueMass (roots k) who := by
        rw [quittingRootDeletedContinueMass_eq_fixedOpponents]
        simp [quittingOpponentSurvivalWeight]
      rw [hweight]
      rfl
  | succ m ih =>
      intro k c
      rw [quittingCompanionComposite_succ]
      have hstep := quittingRootCompanionMap_sub_prescribed_eq reward roots who prescribed
        hprescribed k (quittingCompanionComposite reward roots who (k + 1) (m + 1) c)
      rw [hstep, ih (k + 1) c]
      have hweight : quittingRootDeletedContinueMass (roots k) who *
          quittingOpponentSurvivalWeight roots who (k + 1) (m + 1) =
          quittingOpponentSurvivalWeight roots who k (m + 1 + 1) := by
        rw [quittingRootDeletedContinueMass_eq_fixedOpponents]
        exact (quittingOpponentSurvivalWeight_succ_left roots who k (m + 1)).symm
      have hindex : k + 1 + (m + 1) = k + (m + 1 + 1) := by omega
      rw [show quittingSignedStopGap reward roots prescribed who k (m + 1) =
          max (quittingSignedStopWeight reward roots prescribed who k)
            (quittingSignedContinueWeight reward roots prescribed who k +
              quittingRootDeletedContinueMass (roots k) who *
                quittingSignedStopGap reward roots prescribed who (k + 1) m) from rfl,
        show quittingSignedContinueGap reward roots prescribed who k (m + 1) =
          quittingSignedContinueWeight reward roots prescribed who k +
            quittingRootDeletedContinueMass (roots k) who *
              quittingSignedContinueGap reward roots prescribed who (k + 1) m from rfl,
        mul_max_of_nonneg _ _ (quittingRootDeletedContinueMass_nonneg (roots k) who),
        add_max, ← max_assoc, mul_add, ← mul_assoc, hweight, hindex]
      congr 1
      ring

/-- The recentered finite companion composite is the action of the composite
signed label. -/
theorem quittingCompanionComposite_sub_prescribed_eq_compList_apply
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (prescribed : ℕ → ℝ)
    (hprescribed : IsQuittingLivePrescribedValue reward roots who prescribed)
    (m k : ℕ) (continuation : ℝ) :
    quittingCompanionComposite reward roots who k (m + 1) continuation -
        prescribed k =
      (Math.MaxAffineTransport.Label.compList
        (quittingSignedCompanionLabelList reward roots prescribed who k (m + 1))).apply
          (continuation - prescribed (k + (m + 1))) := by
  rw [quittingCompanionComposite_sub_prescribed_eq
      reward roots who prescribed hprescribed m k continuation,
    quittingSignedCompanionLabelList_compList]
  rfl

/-! ## Solving the single self-referential equation -/

/-- **The scalar self-reference solves to the reported closed form.**  This is the case
split behind `quittingRelaxedCycleGain`: `max {M, N}` with `N = B / (1 - P)` is the unique
solution of `X = max {M, B + P * X}` when `P < 1`. -/
theorem quittingSignedCycleFixedPointEq (M B P : ℝ) (hP : P < 1) :
    max M (B + P * max M (B / (1 - P))) = max M (B / (1 - P)) := by
  have hpos : (0 : ℝ) < 1 - P := by linarith
  have hne : (1 : ℝ) - P ≠ 0 := ne_of_gt hpos
  rcases le_total M (B / (1 - P)) with h | h
  · rw [max_eq_right h,
      show B + P * (B / (1 - P)) = B / (1 - P) from by field_simp; ring,
      max_eq_right h]
  · rw [max_eq_left h]
    have hB : B ≤ M * (1 - P) := by rw [div_le_iff₀ hpos] at h; exact h
    exact max_eq_left (by nlinarith [hB])

/-! ## The main identity -/

/-- **The main identity.**  Adding the signed phasewise accumulation to the prescribed
value at the start of the cycle gives a fixed point of the one-period companion
composite -- the precise sense in which the signed phasewise accumulation is the gain of
a relaxed cycle.  No
complementarity or Nash hypothesis is used: only the value recursion `hprescribed`, the
wraparound `hwrap`, and the survival bound `hP`. -/
theorem quittingCompanionComposite_prescribed_add_gain_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (prescribed : ℕ → ℝ) (m : ℕ)
    (hprescribed : IsQuittingLivePrescribedValue reward roots who prescribed)
    (hwrap : prescribed (m + 1) = prescribed 0)
    (hP : quittingOpponentSurvivalWeight roots who 0 (m + 1) < 1) :
    quittingCompanionComposite reward roots who 0 (m + 1)
        (prescribed 0 + quittingRelaxedCycleGain reward roots prescribed who m) =
      prescribed 0 + quittingRelaxedCycleGain reward roots prescribed who m := by
  have hkey := quittingCompanionComposite_sub_prescribed_eq reward roots who prescribed
    hprescribed m 0 (prescribed 0 + quittingRelaxedCycleGain reward roots prescribed who m)
  simp only [zero_add] at hkey
  rw [hwrap,
    show prescribed 0 + quittingRelaxedCycleGain reward roots prescribed who m -
        prescribed 0 = quittingRelaxedCycleGain reward roots prescribed who m from by ring]
    at hkey
  have hfix := quittingSignedCycleFixedPointEq
    (quittingSignedStopGap reward roots prescribed who 0 m)
    (quittingSignedContinueGap reward roots prescribed who 0 m)
    (quittingOpponentSurvivalWeight roots who 0 (m + 1)) hP
  unfold quittingRelaxedCycleGain at hkey ⊢
  rw [hfix] at hkey
  linarith [hkey]

/-! ## Uniqueness -/

/-- **The gap is unique.**  Any real number whose sum with `prescribed 0` is a fixed point
of the one-period companion composite already equals `quittingRelaxedCycleGain`. Reuses
the existing contraction estimate `abs_iterate_quittingCompanionComposite_sub_le` from
`QuittingCycleMismatchContraction.lean`, applied at a single iterate. -/
theorem quittingRelaxedCycleGain_unique
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (prescribed : ℕ → ℝ) (m : ℕ)
    (hprescribed : IsQuittingLivePrescribedValue reward roots who prescribed)
    (hwrap : prescribed (m + 1) = prescribed 0)
    (hP : quittingOpponentSurvivalWeight roots who 0 (m + 1) < 1)
    (gap : ℝ)
    (hgap : quittingCompanionComposite reward roots who 0 (m + 1) (prescribed 0 + gap) =
      prescribed 0 + gap) :
    gap = quittingRelaxedCycleGain reward roots prescribed who m := by
  have hfixed := quittingCompanionComposite_prescribed_add_gain_eq reward roots who prescribed
    m hprescribed hwrap hP
  have hstep := abs_iterate_quittingCompanionComposite_sub_le reward roots who (m + 1)
    hfixed (prescribed 0 + gap) 1
  rw [Function.iterate_one, hgap, pow_one] at hstep
  have hcollapse : |prescribed 0 + gap -
      (prescribed 0 + quittingRelaxedCycleGain reward roots prescribed who m)| ≤
      quittingOpponentSurvivalWeight roots who 0 (m + 1) *
        |prescribed 0 + gap - (prescribed 0 + quittingRelaxedCycleGain reward roots
          prescribed who m)| := hstep
  have hP0 : 0 ≤ quittingOpponentSurvivalWeight roots who 0 (m + 1) :=
    quittingOpponentSurvivalWeight_nonneg roots who 0 (m + 1)
  have habs : |prescribed 0 + gap -
      (prescribed 0 + quittingRelaxedCycleGain reward roots prescribed who m)| = 0 := by
    nlinarith [abs_nonneg (prescribed 0 + gap -
      (prescribed 0 + quittingRelaxedCycleGain reward roots prescribed who m)), hcollapse]
  have := abs_eq_zero.mp habs
  linarith [this]

/-! ## Necessary and sufficient -/

/-- **Necessary and sufficient.**  The signed phasewise accumulation vanishes exactly when
the one-period companion composite's cyclic fixed point already coincides with the cycle's
own prescribed value at the start -- i.e. exactly when there is no gap for the companion
map (the Bellman-optimal deviation value) to correct. -/
theorem quittingRelaxedCycleGain_eq_zero_iff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (prescribed : ℕ → ℝ) (m : ℕ)
    (hprescribed : IsQuittingLivePrescribedValue reward roots who prescribed)
    (hwrap : prescribed (m + 1) = prescribed 0)
    (hP : quittingOpponentSurvivalWeight roots who 0 (m + 1) < 1) :
    quittingRelaxedCycleGain reward roots prescribed who m = 0 ↔
      quittingCompanionComposite reward roots who 0 (m + 1) (prescribed 0) = prescribed 0 := by
  constructor
  · intro hzero
    have hfixed := quittingCompanionComposite_prescribed_add_gain_eq reward roots who
      prescribed m hprescribed hwrap hP
    rw [hzero, add_zero] at hfixed
    exact hfixed
  · intro hfixed
    have hzero := quittingRelaxedCycleGain_unique reward roots who prescribed m hprescribed
      hwrap hP 0 (by rwa [add_zero])
    linarith [hzero]

end GameTheory
