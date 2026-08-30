/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.Analysis.SummableTailAverage
import Research.Quitting.PaidCapMaximalOneStepRegeneration

/-!
# Canonical positive-absorption paid/reset rays

A recursively coherent sequence of positive maximal-root regenerations retains
more than strict real-valued debt descent.  The paid scalar, every unrestricted
terminal-semantic debt coordinate, and the inherited part of one fixed reset
incidence are all transported by the same joint Continue products.

The positive global minimum keeps those products uniformly away from zero,
while the maximal-root absorption masses are summable.  Consequently the
positive-debt support, normalized debt vector, observer, reset labels, and paid
row orientation cannot orient this recursion by a finite rank; every sufficiently
late block of the canonical maximal-prefix ray has arbitrarily small total
absorption charge.

This is a conditional boundary theorem.  It does not construct the ray, a
charged return outside the ray, terminal approximate Nash profiles, or a
positive-minimum counterexample table.
-/

noncomputable section

namespace GameTheory

open Filter Finset Math.Probability Math.PMFProduct

namespace QuittingPaidCapLiftedSource

variable
  {ι : Type} [Fintype ι] [DecidableEq ι]
  {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- One recursively coherent infinite sequence of the canonical positive
maximal-root successor records.  The reset labels are fixed throughout; the
complete actual law and a fresh fixed-law dispatch remain available inside
every stored step. -/
structure CanonicalMaximalPositiveRay
    (initial : QuittingPaidCapLiftedSource reward)
    (resetOwner other : ι) where
  source : ℕ → QuittingPaidCapLiftedSource reward
  source_zero : source 0 = initial
  step : ∀ time,
    (source time).MaximalOneStepPaidResetRegeneration resetOwner other
  source_succ : ∀ time, source (time + 1) = (step time).descendant
  initial_reset : quittingTerminalSemanticDebt
    (quittingTerminalSemanticPair reward initial.profile) resetOwner = 0
  initial_incidence : 0 <
    quittingTerminalOpponentIncidenceMass resetOwner other
      (quittingTerminalOutcomeMass reward initial.profile)

namespace CanonicalMaximalPositiveRay

variable
  {initial : QuittingPaidCapLiftedSource reward}
  {resetOwner other : ι}

/-- The maximal exact root used at one recursive source. -/
def root
    (ray : CanonicalMaximalPositiveRay initial resetOwner other)
    (time : ℕ) : ι → PMF Bool :=
  quittingMaximalCapPrefixRoot reward (ray.source time).profile

/-- Joint Continue mass of one recursive maximal root. -/
def continueMass
    (ray : CanonicalMaximalPositiveRay initial resetOwner other)
    (time : ℕ) : ℝ :=
  quittingStationaryContinueMass (ray.root time)

/-- One-stage absorption mass of the recursive maximal root. -/
def absorption
    (ray : CanonicalMaximalPositiveRay initial resetOwner other)
    (time : ℕ) : ℝ :=
  quittingRootAbsorptionMass (ray.root time)

/-- Joint survival product through the first `time` recursive roots. -/
def survival
    (ray : CanonicalMaximalPositiveRay initial resetOwner other)
    (time : ℕ) : ℝ :=
  ∏ index ∈ Finset.range time, ray.continueMass index

/-- Total unrestricted terminal-semantic debt of the actual source at one
recursive stage. -/
def totalDebt
    (ray : CanonicalMaximalPositiveRay initial resetOwner other)
    (time : ℕ) : ℝ :=
  (ray.source time).initialDebt

/-- One unrestricted terminal-semantic debt coordinate. -/
def coordinateDebt
    (ray : CanonicalMaximalPositiveRay initial resetOwner other)
    (time : ℕ) (who : ι) : ℝ :=
  quittingTerminalSemanticDebt
    (quittingTerminalSemanticPair reward (ray.source time).profile) who

/-- The canonical paid scalar retained by the source record. -/
def paidGain
    (ray : CanonicalMaximalPositiveRay initial resetOwner other)
    (time : ℕ) : ℝ :=
  (ray.source time).gain

/-- Aggregate reset-owner/opponent incidence of the actual source law.  This is
not a marked-date causal atom. -/
def resetIncidence
    (ray : CanonicalMaximalPositiveRay initial resetOwner other)
    (time : ℕ) : ℝ :=
  quittingTerminalOpponentIncidenceMass resetOwner other
    (quittingTerminalOutcomeMass reward (ray.source time).profile)

@[simp] theorem source_zero_eq
    (ray : CanonicalMaximalPositiveRay initial resetOwner other) :
    ray.source 0 = initial :=
  ray.source_zero

@[simp] theorem survival_zero
    (ray : CanonicalMaximalPositiveRay initial resetOwner other) :
    ray.survival 0 = 1 := by
  simp [survival]

theorem survival_succ
    (ray : CanonicalMaximalPositiveRay initial resetOwner other)
    (time : ℕ) :
    ray.survival (time + 1) =
      ray.survival time * ray.continueMass time := by
  simp [survival, Finset.prod_range_succ]

theorem absorption_eq_one_sub_continueMass
    (ray : CanonicalMaximalPositiveRay initial resetOwner other)
    (time : ℕ) :
    ray.absorption time = 1 - ray.continueMass time := by
  rfl

theorem continueMass_pos
    (ray : CanonicalMaximalPositiveRay initial resetOwner other)
    (time : ℕ) :
    0 < ray.continueMass time := by
  simpa [continueMass, root] using (ray.step time).root_continue_pos

theorem absorption_pos
    (ray : CanonicalMaximalPositiveRay initial resetOwner other)
    (time : ℕ) :
    0 < ray.absorption time := by
  simpa [absorption, root] using (ray.step time).root_absorption_pos

theorem continueMass_lt_one
    (ray : CanonicalMaximalPositiveRay initial resetOwner other)
    (time : ℕ) :
    ray.continueMass time < 1 := by
  have habsorption := ray.absorption_pos time
  rw [ray.absorption_eq_one_sub_continueMass time] at habsorption
  linarith

theorem survival_pos
    (ray : CanonicalMaximalPositiveRay initial resetOwner other) :
    ∀ time, 0 < ray.survival time := by
  intro time
  induction time with
  | zero => simp
  | succ time ih =>
      rw [ray.survival_succ]
      exact mul_pos ih (ray.continueMass_pos time)

/-- Every actual recursive source uses the same stored global minimum. -/
theorem source_minimum_eq
    (ray : CanonicalMaximalPositiveRay initial resetOwner other) :
    ∀ time, (ray.source time).minimum = initial.minimum := by
  intro time
  induction time with
  | zero => exact congrArg QuittingPaidCapLiftedSource.minimum ray.source_zero
  | succ time ih =>
      rw [ray.source_succ time, (ray.step time).descendant_minimum, ih]

/-- The paid observer label is unchanged along the canonical recursion. -/
theorem source_observer_eq
    (ray : CanonicalMaximalPositiveRay initial resetOwner other) :
    ∀ time, (ray.source time).observer = initial.observer := by
  intro time
  induction time with
  | zero => exact congrArg QuittingPaidCapLiftedSource.observer ray.source_zero
  | succ time ih =>
      rw [ray.source_succ time, (ray.step time).descendant_observer, ih]

/-- Every recursive source profile is the literal profile-indexed maximal
prefix of the initial actual profile. -/
theorem source_profile_eq
    (ray : CanonicalMaximalPositiveRay initial resetOwner other) :
    ∀ time, (ray.source time).profile =
      quittingMaximalCapPrefixProfile reward initial.profile time := by
  intro time
  induction time with
  | zero =>
      simpa using congrArg QuittingPaidCapLiftedSource.profile ray.source_zero
  | succ time ih =>
      rw [ray.source_succ time, (ray.step time).descendant_profile]
      simp only [quittingMaximalCapPrefixProfile_succ,
        quittingMaximalCapPrefixProfile_zero]
      rw [ih]

/-- One-step exact total-debt scaling. -/
theorem totalDebt_succ
    (ray : CanonicalMaximalPositiveRay initial resetOwner other)
    (time : ℕ) :
    ray.totalDebt (time + 1) =
      ray.continueMass time * ray.totalDebt time := by
  unfold totalDebt
  rw [ray.source_succ time]
  simpa [continueMass, root] using
    (ray.step time).descendant_initialDebt

/-- One-step exact coordinatewise debt scaling. -/
theorem coordinateDebt_succ
    (ray : CanonicalMaximalPositiveRay initial resetOwner other)
    (time : ℕ) (who : ι) :
    ray.coordinateDebt (time + 1) who =
      ray.continueMass time * ray.coordinateDebt time who := by
  unfold coordinateDebt
  rw [ray.source_succ time]
  simpa [continueMass, root] using
    (ray.step time).descendant_debt_coordinate who

/-- One-step exact canonical paid-scalar scaling. -/
theorem paidGain_succ
    (ray : CanonicalMaximalPositiveRay initial resetOwner other)
    (time : ℕ) :
    ray.paidGain (time + 1) =
      ray.continueMass time * ray.paidGain time := by
  unfold paidGain
  rw [ray.source_succ time]
  simpa [continueMass, root] using (ray.step time).descendant_gain

/-- Prefix absorption may add aggregate incidence, but the inherited incidence
is transported by the same joint Continue mass. -/
theorem continueMass_mul_resetIncidence_le_succ
    (ray : CanonicalMaximalPositiveRay initial resetOwner other)
    (time : ℕ) :
    ray.continueMass time * ray.resetIncidence time ≤
      ray.resetIncidence (time + 1) := by
  unfold resetIncidence
  rw [ray.source_succ time]
  simpa [continueMass, root] using
    (ray.step time).reset_incidence_lower

/-- The fixed reset coordinate remains literally zero at every actual source. -/
theorem reset_debt_eq_zero
    (ray : CanonicalMaximalPositiveRay initial resetOwner other) :
    ∀ time,
      quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward (ray.source time).profile)
        resetOwner = 0 := by
  intro time
  cases time with
  | zero => simpa [ray.source_zero] using ray.initial_reset
  | succ time =>
      rw [ray.source_succ time]
      exact (ray.step time).reset_debt

/-- The fixed incidence coordinate remains strictly positive at every actual
source. -/
theorem resetIncidence_pos
    (ray : CanonicalMaximalPositiveRay initial resetOwner other) :
    ∀ time, 0 < ray.resetIncidence time := by
  intro time
  cases time with
  | zero => simpa [resetIncidence, ray.source_zero] using ray.initial_incidence
  | succ time =>
      unfold resetIncidence
      rw [ray.source_succ time]
      exact (ray.step time).reset_incidence

/-- Exact total-debt product formula. -/
theorem totalDebt_eq_survival_mul_initial
    (ray : CanonicalMaximalPositiveRay initial resetOwner other) :
    ∀ time,
      ray.totalDebt time = ray.survival time * initial.initialDebt := by
  intro time
  induction time with
  | zero => simp [totalDebt, ray.source_zero]
  | succ time ih =>
      rw [ray.totalDebt_succ, ih, ray.survival_succ]
      ring

/-- Exact coordinatewise debt product formula. -/
theorem coordinateDebt_eq_survival_mul_initial
    (ray : CanonicalMaximalPositiveRay initial resetOwner other) :
    ∀ time who,
      ray.coordinateDebt time who = ray.survival time *
        quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward initial.profile) who := by
  intro time who
  induction time with
  | zero => simp [coordinateDebt, ray.source_zero]
  | succ time ih =>
      rw [ray.coordinateDebt_succ, ih, ray.survival_succ]
      ring

/-- Exact canonical paid-scalar product formula. -/
theorem paidGain_eq_survival_mul_initial
    (ray : CanonicalMaximalPositiveRay initial resetOwner other) :
    ∀ time,
      ray.paidGain time = ray.survival time * initial.gain := by
  intro time
  induction time with
  | zero => simp [paidGain, ray.source_zero]
  | succ time ih =>
      rw [ray.paidGain_succ, ih, ray.survival_succ]
      ring

/-- Aggregate incidence dominates its inherited product-scaled contribution. -/
theorem survival_mul_initialIncidence_le_resetIncidence
    (ray : CanonicalMaximalPositiveRay initial resetOwner other) :
    ∀ time,
      ray.survival time *
          quittingTerminalOpponentIncidenceMass resetOwner other
            (quittingTerminalOutcomeMass reward initial.profile) ≤
        ray.resetIncidence time := by
  intro time
  induction time with
  | zero => simp [resetIncidence, ray.source_zero]
  | succ time ih =>
      calc
        ray.survival (time + 1) *
              quittingTerminalOpponentIncidenceMass resetOwner other
                (quittingTerminalOutcomeMass reward initial.profile) =
            ray.continueMass time *
              (ray.survival time *
                quittingTerminalOpponentIncidenceMass resetOwner other
                  (quittingTerminalOutcomeMass reward initial.profile)) := by
              rw [ray.survival_succ]
              ring
        _ ≤ ray.continueMass time * ray.resetIncidence time :=
          mul_le_mul_of_nonneg_left ih (ray.continueMass_pos time).le
        _ ≤ ray.resetIncidence (time + 1) :=
          ray.continueMass_mul_resetIncidence_le_succ time

/-- The same positive global minimum is below every actual recursive debt. -/
theorem minimumDebt_le_totalDebt
    (ray : CanonicalMaximalPositiveRay initial resetOwner other)
    (time : ℕ) :
    quittingTerminalSemanticDebtSum initial.minimum ≤ ray.totalDebt time := by
  have hminimum := (ray.source time).minimum_le_initialDebt
  rw [ray.source_minimum_eq time] at hminimum
  exact hminimum

/-- The joint survival product is uniformly bounded below by the global
minimum-to-initial debt ratio. -/
theorem reachFloor_le_survival
    (ray : CanonicalMaximalPositiveRay initial resetOwner other)
    (time : ℕ) :
    initial.reachFloor ≤ ray.survival time := by
  have hminimum := ray.minimumDebt_le_totalDebt time
  rw [ray.totalDebt_eq_survival_mul_initial time] at hminimum
  apply (div_le_iff₀ initial.initialDebt_pos).2
  simpa [QuittingPaidCapLiftedSource.reachFloor, mul_comm] using hminimum

/-- The canonical paid annotation therefore has one fixed positive lower
bound along the whole ray. -/
theorem reachFloor_mul_gain_le_paidGain
    (ray : CanonicalMaximalPositiveRay initial resetOwner other)
    (time : ℕ) :
    initial.reachFloor * initial.gain ≤ ray.paidGain time := by
  rw [ray.paidGain_eq_survival_mul_initial time]
  exact mul_le_mul_of_nonneg_right
    (ray.reachFloor_le_survival time) initial.gain_pos.le

/-- The inherited part of the fixed incidence also has one positive uniform
lower bound. -/
theorem reachFloor_mul_initialIncidence_le_resetIncidence
    (ray : CanonicalMaximalPositiveRay initial resetOwner other)
    (time : ℕ) :
    initial.reachFloor *
        quittingTerminalOpponentIncidenceMass resetOwner other
          (quittingTerminalOutcomeMass reward initial.profile) ≤
      ray.resetIncidence time := by
  exact (mul_le_mul_of_nonneg_right
      (ray.reachFloor_le_survival time)
      (quittingTerminalOpponentIncidenceMass_outcomeMass_nonneg
        reward initial.profile resetOwner other)).trans
    (ray.survival_mul_initialIncidence_le_resetIncidence time)

/-- Positive-debt support is exactly constant along the canonical ray. -/
theorem coordinateDebt_pos_iff_initial
    (ray : CanonicalMaximalPositiveRay initial resetOwner other)
    (time : ℕ) (who : ι) :
    0 < ray.coordinateDebt time who ↔
      0 < quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward initial.profile) who := by
  rw [ray.coordinateDebt_eq_survival_mul_initial time who]
  constructor
  · intro hproduct
    by_contra hnot
    have hnonpos : quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward initial.profile) who ≤ 0 :=
      le_of_not_gt hnot
    have hle : ray.survival time *
        quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward initial.profile) who ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (ray.survival_pos time).le hnonpos
    exact (not_lt_of_ge hle) hproduct
  · exact mul_pos (ray.survival_pos time)

/-- The normalized debt vector is exactly constant. -/
theorem coordinateDebt_div_totalDebt_eq_initial
    (ray : CanonicalMaximalPositiveRay initial resetOwner other)
    (time : ℕ) (who : ι) :
    ray.coordinateDebt time who / ray.totalDebt time =
      quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward initial.profile) who /
        initial.initialDebt := by
  rw [ray.coordinateDebt_eq_survival_mul_initial time who,
    ray.totalDebt_eq_survival_mul_initial time]
  field_simp [(ray.survival_pos time).ne', initial.initialDebt_pos.ne']

/-- The recursive source profiles are exactly the existing deterministic
profile-indexed maximal-prefix chronology, so its absorption theorem applies
without replacing any actual source. -/
theorem absorption_summable
    (ray : CanonicalMaximalPositiveRay initial resetOwner other) :
    Summable ray.absorption := by
  have hsummable := summable_maximalCapPrefix_absorption
    reward initial.minimum initial.profile initial.minimum_le initial.minimum_pos
  apply hsummable.congr
  intro time
  simp only [absorption, root]
  rw [ray.source_profile_eq time]

/-- Every late tail of the canonical maximal-prefix absorption clock tends to
zero.  This concerns only this recursive ray, not other roots or admissible
paths available from the same source. -/
theorem futureAbsorption_tendsto_zero
    (ray : CanonicalMaximalPositiveRay initial resetOwner other) :
    Tendsto (fun start ↦ ∑' offset, ray.absorption (start + offset))
      atTop (nhds 0) := by
  have hsum := ray.absorption_summable
  have hprefix : Tendsto (fun start ↦
      ∑ time ∈ Finset.range start, ray.absorption time) atTop
      (nhds (∑' time, ray.absorption time)) :=
    hsum.hasSum.tendsto_sum_nat
  have hconst : Tendsto (fun _ : ℕ ↦ ∑' time, ray.absorption time)
      atTop (nhds (∑' time, ray.absorption time)) := tendsto_const_nhds
  have htail := hconst.sub hprefix
  apply htail.congr'
  filter_upwards [] with start
  have hsplit := hsum.sum_add_tsum_nat_add start
  linarith

/-- The four-player descendants themselves remain uniformly separated from
terminal approximate Nash profiles.  This does not exclude a different
profile construction. -/
theorem exists_coordinateDebt_ge_minimum_div_four
    (ray : CanonicalMaximalPositiveRay
      (ι := Fin 4) initial resetOwner other)
    (time : ℕ) :
    ∃ who : Fin 4,
      quittingTerminalSemanticDebtSum initial.minimum / 4 ≤
        ray.coordinateDebt time who := by
  have hsum : quittingTerminalSemanticDebtSum initial.minimum ≤
      ∑ who : Fin 4, ray.coordinateDebt time who := by
    simpa [totalDebt, coordinateDebt,
      QuittingPaidCapLiftedSource.initialDebt,
      quittingTerminalSemanticDebtSum] using ray.minimumDebt_le_totalDebt time
  by_contra hnot
  push Not at hnot
  have hstrict : ∀ who : Fin 4,
      ray.coordinateDebt time who <
        quittingTerminalSemanticDebtSum initial.minimum / 4 := hnot
  have hsumStrict :
      (∑ who : Fin 4, ray.coordinateDebt time who) <
        ∑ _who : Fin 4,
          quittingTerminalSemanticDebtSum initial.minimum / 4 := by
    exact Finset.sum_lt_sum (fun who _ ↦ (hstrict who).le)
      ⟨0, Finset.mem_univ 0, hstrict 0⟩
  have hcard : (∑ _who : Fin 4,
      quittingTerminalSemanticDebtSum initial.minimum / 4) =
      quittingTerminalSemanticDebtSum initial.minimum := by
    norm_num
  rw [hcard] at hsumStrict
  linarith

end CanonicalMaximalPositiveRay

end QuittingPaidCapLiftedSource

end GameTheory
