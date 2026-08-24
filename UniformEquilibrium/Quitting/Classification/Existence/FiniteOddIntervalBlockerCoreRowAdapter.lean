/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import UniformEquilibrium.Quitting.Classification.Existence.FiniteOddBlockerCoreRowAdapter
import UniformEquilibrium.Quitting.Classification.Existence.FiniteOddIntervalBlockerCore

/-!
# Literal row-extrema adapter for finite odd interval blocker cores

For each embedded core owner this module computes four extrema directly from
the finite coalition table:

* the minimum and maximum continuation rewards on nonempty rows omitting it;
* the minimum Quit reward when its cyclic blocker is absent; and
* the maximum Quit reward when its cyclic blocker is present.

The strict sandwich between those four extrema supplies the stationary
interval source.  No outside payoff coordinate is inspected.
-/

noncomputable section

namespace GameTheory

open Set Math Math.Probability Math.Finset
open StochasticGame

variable {ι : Type} [Fintype ι] [DecidableEq ι]

private def finiteOddIntervalBlockerBackground
    (owner blocker : ι) : Finset ι :=
  (Finset.univ.erase owner).erase blocker

/-- Literal continuation rewards on all nonempty coalitions omitting one core
owner. -/
def finiteOddCoreContinuationRowValues
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {n : ℕ} (core : Fin n ↪ ι) (phase : Fin n) : Finset ℝ :=
  (((Finset.univ.erase (core phase)).powerset.erase ∅).image fun coalition =>
    weightOfReward reward coalition (core phase))

/-- Literal owner-Quit rewards on backgrounds omitting both the owner and its
cyclic blocker. -/
def finiteOddCoreBlockerAbsentQuitRowValues
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {n : ℕ} (core : Fin n ↪ ι) (phase : Fin n) : Finset ℝ :=
  ((finiteOddIntervalBlockerBackground
      (core phase) (core (finRotate n phase))).powerset.image fun background =>
    reward ⟨insert (core phase) background,
      Finset.insert_nonempty _ _⟩ (core phase))

/-- Literal owner-Quit rewards on the same backgrounds after inserting the
cyclic blocker. -/
def finiteOddCoreBlockerPresentQuitRowValues
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {n : ℕ} (core : Fin n ↪ ι) (phase : Fin n) : Finset ℝ :=
  ((finiteOddIntervalBlockerBackground
      (core phase) (core (finRotate n phase))).powerset.image fun background =>
    reward ⟨insert (core (finRotate n phase))
        (insert (core phase) background),
      Finset.insert_nonempty _ _⟩ (core phase))

theorem finiteOddCoreContinuationRowValues_nonempty
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {n : ℕ} (core : Fin n ↪ ι) (hn : 3 ≤ n) (phase : Fin n) :
    (finiteOddCoreContinuationRowValues reward core phase).Nonempty := by
  let blocker := core (finRotate n phase)
  have hne : blocker ≠ core phase := finiteOddBlocker_ne hn core phase
  refine ⟨weightOfReward reward {blocker} (core phase), ?_⟩
  apply Finset.mem_image.mpr
  refine ⟨{blocker}, ?_, rfl⟩
  simp [hne]

theorem finiteOddCoreBlockerAbsentQuitRowValues_nonempty
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {n : ℕ} (core : Fin n ↪ ι) (phase : Fin n) :
    (finiteOddCoreBlockerAbsentQuitRowValues reward core phase).Nonempty := by
  refine ⟨reward ⟨{core phase}, Finset.singleton_nonempty _⟩ (core phase), ?_⟩
  apply Finset.mem_image.mpr
  refine ⟨∅, Finset.empty_mem_powerset _, ?_⟩
  simp

theorem finiteOddCoreBlockerPresentQuitRowValues_nonempty
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {n : ℕ} (core : Fin n ↪ ι) (phase : Fin n) :
    (finiteOddCoreBlockerPresentQuitRowValues reward core phase).Nonempty := by
  refine ⟨reward ⟨{core phase, core (finRotate n phase)}, by simp⟩
    (core phase), ?_⟩
  apply Finset.mem_image.mpr
  refine ⟨∅, Finset.empty_mem_powerset _, ?_⟩
  simp [Finset.pair_comm]

/-- `C_i^-`: minimum literal nonempty continuation reward for a core owner. -/
def finiteOddCoreContinuationLower
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {n : ℕ} (core : Fin n ↪ ι) (hn : 3 ≤ n) (phase : Fin n) : ℝ :=
  (finiteOddCoreContinuationRowValues reward core phase).min'
    (finiteOddCoreContinuationRowValues_nonempty reward core hn phase)

/-- `C_i^+`: maximum literal nonempty continuation reward for a core owner. -/
def finiteOddCoreContinuationUpper
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {n : ℕ} (core : Fin n ↪ ι) (hn : 3 ≤ n) (phase : Fin n) : ℝ :=
  (finiteOddCoreContinuationRowValues reward core phase).max'
    (finiteOddCoreContinuationRowValues_nonempty reward core hn phase)

/-- `H_i^-`: minimum literal Quit reward when the blocker is absent. -/
def finiteOddCoreBlockerAbsentQuitLower
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {n : ℕ} (core : Fin n ↪ ι) (phase : Fin n) : ℝ :=
  (finiteOddCoreBlockerAbsentQuitRowValues reward core phase).min'
    (finiteOddCoreBlockerAbsentQuitRowValues_nonempty reward core phase)

/-- `L_i^+`: maximum literal Quit reward when the blocker is present. -/
def finiteOddCoreBlockerPresentQuitUpper
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {n : ℕ} (core : Fin n ↪ ι) (phase : Fin n) : ℝ :=
  (finiteOddCoreBlockerPresentQuitRowValues reward core phase).max'
    (finiteOddCoreBlockerPresentQuitRowValues_nonempty reward core phase)

/-- The exact finite row-extrema sandwich
`L_i^+ < C_i^- ≤ C_i^+ < H_i^-` on an embedded odd core. -/
structure IsLiteralStrictFiniteOddIntervalBlockerCore
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (n : ℕ) (core : Fin n ↪ ι) : Prop where
  three_le : 3 ≤ n
  odd_card : Odd n
  sandwich : ∀ phase,
    finiteOddCoreBlockerPresentQuitUpper reward core phase <
        finiteOddCoreContinuationLower reward core three_le phase ∧
      finiteOddCoreContinuationLower reward core three_le phase ≤
        finiteOddCoreContinuationUpper reward core three_le phase ∧
      finiteOddCoreContinuationUpper reward core three_le phase <
        finiteOddCoreBlockerAbsentQuitLower reward core phase

private theorem continuationLower_le_literalRow
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {n : ℕ} {core : Fin n ↪ ι} (hn : 3 ≤ n) (phase : Fin n)
    (coalition : {S : Finset ι // S.Nonempty})
    (homits : core phase ∉ coalition.1) :
    finiteOddCoreContinuationLower reward core hn phase ≤
      reward coalition (core phase) := by
  apply Finset.min'_le
  apply Finset.mem_image.mpr
  refine ⟨coalition.1, ?_, ?_⟩
  · apply Finset.mem_erase.mpr
    refine ⟨Finset.nonempty_iff_ne_empty.mp coalition.property, ?_⟩
    apply Finset.mem_powerset.mpr
    intro who hwho
    apply Finset.mem_erase.mpr
    exact ⟨fun heq => homits (heq ▸ hwho), Finset.mem_univ who⟩
  · simp [weightOfReward, coalition.property]

private theorem literalRow_le_continuationUpper
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {n : ℕ} {core : Fin n ↪ ι} (hn : 3 ≤ n) (phase : Fin n)
    (coalition : {S : Finset ι // S.Nonempty})
    (homits : core phase ∉ coalition.1) :
    reward coalition (core phase) ≤
      finiteOddCoreContinuationUpper reward core hn phase := by
  apply Finset.le_max'
  apply Finset.mem_image.mpr
  refine ⟨coalition.1, ?_, ?_⟩
  · apply Finset.mem_erase.mpr
    refine ⟨Finset.nonempty_iff_ne_empty.mp coalition.property, ?_⟩
    apply Finset.mem_powerset.mpr
    intro who hwho
    apply Finset.mem_erase.mpr
    exact ⟨fun heq => homits (heq ▸ hwho), Finset.mem_univ who⟩
  · simp [weightOfReward, coalition.property]

private theorem blockerAbsentQuitLower_le_literalRow
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {n : ℕ} {core : Fin n ↪ ι} (phase : Fin n)
    (background : Finset ι) (howner : core phase ∉ background)
    (hblocker : core (finRotate n phase) ∉ background) :
    finiteOddCoreBlockerAbsentQuitLower reward core phase ≤
      reward ⟨insert (core phase) background,
        Finset.insert_nonempty _ _⟩ (core phase) := by
  apply Finset.min'_le
  apply Finset.mem_image.mpr
  refine ⟨background, ?_, rfl⟩
  apply Finset.mem_powerset.mpr
  intro who hwho
  apply Finset.mem_erase.mpr
  refine ⟨fun heq => hblocker (heq ▸ hwho), ?_⟩
  apply Finset.mem_erase.mpr
  exact ⟨fun heq => howner (heq ▸ hwho), Finset.mem_univ who⟩

private theorem literalRow_le_blockerPresentQuitUpper
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {n : ℕ} {core : Fin n ↪ ι} (phase : Fin n)
    (background : Finset ι) (howner : core phase ∉ background)
    (hblocker : core (finRotate n phase) ∉ background) :
    reward ⟨insert (core (finRotate n phase))
        (insert (core phase) background),
      Finset.insert_nonempty _ _⟩ (core phase) ≤
        finiteOddCoreBlockerPresentQuitUpper reward core phase := by
  apply Finset.le_max'
  apply Finset.mem_image.mpr
  refine ⟨background, ?_, rfl⟩
  apply Finset.mem_powerset.mpr
  intro who hwho
  apply Finset.mem_erase.mpr
  refine ⟨fun heq => hblocker (heq ▸ hwho), ?_⟩
  apply Finset.mem_erase.mpr
  exact ⟨fun heq => howner (heq ▸ hwho), Finset.mem_univ who⟩

omit [Fintype ι] in
private theorem intervalBernoulliWeight_nonneg
    {hazard : ι → ℝ} (hhazard0 : ∀ who, 0 ≤ hazard who)
    (hhazard1 : ∀ who, hazard who ≤ 1) (carrier subset : Finset ι) :
    0 ≤ bernoulliWeight hazard carrier subset := by
  exact mul_nonneg
    (Finset.prod_nonneg fun who _ => hhazard0 who)
    (Finset.prod_nonneg fun who _ => sub_nonneg.mpr (hhazard1 who))

private theorem excludedValue_le_of_literalContinuationUpper
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {n : ℕ} {core : Fin n ↪ ι} (hn : 3 ≤ n) (phase : Fin n)
    (hazard : ι → ℝ) (hhazard0 : ∀ who, 0 ≤ hazard who)
    (hhazard1 : ∀ who, hazard who ≤ 1) :
    excludedValue (weightOfReward reward) hazard (core phase) ≤
      (1 - continueMassExcl hazard (core phase)) *
        finiteOddCoreContinuationUpper reward core hn phase := by
  unfold excludedValue continueMassExcl
  let carrier := Finset.univ.erase (core phase)
  change
    (∑ coalition ∈ carrier.powerset.erase ∅,
      bernoulliWeight hazard carrier coalition *
        weightOfReward reward coalition (core phase)) ≤
      (1 - ∏ other ∈ carrier, (1 - hazard other)) *
        finiteOddCoreContinuationUpper reward core hn phase
  have hempty : bernoulliWeight hazard carrier ∅ =
      ∏ other ∈ carrier, (1 - hazard other) := by
    simp [bernoulliWeight]
  have hmass := sum_bernoulliWeight hazard carrier
  have hsumErase :
      ∑ coalition ∈ carrier.powerset.erase ∅,
          bernoulliWeight hazard carrier coalition =
        1 - ∏ other ∈ carrier, (1 - hazard other) := by
    have hsplit := Finset.sum_erase_add carrier.powerset
      (fun coalition => bernoulliWeight hazard carrier coalition)
      (Finset.empty_mem_powerset carrier)
    rw [hempty, hmass] at hsplit
    linarith
  calc
    ∑ coalition ∈ carrier.powerset.erase ∅,
        bernoulliWeight hazard carrier coalition *
          weightOfReward reward coalition (core phase) ≤
        ∑ coalition ∈ carrier.powerset.erase ∅,
          bernoulliWeight hazard carrier coalition *
            finiteOddCoreContinuationUpper reward core hn phase := by
      apply Finset.sum_le_sum
      intro coalition hcoalition
      have hsubset := Finset.mem_powerset.mp
        (Finset.mem_of_mem_erase hcoalition)
      have hnonempty : coalition.Nonempty :=
        Finset.nonempty_iff_ne_empty.mpr
          (Finset.ne_of_mem_erase hcoalition)
      have homits : core phase ∉ coalition := fun hmem =>
        Finset.ne_of_mem_erase (hsubset hmem) rfl
      let row : {S : Finset ι // S.Nonempty} := ⟨coalition, hnonempty⟩
      have hrowOmits : core phase ∉ row.1 := by
        simpa [row] using homits
      exact mul_le_mul_of_nonneg_left
        (by
          have hbound := literalRow_le_continuationUpper
            (reward := reward) hn phase row hrowOmits
          simpa [weightOfReward, hnonempty, row] using hbound)
        (intervalBernoulliWeight_nonneg hhazard0 hhazard1 carrier coalition)
    _ = (1 - ∏ other ∈ carrier, (1 - hazard other)) *
        finiteOddCoreContinuationUpper reward core hn phase := by
      rw [← Finset.sum_mul, hsumErase]

private theorem literalContinuationLower_le_excludedValue
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {n : ℕ} {core : Fin n ↪ ι} (hn : 3 ≤ n) (phase : Fin n)
    (hazard : ι → ℝ) (hhazard0 : ∀ who, 0 ≤ hazard who)
    (hhazard1 : ∀ who, hazard who ≤ 1) :
    (1 - continueMassExcl hazard (core phase)) *
        finiteOddCoreContinuationLower reward core hn phase ≤
      excludedValue (weightOfReward reward) hazard (core phase) := by
  unfold excludedValue continueMassExcl
  let carrier := Finset.univ.erase (core phase)
  change
    (1 - ∏ other ∈ carrier, (1 - hazard other)) *
        finiteOddCoreContinuationLower reward core hn phase ≤
      ∑ coalition ∈ carrier.powerset.erase ∅,
        bernoulliWeight hazard carrier coalition *
          weightOfReward reward coalition (core phase)
  have hempty : bernoulliWeight hazard carrier ∅ =
      ∏ other ∈ carrier, (1 - hazard other) := by
    simp [bernoulliWeight]
  have hmass := sum_bernoulliWeight hazard carrier
  have hsumErase :
      ∑ coalition ∈ carrier.powerset.erase ∅,
          bernoulliWeight hazard carrier coalition =
        1 - ∏ other ∈ carrier, (1 - hazard other) := by
    have hsplit := Finset.sum_erase_add carrier.powerset
      (fun coalition => bernoulliWeight hazard carrier coalition)
      (Finset.empty_mem_powerset carrier)
    rw [hempty, hmass] at hsplit
    linarith
  calc
    (1 - ∏ other ∈ carrier, (1 - hazard other)) *
        finiteOddCoreContinuationLower reward core hn phase =
        ∑ coalition ∈ carrier.powerset.erase ∅,
          bernoulliWeight hazard carrier coalition *
            finiteOddCoreContinuationLower reward core hn phase := by
      rw [← Finset.sum_mul, hsumErase]
    _ ≤ ∑ coalition ∈ carrier.powerset.erase ∅,
        bernoulliWeight hazard carrier coalition *
          weightOfReward reward coalition (core phase) := by
      apply Finset.sum_le_sum
      intro coalition hcoalition
      have hsubset := Finset.mem_powerset.mp
        (Finset.mem_of_mem_erase hcoalition)
      have hnonempty : coalition.Nonempty :=
        Finset.nonempty_iff_ne_empty.mpr
          (Finset.ne_of_mem_erase hcoalition)
      have homits : core phase ∉ coalition := fun hmem =>
        Finset.ne_of_mem_erase (hsubset hmem) rfl
      let row : {S : Finset ι // S.Nonempty} := ⟨coalition, hnonempty⟩
      have hrowOmits : core phase ∉ row.1 := by
        simpa [row] using homits
      exact mul_le_mul_of_nonneg_left
        (by
          have hbound := continuationLower_le_literalRow
            (reward := reward) hn phase row hrowOmits
          simpa [weightOfReward, hnonempty, row] using hbound)
        (intervalBernoulliWeight_nonneg hhazard0 hhazard1 carrier coalition)

/-- The literal extrema sandwich supplies the stationary interval source used
by the odd compact-limit producer. -/
theorem IsLiteralStrictFiniteOddIntervalBlockerCore.toStationaryFace
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {n : ℕ} {core : Fin n ↪ ι}
    (hcore : IsLiteralStrictFiniteOddIntervalBlockerCore reward n core) :
    IsStrictFiniteOddIntervalBlockerCore reward n
      (finiteOddCoreContinuationLower reward core hcore.three_le)
      (finiteOddCoreContinuationUpper reward core hcore.three_le) core where
  three_le := hcore.three_le
  odd_card := hcore.odd_card
  continue_lower := by
    intro phase hazard h0 h1
    exact literalContinuationLower_le_excludedValue
      hcore.three_le phase hazard h0 h1
  continue_upper := by
    intro phase hazard h0 h1
    exact excludedValue_le_of_literalContinuationUpper
      hcore.three_le phase hazard h0 h1
  lower := by
    intro phase hazard h0 h1 hface
    apply baseline_lt_sigmaValue_of_strictBlockerAbsentRows
      (baseline := fun _ =>
        finiteOddCoreContinuationUpper reward core hcore.three_le phase)
      (finiteOddBlocker_ne hcore.three_le core phase)
      (fun background howner hblocker =>
        lt_of_lt_of_le (hcore.sandwich phase).2.2
          (blockerAbsentQuitLower_le_literalRow
            phase background howner hblocker))
      hazard h0 h1 hface
  upper := by
    intro phase hazard h0 h1 hface
    apply sigmaValue_lt_baseline_of_strictBlockerPresentRows
      (baseline := fun _ =>
        finiteOddCoreContinuationLower reward core hcore.three_le phase)
      (finiteOddBlocker_ne hcore.three_le core phase)
      (fun background howner hblocker =>
        lt_of_le_of_lt
          (literalRow_le_blockerPresentQuitUpper
            phase background howner hblocker)
          (hcore.sandwich phase).1)
      hazard h0 h1 hface

/-- The literal finite row-extrema sandwich produces a stationary exact
terminal Nash certificate with interior hazards on the full odd core. -/
theorem exists_stationaryCertificate_of_literalStrictFiniteOddIntervalBlockerCore
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (n : ℕ) (core : Fin n ↪ ι)
    (hcore : IsLiteralStrictFiniteOddIntervalBlockerCore reward n core) :
    Nonempty (FiniteOddIntervalBlockerCoreStationaryCertificate
      reward n core) :=
  exists_stationaryCertificate_of_strictFiniteOddIntervalBlockerCore
    reward n
      (finiteOddCoreContinuationLower reward core hcore.three_le)
      (finiteOddCoreContinuationUpper reward core hcore.three_le)
      core hcore.toStationaryFace

/-- Headline all-behavior uniform-payoff consequence of the literal finite
row-extrema sandwich. -/
theorem isUniformEquilibriumPayoff_of_literalStrictFiniteOddIntervalBlockerCore
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (n : ℕ) (core : Fin n ↪ ι)
    (hcore : IsLiteralStrictFiniteOddIntervalBlockerCore reward n core) :
    ∃ value : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none value :=
  isUniformEquilibriumPayoff_of_strictFiniteOddIntervalBlockerCore
    reward n
      (finiteOddCoreContinuationLower reward core hcore.three_le)
      (finiteOddCoreContinuationUpper reward core hcore.three_le)
      core hcore.toStationaryFace

end GameTheory
