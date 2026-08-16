/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.GroupAction.CyclicKofNPrimitiveBlocks

/-!
# Exact classification of cyclic `K/N` collapse factors

For a nonempty proper block, a natural number `d` occurs as the size of its
translation stabilizer in some finite additive `N`-player population exactly
when `d` is a positive common divisor of `K` and `N`.

Equivalently, the attainable distinct-translation periods are exactly

`L = N / d` for positive `d ∣ gcd(K,N)`.

This file packages the necessity and construction theorems into one public
iff statement.
-/

namespace Math

namespace CyclicKofNCollapseClassification

open CyclicKofNArithmetic CyclicKofNPrimitiveBlocks
open scoped Pointwise

noncomputable section

/-- A universe-small witness that `d` is a cyclic collapse factor for a
`K`-block in an `N`-player finite additive population. -/
structure CollapseWitness (K N d : ℕ) where
  Player : Type
  addGroup : AddGroup Player
  fintype : Fintype Player
  decidableEq : DecidableEq Player
  block : Finset Player
  blockCard : block.card = K
  populationCard : @Fintype.card Player fintype = N
  stabilizerCard :
    letI : AddGroup Player := addGroup
    letI : Fintype Player := fintype
    letI : DecidableEq Player := decidableEq
    Fintype.card (AddAction.stabilizer Player block) = d

/-- Attainability predicate for a cyclic collapse factor. -/
def IsCyclicCollapseFactor (K N d : ℕ) : Prop :=
  Nonempty (CollapseWitness K N d)

/-- Number of distinct translated phases of a collapse witness. -/
def CollapseWitness.period {K N d : ℕ} (w : CollapseWitness K N d) : ℕ :=
  letI : AddGroup w.Player := w.addGroup
  letI : Fintype w.Player := w.fintype
  letI : DecidableEq w.Player := w.decidableEq
  Fintype.card (TranslationPhase w.block)

/-- Every witness period is positive. -/
theorem CollapseWitness.period_pos {K N d : ℕ}
    (w : CollapseWitness K N d) : 0 < w.period := by
  letI : AddGroup w.Player := w.addGroup
  letI : Fintype w.Player := w.fintype
  letI : DecidableEq w.Player := w.decidableEq
  unfold CollapseWitness.period
  exact Fintype.card_pos_iff.mpr inferInstance

/-- The universal reduced-denominator lower bound, stated for an arbitrary
collapse witness. -/
theorem CollapseWitness.reducedPopulation_dvd_period
    {K N d : ℕ} (w : CollapseWitness K N d) :
    N / K.gcd N ∣ w.period := by
  letI : AddGroup w.Player := w.addGroup
  letI : Fintype w.Player := w.fintype
  letI : DecidableEq w.Player := w.decidableEq
  have hdvd := reducedPopulation_dvd_card_translationPhase w.block
  rw [w.populationCard, w.blockCard] at hdvd
  simpa [CollapseWitness.period] using hdvd

/-- Therefore every witness has at least the reduced-denominator number of
phases. -/
theorem CollapseWitness.reducedPopulation_le_period
    {K N d : ℕ} (w : CollapseWitness K N d) :
    N / K.gcd N ≤ w.period :=
  Nat.le_of_dvd w.period_pos w.reducedPopulation_dvd_period

/-- Every collapse witness has positive stabilizer size. -/
theorem IsCyclicCollapseFactor.positive
    {K N d : ℕ} (h : IsCyclicCollapseFactor K N d) : 0 < d := by
  obtain ⟨w⟩ := h
  letI : AddGroup w.Player := w.addGroup
  letI : Fintype w.Player := w.fintype
  letI : DecidableEq w.Player := w.decidableEq
  have hpos : 0 < Fintype.card
      (AddAction.stabilizer w.Player w.block) :=
    Fintype.card_pos_iff.mpr inferInstance
  have hstabilizer : Fintype.card
      (AddAction.stabilizer w.Player w.block) = d := w.stabilizerCard
  rwa [hstabilizer] at hpos

/-- Necessity on block size: the collapse factor divides `K`. -/
theorem IsCyclicCollapseFactor.dvd_active
    {K N d : ℕ} (h : IsCyclicCollapseFactor K N d) : d ∣ K := by
  obtain ⟨w⟩ := h
  letI : AddGroup w.Player := w.addGroup
  letI : Fintype w.Player := w.fintype
  letI : DecidableEq w.Player := w.decidableEq
  have hdvd := card_translationStabilizer_dvd_card_block w.block
  rw [w.stabilizerCard, w.blockCard] at hdvd
  exact hdvd

/-- Necessity on population size: the collapse factor divides `N`. -/
theorem IsCyclicCollapseFactor.dvd_population
    {K N d : ℕ} (h : IsCyclicCollapseFactor K N d) : d ∣ N := by
  obtain ⟨w⟩ := h
  letI : AddGroup w.Player := w.addGroup
  letI : Fintype w.Player := w.fintype
  letI : DecidableEq w.Player := w.decidableEq
  refine ⟨Fintype.card (TranslationPhase w.block), ?_⟩
  have horbit := translationOrbit_mul_stabilizer w.block
  rw [w.stabilizerCard, w.populationCard] at horbit
  simpa [mul_comm] using horbit.symm

/-- Every witness has exactly `N/d` distinct translated phases. -/
theorem IsCyclicCollapseFactor.period_eq_div
    {K N d : ℕ} (h : IsCyclicCollapseFactor K N d) :
    ∃ w : CollapseWitness K N d,
      letI : AddGroup w.Player := w.addGroup
      letI : Fintype w.Player := w.fintype
      letI : DecidableEq w.Player := w.decidableEq
      Fintype.card (TranslationPhase w.block) = N / d := by
  obtain ⟨w⟩ := h
  refine ⟨w, ?_⟩
  letI : AddGroup w.Player := w.addGroup
  letI : Fintype w.Player := w.fintype
  letI : DecidableEq w.Player := w.decidableEq
  rw [card_translationPhase_eq_div_stabilizer,
    w.stabilizerCard, w.populationCard]

/-- Period form of `IsCyclicCollapseFactor.period_eq_div`. -/
theorem IsCyclicCollapseFactor.exists_witness_period_eq_div
    {K N d : ℕ} (h : IsCyclicCollapseFactor K N d) :
    ∃ w : CollapseWitness K N d, w.period = N / d := by
  obtain ⟨w, hw⟩ := h.period_eq_div
  refine ⟨w, ?_⟩
  simpa [CollapseWitness.period] using hw

/-- Construct a witness from a common divisor of the positive active count. -/
theorem isCyclicCollapseFactor_of_commonDivisor
    {K N d : ℕ} (hKpos : 0 < K) (hKN : K < N)
    (hdK : d ∣ K) (hdN : d ∣ N) :
    IsCyclicCollapseFactor K N d := by
  have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdK hKpos
  have hdleN : d ≤ N := Nat.le_of_dvd (hKpos.trans hKN) hdN
  have hnpos : 0 < N / d := Nat.div_pos hdleN hdpos
  letI : NeZero (N / d) := ⟨hnpos.ne'⟩
  letI : NeZero d := ⟨hdpos.ne'⟩
  obtain ⟨A, hcard, hpopulation, _hperiod, hstabilizer⟩ :=
    exists_block_with_exact_admissible_collapse
      (K := K) (N := N) (d := d) hKpos hKN hdK hdN
  let P := ZMod (N / d) × ZMod d
  refine ⟨{
    Player := P
    addGroup := inferInstance
    fintype := inferInstance
    decidableEq := inferInstance
    block := A
    blockCard := hcard
    populationCard := hpopulation
    stabilizerCard := hstabilizer
  }⟩

/-- **Exact cyclic-collapse classification.**  For `0 < K < N`, a factor
`d` is attainable iff it is a common divisor of `K` and `N`.  Positivity of
`d` follows from `d ∣ K` and `0 < K`. -/
theorem isCyclicCollapseFactor_iff
    {K N d : ℕ} (hKpos : 0 < K) (hKN : K < N) :
    IsCyclicCollapseFactor K N d ↔
      d ∣ K ∧ d ∣ N := by
  constructor
  · intro h
    exact ⟨h.dvd_active, h.dvd_population⟩
  · rintro ⟨hdK, hdN⟩
    exact isCyclicCollapseFactor_of_commonDivisor
      hKpos hKN hdK hdN

/-- Equivalent gcd formulation. -/
theorem isCyclicCollapseFactor_iff_dvd_gcd
    {K N d : ℕ} (hKpos : 0 < K) (hKN : K < N) :
    IsCyclicCollapseFactor K N d ↔
      d ∣ K.gcd N := by
  rw [isCyclicCollapseFactor_iff hKpos hKN]
  constructor
  · rintro ⟨hdK, hdN⟩
    exact Nat.dvd_gcd hdK hdN
  · intro hdgcd
    exact ⟨hdgcd.trans (Nat.gcd_dvd_left K N),
      hdgcd.trans (Nat.gcd_dvd_right K N)⟩

/-- **Exact minimum period theorem.**  The reduced denominator is attained,
not merely a lower bound. -/
theorem exists_collapseWitness_period_eq_reducedPopulation
    {K N : ℕ} (hKpos : 0 < K) (hKN : K < N) :
    ∃ w : CollapseWitness K N (K.gcd N),
      w.period = N / K.gcd N := by
  have hattain : IsCyclicCollapseFactor K N (K.gcd N) :=
    isCyclicCollapseFactor_of_commonDivisor hKpos hKN
      (Nat.gcd_dvd_left K N) (Nat.gcd_dvd_right K N)
  exact hattain.exists_witness_period_eq_div

/-- Extremal characterization: every cyclic `K/N` block has period at least
`N/gcd(K,N)`, and some block has equality. -/
theorem reducedPopulation_is_exact_minimum_period
    {K N : ℕ} (hKpos : 0 < K) (hKN : K < N) :
    (∀ d (w : CollapseWitness K N d),
      N / K.gcd N ≤ w.period) ∧
    ∃ w : CollapseWitness K N (K.gcd N),
      w.period = N / K.gcd N := by
  exact ⟨fun _d w => w.reducedPopulation_le_period,
    exists_collapseWitness_period_eq_reducedPopulation hKpos hKN⟩

end

end CyclicKofNCollapseClassification

end Math
