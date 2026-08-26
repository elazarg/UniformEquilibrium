/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.Probability.QuantileClock
import Mathlib.Data.Nat.Choose.Cast
import MathUE.PMFProduct.Conditioning

/-!
# Raw common-quantile collision bounds

This file proves game-independent collision estimates for independent stopping
laws. The parity-valued quotient is deliberately named `Raw`: it is collision
bookkeeping and is not the canonical active target clock. Common marks are
computed from the original laws and remain fixed under a pure replacement.
-/

noncomputable section

namespace Math.PMFProduct

open Set Math.Probability Math.ProbabilityMassFunction

variable {ι α : Type*} [Fintype ι]

open Classical in
private theorem pmfMass_pmfPi_two_coord
    (laws : ι → PMF α) {first second : ι} (hne : first ≠ second)
    (firstEvent secondEvent : α → Prop) :
    pmfMass (pmfPi laws) (fun choices =>
      firstEvent (choices first) ∧ secondEvent (choices second)) =
      pmfMass (laws first) firstEvent *
        pmfMass (laws second) secondEvent := by
  let events : ι → α → Prop := fun who choice =>
    if who = first then firstEvent choice
    else if who = second then secondEvent choice
    else True
  rw [show pmfMass (pmfPi laws) (fun choices =>
      firstEvent (choices first) ∧ secondEvent (choices second)) =
      pmfMass (pmfPi laws) (fun choices => ∀ who, events who (choices who)) by
    congr 1
    funext choices
    apply propext
    constructor
    · rintro ⟨hfirst, hsecond⟩ who
      by_cases hwf : who = first
      · subst who
        simpa [events] using hfirst
      · by_cases hws : who = second
        · subst who
          simpa [events, hne.symm] using hsecond
        · simp [events, hwf, hws]
    · intro hall
      constructor
      · simpa [events] using hall first
      · simpa [events, hne.symm] using hall second]
  rw [pmfMass_pmfPi_forall]
  let mass : ι → ENNReal := fun who =>
    pmfMass (laws who) (events who)
  change (∏ who, mass who) = _
  rw [show (∏ who, mass who) =
      mass first * ∏ who ∈ Finset.univ.erase first, mass who by
    exact (Finset.mul_prod_erase Finset.univ mass
      (Finset.mem_univ first)).symm]
  rw [show (∏ who ∈ Finset.univ.erase first, mass who) =
      mass second *
        ∏ who ∈ (Finset.univ.erase first).erase second, mass who by
    exact (Finset.mul_prod_erase (Finset.univ.erase first) mass
      (by simp [hne.symm])).symm]
  have hrest :
      ∏ who ∈ (Finset.univ.erase first).erase second, mass who = 1 := by
    apply Finset.prod_eq_one
    intro who hwho
    have houter := (Finset.mem_erase.mp hwho).2
    have hwf : who ≠ first := Finset.ne_of_mem_erase houter
    have hws : who ≠ second := Finset.ne_of_mem_erase hwho
    simp [mass, events, hwf, hws, pmfMass_true]
  rw [hrest, mul_one]
  simp [mass, events, hne.symm]

end Math.PMFProduct

namespace Math.PMFProduct

open Set Math.Probability Math.ProbabilityMassFunction

open Classical in
private theorem pmfMass_eq_apply {α : Type*} (law : PMF α) (value : α) :
    pmfMass law (fun choice => choice = value) = law value := by
  rw [pmfMass_eq_toOuterMeasure]
  rw [show {choice | choice = value} = ({value} : Set α) by ext; simp]
  exact PMF.toOuterMeasure_apply_singleton law value

/-- Mass of a same-even-raw-cell collision for one ordered player pair. -/
def pairRawEvenSomeCollisionMass {ι : Type*} [Fintype ι]
    (laws : ι → PMF (Option ℕ)) (first second : ι) : ENNReal :=
  pmfMass (pmfPi laws) fun choices =>
    ∃ cell, Even cell ∧
      choices first = some cell ∧ choices second = some cell

/-- Same-cell collision mass is symmetric in the two coordinates. -/
theorem pairRawEvenSomeCollisionMass_comm
    {ι : Type*} [Fintype ι] (laws : ι → PMF (Option ℕ))
    (first second : ι) :
    pairRawEvenSomeCollisionMass laws first second =
      pairRawEvenSomeCollisionMass laws second first := by
  unfold pairRawEvenSomeCollisionMass
  congr 1
  funext choices
  apply propext
  constructor
  · rintro ⟨cell, heven, hfirst, hsecond⟩
    exact ⟨cell, heven, hsecond, hfirst⟩
  · rintro ⟨cell, heven, hsecond, hfirst⟩
    exact ⟨cell, heven, hfirst, hsecond⟩

open Classical in
theorem pairRawEvenSomeCollisionMass_le
    {ι : Type*} [Fintype ι]
    (laws : ι → PMF (Option ℕ)) {first second : ι}
    (hne : first ≠ second) {bound : ENNReal}
    (hfirst : ∀ cell, Even cell → laws first (some cell) ≤ bound) :
    pairRawEvenSomeCollisionMass laws first second ≤ bound := by
  let joint := pmfPi laws
  let cellEvent : ℕ → Set (ι → Option ℕ) := fun cell =>
    {choices | Even cell ∧
      choices first = some cell ∧ choices second = some cell}
  have hunion : {choices | ∃ cell, Even cell ∧
      choices first = some cell ∧ choices second = some cell} =
      ⋃ cell, cellEvent cell := by
    ext choices
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    rfl
  have houter : joint.toOuterMeasure (⋃ cell, cellEvent cell) ≤
      ∑' cell, joint.toOuterMeasure (cellEvent cell) :=
    MeasureTheory.measure_iUnion_le cellEvent
  have hcell : ∀ cell,
      joint.toOuterMeasure (cellEvent cell) =
        if Even cell then
          laws first (some cell) * laws second (some cell)
        else 0 := by
    intro cell
    rw [← pmfMass_eq_toOuterMeasure]
    by_cases heven : Even cell
    · rw [if_pos heven]
      rw [show pmfMass joint (fun choices =>
          Even cell ∧ choices first = some cell ∧ choices second = some cell) =
          pmfMass joint (fun choices =>
            choices first = some cell ∧ choices second = some cell) by
        congr 1
        funext choices
        apply propext
        simp [heven]]
      change pmfMass (pmfPi laws) (fun choices =>
        choices first = some cell ∧ choices second = some cell) = _
      have hpair := pmfMass_pmfPi_two_coord laws hne
        (fun choice => choice = some cell)
        (fun choice => choice = some cell)
      rw [pmfMass_eq_apply, pmfMass_eq_apply] at hpair
      exact hpair
    · rw [if_neg heven]
      have hempty : pmfMass joint (fun choices => choices ∈ cellEvent cell) = 0 := by
        rw [show (fun choices => choices ∈ cellEvent cell) =
            (fun _ => False) by
          funext choices
          apply propext
          simp [cellEvent, heven]]
        simp [pmfMass, pmfMask]
      exact hempty
  have hsumBound : (∑' cell,
      if Even cell then
        laws first (some cell) * laws second (some cell)
      else 0) ≤ bound := by
    calc
      (∑' cell,
          if Even cell then
            laws first (some cell) * laws second (some cell)
          else 0) ≤
          ∑' cell, bound * laws second (some cell) := by
        apply ENNReal.tsum_le_tsum
        intro cell
        by_cases heven : Even cell
        · rw [if_pos heven]
          exact mul_le_mul_left (hfirst cell heven) _
        · rw [if_neg heven]
          exact bot_le
      _ = bound * ∑' cell, laws second (some cell) :=
        ENNReal.tsum_mul_left
      _ ≤ bound * 1 := by
        apply mul_le_mul_right
        have hsomeLe : (∑' cell : ℕ, laws second (some cell)) ≤
            ∑' choice : Option ℕ, laws second choice := by
          exact Summable.tsum_le_tsum_of_inj some
            (fun _ _ h => Option.some.inj h)
            (fun _ _ => zero_le) (fun _ => le_rfl)
            ENNReal.summable ENNReal.summable
        simpa only [PMF.tsum_coe] using hsomeLe
      _ = bound := mul_one bound
  unfold pairRawEvenSomeCollisionMass
  rw [pmfMass_eq_toOuterMeasure, hunion]
  refine houter.trans ?_
  rw [show (∑' cell, joint.toOuterMeasure (cellEvent cell)) =
      ∑' cell, if Even cell then
        laws first (some cell) * laws second (some cell)
      else 0 by
    apply tsum_congr
    exact hcell]
  exact hsumBound

end Math.PMFProduct

namespace Math.Probability

open Math.PMFProduct Math.ProbabilityMassFunction

/-- Pairwise collision in a common even raw quantile cell has probability at
most one grid quantum. -/
theorem pairRawEvenSomeCollisionMass_commonQuantile_toReal_le_one_div
    {ι : Type*} [Fintype ι] (laws : ι → PMF (Option ℕ))
    {level : ℕ} (hlevel : 0 < level) {first second : ι}
    (hne : first ≠ second) :
    (pairRawEvenSomeCollisionMass
      (fun who => finiteClockRawCompressedLaw (laws who)
        (commonStoppingLawQuantileMarks laws level))
      first second).toReal ≤ 1 / (level : ℝ) := by
  let compressed : ι → PMF (Option ℕ) := fun who =>
    finiteClockRawCompressedLaw (laws who)
      (commonStoppingLawQuantileMarks laws level)
  let bound : ENNReal := ENNReal.ofReal (1 / (level : ℝ))
  have hboundNonneg : 0 ≤ 1 / (level : ℝ) := by positivity
  have hfirst : ∀ cell, Even cell →
      compressed first (some cell) ≤ bound := by
    intro cell heven
    have hreal := finiteClockRawCompressedLaw_common_even_cell_toReal_le_one_div
      laws hlevel first cell heven
    apply (ENNReal.toReal_le_toReal
      (PMF.apply_ne_top (compressed first) (some cell))
      ENNReal.ofReal_ne_top).mp
    simpa only [bound, ENNReal.toReal_ofReal hboundNonneg] using hreal
  have hmass := pairRawEvenSomeCollisionMass_le compressed hne hfirst
  have hmassTop :
      pairRawEvenSomeCollisionMass compressed first second ≠ ⊤ := by
    unfold pairRawEvenSomeCollisionMass
    exact pmfMass_ne_top _ _
  have hreal := (ENNReal.toReal_le_toReal hmassTop ENNReal.ofReal_ne_top).2 hmass
  simpa only [compressed, bound, ENNReal.toReal_ofReal hboundNonneg] using hreal

end Math.Probability

namespace Math.Probability

open Math.PMFProduct Math.ProbabilityMassFunction

open Classical in
private theorem pairRawEvenSomeCollisionMass_commonQuantile_update_pure_le
    {ι : Type*} [Fintype ι] (laws : ι → PMF (Option ℕ))
    {level : ℕ} (hlevel : 0 < level) (deviator : ι)
    (choice : Option ℕ) {first second : ι} (hne : first ≠ second) :
    pairRawEvenSomeCollisionMass
      (Function.update
        (fun who => finiteClockRawCompressedLaw (laws who)
          (commonStoppingLawQuantileMarks laws level))
        deviator (PMF.pure choice)) first second ≤
      ENNReal.ofReal (1 / (level : ℝ)) := by
  let compressed : ι → PMF (Option ℕ) := fun who =>
    finiteClockRawCompressedLaw (laws who)
      (commonStoppingLawQuantileMarks laws level)
  let modified := Function.update compressed deviator (PMF.pure choice)
  let bound : ENNReal := ENNReal.ofReal (1 / (level : ℝ))
  have hboundNonneg : 0 ≤ 1 / (level : ℝ) := by positivity
  have hopponent (who : ι) (hwho : who ≠ deviator) :
      ∀ cell, Even cell → modified who (some cell) ≤ bound := by
    intro cell heven
    have hreal :=
      finiteClockRawCompressedLaw_common_even_cell_toReal_le_one_div
        laws hlevel who cell heven
    have hmodified : modified who = compressed who := by
      simp [modified, hwho]
    rw [hmodified]
    apply (ENNReal.toReal_le_toReal
      (PMF.apply_ne_top (compressed who) (some cell))
      ENNReal.ofReal_ne_top).mp
    simpa only [bound, ENNReal.toReal_ofReal hboundNonneg] using hreal
  change pairRawEvenSomeCollisionMass modified first second ≤ bound
  by_cases hfirst : first = deviator
  · subst first
    rw [pairRawEvenSomeCollisionMass_comm]
    exact pairRawEvenSomeCollisionMass_le modified hne.symm
      (hopponent second hne.symm)
  · exact pairRawEvenSomeCollisionMass_le modified hne
      (hopponent first hfirst)

end Math.Probability

namespace Math.PMFProduct

open Set Math.Probability Math.ProbabilityMassFunction

/-- An even-raw-cell collision among some unordered pair of coordinates. -/
def hasRawEvenSomeCollision {ι : Type*} [Fintype ι]
    (choices : ι → Option ℕ) : Prop :=
  ∃ first second, first ≠ second ∧ ∃ cell, Even cell ∧
    choices first = some cell ∧ choices second = some cell

/-- Product mass of the event that some two distinct coordinates occupy the
same even raw cell. -/
def rawEvenSomeCollisionMass {ι : Type*} [Fintype ι]
    (laws : ι → PMF (Option ℕ)) : ENNReal :=
  pmfMass (pmfPi laws) hasRawEvenSomeCollision

open Classical in
theorem rawEvenSomeCollisionMass_le_choose_mul
    {ι : Type*} [Fintype ι] (laws : ι → PMF (Option ℕ))
    {bound : ENNReal}
    (hpair : ∀ first second, first ≠ second →
      pairRawEvenSomeCollisionMass laws first second ≤ bound) :
    rawEvenSomeCollisionMass laws ≤ (Fintype.card ι).choose 2 * bound := by
  let pairs := Finset.powersetCard 2 (Finset.univ : Finset ι)
  let pairEvent : Finset ι → Set (ι → Option ℕ) := fun pair =>
    {choices | ∃ cell, Even cell ∧
      ∀ who ∈ pair, choices who = some cell}
  have hunion : {choices | hasRawEvenSomeCollision choices} =
      ⋃ pair ∈ pairs, pairEvent pair := by
    ext choices
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨first, second, hne, cell, heven, hfirst, hsecond⟩
      let pair : Finset ι := {first, second}
      have hcard : pair.card = 2 := by simp [pair, hne]
      refine ⟨pair, ?_, ?_⟩
      · simp [pairs, hcard]
      · refine ⟨cell, heven, ?_⟩
        intro who hwho
        simp only [pair, Finset.mem_insert, Finset.mem_singleton] at hwho
        rcases hwho with rfl | rfl
        · exact hfirst
        · exact hsecond
    · rintro ⟨pair, hpairMem, cell, heven, hcell⟩
      have hcard : pair.card = 2 := by
        simpa [pairs] using hpairMem
      obtain ⟨first, second, hne, rfl⟩ := Finset.card_eq_two.mp hcard
      refine ⟨first, second, hne, cell, heven, ?_, ?_⟩
      · exact hcell first (by simp)
      · exact hcell second (by simp)
  have hpairMass : ∀ pair ∈ pairs,
      (pmfPi laws).toOuterMeasure (pairEvent pair) ≤ bound := by
    intro pair hpairMem
    have hcard : pair.card = 2 := by simpa [pairs] using hpairMem
    obtain ⟨first, second, hne, rfl⟩ := Finset.card_eq_two.mp hcard
    rw [← pmfMass_eq_toOuterMeasure]
    have heq : pmfMass (pmfPi laws)
        (fun choices => choices ∈ pairEvent {first, second}) =
        pairRawEvenSomeCollisionMass laws first second := by
      unfold pairRawEvenSomeCollisionMass
      congr 1
      funext choices
      apply propext
      simp only [pairEvent, Set.mem_setOf_eq, Finset.mem_insert,
        Finset.mem_singleton]
      constructor
      · rintro ⟨cell, heven, hall⟩
        exact ⟨cell, heven, hall first (Or.inl rfl),
          hall second (Or.inr rfl)⟩
      · rintro ⟨cell, heven, hfirst, hsecond⟩
        refine ⟨cell, heven, ?_⟩
        intro who hwho
        rcases hwho with rfl | rfl
        · exact hfirst
        · exact hsecond
    change pmfMass (pmfPi laws)
      (fun choices => choices ∈ pairEvent {first, second}) ≤ bound
    rw [heq]
    exact hpair first second hne
  unfold rawEvenSomeCollisionMass
  rw [pmfMass_eq_toOuterMeasure, hunion]
  calc
    (pmfPi laws).toOuterMeasure (⋃ pair ∈ pairs, pairEvent pair) ≤
        ∑ pair ∈ pairs, (pmfPi laws).toOuterMeasure (pairEvent pair) :=
      MeasureTheory.measure_biUnion_finset_le pairs pairEvent
    _ ≤ ∑ _pair ∈ pairs, bound :=
      Finset.sum_le_sum fun pair hmem => hpairMass pair hmem
    _ = (Fintype.card ι).choose 2 * bound := by
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_powersetCard]
      simp

end Math.PMFProduct

namespace Math.Probability

open Math.PMFProduct Math.ProbabilityMassFunction

private theorem pairRawEvenSomeCollisionMass_commonQuantile_le_ofReal
    {ι : Type*} [Fintype ι] (laws : ι → PMF (Option ℕ))
    {level : ℕ} (hlevel : 0 < level) {first second : ι}
    (hne : first ≠ second) :
    pairRawEvenSomeCollisionMass
      (fun who => finiteClockRawCompressedLaw (laws who)
        (commonStoppingLawQuantileMarks laws level))
      first second ≤ ENNReal.ofReal (1 / (level : ℝ)) := by
  let compressed : ι → PMF (Option ℕ) := fun who =>
    finiteClockRawCompressedLaw (laws who)
      (commonStoppingLawQuantileMarks laws level)
  let bound : ENNReal := ENNReal.ofReal (1 / (level : ℝ))
  have hboundNonneg : 0 ≤ 1 / (level : ℝ) := by positivity
  have hfirst : ∀ cell, Even cell →
      compressed first (some cell) ≤ bound := by
    intro cell heven
    have hreal := finiteClockRawCompressedLaw_common_even_cell_toReal_le_one_div
      laws hlevel first cell heven
    apply (ENNReal.toReal_le_toReal
      (PMF.apply_ne_top (compressed first) (some cell))
      ENNReal.ofReal_ne_top).mp
    simpa only [bound, ENNReal.toReal_ofReal hboundNonneg] using hreal
  exact pairRawEvenSomeCollisionMass_le compressed hne hfirst

/-- The probability that any player pair collides in a common even raw
quantile cell is bounded by the number of unordered pairs times one grid
quantum. -/
theorem rawEvenSomeCollisionMass_commonQuantile_toReal_le_choose_div
    {ι : Type*} [Fintype ι] (laws : ι → PMF (Option ℕ))
    {level : ℕ} (hlevel : 0 < level) :
    (rawEvenSomeCollisionMass
      (fun who => finiteClockRawCompressedLaw (laws who)
        (commonStoppingLawQuantileMarks laws level))).toReal ≤
      ((Fintype.card ι).choose 2 : ℝ) / (level : ℝ) := by
  let compressed : ι → PMF (Option ℕ) := fun who =>
    finiteClockRawCompressedLaw (laws who)
      (commonStoppingLawQuantileMarks laws level)
  let bound : ENNReal := ENNReal.ofReal (1 / (level : ℝ))
  have hmass := rawEvenSomeCollisionMass_le_choose_mul compressed
    (bound := bound) fun first second hne =>
      pairRawEvenSomeCollisionMass_commonQuantile_le_ofReal
        laws hlevel hne
  have hmassTop : rawEvenSomeCollisionMass compressed ≠ ⊤ := by
    unfold rawEvenSomeCollisionMass
    exact pmfMass_ne_top _ _
  have hrightTop : ((Fintype.card ι).choose 2 : ENNReal) * bound ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.ofReal_ne_top
  have hreal := (ENNReal.toReal_le_toReal hmassTop hrightTop).2 hmass
  have hboundNonneg : 0 ≤ 1 / (level : ℝ) := by positivity
  rw [ENNReal.toReal_mul, ENNReal.toReal_natCast,
    ENNReal.toReal_ofReal hboundNonneg] at hreal
  simpa only [compressed, bound, one_mul, div_eq_mul_inv] using hreal

end Math.Probability

namespace Math.Probability

lemma natCast_choose_two_eq_mul_sub_div_two (n : ℕ) :
    (n.choose 2 : ℝ) = ((n * (n - 1) : ℕ) : ℝ) / 2 := by
  cases n with
  | zero => simp
  | succ k =>
      rw [Nat.cast_choose_two]
      simp only [Nat.succ_sub_one, Nat.cast_mul, Nat.cast_succ]
      ring

end Math.Probability

namespace Math.Probability

open Math.PMFProduct

/-- Expanded finite-player form of the global collision budget. -/
theorem rawEvenSomeCollisionMass_commonQuantile_toReal_le_pair_budget
    {ι : Type*} [Fintype ι] (laws : ι → PMF (Option ℕ))
    {level : ℕ} (hlevel : 0 < level) :
    (rawEvenSomeCollisionMass
      (fun who => finiteClockRawCompressedLaw (laws who)
        (commonStoppingLawQuantileMarks laws level))).toReal ≤
      ((Fintype.card ι * (Fintype.card ι - 1) : ℕ) : ℝ) /
        (2 * (level : ℝ)) := by
  have h := rawEvenSomeCollisionMass_commonQuantile_toReal_le_choose_div
    laws hlevel
  rw [natCast_choose_two_eq_mul_sub_div_two] at h
  calc
    _ ≤ (((Fintype.card ι * (Fintype.card ι - 1) : ℕ) : ℝ) / 2) /
        (level : ℝ) := h
    _ = ((Fintype.card ι * (Fintype.card ι - 1) : ℕ) : ℝ) /
        (2 * (level : ℝ)) := by ring

end Math.Probability

namespace Math.PMFProduct

open Math.ProbabilityMassFunction

open Classical in
theorem pmfMass_hasRawEvenSomeCollision_coordwiseRawQuotient
    {ι : Type*} [Fintype ι] {α : ι → Type*}
    (laws : ∀ who, PMF (α who))
    (quotient : ∀ who, α who → Option ℕ) :
    pmfMass (pmfPi laws) (fun choices =>
      hasRawEvenSomeCollision (fun who => quotient who (choices who))) =
    rawEvenSomeCollisionMass
      (fun who => pushforward (laws who) (quotient who)) := by
  rw [← pmfMass_pushforward (pmfPi laws)
    (fun choices who => quotient who (choices who)) hasRawEvenSomeCollision]
  rw [pmfPi_push_coordwise]
  rfl

end Math.PMFProduct

namespace Math.Probability

open Math.PMFProduct Math.ProbabilityMassFunction

/-- Source-product form of the common-quantile collision bound. -/
theorem pmfMass_commonQuantileRawQuotient_hasRawEvenSomeCollision_toReal_le
    {ι : Type*} [Fintype ι] (laws : ι → PMF (Option ℕ))
    {level : ℕ} (hlevel : 0 < level) :
    (pmfMass (pmfPi laws) (fun choices =>
      hasRawEvenSomeCollision (fun who => finiteClockRawQuotient
        (commonStoppingLawQuantileMarks laws level) (choices who)))).toReal ≤
      ((Fintype.card ι * (Fintype.card ι - 1) : ℕ) : ℝ) /
        (2 * (level : ℝ)) := by
  rw [pmfMass_hasRawEvenSomeCollision_coordwiseRawQuotient]
  exact rawEvenSomeCollisionMass_commonQuantile_toReal_le_pair_budget
    laws hlevel

end Math.Probability

namespace Math.Probability

open Math.PMFProduct Math.ProbabilityMassFunction

open Classical in
/-- Replacing one compressed coordinate by any deterministic stopping choice
does not increase the common-quantile pair-union budget. Every unordered pair
can be oriented toward an unchanged coordinate. -/
theorem rawEvenSomeCollisionMass_commonQuantile_update_pure_toReal_le_choose_div
    {ι : Type*} [Fintype ι] (laws : ι → PMF (Option ℕ))
    {level : ℕ} (hlevel : 0 < level) (deviator : ι)
    (choice : Option ℕ) :
    (rawEvenSomeCollisionMass
      (Function.update
        (fun who => finiteClockRawCompressedLaw (laws who)
          (commonStoppingLawQuantileMarks laws level))
        deviator (PMF.pure choice))).toReal ≤
      ((Fintype.card ι).choose 2 : ℝ) / (level : ℝ) := by
  let compressed : ι → PMF (Option ℕ) := fun who =>
    finiteClockRawCompressedLaw (laws who)
      (commonStoppingLawQuantileMarks laws level)
  let modified := Function.update compressed deviator (PMF.pure choice)
  let bound : ENNReal := ENNReal.ofReal (1 / (level : ℝ))
  have hmass := rawEvenSomeCollisionMass_le_choose_mul modified
    (bound := bound) fun first second hne =>
      pairRawEvenSomeCollisionMass_commonQuantile_update_pure_le
        laws hlevel deviator choice hne
  have hmassTop : rawEvenSomeCollisionMass modified ≠ ⊤ := by
    unfold rawEvenSomeCollisionMass
    exact pmfMass_ne_top _ _
  have hrightTop : ((Fintype.card ι).choose 2 : ENNReal) * bound ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.ofReal_ne_top
  have hreal := (ENNReal.toReal_le_toReal hmassTop hrightTop).2 hmass
  have hboundNonneg : 0 ≤ 1 / (level : ℝ) := by positivity
  rw [ENNReal.toReal_mul, ENNReal.toReal_natCast,
    ENNReal.toReal_ofReal hboundNonneg] at hreal
  simpa only [modified, compressed, bound, one_mul,
    div_eq_mul_inv] using hreal

open Classical in
/-- Source-product form of the fixed-deviator collision budget. The common
marks remain those of the original laws, while one source law is replaced by
an arbitrary deterministic stopping choice. -/
theorem pmfMass_commonQuantileRawQuotient_update_pure_collision_toReal_le
    {ι : Type*} [Fintype ι] (laws : ι → PMF (Option ℕ))
    {level : ℕ} (hlevel : 0 < level) (deviator : ι)
    (choice : Option ℕ) :
    (pmfMass
      (pmfPi (Function.update laws deviator (PMF.pure choice)))
      (fun choices => hasRawEvenSomeCollision (fun who =>
        finiteClockRawQuotient
          (commonStoppingLawQuantileMarks laws level)
          (choices who)))).toReal ≤
      ((Fintype.card ι).choose 2 : ℝ) / (level : ℝ) := by
  let marks := commonStoppingLawQuantileMarks laws level
  rw [pmfMass_hasRawEvenSomeCollision_coordwiseRawQuotient]
  have hpush :
      (fun who => pushforward
        ((Function.update laws deviator (PMF.pure choice)) who)
        (finiteClockRawQuotient marks)) =
      Function.update
        (fun who => finiteClockRawCompressedLaw (laws who) marks)
        deviator (PMF.pure (finiteClockRawQuotient marks choice)) := by
    funext who
    by_cases hwho : who = deviator
    · subst who
      simp [finiteClockRawCompressedLaw, pushforward_pure]
    · rw [Function.update_of_ne hwho, Function.update_of_ne hwho]
      rfl
  rw [hpush]
  exact
    rawEvenSomeCollisionMass_commonQuantile_update_pure_toReal_le_choose_div
      laws hlevel deviator (finiteClockRawQuotient marks choice)

end Math.Probability
