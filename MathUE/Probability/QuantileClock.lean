/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.ProbabilityMassFunction

/-!
# Finite common quantile clocks

This file records the combinatorial part of the common quantile-clock
compression.  A finite set of marked dates induces an ordered quotient of
`Nat`: marked dates remain singleton cells and each gap becomes one clock
date.  The quotient retains `none` as a literal Never atom.

The file also proves that every unmarked gap has mass at most the reciprocal
of the quantile level, including the unbounded terminal gap.  It does not
assert any game-semantic payoff or deviation-cap comparison.
-/

noncomputable section

namespace Math
namespace Probability

open Set

/-- Finite stopping mass accumulated through `cutoff`. -/
def stoppingLawCumulativeFiniteMass (law : PMF (Option ℕ))
    (cutoff : ℕ) : ℝ :=
  (ProbabilityMassFunction.pmfMass (μ := law) fun choice =>
    ∃ time ≤ cutoff, choice = some time).toReal

theorem stoppingLawCumulativeFiniteMass_mono (law : PMF (Option ℕ)) :
    Monotone (stoppingLawCumulativeFiniteMass law) := by
  intro first second hle
  apply ENNReal.toReal_mono
    (ProbabilityMassFunction.pmfMass_ne_top law _)
  exact ProbabilityMassFunction.pmfMass_mono law fun choice => by
    rintro ⟨time, htime, rfl⟩
    exact ⟨time, htime.trans hle, rfl⟩

theorem stoppingLawCumulativeFiniteMass_nonneg
    (law : PMF (Option ℕ)) (cutoff : ℕ) :
    0 ≤ stoppingLawCumulativeFiniteMass law cutoff :=
  ENNReal.toReal_nonneg

theorem stoppingLawCumulativeFiniteMass_le_one
    (law : PMF (Option ℕ)) (cutoff : ℕ) :
    stoppingLawCumulativeFiniteMass law cutoff ≤ 1 := by
  have hmass : ProbabilityMassFunction.pmfMass (μ := law) (fun choice =>
      ∃ time ≤ cutoff, choice = some time) ≤ 1 := by
    simpa only [ProbabilityMassFunction.pmfMass_true] using
      ProbabilityMassFunction.pmfMass_mono law
        (E := fun choice => ∃ time ≤ cutoff, choice = some time)
        (F := fun _ => True) (fun _ _ => trivial)
  simpa only [stoppingLawCumulativeFiniteMass, ENNReal.toReal_one] using
    ENNReal.toReal_mono (by simp) hmass

/-- The first finite date at which a stopping law reaches a threshold, when
such a date exists. -/
def stoppingLawFirstCrossing? (law : PMF (Option ℕ))
    (threshold : ℝ) : Option ℕ := by
  classical
  exact if hcross : ∃ cutoff,
      threshold ≤ stoppingLawCumulativeFiniteMass law cutoff then
    some (Nat.find hcross)
  else none

theorem stoppingLawFirstCrossing?_eq_some_iff
    (law : PMF (Option ℕ)) (threshold : ℝ) (cutoff : ℕ) :
    stoppingLawFirstCrossing? law threshold = some cutoff ↔
      ∃ hcross : ∃ time,
          threshold ≤ stoppingLawCumulativeFiniteMass law time,
        cutoff = Nat.find hcross := by
  unfold stoppingLawFirstCrossing?
  split_ifs with hcross
  · simp only [Option.some.injEq]
    exact ⟨fun h => ⟨hcross, h.symm⟩, fun ⟨_, h⟩ => h.symm⟩
  · constructor
    · intro himpossible
      cases himpossible
    · rintro ⟨witness, _⟩
      exact (hcross witness).elim

theorem stoppingLawFirstCrossing?_spec
    (law : PMF (Option ℕ)) (threshold : ℝ) {cutoff : ℕ}
    (hcutoff : stoppingLawFirstCrossing? law threshold = some cutoff) :
    threshold ≤ stoppingLawCumulativeFiniteMass law cutoff ∧
      ∀ earlier < cutoff,
        stoppingLawCumulativeFiniteMass law earlier < threshold := by
  rcases (stoppingLawFirstCrossing?_eq_some_iff
    law threshold cutoff).mp hcutoff with ⟨hcross, rfl⟩
  exact ⟨Nat.find_spec hcross, fun earlier hearlier =>
    lt_of_not_ge (Nat.find_min hcross hearlier)⟩

/-- A real interval of width greater than `1 / level` inside `[0,1]`
contains one positive `level`-grid point. -/
theorem exists_positive_grid_point_of_one_div_lt_sub
    {lower upper : ℝ} {level : ℕ}
    (hlevel : 0 < level) (hlower : 0 ≤ lower) (hupper : upper ≤ 1)
    (hwidth : 1 / (level : ℝ) < upper - lower) :
    ∃ index : Fin level,
      lower < ((index.val + 1 : ℕ) : ℝ) / (level : ℝ) ∧
      ((index.val + 1 : ℕ) : ℝ) / (level : ℝ) < upper := by
  let count : ℕ := ⌊(level : ℝ) * lower⌋₊ + 1
  have hlevelReal : 0 < (level : ℝ) := by exact_mod_cast hlevel
  have hlowerOne : lower < 1 := by
    have hpositive : 0 < upper - lower :=
      (div_pos (by norm_num) hlevelReal).trans hwidth
    linarith
  have hscaledNonneg : 0 ≤ (level : ℝ) * lower :=
    mul_nonneg hlevelReal.le hlower
  have hcountLe : count ≤ level := by
    apply Nat.add_one_le_iff.mpr
    rw [Nat.floor_lt hscaledNonneg]
    nlinarith
  have hcountPos : 0 < count := Nat.zero_lt_succ _
  let index : Fin level := ⟨count - 1, by omega⟩
  refine ⟨index, ?_, ?_⟩
  · have hfloor := Nat.lt_floor_add_one ((level : ℝ) * lower)
    have hcountEq : index.val + 1 = count := by
      dsimp [index]
      omega
    rw [hcountEq]
    apply (lt_div_iff₀ hlevelReal).2
    dsimp [count]
    simpa only [Nat.cast_add, Nat.cast_one, mul_comm] using hfloor
  · have hfloorLe : (⌊(level : ℝ) * lower⌋₊ : ℝ) ≤
        (level : ℝ) * lower := Nat.floor_le hscaledNonneg
    have hscaledWidth : (level : ℝ) * lower + 1 <
        (level : ℝ) * upper := by
      have hmul := (div_lt_iff₀ hlevelReal).mp hwidth
      nlinarith
    have hcountEq : index.val + 1 = count := by
      dsimp [index]
      omega
    rw [hcountEq]
    apply (div_lt_iff₀ hlevelReal).2
    dsimp [count]
    norm_num
    linarith

/-- Dates selected by the positive grid thresholds `1/level, ..., 1`.
Repeated first crossings are deduplicated. -/
def stoppingLawQuantileMarks (law : PMF (Option ℕ))
    (level : ℕ) : Finset ℕ :=
  Finset.univ.biUnion fun index : Fin level =>
    match stoppingLawFirstCrossing? law
        (((index.val + 1 : ℕ) : ℝ) / (level : ℝ)) with
    | none => ∅
    | some time => {time}

theorem card_stoppingLawQuantileMarks_le (law : PMF (Option ℕ))
    (level : ℕ) :
    (stoppingLawQuantileMarks law level).card ≤ level := by
  calc
    (stoppingLawQuantileMarks law level).card ≤
        ∑ _index : Fin level, 1 := by
      unfold stoppingLawQuantileMarks
      refine (Finset.card_biUnion_le).trans (Finset.sum_le_sum fun index _ => ?_)
      split <;> simp
    _ = level := by simp

/-- Union of every player's quantile marks. -/
def commonStoppingLawQuantileMarks {ι : Type*} [Fintype ι]
    (laws : ι → PMF (Option ℕ)) (level : ℕ) : Finset ℕ :=
  Finset.univ.biUnion fun who => stoppingLawQuantileMarks (laws who) level

theorem card_commonStoppingLawQuantileMarks_le {ι : Type*}
    [Fintype ι] (laws : ι → PMF (Option ℕ)) (level : ℕ) :
    (commonStoppingLawQuantileMarks laws level).card ≤
      Fintype.card ι * level := by
  calc
    (commonStoppingLawQuantileMarks laws level).card ≤
        ∑ who, (stoppingLawQuantileMarks (laws who) level).card := by
      exact Finset.card_biUnion_le
    _ ≤ ∑ _who : ι, level := by
      exact Finset.sum_le_sum fun who _ =>
        card_stoppingLawQuantileMarks_le (laws who) level
    _ = Fintype.card ι * level := by simp

/-- Ordered finite-cell index.  Each gap has an even index and each marked
singleton has the following odd index. -/
def finiteClockCellIndex (marks : Finset ℕ) (time : ℕ) : ℕ :=
  2 * (marks.filter fun mark => mark < time).card +
    if time ∈ marks then 1 else 0

theorem finiteClockCellIndex_lt (marks : Finset ℕ) (time : ℕ) :
    finiteClockCellIndex marks time < 2 * marks.card + 1 := by
  unfold finiteClockCellIndex
  split_ifs with hmem
  · have hcard : (marks.filter fun mark => mark < time).card < marks.card :=
      Finset.card_lt_card (Finset.filter_ssubset.2 ⟨time, hmem, lt_irrefl time⟩)
    have hmul := Nat.mul_lt_mul_of_pos_left hcard (by omega : 0 < 2)
    omega
  · have hcard : (marks.filter fun mark => mark < time).card ≤ marks.card :=
      Finset.card_filter_le _ _
    have hmul := Nat.mul_le_mul_left 2 hcard
    omega

/-- Escape-aware quotient map: every finite date goes to its ordered finite
cell and Never stays Never. -/
def finiteClockQuotient (marks : Finset ℕ) : Option ℕ → Option ℕ
  | none => none
  | some time => some (finiteClockCellIndex marks time)

@[simp] theorem finiteClockQuotient_none (marks : Finset ℕ) :
    finiteClockQuotient marks none = none := rfl

@[simp] theorem finiteClockQuotient_some (marks : Finset ℕ) (time : ℕ) :
    finiteClockQuotient marks (some time) =
      some (finiteClockCellIndex marks time) := rfl

/-! ## Consecutive indexing of the nonempty cells -/

/-- Raw alternating cell tags that are actually attained by a natural date.
Empty gaps, such as the gap before a mark at date zero or between consecutive
marks, are omitted. -/
noncomputable def finiteClockActiveCells (marks : Finset ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (2 * marks.card + 1)).filter fun cell =>
    ∃ time, finiteClockCellIndex marks time = cell

theorem finiteClockCellIndex_mem_activeCells
    (marks : Finset ℕ) (time : ℕ) :
    finiteClockCellIndex marks time ∈ finiteClockActiveCells marks := by
  classical
  simp only [finiteClockActiveCells, Finset.mem_filter, Finset.mem_range]
  exact ⟨finiteClockCellIndex_lt marks time, ⟨time, rfl⟩⟩

/-- Number of genuinely nonempty finite clock cells. -/
def finiteClockActiveCellCount (marks : Finset ℕ) : ℕ :=
  (finiteClockActiveCells marks).card

theorem finiteClockActiveCellCount_le (marks : Finset ℕ) :
    finiteClockActiveCellCount marks ≤ 2 * marks.card + 1 := by
  classical
  unfold finiteClockActiveCellCount finiteClockActiveCells
  exact (Finset.card_filter_le _ _).trans_eq (Finset.card_range _)

/-- Consecutive rank of the genuinely nonempty raw cell containing `time`.
Unlike `finiteClockCellIndex`, this leaves no artificial dates between
consecutive active cells. -/
noncomputable def finiteClockActiveCellIndex
    (marks : Finset ℕ) (time : ℕ) : ℕ := by
  classical
  exact (((finiteClockActiveCells marks).orderIsoOfFin rfl).symm
    ⟨finiteClockCellIndex marks time,
      finiteClockCellIndex_mem_activeCells marks time⟩).val

theorem finiteClockActiveCellIndex_lt_count
    (marks : Finset ℕ) (time : ℕ) :
    finiteClockActiveCellIndex marks time <
      finiteClockActiveCellCount marks := by
  classical
  exact (((finiteClockActiveCells marks).orderIsoOfFin rfl).symm
    ⟨finiteClockCellIndex marks time,
      finiteClockCellIndex_mem_activeCells marks time⟩).isLt

theorem finiteClockActiveCellCount_pos (marks : Finset ℕ) :
    0 < finiteClockActiveCellCount marks :=
  (Nat.zero_le _).trans_lt
    (finiteClockActiveCellIndex_lt_count marks 0)

theorem finiteClockActiveCellIndex_lt (marks : Finset ℕ) (time : ℕ) :
    finiteClockActiveCellIndex marks time < 2 * marks.card + 1 :=
  (finiteClockActiveCellIndex_lt_count marks time).trans_le
    (finiteClockActiveCellCount_le marks)

theorem finiteClockActiveCellIndex_eq_iff
    (marks : Finset ℕ) (first second : ℕ) :
    finiteClockActiveCellIndex marks first =
        finiteClockActiveCellIndex marks second ↔
      finiteClockCellIndex marks first =
        finiteClockCellIndex marks second := by
  classical
  unfold finiteClockActiveCellIndex
  constructor
  · intro heq
    have hfin :
        ((finiteClockActiveCells marks).orderIsoOfFin rfl).symm
            ⟨finiteClockCellIndex marks first,
              finiteClockCellIndex_mem_activeCells marks first⟩ =
          ((finiteClockActiveCells marks).orderIsoOfFin rfl).symm
            ⟨finiteClockCellIndex marks second,
              finiteClockCellIndex_mem_activeCells marks second⟩ :=
      Fin.ext heq
    have hsubtype := congrArg
      ((finiteClockActiveCells marks).orderIsoOfFin rfl) hfin
    simpa using congrArg Subtype.val hsubtype
  · intro heq
    have hsubtype :
        (⟨finiteClockCellIndex marks first,
            finiteClockCellIndex_mem_activeCells marks first⟩ :
              finiteClockActiveCells marks) =
          ⟨finiteClockCellIndex marks second,
            finiteClockCellIndex_mem_activeCells marks second⟩ :=
      Subtype.ext heq
    exact congrArg Fin.val (congrArg
      ((finiteClockActiveCells marks).orderIsoOfFin rfl).symm hsubtype)

theorem finiteClockActiveCellIndex_lt_of_cellIndex_lt
    (marks : Finset ℕ) {first second : ℕ}
    (hlt : finiteClockCellIndex marks first <
      finiteClockCellIndex marks second) :
    finiteClockActiveCellIndex marks first <
      finiteClockActiveCellIndex marks second := by
  classical
  unfold finiteClockActiveCellIndex
  exact ((finiteClockActiveCells marks).orderIsoOfFin rfl).symm.lt_iff_lt.mpr
    hlt

/-- Every date before the active-cell count is represented by a source
natural date.  Thus all unused support padding lies after the genuine cells. -/
theorem exists_finiteClockActiveCellIndex_eq
    (marks : Finset ℕ) {cell : ℕ}
    (hcell : cell < finiteClockActiveCellCount marks) :
    ∃ time, finiteClockActiveCellIndex marks time = cell := by
  classical
  let tagged := (finiteClockActiveCells marks).orderIsoOfFin rfl
    ⟨cell, hcell⟩
  obtain ⟨time, htime⟩ :=
    (Finset.mem_filter.mp tagged.property).2
  refine ⟨time, ?_⟩
  unfold finiteClockActiveCellIndex
  have htag : (⟨finiteClockCellIndex marks time,
      finiteClockCellIndex_mem_activeCells marks time⟩ :
        finiteClockActiveCells marks) = tagged := by
    exact Subtype.ext htime
  rw [htag]
  exact congrArg Fin.val
    (((finiteClockActiveCells marks).orderIsoOfFin rfl).symm_apply_apply
      ⟨cell, hcell⟩)

/-- Escape-aware quotient with consecutive indices for precisely the
nonempty cells.  Never remains literal. -/
def finiteClockActiveQuotient (marks : Finset ℕ) : Option ℕ → Option ℕ
  | none => none
  | some time => some (finiteClockActiveCellIndex marks time)

@[simp] theorem finiteClockActiveQuotient_none (marks : Finset ℕ) :
    finiteClockActiveQuotient marks none = none := rfl

@[simp] theorem finiteClockActiveQuotient_some
    (marks : Finset ℕ) (time : ℕ) :
    finiteClockActiveQuotient marks (some time) =
      some (finiteClockActiveCellIndex marks time) := rfl

/-- Push a complete stopping law through the consecutive active-cell
quotient. -/
def finiteClockActiveCompressedLaw (law : PMF (Option ℕ))
    (marks : Finset ℕ) : PMF (Option ℕ) :=
  law.map (finiteClockActiveQuotient marks)

@[simp] theorem finiteClockActiveCompressedLaw_none
    (law : PMF (Option ℕ)) (marks : Finset ℕ) :
    finiteClockActiveCompressedLaw law marks none = law none := by
  rw [finiteClockActiveCompressedLaw, PMF.map_apply, tsum_eq_single none]
  · simp
  · intro choice hchoice
    cases choice with
    | none => exact (hchoice rfl).elim
    | some time => simp

theorem finiteClockActiveCompressedLaw_support
    (law : PMF (Option ℕ)) (marks : Finset ℕ)
    {choice : Option ℕ}
    (hchoice : finiteClockActiveCompressedLaw law marks choice ≠ 0) :
    choice = none ∨
      ∃ time < finiteClockActiveCellCount marks, choice = some time := by
  have hmem : choice ∈
      (finiteClockActiveCompressedLaw law marks).support := hchoice
  rw [finiteClockActiveCompressedLaw, PMF.mem_support_map_iff] at hmem
  obtain ⟨source, -, rfl⟩ := hmem
  cases source with
  | none => exact Or.inl rfl
  | some time =>
      exact Or.inr ⟨finiteClockActiveCellIndex marks time,
        finiteClockActiveCellIndex_lt_count marks time, rfl⟩

theorem finiteClockActiveCompressedLaw_support_commonQuantile
    {ι : Type*} [Fintype ι] (laws : ι → PMF (Option ℕ)) (level : ℕ)
    (who : ι) {choice : Option ℕ}
    (hchoice : finiteClockActiveCompressedLaw (laws who)
        (commonStoppingLawQuantileMarks laws level) choice ≠ 0) :
    choice = none ∨ ∃ time < 2 * Fintype.card ι * level + 1,
      choice = some time := by
  rcases finiteClockActiveCompressedLaw_support (laws who)
      (commonStoppingLawQuantileMarks laws level) hchoice with
    hnever | ⟨time, htime, rfl⟩
  · exact Or.inl hnever
  · exact Or.inr ⟨time, htime.trans_le (by
      apply (finiteClockActiveCellCount_le _).trans
      have hcard := card_commonStoppingLawQuantileMarks_le laws level
      have hmul := Nat.mul_le_mul_left 2 hcard
      simpa only [Nat.mul_assoc] using Nat.add_le_add_right hmul 1), rfl⟩

/-- Push a complete stopping law through an ordered finite-cell quotient. -/
def finiteClockCompressedLaw (law : PMF (Option ℕ))
    (marks : Finset ℕ) : PMF (Option ℕ) :=
  law.map (finiteClockQuotient marks)

@[simp] theorem finiteClockCompressedLaw_none
    (law : PMF (Option ℕ)) (marks : Finset ℕ) :
    finiteClockCompressedLaw law marks none = law none := by
  rw [finiteClockCompressedLaw, PMF.map_apply, tsum_eq_single none]
  · simp
  · intro choice hchoice
    cases choice with
    | none => exact (hchoice rfl).elim
    | some time => simp

theorem finiteClockCompressedLaw_support
    (law : PMF (Option ℕ)) (marks : Finset ℕ)
    {choice : Option ℕ}
    (hchoice : finiteClockCompressedLaw law marks choice ≠ 0) :
    choice = none ∨ ∃ time < 2 * marks.card + 1, choice = some time := by
  have hmem : choice ∈ (finiteClockCompressedLaw law marks).support := hchoice
  rw [finiteClockCompressedLaw, PMF.mem_support_map_iff] at hmem
  obtain ⟨source, -, rfl⟩ := hmem
  cases source with
  | none => exact Or.inl rfl
  | some time =>
      exact Or.inr ⟨finiteClockCellIndex marks time,
        finiteClockCellIndex_lt marks time, rfl⟩

theorem finiteClockCompressedLaw_support_commonQuantile {ι : Type*}
    [Fintype ι] (laws : ι → PMF (Option ℕ)) (level : ℕ)
    (who : ι) {choice : Option ℕ}
    (hchoice : finiteClockCompressedLaw (laws who)
        (commonStoppingLawQuantileMarks laws level) choice ≠ 0) :
    choice = none ∨ ∃ time < 2 * Fintype.card ι * level + 1,
      choice = some time := by
  rcases finiteClockCompressedLaw_support (laws who)
      (commonStoppingLawQuantileMarks laws level) hchoice with
    hnever | ⟨time, htime, rfl⟩
  · exact Or.inl hnever
  · exact Or.inr ⟨time, htime.trans_le (by
      have hcard := card_commonStoppingLawQuantileMarks_le laws level
      have hmul := Nat.mul_le_mul_left 2 hcard
      simpa only [Nat.mul_assoc] using Nat.add_le_add_right hmul 1), rfl⟩

/-! ## Whole-cell mass estimate -/

theorem finiteClockCellIndex_mono (marks : Finset ℕ) :
    Monotone (finiteClockCellIndex marks) := by
  intro first second hle
  unfold finiteClockCellIndex
  by_cases hfirst : first ∈ marks
  · have hsub : marks.filter (fun mark => mark < first) ⊆
        marks.filter (fun mark => mark < second) := by
      intro mark hmark
      simp only [Finset.mem_filter] at hmark ⊢
      exact ⟨hmark.1, hmark.2.trans_le hle⟩
    have hcard := Finset.card_le_card hsub
    by_cases heq : first = second
    · subst second
      simp [hfirst]
    · have hlt : first < second := lt_of_le_of_ne hle heq
      have hproper :
          (marks.filter (fun mark => mark < first)).card + 1 ≤
            (marks.filter (fun mark => mark < second)).card := by
        apply Nat.add_one_le_iff.mpr
        apply Finset.card_lt_card
        refine Finset.ssubset_iff_subset_ne.mpr ⟨hsub, ?_⟩
        intro hsets
        have hmem : first ∈ marks.filter (fun mark => mark < second) := by
          simp [hfirst, hlt]
        rw [← hsets] at hmem
        simp at hmem
      simp only [if_pos hfirst]
      split_ifs <;> omega
  · have hsub : marks.filter (fun mark => mark < first) ⊆
        marks.filter (fun mark => mark < second) := by
      intro mark hmark
      simp only [Finset.mem_filter] at hmark ⊢
      exact ⟨hmark.1, hmark.2.trans_le hle⟩
    have hcard := Finset.card_le_card hsub
    simp only [if_neg hfirst]
    split_ifs <;> omega

theorem finiteClockActiveCellIndex_mono (marks : Finset ℕ) :
    Monotone (finiteClockActiveCellIndex marks) := by
  classical
  intro first second hle
  unfold finiteClockActiveCellIndex
  apply ((finiteClockActiveCells marks).orderIsoOfFin rfl).symm.monotone
  exact finiteClockCellIndex_mono marks hle

theorem finiteClockCellIndex_lt_of_lt_of_mem_left
    (marks : Finset ℕ) {first second : ℕ} (hlt : first < second)
    (hfirst : first ∈ marks) :
    finiteClockCellIndex marks first < finiteClockCellIndex marks second := by
  unfold finiteClockCellIndex
  rw [if_pos hfirst]
  have hsub : marks.filter (fun mark => mark < first) ⊆
      marks.filter (fun mark => mark < second) := by
    intro mark hmark
    simp only [Finset.mem_filter] at hmark ⊢
    exact ⟨hmark.1, hmark.2.trans hlt⟩
  have hproper :
      (marks.filter (fun mark => mark < first)).card + 1 ≤
        (marks.filter (fun mark => mark < second)).card := by
    apply Nat.add_one_le_iff.mpr
    apply Finset.card_lt_card
    refine Finset.ssubset_iff_subset_ne.mpr ⟨hsub, ?_⟩
    intro hsets
    have hmem : first ∈ marks.filter (fun mark => mark < second) := by
      simp [hfirst, hlt]
    rw [← hsets] at hmem
    simp at hmem
  split_ifs <;> omega

/-- A representative of the last genuine active cell lies in the unbounded
terminal gap, hence has an even raw tag. -/
theorem finiteClockCellIndex_even_of_activeCellIndex_eq_last
    (marks : Finset ℕ) {time : ℕ}
    (hindex : finiteClockActiveCellIndex marks time =
      finiteClockActiveCellCount marks - 1) :
    Even (finiteClockCellIndex marks time) := by
  by_contra hnotEven
  have hmem : time ∈ marks := by
    by_contra hnotMem
    apply hnotEven
    unfold finiteClockCellIndex
    rw [if_neg hnotMem]
    exact even_two_mul _
  have hrawLt : finiteClockCellIndex marks time <
      finiteClockCellIndex marks (time + 1) :=
    finiteClockCellIndex_lt_of_lt_of_mem_left marks
      (Nat.lt_succ_self time) hmem
  have hactiveLt := finiteClockActiveCellIndex_lt_of_cellIndex_lt
    marks hrawLt
  have hlater := finiteClockActiveCellIndex_lt_count marks (time + 1)
  rw [hindex] at hactiveLt
  have hcount := finiteClockActiveCellCount_pos marks
  omega

/-- Equal raw cell tags either come from the same natural date or from one
common unmarked gap. -/
theorem finiteClockCellIndex_eq_implies_eq_or_even
    (marks : Finset ℕ) {first second : ℕ}
    (heq : finiteClockCellIndex marks first =
      finiteClockCellIndex marks second) :
    first = second ∨ Even (finiteClockCellIndex marks first) := by
  by_cases hfirst : first = second
  · exact Or.inl hfirst
  · right
    have hnotMem : first ∉ marks := by
      intro hmem
      rcases lt_or_gt_of_ne hfirst with hlt | hgt
      · exact (ne_of_lt
          (finiteClockCellIndex_lt_of_lt_of_mem_left marks hlt hmem)) heq
      · have hsecond : second ∈ marks := by
          by_contra hsecond
          unfold finiteClockCellIndex at heq
          rw [if_pos hmem, if_neg hsecond] at heq
          omega
        have hlt := finiteClockCellIndex_lt_of_lt_of_mem_left
          marks hgt hsecond
        exact (ne_of_gt hlt) heq
    unfold finiteClockCellIndex
    rw [if_neg hnotMem]
    exact even_two_mul _

theorem finiteClockCellIndex_eq_of_between {marks : Finset ℕ}
    {first middle last cell : ℕ}
    (hfirst : finiteClockCellIndex marks first = cell)
    (hlast : finiteClockCellIndex marks last = cell)
    (hfm : first ≤ middle) (hml : middle ≤ last) :
    finiteClockCellIndex marks middle = cell := by
  have hmono := finiteClockCellIndex_mono marks
  exact le_antisymm ((hmono hml).trans_eq hlast)
    (hfirst ▸ hmono hfm)

theorem finiteClockCellIndex_not_mem_of_even {marks : Finset ℕ}
    {time cell : ℕ} (hindex : finiteClockCellIndex marks time = cell)
    (heven : Even cell) : time ∉ marks := by
  intro hmem
  unfold finiteClockCellIndex at hindex
  rw [if_pos hmem] at hindex
  rcases heven with ⟨k, hk⟩
  omega

theorem exists_finset_sum_gt_of_lt_tsum {α : Type*}
    (f : α → ENNReal) {x : ENNReal} (h : x < ∑' a, f a) :
    ∃ s : Finset α, x < ∑ a ∈ s, f a := by
  rw [(ENNReal.hasSum (f := f)).tsum_eq] at h
  exact lt_iSup_iff.mp h

open ProbabilityMassFunction

open Classical in
theorem pmfMass_some_pred_eq_tsum (law : PMF (Option ℕ)) (P : ℕ → Prop) :
    pmfMass (μ := law) (fun choice => ∃ time, choice = some time ∧ P time) =
      ∑' time : ℕ, if P time then law (some time) else 0 := by
  let E : Option ℕ → Prop := fun choice =>
    ∃ time, choice = some time ∧ P time
  let f : Option ℕ → ENNReal := pmfMask (μ := law) E
  let e := Equiv.optionEquivSumPUnit.{0, 0} ℕ
  have h : (∑' choice, f choice) =
      ∑' time : ℕ, if P time then law (some time) else 0 := by
    calc
      (∑' choice, f choice) = ∑' s, f (e.symm s) :=
        (e.symm.tsum_eq f).symm
      _ = (∑' time : ℕ, f (e.symm (Sum.inl time))) +
          ∑' never : PUnit.{1}, f (e.symm (Sum.inr never)) :=
        Summable.tsum_sum ENNReal.summable ENNReal.summable
      _ = _ := by
        have hnever : (∑' never : PUnit.{1},
            f (e.symm (Sum.inr never))) = 0 := by
          rw [tsum_eq_single PUnit.unit]
          · simp [f, e, pmfMask, E]
          · intro other hne
            rw [Subsingleton.elim other PUnit.unit] at hne
            exact (hne rfl).elim
        rw [hnever, add_zero]
        apply tsum_congr
        intro time
        simp [f, e, pmfMask, E]
  simpa only [pmfMass, f, E] using h

open Classical in
theorem stoppingLawCumulativeFiniteMass_eq_sum (law : PMF (Option ℕ))
    (cutoff : ℕ) :
    stoppingLawCumulativeFiniteMass law cutoff =
      ∑ time ∈ Finset.range (cutoff + 1), (law (some time)).toReal := by
  unfold stoppingLawCumulativeFiniteMass
  rw [show pmfMass (μ := law) (fun choice =>
      ∃ time ≤ cutoff, choice = some time) =
      pmfMass (μ := law) (fun choice =>
        ∃ time, choice = some time ∧ time ≤ cutoff) by
    congr 1
    funext choice
    apply propext
    aesop]
  rw [pmfMass_some_pred_eq_tsum]
  rw [tsum_eq_sum (s := Finset.range (cutoff + 1))]
  · rw [ENNReal.toReal_sum]
    · apply Finset.sum_congr rfl
      intro time htime
      simp only [Finset.mem_range] at htime
      simp [Nat.lt_succ_iff.mp htime]
    · intro time _
      split_ifs
      · exact PMF.apply_ne_top law (some time)
      · exact ENNReal.zero_ne_top
  · intro time htime
    simp only [Finset.mem_range, Nat.lt_succ_iff] at htime
    simp [Nat.not_le.mp htime]

/-- Total finite stopping mass in one quotient cell. -/
def stoppingLawFiniteClockCellMass (law : PMF (Option ℕ))
    (marks : Finset ℕ) (cell : ℕ) : ℝ :=
  (∑' time : ℕ,
    if finiteClockCellIndex marks time = cell then law (some time) else 0).toReal

open Classical in
/-- Every even common-quantile cell has total finite mass at most
`1 / level`.  The total is a `tsum`, so this includes the unbounded terminal
gap and thresholds approached without being attained. -/
theorem stoppingLawFiniteClockCellMass_le_one_div
    (law : PMF (Option ℕ)) {marks : Finset ℕ} {level : ℕ}
    (hlevel : 0 < level)
    (hmarks : stoppingLawQuantileMarks law level ⊆ marks)
    (cell : ℕ) (heven : Even cell) :
    stoppingLawFiniteClockCellMass law marks cell ≤ 1 / (level : ℝ) := by
  let mass : ENNReal := ∑' time : ℕ,
    if finiteClockCellIndex marks time = cell then law (some time) else 0
  let quantum : ENNReal := ENNReal.ofReal (1 / (level : ℝ))
  have hquantumNonneg : 0 ≤ (1 / (level : ℝ)) := by positivity
  have hmassTop : mass ≠ ⊤ := by
    have hcellLe : mass ≤ ∑' time : ℕ, law (some time) := by
      dsimp only [mass]
      apply ENNReal.tsum_le_tsum
      intro time
      split_ifs <;> simp
    have hsomeLe : (∑' time : ℕ, law (some time)) ≤
        ∑' choice : Option ℕ, law choice := by
      exact Summable.tsum_le_tsum_of_inj some (fun _ _ h => Option.some.inj h)
        (fun _ _ => zero_le) (fun _ => le_rfl)
        ENNReal.summable ENNReal.summable
    rw [PMF.tsum_coe] at hsomeLe
    exact ne_of_lt (hcellLe.trans hsomeLe |>.trans_lt ENNReal.one_lt_top)
  have hquantumTop : quantum ≠ ⊤ := ENNReal.ofReal_ne_top
  have htarget : mass ≤ quantum := by
    by_contra hnot
    have hstrict : quantum < mass := lt_of_not_ge hnot
    obtain ⟨sample, hsample⟩ :=
      exists_finset_sum_gt_of_lt_tsum
        (fun time : ℕ =>
          if finiteClockCellIndex marks time = cell then
            law (some time)
          else 0) hstrict
    let active := sample.filter fun time =>
      finiteClockCellIndex marks time = cell
    have hactiveSum : quantum < ∑ time ∈ active, law (some time) := by
      simpa only [active, Finset.sum_filter] using hsample
    have hactive : active.Nonempty := by
      by_contra hempty
      rw [Finset.not_nonempty_iff_eq_empty.mp hempty] at hactiveSum
      simp only [Finset.sum_empty] at hactiveSum
      exact (not_lt_of_ge bot_le) hactiveSum
    let first := active.min' hactive
    let last := active.max' hactive
    have hfirstMem : first ∈ active := Finset.min'_mem active hactive
    have hlastMem : last ∈ active := Finset.max'_mem active hactive
    have hfirstCell : finiteClockCellIndex marks first = cell :=
      (Finset.mem_filter.mp hfirstMem).2
    have hlastCell : finiteClockCellIndex marks last = cell :=
      (Finset.mem_filter.mp hlastMem).2
    have hfirstLeLast : first ≤ last :=
      Finset.min'_le active last hlastMem
    let weight : ℕ → ℝ := fun time => (law (some time)).toReal
    let lower : ℝ := ∑ time ∈ Finset.range first, weight time
    let upper : ℝ := stoppingLawCumulativeFiniteMass law last
    have hsumReal :
        1 / (level : ℝ) < ∑ time ∈ active, weight time := by
      have hactiveTop : (∑ time ∈ active, law (some time)) ≠ ⊤ :=
        ENNReal.sum_ne_top.mpr fun time _ =>
          PMF.apply_ne_top law (some time)
      have hreal := (ENNReal.toReal_lt_toReal hquantumTop hactiveTop).2
        hactiveSum
      simpa only [quantum, ENNReal.toReal_ofReal hquantumNonneg,
        ENNReal.toReal_sum (fun time _ => PMF.apply_ne_top law (some time)),
        weight] using hreal
    have hdisjoint : Disjoint (Finset.range first) active := by
      rw [Finset.disjoint_left]
      intro time htime htimeActive
      have hlt : time < first := Finset.mem_range.mp htime
      have hle : first ≤ time := Finset.min'_le active time htimeActive
      omega
    have hunionSubset : Finset.range first ∪ active ⊆
        Finset.range (last + 1) := by
      intro time htime
      rw [Finset.mem_union] at htime
      rw [Finset.mem_range, Nat.lt_succ_iff]
      rcases htime with hbefore | hactiveTime
      · exact (Finset.mem_range.mp hbefore).le.trans hfirstLeLast
      · exact Finset.le_max' active time hactiveTime
    have hlowerAdd :
        lower + ∑ time ∈ active, weight time ≤ upper := by
      rw [show upper = ∑ time ∈ Finset.range (last + 1), weight time by
        simpa only [weight] using
          stoppingLawCumulativeFiniteMass_eq_sum law last]
      rw [← Finset.sum_union hdisjoint]
      exact Finset.sum_le_sum_of_subset_of_nonneg hunionSubset
        (fun _ _ _ => ENNReal.toReal_nonneg)
    have hlowerNonneg : 0 ≤ lower :=
      Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg
    have hupperOne : upper ≤ 1 :=
      stoppingLawCumulativeFiniteMass_le_one law last
    have hwidth : 1 / (level : ℝ) < upper - lower := by
      linarith
    obtain ⟨index, hlowerGrid, hgridUpper⟩ :=
      exists_positive_grid_point_of_one_div_lt_sub
        hlevel hlowerNonneg hupperOne hwidth
    let threshold : ℝ :=
      ((index.val + 1 : ℕ) : ℝ) / (level : ℝ)
    have hlowerThreshold : lower < threshold := hlowerGrid
    have hthresholdUpper : threshold < upper := hgridUpper
    have hcross : ∃ cutoff,
        threshold ≤ stoppingLawCumulativeFiniteMass law cutoff :=
      ⟨last, hgridUpper.le⟩
    let cutoff := Nat.find hcross
    have hcrossEq :
        stoppingLawFirstCrossing? law threshold = some cutoff := by
      unfold stoppingLawFirstCrossing?
      rw [dif_pos hcross]
    have hspec := stoppingLawFirstCrossing?_spec law threshold hcrossEq
    have hcutoffCross := hspec.1
    have hcutoffLeLast : cutoff ≤ last :=
      Nat.find_min' hcross hgridUpper.le
    have hfirstLeCutoff : first ≤ cutoff := by
      by_contra hnotFirst
      have hcutoffLtFirst : cutoff < first := Nat.lt_of_not_ge hnotFirst
      have hfirstPos : 0 < first := by omega
      have hcutoffLePred : cutoff ≤ first - 1 := by omega
      have hcumulativeLe :
          stoppingLawCumulativeFiniteMass law cutoff ≤ lower := by
        have hmono := stoppingLawCumulativeFiniteMass_mono law hcutoffLePred
        have hpred :
            stoppingLawCumulativeFiniteMass law (first - 1) = lower := by
          rw [stoppingLawCumulativeFiniteMass_eq_sum]
          have hpredSucc : first - 1 + 1 = first := by omega
          simp only [hpredSucc, lower, weight]
        exact hmono.trans_eq hpred
      linarith
    have hcutoffCell : finiteClockCellIndex marks cutoff = cell :=
      finiteClockCellIndex_eq_of_between hfirstCell hlastCell
        hfirstLeCutoff hcutoffLeLast
    have hownMark : cutoff ∈ stoppingLawQuantileMarks law level := by
      unfold stoppingLawQuantileMarks
      rw [Finset.mem_biUnion]
      refine ⟨index, Finset.mem_univ index, ?_⟩
      simp only [threshold, hcrossEq, Finset.mem_singleton]
    have hcommonMark : cutoff ∈ marks := hmarks hownMark
    exact (finiteClockCellIndex_not_mem_of_even hcutoffCell heven) hcommonMark
  unfold stoppingLawFiniteClockCellMass
  change mass.toReal ≤ _
  rw [← ENNReal.toReal_ofReal hquantumNonneg]
  exact (ENNReal.toReal_le_toReal hmassTop hquantumTop).2 htarget

open Classical in
theorem finiteClockCompressedLaw_some_toReal_eq_cellMass
    (law : PMF (Option ℕ)) (marks : Finset ℕ) (cell : ℕ) :
    (finiteClockCompressedLaw law marks (some cell)).toReal =
      stoppingLawFiniteClockCellMass law marks cell := by
  unfold finiteClockCompressedLaw
  change (ProbabilityMassFunction.pushforward law
    (finiteClockQuotient marks) (some cell)).toReal = _
  rw [ProbabilityMassFunction.pushforward_apply_eq_pmfMass]
  rw [show ProbabilityMassFunction.pmfMass (μ := law)
      (fun choice => finiteClockQuotient marks choice = some cell) =
      ProbabilityMassFunction.pmfMass (μ := law)
        (fun choice => ∃ time,
          choice = some time ∧ finiteClockCellIndex marks time = cell) by
    congr 1
    funext choice
    apply propext
    cases choice <;> simp]
  rw [pmfMass_some_pred_eq_tsum]
  unfold stoppingLawFiniteClockCellMass
  congr 1
  apply tsum_congr
  intro time
  by_cases hcell : finiteClockCellIndex marks time = cell <;>
    simp [hcell]

theorem stoppingLawQuantileMarks_subset_common {ι : Type*} [Fintype ι]
    (laws : ι → PMF (Option ℕ)) (level : ℕ) (who : ι) :
    stoppingLawQuantileMarks (laws who) level ⊆
      commonStoppingLawQuantileMarks laws level := by
  intro time htime
  unfold commonStoppingLawQuantileMarks
  rw [Finset.mem_biUnion]
  exact ⟨who, Finset.mem_univ who, htime⟩

open Classical in
/-- A compressed marginal assigns at most `1 / level` to every even common
gap cell. -/
theorem finiteClockCompressedLaw_common_even_cell_toReal_le_one_div
    {ι : Type*} [Fintype ι] (laws : ι → PMF (Option ℕ))
    {level : ℕ} (hlevel : 0 < level) (who : ι)
    (cell : ℕ) (heven : Even cell) :
    (finiteClockCompressedLaw (laws who)
      (commonStoppingLawQuantileMarks laws level) (some cell)).toReal ≤
        1 / (level : ℝ) := by
  rw [finiteClockCompressedLaw_some_toReal_eq_cellMass]
  exact stoppingLawFiniteClockCellMass_le_one_div (laws who) hlevel
    (stoppingLawQuantileMarks_subset_common laws level who) cell heven

end Probability
end Math
