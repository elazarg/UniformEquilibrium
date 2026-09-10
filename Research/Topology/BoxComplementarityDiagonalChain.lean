import Research.Topology.BoxComplementaritySignedLocalCount
import MathUE.Topology.KuhnSimplexOrientation
import Mathlib.Data.Finset.Sort

/-!
# The actual centered diagonal chain and its signed weight

The negative coordinates rise in increasing order, followed by the positive
coordinates in decreasing order. The literal labels insert the dimension
label between these two groups. This constructs one complete central-cell
simplex and computes its weight; uniqueness and the local count are separate.
-/

noncomputable section

namespace Math

open Classical Set

variable {n : ℕ}

/-- Selected coordinates in increasing order, then the complement in decreasing order. -/
def diagonalCoordinateOrder (negative : Finset (Fin n)) (index : Fin n) : Fin n :=
  if hindex : index.val < negative.card then
    negative.orderEmbOfFin rfl ⟨index.val, hindex⟩
  else
    negativeᶜ.orderEmbOfFin rfl (Fin.rev ⟨index.val - negative.card, by
      have hcard := Finset.card_compl negative
      simp only [Fintype.card_fin] at hcard
      have hbound := index.isLt
      omega⟩)

theorem diagonalCoordinateOrder_mem_iff (negative : Finset (Fin n)) (index : Fin n) :
    diagonalCoordinateOrder negative index ∈ negative ↔ index.val < negative.card := by
  unfold diagonalCoordinateOrder
  split_ifs with hindex
  · simp only [hindex, iff_true]
    exact negative.orderEmbOfFin_mem rfl _
  · simp only [hindex, iff_false]
    exact Finset.mem_compl.mp (negativeᶜ.orderEmbOfFin_mem rfl _)

theorem diagonalCoordinateOrder_injective (negative : Finset (Fin n)) :
    Function.Injective (diagonalCoordinateOrder negative) := by
  intro first second heq
  have hmem : first.val < negative.card ↔ second.val < negative.card := by
    rw [← diagonalCoordinateOrder_mem_iff, ← diagonalCoordinateOrder_mem_iff, heq]
  unfold diagonalCoordinateOrder at heq
  by_cases hfirst : first.val < negative.card
  · rw [dif_pos hfirst, dif_pos (hmem.mp hfirst)] at heq
    have hval := congrArg (fun i : Fin negative.card => i.val)
      ((negative.orderEmbOfFin rfl).injective heq)
    exact Fin.ext hval
  · have hsecond : ¬second.val < negative.card := fun h => hfirst (hmem.mpr h)
    rw [dif_neg hfirst, dif_neg hsecond] at heq
    have hsub := congrArg Fin.val (Fin.rev_injective
      ((negativeᶜ.orderEmbOfFin rfl).injective heq))
    exact Fin.ext (by dsimp at hsub; omega)

/-- The displayed coordinate order is an actual permutation, including the empty case. -/
def diagonalCoordinatePermutation (negative : Finset (Fin n)) : Equiv.Perm (Fin n) :=
  Equiv.ofBijective (diagonalCoordinateOrder negative)
    ((Fintype.bijective_iff_injective_and_card _).mpr
      ⟨diagonalCoordinateOrder_injective negative, rfl⟩)

theorem diagonalCoordinatePermutation_mem_iff (negative : Finset (Fin n)) (index : Fin n) :
    diagonalCoordinatePermutation negative index ∈ negative ↔ index.val < negative.card :=
  diagonalCoordinateOrder_mem_iff negative index

theorem diagonalCoordinatePermutation_mono_negative (negative : Finset (Fin n))
    {first second : Fin n} (hfirst : first.val < negative.card)
    (hsecond : second.val < negative.card) (hle : first ≤ second) :
    diagonalCoordinatePermutation negative first ≤
      diagonalCoordinatePermutation negative second := by
  change diagonalCoordinateOrder negative first ≤ diagonalCoordinateOrder negative second
  simp only [diagonalCoordinateOrder, dif_pos hfirst, dif_pos hsecond]
  exact (negative.orderEmbOfFin rfl).monotone hle

theorem diagonalCoordinatePermutation_anti_positive (negative : Finset (Fin n))
    {first second : Fin n} (hfirst : negative.card ≤ first.val)
    (hsecond : negative.card ≤ second.val) (hle : first ≤ second) :
    diagonalCoordinatePermutation negative second ≤
      diagonalCoordinatePermutation negative first := by
  change diagonalCoordinateOrder negative second ≤ diagonalCoordinateOrder negative first
  simp only [diagonalCoordinateOrder, dif_neg (not_lt.mpr hfirst),
    dif_neg (not_lt.mpr hsecond)]
  apply (negativeᶜ.orderEmbOfFin rfl).monotone
  apply Fin.rev_strictAnti.antitone
  change first.val - negative.card ≤ second.val - negative.card
  exact Nat.sub_le_sub_right hle negative.card

/-- The literal negative pullback of a centered diagonal field. -/
def centeredDiagonalProblem (entries : Fin n → ℝ) : BoxComplementarityProblem (Fin n) where
  gain point who := -entries who * ((point who : ℝ) - 1 / 2)
  continuous_gain who :=
    (((continuous_apply who).subtype_val).sub continuous_const).const_mul _

/-- A unit central-cell chain at the odd mesh `2 * k + 1`, in a given coordinate order. -/
def diagonalCentralChain (permutation : Equiv.Perm (Fin n)) (k : ℕ)
    (index : Fin (n + 1)) (who : Fin n) : Fin (2 * k + 1 + 1) :=
  ⟨k + if (permutation.symm who).val < index.val then 1 else 0, by split_ifs <;> omega⟩

theorem diagonalCentralChain_injective (permutation : Equiv.Perm (Fin n)) (k : ℕ) :
    Function.Injective (diagonalCentralChain permutation k) := by
  suffices ∀ first second : Fin (n + 1), first < second →
      diagonalCentralChain permutation k first ≠ diagonalCentralChain permutation k second by
    intro first second heq
    rcases lt_trichotomy first second with hlt | hequal | hgt
    · exact False.elim (this first second hlt heq)
    · exact hequal
    · exact False.elim (this second first hgt heq.symm)
  intro first second hlt heq
  have hstepBound : first.val < n := by
    have := second.isLt
    change first.val < second.val at hlt
    omega
  let step : Fin n := ⟨first.val, hstepBound⟩
  have hcoord := congrArg (fun vertex => (vertex (permutation step)).val) heq
  simp only [diagonalCentralChain, Equiv.symm_apply_apply] at hcoord
  have hfirst : ¬step.val < first.val := by dsimp [step]; omega
  have hsecond : step.val < second.val := hlt
  rw [if_neg hfirst, if_pos hsecond] at hcoord
  omega

theorem simplex_diagonalCentralChain (entries : Fin n → ℝ)
    (permutation : Equiv.Perm (Fin n)) (k : ℕ) :
    simplex (boxComplementaritySpernerCube (centeredDiagonalProblem entries)
      (2 * k + 1) (by omega)) n (diagonalCentralChain permutation k) := by
  apply simplex_of_step_le _ (diagonalCentralChain_injective permutation k)
  · intro step who
    change k + (if (permutation.symm who).val < step.val then 1 else 0) ≤
      k + (if (permutation.symm who).val < step.val + 1 then 1 else 0)
    split_ifs <;> omega
  · intro who
    change k + (if (permutation.symm who).val < n then 1 else 0) ≤
      k + (if (permutation.symm who).val < 0 then 1 else 0) + 1
    split_ifs <;> omega

theorem diagonalCentralChain_step (permutation : Equiv.Perm (Fin n)) (k : ℕ)
    (step : Fin n) (who : Fin n) :
    ((diagonalCentralChain permutation k step.succ who).val : ℤ) =
      ((diagonalCentralChain permutation k step.castSucc who).val : ℤ) +
        if who = permutation step then 1 else 0 := by
  have heq : who = permutation step ↔ (permutation.symm who).val = step.val := by
    rw [← Fin.ext_iff, Equiv.symm_apply_eq]
  simp only [diagonalCentralChain, Fin.val_succ, Fin.val_castSucc, Nat.cast_add, heq]
  split_ifs <;> simp_all <;> omega

theorem determinant_diagonalCentralChain (permutation : Equiv.Perm (Fin n)) (k : ℕ) :
    OrientedSimplexFacet.determinant
      (fun index who => ((diagonalCentralChain permutation k index who).val : ℤ)) =
        (Equiv.Perm.sign permutation : ℤ) :=
  KuhnSimplex.determinant_eq_sign_of_unitCoordinatePermutation _ permutation
    (diagonalCentralChain_step permutation k)

theorem gridPoint_diagonalCentralChain_interior (permutation : Equiv.Perm (Fin n))
    {k : ℕ} (hk : 0 < k) (index : Fin (n + 1)) (who : Fin n) :
    0 < (boxComplementarityGridPoint (2 * k + 1)
      (diagonalCentralChain permutation k index) who : ℝ) ∧
    (boxComplementarityGridPoint (2 * k + 1)
      (diagonalCentralChain permutation k index) who : ℝ) < 1 := by
  have hkReal : (0 : ℝ) < k := by exact_mod_cast hk
  dsimp [boxComplementarityGridPoint, diagonalCentralChain]
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  split_ifs <;> simp only [Nat.cast_one, Nat.cast_zero] <;> constructor
  all_goals first | positivity | (apply (div_lt_one (by positivity)).mpr; linarith)

theorem isGridViolation_diagonalCentralChain_iff (entries : Fin n → ℝ)
    (permutation : Equiv.Perm (Fin n)) {k : ℕ} (hk : 0 < k)
    (index : Fin (n + 1)) (who : Fin n) :
    (centeredDiagonalProblem entries).IsGridViolation (2 * k + 1)
        (diagonalCentralChain permutation k index) who ↔
      (entries who < 0 ∧ index.val ≤ (permutation.symm who).val) ∨
        (0 < entries who ∧ (permutation.symm who).val < index.val) := by
  have hinterior := gridPoint_diagonalCentralChain_interior permutation hk index who
  have hkReal : (0 : ℝ) < k := by exact_mod_cast hk
  have hden : (0 : ℝ) < 2 * k + 1 := by positivity
  simp only [BoxComplementarityProblem.IsGridViolation, centeredDiagonalProblem,
    hinterior.1, hinterior.2.ne, true_and, or_false]
  change -entries who *
    (((k + if (permutation.symm who).val < index.val then 1 else 0 : ℕ) : ℝ) /
      (2 * k + 1 : ℕ) - 1 / 2) < 0 ↔ _
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  by_cases hraised : (permutation.symm who).val < index.val
  · rw [if_pos hraised]
    have hpositive : (0 : ℝ) < ((k : ℝ) + 1) / (2 * k + 1) - 1 / 2 := by
      apply sub_pos.mpr
      apply (lt_div_iff₀ hden).mpr
      linarith
    simp only [Nat.cast_one, hraised, not_le.mpr hraised, and_false, false_or, and_true]
    constructor <;> intro h <;> nlinarith
  · rw [if_neg hraised, Nat.cast_zero, add_zero]
    have hnegative : (k : ℝ) / (2 * k + 1) - 1 / 2 < 0 := by
      apply sub_neg.mpr
      apply (div_lt_iff₀ hden).mpr
      linarith
    simp only [Nat.cast_one, hraised, Nat.le_of_not_lt hraised, and_true, and_false, or_false]
    constructor <;> intro h <;> nlinarith

def diagonalNegativeCoordinates (entries : Fin n → ℝ) : Finset (Fin n) :=
  Finset.univ.filter (fun who => entries who < 0)

theorem diagonalNegativeCoordinates_card_le (entries : Fin n → ℝ) :
    (diagonalNegativeCoordinates entries).card ≤ n := by
  simpa only [Fintype.card_fin] using
    Finset.card_le_univ (diagonalNegativeCoordinates entries)

theorem isGridViolation_diagonalOrderedChain_iff (entries : Fin n → ℝ)
    (hentries : ∀ who, entries who ≠ 0) {k : ℕ} (hk : 0 < k)
    (index : Fin (n + 1)) (step : Fin n) :
    let negative := diagonalNegativeCoordinates entries
    let permutation := diagonalCoordinatePermutation negative
    (centeredDiagonalProblem entries).IsGridViolation (2 * k + 1)
        (diagonalCentralChain permutation k index) (permutation step) ↔
      (step.val < negative.card ∧ index.val ≤ step.val) ∨
        (negative.card ≤ step.val ∧ step.val < index.val) := by
  dsimp only
  let negative := diagonalNegativeCoordinates entries
  let permutation := diagonalCoordinatePermutation negative
  have hnegative : entries (permutation step) < 0 ↔ step.val < negative.card := by
    simpa only [negative, permutation, diagonalNegativeCoordinates,
      Finset.mem_filter, Finset.mem_univ, true_and]
      using diagonalCoordinatePermutation_mem_iff negative step
  have hpositive : 0 < entries (permutation step) ↔ negative.card ≤ step.val := by
    rw [← not_lt, ← hnegative]
    exact ⟨fun h => not_lt.mpr h.le,
      fun h => lt_of_le_of_ne (not_lt.mp h) (Ne.symm (hentries _))⟩
  simpa only [Equiv.symm_apply_apply, hnegative, hpositive] using
    isGridViolation_diagonalCentralChain_iff entries permutation hk index (permutation step)

private theorem reducedLabel_eq_of_min_violation
    (problem : BoxComplementarityProblem (Fin n)) (p : ℕ)
    (vertex : Fin n → Fin (p + 1)) (target : Fin n)
    (hactive : problem.IsGridViolation p vertex target)
    (hmin : ∀ who, problem.IsGridViolation p vertex who → target ≤ who) :
    boxComplementarityReducedLabel problem p vertex = target.val := by
  have hproperties := boxComplementarityReducedLabel_properties problem p vertex
  apply le_antisymm ((hproperties.2 target).2 hactive)
  by_cases hlt : boxComplementarityReducedLabel problem p vertex < n
  · exact hmin ⟨_, hlt⟩ ((hproperties.2 ⟨_, hlt⟩).1 rfl)
  · omega

private theorem reducedLabel_eq_last_of_no_violation
    (problem : BoxComplementarityProblem (Fin n)) (p : ℕ)
    (vertex : Fin n → Fin (p + 1))
    (hno : ∀ who, ¬problem.IsGridViolation p vertex who) :
    boxComplementarityReducedLabel problem p vertex = n := by
  have hproperties := boxComplementarityReducedLabel_properties problem p vertex
  by_contra hne
  have hlt : boxComplementarityReducedLabel problem p vertex < n := by omega
  exact hno ⟨_, hlt⟩ ((hproperties.2 ⟨_, hlt⟩).1 rfl)

theorem finLabel_diagonalOrderedChain_before (entries : Fin n → ℝ)
    (hentries : ∀ who, entries who ≠ 0) {k : ℕ} (hk : 0 < k)
    (index : Fin (n + 1))
    (hindex : index.val < (diagonalNegativeCoordinates entries).card) :
    boxComplementarityFinLabel (centeredDiagonalProblem entries) (2 * k + 1)
      (diagonalCentralChain
        (diagonalCoordinatePermutation (diagonalNegativeCoordinates entries)) k index) =
      (diagonalCoordinatePermutation (diagonalNegativeCoordinates entries)
        ⟨index.val, lt_of_lt_of_le hindex
          (diagonalNegativeCoordinates_card_le entries)⟩).castSucc := by
  let negative := diagonalNegativeCoordinates entries
  let permutation := diagonalCoordinatePermutation negative
  let target : Fin n := ⟨index.val,
    lt_of_lt_of_le hindex (diagonalNegativeCoordinates_card_le entries)⟩
  apply Fin.ext
  apply reducedLabel_eq_of_min_violation _ _ _ (permutation target)
  · exact (isGridViolation_diagonalOrderedChain_iff entries hentries hk index target).mpr
      (Or.inl ⟨hindex, le_rfl⟩)
  · intro who hactive
    obtain ⟨step, rfl⟩ := permutation.surjective who
    have hstep := (isGridViolation_diagonalOrderedChain_iff
      entries hentries hk index step).mp hactive
    rcases hstep with ⟨hnegative, hle⟩ | ⟨hpositive, hlt⟩
    · exact diagonalCoordinatePermutation_mono_negative negative hindex hnegative hle
    · change negative.card ≤ step.val at hpositive
      change index.val < negative.card at hindex
      omega

theorem finLabel_diagonalOrderedChain_pivot (entries : Fin n → ℝ)
    (hentries : ∀ who, entries who ≠ 0) {k : ℕ} (hk : 0 < k) :
    boxComplementarityFinLabel (centeredDiagonalProblem entries) (2 * k + 1)
      (diagonalCentralChain
        (diagonalCoordinatePermutation (diagonalNegativeCoordinates entries)) k
        ⟨(diagonalNegativeCoordinates entries).card,
          Nat.lt_succ_of_le (diagonalNegativeCoordinates_card_le entries)⟩) = Fin.last n := by
  apply Fin.ext
  apply reducedLabel_eq_last_of_no_violation
  intro who hactive
  obtain ⟨step, rfl⟩ :=
    (diagonalCoordinatePermutation (diagonalNegativeCoordinates entries)).surjective who
  have hstep := (isGridViolation_diagonalOrderedChain_iff
    entries hentries hk _ step).mp hactive
  dsimp only at hstep
  omega

theorem finLabel_diagonalOrderedChain_after (entries : Fin n → ℝ)
    (hentries : ∀ who, entries who ≠ 0) {k : ℕ} (hk : 0 < k)
    (index : Fin (n + 1))
    (hindex : (diagonalNegativeCoordinates entries).card < index.val) :
    boxComplementarityFinLabel (centeredDiagonalProblem entries) (2 * k + 1)
      (diagonalCentralChain
        (diagonalCoordinatePermutation (diagonalNegativeCoordinates entries)) k index) =
      (diagonalCoordinatePermutation (diagonalNegativeCoordinates entries)
        ⟨index.val - 1, by have := index.isLt; omega⟩).castSucc := by
  let negative := diagonalNegativeCoordinates entries
  let permutation := diagonalCoordinatePermutation negative
  let target : Fin n := ⟨index.val - 1, by have := index.isLt; omega⟩
  have htarget : negative.card ≤ target.val := by dsimp [target, negative]; omega
  have htargetIndex : target.val < index.val := by dsimp [target]; omega
  apply Fin.ext
  apply reducedLabel_eq_of_min_violation _ _ _ (permutation target)
  · exact (isGridViolation_diagonalOrderedChain_iff entries hentries hk index target).mpr
      (Or.inr ⟨htarget, htargetIndex⟩)
  · intro who hactive
    obtain ⟨step, rfl⟩ := permutation.surjective who
    have hstep := (isGridViolation_diagonalOrderedChain_iff
      entries hentries hk index step).mp hactive
    rcases hstep with ⟨hnegative, hle⟩ | ⟨hpositive, hlt⟩
    · change step.val < negative.card at hnegative
      change negative.card < index.val at hindex
      omega
    · apply diagonalCoordinatePermutation_anti_positive negative hpositive htarget
      change step.val ≤ index.val - 1
      omega

theorem finLabel_diagonalOrderedChain_eq_insertNth (entries : Fin n → ℝ)
    (hentries : ∀ who, entries who ≠ 0) {k : ℕ} (hk : 0 < k) :
    (fun index => boxComplementarityFinLabel (centeredDiagonalProblem entries) (2 * k + 1)
      (diagonalCentralChain
        (diagonalCoordinatePermutation (diagonalNegativeCoordinates entries)) k index)) =
      Fin.insertNth
        ⟨(diagonalNegativeCoordinates entries).card,
          Nat.lt_succ_of_le (diagonalNegativeCoordinates_card_le entries)⟩
        (Fin.last n) (fun step =>
          (diagonalCoordinatePermutation (diagonalNegativeCoordinates entries) step).castSucc) := by
  let pivot : Fin (n + 1) := ⟨(diagonalNegativeCoordinates entries).card,
    Nat.lt_succ_of_le (diagonalNegativeCoordinates_card_le entries)⟩
  change _ = (Fin.insertNth pivot (Fin.last n) (fun step =>
    (diagonalCoordinatePermutation (diagonalNegativeCoordinates entries) step).castSucc) :
      Fin (n + 1) → Fin (n + 1))
  funext index
  cases index using Fin.succAboveCases pivot with
  | x =>
    simp only [Fin.insertNth_apply_same]
    exact finLabel_diagonalOrderedChain_pivot entries hentries hk
  | p step =>
    simp only [Fin.insertNth_apply_succAbove]
    by_cases hstep : step.val < (diagonalNegativeCoordinates entries).card
    · have hlt : step.castSucc < pivot := hstep
      rw [Fin.succAbove_of_castSucc_lt _ _ hlt]
      exact finLabel_diagonalOrderedChain_before entries hentries hk step.castSucc hstep
    · have hle : pivot ≤ step.castSucc := Nat.le_of_not_lt hstep
      rw [Fin.succAbove_of_le_castSucc _ _ hle]
      have hafter : (diagonalNegativeCoordinates entries).card < step.succ.val := by
        change _ < step.val + 1
        omega
      simpa only [Fin.val_succ, Nat.add_sub_cancel, Fin.eta] using
        finLabel_diagonalOrderedChain_after entries hentries hk step.succ hafter

/-- The canonical central chain is complete for the literal diagonal labels. -/
theorem completeSimplex_diagonalOrderedChain (entries : Fin n → ℝ)
    (hentries : ∀ who, entries who ≠ 0) {k : ℕ} (hk : 0 < k) :
    complete_simplex (boxComplementaritySpernerCube (centeredDiagonalProblem entries)
      (2 * k + 1) (by omega)) n
      (diagonalCentralChain
        (diagonalCoordinatePermutation (diagonalNegativeCoordinates entries)) k) := by
  apply (boxComplementarity_completeSimplex_iff_finLabel_injective _ _ _ _).mpr
  refine ⟨simplex_diagonalCentralChain _ _ _, ?_⟩
  rw [finLabel_diagonalOrderedChain_eq_insertNth entries hentries hk]
  exact SignedSimplexLabel.injective_insertNth_last_castSucc _ _

/-- Actual geometric-times-label signed weight of the constructed complete chain. -/
theorem signedWeight_diagonalOrderedChain (entries : Fin n → ℝ)
    (hentries : ∀ who, entries who ≠ 0) {k : ℕ} (hk : 0 < k) :
    boxComplementarityCompleteSimplexSignedWeight (centeredDiagonalProblem entries)
      (2 * k + 1) (by omega)
      (diagonalCentralChain
        (diagonalCoordinatePermutation (diagonalNegativeCoordinates entries)) k) =
      (-1 : ℤ) ^ n * (-1 : ℤ) ^ (diagonalNegativeCoordinates entries).card := by
  rw [boxComplementarityCompleteSimplexSignedWeight_eq _ _ _ _
    (completeSimplex_diagonalOrderedChain entries hentries hk)]
  change OrientedSimplexFacet.determinant
    (fun index who => ((diagonalCentralChain
      (diagonalCoordinatePermutation (diagonalNegativeCoordinates entries)) k index who).val : ℤ)) *
      SignedSimplexLabel.orientation (fun index => boxComplementarityFinLabel
        (centeredDiagonalProblem entries) (2 * k + 1) (diagonalCentralChain
          (diagonalCoordinatePermutation (diagonalNegativeCoordinates entries)) k index)) = _
  rw [determinant_diagonalCentralChain,
    finLabel_diagonalOrderedChain_eq_insertNth entries hentries hk,
    SignedSimplexLabel.orientation_insertNth_last_castSucc]
  have hsquare : (Equiv.Perm.sign
      (diagonalCoordinatePermutation (diagonalNegativeCoordinates entries)) : ℤ) ^ 2 = 1 := by
    simpa only [Units.val_pow_eq_pow_val, Units.val_one] using
      congrArg (fun unit : ℤˣ => (unit : ℤ)) (Int.units_sq (Equiv.Perm.sign
        (diagonalCoordinatePermutation (diagonalNegativeCoordinates entries))))
  dsimp only
  calc
    _ = ((-1 : ℤ) ^ n * (-1 : ℤ) ^ (diagonalNegativeCoordinates entries).card) *
        (Equiv.Perm.sign
          (diagonalCoordinatePermutation (diagonalNegativeCoordinates entries)) : ℤ) ^ 2 := by
      ring
    _ = _ := by rw [hsquare, mul_one]

end Math
