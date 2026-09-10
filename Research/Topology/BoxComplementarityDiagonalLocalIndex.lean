import Research.Topology.BoxComplementarityDiagonalChain
import Research.Topology.BoxComplementarityStabilizedLocalDegree
import Mathlib.Data.Sign.Basic

/-!
# Actual local signed count and index of a centered diagonal field

On the fixed coordinate neighborhood `(1/4, 3/4)`, every complete simplex
selected by its actual dimension-label anchor is the previously constructed
central chain at each odd mesh at least five. The two cube-boundary label
clips are explicitly excluded before the central-cell and uniqueness arguments.
The resulting normalized local degree is the integer sign of the diagonal
determinant. No general affine-map or arbitrary-chart comparison is asserted.
-/

noncomputable section

namespace Math

open Classical Set

variable {n : ℕ}

/-- The fixed central counting neighborhood, interpreted inside the reference cube. -/
def diagonalCentralRegion (n : ℕ) : Set (UnitCube (Fin n)) :=
  {point | ∀ who, 1 / 4 < (point who : ℝ) ∧ (point who : ℝ) < 3 / 4}

/-- Fine enough anchor selection removes both boundary clips from every vertex. -/
theorem gridPoint_interior_of_anchor_mem_diagonalCentralRegion
    (problem : BoxComplementarityProblem (Fin n)) {p : ℕ} (hp : 5 ≤ p)
    (vertices : Fin (n + 1) → Fin n → Fin (p + 1))
    (hcomplete : complete_simplex (boxComplementaritySpernerCube problem p (by omega)) n vertices)
    (hanchor : boxComplementarityCompleteSimplexAnchorPoint problem p (by omega)
      vertices hcomplete ∈ diagonalCentralRegion n)
    (index : Fin (n + 1)) (who : Fin n) :
    0 < (boxComplementarityGridPoint p (vertices index) who : ℝ) ∧
      (boxComplementarityGridPoint p (vertices index) who : ℝ) < 1 := by
  let anchor := boxComplementarityCompleteSimplexAnchorIndex problem p (by omega)
    vertices hcomplete
  have hanchorCoord := hanchor who
  change 1 / 4 < ((vertices anchor who).val : ℝ) / p ∧
    ((vertices anchor who).val : ℝ) / p < 3 / 4 at hanchorCoord
  have hpReal : (5 : ℝ) ≤ p := by exact_mod_cast hp
  have hpositive : (0 : ℝ) < p := by linarith
  have hlow := (lt_div_iff₀ hpositive).mp hanchorCoord.1
  have hupp := (div_lt_iff₀ hpositive).mp hanchorCoord.2
  have hstepLow : ((vertices anchor who).val : ℝ) ≤ (vertices index who).val + 1 := by
    exact_mod_cast spernerSimplex_val_le_succ hcomplete.1 anchor index who
  have hstepUpp : ((vertices index who).val : ℝ) ≤ (vertices anchor who).val + 1 := by
    exact_mod_cast spernerSimplex_val_le_succ hcomplete.1 index anchor who
  change 0 < ((vertices index who).val : ℝ) / p ∧
    ((vertices index who).val : ℝ) / p < 1
  constructor
  · exact div_pos (by linarith) hpositive
  · apply (div_lt_one hpositive).mpr
    linarith

/-- Every vertex of the displayed central chain lies in the counting region. -/
theorem gridPoint_diagonalCentralChain_mem_region
    (permutation : Equiv.Perm (Fin n)) {k : ℕ} (hk : 0 < k)
    (index : Fin (n + 1)) :
    boxComplementarityGridPoint (2 * k + 1) (diagonalCentralChain permutation k index) ∈
      diagonalCentralRegion n := by
  intro who
  have hkReal : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hden : (0 : ℝ) < 2 * k + 1 := by positivity
  dsimp [boxComplementarityGridPoint, diagonalCentralChain]
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  split_ifs <;> simp only [Nat.cast_one, Nat.cast_zero] <;> constructor
  all_goals first
    | (apply (lt_div_iff₀ hden).mpr; linarith)
    | (apply (div_lt_iff₀ hden).mpr; linarith)

/-- The actual complete canonical chain is selected by its actual label-dimension anchor. -/
theorem diagonalOrderedChain_mem_localCompleteSimplices (entries : Fin n → ℝ)
    (hentries : ∀ who, entries who ≠ 0) {k : ℕ} (hk : 0 < k) :
    diagonalCentralChain
        (diagonalCoordinatePermutation (diagonalNegativeCoordinates entries)) k ∈
      boxComplementarityLocalCompleteSimplices (centeredDiagonalProblem entries)
        (2 * k + 1) (by omega) (diagonalCentralRegion n) := by
  apply (mem_boxComplementarityLocalCompleteSimplices_iff _ _ _ _ _).mpr
  refine ⟨completeSimplex_diagonalOrderedChain entries hentries hk, ?_⟩
  exact gridPoint_diagonalCentralChain_mem_region _ hk _

private theorem oddGrid_le_half_iff (k value : ℕ) :
    (value : ℝ) / (2 * k + 1) ≤ 1 / 2 ↔ value ≤ k := by
  have hden : (0 : ℝ) < 2 * k + 1 := by positivity
  rw [div_le_iff₀ hden]
  constructor
  · intro h
    have hdouble : 2 * value ≤ 2 * k + 1 := by
      exact_mod_cast (by linarith : (2 : ℝ) * value ≤ 2 * k + 1)
    omega
  · intro h
    have hreal : (value : ℝ) ≤ k := by exact_mod_cast h
    linarith

private theorem half_le_oddGrid_iff (k value : ℕ) :
    1 / 2 ≤ (value : ℝ) / (2 * k + 1) ↔ k + 1 ≤ value := by
  have hden : (0 : ℝ) < 2 * k + 1 := by positivity
  rw [le_div_iff₀ hden]
  constructor
  · intro h
    have hdouble : 2 * k + 1 ≤ 2 * value := by
      exact_mod_cast (by linarith : (2 : ℝ) * k + 1 ≤ 2 * value)
    omega
  · intro h
    have hreal : (k : ℝ) + 1 ≤ value := by exact_mod_cast h
    linarith

/-- Local selection forces the initial vertex to be the central-cell base.
This conclusion does not require a separate nonzero-entry hypothesis. -/
theorem initial_eq_center_of_anchor_mem (entries : Fin n → ℝ)
    {k : ℕ} (hk : 2 ≤ k)
    (vertices : Fin (n + 1) → Fin n → Fin (2 * k + 1 + 1))
    (hcomplete : complete_simplex (boxComplementaritySpernerCube
      (centeredDiagonalProblem entries) (2 * k + 1) (by omega)) n vertices)
    (hanchor : boxComplementarityCompleteSimplexAnchorPoint
      (centeredDiagonalProblem entries) (2 * k + 1) (by omega)
      vertices hcomplete ∈ diagonalCentralRegion n) (who : Fin n) :
    (vertices 0 who).val = k := by
  let problem := centeredDiagonalProblem entries
  let anchor := boxComplementarityCompleteSimplexAnchorIndex problem (2 * k + 1)
    (by omega) vertices hcomplete
  let carrier := boxComplementarityCompleteSimplexCoordinateIndex problem (2 * k + 1)
    (by omega) vertices hcomplete who
  have hinterior := gridPoint_interior_of_anchor_mem_diagonalCentralRegion
    problem (by omega : 5 ≤ 2 * k + 1) vertices hcomplete hanchor
  have hanchorGain := completeSimplexAnchor_gain_nonneg_of_pos problem (2 * k + 1)
    (by omega) vertices hcomplete who (hinterior anchor who).1
  have hcarrierGain := completeSimplexCoordinate_gain_neg_of_lt_one problem (2 * k + 1)
    (by omega) vertices hcomplete who (hinterior carrier who).2
  change 0 ≤ -entries who *
    (((vertices anchor who).val : ℝ) / (2 * k + 1 : ℕ) - 1 / 2) at hanchorGain
  change -entries who *
    (((vertices carrier who).val : ℝ) / (2 * k + 1 : ℕ) - 1 / 2) < 0 at hcarrierGain
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at hanchorGain hcarrierGain
  have hbaseAnchor := spernerSimplex_val_le_of_le hcomplete.1 (Fin.zero_le anchor) who
  have hbaseCarrier := spernerSimplex_val_le_of_le hcomplete.1 (Fin.zero_le carrier) who
  have hanchorBase := spernerSimplex_val_le_succ hcomplete.1 anchor 0 who
  have hcarrierBase := spernerSimplex_val_le_succ hcomplete.1 carrier 0 who
  rcases lt_trichotomy (entries who) 0 with hnegative | hzero | hpositive
  · have ha : 1 / 2 ≤ ((vertices anchor who).val : ℝ) / (2 * k + 1) := by
      nlinarith
    have hc : ((vertices carrier who).val : ℝ) / (2 * k + 1) ≤ 1 / 2 := by
      nlinarith
    have haNat := (half_le_oddGrid_iff k _).mp ha
    have hcNat := (oddGrid_le_half_iff k _).mp hc
    omega
  · simp only [hzero, neg_zero, zero_mul, lt_self_iff_false] at hcarrierGain
  · have ha : ((vertices anchor who).val : ℝ) / (2 * k + 1) ≤ 1 / 2 := by
      nlinarith
    have hc : 1 / 2 ≤ ((vertices carrier who).val : ℝ) / (2 * k + 1) := by
      nlinarith
    have haNat := (oddGrid_le_half_iff k _).mp ha
    have hcNat := (half_le_oddGrid_iff k _).mp hc
    omega

/-- Every locally selected tuple is the central chain of its actual chronological
coordinate permutation. This is confinement, not uniqueness of that permutation. -/
theorem eq_diagonalCentralChain_coordinateEquivalence_of_anchor_mem
    (entries : Fin n → ℝ) {k : ℕ} (hk : 2 ≤ k)
    (vertices : Fin (n + 1) → Fin n → Fin (2 * k + 1 + 1))
    (hcomplete : complete_simplex (boxComplementaritySpernerCube
      (centeredDiagonalProblem entries) (2 * k + 1) (by omega)) n vertices)
    (hanchor : boxComplementarityCompleteSimplexAnchorPoint
      (centeredDiagonalProblem entries) (2 * k + 1) (by omega)
      vertices hcomplete ∈ diagonalCentralRegion n) :
    vertices = diagonalCentralChain (KuhnSimplex.coordinateEquivalence hcomplete.1 rfl) k := by
  funext index who
  apply Fin.ext
  have hbase := initial_eq_center_of_anchor_mem entries hk vertices hcomplete hanchor who
  have hraise : (KuhnSimplex.coordinateEquivalence hcomplete.1 rfl).symm who =
      spernerChainRaiseIndex hcomplete.1 rfl who := by
    apply (KuhnSimplex.coordinateEquivalence hcomplete.1 rfl).injective
    rw [Equiv.apply_symm_apply]
    exact (spernerChainStep_raiseIndex hcomplete.1 rfl who).symm
  change (vertices index who).val = k +
    if ((KuhnSimplex.coordinateEquivalence hcomplete.1 rfl).symm who).val < index.val then 1 else 0
  rw [hraise]
  split_ifs with hlt
  · rw [spernerChain_val_eq_of_raiseIndex_lt hcomplete.1 rfl who hlt, hbase]
  · rw [spernerChain_val_eq_of_le_raiseIndex hcomplete.1 rfl who (Nat.le_of_not_lt hlt),
      hbase, add_zero]

theorem isGridViolation_diagonalCentralChain_step_iff_of_ne
    (entries : Fin n → ℝ) (permutation : Equiv.Perm (Fin n))
    {k : ℕ} (hk : 0 < k) (step who : Fin n) (hne : who ≠ permutation step) :
    (centeredDiagonalProblem entries).IsGridViolation (2 * k + 1)
        (diagonalCentralChain permutation k step.castSucc) who ↔
      (centeredDiagonalProblem entries).IsGridViolation (2 * k + 1)
        (diagonalCentralChain permutation k step.succ) who := by
  have hrank : (permutation.symm who).val ≠ step.val := by
    intro heq
    exact hne ((Equiv.symm_apply_eq permutation).mp (Fin.ext heq))
  rw [isGridViolation_diagonalCentralChain_iff entries permutation hk,
    isGridViolation_diagonalCentralChain_iff entries permutation hk]
  simp only [Fin.val_castSucc, Fin.val_succ]
  have hle : step.val ≤ (permutation.symm who).val ↔
      step.val + 1 ≤ (permutation.symm who).val := by omega
  have hlt : (permutation.symm who).val < step.val ↔
      (permutation.symm who).val < step.val + 1 := by omega
  rw [hle, hlt]

/-- A negative coordinate must carry its own label immediately before its raising step. -/
theorem finLabel_diagonalCentralChain_castSucc_of_negative
    (entries : Fin n → ℝ) (permutation : Equiv.Perm (Fin n))
    {k : ℕ} (hk : 0 < k)
    (hcomplete : complete_simplex (boxComplementaritySpernerCube
      (centeredDiagonalProblem entries) (2 * k + 1) (by omega)) n
      (diagonalCentralChain permutation k))
    (step : Fin n) (hnegative : entries (permutation step) < 0) :
    boxComplementarityFinLabel (centeredDiagonalProblem entries) (2 * k + 1)
      (diagonalCentralChain permutation k step.castSucc) = (permutation step).castSucc := by
  let problem := centeredDiagonalProblem entries
  let before := diagonalCentralChain permutation k step.castSucc
  let after := diagonalCentralChain permutation k step.succ
  have hbefore := boxComplementarityReducedLabel_properties problem (2 * k + 1) before
  have hafter := boxComplementarityReducedLabel_properties problem (2 * k + 1) after
  have hactive : problem.IsGridViolation (2 * k + 1) before (permutation step) := by
    exact (isGridViolation_diagonalCentralChain_iff entries permutation hk
      step.castSucc (permutation step)).mpr (by simp [hnegative])
  have hinactive : ¬problem.IsGridViolation (2 * k + 1) after (permutation step) := by
    rw [isGridViolation_diagonalCentralChain_iff entries permutation hk]
    simp [not_lt.mpr hnegative.le]
  have hle := (hbefore.2 (permutation step)).2 hactive
  apply Fin.ext
  change boxComplementarityReducedLabel problem (2 * k + 1) before = (permutation step).val
  by_contra hne
  let old : Fin n := ⟨boxComplementarityReducedLabel problem (2 * k + 1) before,
    lt_of_le_of_lt hle (permutation step).isLt⟩
  have holdNe : old ≠ permutation step := fun heq => hne (congrArg Fin.val heq)
  have holdActive := (hbefore.2 old).1 rfl
  have holdAfter := (isGridViolation_diagonalCentralChain_step_iff_of_ne
    entries permutation hk step old holdNe).mp holdActive
  have hafterLe := (hafter.2 old).2 holdAfter
  let new : Fin n := ⟨boxComplementarityReducedLabel problem (2 * k + 1) after,
    lt_of_le_of_lt hafterLe old.isLt⟩
  have hnewActive := (hafter.2 new).1 rfl
  have hnewNe : new ≠ permutation step := by
    intro heq
    exact hinactive (heq ▸ hnewActive)
  have hnewBefore := (isGridViolation_diagonalCentralChain_step_iff_of_ne
    entries permutation hk step new hnewNe).mpr hnewActive
  have hbeforeLe := (hbefore.2 new).2 hnewBefore
  have hequal : boxComplementarityFinLabel problem (2 * k + 1) before =
      boxComplementarityFinLabel problem (2 * k + 1) after :=
    Fin.ext (le_antisymm hbeforeLe hafterLe)
  have hinjective := (boxComplementarity_completeSimplex_iff_finLabel_injective
    problem (2 * k + 1) (by omega) _).mp hcomplete |>.2
  exact (Fin.castSucc_lt_succ (i := step)).ne (hinjective hequal)

/-- A positive coordinate must carry its own label immediately after its raising step. -/
theorem finLabel_diagonalCentralChain_succ_of_positive
    (entries : Fin n → ℝ) (permutation : Equiv.Perm (Fin n))
    {k : ℕ} (hk : 0 < k)
    (hcomplete : complete_simplex (boxComplementaritySpernerCube
      (centeredDiagonalProblem entries) (2 * k + 1) (by omega)) n
      (diagonalCentralChain permutation k))
    (step : Fin n) (hpositive : 0 < entries (permutation step)) :
    boxComplementarityFinLabel (centeredDiagonalProblem entries) (2 * k + 1)
      (diagonalCentralChain permutation k step.succ) = (permutation step).castSucc := by
  let problem := centeredDiagonalProblem entries
  let before := diagonalCentralChain permutation k step.castSucc
  let after := diagonalCentralChain permutation k step.succ
  have hbefore := boxComplementarityReducedLabel_properties problem (2 * k + 1) before
  have hafter := boxComplementarityReducedLabel_properties problem (2 * k + 1) after
  have hactive : problem.IsGridViolation (2 * k + 1) after (permutation step) := by
    exact (isGridViolation_diagonalCentralChain_iff entries permutation hk
      step.succ (permutation step)).mpr (by simp [hpositive])
  have hinactive : ¬problem.IsGridViolation (2 * k + 1) before (permutation step) := by
    rw [isGridViolation_diagonalCentralChain_iff entries permutation hk]
    simp [not_lt.mpr hpositive.le]
  have hle := (hafter.2 (permutation step)).2 hactive
  apply Fin.ext
  change boxComplementarityReducedLabel problem (2 * k + 1) after = (permutation step).val
  by_contra hne
  let new : Fin n := ⟨boxComplementarityReducedLabel problem (2 * k + 1) after,
    lt_of_le_of_lt hle (permutation step).isLt⟩
  have hnewNe : new ≠ permutation step := fun heq => hne (congrArg Fin.val heq)
  have hnewActive := (hafter.2 new).1 rfl
  have hnewBefore := (isGridViolation_diagonalCentralChain_step_iff_of_ne
    entries permutation hk step new hnewNe).mpr hnewActive
  have hbeforeLe := (hbefore.2 new).2 hnewBefore
  let old : Fin n := ⟨boxComplementarityReducedLabel problem (2 * k + 1) before,
    lt_of_le_of_lt hbeforeLe new.isLt⟩
  have holdActive := (hbefore.2 old).1 rfl
  have holdNe : old ≠ permutation step := by
    intro heq
    exact hinactive (heq ▸ holdActive)
  have holdAfter := (isGridViolation_diagonalCentralChain_step_iff_of_ne
    entries permutation hk step old holdNe).mp holdActive
  have hafterLe := (hafter.2 old).2 holdAfter
  have hequal : boxComplementarityFinLabel problem (2 * k + 1) before =
      boxComplementarityFinLabel problem (2 * k + 1) after :=
    Fin.ext (le_antisymm hbeforeLe hafterLe)
  have hinjective := (boxComplementarity_completeSimplex_iff_finLabel_injective
    problem (2 * k + 1) (by omega) _).mp hcomplete |>.2
  exact (Fin.castSucc_lt_succ (i := step)).ne (hinjective hequal)

/-- A permutation with the displayed two ordered blocks is the literal canonical order. -/
theorem eq_diagonalCoordinatePermutation_of_ordered_blocks
    (negative : Finset (Fin n)) (permutation : Equiv.Perm (Fin n))
    (hmem : ∀ step, permutation step ∈ negative ↔ step.val < negative.card)
    (hnegative : ∀ first second : Fin n, first.val < negative.card →
      second.val < negative.card → first ≤ second → permutation first ≤ permutation second)
    (hpositive : ∀ first second : Fin n, negative.card ≤ first.val →
      negative.card ≤ second.val → first ≤ second → permutation second ≤ permutation first) :
    permutation = diagonalCoordinatePermutation negative := by
  have hcard : negative.card + negativeᶜ.card = n := by
    have := Finset.card_compl negative
    have := Finset.card_le_univ negative
    simp only [Fintype.card_fin] at *
    omega
  let left : Fin negative.card → Fin n := fun index =>
    permutation ⟨index.val, by have := index.isLt; omega⟩
  have hleftMem (index : Fin negative.card) : left index ∈ negative :=
    (hmem _).mpr index.isLt
  have hleftMono : StrictMono left := by
    intro first second hlt
    apply lt_of_le_of_ne (hnegative _ _ first.isLt second.isLt hlt.le)
    intro heq
    have hval := congrArg Fin.val (permutation.injective heq)
    exact hlt.ne (Fin.ext hval)
  have hleft := Finset.orderEmbOfFin_unique rfl hleftMem hleftMono
  let rightIndex : Fin negativeᶜ.card → Fin n := fun index =>
    ⟨negative.card + (Fin.rev index).val, by have := (Fin.rev index).isLt; omega⟩
  let right : Fin negativeᶜ.card → Fin n := fun index => permutation (rightIndex index)
  have hrightMem (index : Fin negativeᶜ.card) : right index ∈ negativeᶜ := by
    rw [Finset.mem_compl, hmem]
    dsimp [rightIndex]
    omega
  have hrightMono : StrictMono right := by
    intro first second hlt
    have hrev : (Fin.rev second).val < (Fin.rev first).val := Fin.rev_strictAnti hlt
    have hle : rightIndex second ≤ rightIndex first := by
      change negative.card + (Fin.rev second).val ≤ negative.card + (Fin.rev first).val
      omega
    apply lt_of_le_of_ne (hpositive _ _ (by dsimp [rightIndex]; omega)
      (by dsimp [rightIndex]; omega) hle)
    intro heq
    have hval := congrArg Fin.val (permutation.injective heq)
    dsimp [rightIndex] at hval
    omega
  have hright := Finset.orderEmbOfFin_unique rfl hrightMem hrightMono
  apply Equiv.ext
  intro index
  change permutation index = diagonalCoordinateOrder negative index
  unfold diagonalCoordinateOrder
  split_ifs with hindex
  · exact congrFun hleft ⟨index.val, hindex⟩
  · let revIndex : Fin negativeᶜ.card := ⟨index.val - negative.card, by
      have := index.isLt
      omega⟩
    have hind : rightIndex (Fin.rev revIndex) = index := by
      apply Fin.ext
      simp only [rightIndex, Fin.rev_rev]
      dsimp [revIndex]
      omega
    have heq := congrFun hright (Fin.rev revIndex)
    change permutation (rightIndex (Fin.rev revIndex)) = _ at heq
    rw [hind] at heq
    exact heq

/-- The dimension-label anchor separates the negative and positive raising steps. -/
theorem diagonalCentralChain_negative_iff_before_anchor
    (entries : Fin n → ℝ) (hentries : ∀ who, entries who ≠ 0)
    (permutation : Equiv.Perm (Fin n)) {k : ℕ} (hk : 0 < k)
    (hcomplete : complete_simplex (boxComplementaritySpernerCube
      (centeredDiagonalProblem entries) (2 * k + 1) (by omega)) n
      (diagonalCentralChain permutation k)) (step : Fin n) :
    entries (permutation step) < 0 ↔ step.val <
      (boxComplementarityCompleteSimplexAnchorIndex (centeredDiagonalProblem entries)
        (2 * k + 1) (by omega) (diagonalCentralChain permutation k) hcomplete).val := by
  have hno := not_isGridViolation_completeSimplexAnchor (centeredDiagonalProblem entries)
    (2 * k + 1) (by omega) (diagonalCentralChain permutation k) hcomplete (permutation step)
  rw [isGridViolation_diagonalCentralChain_iff entries permutation hk] at hno
  simp only [Equiv.symm_apply_apply] at hno
  constructor
  · intro hnegative
    by_contra hnot
    exact hno (Or.inl ⟨hnegative, Nat.le_of_not_lt hnot⟩)
  · intro hlt
    have hnotpos : ¬0 < entries (permutation step) := fun hpos => hno (Or.inr ⟨hpos, hlt⟩)
    exact lt_of_le_of_ne (not_lt.mp hnotpos) (hentries _)

theorem diagonalCentralChain_anchor_val_eq_negative_card
    (entries : Fin n → ℝ) (hentries : ∀ who, entries who ≠ 0)
    (permutation : Equiv.Perm (Fin n)) {k : ℕ} (hk : 0 < k)
    (hcomplete : complete_simplex (boxComplementaritySpernerCube
      (centeredDiagonalProblem entries) (2 * k + 1) (by omega)) n
      (diagonalCentralChain permutation k)) :
    (boxComplementarityCompleteSimplexAnchorIndex (centeredDiagonalProblem entries)
      (2 * k + 1) (by omega) (diagonalCentralChain permutation k) hcomplete).val =
        (diagonalNegativeCoordinates entries).card := by
  let anchor := boxComplementarityCompleteSimplexAnchorIndex (centeredDiagonalProblem entries)
    (2 * k + 1) (by omega) (diagonalCentralChain permutation k) hcomplete
  let negative := diagonalNegativeCoordinates entries
  have hmem (step : Fin n) : permutation step ∈ negative ↔ step.val < anchor.val := by
    simpa only [negative, diagonalNegativeCoordinates, Finset.mem_filter,
      Finset.mem_univ, true_and] using
      diagonalCentralChain_negative_iff_before_anchor entries hentries permutation hk hcomplete step
  let embed : Fin anchor.val → negative := fun index =>
    ⟨permutation ⟨index.val, lt_of_lt_of_le index.isLt (Nat.le_of_lt_succ anchor.isLt)⟩,
      (hmem _).mpr index.isLt⟩
  have hinjective : Function.Injective embed := by
    intro first second heq
    have hval := congrArg Fin.val (permutation.injective (congrArg Subtype.val heq))
    exact Fin.ext hval
  have hsurjective : Function.Surjective embed := by
    intro who
    let step := permutation.symm who.val
    have hstep : step.val < anchor.val := (hmem step).mp (by
      simpa only [step, Equiv.apply_symm_apply] using who.property)
    refine ⟨⟨step.val, hstep⟩, ?_⟩
    apply Subtype.ext
    exact permutation.apply_symm_apply who.val
  have hcard := Fintype.card_congr (Equiv.ofBijective embed ⟨hinjective, hsurjective⟩)
  simpa only [Fintype.card_fin, Fintype.card_coe] using hcard

/-- Literal completeness forces the raising permutation to be the canonical signed order. -/
theorem diagonalCentralChain_permutation_eq_of_complete
    (entries : Fin n → ℝ) (hentries : ∀ who, entries who ≠ 0)
    (permutation : Equiv.Perm (Fin n)) {k : ℕ} (hk : 0 < k)
    (hcomplete : complete_simplex (boxComplementaritySpernerCube
      (centeredDiagonalProblem entries) (2 * k + 1) (by omega)) n
      (diagonalCentralChain permutation k)) :
    permutation = diagonalCoordinatePermutation (diagonalNegativeCoordinates entries) := by
  let negative := diagonalNegativeCoordinates entries
  have hnegative (step : Fin n) :
      entries (permutation step) < 0 ↔ step.val < negative.card := by
    rw [diagonalCentralChain_negative_iff_before_anchor entries hentries permutation hk hcomplete,
      diagonalCentralChain_anchor_val_eq_negative_card entries hentries permutation hk hcomplete]
  have hpositive (step : Fin n) :
      0 < entries (permutation step) ↔ negative.card ≤ step.val := by
    rw [← not_lt, ← hnegative]
    exact ⟨fun h => not_lt.mpr h.le,
      fun h => lt_of_le_of_ne (not_lt.mp h) (Ne.symm (hentries _))⟩
  apply eq_diagonalCoordinatePermutation_of_ordered_blocks negative permutation
  · intro step
    simpa only [negative, diagonalNegativeCoordinates, Finset.mem_filter,
      Finset.mem_univ, true_and] using hnegative step
  · intro first second hfirst hsecond hle
    have hlabel := finLabel_diagonalCentralChain_castSucc_of_negative
      entries permutation hk hcomplete first ((hnegative first).mpr hfirst)
    have hactive := (isGridViolation_diagonalCentralChain_iff entries permutation hk
      first.castSucc (permutation second)).mpr
      (Or.inl ⟨(hnegative second).mpr hsecond, by
        simpa only [Fin.val_castSucc, Equiv.symm_apply_apply] using
          (show first.val ≤ second.val from hle)⟩)
    have hbound := (boxComplementarityReducedLabel_properties
      (centeredDiagonalProblem entries) (2 * k + 1)
      (diagonalCentralChain permutation k first.castSucc)).2 (permutation second) |>.2 hactive
    have hvalue := congrArg Fin.val hlabel
    change boxComplementarityReducedLabel _ _ _ = (permutation first).val at hvalue
    rw [hvalue] at hbound
    exact hbound
  · intro first second hfirst hsecond hle
    have hlabel := finLabel_diagonalCentralChain_succ_of_positive
      entries permutation hk hcomplete second ((hpositive second).mpr hsecond)
    have hactive := (isGridViolation_diagonalCentralChain_iff entries permutation hk
      second.succ (permutation first)).mpr
      (Or.inr ⟨(hpositive first).mpr hfirst, by
        simp only [Fin.val_succ, Equiv.symm_apply_apply]
        exact Nat.lt_succ_of_le hle⟩)
    have hbound := (boxComplementarityReducedLabel_properties
      (centeredDiagonalProblem entries) (2 * k + 1)
      (diagonalCentralChain permutation k second.succ)).2 (permutation first) |>.2 hactive
    have hvalue := congrArg Fin.val hlabel
    change boxComplementarityReducedLabel _ _ _ = (permutation second).val at hvalue
    rw [hvalue] at hbound
    exact hbound

/-- Every actual locally selected complete tuple is the displayed canonical chain. -/
theorem eq_diagonalOrderedChain_of_anchor_mem
    (entries : Fin n → ℝ) (hentries : ∀ who, entries who ≠ 0)
    {k : ℕ} (hk : 2 ≤ k)
    (vertices : Fin (n + 1) → Fin n → Fin (2 * k + 1 + 1))
    (hcomplete : complete_simplex (boxComplementaritySpernerCube
      (centeredDiagonalProblem entries) (2 * k + 1) (by omega)) n vertices)
    (hanchor : boxComplementarityCompleteSimplexAnchorPoint
      (centeredDiagonalProblem entries) (2 * k + 1) (by omega)
      vertices hcomplete ∈ diagonalCentralRegion n) :
    vertices = diagonalCentralChain
      (diagonalCoordinatePermutation (diagonalNegativeCoordinates entries)) k := by
  let permutation := KuhnSimplex.coordinateEquivalence hcomplete.1 rfl
  have heq : vertices = diagonalCentralChain permutation k :=
    eq_diagonalCentralChain_coordinateEquivalence_of_anchor_mem
      entries hk vertices hcomplete hanchor
  have hcentral : complete_simplex (boxComplementaritySpernerCube
      (centeredDiagonalProblem entries) (2 * k + 1) (by omega)) n
      (diagonalCentralChain permutation k) := heq ▸ hcomplete
  rw [heq, diagonalCentralChain_permutation_eq_of_complete
    entries hentries permutation (by omega) hcentral]

/-- The actual anchor-selected finite set is the literal singleton
at every odd mesh at least five. -/
theorem localCompleteSimplices_centeredDiagonal_eq_singleton
    (entries : Fin n → ℝ) (hentries : ∀ who, entries who ≠ 0)
    {k : ℕ} (hk : 2 ≤ k) :
    boxComplementarityLocalCompleteSimplices (centeredDiagonalProblem entries)
      (2 * k + 1) (by omega) (diagonalCentralRegion n) =
        {diagonalCentralChain
          (diagonalCoordinatePermutation (diagonalNegativeCoordinates entries)) k} := by
  ext vertices
  constructor
  · intro hmem
    obtain ⟨hcomplete, hanchor⟩ :=
      (mem_boxComplementarityLocalCompleteSimplices_iff _ _ _ _ _).mp hmem
    exact Finset.mem_singleton.mpr
      (eq_diagonalOrderedChain_of_anchor_mem entries hentries hk vertices hcomplete hanchor)
  · intro hmem
    change vertices ∈ ({diagonalCentralChain
      (diagonalCoordinatePermutation (diagonalNegativeCoordinates entries)) k} :
        Finset (Fin (n + 1) → Fin n → Fin (2 * k + 1 + 1))) at hmem
    have heq := Finset.mem_singleton.mp hmem
    rw [heq]
    exact diagonalOrderedChain_mem_localCompleteSimplices entries hentries (by omega)

/-- Exact signed local count of an arbitrary nonsingular centered diagonal field. -/
theorem localSignedCount_centeredDiagonal_odd
    (entries : Fin n → ℝ) (hentries : ∀ who, entries who ≠ 0)
    {k : ℕ} (hk : 2 ≤ k) :
    boxComplementarityLocalSignedCount (centeredDiagonalProblem entries)
      (2 * k + 1) (by omega) (diagonalCentralRegion n) =
        (-1 : ℤ) ^ n * (-1 : ℤ) ^ (diagonalNegativeCoordinates entries).card := by
  rw [boxComplementarityLocalSignedCount,
    localCompleteSimplices_centeredDiagonal_eq_singleton entries hentries hk]
  change (∑ vertices ∈ ({diagonalCentralChain
      (diagonalCoordinatePermutation (diagonalNegativeCoordinates entries)) k} :
        Finset (Fin (n + 1) → Fin n → Fin (2 * k + 1 + 1))),
    boxComplementarityCompleteSimplexSignedWeight (centeredDiagonalProblem entries)
      (2 * k + 1) (by omega) vertices) = _
  rw [Finset.sum_singleton, signedWeight_diagonalOrderedChain entries hentries (by omega)]

theorem isOpen_diagonalCentralRegion : IsOpen (diagonalCentralRegion n) := by
  have hopen (who : Fin n) : IsOpen {point : UnitCube (Fin n) |
      1 / 4 < (point who : ℝ) ∧ (point who : ℝ) < 3 / 4} := by
    have hcontinuous : Continuous (fun point : UnitCube (Fin n) => (point who : ℝ)) :=
      (continuous_apply who).subtype_val
    exact (isOpen_lt continuous_const hcontinuous).inter
      (isOpen_lt hcontinuous continuous_const)
  simpa only [diagonalCentralRegion, setOf_forall] using isOpen_iInter_of_finite hopen

theorem coordinate_bounds_of_mem_closure_diagonalCentralRegion
    {point : UnitCube (Fin n)} (hpoint : point ∈ closure (diagonalCentralRegion n))
    (who : Fin n) : 1 / 4 ≤ (point who : ℝ) ∧ (point who : ℝ) ≤ 3 / 4 := by
  constructor
  · have hsubset : closure (diagonalCentralRegion n) ⊆
        {point : UnitCube (Fin n) | 1 / 4 ≤ (point who : ℝ)} :=
      closure_minimal (fun _ hmem => (hmem who).1.le)
        (isClosed_le continuous_const (continuous_apply who).subtype_val)
    exact hsubset hpoint
  · have hsubset : closure (diagonalCentralRegion n) ⊆
        {point : UnitCube (Fin n) | (point who : ℝ) ≤ 3 / 4} :=
      closure_minimal (fun _ hmem => (hmem who).2.le)
        (isClosed_le (continuous_apply who).subtype_val continuous_const)
    exact hsubset hpoint

/-- Isolation is derived from the actual interior zero equation, not supplied as data. -/
theorem isIsolating_centeredDiagonal_centralRegion
    (entries : Fin n → ℝ) (hentries : ∀ who, entries who ≠ 0) :
    (centeredDiagonalProblem entries).IsIsolating (diagonalCentralRegion n) := by
  refine ⟨isOpen_diagonalCentralRegion, Set.eq_empty_iff_forall_notMem.mpr ?_⟩
  rintro point ⟨hsolution, hfrontier⟩
  have hbounds := coordinate_bounds_of_mem_closure_diagonalCentralRegion
    (frontier_subset_closure hfrontier)
  have hinterior (who : Fin n) : 0 < (point who : ℝ) ∧ (point who : ℝ) < 1 := by
    have h := hbounds who
    constructor <;> linarith
  have hzero := (BoxComplementarityProblem.isSolution_iff_gain_eq_zero_of_coordinateInterior
    (centeredDiagonalProblem entries) point hinterior).mp hsolution
  have hmem : point ∈ diagonalCentralRegion n := by
    intro who
    have hcoord := congrFun hzero who
    change -entries who * ((point who : ℝ) - 1 / 2) = 0 at hcoord
    have hhalf := sub_eq_zero.mp ((mul_eq_zero.mp hcoord).resolve_left
      (neg_ne_zero.mpr (hentries who)))
    rw [hhalf]
    norm_num
  have hnot : point ∉ interior (diagonalCentralRegion n) := hfrontier.2
  rw [isOpen_diagonalCentralRegion.interior_eq] at hnot
  exact hnot hmem

/-- The normalized local degree is the sign parity of the actual nonzero diagonal entries. -/
theorem localDegree_centeredDiagonal_eq_neg_one_pow
    (entries : Fin n → ℝ) (hentries : ∀ who, entries who ≠ 0) :
    (centeredDiagonalProblem entries).localDegree (diagonalCentralRegion n)
      (isIsolating_centeredDiagonal_centralRegion entries hentries) =
        (-1 : ℤ) ^ (diagonalNegativeCoordinates entries).card := by
  obtain ⟨threshold, hcount⟩ :=
    (centeredDiagonalProblem entries).eventually_normalizedLocalSignedCount_eq_localDegree
      (diagonalCentralRegion n)
      (isIsolating_centeredDiagonal_centralRegion entries hentries)
  have h := hcount (2 * (threshold + 2) + 1) (by omega) (by omega)
  rw [localSignedCount_centeredDiagonal_odd entries hentries (by omega)] at h
  have hsquare : (-1 : ℤ) ^ n * (-1 : ℤ) ^ n = 1 := by
    rw [← mul_pow]
    simp
  rw [← mul_assoc, hsquare, one_mul] at h
  exact h.symm

/-- The same literal normalized index, written as the product of individual entry signs. -/
theorem localDegree_centeredDiagonal_eq_prod_sign
    (entries : Fin n → ℝ) (hentries : ∀ who, entries who ≠ 0) :
    (centeredDiagonalProblem entries).localDegree (diagonalCentralRegion n)
      (isIsolating_centeredDiagonal_centralRegion entries hentries) =
        ∏ who, if entries who < 0 then (-1 : ℤ) else 1 := by
  rw [localDegree_centeredDiagonal_eq_neg_one_pow entries hentries]
  simp only [diagonalNegativeCoordinates, Finset.prod_ite, Finset.prod_const,
    one_pow, mul_one]

/-- The actual centered diagonal local index is the integer sign of its determinant. -/
theorem localDegree_centeredDiagonal_eq_sign_det
    (entries : Fin n → ℝ) (hentries : ∀ who, entries who ≠ 0) :
    (centeredDiagonalProblem entries).localDegree (diagonalCentralRegion n)
      (isIsolating_centeredDiagonal_centralRegion entries hentries) =
        (SignType.sign (Matrix.diagonal entries).det : ℤ) := by
  rw [localDegree_centeredDiagonal_eq_prod_sign entries hentries, Matrix.det_diagonal]
  change _ = (SignType.castHom.comp (signHom : ℝ →*₀ SignType)) (∏ who, entries who)
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro who _
  rcases lt_or_gt_of_ne (hentries who) with hnegative | hpositive
  · simp [hnegative]
  · simp [hpositive, not_lt.mpr hpositive.le]

end Math
