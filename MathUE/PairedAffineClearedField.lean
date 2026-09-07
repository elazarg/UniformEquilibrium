import MathUE.PairedAffineIntervalEstimates
import MathUE.Topology.RectangularPoincareMiranda
import Mathlib.Topology.Algebra.MvPolynomial

/-! # Polynomial simultaneous selection for ordered paired affine maps -/

noncomputable section

namespace Math.PairedAffine

variable {ι : Type*}

/-- A quiet-pair map with its two hazards read from named coordinates. -/
structure IndexedRow (ι : Type*) where
  first : ι
  second : ι
  left : ℝ
  right : ℝ
  tie : ℝ

def IndexedRow.specialize (row : IndexedRow ι) (q : ι → ℝ) : Row where
  left := row.left
  right := row.right
  tie := row.tie
  firstHazard := q row.first
  secondHazard := q row.second

def IndexedRow.polynomial (row : IndexedRow ι) (value : MvPolynomial ι ℝ) :
    MvPolynomial ι ℝ :=
  MvPolynomial.X row.first * (1 - MvPolynomial.X row.second) * MvPolynomial.C row.left +
    (1 - MvPolynomial.X row.first) * MvPolynomial.X row.second * MvPolynomial.C row.right +
    MvPolynomial.X row.first * MvPolynomial.X row.second * MvPolynomial.C row.tie +
    (1 - MvPolynomial.X row.first) * (1 - MvPolynomial.X row.second) * value

def composePolynomial (rows : List (IndexedRow ι)) (value : MvPolynomial ι ℝ) :
    MvPolynomial ι ℝ :=
  rows.foldr IndexedRow.polynomial value

def activePolynomial (singleton joint : ℝ) (coordinate : ι) : MvPolynomial ι ℝ :=
  MvPolynomial.C singleton + MvPolynomial.X coordinate *
    (MvPolynomial.C joint - MvPolynomial.C singleton)

/-- Defined polynomially on the whole coordinate space, without totalized division. -/
def clearedPolynomial (singleton partner joint : ℝ) (coordinate : ι)
    (rows : List (IndexedRow ι)) : MvPolynomial ι ℝ :=
  (1 - MvPolynomial.X coordinate) * MvPolynomial.C singleton +
    MvPolynomial.X coordinate * (MvPolynomial.C joint - MvPolynomial.C partner) -
    (1 - MvPolynomial.X coordinate) *
      composePolynomial rows (activePolynomial singleton joint coordinate)

theorem IndexedRow.eval_polynomial (row : IndexedRow ι) (value : MvPolynomial ι ℝ)
    (q : ι → ℝ) :
    MvPolynomial.eval q (row.polynomial value) = (row.specialize q).apply
      (MvPolynomial.eval q value) := by
  simp [IndexedRow.polynomial, IndexedRow.specialize, Row.apply, bellman, contribution]

theorem eval_composePolynomial (rows : List (IndexedRow ι)) (value : MvPolynomial ι ℝ)
    (q : ι → ℝ) :
    MvPolynomial.eval q (composePolynomial rows value) =
      compose (rows.map fun row => row.specialize q) (MvPolynomial.eval q value) := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
      simpa only [composePolynomial, List.foldr_cons, IndexedRow.eval_polynomial,
        List.map_cons, compose] using congrArg (fun x => (row.specialize q).apply x) ih

theorem eval_activePolynomial (singleton joint : ℝ) (coordinate : ι) (q : ι → ℝ) :
    MvPolynomial.eval q (activePolynomial singleton joint coordinate) =
      activeValue singleton joint (q coordinate) := by
  simp [activePolynomial, activeValue]

theorem eval_clearedPolynomial (singleton partner joint : ℝ) (coordinate : ι)
    (rows : List (IndexedRow ι)) (q : ι → ℝ) (hq : q coordinate ≠ 1) :
    MvPolynomial.eval q (clearedPolynomial singleton partner joint coordinate rows) =
      (1 - q coordinate) *
        (postValue singleton partner joint (q coordinate) -
          compose (rows.map fun row => row.specialize q)
            (activeValue singleton joint (q coordinate))) := by
  simp only [clearedPolynomial, map_sub, map_add, map_mul, MvPolynomial.eval_X,
    map_one, MvPolynomial.eval_C, eval_composePolynomial, eval_activePolynomial]
  unfold postValue
  field_simp

/-- The divided player-indexed gap, used only where partner hazards are below one. -/
def playerGap (partner : ι → ι) (singleton partnerReward joint : ι → ℝ)
    (rows : ι → List (IndexedRow ι)) (q : ι → ℝ) (player : ι) : ℝ :=
  postValue (singleton player) (partnerReward player) (joint player) (q (partner player)) -
    compose ((rows player).map fun row => row.specialize q)
      (activeValue (singleton player) (joint player) (q (partner player)))

/-- Coordinate j clears the gap belonging to j's partner. -/
def clearedField (partner : ι → ι) (singleton partnerReward joint : ι → ℝ)
    (rows : ι → List (IndexedRow ι)) (q : ι → ℝ) (coordinate : ι) : ℝ :=
  MvPolynomial.eval q (clearedPolynomial (singleton (partner coordinate))
    (partnerReward (partner coordinate)) (joint (partner coordinate)) coordinate
    (rows (partner coordinate)))

theorem continuous_clearedField (partner : ι → ι) (singleton partnerReward joint : ι → ℝ)
    (rows : ι → List (IndexedRow ι)) :
    Continuous (clearedField partner singleton partnerReward joint rows) := by
  apply continuous_pi
  intro coordinate
  exact MvPolynomial.continuous_eval _

theorem clearedField_eq_mul_playerGap (partner : ι → ι)
    (hinvolution : Function.Involutive partner) (singleton partnerReward joint : ι → ℝ)
    (rows : ι → List (IndexedRow ι)) (q : ι → ℝ) (coordinate : ι)
    (hq : q coordinate ≠ 1) :
    clearedField partner singleton partnerReward joint rows q coordinate =
      (1 - q coordinate) * playerGap partner singleton partnerReward joint rows q
        (partner coordinate) := by
  unfold clearedField
  rw [eval_clearedPolynomial _ _ _ _ _ _ hq]
  simp only [playerGap, hinvolution coordinate]

theorem specialized_rows_valid {rows : List (IndexedRow ι)} {q : ι → ℝ}
    (hrows : ∀ row ∈ rows, PassiveBounds row.left row.right row.tie)
    (hq : ∀ player, q player ∈ Set.Icc (1 / 100 : ℝ) (1 / 2)) :
    ∀ row ∈ rows.map (fun row => row.specialize q), row.Valid := by
  intro row hrow
  obtain ⟨original, horiginal, rfl⟩ := List.mem_map.mp hrow
  exact ⟨hrows original horiginal, hq original.first, hq original.second⟩

theorem clearedField_lower_face (partner : ι → ι)
    (singleton partnerReward joint : ι → ℝ) (rows : ι → List (IndexedRow ι))
    (hown : ∀ player, OwnBounds (singleton player) (partnerReward player) (joint player))
    (hrows : ∀ player row, row ∈ rows player → PassiveBounds row.left row.right row.tie)
    (hne : ∀ player, rows player ≠ [])
    (q : ι → ℝ) (hq : ∀ player, q player ∈ Set.Icc (1 / 100 : ℝ) (1 / 2))
    (coordinate : ι) (hface : q coordinate = 1 / 100) :
    clearedField partner singleton partnerReward joint rows q coordinate < 0 := by
  unfold clearedField
  rw [eval_clearedPolynomial _ _ _ _ _ _ (by rw [hface]; norm_num), hface]
  have hvalid := specialized_rows_valid (hrows (partner coordinate)) hq
  have hnonempty : ((rows (partner coordinate)).map fun row => row.specialize q) ≠ [] := by
    simpa using hne (partner coordinate)
  have hgap := compose_lower_face_gap_le (hown (partner coordinate)) hvalid hnonempty
  nlinarith

theorem clearedField_upper_face (partner : ι → ι)
    (singleton partnerReward joint : ι → ℝ) (rows : ι → List (IndexedRow ι))
    (hown : ∀ player, OwnBounds (singleton player) (partnerReward player) (joint player))
    (hrows : ∀ player row, row ∈ rows player → PassiveBounds row.left row.right row.tie)
    (q : ι → ℝ) (hq : ∀ player, q player ∈ Set.Icc (1 / 100 : ℝ) (1 / 2))
    (coordinate : ι) (hface : q coordinate = 1 / 2) :
    0 < clearedField partner singleton partnerReward joint rows q coordinate := by
  unfold clearedField
  rw [eval_clearedPolynomial _ _ _ _ _ _ (by rw [hface]; norm_num), hface]
  have hvalid := specialized_rows_valid (hrows (partner coordinate)) hq
  have hgap := compose_upper_face_gap_ge (hown (partner coordinate)) hvalid
  nlinarith

/-- One simultaneous interior choice for all player equations, from literal ranges. -/
theorem exists_interior_hazards_all_playerGap_zero [Fintype ι]
    (partner : ι → ι) (hinvolution : Function.Involutive partner)
    (singleton partnerReward joint : ι → ℝ) (rows : ι → List (IndexedRow ι))
    (hown : ∀ player, OwnBounds (singleton player) (partnerReward player) (joint player))
    (hrows : ∀ player row, row ∈ rows player → PassiveBounds row.left row.right row.tie)
    (hne : ∀ player, rows player ≠ []) :
    ∃ q : ι → ℝ, (∀ player, q player ∈ Set.Ioo (1 / 100 : ℝ) (1 / 2)) ∧
      ∀ player, playerGap partner singleton partnerReward joint rows q player = 0 := by
  obtain ⟨q, hq, hinterior, hzero⟩ :=
    Math.Topology.exists_rectangular_zero_of_strict_face_signs
      (fun _ : ι => (1 / 100 : ℝ)) (fun _ => (1 / 2 : ℝ))
      (clearedField partner singleton partnerReward joint rows)
      (by intro coordinate; norm_num)
      (continuous_clearedField partner singleton partnerReward joint rows)
      (fun q hq coordinate hface => clearedField_lower_face partner singleton partnerReward
        joint rows hown hrows hne q (fun player => ⟨hq.1 player, hq.2 player⟩) coordinate hface)
      (fun q hq coordinate hface => clearedField_upper_face partner singleton partnerReward
        joint rows hown hrows q (fun player => ⟨hq.1 player, hq.2 player⟩) coordinate hface)
  refine ⟨q, hinterior, fun player => ?_⟩
  have hneOne : q (partner player) ≠ 1 := by
    have hupper := (hinterior (partner player)).2
    linarith
  have hgap := hzero (partner player)
  rw [clearedField_eq_mul_playerGap partner hinvolution singleton partnerReward joint rows
    q (partner player) hneOne, hinvolution player] at hgap
  exact (mul_eq_zero.mp hgap).resolve_left (sub_ne_zero.mpr hneOne.symm)

end Math.PairedAffine
