import Mathlib

/-!
# Coalition phase-offset gauge cocycle

This coalition-specific module formalizes the complete-overlap case of
the phase-alignment argument in
the coalition-splitting group-action construction.

An offset between every ordered pair of coalitions is globally alignable iff
it is an exact additive gauge cocycle (equivalently: it is antisymmetric and
has zero triangle sum).  The constructed coalition phases are unique up to
one global additive constant.  This differs from max-affine block holonomy.
-/

noncomputable section

namespace Research.CoalitionPhaseHolonomy

open scoped BigOperators

variable {ι A : Type} [AddCommGroup A]

/-- Pairwise phase offsets between coalition-split certificates. -/
abbrev PhaseOffset (ι A : Type) := Finset ι → Finset ι → A

/-- The pairwise offsets satisfy the additive cocycle law. -/
def IsCoherent (offset : PhaseOffset ι A) : Prop :=
  ∀ first middle last,
    offset first middle + offset middle last = offset first last

/-- The offsets arise by differencing one globally assigned phase per
coalition. -/
def IsExact (offset : PhaseOffset ι A) : Prop :=
  ∃ phase : Finset ι → A,
    ∀ first last, offset first last = phase last - phase first

/-- Every exact offset system is coherent. -/
theorem isCoherent_of_isExact {offset : PhaseOffset ι A}
    (exact : IsExact offset) :
    IsCoherent offset := by
  obtain ⟨phase, realization⟩ := exact
  intro first middle last
  rw [realization, realization, realization]
  abel

/-- **Integrating coalition phase offsets.**  For a nonempty coalition-index
type, every coherent pairwise offset is exact.  The phase of a coalition is
its offset from an arbitrary root coalition. -/
theorem isExact_of_isCoherent
    {offset : PhaseOffset ι A} (coherent : IsCoherent offset) :
    IsExact offset := by
  let root : Finset ι := ∅
  let phase : Finset ι → A := fun coalition => offset root coalition
  refine ⟨phase, fun first last => ?_⟩
  apply (eq_sub_iff_add_eq).2
  simpa only [phase, add_comm] using coherent root first last

/-- Pairwise coherence is exactly global phase alignability. -/
theorem isCoherent_iff_isExact
    (offset : PhaseOffset ι A) :
    IsCoherent offset ↔ IsExact offset := by
  exact ⟨isExact_of_isCoherent, isCoherent_of_isExact⟩

/-- Exact offsets reverse sign when an overlap edge is reversed. -/
theorem antisymmetric_of_isExact {offset : PhaseOffset ι A}
    (exact : IsExact offset) :
    ∀ first last, offset last first = -offset first last := by
  obtain ⟨phase, realization⟩ := exact
  intro first last
  rw [realization, realization]
  abel

/-- Exact offsets have zero sum around every triangle of coalition
splits. -/
theorem triangle_zero_of_isExact {offset : PhaseOffset ι A}
    (exact : IsExact offset) :
    ∀ first middle last,
      offset first middle + offset middle last + offset last first = 0 := by
  obtain ⟨phase, realization⟩ := exact
  intro first middle last
  rw [realization, realization, realization]
  abel

/-- Antisymmetry plus zero triangle holonomy implies the cocycle law. -/
theorem isCoherent_of_antisymmetric_of_triangle_zero
    {offset : PhaseOffset ι A}
    (antisymmetric :
      ∀ first last, offset last first = -offset first last)
    (triangleZero :
      ∀ first middle last,
        offset first middle + offset middle last + offset last first = 0) :
    IsCoherent offset := by
  intro first middle last
  have triangle := triangleZero first middle last
  rw [antisymmetric first last] at triangle
  exact (sub_eq_zero.mp (by
    change offset first middle + offset middle last - offset first last = 0
    simpa [sub_eq_add_neg] using triangle))

/-- **Zero-cocycle-class criterion.**  On the complete coalition-overlap graph,
global phase alignment is equivalent to reversed-edge antisymmetry plus zero
sum on every triangle. -/
theorem isExact_iff_antisymmetric_and_triangle_zero
    (offset : PhaseOffset ι A) :
    IsExact offset ↔
      (∀ first last, offset last first = -offset first last) ∧
      (∀ first middle last,
        offset first middle + offset middle last + offset last first = 0) := by
  constructor
  · intro exact
    exact ⟨antisymmetric_of_isExact exact, triangle_zero_of_isExact exact⟩
  · rintro ⟨antisymmetric, triangleZero⟩
    exact isExact_of_isCoherent
      (isCoherent_of_antisymmetric_of_triangle_zero
        antisymmetric triangleZero)

/-- Two global phase assignments realizing the same offsets differ by one
constant, evaluated here relative to an arbitrary root coalition. -/
theorem phase_assignments_differ_by_constant
    (offset : PhaseOffset ι A) (phase₁ phase₂ : Finset ι → A)
    (realizes₁ : ∀ first last,
      offset first last = phase₁ last - phase₁ first)
    (realizes₂ : ∀ first last,
      offset first last = phase₂ last - phase₂ first)
    (root coalition : Finset ι) :
    phase₂ coalition - phase₁ coalition =
      phase₂ root - phase₁ root := by
  have equalOffsets := (realizes₁ root coalition).symm.trans
    (realizes₂ root coalition)
  calc
    phase₂ coalition - phase₁ coalition =
        ((phase₂ coalition - phase₂ root) -
            (phase₁ coalition - phase₁ root)) +
          (phase₂ root - phase₁ root) := by abel
    _ = 0 + (phase₂ root - phase₁ root) := by
      rw [← equalOffsets]
      simp
    _ = phase₂ root - phase₁ root := zero_add _

/-! ## Diagonal player--phase action laws -/

variable {Gamma Player Phase : Type}
  [Group Gamma] [MulAction Gamma Player] [AddCommGroup Phase]

/-- Player relabeling accompanied by a group-dependent phase shift. -/
def diagonalPlayerPhase
    (shift : Gamma → Phase) (g : Gamma) (pair : Player × Phase) :
    Player × Phase :=
  (g • pair.1, pair.2 + shift g)

theorem diagonalPlayerPhase_one
    (shift : Gamma → Phase) (shift_one : shift 1 = 0)
    (pair : Player × Phase) :
    diagonalPlayerPhase shift 1 pair = pair := by
  simp [diagonalPlayerPhase, shift_one]

/-- The diagonal operation is a group action exactly when phase shifts add
under multiplication. -/
theorem diagonalPlayerPhase_mul
    (shift : Gamma → Phase)
    (shift_mul : ∀ g h, shift (g * h) = shift g + shift h)
    (g h : Gamma) (pair : Player × Phase) :
    diagonalPlayerPhase shift (g * h) pair =
      diagonalPlayerPhase shift g (diagonalPlayerPhase shift h pair) := by
  ext
  · simp [diagonalPlayerPhase, mul_smul]
  · simp [diagonalPlayerPhase, shift_mul]
    abel

end Research.CoalitionPhaseHolonomy
