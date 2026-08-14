import Mathlib

/-!
# Finite-group orbit gluing

This file formalizes the independent order-theoretic note
`ideas/FiniteGroupOrbitGluing.md`.

A group acting monotonically on a complete lattice acts by order
automorphisms.  The supremum of an orbit is invariant and glues any family of
upward-closed constraints containing the corresponding translated witnesses.
The infimum/downward-closed theorem is dual.
-/

noncomputable section

namespace Experiments.FiniteGroupOrbitGluing

variable {Gamma L : Type} [Group Gamma]
  [CompleteLattice L] [MulAction Gamma L]

/-- Upward-closed predicate, kept local to this independent experiment. -/
def IsUpwardClosed (set : Set L) : Prop :=
  ∀ ⦃x y⦄, x ∈ set → x ≤ y → y ∈ set

/-- Downward-closed predicate. -/
def IsDownwardClosed (set : Set L) : Prop :=
  ∀ ⦃x y⦄, x ∈ set → y ≤ x → y ∈ set

/-- A monotone group action is automatically an action by order
automorphisms: the inverse group element reflects order. -/
def smulOrderIso
    (smul_mono : ∀ g : Gamma, Monotone (fun x : L => g • x))
    (g : Gamma) : L ≃o L where
  toEquiv := MulAction.toPerm g
  map_rel_iff' := by
    intro x y
    constructor
    · intro h
      have pulledBack := smul_mono g⁻¹ h
      change g⁻¹ • (g • x) ≤ g⁻¹ • (g • y) at pulledBack
      simpa [← mul_smul] using pulledBack
    · intro h
      change g • x ≤ g • y
      exact smul_mono g h

/-- Supremum of the group orbit of `x`. -/
def orbitSup (x : L) : L :=
  ⨆ g : Gamma, g • x

/-- Infimum of the group orbit of `x`. -/
def orbitInf (x : L) : L :=
  ⨅ g : Gamma, g • x

theorem smul_le_orbitSup (x : L) (g : Gamma) :
    g • x ≤ orbitSup (Gamma := Gamma) x := by
  exact le_iSup (fun h : Gamma => h • x) g

theorem orbitInf_le_smul (x : L) (g : Gamma) :
    orbitInf (Gamma := Gamma) x ≤ g • x := by
  exact iInf_le (fun h : Gamma => h • x) g

/-- The orbit supremum is fixed by the whole group. -/
theorem smul_orbitSup_eq
    (smul_mono : ∀ g : Gamma, Monotone (fun x : L => g • x))
    (h : Gamma) (x : L) :
    h • orbitSup (Gamma := Gamma) x = orbitSup (Gamma := Gamma) x := by
  change (smulOrderIso smul_mono h) (⨆ g : Gamma, g • x) =
    ⨆ g : Gamma, g • x
  rw [(smulOrderIso smul_mono h).map_iSup]
  apply le_antisymm
  · refine iSup_le fun g => ?_
    change h • (g • x) ≤ ⨆ k : Gamma, k • x
    rw [← mul_smul]
    exact le_iSup (fun k : Gamma => k • x) (h * g)
  · refine iSup_le fun g => ?_
    change g • x ≤ ⨆ k : Gamma, h • (k • x)
    have translated :=
      le_iSup (fun k : Gamma => h • (k • x)) (h⁻¹ * g)
    simpa [← mul_smul] using translated

/-- The orbit infimum is fixed by the whole group. -/
theorem smul_orbitInf_eq
    (smul_mono : ∀ g : Gamma, Monotone (fun x : L => g • x))
    (h : Gamma) (x : L) :
    h • orbitInf (Gamma := Gamma) x = orbitInf (Gamma := Gamma) x := by
  change (smulOrderIso smul_mono h) (⨅ g : Gamma, g • x) =
    ⨅ g : Gamma, g • x
  rw [(smulOrderIso smul_mono h).map_iInf]
  apply le_antisymm
  · refine le_iInf fun g => ?_
    change (⨅ k : Gamma, h • (k • x)) ≤ g • x
    have translated :=
      iInf_le (fun k : Gamma => h • (k • x)) (h⁻¹ * g)
    simpa [← mul_smul] using translated
  · refine le_iInf fun g => ?_
    change (⨅ k : Gamma, k • x) ≤ h • (g • x)
    rw [← mul_smul]
    exact iInf_le (fun k : Gamma => k • x) (h * g)

/-- **Orbit-join gluing.**  Each constraint contains its own translated
witness; upward closure promotes that witness to the common orbit supremum. -/
theorem orbitSup_mem_all
    (family : Gamma → Set L) (x : L)
    (upward : ∀ g, IsUpwardClosed (family g))
    (translatedWitness : ∀ g, g • x ∈ family g) :
    ∀ g, orbitSup (Gamma := Gamma) x ∈ family g := by
  intro g
  exact upward g (translatedWitness g) (smul_le_orbitSup x g)

/-- The glued upward witness is simultaneously feasible and invariant. -/
theorem exists_invariant_common_of_orbitSup
    (family : Gamma → Set L) (x : L)
    (smul_mono : ∀ g : Gamma, Monotone (fun x : L => g • x))
    (upward : ∀ g, IsUpwardClosed (family g))
    (translatedWitness : ∀ g, g • x ∈ family g) :
    ∃ common : L,
      (∀ g, common ∈ family g) ∧
      ∀ h : Gamma, h • common = common := by
  exact ⟨orbitSup (Gamma := Gamma) x,
    orbitSup_mem_all family x upward translatedWitness,
    fun h => smul_orbitSup_eq smul_mono h x⟩

/-- **Orbit-meet gluing**, dual to `orbitSup_mem_all`. -/
theorem orbitInf_mem_all
    (family : Gamma → Set L) (x : L)
    (downward : ∀ g, IsDownwardClosed (family g))
    (translatedWitness : ∀ g, g • x ∈ family g) :
    ∀ g, orbitInf (Gamma := Gamma) x ∈ family g := by
  intro g
  exact downward g (translatedWitness g) (orbitInf_le_smul x g)

/-- The glued downward witness is simultaneously feasible and invariant. -/
theorem exists_invariant_common_of_orbitInf
    (family : Gamma → Set L) (x : L)
    (smul_mono : ∀ g : Gamma, Monotone (fun x : L => g • x))
    (downward : ∀ g, IsDownwardClosed (family g))
    (translatedWitness : ∀ g, g • x ∈ family g) :
    ∃ common : L,
      (∀ g, common ∈ family g) ∧
      ∀ h : Gamma, h • common = common := by
  exact ⟨orbitInf (Gamma := Gamma) x,
    orbitInf_mem_all family x downward translatedWitness,
    fun h => smul_orbitInf_eq smul_mono h x⟩

end Experiments.FiniteGroupOrbitGluing
