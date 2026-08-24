import Mathlib.Combinatorics.Quiver.ConnectedComponent
import Mathlib.NumberTheory.FrobeniusNumber

/-!
# Period arithmetic for directed paths

This file isolates the arithmetic part of the cyclic decomposition of a directed graph.  Return
path lengths at a vertex form an additive submonoid of `ℕ`.  Consequently, every sufficiently
large multiple of their gcd is the length of a return path.  In a strongly connected quiver this
gcd is independent of the base vertex, and the lengths of two paths with the same endpoints are
congruent modulo the common gcd.

The results do not construct the finite cyclic classes.  They provide the exact eventual-length
and basepoint-independence lemmas needed by that construction.
-/

namespace Math

namespace DirectedPeriod

open Quiver

universe u v

variable {V : Type u} [Quiver.{v} V]

/-- The additive submonoid of lengths of directed return paths at `vertex`. -/
def returnLengthSubmonoid (vertex : V) : AddSubmonoid ℕ where
  carrier := {length | ∃ path : Path vertex vertex, path.length = length}
  zero_mem' := ⟨Path.nil, rfl⟩
  add_mem' := by
    rintro first second ⟨firstPath, rfl⟩ ⟨secondPath, rfl⟩
    exact ⟨firstPath.comp secondPath, Path.length_comp _ _⟩

theorem mem_returnLengthSubmonoid_iff {vertex : V} {length : ℕ} :
    length ∈ returnLengthSubmonoid vertex ↔
      ∃ path : Path vertex vertex, path.length = length :=
  Iff.rfl

/-- The period at a vertex is the gcd of all directed return-path lengths there. -/
noncomputable def returnPeriod (vertex : V) : ℕ :=
  Nat.setGcd (returnLengthSubmonoid vertex : Set ℕ)

theorem returnPeriod_dvd_path_length {vertex : V} (path : Path vertex vertex) :
    returnPeriod vertex ∣ path.length :=
  Nat.setGcd_dvd_of_mem ⟨path, rfl⟩

theorem returnPeriod_pos_of_exists_positive_path {vertex : V}
    (cycle : Path vertex vertex) (positive : 0 < cycle.length) :
    0 < returnPeriod vertex := by
  apply Nat.pos_of_ne_zero
  intro period_zero
  have hsubset : (returnLengthSubmonoid vertex : Set ℕ) ⊆ {0} :=
    Nat.setGcd_eq_zero_iff.mp (by simpa [returnPeriod] using period_zero)
  have hzero := hsubset ⟨cycle, rfl⟩
  simp only [Set.mem_singleton_iff] at hzero
  omega

/-- Every sufficiently large multiple of the return period is realized by a return path. -/
theorem eventually_exists_return_path (vertex : V) :
    ∃ threshold : ℕ, ∀ length ≥ threshold, returnPeriod vertex ∣ length →
      ∃ path : Path vertex vertex, path.length = length := by
  obtain ⟨threshold, hthreshold⟩ :=
    Nat.exists_mem_closure_of_ge (returnLengthSubmonoid vertex : Set ℕ)
  refine ⟨threshold, fun length hlength hdivides ↦ ?_⟩
  have hmem : length ∈ AddSubmonoid.closure (returnLengthSubmonoid vertex : Set ℕ) :=
    hthreshold length hlength hdivides
  rw [AddSubmonoid.closure_eq] at hmem
  exact hmem

private theorem returnPeriod_dvd_of_paths {first second : V}
    (forward : Path first second) (backward : Path second first) :
    returnPeriod first ∣ returnPeriod second := by
  apply Nat.dvd_setGcd_iff.mpr
  intro length hlength
  obtain ⟨cycle, rfl⟩ := hlength
  have hbase : returnPeriod first ∣ forward.length + backward.length := by
    simpa using returnPeriod_dvd_path_length (forward.comp backward)
  have hextended :
      returnPeriod first ∣ forward.length + cycle.length + backward.length := by
    simpa [Nat.add_assoc] using
      returnPeriod_dvd_path_length (forward.comp (cycle.comp backward))
  have hsum : returnPeriod first ∣
      (forward.length + backward.length) + cycle.length := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hextended
  exact (Nat.dvd_add_iff_right hbase).mpr hsum

/-- In a strongly connected quiver, the return period is independent of the base vertex. -/
theorem returnPeriod_eq_of_isStronglyConnected
    (connected : IsStronglyConnected V) (first second : V) :
    returnPeriod first = returnPeriod second := by
  let forward := (connected first second).some
  let backward := (connected second first).some
  exact Nat.dvd_antisymm
    (returnPeriod_dvd_of_paths forward backward)
    (returnPeriod_dvd_of_paths backward forward)

/-- Paths with the same endpoints have congruent lengths modulo the source return period. -/
theorem path_length_modEq_of_isStronglyConnected
    (connected : IsStronglyConnected V) {first second : V}
    (left right : Path first second) :
    left.length ≡ right.length [MOD returnPeriod first] := by
  let backward := (connected second first).some
  have hleft : returnPeriod first ∣ left.length + backward.length := by
    simpa using returnPeriod_dvd_path_length (left.comp backward)
  have hright : returnPeriod first ∣ right.length + backward.length := by
    simpa using returnPeriod_dvd_path_length (right.comp backward)
  exact Nat.ModEq.add_right_cancel' backward.length <|
    (Nat.modEq_zero_iff_dvd.mpr hleft).trans
      (Nat.modEq_zero_iff_dvd.mpr hright).symm

/-- A chosen path from `base` to `vertex`, used only to define the intrinsic phase label. -/
noncomputable def referencePath (connected : IsStronglyConnected V) (base vertex : V) :
    Path base vertex :=
  (connected base vertex).some

/-- The cyclic phase of a vertex, represented by a natural residue modulo the return period. -/
noncomputable def phaseIndex (connected : IsStronglyConnected V) (base vertex : V) : ℕ :=
  (referencePath connected base vertex).length % returnPeriod base

theorem phaseIndex_eq_iff_path_modEq_zero
    (connected : IsStronglyConnected V) (base : V) {first second : V}
    (path : Path first second) :
    phaseIndex connected base first = phaseIndex connected base second ↔
      path.length ≡ 0 [MOD returnPeriod base] := by
  let firstPath := referencePath connected base first
  let secondPath := referencePath connected base second
  have hpaths : firstPath.length + path.length ≡ secondPath.length
      [MOD returnPeriod base] := by
    simpa using path_length_modEq_of_isStronglyConnected connected
      (firstPath.comp path) secondPath
  change firstPath.length ≡ secondPath.length [MOD returnPeriod base] ↔ _
  constructor
  · intro hphase
    exact hphase.add_left_cancel (by simpa using hpaths)
  · intro hzero
    simpa using (hzero.add_left firstPath.length).symm.trans hpaths

/-- Every arrow advances the cyclic phase by one modulo the return period. -/
theorem phaseIndex_arrow
    (connected : IsStronglyConnected V) (base : V) {first second : V}
    (arrow : first ⟶ second) :
    phaseIndex connected base second =
      (phaseIndex connected base first + 1) % returnPeriod base := by
  have hpaths := path_length_modEq_of_isStronglyConnected connected
    ((referencePath connected base first).comp arrow.toPath)
    (referencePath connected base second)
  change _ % returnPeriod base =
    ((_ % returnPeriod base) + 1) % returnPeriod base
  exact hpaths.symm.trans (Nat.mod_add_mod _ _ _).symm

/-- Fixing one path from `first` to `second`, every sufficiently large compatible length is
realized by another path with those endpoints. -/
theorem eventually_exists_path_of_modEq {first second : V}
    (reference : Path first second) :
    ∃ threshold : ℕ, ∀ length ≥ threshold,
      length ≡ reference.length [MOD returnPeriod second] →
        ∃ path : Path first second, path.length = length := by
  obtain ⟨threshold, hthreshold⟩ := eventually_exists_return_path second
  refine ⟨threshold + reference.length, fun length hlength hcongruent ↦ ?_⟩
  have href : reference.length ≤ length := by omega
  have hdivides : returnPeriod second ∣ length - reference.length :=
    (Nat.modEq_iff_dvd' href).mp hcongruent.symm
  obtain ⟨cycle, hcycle⟩ := hthreshold (length - reference.length) (by omega) hdivides
  refine ⟨reference.comp cycle, ?_⟩
  rw [Path.length_comp, hcycle, Nat.add_sub_of_le href]

/-- Vertices in the same cyclic phase are joined by paths of every sufficiently large length
divisible by the common period. -/
theorem eventually_exists_path_of_phaseIndex_eq
    (connected : IsStronglyConnected V) (base : V) {first second : V}
    (samePhase : phaseIndex connected base first = phaseIndex connected base second) :
    ∃ threshold : ℕ, ∀ length ≥ threshold, returnPeriod base ∣ length →
      ∃ path : Path first second, path.length = length := by
  let reference := referencePath connected first second
  obtain ⟨threshold, hthreshold⟩ := eventually_exists_path_of_modEq reference
  refine ⟨threshold, fun length hlength hdivides ↦ hthreshold length hlength ?_⟩
  have hreference : reference.length ≡ 0 [MOD returnPeriod base] :=
    (phaseIndex_eq_iff_path_modEq_zero connected base reference).mp samePhase
  have hperiods : returnPeriod base = returnPeriod second :=
    returnPeriod_eq_of_isStronglyConnected connected base second
  rw [← hperiods]
  exact (Nat.modEq_zero_iff_dvd.mpr hdivides).trans hreference.symm

end DirectedPeriod

end Math
