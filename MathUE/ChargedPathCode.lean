import MathUE.ChargedPathBudget
import Mathlib.Algebra.BigOperators.Fin

/-! # Finite charged-path codes

Zero-charge stay slots pad finite paths without adding edges to the relation.
The initial vertex is retained even for the empty path. The finite-horizon
supremum and its relation to the full budget-to-go require no topology.
-/

noncomputable section

namespace Math.ChargedPathBudget.ChargedRelation

open Set

universe u v

variable {State : Type u} {Edge : Type v} (R : ChargedRelation State Edge)

@[simp] theorem Path.length_castSrc {s t w : State} (h : s = t) (path : R.Path s w) :
    (path.castSrc h).length = path.length := by
  subst h
  rfl

def compactSlotSource : State ⊕ Edge → State := Sum.elim id R.src

def compactSlotTarget : State ⊕ Edge → State := Sum.elim id R.tgt

def compactSlotCharge : State ⊕ Edge → ℝ := Sum.elim (fun _ ↦ 0) R.charge

/-- A finite vertex array and an equally ordered array of genuine edges or stays. -/
abbrev CompactPathData (horizon : ℕ) :=
  (Fin (horizon + 1) → State) × (Fin horizon → State ⊕ Edge)

def IsCompactPathData {horizon : ℕ} (data : CompactPathData (State := State)
    (Edge := Edge) horizon) : Prop :=
  ∀ index, R.compactSlotSource (data.2 index) = data.1 index.castSucc ∧
    R.compactSlotTarget (data.2 index) = data.1 index.succ

abbrev CompactPathCode (horizon : ℕ) :=
  {data : CompactPathData (State := State) (Edge := Edge) horizon // R.IsCompactPathData data}

namespace CompactPathCode

variable {R} {horizon : ℕ}

def source (code : R.CompactPathCode horizon) : State := code.1.1 0

def target (code : R.CompactPathCode horizon) : State := code.1.1 (Fin.last horizon)

def charge (code : R.CompactPathCode horizon) : ℝ :=
  ∑ index, R.compactSlotCharge (code.1.2 index)

def nil (state : State) (horizon : ℕ) : R.CompactPathCode horizon :=
  ⟨⟨fun _ ↦ state, fun _ ↦ Sum.inl state⟩, fun _ ↦ ⟨rfl, rfl⟩⟩

@[simp] theorem source_nil (state : State) (horizon : ℕ) :
    (nil (R := R) state horizon).source = state := rfl

@[simp] theorem target_nil (state : State) (horizon : ℕ) :
    (nil (R := R) state horizon).target = state := rfl

@[simp] theorem charge_nil (state : State) (horizon : ℕ) :
    (nil (R := R) state horizon).charge = 0 := by
  simp [charge, nil, compactSlotCharge]

def tail (code : R.CompactPathCode (horizon + 1)) : R.CompactPathCode horizon :=
  ⟨⟨fun index ↦ code.1.1 index.succ, fun index ↦ code.1.2 index.succ⟩,
    fun index ↦ by simpa using code.2 index.succ⟩

@[simp] theorem target_tail (code : R.CompactPathCode (horizon + 1)) :
    code.tail.target = code.target := rfl

theorem charge_eq_first_add_tail (code : R.CompactPathCode (horizon + 1)) :
    code.charge = R.compactSlotCharge (code.1.2 0) + code.tail.charge := by
  exact Fin.sum_univ_succ _

/-- Prepend either one genuine edge or one zero-charge stay. -/
def prepend (slot : State ⊕ Edge) (code : R.CompactPathCode horizon)
    (hmatch : R.compactSlotTarget slot = code.source) :
    R.CompactPathCode (horizon + 1) := by
  refine ⟨⟨Fin.cons (R.compactSlotSource slot) code.1.1,
    Fin.cons slot code.1.2⟩, ?_⟩
  intro index
  refine Fin.cases ?_ (fun index ↦ ?_) index
  · constructor
    · rfl
    · simpa [source] using hmatch
  · simpa using code.2 index

@[simp] theorem source_prepend (slot : State ⊕ Edge) (code : R.CompactPathCode horizon)
    (hmatch : R.compactSlotTarget slot = code.source) :
    (prepend slot code hmatch).source = R.compactSlotSource slot := rfl

@[simp] theorem target_prepend (slot : State ⊕ Edge) (code : R.CompactPathCode horizon)
    (hmatch : R.compactSlotTarget slot = code.source) :
    (prepend slot code hmatch).target = code.target := by
  simp [target, prepend, Fin.cons_last]

@[simp] theorem charge_prepend (slot : State ⊕ Edge) (code : R.CompactPathCode horizon)
    (hmatch : R.compactSlotTarget slot = code.source) :
    (prepend slot code hmatch).charge = R.compactSlotCharge slot + code.charge := by
  simp [charge, prepend, Fin.sum_univ_succ]

/-- Every padded code decodes to a literal relation path with the same endpoints and charge. -/
theorem exists_path (code : R.CompactPathCode horizon) :
    ∃ path : R.Path code.source code.target,
      path.length ≤ horizon ∧ path.chargeSum = code.charge := by
  induction horizon with
  | zero =>
      exact ⟨Path.nil code.source, Nat.le_refl 0, by simp [Path.chargeSum, charge]⟩
  | succ horizon ih =>
      obtain ⟨rest, hlength, hcharge⟩ := ih code.tail
      have hfirst := code.2 0
      have hsource : R.compactSlotSource (code.1.2 0) = code.source := hfirst.1
      have htarget : R.compactSlotTarget (code.1.2 0) = code.tail.source := hfirst.2
      cases hslot : code.1.2 0 with
      | inl state =>
          have hsame : code.tail.source = code.source := by
            rw [hslot] at hsource htarget
            exact htarget.symm.trans hsource
          refine ⟨rest.castSrc hsame, ?_, ?_⟩
          · simpa using hlength.trans (Nat.le_succ _)
          · simpa [charge_eq_first_add_tail, hslot, compactSlotCharge] using hcharge
      | inr edge =>
          have hsrc : R.src edge = code.source := by
            simpa [hslot, compactSlotSource] using hsource
          have htgt : code.tail.source = R.tgt edge := by
            simpa [hslot, compactSlotTarget] using htarget.symm
          let path := (Path.cons edge (rest.castSrc htgt)).castSrc hsrc
          refine ⟨path, ?_, ?_⟩
          · simpa [path] using Nat.succ_le_succ hlength
          · simpa [path, charge_eq_first_add_tail, hslot, compactSlotCharge] using
              congrArg (R.charge edge + ·) hcharge

def decode (code : R.CompactPathCode horizon) : R.Path code.source code.target :=
  code.exists_path.choose

theorem decode_length_le (code : R.CompactPathCode horizon) : code.decode.length ≤ horizon :=
  code.exists_path.choose_spec.1

theorem decode_charge (code : R.CompactPathCode horizon) : code.decode.chargeSum = code.charge :=
  code.exists_path.choose_spec.2

end CompactPathCode

/-- Every literal at-most-horizon path has a padded code, including nil at every state. -/
theorem exists_compactPathCode_of_path {source target : State}
    (path : R.Path source target) {horizon : ℕ} (hlen : path.length ≤ horizon) :
    ∃ code : R.CompactPathCode horizon,
      code.source = source ∧ code.target = target ∧ code.charge = path.chargeSum := by
  induction horizon generalizing source target with
  | zero =>
      cases path with
      | nil => exact ⟨.nil source 0, rfl, rfl, by simp⟩
      | cons edge rest => simp at hlen
  | succ horizon ih =>
      cases path with
      | nil => exact ⟨.nil source (horizon + 1), rfl, rfl, by simp⟩
      | cons edge rest =>
          obtain ⟨code, hsource, htarget, hcharge⟩ :=
            ih rest (by simpa using Nat.le_of_succ_le_succ hlen)
          refine ⟨code.prepend (.inr edge) hsource.symm, rfl, ?_, ?_⟩
          · simpa using htarget
          · simpa [compactSlotCharge] using congrArg (R.charge edge + ·) hcharge

/-- Charges of all literal paths with the displayed initial state and length at most the horizon. -/
def chargesFromWithin (state : State) (horizon : ℕ) : Set ℝ :=
  {charge | ∃ target, ∃ path : R.Path state target,
    path.length ≤ horizon ∧ path.chargeSum = charge}

theorem zero_mem_chargesFromWithin (state : State) (horizon : ℕ) :
    0 ∈ R.chargesFromWithin state horizon :=
  ⟨state, Path.nil state, Nat.zero_le _, rfl⟩

theorem chargesFromWithin_eq_codeCharges (state : State) (horizon : ℕ) :
    R.chargesFromWithin state horizon =
      CompactPathCode.charge '' {code : R.CompactPathCode horizon | code.source = state} := by
  ext charge
  constructor
  · rintro ⟨target, path, hlength, rfl⟩
    obtain ⟨code, hsource, _, hcharge⟩ := R.exists_compactPathCode_of_path path hlength
    exact ⟨code, hsource, hcharge⟩
  · rintro ⟨code, hsource, rfl⟩
    exact ⟨code.target, code.decode.castSrc hsource,
      by simpa using code.decode_length_le, by simpa using code.decode_charge⟩

/-- Finite-horizon capacity. Its topological hypotheses enter the theorems, not the definition. -/
def compactFiniteHorizonMaxCharge (state : State) (horizon : ℕ) : ℝ :=
  sSup (R.chargesFromWithin state horizon)

theorem chargesFromWithin_subset (state : State) (horizon : ℕ) :
    R.chargesFromWithin state horizon ⊆ R.chargesFrom state := by
  rintro charge ⟨target, path, _, hcharge⟩
  exact ⟨target, path, hcharge⟩

theorem compactFiniteHorizonMaxCharge_le_value (hbudget : R.HasFiniteBudget)
    (state : State) (horizon : ℕ) :
    R.compactFiniteHorizonMaxCharge state horizon ≤ R.value state := by
  apply csSup_le ⟨0, R.zero_mem_chargesFromWithin state horizon⟩
  rintro charge ⟨target, path, _, rfl⟩
  exact R.chargeSum_le_value hbudget path

/-- The all-length value is the countable supremum of exact at-most-horizon values.
This identity uses finite budget but requires no topology. -/
theorem value_eq_iSup_compactFiniteHorizonMaxCharge (hbudget : R.HasFiniteBudget)
    (state : State) : R.value state = ⨆ horizon, R.compactFiniteHorizonMaxCharge state horizon := by
  have hbounded : BddAbove (Set.range (R.compactFiniteHorizonMaxCharge state)) := by
    refine ⟨R.value state, ?_⟩
    rintro charge ⟨horizon, rfl⟩
    exact R.compactFiniteHorizonMaxCharge_le_value hbudget state horizon
  apply le_antisymm
  · apply csSup_le ⟨0, R.zero_mem_chargesFrom state⟩
    rintro charge ⟨target, path, rfl⟩
    have hfinite : BddAbove (R.chargesFromWithin state path.length) :=
      (R.bddAbove_chargesFrom hbudget state).mono
        (R.chargesFromWithin_subset state path.length)
    exact (le_csSup hfinite ⟨target, path, le_rfl, rfl⟩).trans
      (le_ciSup hbounded path.length)
  · exact ciSup_le fun horizon ↦
      R.compactFiniteHorizonMaxCharge_le_value hbudget state horizon

end Math.ChargedPathBudget.ChargedRelation
