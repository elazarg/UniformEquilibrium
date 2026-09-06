import MathUE.ChargedPathCode
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-! # Compact-edge finite-horizon capacity and measurable budget-to-go

Compact source fibers yield attained finite-horizon maxima and upper
semicontinuity. Under finite budget their countable supremum is the existing
Borel budget-to-go. No all-horizon semicontinuity is asserted.
-/

noncomputable section

namespace Math.ChargedPathBudget.ChargedRelation

open Set

universe u v

variable {State : Type u} {Edge : Type v} (R : ChargedRelation State Edge)

section Topology

variable [TopologicalSpace State] [TopologicalSpace Edge] [T2Space State]

theorem isClosed_compactPathData (hsrc : Continuous R.src) (htgt : Continuous R.tgt)
    (horizon : ℕ) : IsClosed {data : CompactPathData (State := State) (Edge := Edge) horizon |
      R.IsCompactPathData data} := by
  have hs : Continuous R.compactSlotSource := continuous_id.sumElim hsrc
  have ht : Continuous R.compactSlotTarget := continuous_id.sumElim htgt
  have heq : {data : CompactPathData (State := State) (Edge := Edge) horizon |
      R.IsCompactPathData data} =
      ⋂ index, {data | R.compactSlotSource (data.2 index) = data.1 index.castSucc} ∩
        {data | R.compactSlotTarget (data.2 index) = data.1 index.succ} := by
    ext data
    simp [IsCompactPathData]
  rw [heq]
  apply isClosed_iInter
  intro index
  exact (isClosed_eq (hs.comp ((continuous_apply index).comp continuous_snd))
    ((continuous_apply index.castSucc).comp continuous_fst)).inter
    (isClosed_eq (ht.comp ((continuous_apply index).comp continuous_snd))
      ((continuous_apply index.succ).comp continuous_fst))

omit [T2Space State] in
theorem continuous_compactPathCode_source (horizon : ℕ) :
    Continuous (CompactPathCode.source (R := R) (horizon := horizon)) :=
  (continuous_apply 0).comp (continuous_fst.comp continuous_subtype_val)

omit [T2Space State] in
theorem continuous_compactPathCode_target (horizon : ℕ) :
    Continuous (CompactPathCode.target (R := R) (horizon := horizon)) :=
  (continuous_apply (Fin.last horizon)).comp (continuous_fst.comp continuous_subtype_val)

omit [T2Space State] in
theorem continuous_compactPathCode_charge (hcharge : Continuous R.charge) (horizon : ℕ) :
    Continuous (CompactPathCode.charge (R := R) (horizon := horizon)) := by
  have hc : Continuous R.compactSlotCharge := continuous_const.sumElim hcharge
  apply continuous_finsetSum
  intro index _
  exact hc.comp ((continuous_apply index).comp (continuous_snd.comp continuous_subtype_val))

variable [CompactSpace State] [CompactSpace Edge]

theorem isCompact_compactPathCode_univ (hsrc : Continuous R.src) (htgt : Continuous R.tgt)
    (horizon : ℕ) : IsCompact (Set.univ : Set (R.CompactPathCode horizon)) := by
  have hclosed := R.isClosed_compactPathData hsrc htgt horizon
  letI : CompactSpace (R.CompactPathCode horizon) :=
    isCompact_iff_compactSpace.mp hclosed.isCompact
  exact isCompact_univ

/-- The fixed initial-state fiber is compact; nil makes it nonempty even at a dead end. -/
theorem isCompact_compactPathCode_sourceFiber (hsrc : Continuous R.src)
    (htgt : Continuous R.tgt) (state : State) (horizon : ℕ) :
    IsCompact {code : R.CompactPathCode horizon | code.source = state} := by
  exact (R.isCompact_compactPathCode_univ hsrc htgt horizon).of_isClosed_subset
    (isClosed_eq (R.continuous_compactPathCode_source horizon) continuous_const)
    (subset_univ _)

theorem exists_compactPathCode_maximum (hsrc : Continuous R.src) (htgt : Continuous R.tgt)
    (hcharge : Continuous R.charge) (state : State) (horizon : ℕ) :
    ∃ code : R.CompactPathCode horizon, code.source = state ∧
      ∀ other : R.CompactPathCode horizon, other.source = state → other.charge ≤ code.charge := by
  exact (R.isCompact_compactPathCode_sourceFiber hsrc htgt state horizon).exists_isMaxOn
    ⟨CompactPathCode.nil state horizon, rfl⟩
    (R.continuous_compactPathCode_charge hcharge horizon).continuousOn

theorem isCompact_chargesFromWithin (hsrc : Continuous R.src) (htgt : Continuous R.tgt)
    (hcharge : Continuous R.charge) (state : State) (horizon : ℕ) :
    IsCompact (R.chargesFromWithin state horizon) := by
  rw [R.chargesFromWithin_eq_codeCharges]
  exact (R.isCompact_compactPathCode_sourceFiber hsrc htgt state horizon).image
    (R.continuous_compactPathCode_charge hcharge horizon)

theorem chargeSum_le_compactFiniteHorizonMaxCharge
    (hsrc : Continuous R.src) (htgt : Continuous R.tgt) (hcharge : Continuous R.charge)
    {source target : State} (path : R.Path source target) {horizon : ℕ}
    (hlen : path.length ≤ horizon) :
    path.chargeSum ≤ R.compactFiniteHorizonMaxCharge source horizon :=
  le_csSup (R.isCompact_chargesFromWithin hsrc htgt hcharge source horizon).bddAbove
    ⟨target, path, hlen, rfl⟩

theorem compactFiniteHorizonMaxCharge_nonneg
    (hsrc : Continuous R.src) (htgt : Continuous R.tgt) (hcharge : Continuous R.charge)
    (state : State) (horizon : ℕ) : 0 ≤ R.compactFiniteHorizonMaxCharge state horizon :=
  le_csSup (R.isCompact_chargesFromWithin hsrc htgt hcharge state horizon).bddAbove
    (R.zero_mem_chargesFromWithin state horizon)

/-- A maximum is attained by a genuine relation path; padding contributes no edges. -/
theorem exists_path_eq_compactFiniteHorizonMaxCharge
    (hsrc : Continuous R.src) (htgt : Continuous R.tgt) (hcharge : Continuous R.charge)
    (state : State) (horizon : ℕ) :
    ∃ target, ∃ path : R.Path state target,
      path.length ≤ horizon ∧ path.chargeSum = R.compactFiniteHorizonMaxCharge state horizon :=
  (R.isCompact_chargesFromWithin hsrc htgt hcharge state horizon).sSup_mem
    ⟨0, R.zero_mem_chargesFromWithin state horizon⟩

/-- Compact-source projections of closed path superlevels give upper semicontinuity. -/
theorem upperSemicontinuous_compactFiniteHorizonMaxCharge
    (hsrc : Continuous R.src) (htgt : Continuous R.tgt) (hcharge : Continuous R.charge)
    (horizon : ℕ) : UpperSemicontinuous (fun state ↦
      R.compactFiniteHorizonMaxCharge state horizon) := by
  rw [upperSemicontinuous_iff_isClosed_preimage]
  intro threshold
  have hclosed : IsClosed {code : R.CompactPathCode horizon | threshold ≤ code.charge} :=
    isClosed_le continuous_const (R.continuous_compactPathCode_charge hcharge horizon)
  have hcompact : IsCompact {code : R.CompactPathCode horizon | threshold ≤ code.charge} :=
    (R.isCompact_compactPathCode_univ hsrc htgt horizon).of_isClosed_subset hclosed
      (subset_univ _)
  have heq : (fun state ↦ R.compactFiniteHorizonMaxCharge state horizon) ⁻¹' Ici threshold =
      CompactPathCode.source '' {code : R.CompactPathCode horizon | threshold ≤ code.charge} := by
    ext state
    constructor
    · intro hthreshold
      obtain ⟨target, path, hlength, hvalue⟩ :=
        R.exists_path_eq_compactFiniteHorizonMaxCharge hsrc htgt hcharge state horizon
      obtain ⟨code, hsource, _, hcode⟩ := R.exists_compactPathCode_of_path path hlength
      exact ⟨code, by simpa [hcode, hvalue] using hthreshold, hsource⟩
    · rintro ⟨code, hthreshold, rfl⟩
      have hbound := R.chargeSum_le_compactFiniteHorizonMaxCharge
        hsrc htgt hcharge code.decode code.decode_length_le
      exact hthreshold.trans (by simpa [code.decode_charge] using hbound)
  rw [heq]
  exact (hcompact.image (R.continuous_compactPathCode_source horizon)).isClosed

/-- The existing bounded budget-to-go is Borel. No all-horizon semicontinuity is asserted. -/
theorem measurable_value_of_compact_edges [MeasurableSpace State] [BorelSpace State]
    (hsrc : Continuous R.src) (htgt : Continuous R.tgt) (hcharge : Continuous R.charge)
    (hbudget : R.HasFiniteBudget) : Measurable R.value := by
  have heq : R.value = fun state ↦ ⨆ horizon, R.compactFiniteHorizonMaxCharge state horizon := by
    funext state
    exact R.value_eq_iSup_compactFiniteHorizonMaxCharge hbudget state
  rw [heq]
  exact Measurable.iSup fun horizon ↦
    (R.upperSemicontinuous_compactFiniteHorizonMaxCharge hsrc htgt hcharge horizon).measurable

end Topology

end Math.ChargedPathBudget.ChargedRelation
