import FixedPointTheorems.brouwer
import MathUE.Topology.CompactComponentSeparation
import Mathlib.Analysis.Convex.Basic
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.UnitInterval
import Mathlib.Topology.UrysohnsLemma

/-!
# Connected fixed-point continuation over an interval

For a continuous family of self-maps of a nonempty compact convex set in a finite-dimensional
real normed space, an actual compact connected subset of the fixed-point graph meets both
endpoint fibers. The proof is the standard component separation, Urysohn, and Brouwer argument.
It requires neither isolated fixed points, regularity, nonempty interior, nor a supplied
spanning component.
-/

namespace Math

open Set

private theorem exists_fixedPoint_unitInterval_prod
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {K : Set E} (hconvex : Convex ℝ K) (hcompact : IsCompact K)
    (hne : K.Nonempty) (T : C(unitInterval × K, unitInterval × K)) :
    ∃ p, T p = p := by
  let e := Homeomorph.Set.prod (Icc (0 : ℝ) 1) K
  let lifted : C(↥(Icc (0 : ℝ) 1 ×ˢ K), ↥(Icc (0 : ℝ) 1 ×ˢ K)) :=
    (toContinuousMap e.symm).comp (T.comp (toContinuousMap e))
  have hproduct : (Icc (0 : ℝ) 1 ×ˢ K).Nonempty := by
    obtain ⟨x, hx⟩ := hne
    exact ⟨(0, x), ⟨⟨le_rfl, zero_le_one⟩, hx⟩⟩
  obtain ⟨p, hp⟩ := brouwer_fixed_point _
    ((convex_Icc (𝕜 := ℝ) (0 : ℝ) 1).prod hconvex)
    (isCompact_Icc.prod hcompact) hproduct lifted
  refine ⟨e p, ?_⟩
  have heq := congrArg e hp
  change e (e.symm (T (e p))) = e p at heq
  simpa only [e.apply_symm_apply] using heq

/-- Browder's connected fixed-point continuation theorem on the unit interval.

The output is a compact connected set of actual parameter/fixed-point pairs and explicitly
contains a pair over each endpoint. The ambient space may have dimension zero, and the compact
convex set may have empty interior. -/
theorem exists_compact_connected_fixedPoint_continuation
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {K : Set E} (hconvex : Convex ℝ K) (hcompact : IsCompact K)
    (hne : K.Nonempty) (f : C(unitInterval × K, K)) :
    ∃ C : Set (unitInterval × K),
      IsCompact C ∧ IsConnected C ∧
      (∀ p ∈ C, f p = p.2) ∧
      (∃ x : K, (0, x) ∈ C) ∧ (∃ x : K, (1, x) ∈ C) := by
  classical
  let : CompactSpace K := isCompact_iff_compactSpace.mp hcompact
  let P := unitInterval × K
  let Z : Set P := {p | f p = p.2}
  have hZ : IsClosed Z := isClosed_eq f.continuous continuous_snd
  let : CompactSpace Z := isCompact_iff_compactSpace.mp hZ.isCompact
  let A : Set Z := {z | z.val.1 = 0}
  let B : Set Z := {z | z.val.1 = 1}
  have hA : IsClosed A :=
    isClosed_eq (continuous_fst.comp continuous_subtype_val) continuous_const
  have hB : IsClosed B :=
    isClosed_eq (continuous_fst.comp continuous_subtype_val) continuous_const
  have hspanning : ∃ a : Z, a ∈ A ∧ ∃ b : Z, b ∈ B ∧ b ∈ connectedComponent a := by
    by_contra hnone
    obtain ⟨U, hU, hAU, hUB⟩ :=
      exists_isClopen_separator_of_no_common_component hA hB
        (fun a ha b hb hab => hnone ⟨a, ha, b, hb, hab⟩)
    let Uzero : Set P := Subtype.val '' Uᶜ
    let Uone : Set P := Subtype.val '' U
    have hzero : IsClosed Uzero :=
      (hU.compl.isClosed.isCompact.image continuous_subtype_val).isClosed
    have hone : IsClosed Uone :=
      (hU.isClosed.isCompact.image continuous_subtype_val).isClosed
    have hdisjoint : Disjoint Uzero Uone := by
      apply Set.disjoint_left.mpr
      rintro _ ⟨z, hz, rfl⟩ ⟨w, hw, hwz⟩
      have hweq : w = z := Subtype.ext hwz
      subst w
      exact hz hw
    obtain ⟨g, hgzero, hgone, hgrange⟩ :=
      exists_continuous_zero_one_of_isClosed hzero hone hdisjoint
    let clock : C(P, unitInterval) :=
      ⟨fun p => ⟨g p, hgrange p⟩, g.continuous.subtype_mk _⟩
    let T : C(P, P) := ⟨fun p => (clock p, f p),
      clock.continuous.prodMk f.continuous⟩
    obtain ⟨p, hp⟩ := exists_fixedPoint_unitInterval_prod hconvex hcompact hne T
    have hfixed : f p = p.2 := congrArg Prod.snd hp
    let z : Z := ⟨p, hfixed⟩
    have hclock : g p = (p.1 : ℝ) :=
      congrArg (fun q : P => (q.1 : ℝ)) hp
    by_cases hz : z ∈ U
    · have hg : g p = 1 := hgone ⟨z, hz, rfl⟩
      have hzB : z ∈ B := Subtype.ext (hclock.symm.trans hg)
      exact Set.disjoint_left.mp hUB hz hzB
    · have hg : g p = 0 := hgzero ⟨z, hz, rfl⟩
      have hzA : z ∈ A := Subtype.ext (hclock.symm.trans hg)
      exact hz (hAU hzA)
  obtain ⟨a, ha, b, hb, hab⟩ := hspanning
  refine ⟨Subtype.val '' connectedComponent a,
    isClosed_connectedComponent.isCompact.image continuous_subtype_val,
    isConnected_connectedComponent.image _ continuous_subtype_val.continuousOn, ?_, ?_, ?_⟩
  · rintro p ⟨z, _, rfl⟩
    exact z.property
  · refine ⟨a.val.2, a, mem_connectedComponent, ?_⟩
    exact Prod.ext ha rfl
  · refine ⟨b.val.2, b, hab, ?_⟩
    exact Prod.ext hb rfl

end Math
