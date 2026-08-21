/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.Semicontinuity.Hemicontinuity
import Mathlib.Analysis.Calculus.TangentCone.Seq
import UniformEquilibrium.Quitting.AbsorptionPath.PrincipalQBoundaryDirection

/-!
# The closed support correspondence for principal-Q viability

The published viability proof puts both complementarity and the inward
residual inequalities into its control correspondence.  The latter makes its
graph nonclosed.  Viability only needs the correspondence itself to retain
complementarity; the inward residual inequalities belong in the separate
tangency witness.

Accordingly, this module uses the simplex controls `z` satisfying
`zᵢ qᵢ = 0`.  Its graph is closed and its values are compact.  At a
nonnegative boundary point, a principal-Q direction belongs to this
correspondence and separately supplies the inward tangent condition.
-/

noncomputable section

namespace GameTheory.QuittingLCPClassification

open Filter Finset Math.LinearProgramming Set
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Simplex controls supported on the zero coordinates of `q`, stated in the
closed complementary-product form `zᵢ qᵢ = 0`. -/
def principalQSupportControls (q : ι → ℝ) : Set (stdSimplex ℝ ι) :=
  {z | ∀ i, z i * q i = 0}

/-- The nonnegative orthant boundary as a subset of the ambient vector space. -/
def nonnegativeBoundary : Set (ι → ℝ) :=
  {q | IsNonnegativeBoundary q}

omit [DecidableEq ι] in
/-- The complementary-product form says exactly that every nonzero control
coordinate is supported on a zero coordinate of the state. -/
theorem mem_principalQSupportControls_iff
    {q : ι → ℝ} {z : stdSimplex ℝ ι} :
    z ∈ principalQSupportControls q ↔
      ∀ i, z i ≠ 0 → q i = 0 := by
  constructor
  · intro hcomplementary i hi
    exact (mul_eq_zero.mp (hcomplementary i)).resolve_left hi
  · intro hsupported i
    by_cases hi : z i = 0
    · simp [hi]
    · simp [hsupported i hi]

omit [DecidableEq ι] in
/-- The graph of the support-only correspondence is closed. -/
theorem isClosed_graph_principalQSupportControls :
    IsClosed {point : (ι → ℝ) × stdSimplex ℝ ι |
      point.2 ∈ principalQSupportControls point.1} := by
  have hcoordinate (i : ι) : IsClosed
      {point : (ι → ℝ) × stdSimplex ℝ ι |
      point.2 i * point.1 i = 0} := by
    exact isClosed_eq
      (((continuous_apply i).comp continuous_subtype_val).comp continuous_snd |>.mul
        ((continuous_apply i).comp continuous_fst)) continuous_const
  rw [show {point : (ι → ℝ) × stdSimplex ℝ ι |
      point.2 ∈ principalQSupportControls point.1} =
        ⋂ i, {point | point.2 i * point.1 i = 0} by
    ext point
    simp [principalQSupportControls]]
  exact isClosed_iInter hcoordinate

omit [DecidableEq ι] in
/-- Every value of the support-only correspondence is compact. -/
theorem isCompact_principalQSupportControls (q : ι → ℝ) :
    IsCompact (principalQSupportControls q) := by
  have hcoordinate (i : ι) : IsClosed
      {z : stdSimplex ℝ ι | z i * q i = 0} :=
    isClosed_eq
      (((continuous_apply i).comp continuous_subtype_val).mul continuous_const)
      continuous_const
  have hclosed : IsClosed (principalQSupportControls q) := by
    rw [show principalQSupportControls q =
        ⋂ i, {z | z i * q i = 0} by
      ext z
      simp [principalQSupportControls]]
    exact isClosed_iInter hcoordinate
  exact hclosed.isCompact

omit [DecidableEq ι] in
/-- Closed graph plus the common compact simplex range makes the support-only
correspondence upper hemicontinuous. -/
theorem upperHemicontinuous_principalQSupportControls :
    UpperHemicontinuous (principalQSupportControls (ι := ι)) := by
  rw [upperHemicontinuous_iff_forall_isOpen]
  intro q u hopen hu
  let bad : Set ((ι → ℝ) × stdSimplex ℝ ι) :=
    {point | point.2 ∈ principalQSupportControls point.1} ∩
      Prod.snd ⁻¹' uᶜ
  have hbad : IsClosed bad :=
    isClosed_graph_principalQSupportControls.inter
      (hopen.isClosed_compl.preimage continuous_snd)
  have hprojection : IsClosed (Prod.fst '' bad) :=
    isClosedMap_fst_of_compactSpace _ hbad
  have hq : q ∉ Prod.fst '' bad := by
    rintro ⟨point, ⟨hcontrol, hnotu⟩, rfl⟩
    exact hnotu (hu hcontrol)
  filter_upwards [hprojection.isOpen_compl.mem_nhds hq] with q' hq'
  intro z hz
  by_contra hzu
  exact hq' ⟨(q', z), ⟨hz, hzu⟩, rfl⟩

/-- The principal-Q face direction is a support-only control and its residual
is a separate inward tangent witness at every current zero coordinate. -/
theorem exists_supportControl_with_tangency
    (M : ι → ι → ℝ) (hdiag : ∀ i, M i i = 0)
    (hQ : IsProjectiveQBarMatrix M) (q : ι → ℝ)
    (hq : IsNonnegativeBoundary q) :
    ∃ direction : NonnegativeBoundaryDirection M q,
      direction.weight ∈ principalQSupportControls q := by
  obtain ⟨direction⟩ := exists_nonnegativeBoundaryDirection M hdiag hQ q hq
  refine ⟨direction, ?_⟩
  exact (mem_principalQSupportControls_iff).2
    direction.supported_on_zero

/-- The residual-minus-state velocity of a principal-Q direction lies in the
Bouligand tangent cone of the nonnegative boundary. -/
theorem NonnegativeBoundaryDirection.velocity_mem_tangentCone
    {M : ι → ι → ℝ} {q : ι → ℝ}
    (direction : NonnegativeBoundaryDirection M q)
    (hq : IsNonnegativeBoundary q) :
    (fun i => singletonLCPResidual M direction.weight i - q i) ∈
      tangentConeAt ℝ nonnegativeBoundary q := by
  let velocity : ι → ℝ := fun i =>
    singletonLCPResidual M direction.weight i - q i
  have hstep (n : ℕ) := direction.exists_boundary_step hq
    (show 0 < (1 : ℝ) / (n + 1) by positivity)
  choose α hα hαbound hαone hboundary using hstep
  have hα_tendsto : Tendsto α atTop (𝓝 0) := by
    apply squeeze_zero
    · exact fun n => (hα n).le
    · exact fun n => (hαbound n).le
    · simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  rw [mem_tangentConeAt_iff_exists_seq]
  refine ⟨fun n => (α n)⁻¹, fun n => α n • velocity, ?_, ?_, ?_⟩
  · simpa using hα_tendsto.smul_const velocity
  · filter_upwards [] with n
    have hpoint : q + α n • velocity = fun i =>
        (1 - α n) * q i +
          α n * singletonLCPResidual M direction.weight i := by
      funext i
      dsimp [velocity]
      ring
    rw [hpoint]
    exact hboundary n
  · have heq : (fun n => (α n)⁻¹ • (α n • velocity)) = fun _ => velocity := by
      funext n i
      simp only [Pi.smul_apply, smul_eq_mul]
      field_simp [ne_of_gt (hα n)]
    rw [heq]
    exact tendsto_const_nhds

/-! ## The induced velocity correspondence -/

/-- Residual-minus-state velocities generated by support-compatible simplex
controls. -/
def principalQVelocities (M : ι → ι → ℝ) (q : ι → ℝ) : Set (ι → ℝ) :=
  {velocity | ∃ z : stdSimplex ℝ ι,
    z ∈ principalQSupportControls q ∧
      velocity = fun i => singletonLCPResidual M z i - q i}

omit [DecidableEq ι] in
/-- Every velocity fiber is compact: it is the continuous image of the
compact support-control fiber. -/
theorem isCompact_principalQVelocities (M : ι → ι → ℝ) (q : ι → ℝ) :
    IsCompact (principalQVelocities M q) := by
  let velocity : stdSimplex ℝ ι → (ι → ℝ) := fun z i =>
    singletonLCPResidual M z i - q i
  have hcontinuous : Continuous velocity := by
    unfold velocity singletonLCPResidual
    fun_prop
  have himage : velocity '' principalQSupportControls q =
      principalQVelocities M q := by
    ext v
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z, hz, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z, hz, rfl⟩
  rw [← himage]
  exact (isCompact_principalQSupportControls q).image hcontinuous

omit [DecidableEq ι] in
/-- The induced velocity correspondence is upper hemicontinuous.  Compactness
of the common simplex control space turns its closed graph into a closed bad-
control projection. -/
theorem upperHemicontinuous_principalQVelocities (M : ι → ι → ℝ) :
    UpperHemicontinuous (principalQVelocities M) := by
  rw [upperHemicontinuous_iff_forall_isOpen]
  intro q u hopen hu
  let bad : Set ((ι → ℝ) × stdSimplex ℝ ι) :=
    {point | point.2 ∈ principalQSupportControls point.1} ∩
      {point | (fun i => singletonLCPResidual M point.2 i - point.1 i) ∉ u}
  have hbad : IsClosed bad := by
    apply isClosed_graph_principalQSupportControls.inter
    apply hopen.isClosed_compl.preimage
    unfold singletonLCPResidual
    fun_prop
  have hprojection : IsClosed (Prod.fst '' bad) :=
    isClosedMap_fst_of_compactSpace _ hbad
  have hq : q ∉ Prod.fst '' bad := by
    rintro ⟨point, ⟨hcontrol, hnotu⟩, rfl⟩
    exact hnotu (hu ⟨point.2, hcontrol, rfl⟩)
  filter_upwards [hprojection.isOpen_compl.mem_nhds hq] with q' hq'
  rintro velocity ⟨z, hz, rfl⟩
  by_contra hnotu
  exact hq' ⟨(q', z), ⟨hz, hnotu⟩, rfl⟩

omit [DecidableEq ι] in
/-- Every velocity fiber is convex.  Complementarity is linear in the
control once the state is fixed, and the residual velocity is affine. -/
theorem convex_principalQVelocities (M : ι → ι → ℝ) (q : ι → ℝ) :
    Convex ℝ (principalQVelocities M q) := by
  intro first hfirst second hsecond a b ha hb hab
  obtain ⟨z, hz, rfl⟩ := hfirst
  obtain ⟨w, hw, rfl⟩ := hsecond
  let mixedValue : ι → ℝ := a • (z : ι → ℝ) + b • (w : ι → ℝ)
  have hmixedSimplex : mixedValue ∈ stdSimplex ℝ ι :=
    convex_stdSimplex ℝ ι z.property w.property ha hb hab
  let mixed : stdSimplex ℝ ι := ⟨mixedValue, hmixedSimplex⟩
  have hmixedSupport : mixed ∈ principalQSupportControls q := by
    intro i
    have hzi := hz i
    have hwi := hw i
    change (a * z i + b * w i) * q i = 0
    rw [add_mul, mul_assoc, hzi, mul_zero, mul_assoc, hwi, mul_zero, add_zero]
  refine ⟨mixed, hmixedSupport, ?_⟩
  funext i
  change a * (singletonLCPResidual M z i - q i) +
      b * (singletonLCPResidual M w i - q i) =
    singletonLCPResidual M mixed i - q i
  unfold singletonLCPResidual
  change a * ((∑ owner, z owner * M i owner) - q i) +
      b * ((∑ owner, w owner * M i owner) - q i) =
    (∑ owner, (a * z owner + b * w owner) * M i owner) - q i
  rw [show (∑ owner, (a * z owner + b * w owner) * M i owner) =
      a * ∑ owner, z owner * M i owner +
        b * ∑ owner, w owner * M i owner by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro owner _
    ring]
  calc
    a * ((∑ owner, z owner * M i owner) - q i) +
        b * ((∑ owner, w owner * M i owner) - q i) =
      a * ∑ owner, z owner * M i owner +
        b * ∑ owner, w owner * M i owner - (a + b) * q i := by ring
    _ = a * ∑ owner, z owner * M i owner +
        b * ∑ owner, w owner * M i owner - q i := by rw [hab, one_mul]

omit [DecidableEq ι] in
/-- Every induced velocity has the coordinatewise linear-growth bound
`|vᵢ| ≤ ∑ⱼ |Mᵢⱼ| + |qᵢ|`. -/
theorem abs_le_of_mem_principalQVelocities
    (M : ι → ι → ℝ) (q velocity : ι → ℝ)
    (hvelocity : velocity ∈ principalQVelocities M q) (i : ι) :
    |velocity i| ≤ (∑ owner, |M i owner|) + |q i| := by
  obtain ⟨z, _hz, rfl⟩ := hvelocity
  unfold singletonLCPResidual
  refine (abs_sub _ _).trans (add_le_add ?_ le_rfl)
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  apply Finset.sum_le_sum
  intro owner _
  rw [abs_mul]
  have hzabs : |z owner| = z owner := abs_of_nonneg (z.property.1 owner)
  rw [hzabs]
  exact mul_le_of_le_one_left (abs_nonneg _) (stdSimplex.le_one z owner)

/-- Principal-Q tangency says precisely that the velocity fiber meets the
Bouligand tangent cone at every nonnegative boundary point. -/
theorem principalQVelocities_inter_tangentCone_nonempty
    (M : ι → ι → ℝ) (hdiag : ∀ i, M i i = 0)
    (hQ : IsProjectiveQBarMatrix M) (q : ι → ℝ)
    (hq : IsNonnegativeBoundary q) :
    (principalQVelocities M q ∩ tangentConeAt ℝ nonnegativeBoundary q).Nonempty := by
  obtain ⟨direction, hcontrol⟩ :=
    exists_supportControl_with_tangency M hdiag hQ q hq
  refine ⟨fun i => singletonLCPResidual M direction.weight i - q i,
    ⟨?_, direction.velocity_mem_tangentCone hq⟩⟩
  exact ⟨direction.weight, hcontrol, rfl⟩

end GameTheory.QuittingLCPClassification
