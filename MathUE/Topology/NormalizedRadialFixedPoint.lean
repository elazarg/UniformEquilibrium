import FixedPointTheorems.brouwer
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! # A normalized direction and radius fixed-point construction

The outer hypothesis excludes scaled eigenpoints with scale at most one.
It is weaker than requiring an outward radial inequality everywhere.
-/

noncomputable section

namespace Math

open Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem exists_fixedPoint_of_normalized_radial_map
    (field : E → E) (mass : E → ℝ) (hmass : Continuous mass)
    (directions : Set E) (hconvex : Convex ℝ directions)
    (hcompact : IsCompact directions) (hnonempty : directions.Nonempty)
    {inner outer : ℝ} (hinner : 0 < inner) (hradii : inner < outer)
    (hfield : ContinuousOn (fun pair : E × ℝ => field (pair.2 • pair.1))
      (directions ×ˢ Icc inner outer))
    (hpositive : ∀ point ∈ directions, ∀ radius ∈ Icc inner outer,
      0 < mass (field (radius • point)))
    (hdirection : ∀ point ∈ directions, ∀ radius ∈ Icc inner outer,
      (mass (field (radius • point)))⁻¹ • field (radius • point) ∈ directions)
    (hsmall : ∀ point ∈ directions, mass (field (inner • point)) / inner < 1)
    (houter : ∀ point ∈ directions, ∀ scale : ℝ, 0 < scale → scale ≤ 1 →
      field (outer • point) ≠ scale • (outer • point)) :
    ∃ point ∈ directions, ∃ radius ∈ Ioo inner outer,
      field (radius • point) = radius • point := by
  let domain : Set (E × ℝ) := directions ×ˢ Icc inner outer
  let values : domain → E := fun pair => field (pair.val.2 • pair.val.1)
  let radii : domain → ℝ := fun pair => pair.val.2
  let input : domain → ℝ := fun pair => radii pair + 1 - mass (values pair) / radii pair
  let transform : domain → domain := fun pair =>
    ⟨((mass (values pair))⁻¹ • values pair,
      (projIcc inner outer hradii.le (input pair) : ℝ)),
      hdirection pair.val.1 pair.property.1 pair.val.2 pair.property.2,
      (projIcc inner outer hradii.le (input pair)).property⟩
  have hvalues : Continuous values := hfield.domRestrict
  have hradiiContinuous : Continuous radii := continuous_snd.comp continuous_subtype_val
  have hmassContinuous := hmass.comp hvalues
  have hmassPositive : ∀ pair : domain, 0 < mass (values pair) := fun pair =>
    hpositive pair.val.1 pair.property.1 pair.val.2 pair.property.2
  have hradiiPositive : ∀ pair : domain, 0 < radii pair := fun pair =>
    hinner.trans_le pair.property.2.1
  have hinput : Continuous input :=
    (hradiiContinuous.add continuous_const).sub
      (hmassContinuous.div hradiiContinuous (fun pair => (hradiiPositive pair).ne'))
  have htransform : Continuous transform := by
    apply continuous_induced_rng.mpr
    exact ((hmassContinuous.inv₀ (fun pair => (hmassPositive pair).ne')).smul hvalues).prodMk
      (continuous_subtype_val.comp (continuous_projIcc.comp hinput))
  have hdomainNonempty : domain.Nonempty := by
    obtain ⟨point, hpoint⟩ := hnonempty
    exact ⟨(point, inner), hpoint, le_rfl, hradii.le⟩
  obtain ⟨pair, hfixed⟩ := brouwer_fixed_point domain
    (hconvex.prod (convex_Icc inner outer)) (hcompact.prod isCompact_Icc)
    hdomainNonempty ⟨transform, htransform⟩
  have hdirectionEq : (mass (values pair))⁻¹ • values pair = pair.val.1 :=
    congrArg Prod.fst (congrArg Subtype.val hfixed)
  have hradiusEq : (projIcc inner outer hradii.le (input pair) : ℝ) = radii pair :=
    congrArg Prod.snd (congrArg Subtype.val hfixed)
  have hvaluesEq : values pair = mass (values pair) • pair.val.1 := by
    rw [← hdirectionEq, smul_smul, mul_inv_cancel₀ (hmassPositive pair).ne', one_smul]
  have hnotInner : radii pair ≠ inner := by
    intro heq
    have hleft : projIcc inner outer hradii.le (input pair) =
        ⟨inner, left_mem_Icc.mpr hradii.le⟩ := Subtype.ext (hradiusEq.trans heq)
    have hinputLe := (projIcc_eq_left hradii).mp hleft
    have hsmallAt := hsmall pair.val.1 pair.property.1
    have hvaluesInner : values pair = field (inner • pair.val.1) := by
      change field (radii pair • pair.val.1) = _
      rw [heq]
    change radii pair + 1 - mass (values pair) / radii pair ≤ inner at hinputLe
    rw [heq, hvaluesInner] at hinputLe
    linarith
  have hnotOuter : radii pair ≠ outer := by
    intro heq
    have hright : projIcc inner outer hradii.le (input pair) =
        ⟨outer, right_mem_Icc.mpr hradii.le⟩ := Subtype.ext (hradiusEq.trans heq)
    have hinputGe := (projIcc_eq_right hradii).mp hright
    have hscaleLe : mass (values pair) / radii pair ≤ 1 := by
      change outer ≤ radii pair + 1 - mass (values pair) / radii pair at hinputGe
      rw [heq] at hinputGe
      rw [heq]
      linarith
    apply houter pair.val.1 pair.property.1 (mass (values pair) / radii pair)
      (div_pos (hmassPositive pair) (hradiiPositive pair)) hscaleLe
    rw [← heq]
    change values pair = (mass (values pair) / radii pair) • (radii pair • pair.val.1)
    rw [smul_smul, div_mul_cancel₀ _ (hradiiPositive pair).ne', ← hvaluesEq]
  have hinterior : radii pair ∈ Ioo inner outer :=
    ⟨lt_of_le_of_ne pair.property.2.1 (Ne.symm hnotInner),
      lt_of_le_of_ne pair.property.2.2 hnotOuter⟩
  have hinputEq : input pair = radii pair := by
    by_cases hlow : input pair ≤ inner
    · rw [projIcc_of_le_left hradii.le hlow] at hradiusEq
      exact False.elim (hnotInner hradiusEq.symm)
    by_cases hhigh : outer ≤ input pair
    · rw [projIcc_of_right_le hradii.le hhigh] at hradiusEq
      exact False.elim (hnotOuter hradiusEq.symm)
    have hmem : input pair ∈ Icc inner outer := ⟨(lt_of_not_ge hlow).le,
      (lt_of_not_ge hhigh).le⟩
    rw [projIcc_of_mem hradii.le hmem] at hradiusEq
    exact hradiusEq
  have hmassEq : mass (values pair) = radii pair := by
    change radii pair + 1 - mass (values pair) / radii pair = radii pair at hinputEq
    have hratio : mass (values pair) / radii pair = 1 := by linarith
    simpa only [one_mul] using (div_eq_iff (hradiiPositive pair).ne').mp hratio
  refine ⟨pair.val.1, pair.property.1, radii pair, hinterior, ?_⟩
  exact hvaluesEq.trans (congrArg (fun radius => radius • pair.val.1) hmassEq)

end Math
