/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.Probability
import MathUE.ProbabilityMassFunction
import MathUE.Simplex
import GameTheory.Math.Probability.Simplex
import Mathlib.Analysis.Convex.Extreme
import Mathlib.LinearAlgebra.AffineSpace.AffineMap

/-!
# PMFs and finite simplices

This file provides a small bridge between finite `PMF`s and the standard
simplex in the ambient vector space `α → ℝ`.
-/

noncomputable section

open scoped BigOperators

namespace Math
namespace ProbabilityMassFunction

open GameTheory.Math.Probability

variable {α : Type*}

/-- The real coordinate vector associated to a finite probability mass
function. -/
def toVector [Fintype α] (μ : PMF α) : α → ℝ :=
  fun a => (μ a).toReal

/-- The coordinate vector of a finite `PMF` belongs to the canonical
coordinate image of the standard simplex. -/
theorem toVector_mem_stdSimplex [Fintype α] (μ : PMF α) :
    toVector μ ∈ simplexWeights α := by
  rw [mem_simplexWeights]
  exact ⟨fun _ => ENNReal.toReal_nonneg, Math.Probability.pmf_toReal_sum_one μ⟩

/-- The weights of a canonical simplex element lie in its coordinate image. -/
theorem weights_mem_simplexWeights (x : Convexity.StdSimplex ℝ α) :
    (x.weights : α → ℝ) ∈ simplexWeights α := by
  unfold simplexWeights
  exact ⟨x, rfl⟩

/-- The coordinate-vector map from finite `PMF`s is injective. -/
theorem toVector_injective [Fintype α] :
    Function.Injective (toVector : PMF α → α → ℝ) := by
  intro μ ν h
  apply PMF.ext
  intro a
  have hreal : (μ a).toReal = (ν a).toReal := congrFun h a
  exact (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top μ a) (PMF.apply_ne_top ν a)).mp hreal

@[simp]
theorem toVector_pos_iff_ne_zero [Fintype α] (μ : PMF α) (a : α) :
    0 < toVector μ a ↔ μ a ≠ 0 := by
  constructor
  · intro h hzero
    simp [toVector, hzero] at h
  · intro h
    exact ENNReal.toReal_pos h (PMF.apply_ne_top μ a)

/-- Turn a point of the finite simplex's coordinate image into a `PMF`. -/
def ofVector [Fintype α] (w : α → ℝ) (hw : w ∈ simplexWeights α) : PMF α :=
  ⟨fun a => ENNReal.ofReal (w a), by
    rw [mem_simplexWeights] at hw
    have hsum : ∑ a : α, ENNReal.ofReal (w a) = 1 := by
      rw [← ENNReal.ofReal_sum_of_nonneg (fun a _ => hw.1 a), hw.2]
      norm_num
    simpa [tsum_fintype, hsum] using (hasSum_fintype (fun a : α => ENNReal.ofReal (w a)))⟩

@[simp]
theorem ofVector_apply [Fintype α] {w : α → ℝ} (hw : w ∈ simplexWeights α) (a : α) :
    ofVector w hw a = ENNReal.ofReal (w a) :=
  rfl

@[simp]
theorem ofVector_toReal [Fintype α] {w : α → ℝ} (hw : w ∈ simplexWeights α) (a : α) :
    ((ofVector w hw) a).toReal = w a := by
  rw [ofVector_apply]
  exact ENNReal.toReal_ofReal ((mem_simplexWeights.mp hw).1 a)

@[simp]
theorem ofVector_ne_zero_iff [Fintype α] {w : α → ℝ} (hw : w ∈ simplexWeights α)
    (a : α) :
    ofVector w hw a ≠ 0 ↔ 0 < w a := by
  constructor
  · intro h
    have hpos := ENNReal.toReal_pos h (PMF.apply_ne_top (ofVector w hw) a)
    rwa [ofVector_toReal hw a] at hpos
  · intro h hzero
    have hreal : ((ofVector w hw) a).toReal = 0 := by simp [hzero]
    rw [ofVector_toReal hw a] at hreal
    linarith

/-- Converting a simplex vector to a `PMF` and back recovers the vector. -/
theorem toVector_ofVector [Fintype α] {w : α → ℝ} (hw : w ∈ simplexWeights α) :
    toVector (ofVector w hw) = w := by
  funext a
  exact ofVector_toReal hw a

/-- Converting a finite `PMF` to its coordinate vector and back recovers the
original `PMF`. -/
theorem ofVector_toVector [Fintype α] (μ : PMF α) :
    ofVector (toVector μ) (toVector_mem_stdSimplex μ) = μ := by
  exact toVector_injective (toVector_ofVector (toVector_mem_stdSimplex μ))

/-- Finite probability mass functions are equivalent to points of the real
standard simplex. -/
def stdSimplexEquiv [Fintype α] : PMF α ≃ Convexity.StdSimplex ℝ α where
  toFun μ := {
    weights := Finsupp.equivFunOnFinite.symm (toVector μ)
    nonneg a := ENNReal.toReal_nonneg
    total := by
      rw [Finsupp.sum_fintype]
      · exact Math.Probability.pmf_toReal_sum_one μ
      · intro
        rfl }
  invFun x := ofVector x.weights (weights_mem_simplexWeights x)
  left_inv := ofVector_toVector
  right_inv x := by
    apply Convexity.StdSimplex.ext
    ext a
    exact ofVector_toReal (weights_mem_simplexWeights x) a

@[simp]
theorem simplexEquiv_apply_weights [Fintype α] (μ : PMF α) :
    (stdSimplexEquiv μ).weights = Finsupp.equivFunOnFinite.symm (toVector μ) :=
  rfl

@[simp]
theorem coe_stdSimplexEquiv_apply [Fintype α] (μ : PMF α) :
    ((stdSimplexEquiv μ).weights : α → ℝ) = toVector μ :=
  rfl

@[simp]
theorem stdSimplexEquiv_symm_apply [Fintype α] (x : Convexity.StdSimplex ℝ α) :
    (stdSimplexEquiv (α := α)).symm x =
      ofVector x.weights (weights_mem_simplexWeights x) :=
  rfl

/-- Expectation under the PMF represented by a simplex point is the simplex
weighted sum.  This is the basic dictionary between the probabilistic and
finite-dimensional presentations of mixed strategies. -/
theorem expect_stdSimplexEquiv_symm_eq_wsum [Fintype α]
    (x : Convexity.StdSimplex ℝ α) (f : α → ℝ) :
    Math.Probability.expect ((stdSimplexEquiv (α := α)).symm x) f = wsum x f := by
  rw [Math.Probability.expect_eq_sum]
  change (∑ a, ((ofVector x.weights (weights_mem_simplexWeights x)) a).toReal * f a) =
    ∑ a, x.weights a * f a
  apply Finset.sum_congr rfl
  intro a _
  rw [ofVector_toReal]

/-- The coordinatewise expectation of vectors lies in the convex hull of
their range. -/
theorem coordinateExpectation_mem_convexHull_range [Fintype α]
    {ι : Type*} (μ : PMF α) (f : α → ι → ℝ) :
    (fun i ↦ Math.Probability.expect μ (fun a ↦ f a i)) ∈
      convexHull ℝ (Set.range f) := by
  refine mem_convexHull_of_exists_fintype (s := Set.range f)
    (ι := α) (fun a ↦ (μ a).toReal) f (fun _ ↦ ENNReal.toReal_nonneg) ?_ ?_ ?_
  · exact Math.Probability.pmf_toReal_sum_one μ
  · exact fun a ↦ ⟨a, rfl⟩
  · funext i
    simp only [Math.Probability.expect_eq_sum, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul]

/-- Linear maps commute with the actual finite coordinatewise expectation. -/
theorem coordinateExpectation_map_linear [Fintype α] {ι : Type*}
    (μ : PMF α) (value : α → ι → ℝ) (map : (ι → ℝ) →ₗ[ℝ] ℝ) :
    map (fun i => Math.Probability.expect μ (fun a => value a i)) =
      Math.Probability.expect μ (fun a => map (value a)) := by
  have hvector : (fun i => Math.Probability.expect μ (fun a => value a i)) =
      ∑ a, (μ a).toReal • value a := by
    funext i
    simp only [Math.Probability.expect_eq_sum, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul]
  rw [hvector, map_sum, Math.Probability.expect_eq_sum]
  simp only [map_smul, smul_eq_mul]

/-- Affine coordinates commute with finite coordinatewise expectation. -/
theorem coordinateExpectation_map_affine [Fintype α] {ι : Type*}
    (μ : PMF α) (value : α → ι → ℝ) (map : (ι → ℝ) →ᵃ[ℝ] ℝ) :
    map (fun i => Math.Probability.expect μ (fun a => value a i)) =
      Math.Probability.expect μ (fun a => map (value a)) := by
  have hmap (point : ι → ℝ) : map point = map.linear point + map 0 := by
    exact congrFun (AffineMap.decomp map) point
  have hvalues : (fun a => map (value a)) =
      (fun a => map.linear (value a) + map 0) := by
    funext a
    exact hmap (value a)
  calc
    map (fun i => Math.Probability.expect μ (fun a => value a i)) =
        map.linear (fun i => Math.Probability.expect μ (fun a => value a i)) + map 0 :=
      hmap _
    _ = Math.Probability.expect μ (fun a => map (value a)) := by
      rw [hvalues, Math.Probability.expect_add, Math.Probability.expect_const,
        coordinateExpectation_map_linear]

/-- Replacing one finite-PMF observable changes its expectation by exactly
that atom's mass times the replacement difference. -/
theorem expect_functionUpdate [Fintype α] [DecidableEq α]
    (μ : PMF α) (value : α → ℝ) (selected : α) (replacement : ℝ) :
    Math.Probability.expect μ (Function.update value selected replacement) =
      Math.Probability.expect μ value +
        (μ selected).toReal * (replacement - value selected) := by
  have hupdate : Function.update value selected replacement =
      fun point => value point +
        (replacement - value selected) * (Pi.single selected (1 : ℝ) : α → ℝ) point := by
    funext point
    by_cases hpoint : point = selected
    · subst point
      simp
    · simp [hpoint]
  rw [hupdate, Math.Probability.expect_add, Math.Probability.expect_const_mul,
    Math.Probability.expect_pi_single]
  ring

/-- Finite coordinatewise expectations preserve a convex set when the actual
supported values belong to it; unsupported values need no membership premise. -/
theorem coordinateExpectation_mem_convex_of_mem_support [Fintype α] {ι : Type*}
    (μ : PMF α) (value : α → ι → ℝ) (target : Set (ι → ℝ))
    (hconvex : Convex ℝ target)
    (hvalue : ∀ point ∈ μ.support, value point ∈ target) :
    (fun i => Math.Probability.expect μ (fun point => value point i)) ∈ target := by
  classical
  obtain ⟨anchor, hanchor⟩ := μ.support_nonempty
  let completed := fun point => if point ∈ μ.support then value point else value anchor
  have hcompleted (point : α) : completed point ∈ target := by
    by_cases hpoint : point ∈ μ.support
    · simpa only [completed, ite_eq_left hpoint] using hvalue point hpoint
    · simpa only [completed, ite_eq_right hpoint] using hvalue anchor hanchor
  have hmem : (fun i => Math.Probability.expect μ (fun point => completed point i)) ∈
      target := convexHull_min
        (by rintro _ ⟨point, rfl⟩; exact hcompleted point) hconvex
        (coordinateExpectation_mem_convexHull_range μ completed)
  have hequal : (fun i => Math.Probability.expect μ (fun point => value point i)) =
      fun i => Math.Probability.expect μ (fun point => completed point i) := by
    funext i
    apply expect_congr_on_support
    intro point hpoint
    simp only [completed, ite_eq_left hpoint]
  rw [hequal]
  exact hmem

/-- If the actual finite-PMF barycenter lies in an extreme subset of a convex
set, each supported point lies in that extreme subset. The remainder is the
canonical Finset.centerMass; no face-valued selection is a premise. -/
theorem coordinateExpectation_mem_isExtreme_of_mem [Fintype α] {ι : Type*}
    (μ : PMF α) (value : α → ι → ℝ) (ambient face : Set (ι → ℝ))
    (hconvex : Convex ℝ ambient) (hextreme : IsExtreme ℝ ambient face)
    (hvalue : ∀ point, value point ∈ ambient)
    (hmean : (fun i => Math.Probability.expect μ (fun point => value point i)) ∈ face)
    (selected : α) (hsupport : selected ∈ μ.support) : value selected ∈ face := by
  classical
  let weight := fun point => (μ point).toReal
  have hsum : ∑ point, weight point = 1 := Math.Probability.pmf_toReal_sum_one μ
  have hpositive : 0 < weight selected :=
    ENNReal.toReal_pos ((PMF.mem_support_iff μ selected).mp hsupport)
      (μ.apply_ne_top selected)
  have hle : weight selected ≤ 1 :=
    ENNReal.toReal_mono ENNReal.one_ne_top (PMF.coe_le_one μ selected)
  by_cases hone : weight selected = 1
  · have hmass : μ selected = 1 :=
      (ENNReal.toReal_eq_toReal_iff' (μ.apply_ne_top selected) ENNReal.one_ne_top).mp
        (by simpa only [weight, ENNReal.toReal_one] using hone)
    have hsingleton := (PMF.apply_eq_one_iff μ selected).mp hmass
    have hequal : (fun i => Math.Probability.expect μ (fun point => value point i)) =
        value selected := by
      funext i
      calc
        Math.Probability.expect μ (fun point => value point i) =
            Math.Probability.expect μ (fun _ => value selected i) := by
          apply expect_congr_on_support
          intro point hpoint
          rw [hsingleton] at hpoint
          exact congrArg (fun member => value member i) (Set.mem_singleton_iff.mp hpoint)
        _ = value selected i := Math.Probability.expect_const _ _
    rw [hequal] at hmean
    exact hmean
  · have hlt : weight selected < 1 := lt_of_le_of_ne hle hone
    let remainder := (Finset.univ : Finset α).erase selected
    have hrestSum : ∑ point ∈ remainder, weight point = 1 - weight selected := by
      have h := Finset.sum_erase_add Finset.univ weight (Finset.mem_univ selected)
      rw [hsum] at h
      dsimp only [remainder]
      linarith
    have hrestPositive : 0 < ∑ point ∈ remainder, weight point := by
      rw [hrestSum]
      exact sub_pos.mpr hlt
    have hrest : remainder.centerMass weight value ∈ ambient :=
      hconvex.centerMass_mem (fun _ _ => ENNReal.toReal_nonneg)
        hrestPositive (fun point _ => hvalue point)
    have hvector : (fun i => Math.Probability.expect μ (fun point => value point i)) =
        ∑ point, weight point • value point := by
      funext i
      simp only [Math.Probability.expect_eq_sum, Finset.sum_apply,
        Pi.smul_apply, smul_eq_mul, weight]
    have hcenter : (fun i => Math.Probability.expect μ (fun point => value point i)) =
        Finset.univ.centerMass weight value :=
      hvector.trans (Finset.univ.centerMass_eq_of_sum_1 value hsum).symm
    have hinsert : insert selected remainder = (Finset.univ : Finset α) := by
      simpa only [remainder] using Finset.insert_erase (Finset.mem_univ selected)
    have hsplit := Finset.centerMass_insert selected remainder value
      (Finset.notMem_erase selected Finset.univ) (ne_of_gt hrestPositive)
    rw [hinsert, hrestSum,
      show weight selected + (1 - weight selected) = 1 by ring, div_one, div_one] at hsplit
    exact hextreme.left_mem_of_mem_openSegment (hvalue selected) hrest hmean
      ⟨weight selected, 1 - weight selected, hpositive, sub_pos.mpr hlt,
        by ring, (hcenter.trans hsplit).symm⟩

/-- A convex extreme subset of a finite hull is the hull of the actual
generators it contains. Supported generator inheritance is canonical PMF
face inheritance, not a supplied finite-face presentation. -/
theorem convex_isExtreme_eq_convexHull_inter_of_finite {ι : Type*}
    (source face : Set (ι → ℝ)) (hfinite : source.Finite)
    (hface : Convex ℝ face) (hextreme : IsExtreme ℝ (convexHull ℝ source) face) :
    face = convexHull ℝ (source ∩ face) := by
  classical
  apply Set.Subset.antisymm
  · intro x hx
    let family := hfinite.toFinset
    have hxHull : x ∈ convexHull ℝ (family : Set (ι → ℝ)) := by
      simpa only [family, Set.Finite.coe_toFinset] using hextreme.subset hx
    obtain ⟨weight, hnonneg, hsum, hvalue⟩ := Finset.mem_convexHull'.mp hxHull
    let weights : family → ℝ := fun k => weight k
    have hweights : weights ∈ simplexWeights family := by
      rw [mem_simplexWeights]
      refine ⟨fun k => hnonneg k k.property, ?_⟩
      rw [family.sum_coe_sort (fun k => weight k)]
      exact hsum
    let law := ofVector weights hweights
    let value : family → ι → ℝ := fun k => k
    have hmean : (fun i => Math.Probability.expect law (fun k => value k i)) = x := by
      have hsumValue : ∑ k : family, weights k • value k = x := by
        rw [family.sum_coe_sort (fun k => weight k • k)]
        exact hvalue
      rw [← hsumValue]
      funext i
      simp only [Math.Probability.expect_eq_sum, law, ofVector_toReal,
        Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    have hsource (k : family) : value k ∈ source := by
      simpa only [value, family, Set.Finite.mem_toFinset] using k.property
    have hfaceSupport (k : family) (hk : k ∈ law.support) : value k ∈ face :=
      coordinateExpectation_mem_isExtreme_of_mem law value
        (convexHull ℝ source) face (convex_convexHull ℝ source) hextreme
        (fun j => subset_convexHull ℝ source (hsource j)) (hmean.symm ▸ hx) k hk
    have hmem := coordinateExpectation_mem_convex_of_mem_support law value
      (convexHull ℝ (source ∩ face)) (convex_convexHull ℝ (source ∩ face))
        (fun k hk => subset_convexHull ℝ _ ⟨hsource k, hfaceSupport k hk⟩)
    rwa [hmean] at hmem
  · exact convexHull_min Set.inter_subset_right hface

/-- A simplex point represents a given finite `PMF` exactly when its coordinate
vector is that PMF's coordinate vector. -/
theorem ofVector_eq_iff_eq_toVector [Fintype α]
    (x : Convexity.StdSimplex ℝ α) (μ : PMF α) :
    ofVector x.weights (weights_mem_simplexWeights x) = μ ↔ x = stdSimplexEquiv μ := by
  constructor
  · intro h
    apply Convexity.StdSimplex.ext
    have hx :
        toVector (ofVector x.weights (weights_mem_simplexWeights x)) = toVector μ :=
      congrArg toVector h
    ext a
    change x.weights a = toVector μ a
    exact (ofVector_toReal (weights_mem_simplexWeights x) a).symm.trans (congrFun hx a)
  · intro h
    subst h
    exact ofVector_toVector μ

/-! ## Boolean Bernoulli laws -/

/-- The Boolean PMF assigning real probability `p` to `true`. -/
def bernoulliBool (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : PMF Bool :=
  ofVector (fun value ↦ if value then p else 1 - p) <| by
    rw [mem_simplexWeights]
    constructor
    · intro value
      cases value <;> simp_all
    · simp

@[simp] theorem bernoulliBool_true_toReal
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (bernoulliBool p hp0 hp1 true).toReal = p := by
  apply ofVector_toReal

@[simp] theorem bernoulliBool_false_toReal
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (bernoulliBool p hp0 hp1 false).toReal = 1 - p := by
  apply ofVector_toReal

end ProbabilityMassFunction
end Math
