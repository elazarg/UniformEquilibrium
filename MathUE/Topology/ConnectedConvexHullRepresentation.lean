import MathUE.Topology.FarthestPointContactHull
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel

/-!
# Small convex representations of preconnected sets

The classical connected-set strengthening of Carathéodory's theorem needs
neither compactness nor path connectedness. The strict maximum regions of
normalized barycentric coordinates are the reflected-simplex cones in
Hanner--Rådström's proof, as reproduced by Teissier (2004), Proposition 4.2.
A tied maximum removes two old vertices while adding one actual source point.
Dimension zero needs one point; an empty source has no convex-hull point.
-/

noncomputable section

open Set
open scoped BigOperators Topology

namespace Math.Topology

/-- If every label has a strict winning point in a preconnected set, some
actual point has two maximizing labels. Finite strict-winner regions are
open; their discrete label cannot vary continuously on a preconnected set. -/
theorem exists_tied_max_of_isPreconnected
    {X I : Type*} [TopologicalSpace X] [Fintype I] [Nontrivial I]
    (source : Set X) (hsource : IsPreconnected source)
    (score : I → X → ℝ) (hcontinuous : ∀ i, ContinuousOn (score i) source)
    (hwinners : ∀ i, ∃ point ∈ source, ∀ j, j ≠ i → score j point < score i point) :
    ∃ point ∈ source, ∃ i j, i ≠ j ∧
      (∀ k, score k point ≤ score i point) ∧ score i point = score j point := by
  classical
  by_contra hnone
  have hmax (point : source) : ∃ i, ∀ j, score j point ≤ score i point := by
    obtain ⟨i, _hi, hbest⟩ := Finset.univ.exists_max_image
      (fun i => score i point) Finset.univ_nonempty
    exact ⟨i, fun j => hbest j (Finset.mem_univ j)⟩
  let winner : source → I := fun point => Classical.choose (hmax point)
  have winner_max (point : source) (j : I) : score j point ≤ score (winner point) point :=
    Classical.choose_spec (hmax point) j
  have winner_strict (point : source) (j : I) (hne : j ≠ winner point) :
      score j point < score (winner point) point := by
    apply lt_of_le_of_ne (winner_max point j)
    intro hequal
    exact hnone ⟨point, point.property, winner point, j, hne.symm,
      winner_max point, hequal.symm⟩
  let : TopologicalSpace I := ⊥
  let : DiscreteTopology I := discreteTopology_bot I
  let : PreconnectedSpace source := isPreconnected_iff_preconnectedSpace.mp hsource
  have hlabel : Continuous winner := by
    apply continuous_discrete_rng.mpr
    intro i
    have hfiber : winner ⁻¹' {i} =
        ⋂ j : {j : I // j ≠ i}, {point : source | score j.val point < score i point} := by
      ext point
      simp only [mem_preimage, mem_singleton_iff, mem_iInter, mem_ofPred_eq]
      constructor
      · intro hequal j
        simpa only [hequal] using winner_strict point j.val (by simpa [hequal] using j.2)
      · intro hstrict
        by_contra hne
        exact (hstrict ⟨winner point, hne⟩).not_ge (winner_max point i)
    rw [hfiber]
    apply isOpen_iInter_of_finite
    intro j
    exact isOpen_lt (hcontinuous j.val).domRestrict
      (hcontinuous i).domRestrict
  obtain ⟨i, j, hij⟩ := exists_pair_ne I
  obtain ⟨first, hfirst, hfirstWins⟩ := hwinners i
  obtain ⟨last, hlast, hlastWins⟩ := hwinners j
  have hfirstLabel : winner ⟨first, hfirst⟩ = i := by
    by_contra hne
    exact (hfirstWins _ hne).not_ge (winner_max ⟨first, hfirst⟩ i)
  have hlastLabel : winner ⟨last, hlast⟩ = j := by
    by_contra hne
    exact (hlastWins _ hne).not_ge (winner_max ⟨last, hlast⟩ j)
  have hconstant := PreconnectedSpace.constant
    (inferInstance : PreconnectedSpace source) hlabel
    (x := ⟨first, hfirst⟩) (y := ⟨last, hlast⟩)
  rw [hfirstLabel, hlastLabel] at hconstant
  exact hij hconstant

/-- Every convex-hull point of a preconnected subset of a finite-dimensional
real normed space has an internally selected nonempty finite representation
with at most the ambient dimension many points, or one point in dimension
zero. There is no compactness, path, supplied simplex or nonemptiness premise. -/
theorem exists_small_finset_of_mem_convexHull_isPreconnected
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (source : Set E) (hsource : IsPreconnected source) (point : E)
    (hpoint : point ∈ convexHull ℝ source) :
    ∃ family : Finset E, family.Nonempty ∧ (family : Set E) ⊆ source ∧
      point ∈ convexHull ℝ (family : Set E) ∧
      family.card ≤ max 1 (Module.finrank ℝ E) := by
  classical
  obtain ⟨family, hnonempty, hsubset, hmem, hindependent, hcard, hminimal⟩ :=
    exists_minimal_affineIndependent_finset_of_mem_convexHull
      source source point Subset.rfl hpoint
  have hcardAmbient : family.card ≤ Module.finrank ℝ E + 1 :=
    hcard.trans (Nat.add_le_add_right (Submodule.finrank_le _) 1)
  by_cases hsmall : family.card ≤ max 1 (Module.finrank ℝ E)
  · exact ⟨family, hnonempty, hsubset, hmem, hsmall⟩
  exfalso
  have hfull : family.card = Module.finrank ℝ E + 1 := by
    have := le_max_right 1 (Module.finrank ℝ E)
    omega
  have hmany : 1 < family.card := by
    have := le_max_left 1 (Module.finrank ℝ E)
    omega
  let I := ↥family
  let : Nontrivial I := Fintype.one_lt_card_iff_nontrivial.mp
    (by simpa only [I, Fintype.card_coe] using hmany)
  let basis : AffineBasis I ℝ E :=
    { toFun := fun i => (i : E)
      ind' := hindependent
      tot' := hindependent.affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr
        (by simpa only [I, Fintype.card_coe] using hfull) }
  obtain ⟨weight, hweightPos, hweightSum, hweightValue⟩ :=
    exists_pos_weights_of_minimal_convexHull_family family point hmem
      (fun alternative halternative hvalue =>
        hminimal alternative (halternative.trans hsubset) hvalue)
  let score : I → E → ℝ := fun i value => basis.coord i value / weight i
  have hscoreContinuous (i : I) : ContinuousOn (score i) source :=
    ((continuous_barycentric_coord basis i).div_const (weight i)).continuousOn
  have hwinners (i : I) : ∃ value ∈ source,
      ∀ j, j ≠ i → score j value < score i value := by
    refine ⟨basis i, hsubset i.property, ?_⟩
    intro j hji
    dsimp only [score]
    rw [basis.coord_apply_ne hji, basis.coord_apply_eq, zero_div]
    exact div_pos zero_lt_one (hweightPos i)
  obtain ⟨value, hvalueSource, i, j, hij, hmaximum, htied⟩ :=
    exists_tied_max_of_isPreconnected source hsource score hscoreContinuous hwinners
  let maximum := score i value
  have hmaximumPos : 0 < maximum := by
    by_contra hnot
    have hmaximumNonpos : maximum ≤ 0 := not_lt.mp hnot
    have hcoordNonpos (k : I) : basis.coord k value ≤ 0 := by
      have hratio : basis.coord k value / weight k ≤ 0 :=
        (hmaximum k).trans hmaximumNonpos
      simpa only [zero_mul] using (div_le_iff₀ (hweightPos k)).mp hratio
    have hsum := Finset.sum_nonpos (s := Finset.univ) (fun k _ => hcoordNonpos k)
    rw [basis.sum_coord_apply_eq_one] at hsum
    norm_num at hsum
  let coefficient := maximum⁻¹
  have hcoefficientPos : 0 < coefficient := inv_pos.mpr hmaximumPos
  have hcancel : coefficient * maximum = 1 := inv_mul_cancel₀ hmaximumPos.ne'
  let residual : I → ℝ := fun k => weight k - coefficient * basis.coord k value
  have hresidualNonneg (k : I) : 0 ≤ residual k := by
    have hcoord : basis.coord k value ≤ maximum * weight k :=
      (div_le_iff₀ (hweightPos k)).mp (hmaximum k)
    have hscaled : coefficient * basis.coord k value ≤ weight k := by
      calc
        _ ≤ coefficient * (maximum * weight k) :=
          mul_le_mul_of_nonneg_left hcoord hcoefficientPos.le
        _ = weight k := by rw [← mul_assoc, hcancel, one_mul]
    exact sub_nonneg.mpr hscaled
  have hcoordI : basis.coord i value = maximum * weight i :=
    (div_eq_iff (hweightPos i).ne').mp rfl
  have hcoordJ : basis.coord j value = maximum * weight j :=
    (div_eq_iff (hweightPos j).ne').mp htied.symm
  have hresidualI : residual i = 0 := by
    dsimp only [residual]
    rw [hcoordI, ← mul_assoc, hcancel, one_mul, sub_self]
  have hresidualJ : residual j = 0 := by
    dsimp only [residual]
    rw [hcoordJ, ← mul_assoc, hcancel, one_mul, sub_self]
  have hsum : ∑ k, residual k = 1 - coefficient := by
    dsimp only [residual]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hweightSum,
      basis.sum_coord_apply_eq_one, mul_one]
  have hvalue : ∑ k, residual k • basis k = point - coefficient • value := by
    simp only [residual, sub_smul, mul_smul, Finset.sum_sub_distrib, ← Finset.smul_sum,
      basis.linear_combination_coord_eq_self]
    change (∑ k, weight k • (k : E)) - coefficient • value = _
    rw [hweightValue]
  let remaining : Finset I := (Finset.univ.erase i).erase j
  have hsumRemaining : ∑ k ∈ remaining, residual k = 1 - coefficient := by
    dsimp only [remaining]
    rw [Finset.sum_erase _ hresidualJ, Finset.sum_erase _ hresidualI, hsum]
  have hvalueRemaining : ∑ k ∈ remaining, residual k • basis k =
      point - coefficient • value := by
    dsimp only [remaining]
    rw [Finset.sum_erase _ (by rw [hresidualJ, zero_smul]),
      Finset.sum_erase _ (by rw [hresidualI, zero_smul]), hvalue]
  let smaller := insert value ((family.erase (i : E)).erase (j : E))
  let newWeight : Option ↥remaining → ℝ
    | none => coefficient
    | some k => residual k.val
  let newPoint : Option ↥remaining → E
    | none => value
    | some k => basis k.val
  have hnewWeightNonneg (label : Option ↥remaining) : 0 ≤ newWeight label := by
    cases label with
    | none => exact hcoefficientPos.le
    | some k => exact hresidualNonneg k.val
  have hnewWeightSum : ∑ label, newWeight label = 1 := by
    rw [Fintype.sum_option]
    change coefficient + ∑ k : remaining, residual k.val = 1
    rw [remaining.sum_coe_sort (fun k => residual k), hsumRemaining]
    ring
  have hnewValue : ∑ label, newWeight label • newPoint label = point := by
    rw [Fintype.sum_option]
    change coefficient • value + ∑ k : remaining, residual k.val • basis k.val = point
    rw [remaining.sum_coe_sort (fun k => residual k • basis k), hvalueRemaining]
    abel
  have hnewPoint (label : Option ↥remaining) : newPoint label ∈ (smaller : Set E) := by
    cases label with
    | none => exact Finset.mem_insert_self _ _
    | some k =>
      apply Finset.mem_insert_of_mem
      have hk := Finset.mem_erase.mp k.property
      have hk' := Finset.mem_erase.mp hk.2
      refine Finset.mem_erase.mpr ⟨?_, Finset.mem_erase.mpr ⟨?_, k.val.property⟩⟩
      · intro hequal
        exact hk.1 (Subtype.ext hequal)
      · intro hequal
        exact hk'.1 (Subtype.ext hequal)
  have hsmallerSubset : (smaller : Set E) ⊆ source := by
    intro member hmember
    rcases Finset.mem_insert.mp hmember with rfl | hmember
    · exact hvalueSource
    · exact hsubset (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hmember))
  have hsmallerMem : point ∈ convexHull ℝ (smaller : Set E) := by
    rw [← hnewValue]
    exact (convex_convexHull ℝ (smaller : Set E)).sum_mem
      (fun label _ => hnewWeightNonneg label) hnewWeightSum
      (fun label _ => subset_convexHull ℝ (smaller : Set E) (hnewPoint label))
  have hji : (j : E) ≠ (i : E) := fun hequal => hij (Subtype.ext hequal.symm)
  have hjRemaining : (j : E) ∈ family.erase (i : E) :=
    Finset.mem_erase.mpr ⟨hji, j.property⟩
  have hcardI := Finset.card_erase_add_one i.property
  have hcardJ := Finset.card_erase_add_one hjRemaining
  have hcardSmaller : smaller.card < family.card := by
    have := Finset.card_insert_le value ((family.erase (i : E)).erase (j : E))
    dsimp only [smaller]
    omega
  exact hcardSmaller.not_ge (hminimal smaller hsmallerSubset hsmallerMem)

end Math.Topology
