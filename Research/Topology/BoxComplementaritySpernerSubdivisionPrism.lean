/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Research.Topology.BoxComplementaritySpernerLocalCount

/-!
# Common refinements and the cubical subdivision-prism seam

This module begins the concrete cross-resolution prism construction below the
finite local counts.  It constructs the full same-resolution prism incidence,
identifies both endpoint counts, and proves the parity of one elementary
stellar-subdivision move.  Product resolution contains both endpoint grids at
their literal geometric points, but the pinned ordered Kuhn simplices are not
preserved by those vertex embeddings: a unit coarse jump becomes a jump by the
other resolution.  No cross-resolution subdivision chain or parity
specification is constructed here.
-/

noncomputable section

namespace Math

open Classical Set

variable {n : ℕ}

/-- Scale one grid coordinate into a product-resolution grid. -/
def finProductRefinementCoordinate (p factor : ℕ)
    (coordinate : Fin (p + 1)) : Fin (p * factor + 1) :=
  ⟨coordinate.1 * factor, by
    have hcoordinate : coordinate.1 ≤ p := Nat.le_of_lt_succ coordinate.2
    exact lt_of_le_of_lt (Nat.mul_le_mul_right factor hcoordinate)
      (Nat.lt_succ_self _) ⟩

@[simp] theorem finProductRefinementCoordinate_val
    (p factor : ℕ) (coordinate : Fin (p + 1)) :
    (finProductRefinementCoordinate p factor coordinate).1 =
      coordinate.1 * factor :=
  rfl

/-- Positive scaling is injective on grid coordinates. -/
theorem finProductRefinementCoordinate_injective
    (p factor : ℕ) (hfactor : 0 < factor) :
    Function.Injective (finProductRefinementCoordinate p factor) := by
  intro first second heq
  apply Fin.ext
  have hval := congrArg Fin.val heq
  simp only [finProductRefinementCoordinate_val] at hval
  exact Nat.eq_of_mul_eq_mul_right hfactor hval

/-- Coordinatewise product-refinement embedding of a cubical grid. -/
def productRefinementVertex (p factor : ℕ)
    (vertex : Fin n → Fin (p + 1)) : Fin n → Fin (p * factor + 1) :=
  fun who ↦ finProductRefinementCoordinate p factor (vertex who)

/-- The product-refinement vertex embedding is injective. -/
theorem productRefinementVertex_injective
    (p factor : ℕ) (hfactor : 0 < factor) :
    Function.Injective (productRefinementVertex (n := n) p factor) := by
  intro first second heq
  funext who
  exact finProductRefinementCoordinate_injective p factor hfactor
    (congrFun heq who)

/-- Scaling grid numerators and denominators by the same positive factor does
not change the represented point of the unit cube. -/
theorem boxComplementarityGridPoint_productRefinementVertex
    (p factor : ℕ) (hp : 0 < p) (hfactor : 0 < factor)
    (vertex : Fin n → Fin (p + 1)) :
    boxComplementarityGridPoint (p * factor)
        (productRefinementVertex p factor vertex) =
      boxComplementarityGridPoint p vertex := by
  funext who
  apply Subtype.ext
  simp only [boxComplementarityGridPoint, productRefinementVertex,
    finProductRefinementCoordinate]
  push_cast
  field_simp [Nat.ne_of_gt hp, Nat.ne_of_gt hfactor]

/-- The concrete common product resolution for two positive grids. -/
def commonProductResolution (p q : ℕ) : ℕ := p * q

/-- The left grid embeds into the common product resolution. -/
def leftCommonRefinementVertex (p q : ℕ)
    (vertex : Fin n → Fin (p + 1)) :
    Fin n → Fin (commonProductResolution p q + 1) :=
  productRefinementVertex p q vertex

/-- The right grid embeds into the same common product resolution. -/
def rightCommonRefinementVertex (p q : ℕ)
    (vertex : Fin n → Fin (q + 1)) :
    Fin n → Fin (commonProductResolution p q + 1) := by
  simpa only [commonProductResolution, Nat.mul_comm] using
    productRefinementVertex q p vertex

/-- The reduced complementarity label bundled with its sharp finite bound. -/
def boxComplementarityFinLabel
    (problem : BoxComplementarityProblem (Fin n)) (p : ℕ)
    (vertex : Fin n → Fin (p + 1)) : Fin (n + 1) :=
  ⟨boxComplementarityReducedLabel problem p vertex,
    Nat.lt_succ_of_le
      (boxComplementarityReducedLabel_properties problem p vertex).1⟩

@[simp] theorem boxComplementarityFinLabel_val
    (problem : BoxComplementarityProblem (Fin n)) (p : ℕ)
    (vertex : Fin n → Fin (p + 1)) :
    (boxComplementarityFinLabel problem p vertex).1 =
      boxComplementarityReducedLabel problem p vertex :=
  rfl

/-- On a top-dimensional Kuhn simplex, carrying every reduced label is
equivalent to injectivity of the bounded finite labels. -/
theorem boxComplementarity_completeSimplex_iff_finLabel_injective
    (problem : BoxComplementarityProblem (Fin n))
    (p : ℕ) (hp : 0 < p)
    (vertices : Fin (n + 1) →
      (boxComplementaritySpernerCube problem p hp).G) :
    complete_simplex (boxComplementaritySpernerCube problem p hp) n vertices ↔
      simplex (boxComplementaritySpernerCube problem p hp) n vertices ∧
        Function.Injective fun index ↦
          boxComplementarityFinLabel problem p (vertices index) := by
  constructor
  · rintro ⟨hsimplex, hrange⟩
    refine ⟨hsimplex, ?_⟩
    have hsurjective : Function.Surjective (fun index ↦
        boxComplementarityFinLabel problem p (vertices index)) := by
      intro target
      have hrange' : Set.range (fun index ↦
          boxComplementarityReducedLabel problem p
            (show Fin n → Fin (p + 1) from vertices index)) =
          {label | label ≤ n} := by
        simpa only [boxComplementaritySpernerCube] using hrange
      have hmem : target.1 ∈ Set.range (fun index ↦
          boxComplementarityReducedLabel problem p
            (show Fin n → Fin (p + 1) from vertices index)) := by
        rw [hrange']
        exact Nat.le_of_lt_succ target.2
      obtain ⟨index, hindex⟩ := hmem
      exact ⟨index, Fin.ext hindex⟩
    exact ((Fintype.bijective_iff_surjective_and_card _).2
      ⟨hsurjective, rfl⟩).1
  · rintro ⟨hsimplex, hinjective⟩
    refine ⟨hsimplex, ?_⟩
    have hsurjective : Function.Surjective (fun index ↦
        boxComplementarityFinLabel problem p (vertices index)) :=
      ((Fintype.bijective_iff_injective_and_card _).2
        ⟨hinjective, rfl⟩).2
    ext label
    simp only [Set.mem_range, Set.mem_setOf_eq]
    constructor
    · rintro ⟨index, rfl⟩
      exact (boxComplementarityReducedLabel_properties
        problem p (vertices index)).1
    · intro hlabel
      let target : Fin (n + 1) := ⟨label, Nat.lt_succ_of_le hlabel⟩
      obtain ⟨index, hindex⟩ := hsurjective target
      exact ⟨index, congrArg Fin.val hindex⟩

/-- Endpoint simplices with the complete external finite label sequence. -/
def KuhnEndpointLabeledSimplex
    (problem : BoxComplementarityProblem (Fin n))
    (p : ℕ) (hp : 0 < p) :=
  {vertices : Fin (n + 1) →
      (boxComplementaritySpernerCube problem p hp).G //
    simplex (boxComplementaritySpernerCube problem p hp) n vertices ∧
      Function.Injective fun index ↦
        boxComplementarityFinLabel problem p (vertices index)}

instance kuhnEndpointLabeledSimplexFinite
    (problem : BoxComplementarityProblem (Fin n))
    (p : ℕ) (hp : 0 < p) :
    Finite (KuhnEndpointLabeledSimplex problem p hp) :=
  Finite.of_injective (fun simplex ↦ simplex.1) Subtype.val_injective

noncomputable instance kuhnEndpointLabeledSimplexFintype
    (problem : BoxComplementarityProblem (Fin n))
    (p : ℕ) (hp : 0 < p) :
    Fintype (KuhnEndpointLabeledSimplex problem p hp) :=
  Fintype.ofFinite _

/-- The bounded-label endpoint subtype is exactly the pinned library's
complete-simplex subtype. -/
def completeSimplexEquivKuhnEndpointLabeledSimplex
    (problem : BoxComplementarityProblem (Fin n))
    (p : ℕ) (hp : 0 < p) :
    {vertices : Fin (n + 1) →
        (boxComplementaritySpernerCube problem p hp).G //
      complete_simplex (boxComplementaritySpernerCube problem p hp) n vertices} ≃
      KuhnEndpointLabeledSimplex problem p hp where
  toFun vertices := ⟨vertices.1,
    (boxComplementarity_completeSimplex_iff_finLabel_injective
      problem p hp vertices.1).1 vertices.2⟩
  invFun vertices := ⟨vertices.1,
    (boxComplementarity_completeSimplex_iff_finLabel_injective
      problem p hp vertices.1).2 vertices.2⟩
  left_inv := by intro vertices; rfl
  right_inv := by intro vertices; rfl

/-- A deletion face is fully labeled when the labels of its retained vertices
are injective. -/
def kuhnDeletionFaceIsComplete
    (labels : Fin (n + 2) → Fin (n + 1)) (omitted : Fin (n + 2)) : Prop :=
  Function.Injective fun kept : Fin (n + 1) ↦ labels (omitted.succAbove kept)

/-- The concrete finite set of fully labeled deletion faces of one prism
simplex. -/
def kuhnCompleteDeletionFaces
    (labels : Fin (n + 2) → Fin (n + 1)) : Finset (Fin (n + 2)) :=
  {omitted | kuhnDeletionFaceIsComplete labels omitted}

/-- If one deletion leaves all labels distinct, there is a unique other
vertex with the omitted vertex's label. -/
private theorem exists_unique_kuhnDeletionPartner
    (labels : Fin (n + 2) → Fin (n + 1))
    (omitted : Fin (n + 2))
    (hcomplete : kuhnDeletionFaceIsComplete labels omitted) :
    ∃! partner, partner ≠ omitted ∧ labels partner = labels omitted := by
  have hbijective : Function.Bijective
      (fun kept : Fin (n + 1) ↦ labels (omitted.succAbove kept)) :=
    (Fintype.bijective_iff_injective_and_card _).2 ⟨hcomplete, rfl⟩
  obtain ⟨kept, hkept⟩ := hbijective.2 (labels omitted)
  refine ⟨omitted.succAbove kept,
    ⟨Fin.succAbove_ne omitted kept, hkept⟩, ?_⟩
  intro partner hpartner
  obtain ⟨other, hother⟩ := Fin.exists_succAbove_eq hpartner.1
  rw [← hother]
  congr 1
  apply hcomplete
  change labels (omitted.succAbove other) = labels (omitted.succAbove kept)
  rw [hother, hpartner.2]
  exact hkept.symm

/-- The collision partner of a complete deletion is itself a complete
deletion. -/
private theorem kuhnDeletionPartner_isComplete
    (labels : Fin (n + 2) → Fin (n + 1))
    (omitted partner : Fin (n + 2))
    (hcomplete : kuhnDeletionFaceIsComplete labels omitted)
    (hpartner : partner ≠ omitted ∧ labels partner = labels omitted) :
    kuhnDeletionFaceIsComplete labels partner := by
  intro first second heq
  apply Fin.succAbove_right_injective (p := partner)
  let firstVertex := partner.succAbove first
  let secondVertex := partner.succAbove second
  have first_ne_partner : firstVertex ≠ partner := Fin.succAbove_ne partner first
  have second_ne_partner : secondVertex ≠ partner := Fin.succAbove_ne partner second
  obtain ⟨canonicalPartner, hcanonicalPartner, hcanonicalUnique⟩ :=
    exists_unique_kuhnDeletionPartner labels omitted hcomplete
  have hcanonical_eq : canonicalPartner = partner :=
    (hcanonicalUnique partner hpartner).symm
  have uniquePartner (vertex : Fin (n + 2))
      (hvertex : vertex ≠ omitted ∧ labels vertex = labels omitted) :
      vertex = partner :=
    (hcanonicalUnique vertex hvertex).trans hcanonical_eq
  by_cases hfirst : firstVertex = omitted
  · have hsecond : secondVertex = omitted := by
      by_contra hsecond
      have hsecondPartner : secondVertex = partner := uniquePartner secondVertex
        ⟨hsecond, by simpa only [firstVertex, secondVertex, hfirst] using heq.symm⟩
      exact second_ne_partner hsecondPartner
    exact hfirst.trans hsecond.symm
  by_cases hsecond : secondVertex = omitted
  · have hfirstPartner : firstVertex = partner := uniquePartner firstVertex
      ⟨hfirst, by simpa only [firstVertex, secondVertex, hsecond] using heq⟩
    exact False.elim (first_ne_partner hfirstPartner)
  obtain ⟨firstKept, hfirstKept⟩ := Fin.exists_succAbove_eq hfirst
  obtain ⟨secondKept, hsecondKept⟩ := Fin.exists_succAbove_eq hsecond
  have hkept : firstKept = secondKept := hcomplete (by
    simpa only [firstVertex, secondVertex, hfirstKept, hsecondKept] using heq)
  change firstVertex = secondVertex
  rw [← hfirstKept, ← hsecondKept, hkept]

/-- Among `n + 2` vertices carrying `n + 1` labels, either no deletion is
fully labeled or exactly the two vertices in the unique collision fiber can
be deleted. -/
theorem card_kuhnCompleteDeletionFaces_eq_zero_or_two
    (labels : Fin (n + 2) → Fin (n + 1)) :
    (kuhnCompleteDeletionFaces labels).card = 0 ∨
      (kuhnCompleteDeletionFaces labels).card = 2 := by
  classical
  by_cases hexists : ∃ omitted, kuhnDeletionFaceIsComplete labels omitted
  · obtain ⟨omitted, homitted⟩ := hexists
    obtain ⟨partner, hpartner, hpartnerUnique⟩ :=
      exists_unique_kuhnDeletionPartner labels omitted homitted
    have hpartnerComplete := kuhnDeletionPartner_isComplete
      labels omitted partner homitted hpartner
    right
    have hfaces : kuhnCompleteDeletionFaces labels = {omitted, partner} := by
      ext candidate
      simp only [kuhnCompleteDeletionFaces, Finset.mem_filter,
        Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · intro hcandidate
        by_cases hcOmitted : candidate = omitted
        · exact Or.inl hcOmitted
        by_cases hcPartner : candidate = partner
        · exact Or.inr hcPartner
        exfalso
        obtain ⟨first, hfirst⟩ := Fin.exists_succAbove_eq
          (x := omitted) (y := candidate) (Ne.symm hcOmitted)
        obtain ⟨second, hsecond⟩ := Fin.exists_succAbove_eq
          (x := partner) (y := candidate) (Ne.symm hcPartner)
        have hfirstSecond : first = second := hcandidate (by
          change labels (candidate.succAbove first) =
            labels (candidate.succAbove second)
          rw [hfirst, hsecond, hpartner.2])
        exact hpartner.1 (by rw [← hfirst, ← hsecond, hfirstSecond])
      · rintro (rfl | rfl)
        · exact homitted
        · exact hpartnerComplete
    rw [hfaces]
    simp [Ne.symm hpartner.1]
  · left
    rw [Finset.card_eq_zero]
    apply Finset.not_nonempty_iff_eq_empty.mp
    rintro ⟨omitted, homitted⟩
    exact hexists ⟨omitted, by
      simpa only [kuhnCompleteDeletionFaces, Finset.mem_filter,
        Finset.mem_univ, true_and] using homitted⟩

/-- Every labeled Kuhn prism simplex has an even number of fully labeled
deletion faces. -/
theorem even_card_kuhnCompleteDeletionFaces
    (labels : Fin (n + 2) → Fin (n + 1)) :
    Even (kuhnCompleteDeletionFaces labels).card := by
  rcases card_kuhnCompleteDeletionFaces_eq_zero_or_two labels with hzero | htwo
  · rw [hzero]
    exact Even.zero
  · rw [htwo]
    exact even_two

/-! ## One elementary stellar-subdivision move -/

/-- Extend the labels on one `n`-simplex by the label of a new stellar
vertex, placed last in the finite indexing. -/
def kuhnStarSubdivisionLabels
    (labels : Fin (n + 1) → Fin (n + 1))
    (stellarLabel : Fin (n + 1)) : Fin (n + 2) → Fin (n + 1) :=
  Fin.lastCases stellarLabel labels

/-- The new top-dimensional facets in the stellar subdivision are the
complete deletion faces which retain the new last vertex. -/
def kuhnStarSubdivisionCompleteFacets
    (labels : Fin (n + 1) → Fin (n + 1))
    (stellarLabel : Fin (n + 1)) : Finset (Fin (n + 2)) :=
  (kuhnCompleteDeletionFaces
    (kuhnStarSubdivisionLabels labels stellarLabel)).erase (Fin.last (n + 1))

/-- Deleting the new stellar vertex is complete exactly when the original
simplex was completely labeled. -/
@[simp] theorem kuhnDeletionFaceIsComplete_star_last_iff
    (labels : Fin (n + 1) → Fin (n + 1))
    (stellarLabel : Fin (n + 1)) :
    kuhnDeletionFaceIsComplete
        (kuhnStarSubdivisionLabels labels stellarLabel) (Fin.last (n + 1)) ↔
      Function.Injective labels := by
  simp [kuhnDeletionFaceIsComplete, kuhnStarSubdivisionLabels,
    Fin.succAbove_last]

/-- Stellar subdivision preserves the mod-two complete-simplex count on one
labeled simplex.  This is an executable finite consequence of deletion-face
pairing and is the elementary combinatorial move needed by a future common
subdivision; it does not assert that the pinned Kuhn refinements have already
been connected by such moves. -/
theorem kuhnStarSubdivision_completeFacetParity_eq
    (labels : Fin (n + 1) → Fin (n + 1))
    (stellarLabel : Fin (n + 1)) :
    ((kuhnStarSubdivisionCompleteFacets labels stellarLabel).card : ZMod 2) =
      if Function.Injective labels then 1 else 0 := by
  classical
  let allFaces := kuhnCompleteDeletionFaces
    (kuhnStarSubdivisionLabels labels stellarLabel)
  have hallEven : Even allFaces.card :=
    even_card_kuhnCompleteDeletionFaces _
  by_cases hinjective : Function.Injective labels
  · have hlast : Fin.last (n + 1) ∈ allFaces := by
      dsimp only [allFaces]
      simp only [kuhnCompleteDeletionFaces, Finset.mem_filter,
        Finset.mem_univ, true_and]
      exact (kuhnDeletionFaceIsComplete_star_last_iff
        labels stellarLabel).2 hinjective
    have hcard :
        (kuhnStarSubdivisionCompleteFacets labels stellarLabel).card + 1 =
          allFaces.card := by
      simpa only [kuhnStarSubdivisionCompleteFacets, allFaces] using
        Finset.card_erase_add_one hlast
    obtain ⟨half, hhalf⟩ := hallEven
    have hfacetOdd : Odd
        (kuhnStarSubdivisionCompleteFacets labels stellarLabel).card := by
      refine ⟨half - 1, ?_⟩
      omega
    simp only [hinjective, if_true]
    obtain ⟨count, hcount⟩ := hfacetOdd
    rw [hcount, Nat.cast_add, Nat.cast_mul]
    change (2 : ZMod 2) * (count : ZMod 2) + 1 = 1
    rw [show (2 : ZMod 2) = 0 by exact ZMod.natCast_self 2]
    simp
  · have hlast : Fin.last (n + 1) ∉ allFaces := by
      intro hmem
      apply hinjective
      exact (kuhnDeletionFaceIsComplete_star_last_iff
        labels stellarLabel).1 (by
          simpa only [allFaces, kuhnCompleteDeletionFaces,
            Finset.mem_filter, Finset.mem_univ, true_and] using hmem)
    have hfacets :
        kuhnStarSubdivisionCompleteFacets labels stellarLabel = allFaces := by
      simp [kuhnStarSubdivisionCompleteFacets, allFaces, hlast]
    simp only [hinjective, if_false, hfacets]
    obtain ⟨half, hhalf⟩ := hallEven
    rw [hhalf, Nat.cast_add]
    change (half : ZMod 2) + half = 0
    rw [← two_mul]
    rw [show (2 : ZMod 2) = 0 by exact ZMod.natCast_self 2]
    simp

/-! ## Concrete ordered-Kuhn prism incidence -/

/-- The zero gain field, used only to obtain the pinned cube's ordered Kuhn
geometry.  Its reduced labels play no role in the external prism labeling. -/
def zeroBoxComplementarityProblem (dimension : ℕ) :
    BoxComplementarityProblem (Fin dimension) where
  gain := fun _ _ ↦ 0
  continuous_gain := by
    intro who
    fun_prop

/-- Pinned ordered-Kuhn geometry in one dimension more than the endpoint
problem. -/
def kuhnPrismGeometryCube (n resolution : ℕ) (hresolution : 0 < resolution) :
    SpernerCube :=
  boxComplementaritySpernerCube
    (zeroBoxComplementarityProblem (n + 1)) resolution hresolution

/-- Insert a fixed parameter coordinate after a spatial grid vertex. -/
def kuhnPrismEndVertex
    (resolution : ℕ) (hresolution : 0 < resolution)
    (parameter : Fin (resolution + 1))
    (vertex : Fin n → Fin (resolution + 1)) :
    (kuhnPrismGeometryCube n resolution hresolution).G :=
  Fin.lastCases parameter vertex

@[simp] theorem kuhnPrismEndVertex_castSucc
    (resolution : ℕ) (hresolution : 0 < resolution)
    (parameter : Fin (resolution + 1))
    (vertex : Fin n → Fin (resolution + 1)) (who : Fin n) :
    kuhnPrismEndVertex resolution hresolution parameter vertex who.castSucc =
      vertex who := by
  simp [kuhnPrismEndVertex]

@[simp] theorem kuhnPrismEndVertex_last
    (resolution : ℕ) (hresolution : 0 < resolution)
    (parameter : Fin (resolution + 1))
    (vertex : Fin n → Fin (resolution + 1)) :
    kuhnPrismEndVertex resolution hresolution parameter vertex (Fin.last n) =
      parameter := by
  simp [kuhnPrismEndVertex]

@[simp] theorem finInit_kuhnPrismEndVertex
    (resolution : ℕ) (hresolution : 0 < resolution)
    (parameter : Fin (resolution + 1))
    (vertex : Fin n → Fin (resolution + 1)) :
    Fin.init (kuhnPrismEndVertex resolution hresolution parameter vertex) =
      vertex := by
  funext who
  exact kuhnPrismEndVertex_castSucc resolution hresolution parameter vertex who

/-- Lifting every vertex to one fixed parameter end preserves the pinned
ordered-Kuhn simplex relation. -/
theorem simplex_kuhnPrismEndVertex
    (problem : BoxComplementarityProblem (Fin n))
    (resolution : ℕ) (hresolution : 0 < resolution)
    (parameter : Fin (resolution + 1))
    (vertices : Fin (n + 1) →
      (boxComplementaritySpernerCube problem resolution hresolution).G)
    (hsimplex : simplex
      (boxComplementaritySpernerCube problem resolution hresolution)
        n vertices) :
    simplex (kuhnPrismGeometryCube n resolution hresolution) n
      (fun index ↦ kuhnPrismEndVertex resolution hresolution parameter
        (show Fin n → Fin (resolution + 1) from vertices index)) := by
  constructor
  · intro first second heq
    apply hsimplex.1
    have hspatial := congrArg Fin.init heq
    simp only [finInit_kuhnPrismEndVertex] at hspatial
    simpa only [SpernerCube.G, boxComplementaritySpernerCube,
      kuhnPrismGeometryCube] using hspatial
  · intro index hindex coordinate
    refine Fin.lastCases ?_ (fun who ↦ ?_) coordinate
    · simp only [kuhnPrismEndVertex_last]
      exact ⟨le_rfl, by omega⟩
    · simpa only [kuhnPrismEndVertex_castSucc] using
        hsimplex.2 index hindex who

/-- Projecting an end face to its spatial coordinates preserves the pinned
ordered-Kuhn simplex relation. -/
theorem simplex_finInit_of_kuhnPrismEnd
    (problem : BoxComplementarityProblem (Fin n))
    (resolution : ℕ) (hresolution : 0 < resolution)
    (parameter : Fin (resolution + 1))
    (vertices : Fin (n + 1) →
      (kuhnPrismGeometryCube n resolution hresolution).G)
    (hsimplex : simplex (kuhnPrismGeometryCube n resolution hresolution)
      n vertices)
    (hend : ∀ index, vertices index (Fin.last n) = parameter) :
    simplex (boxComplementaritySpernerCube problem resolution hresolution) n
      (fun index ↦ Fin.init (vertices index)) := by
  constructor
  · intro first second heq
    apply hsimplex.1
    funext coordinate
    refine Fin.lastCases ?_ (fun who ↦ ?_) coordinate
    · exact (hend first).trans (hend second).symm
    · exact congrFun heq who
  · intro index hindex who
    have hcoordinate := hsimplex.2 index hindex who.castSucc
    constructor
    · exact hcoordinate.1
    · exact hcoordinate.2

/-- A top-dimensional ordered Kuhn simplex in the parameter-times-cube grid. -/
def KuhnPrismCell (n resolution : ℕ) (hresolution : 0 < resolution) :=
  {vertices : Fin (n + 2) →
      (kuhnPrismGeometryCube n resolution hresolution).G //
    simplex (kuhnPrismGeometryCube n resolution hresolution) (n + 1) vertices}

/-- A fully externally labeled codimension-one Kuhn face. -/
def KuhnPrismFace (n resolution : ℕ) (hresolution : 0 < resolution)
    (label : (kuhnPrismGeometryCube n resolution hresolution).G → Fin (n + 1)) :=
  {vertices : Fin (n + 1) →
      (kuhnPrismGeometryCube n resolution hresolution).G //
    simplex (kuhnPrismGeometryCube n resolution hresolution) n vertices ∧
      Function.Injective fun index ↦ label (vertices index)}

instance kuhnPrismCellFinite
    (n resolution : ℕ) (hresolution : 0 < resolution) :
    Finite (KuhnPrismCell n resolution hresolution) :=
  Finite.of_injective (fun cell ↦ cell.1) Subtype.val_injective

noncomputable instance kuhnPrismCellFintype
    (n resolution : ℕ) (hresolution : 0 < resolution) :
    Fintype (KuhnPrismCell n resolution hresolution) :=
  Fintype.ofFinite _

instance kuhnPrismFaceFinite
    (n resolution : ℕ) (hresolution : 0 < resolution)
    (label : (kuhnPrismGeometryCube n resolution hresolution).G → Fin (n + 1)) :
    Finite (KuhnPrismFace n resolution hresolution label) :=
  Finite.of_injective (fun face ↦ face.1) Subtype.val_injective

noncomputable instance kuhnPrismFaceFintype
    (n resolution : ℕ) (hresolution : 0 < resolution)
    (label : (kuhnPrismGeometryCube n resolution hresolution).G → Fin (n + 1)) :
    Fintype (KuhnPrismFace n resolution hresolution label) :=
  Fintype.ofFinite _

/-- A face is incident to a cell when its vertices form a pinned Kuhn face of
that cell. -/
def kuhnPrismIncident
    {resolution : ℕ} {hresolution : 0 < resolution}
    {label : (kuhnPrismGeometryCube n resolution hresolution).G → Fin (n + 1)}
    (cell : KuhnPrismCell n resolution hresolution)
    (face : KuhnPrismFace n resolution hresolution label) : Prop :=
  is_face (kuhnPrismGeometryCube n resolution hresolution) face.1 cell.1

/-- The external label sequence around one concrete prism cell. -/
def kuhnPrismCellLabels
    {resolution : ℕ} {hresolution : 0 < resolution}
    (label : (kuhnPrismGeometryCube n resolution hresolution).G → Fin (n + 1))
    (cell : KuhnPrismCell n resolution hresolution) :
    Fin (n + 2) → Fin (n + 1) :=
  fun index ↦ label (cell.1 index)

/-- On the concrete prism cube, the pinned library's deletion embedding is
the standard `Fin.succAbove` embedding used by the finite deletion count. -/
theorem kuhnPrism_insertIndex_eq_succAbove
    {resolution : ℕ} {hresolution : 0 < resolution}
    (omitted : Fin (n + 2)) (kept : Fin (n + 1)) :
    @insert_index (kuhnPrismGeometryCube n resolution hresolution) n rfl
        omitted kept =
      omitted.succAbove kept := by
  apply Fin.ext
  by_cases hlt : kept.castSucc < omitted
  · have hval : kept.val < omitted.val := hlt
    simp [insert_index, Fin.succAbove, hlt, hval]
  · have hval : ¬kept.val < omitted.val := hlt
    simp [insert_index, Fin.succAbove, hlt, hval]

/-- Delete one vertex of a prism cell when the remaining external labels are
complete. -/
def KuhnPrismCell.deletionFace
    {resolution : ℕ} {hresolution : 0 < resolution}
    (label : (kuhnPrismGeometryCube n resolution hresolution).G → Fin (n + 1))
    (cell : KuhnPrismCell n resolution hresolution)
    (omitted : {index : Fin (n + 2) //
      kuhnDeletionFaceIsComplete (kuhnPrismCellLabels label cell) index}) :
    KuhnPrismFace n resolution hresolution label where
  val := @delete_vertex (kuhnPrismGeometryCube n resolution hresolution) n rfl
    omitted.1 cell.1
  property := by
    constructor
    · exact @delete_vertex_simplex
        (kuhnPrismGeometryCube n resolution hresolution) n rfl cell.1
          cell.2 omitted.1
    · intro first second heq
      apply omitted.2
      simpa only [kuhnPrismCellLabels, delete_vertex,
        kuhnPrism_insertIndex_eq_succAbove] using heq

/-- A deletion face is incident to its originating prism cell. -/
theorem KuhnPrismCell.deletionFace_incident
    {resolution : ℕ} {hresolution : 0 < resolution}
    (label : (kuhnPrismGeometryCube n resolution hresolution).G → Fin (n + 1))
    (cell : KuhnPrismCell n resolution hresolution)
    (omitted : {index : Fin (n + 2) //
      kuhnDeletionFaceIsComplete (kuhnPrismCellLabels label cell) index}) :
    kuhnPrismIncident cell (cell.deletionFace label omitted) := by
  exact delete_vertex_is_face
    (kuhnPrismGeometryCube n resolution hresolution) cell.1
      (hs := cell.2) omitted.1

/-- Complete deletions of one prism cell are exactly its incident externally
complete faces. -/
def KuhnPrismCell.completeDeletionEquivIncidentFace
    {resolution : ℕ} {hresolution : 0 < resolution}
    (label : (kuhnPrismGeometryCube n resolution hresolution).G → Fin (n + 1))
    (cell : KuhnPrismCell n resolution hresolution) :
    {index : Fin (n + 2) //
        kuhnDeletionFaceIsComplete (kuhnPrismCellLabels label cell) index} ≃
      {face : KuhnPrismFace n resolution hresolution label //
        kuhnPrismIncident cell face} := by
  let forward : {index : Fin (n + 2) //
      kuhnDeletionFaceIsComplete (kuhnPrismCellLabels label cell) index} →
      {face : KuhnPrismFace n resolution hresolution label //
        kuhnPrismIncident cell face} :=
    fun omitted ↦ ⟨cell.deletionFace label omitted,
      cell.deletionFace_incident label omitted⟩
  refine Equiv.ofBijective forward ⟨?_, ?_⟩
  · intro first second heq
    apply Subtype.ext
    apply delete_vertex_inj
      (kuhnPrismGeometryCube n resolution hresolution) cell.1
        (hs := cell.2)
    exact congrArg (fun face ↦ face.1.1) heq
  · rintro ⟨face, hface⟩
    obtain ⟨omitted, homitted⟩ :=
      (@child_simplex_char
        (kuhnPrismGeometryCube n resolution hresolution) n rfl face.1 cell.1
          cell.2).mp hface
    have hcomplete : kuhnDeletionFaceIsComplete
        (kuhnPrismCellLabels label cell) omitted := by
      intro first second heq
      apply face.2.2
      simpa only [homitted, kuhnPrismCellLabels, delete_vertex,
        kuhnPrism_insertIndex_eq_succAbove] using heq
    let selected : {index : Fin (n + 2) //
        kuhnDeletionFaceIsComplete (kuhnPrismCellLabels label cell) index} :=
      ⟨omitted, hcomplete⟩
    refine ⟨selected, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact homitted.symm

/-- Every concrete prism cell has even indexed external boundary degree.  The
later subdivision constructor only has to identify equal deletion faces
across neighboring cells and classify the unpaired geometric boundary. -/
theorem KuhnPrismCell.even_indexedBoundaryDegree
    {resolution : ℕ} {hresolution : 0 < resolution}
    (label : (kuhnPrismGeometryCube n resolution hresolution).G → Fin (n + 1))
    (cell : KuhnPrismCell n resolution hresolution) :
    Even (kuhnCompleteDeletionFaces (kuhnPrismCellLabels label cell)).card :=
  even_card_kuhnCompleteDeletionFaces _

/-- The indexed deletion parity is the actual parity of incident externally
complete faces. -/
theorem KuhnPrismCell.even_incidentFaceDegree
    {resolution : ℕ} {hresolution : 0 < resolution}
    (label : (kuhnPrismGeometryCube n resolution hresolution).G → Fin (n + 1))
    (cell : KuhnPrismCell n resolution hresolution) :
    Even (Finset.univ.filter fun face :
      KuhnPrismFace n resolution hresolution label ↦
        kuhnPrismIncident cell face).card := by
  classical
  let deletionPredicate : Fin (n + 2) → Prop := fun index ↦
    kuhnDeletionFaceIsComplete (kuhnPrismCellLabels label cell) index
  let incidentPredicate : KuhnPrismFace n resolution hresolution label → Prop :=
    fun face ↦ kuhnPrismIncident cell face
  have hdeletionCard : Fintype.card {index // deletionPredicate index} =
      (Finset.univ.filter deletionPredicate).card :=
    Fintype.card_ofFinset (Finset.univ.filter deletionPredicate) (by
      intro index
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        deletionPredicate]
      rfl)
  have hincidentCard : Fintype.card {face // incidentPredicate face} =
      (Finset.univ.filter incidentPredicate).card :=
    Fintype.card_ofFinset (Finset.univ.filter incidentPredicate) (by
      intro face
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        incidentPredicate]
      rfl)
  have hequivalentCard :
      Fintype.card {index // deletionPredicate index} =
        Fintype.card {face // incidentPredicate face} := by
    simpa only [deletionPredicate, incidentPredicate] using
      Fintype.card_congr (cell.completeDeletionEquivIncidentFace label)
  rw [← hincidentCard, ← hequivalentCard, hdeletionCard]
  exact even_card_kuhnCompleteDeletionFaces _

/-- Incident prism cells are definitionally the pinned Kuhn parents of a
fixed face; the subtype wrapper retains each parent's simplex proof. -/
def KuhnPrismFace.incidentCellEquivParent
    {resolution : ℕ} {hresolution : 0 < resolution}
    {label : (kuhnPrismGeometryCube n resolution hresolution).G → Fin (n + 1)}
    (face : KuhnPrismFace n resolution hresolution label) :
    {cell : KuhnPrismCell n resolution hresolution //
        kuhnPrismIncident cell face} ≃
      {vertices : Fin (n + 2) →
          (kuhnPrismGeometryCube n resolution hresolution).G //
        is_face (kuhnPrismGeometryCube n resolution hresolution)
          face.1 vertices} where
  toFun cell := ⟨cell.1.1, cell.2⟩
  invFun parent := ⟨⟨parent.1, parent.2.2.1⟩, parent.2⟩
  left_inv := by rintro ⟨⟨vertices, hvertices⟩, hincident⟩; rfl
  right_inv := by rintro ⟨vertices, hincident⟩; rfl

/-- Actual incident-cell cardinality is the pinned parent cardinality. -/
theorem KuhnPrismFace.incidentCell_card_eq_parent_card
    {resolution : ℕ} {hresolution : 0 < resolution}
    {label : (kuhnPrismGeometryCube n resolution hresolution).G → Fin (n + 1)}
    (face : KuhnPrismFace n resolution hresolution label) :
    (Finset.univ.filter fun cell : KuhnPrismCell n resolution hresolution ↦
        kuhnPrismIncident cell face).card =
      (Finset.univ.filter fun vertices : Fin (n + 2) →
          (kuhnPrismGeometryCube n resolution hresolution).G ↦
        is_face (kuhnPrismGeometryCube n resolution hresolution)
          face.1 vertices).card := by
  classical
  let incidentPredicate : KuhnPrismCell n resolution hresolution → Prop :=
    fun cell ↦ kuhnPrismIncident cell face
  let parentPredicate :
      (Fin (n + 2) → (kuhnPrismGeometryCube n resolution hresolution).G) →
        Prop :=
    fun vertices ↦ is_face (kuhnPrismGeometryCube n resolution hresolution)
      face.1 vertices
  have hincidentCard : Fintype.card {cell // incidentPredicate cell} =
      (Finset.univ.filter incidentPredicate).card :=
    Fintype.card_ofFinset (Finset.univ.filter incidentPredicate) (by
      intro cell
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        incidentPredicate]
      rfl)
  have hparentCard : Fintype.card {vertices // parentPredicate vertices} =
      (Finset.univ.filter parentPredicate).card :=
    Fintype.card_ofFinset (Finset.univ.filter parentPredicate) (by
      intro vertices
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        parentPredicate]
      rfl)
  have hequivalentCard : Fintype.card {cell // incidentPredicate cell} =
      Fintype.card {vertices // parentPredicate vertices} := by
    change Fintype.card {cell // kuhnPrismIncident cell face} =
      Fintype.card {vertices //
        is_face (kuhnPrismGeometryCube n resolution hresolution)
          face.1 vertices}
    exact Fintype.card_congr face.incidentCellEquivParent
  rw [← hincidentCard, hequivalentCard, hparentCard]

/-- A concrete face lies on the left parameter end. -/
def KuhnPrismFace.IsLeftEnd
    {resolution : ℕ} {hresolution : 0 < resolution}
    {label : (kuhnPrismGeometryCube n resolution hresolution).G → Fin (n + 1)}
    (face : KuhnPrismFace n resolution hresolution label) : Prop :=
  ∀ index, face.1 index (Fin.last n) = 0

/-- A concrete face lies on the right parameter end. -/
def KuhnPrismFace.IsRightEnd
    {resolution : ℕ} {hresolution : 0 < resolution}
    {label : (kuhnPrismGeometryCube n resolution hresolution).G → Fin (n + 1)}
    (face : KuhnPrismFace n resolution hresolution label) : Prop :=
  ∀ index, (face.1 index (Fin.last n)).1 = resolution

/-- A concrete face lies on a spatial side of the parameter-times-cube. -/
def KuhnPrismFace.IsLateral
    {resolution : ℕ} {hresolution : 0 < resolution}
    {label : (kuhnPrismGeometryCube n resolution hresolution).G → Fin (n + 1)}
    (face : KuhnPrismFace n resolution hresolution label) : Prop :=
  ∃ who : Fin n,
    (∀ index, face.1 index who.castSucc = 0) ∨
      (∀ index, (face.1 index who.castSucc).1 = resolution)

/-- A concrete face is geometric boundary exactly when it has a unique Kuhn
parent cell. -/
def KuhnPrismFace.IsGeometricBoundary
    {resolution : ℕ} {hresolution : 0 < resolution}
    {label : (kuhnPrismGeometryCube n resolution hresolution).G → Fin (n + 1)}
    (face : KuhnPrismFace n resolution hresolution label) : Prop :=
    is_boundary_face (kuhnPrismGeometryCube n resolution hresolution) face.1

/-- A concrete fully labeled face has odd incidence degree exactly on the
geometric boundary of the parameter-times-cube. -/
theorem KuhnPrismFace.odd_incidentCellDegree_iff_isGeometricBoundary
    {resolution : ℕ} {hresolution : 0 < resolution}
    {label : (kuhnPrismGeometryCube n resolution hresolution).G → Fin (n + 1)}
    (face : KuhnPrismFace n resolution hresolution label) :
    Odd (Finset.univ.filter fun cell :
        KuhnPrismCell n resolution hresolution ↦
          kuhnPrismIncident cell face).card ↔
      face.IsGeometricBoundary := by
  classical
  rw [face.incidentCell_card_eq_parent_card]
  let parents := Finset.univ.filter fun vertices : Fin (n + 2) →
      (kuhnPrismGeometryCube n resolution hresolution).G ↦
        is_face (kuhnPrismGeometryCube n resolution hresolution)
          face.1 vertices
  have hcount : parents.card = 1 ∨ parents.card = 2 := by
    have hparents := @parent_count
      (kuhnPrismGeometryCube n resolution hresolution)
        n rfl face.1 face.2.1
    change parents.card ∈ {count | count = 1 ∨ count = 2} at hparents
    simpa only [Set.mem_setOf_eq] using hparents
  have hboundary : face.IsGeometricBoundary ↔ parents.card = 1 := by
    rw [KuhnPrismFace.IsGeometricBoundary, is_boundary_face,
      Fintype.existsUnique_iff_card_one]
    rfl
  rw [hboundary]
  constructor
  · intro hodd
    rcases hcount with hone | htwo
    · exact hone
    · rw [htwo] at hodd
      exact (Nat.not_odd_iff_even.mpr even_two hodd).elim
  · intro hone
    rw [hone]
    exact odd_one

/-- An external prism labeling has the spatial boundary conditions inherited
from the reduced box-complementarity label.  No condition is imposed at the
two parameter ends. -/
structure KuhnPrismSpatialBoundaryLabeling
    (n resolution : ℕ) (hresolution : 0 < resolution) where
  label : (kuhnPrismGeometryCube n resolution hresolution).G → Fin (n + 1)
  label_ne_of_spatial_eq_zero : ∀ vertex (who : Fin n),
    vertex who.castSucc = 0 → label vertex ≠ who.castSucc
  label_le_of_spatial_eq_top : ∀ vertex (who : Fin n),
    (vertex who.castSucc).1 = resolution → label vertex ≤ who.castSucc

/-- A fully externally labeled face cannot lie on a spatial side of the
prism.  Thus every odd geometric boundary face, once incidence is constructed,
must lie on one of the two parameter ends. -/
theorem KuhnPrismSpatialBoundaryLabeling.not_face_isLateral
    {resolution : ℕ} {hresolution : 0 < resolution}
    (boundary : KuhnPrismSpatialBoundaryLabeling n resolution hresolution)
    (face : KuhnPrismFace n resolution hresolution boundary.label) :
    ¬face.IsLateral := by
  rintro ⟨who, hlower | hupper⟩
  · have hbijective : Function.Bijective
        (fun index ↦ boundary.label (face.1 index)) :=
      (Fintype.bijective_iff_injective_and_card _).2 ⟨face.2.2, rfl⟩
    obtain ⟨index, hindex⟩ := hbijective.2 who.castSucc
    exact boundary.label_ne_of_spatial_eq_zero
      (face.1 index) who (hlower index) hindex
  · have hbijective : Function.Bijective
        (fun index ↦ boundary.label (face.1 index)) :=
      (Fintype.bijective_iff_injective_and_card _).2 ⟨face.2.2, rfl⟩
    obtain ⟨index, hindex⟩ := hbijective.2 (Fin.last n)
    have hle := boundary.label_le_of_spatial_eq_top
      (face.1 index) who (hupper index)
    change boundary.label (face.1 index) = Fin.last n at hindex
    rw [hindex] at hle
    exact (Nat.not_le_of_lt who.2) hle

/-- Under the spatial boundary signs, the only geometric boundary faces with
all external labels are the two parameter ends. -/
theorem KuhnPrismSpatialBoundaryLabeling.isGeometricBoundary_iff
    {resolution : ℕ} {hresolution : 0 < resolution}
    (boundary : KuhnPrismSpatialBoundaryLabeling n resolution hresolution)
    (face : KuhnPrismFace n resolution hresolution boundary.label) :
    face.IsGeometricBoundary ↔ face.IsLeftEnd ∨ face.IsRightEnd := by
  constructor
  · intro hboundary
    rcases @boundary_is_A_or_B
      (kuhnPrismGeometryCube n resolution hresolution) n rfl face.1 hboundary with
      hleft | hright
    · obtain ⟨coordinate, hcoordinate⟩ := hleft
      by_cases hparameter : coordinate = Fin.last n
      · left
        subst coordinate
        exact hcoordinate
      · obtain ⟨who, hwho⟩ := Fin.exists_castSucc_eq.mpr hparameter
        exfalso
        apply boundary.not_face_isLateral face
        exact ⟨who, Or.inl (by simpa only [hwho] using hcoordinate)⟩
    · obtain ⟨coordinate, hcoordinate⟩ := hright
      by_cases hparameter : coordinate = Fin.last n
      · right
        subst coordinate
        intro index
        have hvalue := congrArg Fin.val (hcoordinate index)
        simpa [kuhnPrismGeometryCube, boxComplementaritySpernerCube] using hvalue
      · obtain ⟨who, hwho⟩ := Fin.exists_castSucc_eq.mpr hparameter
        exfalso
        apply boundary.not_face_isLateral face
        refine ⟨who, Or.inr ?_⟩
        intro index
        have hvalue := congrArg Fin.val (hcoordinate index)
        simpa [hwho, kuhnPrismGeometryCube, boxComplementaritySpernerCube] using
          hvalue
  · rintro (hleft | hright)
    · rw [KuhnPrismFace.IsGeometricBoundary, is_boundary_face,
        Fintype.existsUnique_iff_card_one]
      exact @case_A_parent_count
        (kuhnPrismGeometryCube n resolution hresolution) n rfl face.1
          face.2.1 ⟨Fin.last n, hleft⟩
    · exact @case_B_boundary
        (kuhnPrismGeometryCube n resolution hresolution) n rfl face.1
          face.2.1 ⟨Fin.last n, fun index ↦ Fin.ext (hright index)⟩

/-- Finite double counting on the concrete ordered-Kuhn prism equates the
mod-two counts of fully labeled faces at its two parameter ends. -/
theorem KuhnPrismSpatialBoundaryLabeling.leftEndParity_eq_rightEndParity
    {resolution : ℕ} {hresolution : 0 < resolution}
    (boundary : KuhnPrismSpatialBoundaryLabeling n resolution hresolution) :
    ((Finset.univ.filter fun face :
        KuhnPrismFace n resolution hresolution boundary.label ↦
          face.IsLeftEnd).card : ZMod 2) =
      ((Finset.univ.filter fun face :
        KuhnPrismFace n resolution hresolution boundary.label ↦
          face.IsRightEnd).card : ZMod 2) := by
  apply relativeCubicalPrism_boundaryParity_eq
    (fun cell face ↦ kuhnPrismIncident cell face)
    KuhnPrismFace.IsLeftEnd KuhnPrismFace.IsRightEnd
  · intro face hboth
    have hleft := congrArg Fin.val (hboth.1 0)
    have hright := hboth.2 0
    simp only [Fin.val_zero] at hleft
    rw [hleft] at hright
    exact (Nat.ne_of_gt hresolution) hright.symm
  · intro cell
    exact cell.even_incidentFaceDegree boundary.label
  · intro face
    rw [face.odd_incidentCellDegree_iff_isGeometricBoundary,
      boundary.isGeometricBoundary_iff face]

/-- The external prism label associated with a discrete family of
box-complementarity problems on one common grid.  The parameter is the last
grid coordinate; the spatial reduced label is coerced to `Fin (n + 1)`. -/
def boxComplementarityDiscretePrismBoundaryLabeling
    (resolution : ℕ) (hresolution : 0 < resolution)
    (family : Fin (resolution + 1) → BoxComplementarityProblem (Fin n)) :
    KuhnPrismSpatialBoundaryLabeling n resolution hresolution where
  label := fun vertex ↦
    let spatial := Fin.init vertex
    let reduced := boxComplementarityReducedLabel
      (family (vertex (Fin.last n))) resolution spatial
    ⟨reduced, Nat.lt_succ_of_le
      (boxComplementarityReducedLabel_properties
        (family (vertex (Fin.last n))) resolution spatial).1⟩
  label_ne_of_spatial_eq_zero := by
    intro vertex who hzero heq
    have hreduced := boxComplementarityReducedLabel_ne_of_eq_zero
      (family (vertex (Fin.last n))) resolution (Fin.init vertex) who
      (by
        change vertex who.castSucc = 0
        exact hzero)
    apply hreduced
    exact congrArg Fin.val heq
  label_le_of_spatial_eq_top := by
    intro vertex who htop
    apply Fin.val_fin_le.mpr
    exact boxComplementarityReducedLabel_le_of_eq_last
      (family (vertex (Fin.last n))) resolution hresolution
      (Fin.init vertex) who (by
        change (vertex who.castSucc).1 = resolution
        exact htop)

/-- At a fixed parameter slice, the discrete-prism label is exactly the
bounded endpoint label of the corresponding problem. -/
@[simp] theorem boxComplementarityDiscretePrismBoundaryLabeling_endVertex
    (resolution : ℕ) (hresolution : 0 < resolution)
    (family : Fin (resolution + 1) → BoxComplementarityProblem (Fin n))
    (parameter : Fin (resolution + 1))
    (vertex : Fin n → Fin (resolution + 1)) :
    (boxComplementarityDiscretePrismBoundaryLabeling
      resolution hresolution family).label
        (kuhnPrismEndVertex resolution hresolution parameter vertex) =
      boxComplementarityFinLabel (family parameter) resolution vertex := by
  apply Fin.ext
  simp [boxComplementarityDiscretePrismBoundaryLabeling,
    boxComplementarityFinLabel]

/-- The same slice identification for a prism vertex presented without the
canonical `kuhnPrismEndVertex` constructor. -/
theorem boxComplementarityDiscretePrismBoundaryLabeling_eq_finLabel_of_last_eq
    (resolution : ℕ) (hresolution : 0 < resolution)
    (family : Fin (resolution + 1) → BoxComplementarityProblem (Fin n))
    (parameter : Fin (resolution + 1))
    (vertex : (kuhnPrismGeometryCube n resolution hresolution).G)
    (hlast : vertex (Fin.last n) = parameter) :
    (boxComplementarityDiscretePrismBoundaryLabeling
      resolution hresolution family).label vertex =
      boxComplementarityFinLabel (family parameter) resolution
        (Fin.init vertex) := by
  apply Fin.ext
  simp [boxComplementarityDiscretePrismBoundaryLabeling,
    boxComplementarityFinLabel, hlast]

/-- Fully labeled faces on any fixed parameter slice are exactly the pinned
fully labeled endpoint simplices for the problem at that parameter. -/
def boxComplementarityDiscretePrismParameterEndEquiv
    (resolution : ℕ) (hresolution : 0 < resolution)
    (family : Fin (resolution + 1) → BoxComplementarityProblem (Fin n))
    (parameter : Fin (resolution + 1)) :
    {face : KuhnPrismFace n resolution hresolution
        (boxComplementarityDiscretePrismBoundaryLabeling
          resolution hresolution family).label //
      ∀ index, face.1 index (Fin.last n) = parameter} ≃
      KuhnEndpointLabeledSimplex (family parameter) resolution hresolution where
  toFun face := by
    refine ⟨fun index ↦ Fin.init (face.1.1 index), ?_, ?_⟩
    · exact simplex_finInit_of_kuhnPrismEnd
        (family parameter) resolution hresolution parameter face.1.1
          face.1.2.1 face.2
    · intro first second heq
      apply face.1.2.2
      change boxComplementarityFinLabel (family parameter) resolution
          (Fin.init (face.1.1 first)) =
        boxComplementarityFinLabel (family parameter) resolution
          (Fin.init (face.1.1 second)) at heq
      change (boxComplementarityDiscretePrismBoundaryLabeling
          resolution hresolution family).label (face.1.1 first) =
        (boxComplementarityDiscretePrismBoundaryLabeling
          resolution hresolution family).label (face.1.1 second)
      rw [boxComplementarityDiscretePrismBoundaryLabeling_eq_finLabel_of_last_eq
          resolution hresolution family parameter (face.1.1 first)
            (face.2 first),
        boxComplementarityDiscretePrismBoundaryLabeling_eq_finLabel_of_last_eq
          resolution hresolution family parameter (face.1.1 second)
            (face.2 second)]
      exact heq
  invFun endpoint := by
    refine ⟨⟨fun index ↦ kuhnPrismEndVertex resolution hresolution parameter
        (endpoint.1 index), ?_, ?_⟩, ?_⟩
    · exact simplex_kuhnPrismEndVertex
        (family parameter) resolution hresolution parameter endpoint.1
          endpoint.2.1
    · intro first second heq
      apply endpoint.2.2
      simpa only [boxComplementarityDiscretePrismBoundaryLabeling_endVertex]
        using heq
    · intro index
      exact kuhnPrismEndVertex_last
        resolution hresolution parameter (endpoint.1 index)
  left_inv := by
    intro face
    apply Subtype.ext
    apply Subtype.ext
    funext index coordinate
    refine Fin.lastCases ?_ (fun who ↦ ?_) coordinate
    · simpa only [kuhnPrismEndVertex_last] using (face.2 index).symm
    · simp only [kuhnPrismEndVertex_castSucc, Fin.init]
  right_inv := by
    intro endpoint
    apply Subtype.ext
    funext index who
    exact kuhnPrismEndVertex_castSucc
      resolution hresolution parameter (endpoint.1 index) who

/-- The left parameter-end faces are the endpoint simplices of the first
problem in the discrete family. -/
def boxComplementarityDiscretePrismLeftEndEquiv
    (resolution : ℕ) (hresolution : 0 < resolution)
    (family : Fin (resolution + 1) → BoxComplementarityProblem (Fin n)) :
    {face : KuhnPrismFace n resolution hresolution
        (boxComplementarityDiscretePrismBoundaryLabeling
          resolution hresolution family).label // face.IsLeftEnd} ≃
      KuhnEndpointLabeledSimplex (family 0) resolution hresolution :=
  boxComplementarityDiscretePrismParameterEndEquiv
    resolution hresolution family 0

/-- The right parameter-end faces are the endpoint simplices of the last
problem in the discrete family. -/
def boxComplementarityDiscretePrismRightEndEquiv
    (resolution : ℕ) (hresolution : 0 < resolution)
    (family : Fin (resolution + 1) → BoxComplementarityProblem (Fin n)) :
    {face : KuhnPrismFace n resolution hresolution
        (boxComplementarityDiscretePrismBoundaryLabeling
          resolution hresolution family).label // face.IsRightEnd} ≃
      KuhnEndpointLabeledSimplex
        (family (Fin.last resolution)) resolution hresolution :=
  (Equiv.subtypeEquivProp (by
      funext face
      apply propext
      constructor
      · intro hright index
        apply Fin.ext
        exact hright index
      · intro hparameter index
        exact congrArg Fin.val (hparameter index))).trans
    (boxComplementarityDiscretePrismParameterEndEquiv
      resolution hresolution family (Fin.last resolution))

/-- The concrete left-end face count is literally the first endpoint's
complete-simplex count. -/
theorem card_boxComplementarityDiscretePrism_leftEnd_eq
    (resolution : ℕ) (hresolution : 0 < resolution)
    (family : Fin (resolution + 1) → BoxComplementarityProblem (Fin n)) :
    (Finset.univ.filter fun face : KuhnPrismFace n resolution hresolution
        (boxComplementarityDiscretePrismBoundaryLabeling
          resolution hresolution family).label ↦ face.IsLeftEnd).card =
      Fintype.card
        (KuhnEndpointLabeledSimplex (family 0) resolution hresolution) := by
  classical
  let predicate : KuhnPrismFace n resolution hresolution
      (boxComplementarityDiscretePrismBoundaryLabeling
        resolution hresolution family).label → Prop :=
    fun face ↦ face.IsLeftEnd
  have hsubtype : Fintype.card {face // predicate face} =
      (Finset.univ.filter predicate).card :=
    Fintype.card_ofFinset (Finset.univ.filter predicate) (by
      intro face
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rfl)
  rw [← hsubtype]
  exact Fintype.card_congr
    (boxComplementarityDiscretePrismLeftEndEquiv
      resolution hresolution family)

/-- The concrete right-end face count is literally the last endpoint's
complete-simplex count. -/
theorem card_boxComplementarityDiscretePrism_rightEnd_eq
    (resolution : ℕ) (hresolution : 0 < resolution)
    (family : Fin (resolution + 1) → BoxComplementarityProblem (Fin n)) :
    (Finset.univ.filter fun face : KuhnPrismFace n resolution hresolution
        (boxComplementarityDiscretePrismBoundaryLabeling
          resolution hresolution family).label ↦ face.IsRightEnd).card =
      Fintype.card (KuhnEndpointLabeledSimplex
        (family (Fin.last resolution)) resolution hresolution) := by
  classical
  let predicate : KuhnPrismFace n resolution hresolution
      (boxComplementarityDiscretePrismBoundaryLabeling
        resolution hresolution family).label → Prop :=
    fun face ↦ face.IsRightEnd
  have hsubtype : Fintype.card {face // predicate face} =
      (Finset.univ.filter predicate).card :=
    Fintype.card_ofFinset (Finset.univ.filter predicate) (by
      intro face
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rfl)
  rw [← hsubtype]
  exact Fintype.card_congr
    (boxComplementarityDiscretePrismRightEndEquiv
      resolution hresolution family)

/-- A discrete family on one common grid has equal mod-two complete-simplex
counts at its first and last parameter slices.  This is a literal consequence
of the constructed prism incidence; it is not cross-resolution subdivision
invariance. -/
theorem boxComplementarityDiscretePrism_endpointParity_eq
    (resolution : ℕ) (hresolution : 0 < resolution)
    (family : Fin (resolution + 1) → BoxComplementarityProblem (Fin n)) :
    (Fintype.card
        (KuhnEndpointLabeledSimplex (family 0) resolution hresolution) :
      ZMod 2) =
      (Fintype.card (KuhnEndpointLabeledSimplex
        (family (Fin.last resolution)) resolution hresolution) : ZMod 2) := by
  rw [← card_boxComplementarityDiscretePrism_leftEnd_eq,
    ← card_boxComplementarityDiscretePrism_rightEnd_eq]
  exact
    (boxComplementarityDiscretePrismBoundaryLabeling
      resolution hresolution family).leftEndParity_eq_rightEndParity

/-- The concrete discrete complementarity prism has no fully labeled lateral
face. -/
theorem not_face_isLateral_boxComplementarityDiscretePrism
    (resolution : ℕ) (hresolution : 0 < resolution)
    (family : Fin (resolution + 1) → BoxComplementarityProblem (Fin n))
    (face : KuhnPrismFace n resolution hresolution
      (boxComplementarityDiscretePrismBoundaryLabeling
        resolution hresolution family).label) :
    ¬face.IsLateral :=
  (boxComplementarityDiscretePrismBoundaryLabeling
    resolution hresolution family).not_face_isLateral face

/-- Product refinement does not itself give the required simplex map.  This
small numerical witness is the obstruction in the pinned unit-jump
representation: a coarse jump of one scales to a jump of `factor`. -/
theorem productRefinement_unitJump_not_unit_of_one_lt
    (factor : ℕ) (hfactor : 1 < factor) :
    ¬factor ≤ 0 + 1 := by
  omega

end Math
