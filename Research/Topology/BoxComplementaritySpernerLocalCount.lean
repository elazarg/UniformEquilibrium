/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Topology.MetricSpace.Thickening
import Research.Topology.BoxComplementaritySpernerApproximation

/-!
# Local finite-grid counts for box complementarity

This module defines the mod-two count of complete Sperner simplices whose
selected label-`n` anchor lies in a displayed set.  It proves the finite-set
coherence and excision laws, identifies the global count with one, and uses
fine-mesh compact localization to clear a closed collar around the frontier
of an isolating open set.

The count still depends on the mesh.  No subdivision invariance, homotopy
invariance, eventual local parity, or `ModTwoBoxComplementarityParitySpec`
inhabitant is asserted here.
-/

noncomputable section

namespace Math

open Classical Filter Metric Set Topology

variable {n : ℕ}

/-- A raw grid simplex is locally counted when it is complete and its
proof-independent selected label-`n` anchor lies in `region`. -/
def boxComplementarityCompleteSimplexAnchorIn
    (problem : BoxComplementarityProblem (Fin n))
    (p : ℕ) (hp : 0 < p)
    (region : Set (UnitCube (Fin n)))
    (vertices : Fin (n + 1) → (boxComplementaritySpernerCube problem p hp).G) : Prop :=
  ∃ hcomplete : complete_simplex
      (boxComplementaritySpernerCube problem p hp) n vertices,
    boxComplementarityCompleteSimplexAnchorPoint
      problem p hp vertices hcomplete ∈ region

/-- Complete simplices whose selected anchors lie in `region`. -/
def boxComplementarityLocalCompleteSimplices
    (problem : BoxComplementarityProblem (Fin n))
    (p : ℕ) (hp : 0 < p)
    (region : Set (UnitCube (Fin n))) :
    Finset (Fin (n + 1) → (boxComplementaritySpernerCube problem p hp).G) :=
  {vertices | boxComplementarityCompleteSimplexAnchorIn
    problem p hp region vertices}

/-- The finite-mesh local complete-simplex count modulo two. -/
def boxComplementarityLocalCompleteSimplexParity
    (problem : BoxComplementarityProblem (Fin n))
    (p : ℕ) (hp : 0 < p)
    (region : Set (UnitCube (Fin n))) : ZMod 2 :=
  (boxComplementarityLocalCompleteSimplices problem p hp region).card

@[simp] theorem mem_boxComplementarityLocalCompleteSimplices_iff
    (problem : BoxComplementarityProblem (Fin n))
    (p : ℕ) (hp : 0 < p)
    (region : Set (UnitCube (Fin n)))
    (vertices : Fin (n + 1) → (boxComplementaritySpernerCube problem p hp).G) :
    vertices ∈ boxComplementarityLocalCompleteSimplices problem p hp region ↔
      ∃ hcomplete : complete_simplex
          (boxComplementaritySpernerCube problem p hp) n vertices,
        boxComplementarityCompleteSimplexAnchorPoint
          problem p hp vertices hcomplete ∈ region := by
  simp [boxComplementarityLocalCompleteSimplices,
    boxComplementarityCompleteSimplexAnchorIn]

/-- Anchor membership is independent of the proof of completeness. -/
theorem completeSimplexAnchorPoint_proof_irrel
    (problem : BoxComplementarityProblem (Fin n))
    (p : ℕ) (hp : 0 < p)
    (vertices : Fin (n + 1) → (boxComplementaritySpernerCube problem p hp).G)
    (first second : complete_simplex
      (boxComplementaritySpernerCube problem p hp) n vertices) :
    boxComplementarityCompleteSimplexAnchorPoint problem p hp vertices first =
      boxComplementarityCompleteSimplexAnchorPoint problem p hp vertices second := by
  congr

/-- Local counting in the whole cube is exactly completeness. -/
theorem completeSimplexAnchorIn_univ_iff
    (problem : BoxComplementarityProblem (Fin n))
    (p : ℕ) (hp : 0 < p)
    (vertices : Fin (n + 1) → (boxComplementaritySpernerCube problem p hp).G) :
    boxComplementarityCompleteSimplexAnchorIn problem p hp Set.univ vertices ↔
      complete_simplex (boxComplementaritySpernerCube problem p hp) n vertices := by
  constructor
  · rintro ⟨hcomplete, -⟩
    exact hcomplete
  · intro hcomplete
    exact ⟨hcomplete, Set.mem_univ _⟩

/-- At every positive resolution the global finite-mesh count is one modulo
two.  The cardinal transports below avoid relying on definitional equality of
the decidability terms in the two Finset comprehensions. -/
@[simp] theorem boxComplementarityLocalCompleteSimplexParity_univ
    (problem : BoxComplementarityProblem (Fin n))
    (p : ℕ) (hp : 0 < p) :
    boxComplementarityLocalCompleteSimplexParity problem p hp Set.univ = 1 := by
  classical
  let seedN : Finset (Fin (n + 1) →
      (boxComplementaritySpernerCube problem p hp).G) :=
    {vertices | complete_simplex
      (boxComplementaritySpernerCube problem p hp) n vertices}
  let seedSC : Finset
      (Fin ((boxComplementaritySpernerCube problem p hp).n + 1) →
        (boxComplementaritySpernerCube problem p hp).G) :=
    {vertices | complete_simplex (boxComplementaritySpernerCube problem p hp)
      (boxComplementaritySpernerCube problem p hp).n vertices}
  have hoddSC : Odd seedSC.card := by
    simpa only [seedSC] using
      boxComplementarity_completeSimplex_card_odd problem p hp
  have hcardSeed : seedN.card = seedSC.card := by
    apply Finset.card_nbij (fun vertices ↦ vertices)
    · intro vertices hvertices
      change vertices ∈ seedN at hvertices
      dsimp only [seedN] at hvertices
      have hcomplete := (Finset.mem_filter.mp hvertices).2
      change vertices ∈ seedSC
      dsimp only [seedSC]
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      simpa only [boxComplementaritySpernerCube] using hcomplete
    · intro first _ second _ heq
      exact heq
    · intro vertices hvertices
      change vertices ∈ seedSC at hvertices
      dsimp only [seedSC] at hvertices
      have hcomplete := (Finset.mem_filter.mp hvertices).2
      refine ⟨vertices, ?_, rfl⟩
      change vertices ∈ seedN
      dsimp only [seedN]
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      simpa only [boxComplementaritySpernerCube] using hcomplete
  have hcardLocal :
      (boxComplementarityLocalCompleteSimplices problem p hp Set.univ).card =
        seedN.card := by
    apply Finset.card_nbij (fun vertices ↦ vertices)
    · intro vertices hvertices
      change vertices ∈ seedN
      dsimp only [seedN]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact (completeSimplexAnchorIn_univ_iff problem p hp vertices).1
        ((mem_boxComplementarityLocalCompleteSimplices_iff
          problem p hp Set.univ vertices).1 hvertices)
    · intro first _ second _ heq
      exact heq
    · intro vertices hvertices
      change vertices ∈ seedN at hvertices
      dsimp only [seedN] at hvertices
      have hcomplete : complete_simplex
          (boxComplementaritySpernerCube problem p hp) n vertices :=
        (Finset.mem_filter.mp hvertices).2
      refine ⟨vertices, ?_, rfl⟩
      exact (mem_boxComplementarityLocalCompleteSimplices_iff
        problem p hp Set.univ vertices).2 ⟨hcomplete, Set.mem_univ _⟩
  have hoddLocal : Odd
      (boxComplementarityLocalCompleteSimplices problem p hp Set.univ).card := by
    rw [hcardLocal, hcardSeed]
    exact hoddSC
  rw [boxComplementarityLocalCompleteSimplexParity]
  obtain ⟨half, hhalf⟩ := hoddLocal
  rw [hhalf, Nat.cast_add, Nat.cast_mul]
  change (2 : ZMod 2) * (half : ZMod 2) + 1 = 1
  rw [show (2 : ZMod 2) = 0 by exact ZMod.natCast_self 2]
  norm_num

/-- A region inclusion induces inclusion of the locally counted simplex
Finsets. -/
theorem boxComplementarityLocalCompleteSimplices_mono
    (problem : BoxComplementarityProblem (Fin n))
    (p : ℕ) (hp : 0 < p)
    {first second : Set (UnitCube (Fin n))}
    (hsubset : first ⊆ second) :
    boxComplementarityLocalCompleteSimplices problem p hp first ⊆
      boxComplementarityLocalCompleteSimplices problem p hp second := by
  intro vertices hvertices
  obtain ⟨hcomplete, hanchor⟩ :=
    (mem_boxComplementarityLocalCompleteSimplices_iff
      problem p hp first vertices).1 hvertices
  exact (mem_boxComplementarityLocalCompleteSimplices_iff
    problem p hp second vertices).2 ⟨hcomplete, hsubset hanchor⟩

/-- If two regions agree on the selected anchors of all complete simplices,
their local finite counts agree literally. -/
theorem boxComplementarityLocalCompleteSimplices_eq_of_anchor_mem_iff
    (problem : BoxComplementarityProblem (Fin n))
    (p : ℕ) (hp : 0 < p)
    (first second : Set (UnitCube (Fin n)))
    (hagrees : ∀ vertices
      (hcomplete : complete_simplex
        (boxComplementaritySpernerCube problem p hp) n vertices),
      boxComplementarityCompleteSimplexAnchorPoint
          problem p hp vertices hcomplete ∈ first ↔
        boxComplementarityCompleteSimplexAnchorPoint
          problem p hp vertices hcomplete ∈ second) :
    boxComplementarityLocalCompleteSimplices problem p hp first =
      boxComplementarityLocalCompleteSimplices problem p hp second := by
  ext vertices
  constructor
  · intro hvertices
    obtain ⟨hcomplete, hanchor⟩ :=
      (mem_boxComplementarityLocalCompleteSimplices_iff
        problem p hp first vertices).1 hvertices
    exact (mem_boxComplementarityLocalCompleteSimplices_iff
      problem p hp second vertices).2
        ⟨hcomplete, (hagrees vertices hcomplete).1 hanchor⟩
  · intro hvertices
    obtain ⟨hcomplete, hanchor⟩ :=
      (mem_boxComplementarityLocalCompleteSimplices_iff
        problem p hp second vertices).1 hvertices
    exact (mem_boxComplementarityLocalCompleteSimplices_iff
      problem p hp first vertices).2
        ⟨hcomplete, (hagrees vertices hcomplete).2 hanchor⟩

/-- Local complete-simplex Finsets distribute over a union of regions. -/
theorem boxComplementarityLocalCompleteSimplices_union
    (problem : BoxComplementarityProblem (Fin n))
    (p : ℕ) (hp : 0 < p)
    (first second : Set (UnitCube (Fin n))) :
    boxComplementarityLocalCompleteSimplices problem p hp (first ∪ second) =
      boxComplementarityLocalCompleteSimplices problem p hp first ∪
        boxComplementarityLocalCompleteSimplices problem p hp second := by
  ext vertices
  simp only [mem_boxComplementarityLocalCompleteSimplices_iff,
    Finset.mem_union]
  constructor
  · rintro ⟨hcomplete, hfirst | hsecond⟩
    · exact Or.inl ⟨hcomplete, hfirst⟩
    · exact Or.inr ⟨hcomplete, hsecond⟩
  · rintro (⟨hcomplete, hfirst⟩ | ⟨hcomplete, hsecond⟩)
    · exact ⟨hcomplete, Or.inl hfirst⟩
    · exact ⟨hcomplete, Or.inr hsecond⟩

/-- Disjoint regions have disjoint local complete-simplex Finsets. -/
theorem boxComplementarityLocalCompleteSimplices_disjoint
    (problem : BoxComplementarityProblem (Fin n))
    (p : ℕ) (hp : 0 < p)
    {first second : Set (UnitCube (Fin n))}
    (hdisjoint : Disjoint first second) :
    Disjoint (boxComplementarityLocalCompleteSimplices problem p hp first)
      (boxComplementarityLocalCompleteSimplices problem p hp second) := by
  rw [Finset.disjoint_left]
  intro vertices hfirst hsecond
  obtain ⟨hcompleteFirst, hanchorFirst⟩ :=
    (mem_boxComplementarityLocalCompleteSimplices_iff
      problem p hp first vertices).1 hfirst
  obtain ⟨hcompleteSecond, hanchorSecond⟩ :=
    (mem_boxComplementarityLocalCompleteSimplices_iff
      problem p hp second vertices).1 hsecond
  have hanchorSecond' : boxComplementarityCompleteSimplexAnchorPoint
      problem p hp vertices hcompleteFirst ∈ second := by
    rwa [completeSimplexAnchorPoint_proof_irrel problem p hp vertices
      hcompleteFirst hcompleteSecond]
  exact Set.disjoint_left.1 hdisjoint hanchorFirst hanchorSecond'

/-- Finite-mesh excision for a disjoint union is literal addition modulo two. -/
theorem boxComplementarityLocalCompleteSimplexParity_union_of_disjoint
    (problem : BoxComplementarityProblem (Fin n))
    (p : ℕ) (hp : 0 < p)
    {first second : Set (UnitCube (Fin n))}
    (hdisjoint : Disjoint first second) :
    boxComplementarityLocalCompleteSimplexParity problem p hp (first ∪ second) =
      boxComplementarityLocalCompleteSimplexParity problem p hp first +
        boxComplementarityLocalCompleteSimplexParity problem p hp second := by
  simp only [boxComplementarityLocalCompleteSimplexParity]
  rw [boxComplementarityLocalCompleteSimplices_union,
    Finset.card_union_of_disjoint
      (boxComplementarityLocalCompleteSimplices_disjoint
        problem p hp hdisjoint), Nat.cast_add]

/-! ## Closedness of the solution set and isolating collars -/

/-- Closed product-inequality form of box complementarity. -/
theorem BoxComplementarityProblem.isSolution_iff_mul_gain
    (problem : BoxComplementarityProblem (Fin n))
    (point : UnitCube (Fin n)) :
    problem.IsSolution point ↔
      ∀ who,
        0 ≤ (point who : ℝ) * problem.gain point who ∧
          (1 - (point who : ℝ)) * problem.gain point who ≤ 0 := by
  constructor
  · intro hsolution who
    have hwho := hsolution who
    by_cases hzero : (point who : ℝ) = 0
    · rw [hzero]
      simpa using hwho.1 hzero
    by_cases hone : (point who : ℝ) = 1
    · rw [hone]
      simpa using hwho.2.1 hone
    · have hpos : 0 < (point who : ℝ) :=
        lt_of_le_of_ne (point who).property.1 (Ne.symm hzero)
      have hlt : (point who : ℝ) < 1 :=
        lt_of_le_of_ne (point who).property.2 hone
      rw [hwho.2.2 hpos hlt]
      constructor <;> norm_num
  · intro hproducts who
    have hwho := hproducts who
    constructor
    · intro hzero
      rw [hzero] at hwho
      simpa using hwho.2
    constructor
    · intro hone
      rw [hone] at hwho
      simpa using hwho.1
    · intro hpos hlt
      have hnonneg : 0 ≤ problem.gain point who := by
        nlinarith [hwho.1]
      have hnonpos : problem.gain point who ≤ 0 := by
        nlinarith [hwho.2]
      exact le_antisymm hnonpos hnonneg

/-- The box-complementarity solution set is closed. -/
theorem BoxComplementarityProblem.isClosed_solutionSet
    (problem : BoxComplementarityProblem (Fin n)) :
    IsClosed problem.solutionSet := by
  have hset : problem.solutionSet = ⋂ who : Fin n,
      {point : UnitCube (Fin n) |
        0 ≤ (point who : ℝ) * problem.gain point who} ∩
      {point : UnitCube (Fin n) |
        (1 - (point who : ℝ)) * problem.gain point who ≤ 0} := by
    ext point
    simp only [BoxComplementarityProblem.solutionSet, Set.mem_setOf_eq,
      Set.mem_iInter, Set.mem_inter_iff]
    exact problem.isSolution_iff_mul_gain point
  rw [hset]
  apply isClosed_iInter
  intro who
  have hcoordinate : Continuous
      (fun point : UnitCube (Fin n) ↦ (point who : ℝ)) :=
    continuous_subtype_val.comp (continuous_apply who)
  have hgain := problem.continuous_gain who
  exact (isClosed_Ici.preimage (hcoordinate.mul hgain)).inter
    (isClosed_Iic.preimage ((continuous_const.sub hcoordinate).mul hgain))

/-- The frontier of an isolating open set is compact and disjoint from the
solution set. -/
theorem BoxComplementarityProblem.isCompact_frontier_and_disjoint_solutionSet
    (problem : BoxComplementarityProblem (Fin n))
    (region : Set (UnitCube (Fin n)))
    (hisolating : problem.IsIsolating region) :
    IsCompact (frontier region) ∧
      Disjoint (frontier region) problem.solutionSet := by
  have hcompact : IsCompact (frontier region) :=
    by simpa only [Set.univ_inter] using
      isCompact_univ.inter_right (t := frontier region) isClosed_frontier
  refine ⟨hcompact, ?_⟩
  rw [Set.disjoint_left]
  intro point hfrontier hsolution
  have hintersection : point ∈ problem.solutionSet ∩ frontier region :=
    ⟨hsolution, hfrontier⟩
  rw [hisolating.2] at hintersection
  exact hintersection

/-- An isolating frontier has a positive compact closed collar disjoint from
all complementarity solutions. -/
theorem BoxComplementarityProblem.exists_compact_isolatingFrontierCollar
    (problem : BoxComplementarityProblem (Fin n))
    (region : Set (UnitCube (Fin n)))
    (hisolating : problem.IsIsolating region) :
    ∃ radius : ℝ, 0 < radius ∧
      IsCompact (Metric.cthickening radius (frontier region)) ∧
      Disjoint (Metric.cthickening radius (frontier region))
        problem.solutionSet := by
  have hfrontier :=
    problem.isCompact_frontier_and_disjoint_solutionSet region hisolating
  have hsubset : frontier region ⊆ problem.solutionSetᶜ := by
    intro point hpoint hsolution
    exact Set.disjoint_left.1 hfrontier.2 hpoint hsolution
  obtain ⟨radius, hradius, hcollarSubset⟩ :=
    hfrontier.1.exists_cthickening_subset_open
      problem.isClosed_solutionSet.isOpen_compl hsubset
  refine ⟨radius, hradius, hfrontier.1.cthickening, ?_⟩
  rw [Set.disjoint_left]
  intro point hcollar hsolution
  exact (hcollarSubset hcollar) hsolution

/-! ## Fine-mesh collar coherence -/

/-- A complete simplex whose anchor lies in `region` is in particular a
complete simplex with a vertex in `region`. -/
theorem BoxComplementarityProblem.hasCompleteSimplexVertexIn_of_anchor_mem
    (problem : BoxComplementarityProblem (Fin n))
    (p : ℕ) (hp : 0 < p)
    (region : Set (UnitCube (Fin n)))
    (vertices : Fin (n + 1) → (boxComplementaritySpernerCube problem p hp).G)
    (hcomplete : complete_simplex
      (boxComplementaritySpernerCube problem p hp) n vertices)
    (hanchor : boxComplementarityCompleteSimplexAnchorPoint
      problem p hp vertices hcomplete ∈ region) :
    problem.HasCompleteSimplexVertexIn region p := by
  refine ⟨hp, vertices, hcomplete,
    boxComplementarityCompleteSimplexAnchorIndex
      problem p hp vertices hcomplete, ?_⟩
  exact hanchor

/-- If no complete simplex has any vertex in `region`, the local anchor count
there is empty. -/
theorem boxComplementarityLocalCompleteSimplices_eq_empty_of_no_vertex
    (problem : BoxComplementarityProblem (Fin n))
    (p : ℕ) (hp : 0 < p)
    (region : Set (UnitCube (Fin n)))
    (hno : ¬problem.HasCompleteSimplexVertexIn region p) :
    boxComplementarityLocalCompleteSimplices problem p hp region = ∅ := by
  apply Finset.not_nonempty_iff_eq_empty.mp
  rintro ⟨vertices, hvertices⟩
  obtain ⟨hcomplete, hanchor⟩ :=
    (mem_boxComplementarityLocalCompleteSimplices_iff
      problem p hp region vertices).1 hvertices
  exact hno (problem.hasCompleteSimplexVertexIn_of_anchor_mem
    p hp region vertices hcomplete hanchor)

/-- Under the same hypothesis, the local parity is zero. -/
theorem boxComplementarityLocalCompleteSimplexParity_eq_zero_of_no_vertex
    (problem : BoxComplementarityProblem (Fin n))
    (p : ℕ) (hp : 0 < p)
    (region : Set (UnitCube (Fin n)))
    (hno : ¬problem.HasCompleteSimplexVertexIn region p) :
    boxComplementarityLocalCompleteSimplexParity problem p hp region = 0 := by
  rw [boxComplementarityLocalCompleteSimplexParity,
    boxComplementarityLocalCompleteSimplices_eq_empty_of_no_vertex
      problem p hp region hno]
  norm_num

/-- Regions whose symmetric difference is contained in a cleared set have
the same local finite-mesh simplex Finset. -/
theorem boxComplementarityLocalCompleteSimplices_eq_of_difference_subset_cleared
    (problem : BoxComplementarityProblem (Fin n))
    (p : ℕ) (hp : 0 < p)
    (first second cleared : Set (UnitCube (Fin n)))
    (hdifference : (first \ second) ∪ (second \ first) ⊆ cleared)
    (hcleared : ¬problem.HasCompleteSimplexVertexIn cleared p) :
    boxComplementarityLocalCompleteSimplices problem p hp first =
      boxComplementarityLocalCompleteSimplices problem p hp second := by
  apply boxComplementarityLocalCompleteSimplices_eq_of_anchor_mem_iff
  intro vertices hcomplete
  constructor
  · intro hfirst
    by_contra hnsecond
    apply hcleared
    apply problem.hasCompleteSimplexVertexIn_of_anchor_mem
      p hp cleared vertices hcomplete
    exact hdifference (Or.inl ⟨hfirst, hnsecond⟩)
  · intro hsecond
    by_contra hnfirst
    apply hcleared
    apply problem.hasCompleteSimplexVertexIn_of_anchor_mem
      p hp cleared vertices hcomplete
    exact hdifference (Or.inr ⟨hsecond, hnfirst⟩)

/-- The corresponding local mod-two counts agree. -/
theorem boxComplementarityLocalCompleteSimplexParity_eq_of_difference_subset_cleared
    (problem : BoxComplementarityProblem (Fin n))
    (p : ℕ) (hp : 0 < p)
    (first second cleared : Set (UnitCube (Fin n)))
    (hdifference : (first \ second) ∪ (second \ first) ⊆ cleared)
    (hcleared : ¬problem.HasCompleteSimplexVertexIn cleared p) :
    boxComplementarityLocalCompleteSimplexParity problem p hp first =
      boxComplementarityLocalCompleteSimplexParity problem p hp second := by
  rw [boxComplementarityLocalCompleteSimplexParity,
    boxComplementarityLocalCompleteSimplexParity,
    boxComplementarityLocalCompleteSimplices_eq_of_difference_subset_cleared
      problem p hp first second cleared hdifference hcleared]

/-- Every isolating open set has a positive closed frontier collar with zero
fine-mesh complete-simplex count. -/
theorem BoxComplementarityProblem.exists_isolatingFrontierCollar_eventually_cleared
    (problem : BoxComplementarityProblem (Fin n))
    (region : Set (UnitCube (Fin n)))
    (hisolating : problem.IsIsolating region) :
    ∃ radius : ℝ, 0 < radius ∧
      ∃ threshold, ∀ p, threshold ≤ p →
        ¬problem.HasCompleteSimplexVertexIn
          (Metric.cthickening radius (frontier region)) p := by
  obtain ⟨radius, hradius, hcompact, hdisjoint⟩ :=
    problem.exists_compact_isolatingFrontierCollar region hisolating
  obtain ⟨threshold, hthreshold⟩ :=
    problem.eventually_no_completeSimplexVertexIn_of_compact
      (Metric.cthickening radius (frontier region)) hcompact hdisjoint
  exact ⟨radius, hradius, threshold, hthreshold⟩

/-- The local count of a suitable isolating frontier collar is eventually
zero at every positive fine resolution. -/
theorem BoxComplementarityProblem.exists_isolatingFrontierCollar_eventually_parity_zero
    (problem : BoxComplementarityProblem (Fin n))
    (region : Set (UnitCube (Fin n)))
    (hisolating : problem.IsIsolating region) :
    ∃ radius : ℝ, 0 < radius ∧
      ∃ threshold, ∀ p, threshold ≤ p → ∀ hp : 0 < p,
        boxComplementarityLocalCompleteSimplexParity problem p hp
          (Metric.cthickening radius (frontier region)) = 0 := by
  obtain ⟨radius, hradius, threshold, hcleared⟩ :=
    problem.exists_isolatingFrontierCollar_eventually_cleared region hisolating
  refine ⟨radius, hradius, threshold, ?_⟩
  intro p hpFine hp
  exact boxComplementarityLocalCompleteSimplexParity_eq_zero_of_no_vertex
    problem p hp _ (hcleared p hpFine)

/-- At fine meshes, changing a local-count region only inside a cleared
isolating frontier collar does not change its mod-two count. -/
theorem BoxComplementarityProblem.exists_isolatingFrontierCollar_eventually_coherent
    (problem : BoxComplementarityProblem (Fin n))
    (region : Set (UnitCube (Fin n)))
    (hisolating : problem.IsIsolating region) :
    ∃ radius : ℝ, 0 < radius ∧
      ∃ threshold, ∀ p, threshold ≤ p → ∀ hp : 0 < p,
        ∀ first second : Set (UnitCube (Fin n)),
          (first \ second) ∪ (second \ first) ⊆
              Metric.cthickening radius (frontier region) →
            boxComplementarityLocalCompleteSimplexParity problem p hp first =
              boxComplementarityLocalCompleteSimplexParity problem p hp second := by
  obtain ⟨radius, hradius, threshold, hcleared⟩ :=
    problem.exists_isolatingFrontierCollar_eventually_cleared region hisolating
  refine ⟨radius, hradius, threshold, ?_⟩
  intro p hpFine hp first second hdifference
  exact
    boxComplementarityLocalCompleteSimplexParity_eq_of_difference_subset_cleared
      problem p hp first second _ hdifference (hcleared p hpFine)

/-! ## Abstract relative-prism parity -/

/-- The mod-two boundary identity underlying a relative cubical prism.

This is a finite double-counting theorem, not a supplied invariance axiom. A
concrete subdivision or parameter-times-cube construction can use it after
exhibiting its cells and faces, proving that every cell has even incidence
degree, and identifying the odd-degree faces with the disjoint left and right
ends. -/
theorem relativeCubicalPrism_boundaryParity_eq
    {Cell Face : Type*} [Fintype Cell] [Fintype Face]
    (incident : Cell → Face → Prop)
    (leftBoundary rightBoundary : Face → Prop)
    (hdisjoint : ∀ face, ¬(leftBoundary face ∧ rightBoundary face))
    (hcellEven : ∀ cell,
      Even (Finset.univ.filter fun face ↦ incident cell face).card)
    (hfaceOdd : ∀ face,
      Odd (Finset.univ.filter fun cell ↦ incident cell face).card ↔
        leftBoundary face ∨ rightBoundary face) :
    ((Finset.univ.filter leftBoundary).card : ZMod 2) =
      ((Finset.univ.filter rightBoundary).card : ZMod 2) := by
  classical
  let leftFaces : Finset Face := {face | leftBoundary face}
  let rightFaces : Finset Face := {face | rightBoundary face}
  let boundaryFaces : Finset Face :=
    {face | leftBoundary face ∨ rightBoundary face}
  have hdoubleCount :
      ∑ cell : Cell, (Finset.univ.filter fun face ↦ incident cell face).card =
        ∑ face : Face,
          (Finset.univ.filter fun cell ↦ incident cell face).card := by
    simpa [Finset.bipartiteAbove, Finset.bipartiteBelow] using
      (Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
        incident (s := Finset.univ) (t := Finset.univ))
  have hcellSumEven : Even
      (∑ cell : Cell,
        (Finset.univ.filter fun face ↦ incident cell face).card) := by
    exact Finset.even_sum _ (fun cell _ ↦ hcellEven cell)
  have hfaceSumEven : Even
      (∑ face : Face,
        (Finset.univ.filter fun cell ↦ incident cell face).card) := by
    rwa [← hdoubleCount]
  have hboundaryEven : Even boundaryFaces.card := by
    rw [← Nat.not_odd_iff_even]
    intro hboundaryOdd
    have hfaceSumOdd : Odd
        (∑ face : Face,
          (Finset.univ.filter fun cell ↦ incident cell face).card) :=
      (handshake_3 (fun face cell ↦ incident cell face)
        (fun face ↦ face ∈ boundaryFaces)
        (fun face ↦ by
          rw [hfaceOdd face]
          simp only [boundaryFaces, Finset.mem_filter, Finset.mem_univ,
            true_and])).1 (by
          simpa only [Finset.filter_mem_eq_inter, Finset.univ_inter] using
            hboundaryOdd)
    exact (Nat.not_odd_iff_even.mpr hfaceSumEven) hfaceSumOdd
  have hboundaryUnion : boundaryFaces = leftFaces ∪ rightFaces := by
    ext face
    simp only [boundaryFaces, leftFaces, rightFaces, Finset.mem_filter,
      Finset.mem_univ, true_and, Finset.mem_union]
  have hleftRightDisjoint : Disjoint leftFaces rightFaces := by
    rw [Finset.disjoint_left]
    intro face hleft hright
    exact hdisjoint face (by
      simpa only [leftFaces, rightFaces, Finset.mem_filter, Finset.mem_univ,
        true_and] using And.intro hleft hright)
  have hsumEven : Even (leftFaces.card + rightFaces.card) := by
    rw [← Finset.card_union_of_disjoint hleftRightDisjoint, ← hboundaryUnion]
    exact hboundaryEven
  have hsameEven : Even leftFaces.card ↔ Even rightFaces.card :=
    Nat.even_add.mp hsumEven
  have hmod : leftFaces.card % 2 = rightFaces.card % 2 := by
    by_cases hleft : Even leftFaces.card
    · exact (Nat.even_iff.mp hleft).trans
        (Nat.even_iff.mp (hsameEven.mp hleft)).symm
    · have hright : ¬Even rightFaces.card := by
        intro hright
        exact hleft (hsameEven.mpr hright)
      exact (Nat.odd_iff.mp (Nat.not_even_iff_odd.mp hleft)).trans
        (Nat.odd_iff.mp (Nat.not_even_iff_odd.mp hright)).symm
  change (leftFaces.card : ZMod 2) = (rightFaces.card : ZMod 2)
  calc
    (leftFaces.card : ZMod 2) = (leftFaces.card % 2 : ℕ) :=
      (ZMod.natCast_mod leftFaces.card 2).symm
    _ = (rightFaces.card % 2 : ℕ) := congrArg Nat.cast hmod
    _ = (rightFaces.card : ZMod 2) :=
      ZMod.natCast_mod rightFaces.card 2

end Math
