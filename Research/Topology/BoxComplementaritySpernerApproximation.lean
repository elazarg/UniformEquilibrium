/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Research.Topology.BoxComplementarityCubicalSperner

/-!
# Fine-mesh approximation for box complementarity

Complete simplices for the concrete cubical Sperner labeling carry one
label-`n` anchor and one label-`i` vertex for every coordinate `i`.  Their
grid points are within `1 / p` of each other.  Consequently every sequential
cluster of anchors along resolutions tending to infinity is an actual box
complementarity solution.

The final theorem localizes this statement away from the solution set on a
compact set.  This is a compactness/approximation result only: it does not
define local parity or prove invariance of local counts across subdivisions.
-/

noncomputable section

namespace Math

open Classical Filter Set Topology

variable {n : ℕ}

/-- Coordinatewise neighboring grid vertices map to unit-cube points at
distance at most `1 / p`. -/
theorem dist_boxComplementarityGridPoint_le_one_div
    (p : ℕ) (hp : 0 < p)
    (first second : Fin n → Fin (p + 1))
    (hneighbors : ∀ who,
      (first who).1 ≤ (second who).1 + 1 ∧
        (second who).1 ≤ (first who).1 + 1) :
    dist (boxComplementarityGridPoint p first)
      (boxComplementarityGridPoint p second) ≤ 1 / (p : ℝ) := by
  rw [dist_pi_le_iff (by positivity : 0 ≤ (1 : ℝ) / p)]
  intro who
  change dist (((first who).1 : ℝ) / p) (((second who).1 : ℝ) / p) ≤
    1 / (p : ℝ)
  rw [Real.dist_eq, abs_sub_le_iff]
  constructor
  · rw [sub_le_iff_le_add', ← add_div]
    rw [div_le_div_iff_of_pos_right (Nat.cast_pos.mpr hp)]
    exact_mod_cast (hneighbors who).1
  · rw [sub_le_iff_le_add', ← add_div]
    rw [div_le_div_iff_of_pos_right (Nat.cast_pos.mpr hp)]
    exact_mod_cast (hneighbors who).2

/-- Any two vertices of one complete (indeed, one simplex) have grid points
within one mesh width. -/
theorem dist_boxComplementarityGridPoint_le_one_div_of_simplex
    (problem : BoxComplementarityProblem (Fin n))
    (p : ℕ) (hp : 0 < p)
    (vertices : Fin (n + 1) → (boxComplementaritySpernerCube problem p hp).G)
    (hsimplex : simplex (boxComplementaritySpernerCube problem p hp) n vertices)
    (first second : Fin (n + 1)) :
    dist (boxComplementarityGridPoint p (vertices first))
      (boxComplementarityGridPoint p (vertices second)) ≤ 1 / (p : ℝ) := by
  apply dist_boxComplementarityGridPoint_le_one_div p hp
  intro who
  exact ⟨le_add_one_of_simplex (boxComplementaritySpernerCube problem p hp)
      vertices hsimplex first second who,
    le_add_one_of_simplex (boxComplementaritySpernerCube problem p hp)
      vertices hsimplex second first who⟩

/-- The selected vertex carrying the extra label `n`. -/
def boxComplementarityCompleteSimplexAnchorIndex
    (problem : BoxComplementarityProblem (Fin n))
    (p : ℕ) (hp : 0 < p)
    (vertices : Fin (n + 1) → (boxComplementaritySpernerCube problem p hp).G)
    (hcomplete : complete_simplex
      (boxComplementaritySpernerCube problem p hp) n vertices) : Fin (n + 1) :=
  Classical.choose (by
    have hmem : n ∈ Set.range (fun index : Fin (n + 1) ↦
        (boxComplementaritySpernerCube problem p hp).RL (vertices index)) := by
      rw [hcomplete.2]
      show n ≤ n
      exact le_rfl
    exact hmem)

/-- The anchor has literal reduced label `n`. -/
theorem boxComplementarityCompleteSimplexAnchorIndex_label
    (problem : BoxComplementarityProblem (Fin n))
    (p : ℕ) (hp : 0 < p)
    (vertices : Fin (n + 1) → (boxComplementaritySpernerCube problem p hp).G)
    (hcomplete : complete_simplex
      (boxComplementaritySpernerCube problem p hp) n vertices) :
    boxComplementarityReducedLabel problem p
        (vertices (boxComplementarityCompleteSimplexAnchorIndex
          problem p hp vertices hcomplete)) = n :=
  Classical.choose_spec (by
    have hmem : n ∈ Set.range (fun index : Fin (n + 1) ↦
        (boxComplementaritySpernerCube problem p hp).RL (vertices index)) := by
      rw [hcomplete.2]
      show n ≤ n
      exact le_rfl
    exact hmem)

/-- The selected vertex carrying coordinate label `who`. -/
def boxComplementarityCompleteSimplexCoordinateIndex
    (problem : BoxComplementarityProblem (Fin n))
    (p : ℕ) (hp : 0 < p)
    (vertices : Fin (n + 1) → (boxComplementaritySpernerCube problem p hp).G)
    (hcomplete : complete_simplex
      (boxComplementaritySpernerCube problem p hp) n vertices)
    (who : Fin n) : Fin (n + 1) :=
  Classical.choose (by
    have hmem : who.1 ∈ Set.range (fun index : Fin (n + 1) ↦
        (boxComplementaritySpernerCube problem p hp).RL (vertices index)) := by
      rw [hcomplete.2]
      exact Nat.le_of_lt who.isLt
    exact hmem)

/-- The coordinate selector has the literal label of that coordinate. -/
theorem boxComplementarityCompleteSimplexCoordinateIndex_label
    (problem : BoxComplementarityProblem (Fin n))
    (p : ℕ) (hp : 0 < p)
    (vertices : Fin (n + 1) → (boxComplementaritySpernerCube problem p hp).G)
    (hcomplete : complete_simplex
      (boxComplementaritySpernerCube problem p hp) n vertices)
    (who : Fin n) :
    boxComplementarityReducedLabel problem p
        (vertices (boxComplementarityCompleteSimplexCoordinateIndex
          problem p hp vertices hcomplete who)) = who.1 :=
  Classical.choose_spec (by
    have hmem : who.1 ∈ Set.range (fun index : Fin (n + 1) ↦
        (boxComplementaritySpernerCube problem p hp).RL (vertices index)) := by
      rw [hcomplete.2]
      exact Nat.le_of_lt who.isLt
    exact hmem)

/-- The unit-cube point at the selected label-`n` anchor. -/
def boxComplementarityCompleteSimplexAnchorPoint
    (problem : BoxComplementarityProblem (Fin n))
    (p : ℕ) (hp : 0 < p)
    (vertices : Fin (n + 1) → (boxComplementaritySpernerCube problem p hp).G)
    (hcomplete : complete_simplex
      (boxComplementaritySpernerCube problem p hp) n vertices) :
    UnitCube (Fin n) :=
  boxComplementarityGridPoint p
    (vertices (boxComplementarityCompleteSimplexAnchorIndex
      problem p hp vertices hcomplete))

/-- The unit-cube point at the selected label-`who` vertex. -/
def boxComplementarityCompleteSimplexCoordinatePoint
    (problem : BoxComplementarityProblem (Fin n))
    (p : ℕ) (hp : 0 < p)
    (vertices : Fin (n + 1) → (boxComplementaritySpernerCube problem p hp).G)
    (hcomplete : complete_simplex
      (boxComplementaritySpernerCube problem p hp) n vertices)
    (who : Fin n) : UnitCube (Fin n) :=
  boxComplementarityGridPoint p
    (vertices (boxComplementarityCompleteSimplexCoordinateIndex
      problem p hp vertices hcomplete who))

/-- The selected anchor and every selected coordinate vertex are within one
mesh width. -/
theorem dist_completeSimplexAnchorPoint_coordinatePoint_le_one_div
    (problem : BoxComplementarityProblem (Fin n))
    (p : ℕ) (hp : 0 < p)
    (vertices : Fin (n + 1) → (boxComplementaritySpernerCube problem p hp).G)
    (hcomplete : complete_simplex
      (boxComplementaritySpernerCube problem p hp) n vertices)
    (who : Fin n) :
    dist (boxComplementarityCompleteSimplexAnchorPoint
        problem p hp vertices hcomplete)
      (boxComplementarityCompleteSimplexCoordinatePoint
        problem p hp vertices hcomplete who) ≤ 1 / (p : ℝ) := by
  exact dist_boxComplementarityGridPoint_le_one_div_of_simplex
    problem p hp vertices hcomplete.1 _ _

/-- No coordinate is a grid violation at the selected label-`n` anchor. -/
theorem not_isGridViolation_completeSimplexAnchor
    (problem : BoxComplementarityProblem (Fin n))
    (p : ℕ) (hp : 0 < p)
    (vertices : Fin (n + 1) → (boxComplementaritySpernerCube problem p hp).G)
    (hcomplete : complete_simplex
      (boxComplementaritySpernerCube problem p hp) n vertices)
    (who : Fin n) :
    ¬problem.IsGridViolation p
      (vertices (boxComplementarityCompleteSimplexAnchorIndex
        problem p hp vertices hcomplete)) who := by
  intro hviolation
  have hle := (boxComplementarityReducedLabel_properties problem p
    (vertices (boxComplementarityCompleteSimplexAnchorIndex
      problem p hp vertices hcomplete))).2 who |>.2 hviolation
  rw [boxComplementarityCompleteSimplexAnchorIndex_label] at hle
  exact (Nat.not_le_of_lt who.isLt) hle

/-- The selected label-`who` vertex is a grid violation at that coordinate. -/
theorem isGridViolation_completeSimplexCoordinate
    (problem : BoxComplementarityProblem (Fin n))
    (p : ℕ) (hp : 0 < p)
    (vertices : Fin (n + 1) → (boxComplementaritySpernerCube problem p hp).G)
    (hcomplete : complete_simplex
      (boxComplementaritySpernerCube problem p hp) n vertices)
    (who : Fin n) :
    problem.IsGridViolation p
      (vertices (boxComplementarityCompleteSimplexCoordinateIndex
        problem p hp vertices hcomplete who)) who := by
  apply (boxComplementarityReducedLabel_properties problem p
    (vertices (boxComplementarityCompleteSimplexCoordinateIndex
      problem p hp vertices hcomplete who))).2 who |>.1
  exact boxComplementarityCompleteSimplexCoordinateIndex_label
    problem p hp vertices hcomplete who

/-- At a positive anchor coordinate, absence of a grid violation makes the
gain nonnegative. -/
theorem completeSimplexAnchor_gain_nonneg_of_pos
    (problem : BoxComplementarityProblem (Fin n))
    (p : ℕ) (hp : 0 < p)
    (vertices : Fin (n + 1) → (boxComplementaritySpernerCube problem p hp).G)
    (hcomplete : complete_simplex
      (boxComplementaritySpernerCube problem p hp) n vertices)
    (who : Fin n)
    (hpositive : 0 < (boxComplementarityCompleteSimplexAnchorPoint
      problem p hp vertices hcomplete who : ℝ)) :
    0 ≤ problem.gain
      (boxComplementarityCompleteSimplexAnchorPoint
        problem p hp vertices hcomplete) who := by
  apply le_of_not_gt
  intro hnegative
  apply not_isGridViolation_completeSimplexAnchor
    problem p hp vertices hcomplete who
  exact Or.inl ⟨hpositive, hnegative⟩

/-- Below the upper face, the selected coordinate violation has strictly
negative gain. -/
theorem completeSimplexCoordinate_gain_neg_of_lt_one
    (problem : BoxComplementarityProblem (Fin n))
    (p : ℕ) (hp : 0 < p)
    (vertices : Fin (n + 1) → (boxComplementaritySpernerCube problem p hp).G)
    (hcomplete : complete_simplex
      (boxComplementaritySpernerCube problem p hp) n vertices)
    (who : Fin n)
    (hlt : (boxComplementarityCompleteSimplexCoordinatePoint
      problem p hp vertices hcomplete who who : ℝ) < 1) :
    problem.gain (boxComplementarityCompleteSimplexCoordinatePoint
      problem p hp vertices hcomplete who) who < 0 := by
  have hviolation := isGridViolation_completeSimplexCoordinate
    problem p hp vertices hcomplete who
  rw [BoxComplementarityProblem.IsGridViolation] at hviolation
  rcases hviolation with hnegative | hupp
  · exact hnegative.2
  · change (boxComplementarityCompleteSimplexCoordinatePoint
      problem p hp vertices hcomplete who who : ℝ) = 1 at hupp
    linarith

/-- Vanishing mesh width transports convergence of the selected anchors to
every selected coordinate vertex. -/
theorem tendsto_completeSimplexCoordinatePoint_of_anchorPoint
    (problem : BoxComplementarityProblem (Fin n))
    (resolution : ℕ → ℕ)
    (hpositive : ∀ time, 0 < resolution time)
    (hresolution : Tendsto resolution atTop atTop)
    (vertices : ∀ time,
      Fin (n + 1) →
        (boxComplementaritySpernerCube problem
          (resolution time) (hpositive time)).G)
    (hcomplete : ∀ time, complete_simplex
      (boxComplementaritySpernerCube problem
        (resolution time) (hpositive time)) n (vertices time))
    {limit : UnitCube (Fin n)}
    (hanchor : Tendsto (fun time ↦
      boxComplementarityCompleteSimplexAnchorPoint problem
        (resolution time) (hpositive time) (vertices time) (hcomplete time))
      atTop (nhds limit))
    (who : Fin n) :
    Tendsto (fun time ↦
      boxComplementarityCompleteSimplexCoordinatePoint problem
        (resolution time) (hpositive time) (vertices time)
        (hcomplete time) who) atTop (nhds limit) := by
  apply hanchor.congr_dist
  apply squeeze_zero' (Eventually.of_forall fun _ ↦ dist_nonneg)
    (Eventually.of_forall fun time ↦
      dist_completeSimplexAnchorPoint_coordinatePoint_le_one_div
        problem (resolution time) (hpositive time) (vertices time)
          (hcomplete time) who)
  have hcast : Tendsto (fun time ↦ (resolution time : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hresolution
  simpa only [one_div, Function.comp_def] using
    tendsto_inv_atTop_zero.comp hcast

/-- In dimension zero every cube point vacuously solves complementarity. -/
theorem BoxComplementarityProblem.isSolution_fin_zero
    (problem : BoxComplementarityProblem (Fin 0))
    (point : UnitCube (Fin 0)) : problem.IsSolution point := by
  intro who
  exact Fin.elim0 who

/-- Every limit of selected complete-simplex anchors along a mesh tending to
infinity is a literal box-complementarity solution. -/
theorem BoxComplementarityProblem.isSolution_of_completeSimplexAnchorPoint_tendsto
    (problem : BoxComplementarityProblem (Fin n))
    (resolution : ℕ → ℕ)
    (hpositive : ∀ time, 0 < resolution time)
    (hresolution : Tendsto resolution atTop atTop)
    (vertices : ∀ time,
      Fin (n + 1) →
        (boxComplementaritySpernerCube problem
          (resolution time) (hpositive time)).G)
    (hcomplete : ∀ time, complete_simplex
      (boxComplementaritySpernerCube problem
        (resolution time) (hpositive time)) n (vertices time))
    {limit : UnitCube (Fin n)}
    (hanchor : Tendsto (fun time ↦
      boxComplementarityCompleteSimplexAnchorPoint problem
        (resolution time) (hpositive time) (vertices time) (hcomplete time))
      atTop (nhds limit)) :
    problem.IsSolution limit := by
  by_cases hdimension : n = 0
  · subst n
    exact problem.isSolution_fin_zero limit
  intro who
  let anchorPoint : ℕ → UnitCube (Fin n) := fun time ↦
    boxComplementarityCompleteSimplexAnchorPoint problem
      (resolution time) (hpositive time) (vertices time) (hcomplete time)
  let coordinatePoint : ℕ → UnitCube (Fin n) := fun time ↦
    boxComplementarityCompleteSimplexCoordinatePoint problem
      (resolution time) (hpositive time) (vertices time) (hcomplete time) who
  have hcoordinate : Tendsto coordinatePoint atTop (nhds limit) :=
    tendsto_completeSimplexCoordinatePoint_of_anchorPoint problem resolution
      hpositive hresolution vertices hcomplete hanchor who
  have hanchorCoordinate : Tendsto (fun time ↦ (anchorPoint time who : ℝ))
      atTop (nhds (limit who : ℝ)) := by
    have hcontinuous : Continuous
        (fun point : UnitCube (Fin n) ↦ (point who : ℝ)) :=
      continuous_subtype_val.comp (continuous_apply who)
    exact (hcontinuous.tendsto limit).comp hanchor
  have hselectedCoordinate :
      Tendsto (fun time ↦ (coordinatePoint time who : ℝ))
        atTop (nhds (limit who : ℝ)) := by
    have hcontinuous : Continuous
        (fun point : UnitCube (Fin n) ↦ (point who : ℝ)) :=
      continuous_subtype_val.comp (continuous_apply who)
    exact (hcontinuous.tendsto limit).comp hcoordinate
  have hanchorGain : Tendsto (fun time ↦ problem.gain (anchorPoint time) who)
      atTop (nhds (problem.gain limit who)) :=
    (problem.continuous_gain who).tendsto limit |>.comp hanchor
  have hcoordinateGain :
      Tendsto (fun time ↦ problem.gain (coordinatePoint time) who)
        atTop (nhds (problem.gain limit who)) :=
    (problem.continuous_gain who).tendsto limit |>.comp hcoordinate
  constructor
  · intro hzero
    have hlt : (limit who : ℝ) < 1 := by rw [hzero]; norm_num
    have heventually := hselectedCoordinate.eventually (eventually_lt_nhds hlt)
    apply le_of_tendsto hcoordinateGain
    filter_upwards [heventually] with time htime
    exact (completeSimplexCoordinate_gain_neg_of_lt_one problem
      (resolution time) (hpositive time) (vertices time)
      (hcomplete time) who htime).le
  constructor
  · intro hone
    have hpos : 0 < (limit who : ℝ) := by rw [hone]; norm_num
    have heventually := hanchorCoordinate.eventually (eventually_gt_nhds hpos)
    apply ge_of_tendsto hanchorGain
    filter_upwards [heventually] with time htime
    exact completeSimplexAnchor_gain_nonneg_of_pos problem
      (resolution time) (hpositive time) (vertices time)
      (hcomplete time) who htime
  · intro hpos hlt
    apply le_antisymm
    · have heventually :=
        hselectedCoordinate.eventually (eventually_lt_nhds hlt)
      apply le_of_tendsto hcoordinateGain
      filter_upwards [heventually] with time htime
      exact (completeSimplexCoordinate_gain_neg_of_lt_one problem
        (resolution time) (hpositive time) (vertices time)
        (hcomplete time) who htime).le
    · have heventually :=
        hanchorCoordinate.eventually (eventually_gt_nhds hpos)
      apply ge_of_tendsto hanchorGain
      filter_upwards [heventually] with time htime
      exact completeSimplexAnchor_gain_nonneg_of_pos problem
        (resolution time) (hpositive time) (vertices time)
        (hcomplete time) who htime

/-- Sequential-cluster form: every convergent subsequence of anchors along one
fine-mesh family has a complementarity-solution limit. -/
theorem BoxComplementarityProblem.isSolution_of_completeSimplexAnchorPoint_subsequence_tendsto
    (problem : BoxComplementarityProblem (Fin n))
    (resolution : ℕ → ℕ)
    (hpositive : ∀ time, 0 < resolution time)
    (hresolution : Tendsto resolution atTop atTop)
    (vertices : ∀ time,
      Fin (n + 1) →
        (boxComplementaritySpernerCube problem
          (resolution time) (hpositive time)).G)
    (hcomplete : ∀ time, complete_simplex
      (boxComplementaritySpernerCube problem
        (resolution time) (hpositive time)) n (vertices time))
    (subseq : ℕ → ℕ) (hsubseq : StrictMono subseq)
    {limit : UnitCube (Fin n)}
    (hanchor : Tendsto (fun time ↦
      boxComplementarityCompleteSimplexAnchorPoint problem
        (resolution (subseq time)) (hpositive (subseq time))
        (vertices (subseq time)) (hcomplete (subseq time)))
      atTop (nhds limit)) :
    problem.IsSolution limit :=
  problem.isSolution_of_completeSimplexAnchorPoint_tendsto
    (resolution ∘ subseq) (fun time ↦ hpositive (subseq time))
    (hresolution.comp hsubseq.tendsto_atTop)
    (fun time ↦ vertices (subseq time))
    (fun time ↦ hcomplete (subseq time)) hanchor

/-- A complete simplex at resolution `p` with at least one grid vertex in the
displayed set. -/
def BoxComplementarityProblem.HasCompleteSimplexVertexIn
    (problem : BoxComplementarityProblem (Fin n))
    (target : Set (UnitCube (Fin n))) (p : ℕ) : Prop :=
  ∃ hp : 0 < p,
    ∃ vertices : Fin (n + 1) →
        (boxComplementaritySpernerCube problem p hp).G,
      complete_simplex (boxComplementaritySpernerCube problem p hp) n vertices ∧
        ∃ index : Fin (n + 1),
          boxComplementarityGridPoint p (vertices index) ∈ target

/-- A compact set disjoint from the complementarity solution set contains no
vertex of a complete simplex at every sufficiently fine mesh. -/
theorem BoxComplementarityProblem.eventually_no_completeSimplexVertexIn_of_compact
    (problem : BoxComplementarityProblem (Fin n))
    (target : Set (UnitCube (Fin n)))
    (hcompact : IsCompact target)
    (hdisjoint : Disjoint target problem.solutionSet) :
    ∃ threshold, ∀ p, threshold ≤ p →
      ¬problem.HasCompleteSimplexVertexIn target p := by
  by_contra hfailure
  push Not at hfailure
  choose resolution hlower hwitness using hfailure
  choose hpositive vertices hcomplete selectedIndex hselected using hwitness
  have hresolution : Tendsto resolution atTop atTop := by
    rw [tendsto_atTop]
    intro lower
    filter_upwards [eventually_ge_atTop lower] with time htime
    exact htime.trans (hlower time)
  let selectedPoint : ℕ → UnitCube (Fin n) := fun time ↦
    boxComplementarityGridPoint (resolution time)
      (vertices time (selectedIndex time))
  obtain ⟨limit, hlimitTarget, subseq, hsubseq, hselectedTendsto⟩ :=
    hcompact.tendsto_subseq hselected
  have hsubResolution : Tendsto (resolution ∘ subseq) atTop atTop :=
    hresolution.comp hsubseq.tendsto_atTop
  have hmeshZero : Tendsto (fun time ↦ 1 / (resolution (subseq time) : ℝ))
      atTop (nhds 0) := by
    have hcast : Tendsto (fun time ↦ (resolution (subseq time) : ℝ))
        atTop atTop := tendsto_natCast_atTop_atTop.comp hsubResolution
    simpa only [one_div, Function.comp_def] using
      tendsto_inv_atTop_zero.comp hcast
  have hdist : Tendsto (fun time ↦
      dist ((selectedPoint ∘ subseq) time)
        (boxComplementarityCompleteSimplexAnchorPoint problem
          (resolution (subseq time)) (hpositive (subseq time))
          (vertices (subseq time)) (hcomplete (subseq time))))
      atTop (nhds 0) := by
    apply squeeze_zero' (Eventually.of_forall fun _ ↦ dist_nonneg)
      (Eventually.of_forall fun time ↦ ?_) hmeshZero
    exact dist_boxComplementarityGridPoint_le_one_div_of_simplex
      problem (resolution (subseq time)) (hpositive (subseq time))
      (vertices (subseq time)) (hcomplete (subseq time)).1
      (selectedIndex (subseq time))
      (boxComplementarityCompleteSimplexAnchorIndex problem
        (resolution (subseq time)) (hpositive (subseq time))
        (vertices (subseq time)) (hcomplete (subseq time)))
  have hanchorTendsto : Tendsto (fun time ↦
      boxComplementarityCompleteSimplexAnchorPoint problem
        (resolution (subseq time)) (hpositive (subseq time))
        (vertices (subseq time)) (hcomplete (subseq time)))
      atTop (nhds limit) :=
    hselectedTendsto.congr_dist hdist
  have hsolution : problem.IsSolution limit :=
    problem.isSolution_of_completeSimplexAnchorPoint_tendsto
      (resolution ∘ subseq) (fun time ↦ hpositive (subseq time))
      hsubResolution (fun time ↦ vertices (subseq time))
      (fun time ↦ hcomplete (subseq time)) hanchorTendsto
  exact Set.disjoint_left.1 hdisjoint hlimitTarget hsolution

end Math
