import MathUE.Topology.AmbientDegreeProperties
import MathUE.Topology.AmbientDegreeHomotopyNormalization

/-!
# Boundary-fixing maps cover their source regions

Identity normalization and the existing actual-source straight-line homotopy
show degree one for a field equal to identity on an open bounded source frontier.
This produces actual interior preimages without any isolated-root assumption.
The closed-ball facade constructs a continuous extension internally and treats
boundary targets directly. Negative and zero radii and dimension zero are allowed.
-/

namespace Math.Topology

open Set

variable {n : ℕ}

/-- Identity on the source frontier excludes any target in its interior. -/
theorem frontier_avoids_of_eq_identity
    (field : (Fin n → ℝ) → Fin n → ℝ) (region : Set (Fin n → ℝ))
    (target : Fin n → ℝ) (hopen : IsOpen region) (htarget : target ∈ region)
    (hfix : ∀ point ∈ frontier region, field point = point) :
    ∀ point ∈ frontier region, field point ≠ target := by
  intro point hpoint
  rw [hfix point hpoint]
  exact identity_ne_target_on_frontier region target hopen htarget point hpoint

/-- A field continuous on the source closure and equal to identity on its
frontier has intrinsic degree one at every target in the open bounded source. -/
theorem ambientDegree_eq_one_of_eq_identity_on_frontier
    (field : (Fin n → ℝ) → Fin n → ℝ) (region : Set (Fin n → ℝ))
    (target : Fin n → ℝ) (hopen : IsOpen region)
    (hbounded : Bornology.IsBounded region)
    (hfield : ContinuousOn field (closure region)) (htarget : target ∈ region)
    (hfix : ∀ point ∈ frontier region, field point = point) :
    ambientDegree field region target hopen hbounded hfield
      (frontier_avoids_of_eq_identity field region target hopen htarget hfix) = 1 := by
  let interpolation : (ℝ × (Fin n → ℝ)) → Fin n → ℝ :=
    fun point => point.2 + point.1 • (field point.2 - point.2)
  have hjoint : ContinuousOn interpolation (Icc (0 : ℝ) 1 ×ˢ closure region) := by
    have hcompose : ContinuousOn (fun point : ℝ × (Fin n → ℝ) => field point.2)
        (Icc (0 : ℝ) 1 ×ˢ closure region) :=
      hfield.comp continuous_snd.continuousOn (fun _ hpoint => hpoint.2)
    exact continuous_snd.continuousOn.add
      (continuous_fst.continuousOn.smul (hcompose.sub continuous_snd.continuousOn))
  have hfrontier (parameter : Icc (0 : ℝ) 1) :
      ∀ point ∈ frontier region, interpolation ((parameter : ℝ), point) ≠ target := by
    intro point hpoint
    have hequal : interpolation ((parameter : ℝ), point) = point := by
      simp only [interpolation, hfix point hpoint, sub_self, smul_zero, add_zero]
    rw [hequal]
    exact identity_ne_target_on_frontier region target hopen htarget point hpoint
  have hzero : (fun point => interpolation (0, point)) = id := by
    funext point
    simp only [interpolation, zero_smul, add_zero, id_eq]
  have hone : (fun point => interpolation (1, point)) = field := by
    funext point
    simp only [interpolation, one_smul, add_sub_cancel]
  have hdegree := ambientDegree_homotopy interpolation region target hopen hbounded
    hjoint hfrontier
  have hzeroDegree := ambientDegree_congr
    (fun point => interpolation (0, point)) id region target hopen hbounded
    (continuousOn_jointField_slice region interpolation hjoint 0) (hfrontier 0)
    (fun point _ => congrFun hzero point)
  have honeDegree := ambientDegree_congr
    (fun point => interpolation (1, point)) field region target hopen hbounded
    (continuousOn_jointField_slice region interpolation hjoint 1) (hfrontier 1)
    (fun point _ => congrFun hone point)
  exact honeDegree.symm.trans (hdegree.symm.trans (hzeroDegree.trans
    (ambientDegree_id_eq_one region target hopen hbounded htarget)))

/-- The degree-one computation supplies an actual source preimage. No
nonempty source, selected root, degree equality or regularity premise is added. -/
theorem exists_preimage_mem_of_eq_identity_on_frontier
    (field : (Fin n → ℝ) → Fin n → ℝ) (region : Set (Fin n → ℝ))
    (target : Fin n → ℝ) (hopen : IsOpen region)
    (hbounded : Bornology.IsBounded region)
    (hfield : ContinuousOn field (closure region)) (htarget : target ∈ region)
    (hfix : ∀ point ∈ frontier region, field point = point) :
    ∃ point ∈ region, field point = target := by
  apply exists_eq_target_of_ambientDegree_ne_zero field region target hopen hbounded hfield
    (frontier_avoids_of_eq_identity field region target hopen htarget hfix)
  rw [ambientDegree_eq_one_of_eq_identity_on_frontier
    field region target hopen hbounded hfield htarget hfix]
  exact one_ne_zero

/-- Every point of a closed ball is hit by a continuous map from that ball
which fixes its sphere. The map's values need not stay in the ball. All radii,
including the empty and singleton boundaries, and dimension zero are allowed. -/
theorem exists_preimage_closedBall_of_eq_on_sphere
    (center : Fin n → ℝ) (radius : ℝ)
    (field : Metric.closedBall center radius → Fin n → ℝ) (hfield : Continuous field)
    (hfix : ∀ point : Metric.closedBall center radius,
      dist (point : Fin n → ℝ) center = radius → field point = point)
    (target : Metric.closedBall center radius) :
    ∃ point : Metric.closedBall center radius, field point = target := by
  classical
  by_cases htarget : (target : Fin n → ℝ) ∈ Metric.ball center radius
  · let source : C(Metric.closedBall center radius, Fin n → ℝ) := ⟨field, hfield⟩
    obtain ⟨extension, hextension⟩ :=
      ContinuousMap.exists_restrict_eq Metric.isClosed_closedBall source
    have hagrees (point : Fin n → ℝ) (hpoint : point ∈ Metric.closedBall center radius) :
        extension point = field ⟨point, hpoint⟩ :=
      congrArg (fun map : C(Metric.closedBall center radius, Fin n → ℝ) =>
        map ⟨point, hpoint⟩) hextension
    have hboundary (point : Fin n → ℝ)
        (hpoint : point ∈ frontier (Metric.ball center radius)) : extension point = point := by
      have hclosed := Metric.closure_ball_subset_closedBall (frontier_subset_closure hpoint)
      rw [hagrees point hclosed]
      exact hfix ⟨point, hclosed⟩ (Metric.mem_sphere.mp
        (Metric.frontier_ball_subset_sphere hpoint))
    obtain ⟨point, hpoint, hvalue⟩ := exists_preimage_mem_of_eq_identity_on_frontier
      extension (Metric.ball center radius) target Metric.isOpen_ball
      Metric.isBounded_ball extension.continuous.continuousOn htarget hboundary
    have hclosed := Metric.ball_subset_closedBall hpoint
    exact ⟨⟨point, hclosed⟩, (hagrees point hclosed).symm.trans hvalue⟩
  · have hnot : ¬dist (target : Fin n → ℝ) center < radius := htarget
    have hequal : dist (target : Fin n → ℝ) center = radius :=
      le_antisymm (Metric.mem_closedBall.mp target.property) (le_of_not_gt hnot)
    exact ⟨target, hfix target hequal⟩

/-- A continuous closed-ball self-map fixing its sphere is surjective,
with no positive-radius or nonzero-dimension restriction. -/
theorem surjective_closedBall_selfMap_of_eq_on_sphere
    (center : Fin n → ℝ) (radius : ℝ)
    (field : Metric.closedBall center radius → Metric.closedBall center radius)
    (hfield : Continuous field)
    (hfix : ∀ point : Metric.closedBall center radius,
      dist (point : Fin n → ℝ) center = radius → field point = point) :
    Function.Surjective field := by
  intro target
  obtain ⟨point, hpoint⟩ := exists_preimage_closedBall_of_eq_on_sphere center radius
    (fun point => (field point : Fin n → ℝ)) (continuous_subtype_val.comp hfield)
    (fun point hpoint => congrArg Subtype.val (hfix point hpoint)) target
  exact ⟨point, Subtype.ext hpoint⟩

end Math.Topology
