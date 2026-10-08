import MathUE.Analysis.BooleanEndpointInterpolation
import GameTheory.Math.Probability.FinDist

/-! # Boolean endpoint expansion of actual independent finite laws

An affine identity for the probabilities of supplied legal laws gives the exact
Boolean endpoint interpolant of every observable. The coordinate weights may be
arbitrary real numbers; no signed weights are used to construct a probability law.
Ambient action types need not be finite, and the finite index type may be empty.
-/

noncomputable section

namespace GameTheory.Math.Probability.FinDist

open scoped BigOperators

variable {ι : Type*} [Fintype ι] {A : ι → Type*}

open Classical in
private theorem prob_pi_eq_endpoint_sum
    (laws : ∀ i, FinDist (A i)) (endpoints : ∀ i, Bool → FinDist (A i))
    (weights : ι → ℝ)
    (haffine : ∀ i action, (laws i).prob action =
      (1 - weights i) * (endpoints i false).prob action +
        weights i * (endpoints i true).prob action)
    (sample : ∀ i, A i) :
    (pi laws).prob sample = ∑ vertex : ι → Bool,
      _root_.Math.booleanEndpointWeight vertex weights *
        (pi (fun i => endpoints i (vertex i))).prob sample := by
  classical
  rw [prob_pi]
  simp_rw [haffine]
  calc
    _ = ∏ i, ∑ bit : Bool,
        (if bit then weights i else 1 - weights i) * (endpoints i bit).prob (sample i) := by
      apply Finset.prod_congr rfl
      intro i _
      rw [Fintype.sum_bool]
      simp only [ite_true, Bool.false_eq_true, ite_false]
      ring
    _ = ∑ vertex : ι → Bool, ∏ i,
        (if vertex i then weights i else 1 - weights i) *
          (endpoints i (vertex i)).prob (sample i) := Fintype.prod_sum _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro vertex _
      rw [Finset.prod_mul_distrib, prob_pi]
      rfl

/-- Actual independent laws with affine coordinate probabilities have precisely
the Boolean endpoint expectation, even for signed coordinate weights. -/
theorem expect_pi_eq_booleanEndpointInterpolant_of_affine_prob
    (laws : ∀ i, FinDist (A i)) (endpoints : ∀ i, Bool → FinDist (A i))
    (weights : ι → ℝ)
    (haffine : ∀ i action, (laws i).prob action =
      (1 - weights i) * (endpoints i false).prob action +
        weights i * (endpoints i true).prob action)
    (test : (∀ i, A i) → ℝ) :
    (pi laws).expect test = _root_.Math.booleanEndpointInterpolant
      (fun vertex => (pi (fun i => endpoints i (vertex i))).expect test) weights := by
  classical
  let endpointLaw (vertex : ι → Bool) := pi (fun i => endpoints i (vertex i))
  let samples := (pi laws).supportFinset ∪
    Finset.univ.biUnion (fun vertex => (endpointLaw vertex).supportFinset)
  have hsource : (pi laws).support ⊆ (samples : Set (∀ i, A i)) := by
    intro sample hsample
    exact Finset.mem_union_left _ (mem_supportFinset.mpr hsample)
  have hendpoint (vertex : ι → Bool) :
      (endpointLaw vertex).support ⊆ (samples : Set (∀ i, A i)) := by
    intro sample hsample
    exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
      ⟨vertex, Finset.mem_univ _, mem_supportFinset.mpr hsample⟩)
  rw [expect_eq_sum_of_subset _ _ samples hsource]
  simp_rw [prob_pi_eq_endpoint_sum laws endpoints weights haffine, Finset.sum_mul]
  rw [Finset.sum_comm]
  unfold _root_.Math.booleanEndpointInterpolant
  apply Finset.sum_congr (by ext vertex; simp)
  intro vertex _
  change (∑ sample ∈ samples,
    (_root_.Math.booleanEndpointWeight vertex weights * (endpointLaw vertex).prob sample) *
      test sample) =
    (endpointLaw vertex).expect test * _root_.Math.booleanEndpointWeight vertex weights
  rw [expect_eq_sum_of_subset _ _ samples (hendpoint vertex), Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro sample _
  ring

end GameTheory.Math.Probability.FinDist
