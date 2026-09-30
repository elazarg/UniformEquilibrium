import MathUE.LinearProgramming.R0AmbientDegree
import UniformEquilibrium.Quitting.Classification.LCP.ThreeCore.PassiveRowFourDegreeNeighborhood

/-!
# Intrinsic degree one for the literal passive-row fixture and its open class

The field is the packet's literal homogeneous minimum map, with target zero.
The intrinsic operation on every bounded open neighborhood of the origin
equals one. The existing exact support calculation and strict passive-row
neighborhood are reused, without repeating their inventories or inferring
quitting equilibrium from degree one alone.
-/

noncomputable section

namespace GameTheory.PassiveRowFourDegreeNeighborhood

open Set Filter Math.Topology Math.LinearProgramming
open scoped _root_.Topology

/-- The literal packet matrix has intrinsic homogeneous minimum-map degree one
on every bounded open neighborhood of its unique zero. -/
theorem ambientDegree_eq_one
    (region : Set (Fin 4 → ℝ)) (hopen : IsOpen region)
    (hbounded : Bornology.IsBounded region) (horigin : 0 ∈ region) :
    ambientDegree (lcpMinMap matrix 0) region 0 hopen hbounded
      (continuous_lcpMinMap matrix 0).continuousOn
      (lcpMinMap_zero_ne_zero_on_frontier_of_isR0Matrix
        matrix isR0Matrix region hopen horigin) = 1 :=
  (ambientDegree_lcpMinMap_zero_eq_r0Degree
    matrix isR0Matrix region hopen hbounded horigin).trans r0Degree_eq_one

/-- The same zero-diagonal matrix neighborhood has intrinsic degree one and
the existing strict child-inverse/outside-row properties. -/
theorem eventually_ambient_degree_one_and_strict_passive_rows :
    ∀ᶠ other : Matrix (Fin 4) (Fin 4) ℝ in 𝓝 matrix,
      (∀ who, other who who = 0) →
      ∃ hR0 : IsR0Matrix other,
        (∀ (region : Set (Fin 4 → ℝ)) (hopen : IsOpen region)
          (hbounded : Bornology.IsBounded region) (horigin : 0 ∈ region),
          ambientDegree (lcpMinMap other 0) region 0 hopen hbounded
            (continuous_lcpMinMap other 0).continuousOn
            (lcpMinMap_zero_ne_zero_on_frontier_of_isR0Matrix
              other hR0 region hopen horigin) = 1) ∧
        HasStrictlyPositiveInverse (selectedPrincipal other) ∧
        ∀ column, 0 < selectedOutsideWeight other column := by
  filter_upwards [eventually_degree_one_and_strict_passive_rows] with other hother hdiagonal
  obtain ⟨hR0, hdegree, hinverse, houtside⟩ := hother hdiagonal
  refine ⟨hR0, ?_, hinverse, houtside⟩
  intro region hopen hbounded horigin
  exact (ambientDegree_lcpMinMap_zero_eq_r0Degree
    other hR0 region hopen hbounded horigin).trans hdegree

/-- A full reward-table open neighborhood realizes the packet's intrinsic
degree-one claim, while retaining its strict passive-row hypotheses. -/
theorem exists_open_reward_ambient_degree_one_neighborhood :
    ∃ neighborhood : Set Reward,
      IsOpen neighborhood ∧ centerReward ∈ neighborhood ∧
      ∀ reward ∈ neighborhood,
        ∃ hR0 : IsR0Matrix (singletonMatrix reward),
          (∀ (region : Set (Fin 4 → ℝ)) (hopen : IsOpen region)
            (hbounded : Bornology.IsBounded region) (horigin : 0 ∈ region),
            ambientDegree (lcpMinMap (singletonMatrix reward) 0) region 0 hopen hbounded
              (continuous_lcpMinMap (singletonMatrix reward) 0).continuousOn
              (lcpMinMap_zero_ne_zero_on_frontier_of_isR0Matrix
                (singletonMatrix reward) hR0 region hopen horigin) = 1) ∧
          HasStrictlyPositiveInverse (selectedPrincipal (singletonMatrix reward)) ∧
          ∀ column, 0 < selectedOutsideWeight (singletonMatrix reward) column := by
  obtain ⟨neighborhood, hopen, hcenter, hall⟩ := exists_open_reward_neighborhood
  refine ⟨neighborhood, hopen, hcenter, ?_⟩
  intro reward hreward
  obtain ⟨hR0, hdegree, hinverse, houtside⟩ := hall reward hreward
  refine ⟨hR0, ?_, hinverse, houtside⟩
  intro region hregionOpen hbounded horigin
  exact (ambientDegree_lcpMinMap_zero_eq_r0Degree
    (singletonMatrix reward) hR0 region hregionOpen hbounded horigin).trans hdegree

/-- One open class has both intrinsic degree one and a fixed uniform-equilibrium
payoff. The payoff still comes from strict passive rows, not degree one alone. -/
theorem exists_open_ambient_degree_one_uniformPayoff_class :
    ∃ neighborhood : Set Reward,
      IsOpen neighborhood ∧ centerReward ∈ neighborhood ∧
      ∀ reward ∈ neighborhood,
        (∃ hR0 : IsR0Matrix (singletonMatrix reward),
          ∀ (region : Set (Fin 4 → ℝ)) (hopen : IsOpen region)
            (hbounded : Bornology.IsBounded region) (horigin : 0 ∈ region),
            ambientDegree (lcpMinMap (singletonMatrix reward) 0) region 0 hopen hbounded
              (continuous_lcpMinMap (singletonMatrix reward) 0).continuousOn
              (lcpMinMap_zero_ne_zero_on_frontier_of_isR0Matrix
                (singletonMatrix reward) hR0 region hopen horigin) = 1) ∧
        ∃ target, (quittingGame reward).IsUniformEquilibriumPayoff none target := by
  obtain ⟨neighborhood, hopen, hcenter, hall⟩ := exists_open_degree_one_uniformPayoff_class
  refine ⟨neighborhood, hopen, hcenter, ?_⟩
  intro reward hreward
  obtain ⟨⟨hR0, hdegree⟩, hpayoff⟩ := hall reward hreward
  refine ⟨⟨hR0, ?_⟩, hpayoff⟩
  intro region hregionOpen hbounded horigin
  exact (ambientDegree_lcpMinMap_zero_eq_r0Degree
    (singletonMatrix reward) hR0 region hregionOpen hbounded horigin).trans hdegree

end GameTheory.PassiveRowFourDegreeNeighborhood
