import Research.Quitting.BlockPair.K11.EndpointSemanticZero
import Research.Quitting.BlockPair.K11.EndpointSemanticOne
import Research.Quitting.BlockPair.K11.EndpointSemanticTwo
import Research.Quitting.BlockPair.K11.EndpointSemanticThree

noncomputable section

namespace GameTheory.BlockPairK11.ConditionalData

/-- The quitting-game endpoint difference for the concrete terminal table is
the corresponding four-player predecessor chart.  The four finite expansions
are deliberately compiled in separate dependency shards. -/
theorem endpointDifference_eq_chart
    (h : Player → ℝ) (h0 : ∀ who, 0 ≤ h who)
    (h1 : ∀ who, h who ≤ 1) (tail : Payoff Player) (who : Player) :
    quittingRootEndpointDifference reward tail (rootOfHazard h h0 h1) who =
      BlockPairCharts.difference h tail who := by
  rw [BlockPairCharts.difference_eq_expanded]
  fin_cases who
  · exact endpointDifference_zero_eq_expanded h h0 h1 tail
  · exact endpointDifference_one_eq_expanded h h0 h1 tail
  · exact endpointDifference_two_eq_expanded h h0 h1 tail
  · exact endpointDifference_three_eq_expanded h h0 h1 tail

/-- Phase specialization of `endpointDifference_eq_chart`. -/
theorem phaseRoot_endpointDifference_eq_chart
    (x : HazardIndex → ℝ)
    (hx : ∀ index, 0 < x index ∧ x index < 1)
    (phase : Phase) (tail : Payoff Player) (who : Player) :
    quittingRootEndpointDifference reward tail (phaseRoot x hx phase) who =
      BlockPairCharts.difference (hazard x phase) tail who := by
  exact endpointDifference_eq_chart (hazard x phase)
    (hazard_nonneg x hx phase) (hazard_le_one x hx phase) tail who

end GameTheory.BlockPairK11.ConditionalData
