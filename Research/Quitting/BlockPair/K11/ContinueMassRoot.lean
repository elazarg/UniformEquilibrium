import Research.Quitting.BlockPair.K11.ConditionalData
import UniformEquilibrium.Quitting.Stationary.LiveMass

noncomputable section

namespace GameTheory.BlockPairK11.ConditionalData

open Math.ProbabilityMassFunction

theorem rootOfHazard_continueMass_eq_maskProbability
    (h : Player → ℝ) (h0 : ∀ who, 0 ≤ h who)
    (h1 : ∀ who, h who ≤ 1) :
    quittingStationaryContinueMass (rootOfHazard h h0 h1) =
      BlockPairCharts.maskProbability h 0 := by
  rw [quittingStationaryContinueMass_eq_prod_continueProbability,
    Fin.prod_univ_four]
  simp +decide [rootOfHazard, BlockPairCharts.maskProbability,
    BlockPairCharts.realProduct, BlockPairCharts.actionFactor]

end GameTheory.BlockPairK11.ConditionalData
