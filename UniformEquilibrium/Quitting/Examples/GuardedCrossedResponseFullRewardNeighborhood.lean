import UniformEquilibrium.Quitting.Examples.GuardedCrossedResponseInverseNeighborhood
import UniformEquilibrium.Quitting.Examples.GuardedCrossedResponseRawNeighborhood
import UniformEquilibrium.Quitting.Stationary.GuardedCrossedResponseHalfCeilingProducer
import UniformEquilibrium.Quitting.Stationary.GuardedCrossedResponseRawProducer

/-!
# Literal sixty-coordinate crossed-response reward neighborhoods

The metric here is the ordinary entrywise Pi sup metric on the entire
nonempty-coalition reward table. Matrix operator norms are confined to the
imported inverse calculation, never used as a reward-table metric. The root
and payoff below are produced for the actual perturbed reward, not retained
from the center. No scalar reward or singleton coordinate is held fixed.
-/

noncomputable section

namespace GameTheory.GuardedCrossedResponseExamples

open QuittingLCPClassification

/-- The exact half reward ball has positive actual determinant/inverse and literal guards. -/
theorem halfCeiling_fullRewardBall_source
    (other : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hclose : dist other halfCeilingReward < 1 / 100) :
    0 < (quittingSingletonMatrix other).det ∧
      (∀ row column, 0 < (quittingSingletonMatrix other)⁻¹ row column) ∧
      QuittingHalfStrictRawGuards other := by
  have hcoordinate : ∀ terminal who,
      |other terminal who - halfCeilingReward terminal who| ≤ dist other halfCeilingReward := by
    intro terminal who
    simpa only [Real.dist_eq] using
      (dist_le_pi_dist (other terminal) (halfCeilingReward terminal) who).trans
        (dist_le_pi_dist other halfCeilingReward terminal)
  obtain ⟨hdet, hinverse, _⟩ := halfCeiling_inverse_neighborhood_of_coordinate_error
    other (dist other halfCeilingReward) hclose hcoordinate
  exact ⟨hdet, hinverse, halfCeiling_strictRawGuards_of_coordinate_error
    other (dist other halfCeilingReward) hclose hcoordinate⟩

/-- The exact unit reward ball has positive actual determinant/inverse and literal guards. -/
theorem unitCeiling_fullRewardBall_source
    (other : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hclose : dist other unitCeilingReward < 1 / 1000) :
    0 < (quittingSingletonMatrix other).det ∧
      (∀ row column, 0 < (quittingSingletonMatrix other)⁻¹ row column) ∧
      QuittingCrossedStrictRawUnitGuards other 0 1 := by
  have hcoordinate : ∀ terminal who,
      |other terminal who - unitCeilingReward terminal who| ≤ dist other unitCeilingReward := by
    intro terminal who
    simpa only [Real.dist_eq] using
      (dist_le_pi_dist (other terminal) (unitCeilingReward terminal) who).trans
        (dist_le_pi_dist other unitCeilingReward terminal)
  obtain ⟨hdet, hinverse, _⟩ := unitCeiling_inverse_neighborhood_of_coordinate_error
    other (dist other unitCeilingReward) hclose hcoordinate
  exact ⟨hdet, hinverse, unitCeiling_strictRawGuards_of_coordinate_error
    other (dist other unitCeilingReward) hclose hcoordinate⟩

/-- Every actual reward in the literal half ball produces its own contracting
stationary behavioral equilibrium and one fixed uniform-equilibrium target. -/
theorem halfCeiling_fullRewardBall_stationaryTerminalNash_uniformPayoff
    (other : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hclose : dist other halfCeilingReward < 1 / 100) :
    ∃ root : Fin 4 → PMF Bool, ∃ value : Payoff (Fin 4),
      0 < hazardOfRoot root 0 ∧ hazardOfRoot root 0 < 1 / 2 ∧
      0 < hazardOfRoot root 1 ∧ hazardOfRoot root 1 < 1 / 2 ∧
      (∃ outsider, outsider ≠ 0 ∧ outsider ≠ 1 ∧ 0 < hazardOfRoot root outsider) ∧
      value = quittingTerminalPayoff other (quittingStationaryProfile other root) ∧
      (∀ who, quittingStationaryFixedOpponentsContinueMass root who < 1) ∧
      (quittingGame other).IsεAsymptoticNash
        (quittingTerminalPayoff other) 0 (quittingStationaryProfile other root) ∧
      (quittingGame other).IsUniformEquilibriumPayoff none value := by
  obtain ⟨hdet, hinverse, hraw⟩ := halfCeiling_fullRewardBall_source other hclose
  exact exists_guardedCrossed_stationaryTerminalNash_uniformPayoff_of_halfStrictRaw
    other hdet hinverse hraw

/-- Every actual reward in the literal unit ball produces its own contracting
stationary behavioral equilibrium and one fixed uniform-equilibrium target. -/
theorem unitCeiling_fullRewardBall_stationaryTerminalNash_uniformPayoff
    (other : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hclose : dist other unitCeilingReward < 1 / 1000) :
    ∃ root : Fin 4 → PMF Bool, ∃ value : Payoff (Fin 4),
      0 < hazardOfRoot root 0 ∧ hazardOfRoot root 0 < 1 ∧
      0 < hazardOfRoot root 1 ∧ hazardOfRoot root 1 < 1 ∧
      (∃ outsider, outsider ≠ 0 ∧ outsider ≠ 1 ∧ 0 < hazardOfRoot root outsider) ∧
      value = quittingTerminalPayoff other (quittingStationaryProfile other root) ∧
      (∀ who, quittingStationaryFixedOpponentsContinueMass root who < 1) ∧
      (quittingGame other).IsεAsymptoticNash
        (quittingTerminalPayoff other) 0 (quittingStationaryProfile other root) ∧
      (quittingGame other).IsUniformEquilibriumPayoff none value := by
  obtain ⟨hdet, hinverse, hraw⟩ := unitCeiling_fullRewardBall_source other hclose
  exact exists_guardedCrossed_stationaryTerminalNash_uniformPayoff_of_strictRawUnit
    other 0 1 (by decide) hdet hinverse hraw

end GameTheory.GuardedCrossedResponseExamples
