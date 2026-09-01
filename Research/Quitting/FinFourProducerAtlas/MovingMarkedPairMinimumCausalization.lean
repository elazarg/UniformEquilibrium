import Research.Quitting.FinFourProducerAtlas.MovingMarkedPairChordMarkedMass
import Research.Quitting.FinFourProducerAtlas.MovingMarkedPairMinimumChordCompactification
import Research.Quitting.SourceFaithfulMinimumLawCausalization

/-!
# Source-faithful causalization of a moving-pair minimum chord

The actual fixed-weight chord family has a uniformly positive atom at its
original marked dates.  The general source-faithful theorem therefore
selects exact cap--Nash words while retaining those literal chord tails and
dates.  The construction remains conditional on the supplied moving family.
-/

noncomputable section

namespace GameTheory

open Filter
open scoped Topology

variable
  {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
  {bound : ℝ} {source : FinFourMinimumAtomProducer reward bound}
  {data : FinFourMovingMarkedPairMinimumSource source}
  {residual : FinFourMovingMarkedPairVanishingResidual data}
  {minimum : FinFourMovingMarkedPairMinimumApproach residual}
  {weight : ℝ} {hweight0 : 0 < weight} {hweight1 : weight < 1}

namespace FinFourMovingMarkedPairMinimumChordCompactification

/-- The compact chord is itself a global minimum. -/
theorem chord_globalMinimum
    (compactification : FinFourMovingMarkedPairMinimumChordCompactification
      minimum weight hweight0 hweight1) :
    ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum compactification.chordPoint.1 ≤
        quittingTerminalSemanticDebtSum candidate := by
  intro candidate hcandidate
  rw [(compactification.target_and_chord_debtSum_eq_source).2]
  exact source.minimum candidate hcandidate

/-- The compact chord realizes the literal global debt infimum. -/
theorem chord_debtSum_eq_inf
    (compactification : FinFourMovingMarkedPairMinimumChordCompactification
      minimum weight hweight0 hweight1) :
    quittingTerminalSemanticDebtSum compactification.chordPoint.1 =
      quittingTerminalDebtSumInf reward := by
  rw [(compactification.target_and_chord_debtSum_eq_source).2,
    source.debt_eq_inf]

/-- Source-faithful causalization of the actual fixed-weight chord family,
at the same composed selector and the original marked dates. -/
theorem nonempty_sourceFaithfulMinimumCausalization
    (compactification : FinFourMovingMarkedPairMinimumChordCompactification
      minimum weight hweight0 hweight1) :
    Nonempty (QuittingSourceFaithfulMinimumCausalization
      compactification.chordPoint data.labels.targetTerminal
      (fun rank ↦ data.chordProfile weight hweight0.le hweight1.le
        (compactification.select rank))
      (fun rank ↦ (data.marked (compactification.select rank)).mark)
      (weight * data.reachFloor)) := by
  apply GameTheory.nonempty_sourceFaithfulMinimumCausalization
  · exact compactification.chordPoint_mem
  · exact compactification.chord_tendsto
  · exact compactification.chord_globalMinimum
  · exact compactification.chord_debtSum_eq_inf
  · exact source.inf_pos
  · exact mul_pos hweight0 data.reachFloor_pos
  · intro rank
    rw [data.chord_stageCoalitionMass_targetTerminal_eq_weight_mul_markedReach]
    exact mul_le_mul_of_nonneg_left
      (data.reachFloor_le (compactification.select rank)) hweight0.le

end FinFourMovingMarkedPairMinimumChordCompactification

end GameTheory
