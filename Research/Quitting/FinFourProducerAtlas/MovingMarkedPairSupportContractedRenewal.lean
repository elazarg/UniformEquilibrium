import Research.Quitting.FinFourProducerAtlas.MovingMarkedPairSameResidualSupportDescent
import Research.Quitting.FinFourProducerAtlas.SupportContractedRenewal

/-!
# Renewable trace after a moving-pair support contraction

The moving-pair construction supplies one strict-support edge into a
same-residual regenerated minimum source.  This thin adapter retains that
edge separately and starts the generic renewable trace at the regenerated
source.  Its descent count therefore records only later renewable children.

The theorem remains conditional on the supplied moving marked-pair family.
It neither constructs that family nor turns the renewal terminal exit into a
uniform equilibrium.
-/

noncomputable section

namespace GameTheory

variable
  {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
  {bound : ℝ} {source : FinFourMinimumAtomProducer reward bound}
  {moving : FinFourMovingMarkedPairMinimumSource source}
  {residual : FinFourMovingMarkedPairVanishingResidual moving}
  {minimum : FinFourMovingMarkedPairMinimumApproach residual}
  {weight : ℝ} {hweight0 : 0 < weight} {hweight1 : weight < 1}
  {compactification :
    FinFourMovingMarkedPairMinimumChordCompactification
      minimum weight hweight0 hweight1}
  {common : FinFourMovingMarkedPairCommonPrefixResponse compactification}

/-- The one-use edge into the strict-support target.  It is not counted as a
renewable descent. -/
structure FinFourMovingMarkedPairSupportContractionEdge
    (compactification : FinFourMovingMarkedPairMinimumChordCompactification
      minimum weight hweight0 hweight1)
    (point : QuittingTerminalSemanticLawPoint (Fin 4)) : Prop where
  point_eq : point = compactification.targetPoint
  strictSupport :
    quittingPositiveDebtSupport point.1 ⊂
      quittingPositiveDebtSupport compactification.chordPoint.1

/-- Renewable output after the separately retained moving-pair entry edge. -/
structure FinFourMovingMarkedPairSupportContractedRenewal
    (common : FinFourMovingMarkedPairCommonPrefixResponse compactification) where
  descent : FinFourMovingMarkedPairSameResidualSupportDescent common
  renewalInput : FinFourSupportContractedRenewalInput source
    compactification.targetPoint
      (FinFourMovingMarkedPairSupportContractionEdge compactification)
  renewalInput_target_eq : renewalInput.target = descent.regeneration.next
  renewal : FinFourSupportContractedRenewalResult renewalInput

namespace FinFourMovingMarkedPairSupportContractedRenewal

/-- The initial moving-pair edge remains a strict support contraction. -/
theorem incoming_strictSupport
    (renewal : FinFourMovingMarkedPairSupportContractedRenewal common) :
    quittingPositiveDebtSupport compactification.targetPoint.1 ⊂
      quittingPositiveDebtSupport compactification.chordPoint.1 := by
  exact renewal.renewal.incoming.strictSupport

/-- At most two further strict-support descents occur after the initial
moving-pair edge. -/
theorem furtherDescentCount_le_two
    (renewal : FinFourMovingMarkedPairSupportContractedRenewal common) :
    renewal.renewal.trace.descentCount ≤ 2 :=
  renewal.renewal.furtherDescentCount_le_two

/-- The terminal descendant retains the original hard residual. -/
theorem terminalResidual_eq_source
    (renewal : FinFourMovingMarkedPairSupportContractedRenewal common) :
    renewal.renewal.terminalNode.source.residual = source.residual :=
  renewal.renewal.terminalResidual_eq_origin

end FinFourMovingMarkedPairSupportContractedRenewal

/-- A regenerated moving-pair strict-support child starts the generic
renewable trace with at most two later descents. -/
theorem nonempty_finFourMovingMarkedPairSupportContractedRenewal
    (common : FinFourMovingMarkedPairCommonPrefixResponse compactification) :
    Nonempty (FinFourMovingMarkedPairSupportContractedRenewal common) := by
  obtain ⟨descent⟩ :=
    nonempty_finFourMovingMarkedPairSameResidualSupportDescent common
  let edge : FinFourMovingMarkedPairSupportContractionEdge compactification
      compactification.targetPoint := {
    point_eq := rfl
    strictSupport := descent.strictSupport
  }
  let input : FinFourSupportContractedRenewalInput source
      compactification.targetPoint
        (FinFourMovingMarkedPairSupportContractionEdge compactification) := {
    incoming := edge
    target := descent.regeneration.next
    target_point_eq := descent.regenerated_point_eq
    target_residual_eq_origin := descent.regenerated_residual_eq
    targetSupport_card_le_three := descent.targetSupport_card_le_three
  }
  obtain ⟨renewal⟩ := nonempty_finFourSupportContractedRenewalResult input
  exact ⟨{
    descent := descent
    renewalInput := input
    renewalInput_target_eq := rfl
    renewal := renewal
  }⟩

end GameTheory
