import Research.Quitting.FinFourProducerAtlas.MovingMarkedPairResidualAlternative
import UniformEquilibrium.Diagnostics.Quitting.StoppingLaw.Endpoint.ArbitraryClockMinimumActualReachPaidPort
import UniformEquilibrium.Diagnostics.Quitting.StoppingLaw.Endpoint.PaidCapPortExactTrichotomy

/-!
# Public paid-port attachment for an off-minimum moving-pair target

Every selected target in the positive-excess branch is a literal unilateral
replacement descendant of its selected source profile.  The existing
actual-reach theorem therefore supplies a paid first-disagreement row and
the exact paid-cap trichotomy at the original positive global minimum.

This is a branch-local consumer of supplied moving-family data.  It neither
constructs that family nor supplies chronology or renewal.
-/

noncomputable section

namespace GameTheory

variable
  {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
  {bound : ℝ} {source : FinFourMinimumAtomProducer reward bound}
  {data : FinFourMovingMarkedPairMinimumSource source}
  {residual : FinFourMovingMarkedPairVanishingResidual data}

/-- One selected off-minimum moving-pair target and its public actual-reach
paid port. -/
structure FinFourMovingMarkedPairOffMinimumActualReachPaidPort
    (result : FinFourMovingMarkedPairOffMinimumEndpoint residual)
    (M : ℝ) (rank : ℕ) where
  port : QuittingOffMinimumActualReachPaidPort reward data.sourceProfile
    (quittingTerminalSemanticDebtSum source.point.1) M
  port_sourceIndex_eq : port.sourceIndex = result.select rank
  port_target_eq : port.target = data.targetProfile (result.select rank)

/-- Every literal selected target in the positive-excess branch has the
fixed actual-reach paid-port passport. -/
theorem nonempty_finFourMovingMarkedPairOffMinimumActualReachPaidPortAt
    (result : FinFourMovingMarkedPairOffMinimumEndpoint residual)
    (M : ℝ)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (rank : ℕ) :
    Nonempty (FinFourMovingMarkedPairOffMinimumActualReachPaidPort
      result M rank) := by
  have hoff : quittingTerminalSemanticDebtSum source.point.1 <
      quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward
          (data.targetProfile (result.select rank))) := by
    have hstrict : quittingTerminalSemanticDebtSum source.point.1 <
        quittingTerminalSemanticDebtSum source.point.1 + result.excessFloor := by
      linarith [result.excessFloor_pos]
    exact hstrict.trans_le (result.minimum_add_excessFloor_le_targetDebt rank)
  obtain ⟨port, hsourceIndex, htarget⟩ :=
    replacementAncestry_exists_offMinimumActualReachPaidPort
      reward data.sourceProfile
        (quittingTerminalSemanticDebtSum source.point.1) M
        source.minimumDebt_pos hreward (result.select rank)
        (data.targetProfile (result.select rank))
        (result.target_ancestry rank) hoff
  exact ⟨{
    port := port
    port_sourceIndex_eq := hsourceIndex
    port_target_eq := htarget }⟩

namespace FinFourMovingMarkedPairOffMinimumActualReachPaidPort

variable {result : FinFourMovingMarkedPairOffMinimumEndpoint residual}
  {M : ℝ} {rank : ℕ}

/-- Attach the selected paid row to the exact supplied minimum. -/
def capLiftedSource
    (portResult :
      FinFourMovingMarkedPairOffMinimumActualReachPaidPort result M rank) :
    QuittingPaidCapLiftedSource reward where
  minimum := source.point.1
  minimum_le := source.minimum
  minimum_pos := source.minimumDebt_pos
  profile := portResult.port.target
  observer := portResult.port.observer
  gain := quittingTerminalSemanticDebtSum source.point.1 /
    Fintype.card (Fin 4) / 4
  gain_pos := by
    have hcard : (0 : ℝ) < Fintype.card (Fin 4) := by
      exact_mod_cast Fintype.card_pos
    exact div_pos (div_pos source.minimumDebt_pos hcard) (by norm_num)
  row := portResult.port.row

@[simp] theorem capLiftedSource_minimum
    (portResult :
      FinFourMovingMarkedPairOffMinimumActualReachPaidPort result M rank) :
    portResult.capLiftedSource.minimum = source.point.1 := rfl

@[simp] theorem capLiftedSource_profile
    (portResult :
      FinFourMovingMarkedPairOffMinimumActualReachPaidPort result M rank) :
    portResult.capLiftedSource.profile = portResult.port.target := rfl

/-- The selected public paid port feeds the exhaustive, pairwise-disjoint
paid-cap trichotomy. -/
theorem exists_summablePort_exactTrichotomy
    (portResult :
      FinFourMovingMarkedPairOffMinimumActualReachPaidPort result M rank) :
    ∃ capPort : portResult.capLiftedSource.SummablePort,
      (QuittingPaidCapLiftedSource.ChargedNearReturn
          portResult.capLiftedSource capPort ∨
        QuittingPaidCapLiftedSource.QuantitativeDebtDescent
          portResult.capLiftedSource capPort ∨
        QuittingPaidCapLiftedSource.InertStall
          portResult.capLiftedSource capPort) ∧
      ¬(QuittingPaidCapLiftedSource.ChargedNearReturn
          portResult.capLiftedSource capPort ∧
        QuittingPaidCapLiftedSource.QuantitativeDebtDescent
          portResult.capLiftedSource capPort) ∧
      ¬(QuittingPaidCapLiftedSource.ChargedNearReturn
          portResult.capLiftedSource capPort ∧
        QuittingPaidCapLiftedSource.InertStall
          portResult.capLiftedSource capPort) ∧
      ¬(QuittingPaidCapLiftedSource.QuantitativeDebtDescent
          portResult.capLiftedSource capPort ∧
        QuittingPaidCapLiftedSource.InertStall
          portResult.capLiftedSource capPort) := by
  obtain ⟨capPort⟩ :=
    QuittingPaidCapLiftedSource.nonempty_summablePort
      portResult.capLiftedSource
  exact ⟨capPort, portResult.capLiftedSource.exactTrichotomy capPort⟩

end FinFourMovingMarkedPairOffMinimumActualReachPaidPort

end GameTheory
