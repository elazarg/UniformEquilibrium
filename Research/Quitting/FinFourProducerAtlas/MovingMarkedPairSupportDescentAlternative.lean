import Research.Quitting.FinFourProducerAtlas.MovingMarkedPairOffMinimumPaidPort
import Research.Quitting.FinFourProducerAtlas.MovingMarkedPairSupportContractedRenewal

/-!
# Exhaustive supplied moving-pair support-descent alternative

This is the result-facing compiler for a supplied moving marked-pair family.
It returns a uniformly positive premark-residual paid port, a vanishing-
residual off-minimum paid-port family, or a regenerated strict-support child
with its renewable trace.  Every selection remains explicit in the branch
data constructed by the preceding modules.

This theorem does not construct the moving family.  Its renewable terminal
exit is not a Nash--Bellman consumer and no uniform equilibrium is asserted.
-/

noncomputable section

namespace GameTheory

variable
  {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
  {bound : ℝ} {source : FinFourMinimumAtomProducer reward bound}
  {moving : FinFourMovingMarkedPairMinimumSource source}

/-- The full selected off-minimum family, with a public actual-reach paid port
at every displayed rank. -/
structure FinFourMovingMarkedPairOffMinimumPaidPortFamily
    {residual : FinFourMovingMarkedPairVanishingResidual moving}
    (result : FinFourMovingMarkedPairOffMinimumEndpoint residual)
    (M : ℝ) where
  paidPort : ∀ rank : ℕ,
    FinFourMovingMarkedPairOffMinimumActualReachPaidPort result M rank

/-- Construct the paid-port family without changing the selected profiles or
their common selector. -/
theorem nonempty_finFourMovingMarkedPairOffMinimumPaidPortFamily
    {residual : FinFourMovingMarkedPairVanishingResidual moving}
    (result : FinFourMovingMarkedPairOffMinimumEndpoint residual)
    (M : ℝ)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M) :
    Nonempty (FinFourMovingMarkedPairOffMinimumPaidPortFamily result M) := by
  let paidPort : ∀ rank : ℕ,
      FinFourMovingMarkedPairOffMinimumActualReachPaidPort result M rank :=
    fun rank ↦ Classical.choice
      (nonempty_finFourMovingMarkedPairOffMinimumActualReachPaidPortAt
        result M hreward rank)
  exact ⟨⟨paidPort⟩⟩

/-- Exhaustive output of the supplied moving-pair compiler.  The weight is a
fixed interior stopping-law chord parameter, not a correlated profile mix. -/
inductive FinFourMovingMarkedPairSupportDescentAlternative
    (moving : FinFourMovingMarkedPairMinimumSource source)
    (M weight : ℝ) (hweight0 : 0 < weight) (hweight1 : weight < 1) : Type
  | positiveResidual
      (result : FinFourMovingMarkedPairPositiveResidual moving M)
  | offMinimum
      (residual : FinFourMovingMarkedPairVanishingResidual moving)
      (result : FinFourMovingMarkedPairOffMinimumEndpoint residual)
      (ports : FinFourMovingMarkedPairOffMinimumPaidPortFamily result M)
  | supportDescent
      (residual : FinFourMovingMarkedPairVanishingResidual moving)
      (minimum : FinFourMovingMarkedPairMinimumApproach residual)
      (compactification :
        FinFourMovingMarkedPairMinimumChordCompactification
          minimum weight hweight0 hweight1)
      (common : FinFourMovingMarkedPairCommonPrefixResponse compactification)
      (renewal : FinFourMovingMarkedPairSupportContractedRenewal common)

/-- Every supplied moving marked-pair family has one of the three literal
paid-port/support-descent outputs. -/
theorem nonempty_finFourMovingMarkedPairSupportDescentAlternative
    (moving : FinFourMovingMarkedPairMinimumSource source)
    (M weight : ℝ)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hweight0 : 0 < weight) (hweight1 : weight < 1) :
    Nonempty (FinFourMovingMarkedPairSupportDescentAlternative
      moving M weight hweight0 hweight1) := by
  obtain ⟨precompact⟩ :=
    nonempty_finFourMovingMarkedPairPrecompactAlternative moving M hreward
  cases precompact with
  | positiveResidual result =>
      exact ⟨.positiveResidual result⟩
  | offMinimum residual result =>
      obtain ⟨ports⟩ :=
        nonempty_finFourMovingMarkedPairOffMinimumPaidPortFamily
          result M hreward
      exact ⟨.offMinimum residual result ports⟩
  | minimumApproach residual minimum =>
      obtain ⟨compactification⟩ :=
        nonempty_finFourMovingMarkedPairMinimumChordCompactification
          minimum weight hweight0 hweight1
      obtain ⟨common⟩ :=
        nonempty_finFourMovingMarkedPairCommonPrefixResponse compactification
      obtain ⟨renewal⟩ :=
        nonempty_finFourMovingMarkedPairSupportContractedRenewal common
      exact ⟨.supportDescent residual minimum compactification common renewal⟩

end GameTheory
