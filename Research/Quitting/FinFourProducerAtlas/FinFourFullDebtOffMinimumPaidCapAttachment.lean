import Research.Quitting.FinFourProducerAtlas.FinFourFullDebtOffMinimumActualReachPaidPort
import UniformEquilibrium.Diagnostics.Quitting.StoppingLaw.Endpoint.PaidCapPortExactTrichotomy

/-!
# Paid-cap attachment for a strict full-debt target

The actual paid row selected from a strict cap-band target is attached to the
existing paid-cap prefix construction using exactly the supplied source
minimum.  This is a branch-local consumer; it does not select another minimum
or assert renewal, a terminal conclusion, or equilibrium.
-/

noncomputable section

namespace GameTheory

namespace FinFourFullDebtOffMinimumActualReachPaidPort

variable
  {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
  {bound M : ℝ} {source : FinFourMinimumAtomProducer reward bound}
  {base : FinFourFullDebtCapBandTargetCompactification source M}

/-- The paid row is attached to the exact original minimum, not to an
independently selected positive minimum. -/
def capLiftedSource
    (result : FinFourFullDebtOffMinimumActualReachPaidPort base) :
    QuittingPaidCapLiftedSource reward where
  minimum := source.point.1
  minimum_le := source.minimum
  minimum_pos := source.minimumDebt_pos
  profile := result.port.target
  observer := result.port.observer
  gain := quittingTerminalSemanticDebtSum source.point.1 /
    Fintype.card (Fin 4) / 4
  gain_pos := by
    have hcard : (0 : ℝ) < Fintype.card (Fin 4) := by
      exact_mod_cast Fintype.card_pos
    exact div_pos (div_pos source.minimumDebt_pos hcard) (by norm_num)
  row := result.port.row

@[simp] theorem capLiftedSource_minimum
    (result : FinFourFullDebtOffMinimumActualReachPaidPort base) :
    result.capLiftedSource.minimum = source.point.1 := rfl

@[simp] theorem capLiftedSource_profile
    (result : FinFourFullDebtOffMinimumActualReachPaidPort base) :
    result.capLiftedSource.profile = result.port.target := rfl

/-- The existing exact paid-cap trichotomy applies to a summable port whose
minimum is literally the supplied full-debt source minimum. -/
theorem exists_summablePort_exactTrichotomy
    (result : FinFourFullDebtOffMinimumActualReachPaidPort base) :
    ∃ capPort : result.capLiftedSource.SummablePort,
      (QuittingPaidCapLiftedSource.ChargedNearReturn
          result.capLiftedSource capPort ∨
        QuittingPaidCapLiftedSource.QuantitativeDebtDescent
          result.capLiftedSource capPort ∨
        QuittingPaidCapLiftedSource.InertStall
          result.capLiftedSource capPort) ∧
      ¬(QuittingPaidCapLiftedSource.ChargedNearReturn
          result.capLiftedSource capPort ∧
        QuittingPaidCapLiftedSource.QuantitativeDebtDescent
          result.capLiftedSource capPort) ∧
      ¬(QuittingPaidCapLiftedSource.ChargedNearReturn
          result.capLiftedSource capPort ∧
        QuittingPaidCapLiftedSource.InertStall
          result.capLiftedSource capPort) ∧
      ¬(QuittingPaidCapLiftedSource.QuantitativeDebtDescent
          result.capLiftedSource capPort ∧
        QuittingPaidCapLiftedSource.InertStall
          result.capLiftedSource capPort) := by
  obtain ⟨capPort⟩ :=
    QuittingPaidCapLiftedSource.nonempty_summablePort result.capLiftedSource
  exact ⟨capPort, result.capLiftedSource.exactTrichotomy capPort⟩

end FinFourFullDebtOffMinimumActualReachPaidPort

end GameTheory
