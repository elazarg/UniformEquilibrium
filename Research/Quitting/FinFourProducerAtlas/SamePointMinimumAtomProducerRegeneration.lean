import Research.Quitting.FinFourProducerAtlas.Source
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticLawCarrierCausalization

/-! # Same-point minimum-atom producer regeneration -/

noncomputable section

namespace GameTheory

/-- Repackage any same-fibre positive-law point as a new minimum source while
retaining the exact hard residual and displayed law coordinate. -/
def FinFourMinimumAtomProducer.regeneratedAtLawPoint
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound : ℝ}
    (source : FinFourMinimumAtomProducer reward bound)
    (point : QuittingTerminalSemanticLawPoint (Fin 4))
    (terminal : {S : Finset (Fin 4) // S.Nonempty})
    (hpoint : point ∈ quittingTerminalSemanticLawCarrier reward)
    (hdebt : quittingTerminalSemanticDebtSum point.1 =
      quittingTerminalSemanticDebtSum source.point.1)
    (hmass : 0 < point.2 (some terminal)) :
    FinFourMinimumAtomProducer reward bound := by
  let atom : QuittingMinimumLawCausalSuffixAtom reward point := {
    terminal := terminal
    terminalMass_pos := hmass
    chronology :=
      exists_deep_nearMinimum_capNashChronologies_with_causalSuffixAtom
        reward point terminal hpoint hmass source.inf_pos
          (hdebt.trans source.debt_eq_inf)
  }
  exact {
    residual := source.residual
    point := point
    point_mem := hpoint
    semantic_mem := terminalSemanticLawCarrier_fst_mem_carrier point hpoint
    minimum := by
      intro candidate hcandidate
      rw [hdebt]
      exact source.minimum candidate hcandidate
    inf_pos := source.inf_pos
    debt_eq_inf := hdebt.trans source.debt_eq_inf
    atom := atom
  }

end GameTheory

