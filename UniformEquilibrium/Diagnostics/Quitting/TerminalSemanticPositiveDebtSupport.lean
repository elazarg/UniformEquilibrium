import UniformEquilibrium.Quitting.Root.TerminalSemanticEqualityStratum

/-!
# Positive terminal-semantic debt support

This low module owns the finite set of coordinates with strictly positive
terminal-semantic debt.  It is independent of tangent extraction, stopping-law
chords, source regeneration, and any four-player specialization.
-/

noncomputable section

namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The positive-debt coordinates of a terminal-semantic pair. -/
def quittingPositiveDebtSupport (base : QuittingTerminalSemanticPair ι) : Finset ι :=
  Finset.univ.filter fun who ↦ 0 < quittingTerminalSemanticDebt base who

omit [DecidableEq ι] in
/-- Membership in positive-debt support is strict coordinate debt
positivity. -/
theorem mem_quittingPositiveDebtSupport_iff
    (base : QuittingTerminalSemanticPair ι) (who : ι) :
    who ∈ quittingPositiveDebtSupport base ↔
      0 < quittingTerminalSemanticDebt base who := by
  simp [quittingPositiveDebtSupport]

end GameTheory
