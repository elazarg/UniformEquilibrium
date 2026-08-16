import Literature.Catalog
import UniformEquilibrium.Quitting.Terminal.TargetTail.TerminalUniformization

/-!
# Literature audit

Bibliography label: Solan & Vieille 2001

The published paper was inspected directly for the terminal-to-uniform bridge.
-/

namespace Literature.Papers.SolanAndVieille2001

open GameTheory StochasticGame

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Proposition 2.13 in the finite-quitting-game semantics: an
`ε`-terminal Nash profile is a uniform `ε'`-equilibrium whenever `ε < ε'`. -/
theorem terminalNash_isUniformEquilibrium
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    {ε ε' : ℝ} (herror : ε < ε')
    (hnash : (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) ε profile) :
    (quittingGame reward).IsUniformεEquilibrium none ε' profile :=
  quittingGame_isUniformεEquilibrium_of_terminalNash
    reward profile herror hnash

/-- Paper-level coverage record. -/
def record : Literature.PaperRecord where
  paperId := "solan_and_vieille_2001"
  bibliographyLabel := "Solan & Vieille 2001"
  bibliographyLocator := "docs/references/00_BIBLIOGRAPHY.md :: Solan & Vieille 2001"
  role := .nonzeroSumExistence
  sourceEvidence := .primaryInspected
  auditStatus := .claimAuditInProgress
  claims :=
    [ { claimId := "cyclic_subgame_perfect_uniform_equilibrium"
        sourceLocator := "Theorem 1.2"
        summary :=
          "Under A.1 and A.2, every quitting game has cyclic subgame-perfect " ++
          "uniform epsilon-equilibria."
        status := .sourceOnly },
      { claimId := "stationary_or_subgame_perfect_profile"
        sourceLocator := "Proposition 2.4"
        summary :=
          "The constructed profile is subgame-perfect at the stated error, " ++
          "or a stationary equilibrium exists."
        status := .sourceOnly },
      { claimId := "terminal_equilibrium_to_uniform_equilibrium"
        sourceLocator := "Proposition 2.13"
        summary := "An epsilon terminal equilibrium is uniform at every larger error."
        status := .provedInLean
          "Literature.Papers.SolanAndVieille2001.terminalNash_isUniformEquilibrium"
          "GameTheory.quittingGame_isUniformεEquilibrium_of_terminalNash" } ]

end Literature.Papers.SolanAndVieille2001
