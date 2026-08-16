import Literature.Catalog

/-!
# Literature audit

Bibliography label: Solan & Vieille 2001

The published paper was inspected directly for the terminal-to-uniform bridge.
-/

namespace Literature.Papers.SolanAndVieille2001

/-- Paper-level coverage record. -/
def record : Literature.PaperRecord where
  paperId := "solan_and_vieille_2001"
  bibliographyLabel := "Solan & Vieille 2001"
  bibliographyLocator := "docs/references/00_BIBLIOGRAPHY.md :: Solan & Vieille 2001"
  role := .nonzeroSumExistence
  sourceEvidence := .primaryInspected
  auditStatus := .claimAuditInProgress
  claims :=
    [ { claimId := "terminal_equilibrium_to_uniform_equilibrium"
        sourceLocator := "Proposition 2.13"
        summary := "An epsilon terminal equilibrium is uniform at every larger error."
        status := .sourceOnly } ]

end Literature.Papers.SolanAndVieille2001
