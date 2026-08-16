import Literature.Catalog

/-!
# Literature audit

Bibliography label: Solan 1998 (dissertation)

The dissertation was inspected directly for the three-player absorbing-game
statement.
-/

namespace Literature.Papers.Solan1998Dissertation

/-- Paper-level coverage record. -/
def record : Literature.PaperRecord where
  paperId := "solan_1998_dissertation"
  bibliographyLabel := "Solan 1998 (dissertation)"
  bibliographyLocator := "docs/references/00_BIBLIOGRAPHY.md :: Solan 1998 (dissertation)"
  role := .nonzeroSumExistence
  sourceEvidence := .primaryInspected
  auditStatus := .claimAuditInProgress
  claims :=
    [ { claimId := "three_player_absorbing_uniform_equilibrium"
        sourceLocator := "Definition 3.9, Theorem 4.23, and the chapter convention"
        summary := "Every three-player absorbing game has a uniform equilibrium payoff."
        status := .sourceOnly } ]

end Literature.Papers.Solan1998Dissertation
