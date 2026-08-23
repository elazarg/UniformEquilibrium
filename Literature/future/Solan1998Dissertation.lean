import Literature.Catalog

/-!
# Literature audit

Bibliography label: Solan 1998 (dissertation)

The dissertation was inspected directly for the three-player absorbing-game
statement.
-/

namespace Literature.Solan1998Dissertation

/-- Paper-level coverage record. -/
def record : Literature.PaperRecord where
  paperId := "solan_1998_dissertation"
  bibliographyLabel := "Solan 1998 (dissertation)"
  bibliographyLocator := "Published source: Solan 1998 (dissertation)"
  role := .nonzeroSumExistence
  paperEvidence := .primaryInspected
  auditStatus := .claimAuditInProgress
  claims :=
    [ { claimId := "three_player_absorbing_uniform_equilibrium"
        paperLocator := "Definition 3.9, Theorem 4.23, and the chapter convention"
        summary := "Every three-player absorbing game has a uniform equilibrium payoff."
        status := .paperOnly } ]

end Literature.Solan1998Dissertation
