import Literature.Catalog

/-!
# Literature audit

Bibliography label: Solan & Vieille 2002b

The primary paper supplies the mediated-equilibrium statement below.
-/

namespace Literature.SolanAndVieille2002b

/-- Paper-level coverage record. -/
def record : Literature.PaperRecord where
  paperId := "solan_and_vieille_2002b"
  bibliographyLabel := "Solan & Vieille 2002b"
  bibliographyLocator := "Published source: Solan & Vieille 2002b"
  role := .nonzeroSumExistence
  paperEvidence := .primaryInspected
  auditStatus := .claimAuditInProgress
  claims :=
    [ { claimId := "uniform_autonomous_correlated_equilibrium"
        paperLocator := "Definition 2.2 and Theorem 2.3"
        summary := "Every finite multiplayer stochastic game has the mediated payoff."
        status := .paperOnly } ]

end Literature.SolanAndVieille2002b
