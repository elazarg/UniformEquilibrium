import Literature.Catalog

/-!
# Literature audit

Bibliography label: Chatterjee, Saona & Ziliotto 2022

The primary paper supplies the paper statements recorded below.
-/

namespace Literature.ChatterjeeSaonaAndZiliotto2022

/-- Paper-level coverage record. -/
def record : Literature.PaperRecord where
  paperId := "chatterjee_saona_and_ziliotto_2022"
  bibliographyLabel := "Chatterjee, Saona & Ziliotto 2022"
  bibliographyLocator := "Published source: Chatterjee, Saona & Ziliotto 2022"
  role := .zeroSumBoundary
  paperEvidence := .primaryInspected
  auditStatus := .claimAuditInProgress
  claims :=
    [ { claimId := "finite_memory_epsilon_optimality"
        paperLocator := "Theorem 2.9"
        summary := "Finite POMDPs admit deterministic finite-memory epsilon-optimal strategies."
        status := .paperOnly },
      { claimId := "uniform_value_identification"
        paperLocator := "Remark 2.1"
        summary := "The long-run value agrees with asymptotic and uniform values."
        status := .paperOnly },
      { claimId := "promised_gap_approximation"
        paperLocator := "Corollary 3.2"
        summary := "The promised-gap approximation problem is recursively enumerable."
        status := .paperOnly } ]

end Literature.ChatterjeeSaonaAndZiliotto2022
