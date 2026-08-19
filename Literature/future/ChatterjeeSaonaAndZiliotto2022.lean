import Literature.Catalog

/-!
# Literature audit

Bibliography label: Chatterjee, Saona & Ziliotto 2022

The primary paper supplies the source statements recorded below.
-/

namespace Literature.ChatterjeeSaonaAndZiliotto2022

/-- Paper-level coverage record. -/
def record : Literature.PaperRecord where
  paperId := "chatterjee_saona_and_ziliotto_2022"
  bibliographyLabel := "Chatterjee, Saona & Ziliotto 2022"
  bibliographyLocator := "docs/references/00_BIBLIOGRAPHY.md :: Chatterjee, Saona & Ziliotto 2022"
  role := .zeroSumBoundary
  sourceEvidence := .primaryInspected
  auditStatus := .claimAuditInProgress
  claims :=
    [ { claimId := "finite_memory_epsilon_optimality"
        sourceLocator := "Theorem 2.9"
        summary := "Finite POMDPs admit deterministic finite-memory epsilon-optimal strategies."
        status := .sourceOnly },
      { claimId := "uniform_value_identification"
        sourceLocator := "Remark 2.1"
        summary := "The long-run value agrees with asymptotic and uniform values."
        status := .sourceOnly },
      { claimId := "promised_gap_approximation"
        sourceLocator := "Corollary 3.2"
        summary := "The promised-gap approximation problem is recursively enumerable."
        status := .sourceOnly } ]

end Literature.ChatterjeeSaonaAndZiliotto2022
