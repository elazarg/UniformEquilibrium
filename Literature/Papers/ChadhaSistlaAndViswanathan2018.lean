import Literature.Catalog

/-!
# Literature audit

Bibliography label: Chadha, Sistla & Viswanathan 2018

The primary paper supplies the complexity restatements recorded below.
-/

namespace Literature.Papers.ChadhaSistlaAndViswanathan2018

/-- Paper-level coverage record. -/
def record : Literature.PaperRecord where
  paperId := "chadha_sistla_and_viswanathan_2018"
  bibliographyLabel := "Chadha, Sistla & Viswanathan 2018"
  bibliographyLocator := "docs/references/00_BIBLIOGRAPHY.md :: Chadha, Sistla & Viswanathan 2018"
  role := .zeroSumBoundary
  sourceEvidence := .primaryInspected
  auditStatus := .claimAuditInProgress
  claims :=
    [ { claimId := "strict_cutpoint_emptiness_complexity"
        sourceLocator := "Section 2"
        summary := "Strict-cutpoint PFA emptiness is co-r.e.-complete."
        status := .sourceOnly },
      { claimId := "pfa_value_equality_complexity"
        sourceLocator := "Section 2"
        summary := "PFA value equality is Pi-0-2-complete."
        status := .sourceOnly } ]

end Literature.Papers.ChadhaSistlaAndViswanathan2018
