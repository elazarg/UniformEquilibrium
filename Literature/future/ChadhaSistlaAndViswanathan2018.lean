import Literature.Catalog

/-!
# Literature audit

Bibliography label: Chadha, Sistla & Viswanathan 2018

The primary paper supplies the complexity restatements recorded below.
-/

namespace Literature.ChadhaSistlaAndViswanathan2018

/-- Paper-level coverage record. -/
def record : Literature.PaperRecord where
  paperId := "chadha_sistla_and_viswanathan_2018"
  bibliographyLabel := "Chadha, Sistla & Viswanathan 2018"
  bibliographyLocator := "Published source: Chadha, Sistla & Viswanathan 2018"
  role := .zeroSumBoundary
  paperEvidence := .primaryInspected
  auditStatus := .claimAuditInProgress
  claims :=
    [ { claimId := "strict_cutpoint_emptiness_complexity"
        paperLocator := "Section 2"
        summary := "Strict-cutpoint PFA emptiness is co-r.e.-complete."
        status := .paperOnly },
      { claimId := "pfa_value_equality_complexity"
        paperLocator := "Section 2"
        summary := "PFA value equality is Pi-0-2-complete."
        status := .paperOnly } ]

end Literature.ChadhaSistlaAndViswanathan2018
