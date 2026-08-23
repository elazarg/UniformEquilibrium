import Literature.Catalog

/-!
# Literature audit

Bibliography label: Rote 2025

The primary paper supplies the fixed-automaton undecidability statement below.
-/

namespace Literature.Rote2025

/-- Paper-level coverage record. -/
def record : Literature.PaperRecord where
  paperId := "rote_2025"
  bibliographyLabel := "Rote 2025"
  bibliographyLocator := "Published source: Rote 2025"
  role := .zeroSumBoundary
  paperEvidence := .primaryInspected
  auditStatus := .claimAuditInProgress
  claims :=
    [ { claimId := "fixed_pfa_emptiness_undecidable"
        paperLocator := "Theorem 1(a)"
        summary := "Strict and weak PFA emptiness are undecidable for a fixed automaton."
        status := .paperOnly } ]

end Literature.Rote2025
