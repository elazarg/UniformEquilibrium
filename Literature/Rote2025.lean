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
  bibliographyLocator := "docs/references/00_BIBLIOGRAPHY.md :: Rote 2025"
  role := .zeroSumBoundary
  sourceEvidence := .primaryInspected
  auditStatus := .claimAuditInProgress
  claims :=
    [ { claimId := "fixed_pfa_emptiness_undecidable"
        sourceLocator := "Theorem 1(a)"
        summary := "Strict and weak PFA emptiness are undecidable for a fixed automaton."
        status := .sourceOnly } ]

end Literature.Rote2025
