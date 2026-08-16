import Literature.Catalog

/-!
# Literature audit

Bibliography label: Ummels 2010

The thesis and its proof-sketch qualification were inspected.
-/

namespace Literature.Papers.Ummels2010

/-- Paper-level coverage record. -/
def record : Literature.PaperRecord where
  paperId := "ummels_2010"
  bibliographyLabel := "Ummels 2010"
  bibliographyLocator := "docs/references/00_BIBLIOGRAPHY.md :: Ummels 2010"
  role := .finiteMemoryAlgorithms
  sourceEvidence := .primaryInspected
  auditStatus := .claimAuditInProgress
  claims :=
    [ { claimId := "finite_memory_nash_and_spe_undecidable"
        sourceLocator := "Theorem 4.13"
        summary := "Finite-memory Nash and subgame-perfect variants are undecidable."
        status := .sourceOnly } ]

end Literature.Papers.Ummels2010
