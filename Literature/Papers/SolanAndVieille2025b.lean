import Literature.Catalog

/-!
# Literature audit

Bibliography label: Solan & Vieille 2025b

This record contains bibliographic coverage and no source-claim
correspondence.
-/

namespace Literature.Papers.SolanAndVieille2025b

/-- Paper-level coverage record. -/
def record : Literature.PaperRecord where
  paperId := "solan_and_vieille_2025b"
  bibliographyLabel := "Solan & Vieille 2025b"
  bibliographyLocator := "docs/references/00_BIBLIOGRAPHY.md :: Solan & Vieille 2025b"
  role := .recentNonzeroSum
  sourceEvidence := .bibliographic
  auditStatus := .catalogued
  claims := []

end Literature.Papers.SolanAndVieille2025b
