import Literature.Catalog

/-!
# Literature audit

Bibliography label: Solan & Vieille 2025

This record contains bibliographic coverage and no source-claim
correspondence.
-/

namespace Literature.SolanAndVieille2025

/-- Paper-level coverage record. -/
def record : Literature.PaperRecord where
  paperId := "solan_and_vieille_2025"
  bibliographyLabel := "Solan & Vieille 2025"
  bibliographyLocator := "docs/references/00_BIBLIOGRAPHY.md :: Solan & Vieille 2025"
  role := .recentNonzeroSum
  sourceEvidence := .bibliographic
  auditStatus := .catalogued
  claims := []

end Literature.SolanAndVieille2025
