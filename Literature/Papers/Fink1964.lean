import Literature.Catalog

/-!
# Literature audit

Bibliography label: Fink 1964

This record contains bibliographic coverage and no source-claim
correspondence.
-/

namespace Literature.Papers.Fink1964

/-- Paper-level coverage record. -/
def record : Literature.PaperRecord where
  paperId := "fink_1964"
  bibliographyLabel := "Fink 1964"
  bibliographyLocator := "docs/references/00_BIBLIOGRAPHY.md :: Fink 1964"
  role := .foundations
  sourceEvidence := .bibliographic
  auditStatus := .catalogued
  claims := []

end Literature.Papers.Fink1964
