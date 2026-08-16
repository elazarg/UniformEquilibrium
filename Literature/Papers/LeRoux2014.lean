import Literature.Catalog

/-!
# Literature audit

Bibliography label: Le Roux 2014

This record contains bibliographic coverage and no source-claim
correspondence.
-/

namespace Literature.Papers.LeRoux2014

/-- Paper-level coverage record. -/
def record : Literature.PaperRecord where
  paperId := "le_roux_2014"
  bibliographyLabel := "Le Roux 2014"
  bibliographyLocator := "docs/references/00_BIBLIOGRAPHY.md :: Le Roux 2014"
  role := .formalization
  sourceEvidence := .bibliographic
  auditStatus := .catalogued
  claims := []

end Literature.Papers.LeRoux2014
