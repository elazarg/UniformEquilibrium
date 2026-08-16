import Literature.Catalog

/-!
# Literature audit

Bibliography label: Simon 2012

This record contains bibliographic coverage and no source-claim
correspondence.
-/

namespace Literature.Papers.Simon2012

/-- Paper-level coverage record. -/
def record : Literature.PaperRecord where
  paperId := "simon_2012"
  bibliographyLabel := "Simon 2012"
  bibliographyLocator := "docs/references/00_BIBLIOGRAPHY.md :: Simon 2012"
  role := .nonzeroSumExistence
  sourceEvidence := .bibliographic
  auditStatus := .catalogued
  claims := []

end Literature.Papers.Simon2012
