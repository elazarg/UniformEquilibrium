import Literature.Catalog

/-!
# Literature audit

Bibliography label: Gillette 1957

This record contains bibliographic coverage and no source-claim
correspondence.
-/

namespace Literature.Papers.Gillette1957

/-- Paper-level coverage record. -/
def record : Literature.PaperRecord where
  paperId := "gillette_1957"
  bibliographyLabel := "Gillette 1957"
  bibliographyLocator := "docs/references/00_BIBLIOGRAPHY.md :: Gillette 1957"
  role := .foundations
  sourceEvidence := .bibliographic
  auditStatus := .catalogued
  claims := []

end Literature.Papers.Gillette1957
