import Literature.Catalog

/-!
# Literature audit

Bibliography label: Everett 1957

This record contains bibliographic coverage and no source-claim
correspondence.
-/

namespace Literature.Everett1957

/-- Paper-level coverage record. -/
def record : Literature.PaperRecord where
  paperId := "everett_1957"
  bibliographyLabel := "Everett 1957"
  bibliographyLocator := "docs/references/00_BIBLIOGRAPHY.md :: Everett 1957"
  role := .foundations
  sourceEvidence := .bibliographic
  auditStatus := .catalogued
  claims := []

end Literature.Everett1957
