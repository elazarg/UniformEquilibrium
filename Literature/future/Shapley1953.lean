import Literature.Catalog

/-!
# Literature audit

Bibliography label: Shapley 1953

This record contains bibliographic coverage and no source-claim
correspondence.
-/

namespace Literature.Shapley1953

/-- Paper-level coverage record. -/
def record : Literature.PaperRecord where
  paperId := "shapley_1953"
  bibliographyLabel := "Shapley 1953"
  bibliographyLocator := "docs/references/00_BIBLIOGRAPHY.md :: Shapley 1953"
  role := .foundations
  sourceEvidence := .bibliographic
  auditStatus := .catalogued
  claims := []

end Literature.Shapley1953
