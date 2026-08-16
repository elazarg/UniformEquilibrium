import Literature.Catalog

/-!
# Literature audit

Bibliography label: Solan 2022

This record contains bibliographic coverage and no source-claim
correspondence.
-/

namespace Literature.Papers.Solan2022

/-- Paper-level coverage record. -/
def record : Literature.PaperRecord where
  paperId := "solan_2022"
  bibliographyLabel := "Solan 2022"
  bibliographyLocator := "docs/references/00_BIBLIOGRAPHY.md :: Solan 2022"
  role := .surveys
  sourceEvidence := .bibliographic
  auditStatus := .catalogued
  claims := []

end Literature.Papers.Solan2022
