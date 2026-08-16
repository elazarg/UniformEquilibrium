import Literature.Catalog

/-!
# Literature audit

Bibliography label: Thuijsman 2003

This record contains bibliographic coverage and no source-claim
correspondence.
-/

namespace Literature.Papers.Thuijsman2003

/-- Paper-level coverage record. -/
def record : Literature.PaperRecord where
  paperId := "thuijsman_2003"
  bibliographyLabel := "Thuijsman 2003"
  bibliographyLocator := "docs/references/00_BIBLIOGRAPHY.md :: Thuijsman 2003"
  role := .surveys
  sourceEvidence := .bibliographic
  auditStatus := .catalogued
  claims := []

end Literature.Papers.Thuijsman2003
