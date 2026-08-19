import Literature.Catalog

/-!
# Literature audit

Bibliography label: Thuijsman 2003

This record contains bibliographic coverage and no paper-claim
correspondence.
-/

namespace Literature.Thuijsman2003

/-- Paper-level coverage record. -/
def record : Literature.PaperRecord where
  paperId := "thuijsman_2003"
  bibliographyLabel := "Thuijsman 2003"
  bibliographyLocator := "docs/references/00_BIBLIOGRAPHY.md :: Thuijsman 2003"
  role := .surveys
  paperEvidence := .bibliographic
  auditStatus := .catalogued
  claims := []

end Literature.Thuijsman2003
