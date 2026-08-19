import Literature.Catalog

/-!
# Literature audit

Bibliography label: Vrieze & Thuijsman 1989

This record contains bibliographic coverage and no source-claim
correspondence.
-/

namespace Literature.VriezeAndThuijsman1989

/-- Paper-level coverage record. -/
def record : Literature.PaperRecord where
  paperId := "vrieze_and_thuijsman_1989"
  bibliographyLabel := "Vrieze & Thuijsman 1989"
  bibliographyLocator := "docs/references/00_BIBLIOGRAPHY.md :: Vrieze & Thuijsman 1989"
  role := .nonzeroSumExistence
  sourceEvidence := .bibliographic
  auditStatus := .catalogued
  claims := []

end Literature.VriezeAndThuijsman1989
