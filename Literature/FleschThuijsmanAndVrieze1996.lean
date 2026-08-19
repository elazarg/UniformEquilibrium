import Literature.Catalog

/-!
# Literature audit

Bibliography label: Flesch, Thuijsman & Vrieze 1996

This record contains bibliographic coverage and no source-claim
correspondence.
-/

namespace Literature.FleschThuijsmanAndVrieze1996

/-- Paper-level coverage record. -/
def record : Literature.PaperRecord where
  paperId := "flesch_thuijsman_and_vrieze_1996"
  bibliographyLabel := "Flesch, Thuijsman & Vrieze 1996"
  bibliographyLocator := "docs/references/00_BIBLIOGRAPHY.md :: Flesch, Thuijsman & Vrieze 1996"
  role := .nonzeroSumExistence
  sourceEvidence := .bibliographic
  auditStatus := .catalogued
  claims := []

end Literature.FleschThuijsmanAndVrieze1996
