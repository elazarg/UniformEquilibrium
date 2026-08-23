import Literature.Catalog

/-!
# Literature audit

Bibliography label: Flesch, Thuijsman & Vrieze 1996

This record contains bibliographic coverage and no paper-claim
correspondence.
-/

namespace Literature.FleschThuijsmanAndVrieze1996

/-- Paper-level coverage record. -/
def record : Literature.PaperRecord where
  paperId := "flesch_thuijsman_and_vrieze_1996"
  bibliographyLabel := "Flesch, Thuijsman & Vrieze 1996"
  bibliographyLocator := "Published source: Flesch, Thuijsman & Vrieze 1996"
  role := .nonzeroSumExistence
  paperEvidence := .bibliographic
  auditStatus := .catalogued
  claims := []

end Literature.FleschThuijsmanAndVrieze1996
