import Literature.Catalog

/-!
# Literature audit

Bibliography label: Szczechla, Connell, Filar & Vrieze 1997

This record contains bibliographic coverage and no paper-claim
correspondence.
-/

namespace Literature.SzczechlaConnellFilarAndVrieze1997

/-- Paper-level coverage record. -/
def record : Literature.PaperRecord where
  paperId := "szczechla_connell_filar_and_vrieze_1997"
  bibliographyLabel := "Szczechla, Connell, Filar & Vrieze 1997"
  bibliographyLocator :=
    "Published source: " ++
      "Szczechla, Connell, Filar & Vrieze 1997"
  role := .zeroSumUniformValue
  paperEvidence := .bibliographic
  auditStatus := .catalogued
  claims := []

end Literature.SzczechlaConnellFilarAndVrieze1997
