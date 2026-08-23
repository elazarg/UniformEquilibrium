import Literature.Catalog

/-!
# Literature audit

Bibliography label: Le Roux 2014

This record contains bibliographic coverage and no paper-claim
correspondence.
-/

namespace Literature.LeRoux2014

/-- Paper-level coverage record. -/
def record : Literature.PaperRecord where
  paperId := "le_roux_2014"
  bibliographyLabel := "Le Roux 2014"
  bibliographyLocator := "Published source: Le Roux 2014"
  role := .formalization
  paperEvidence := .bibliographic
  auditStatus := .catalogued
  claims := []

end Literature.LeRoux2014
