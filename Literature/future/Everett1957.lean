import Literature.Catalog

/-!
# Literature audit

Bibliography label: Everett 1957

This record contains bibliographic coverage and no paper-claim
correspondence.
-/

namespace Literature.Everett1957

/-- Paper-level coverage record. -/
def record : Literature.PaperRecord where
  paperId := "everett_1957"
  bibliographyLabel := "Everett 1957"
  bibliographyLocator := "Published source: Everett 1957"
  role := .foundations
  paperEvidence := .bibliographic
  auditStatus := .catalogued
  claims := []

end Literature.Everett1957
