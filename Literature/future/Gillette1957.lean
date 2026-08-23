import Literature.Catalog

/-!
# Literature audit

Bibliography label: Gillette 1957

This record contains bibliographic coverage and no paper-claim
correspondence.
-/

namespace Literature.Gillette1957

/-- Paper-level coverage record. -/
def record : Literature.PaperRecord where
  paperId := "gillette_1957"
  bibliographyLabel := "Gillette 1957"
  bibliographyLocator := "Published source: Gillette 1957"
  role := .foundations
  paperEvidence := .bibliographic
  auditStatus := .catalogued
  claims := []

end Literature.Gillette1957
