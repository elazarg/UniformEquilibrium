import Literature.Catalog

/-!
# Literature audit

Bibliography label: Renault 2011

This record contains bibliographic coverage and no paper-claim
correspondence.
-/

namespace Literature.Renault2011

/-- Paper-level coverage record. -/
def record : Literature.PaperRecord where
  paperId := "renault_2011"
  bibliographyLabel := "Renault 2011"
  bibliographyLocator := "Published source: Renault 2011"
  role := .zeroSumBoundary
  paperEvidence := .bibliographic
  auditStatus := .catalogued
  claims := []

end Literature.Renault2011
