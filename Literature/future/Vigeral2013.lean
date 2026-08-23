import Literature.Catalog

/-!
# Literature audit

Bibliography label: Vigeral 2013

This record contains bibliographic coverage and no paper-claim
correspondence.
-/

namespace Literature.Vigeral2013

/-- Paper-level coverage record. -/
def record : Literature.PaperRecord where
  paperId := "vigeral_2013"
  bibliographyLabel := "Vigeral 2013"
  bibliographyLocator := "Published source: Vigeral 2013"
  role := .zeroSumBoundary
  paperEvidence := .bibliographic
  auditStatus := .catalogued
  claims := []

end Literature.Vigeral2013
