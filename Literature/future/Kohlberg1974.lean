import Literature.Catalog

/-!
# Literature audit

Bibliography label: Kohlberg 1974

This record contains bibliographic coverage and no paper-claim
correspondence.
-/

namespace Literature.Kohlberg1974

/-- Paper-level coverage record. -/
def record : Literature.PaperRecord where
  paperId := "kohlberg_1974"
  bibliographyLabel := "Kohlberg 1974"
  bibliographyLocator := "Published source: Kohlberg 1974"
  role := .zeroSumUniformValue
  paperEvidence := .bibliographic
  auditStatus := .catalogued
  claims := []

end Literature.Kohlberg1974
