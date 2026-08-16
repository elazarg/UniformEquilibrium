import Literature.Catalog

/-!
# Literature audit

Bibliography label: Kohlberg 1974

This record contains bibliographic coverage and no source-claim
correspondence.
-/

namespace Literature.Papers.Kohlberg1974

/-- Paper-level coverage record. -/
def record : Literature.PaperRecord where
  paperId := "kohlberg_1974"
  bibliographyLabel := "Kohlberg 1974"
  bibliographyLocator := "docs/references/00_BIBLIOGRAPHY.md :: Kohlberg 1974"
  role := .zeroSumUniformValue
  sourceEvidence := .bibliographic
  auditStatus := .catalogued
  claims := []

end Literature.Papers.Kohlberg1974
