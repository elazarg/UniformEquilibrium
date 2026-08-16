import Literature.Catalog

/-!
# Literature audit

Bibliography label: Bewley & Kohlberg 1976b

This record contains bibliographic coverage and no source-claim
correspondence.
-/

namespace Literature.Papers.BewleyAndKohlberg1976b

/-- Paper-level coverage record. -/
def record : Literature.PaperRecord where
  paperId := "bewley_and_kohlberg_1976b"
  bibliographyLabel := "Bewley & Kohlberg 1976b"
  bibliographyLocator := "docs/references/00_BIBLIOGRAPHY.md :: Bewley & Kohlberg 1976b"
  role := .zeroSumUniformValue
  sourceEvidence := .bibliographic
  auditStatus := .catalogued
  claims := []

end Literature.Papers.BewleyAndKohlberg1976b
