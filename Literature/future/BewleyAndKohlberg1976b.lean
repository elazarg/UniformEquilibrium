import Literature.Catalog

/-!
# Literature audit

Bibliography label: Bewley & Kohlberg 1976b

This record contains bibliographic coverage and no paper-claim
correspondence.
-/

namespace Literature.BewleyAndKohlberg1976b

/-- Paper-level coverage record. -/
def record : Literature.PaperRecord where
  paperId := "bewley_and_kohlberg_1976b"
  bibliographyLabel := "Bewley & Kohlberg 1976b"
  bibliographyLocator := "Published source: Bewley & Kohlberg 1976b"
  role := .zeroSumUniformValue
  paperEvidence := .bibliographic
  auditStatus := .catalogued
  claims := []

end Literature.BewleyAndKohlberg1976b
