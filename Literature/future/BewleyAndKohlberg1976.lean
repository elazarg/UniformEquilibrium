import Literature.Catalog

/-!
# Literature audit

Bibliography label: Bewley & Kohlberg 1976

This record contains bibliographic coverage and no paper-claim
correspondence.
-/

namespace Literature.BewleyAndKohlberg1976

/-- Paper-level coverage record. -/
def record : Literature.PaperRecord where
  paperId := "bewley_and_kohlberg_1976"
  bibliographyLabel := "Bewley & Kohlberg 1976"
  bibliographyLocator := "Published source: Bewley & Kohlberg 1976"
  role := .zeroSumUniformValue
  paperEvidence := .bibliographic
  auditStatus := .catalogued
  claims := []

end Literature.BewleyAndKohlberg1976
