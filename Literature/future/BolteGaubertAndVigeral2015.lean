import Literature.Catalog

/-!
# Literature audit

Bibliography label: Bolte, Gaubert & Vigeral 2015

This record contains bibliographic coverage and no paper-claim
correspondence.
-/

namespace Literature.BolteGaubertAndVigeral2015

/-- Paper-level coverage record. -/
def record : Literature.PaperRecord where
  paperId := "bolte_gaubert_and_vigeral_2015"
  bibliographyLabel := "Bolte, Gaubert & Vigeral 2015"
  bibliographyLocator := "docs/references/00_BIBLIOGRAPHY.md :: Bolte, Gaubert & Vigeral 2015"
  role := .zeroSumBoundary
  paperEvidence := .bibliographic
  auditStatus := .catalogued
  claims := []

end Literature.BolteGaubertAndVigeral2015
