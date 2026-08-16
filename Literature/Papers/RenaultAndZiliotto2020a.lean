import Literature.Catalog

/-!
# Literature audit

Bibliography label: Renault & Ziliotto 2020a

This record contains bibliographic coverage and no source-claim
correspondence.
-/

namespace Literature.Papers.RenaultAndZiliotto2020a

/-- Paper-level coverage record. -/
def record : Literature.PaperRecord where
  paperId := "renault_and_ziliotto_2020a"
  bibliographyLabel := "Renault & Ziliotto 2020a"
  bibliographyLocator := "docs/references/00_BIBLIOGRAPHY.md :: Renault & Ziliotto 2020a"
  role := .counterexamples
  sourceEvidence := .bibliographic
  auditStatus := .catalogued
  claims := []

end Literature.Papers.RenaultAndZiliotto2020a
