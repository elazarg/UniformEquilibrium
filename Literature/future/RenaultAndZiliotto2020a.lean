import Literature.Catalog

/-!
# Literature audit

Bibliography label: Renault & Ziliotto 2020a

This record contains bibliographic coverage and no paper-claim
correspondence.
-/

namespace Literature.RenaultAndZiliotto2020a

/-- Paper-level coverage record. -/
def record : Literature.PaperRecord where
  paperId := "renault_and_ziliotto_2020a"
  bibliographyLabel := "Renault & Ziliotto 2020a"
  bibliographyLocator := "Published source: Renault & Ziliotto 2020a"
  role := .counterexamples
  paperEvidence := .bibliographic
  auditStatus := .catalogued
  claims := []

end Literature.RenaultAndZiliotto2020a
