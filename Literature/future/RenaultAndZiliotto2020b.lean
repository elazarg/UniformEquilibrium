import Literature.Catalog

/-!
# Literature audit

Bibliography label: Renault & Ziliotto 2020b

This record contains bibliographic coverage and no paper-claim
correspondence.
-/

namespace Literature.RenaultAndZiliotto2020b

/-- Paper-level coverage record. -/
def record : Literature.PaperRecord where
  paperId := "renault_and_ziliotto_2020b"
  bibliographyLabel := "Renault & Ziliotto 2020b"
  bibliographyLocator := "Published source: Renault & Ziliotto 2020b"
  role := .counterexamples
  paperEvidence := .bibliographic
  auditStatus := .catalogued
  claims := []

end Literature.RenaultAndZiliotto2020b
