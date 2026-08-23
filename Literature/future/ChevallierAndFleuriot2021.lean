import Literature.Catalog

/-!
# Literature audit

Bibliography label: Chevallier & Fleuriot 2021

This record contains bibliographic coverage and no paper-claim
correspondence.
-/

namespace Literature.ChevallierAndFleuriot2021

/-- Paper-level coverage record. -/
def record : Literature.PaperRecord where
  paperId := "chevallier_and_fleuriot_2021"
  bibliographyLabel := "Chevallier & Fleuriot 2021"
  bibliographyLocator := "Published source: Chevallier & Fleuriot 2021"
  role := .formalization
  paperEvidence := .bibliographic
  auditStatus := .catalogued
  claims := []

end Literature.ChevallierAndFleuriot2021
