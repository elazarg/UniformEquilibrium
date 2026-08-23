import Literature.Catalog

/-!
# Literature audit

Bibliography label: Solan & Vieille 2015

This record contains bibliographic coverage and no paper-claim
correspondence.
-/

namespace Literature.SolanAndVieille2015

/-- Paper-level coverage record. -/
def record : Literature.PaperRecord where
  paperId := "solan_and_vieille_2015"
  bibliographyLabel := "Solan & Vieille 2015"
  bibliographyLocator := "Published source: Solan & Vieille 2015"
  role := .surveys
  paperEvidence := .bibliographic
  auditStatus := .catalogued
  claims := []

end Literature.SolanAndVieille2015
