import Literature.Catalog

/-!
# Literature audit

Bibliography label: Munk & Solan 2020

This record contains bibliographic coverage and no paper-claim
correspondence.
-/

namespace Literature.MunkAndSolan2020

/-- Paper-level coverage record. -/
def record : Literature.PaperRecord where
  paperId := "munk_and_solan_2020"
  bibliographyLabel := "Munk & Solan 2020"
  bibliographyLocator := "Published source: Munk & Solan 2020"
  role := .recentNonzeroSum
  paperEvidence := .bibliographic
  auditStatus := .catalogued
  claims := []

end Literature.MunkAndSolan2020
