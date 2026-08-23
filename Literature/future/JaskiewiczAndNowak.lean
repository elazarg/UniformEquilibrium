import Literature.Catalog

/-!
# Literature audit

Bibliography label: Jaśkiewicz & Nowak

This record contains bibliographic coverage and no paper-claim
correspondence.
-/

namespace Literature.JaskiewiczAndNowak

/-- Paper-level coverage record. -/
def record : Literature.PaperRecord where
  paperId := "jaskiewicz_and_nowak"
  bibliographyLabel := "Jaśkiewicz & Nowak"
  bibliographyLocator := "Published source: Jaśkiewicz & Nowak"
  role := .surveys
  paperEvidence := .bibliographic
  auditStatus := .catalogued
  claims := []

end Literature.JaskiewiczAndNowak
