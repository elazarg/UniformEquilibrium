import Literature.Catalog

/-!
# Literature audit

Bibliography label: Mertens, Sorin & Zamir 2015

This record contains bibliographic coverage and no paper-claim
correspondence.
-/

namespace Literature.MertensSorinAndZamir2015

/-- Paper-level coverage record. -/
def record : Literature.PaperRecord where
  paperId := "mertens_sorin_and_zamir_2015"
  bibliographyLabel := "Mertens, Sorin & Zamir 2015"
  bibliographyLocator := "Published source: Mertens, Sorin & Zamir 2015"
  role := .surveys
  paperEvidence := .bibliographic
  auditStatus := .catalogued
  claims := []

end Literature.MertensSorinAndZamir2015
