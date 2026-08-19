import Literature.Catalog

/-!
# Literature audit

Bibliography label: Mertens, Sorin & Zamir 2015

This record contains bibliographic coverage and no source-claim
correspondence.
-/

namespace Literature.MertensSorinAndZamir2015

/-- Paper-level coverage record. -/
def record : Literature.PaperRecord where
  paperId := "mertens_sorin_and_zamir_2015"
  bibliographyLabel := "Mertens, Sorin & Zamir 2015"
  bibliographyLocator := "docs/references/00_BIBLIOGRAPHY.md :: Mertens, Sorin & Zamir 2015"
  role := .surveys
  sourceEvidence := .bibliographic
  auditStatus := .catalogued
  claims := []

end Literature.MertensSorinAndZamir2015
