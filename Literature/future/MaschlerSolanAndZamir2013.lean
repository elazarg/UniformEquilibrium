import Literature.Catalog

/-!
# Literature audit

Bibliography label: Maschler, Solan & Zamir 2013

This record contains bibliographic coverage and no paper-claim
correspondence.
-/

namespace Literature.MaschlerSolanAndZamir2013

/-- Paper-level coverage record. -/
def record : Literature.PaperRecord where
  paperId := "maschler_solan_and_zamir_2013"
  bibliographyLabel := "Maschler, Solan & Zamir 2013"
  bibliographyLocator := "docs/references/00_BIBLIOGRAPHY.md :: Maschler, Solan & Zamir 2013"
  role := .surveys
  paperEvidence := .bibliographic
  auditStatus := .catalogued
  claims := []

end Literature.MaschlerSolanAndZamir2013
