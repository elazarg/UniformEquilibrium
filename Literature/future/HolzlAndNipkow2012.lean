import Literature.Catalog

/-!
# Literature audit

Bibliography label: Hölzl & Nipkow 2012

This record contains bibliographic coverage and no paper-claim
correspondence.
-/

namespace Literature.HolzlAndNipkow2012

/-- Paper-level coverage record. -/
def record : Literature.PaperRecord where
  paperId := "holzl_and_nipkow_2012"
  bibliographyLabel := "Hölzl & Nipkow 2012"
  bibliographyLocator := "docs/references/00_BIBLIOGRAPHY.md :: Hölzl & Nipkow 2012"
  role := .formalization
  paperEvidence := .bibliographic
  auditStatus := .catalogued
  claims := []

end Literature.HolzlAndNipkow2012
