import Literature.Catalog

/-!
# Literature audit

Bibliography label: Chadha, Sistla & Viswanathan 2013

The theorem role was checked through the later primary paper, not by reading
this paper's proof.
-/

namespace Literature.ChadhaSistlaAndViswanathan2013

/-- Paper-level coverage record. -/
def record : Literature.PaperRecord where
  paperId := "chadha_sistla_and_viswanathan_2013"
  bibliographyLabel := "Chadha, Sistla & Viswanathan 2013"
  bibliographyLocator := "Published source: Chadha, Sistla & Viswanathan 2013"
  role := .zeroSumBoundary
  paperEvidence := .secondaryInspected
  auditStatus := .paperInspected
  claims := []

end Literature.ChadhaSistlaAndViswanathan2013
