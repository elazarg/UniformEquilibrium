import Literature.Catalog

/-!
# Literature audit

Bibliography label: Blackwell & Ferguson 1968

The primary paper supplies the paper statements recorded below. Their
limiting-average criterion is distinct from the later uniform-value notion.
-/

namespace Literature.BlackwellAndFerguson1968

/-- Paper-level coverage record. -/
def record : Literature.PaperRecord where
  paperId := "blackwell_and_ferguson_1968"
  bibliographyLabel := "Blackwell & Ferguson 1968"
  bibliographyLocator := "docs/references/00_BIBLIOGRAPHY.md :: Blackwell & Ferguson 1968"
  role := .zeroSumUniformValue
  paperEvidence := .primaryInspected
  auditStatus := .claimAuditInProgress
  claims :=
    [ { claimId := "theorem_1_big_match_value"
        paperLocator := "Theorem 1"
        summary := "The Big Match has limiting-average value one half."
        status := .paperOnly },
      { claimId := "player_one_has_no_optimal_strategy"
        paperLocator := "argument following Theorem 1"
        summary := "Player one has no optimal limiting-average strategy."
        status := .paperOnly } ]

end Literature.BlackwellAndFerguson1968
