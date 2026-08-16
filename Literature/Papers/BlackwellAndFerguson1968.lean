import Literature.Catalog

/-!
# Literature audit

Bibliography label: Blackwell & Ferguson 1968

The primary paper supplies the source statements recorded below. Their
limiting-average criterion is distinct from the later uniform-value notion.
-/

namespace Literature.Papers.BlackwellAndFerguson1968

/-- Paper-level coverage record. -/
def record : Literature.PaperRecord where
  paperId := "blackwell_and_ferguson_1968"
  bibliographyLabel := "Blackwell & Ferguson 1968"
  bibliographyLocator := "docs/references/00_BIBLIOGRAPHY.md :: Blackwell & Ferguson 1968"
  role := .zeroSumUniformValue
  sourceEvidence := .primaryInspected
  auditStatus := .claimAuditInProgress
  claims :=
    [ { claimId := "theorem_1_big_match_value"
        sourceLocator := "Theorem 1"
        summary := "The Big Match has limiting-average value one half."
        status := .sourceOnly },
      { claimId := "player_one_has_no_optimal_strategy"
        sourceLocator := "argument following Theorem 1"
        summary := "Player one has no optimal limiting-average strategy."
        status := .sourceOnly } ]

end Literature.Papers.BlackwellAndFerguson1968
