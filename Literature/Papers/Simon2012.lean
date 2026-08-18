import Literature.Catalog

/-!
# Literature audit

Bibliography label: Simon 2012

R. S. Simon, *A topological approach to quitting games*, Mathematics of
Operations Research **37**(1), 180–195 (2012),
DOI `10.1287/moor.1110.0524`.  Only the abstract was read directly, from three
independent DOI-keyed records that agree verbatim.

The paper is cited by Solan and Solan 2020 for the normal/abnormal player
vocabulary, and its own headline result extends the reach of the Solan and
Vieille 2001 existence condition **conditionally**.  Its abstract states that
the paper "presents a question of topological dynamics and demonstrates that
its affirmation would establish the existence of approximate equilibria in all
quitting games with only normal players".  A restatement such as "this result
was extended to a more general class of quitting games by Simon (2012)" reads
as unconditional in isolation and must not be used that way: the paper's own
wording is "would establish", and the four-player and all-normal cases are
declared open.

No claim below has a Lean statement.
-/

namespace Literature.Papers.Simon2012

/-- Paper-level coverage record. -/
def record : Literature.PaperRecord where
  paperId := "simon_2012"
  bibliographyLabel := "Simon 2012"
  bibliographyLocator := "docs/references/00_BIBLIOGRAPHY.md :: Simon 2012"
  role := .nonzeroSumExistence
  sourceEvidence := .abstractInspected
  auditStatus := .claimAuditInProgress
  claims :=
    [ { claimId := "conditional_existence_for_normal_players"
        sourceLocator := "Abstract"
        summary :=
          "The paper poses a question of topological dynamics and shows " ++
          "that an affirmative answer would establish existence of " ++
          "approximate equilibria in all quitting games with only normal " ++
          "players. The existence conclusion is conditional on that " ++
          "unresolved question."
        status := .sourceOnly },
      { claimId := "normal_and_abnormal_player_vocabulary"
        sourceLocator := "Abstract and the definitions it summarizes"
        summary :=
          "The normal and abnormal player vocabulary later used by Solan " ++
          "and Solan 2020 is introduced here. Solan and Solan credit this " ++
          "paper for it and define a normal player as one whose min-max " ++
          "value is nonpositive after the solo-exit normalization."
        status := .sourceOnly },
      { claimId := "four_player_and_all_normal_cases_open"
        sourceLocator := "Abstract and the paper's own statement of scope"
        summary :=
          "The paper declares the four-player case and the all-normal case " ++
          "open, so it does not supply an unconditional extension of the " ++
          "Solan and Vieille 2001 existence theorem."
        status := .sourceOnly } ]

end Literature.Papers.Simon2012
