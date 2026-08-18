import Literature.Catalog
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticSmallSurvivorDeletion

/-!
# Literature audit

Bibliography label: Solan 1999

E. Solan, *Three-player absorbing games*, Mathematics of Operations Research
**24**(3), 669–698 (1999), DOI `10.1287/moor.24.3.669`.  The published text is
paywalled and was not obtained; only the abstract is recorded from the source
itself, cross-checked against Crossref metadata.

The abstract's headline word is *undiscounted*, which is a priori weaker than
the uniform notion this development uses.  Three Solan-authored documents
supply the uniform reading for the same theorem: the contemporaneous lecture
chapter Solan 1999b, whose Theorem 2.1 states it for the uniform notion with a
proof sketch; the author's doctoral dissertation, whose Theorem 4.23 carries a
complete proof under a declared global convention that "equilibrium payoff"
means uniform equilibrium payoff; and two restatements in Munk and Solan 2020.
No positivity or sign hypothesis appears in any of them.

Quitting games are the special case of absorbing games in which every player
has two actions, continue and quit, so the theorem covers every three-player
quitting game.  That specialization is proved independently in this
development, from the analytic Bellman germ of the punishment-normalized
auxiliary game rather than from the source's Puiseux-limit argument; the
broader absorbing-game theorem has no Lean statement here.  The restriction to
`n = 3` is the source's: it defines the `n`-player class but proves nothing for
`n ≥ 4`.
-/

namespace Literature.Papers.Solan1999

open GameTheory StochasticGame

/-- **The quitting specialization of the three-player theorem.**  Every finite
quitting game with at most three players has a uniform-equilibrium payoff.
The proof in this development is independent of the source. -/
theorem quittingGame_exists_uniformEquilibriumPayoff_of_card_le_three
    {κ : Type} [Fintype κ] [DecidableEq κ] (hcard : Fintype.card κ ≤ 3)
    (reward : {S : Finset κ // S.Nonempty} → Payoff κ) :
    ∃ payoff : Payoff κ,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff :=
  GameTheory.quittingGame_exists_uniformEquilibriumPayoff_of_card_le_three
    hcard reward

/-- Paper-level coverage record. -/
def record : Literature.PaperRecord where
  paperId := "solan_1999"
  bibliographyLabel := "Solan 1999"
  bibliographyLocator := "docs/references/00_BIBLIOGRAPHY.md :: Solan 1999"
  role := .nonzeroSumExistence
  sourceEvidence := .abstractInspected
  auditStatus := .claimAuditInProgress
  claims :=
    [ { claimId := "three_player_absorbing_undiscounted_equilibrium_payoff"
        sourceLocator := "Abstract"
        summary :=
          "Every three-player absorbing game has an undiscounted " ++
          "equilibrium payoff."
        status := .sourceOnly },
      { claimId := "three_player_absorbing_uniform_equilibrium_payoff"
        sourceLocator :=
          "Abstract, read through Solan 1999b Theorem 2.1 and the author's " ++
          "dissertation Theorem 4.23"
        summary :=
          "The same theorem for the uniform notion, with no positivity or " ++
          "sign hypothesis. The uniform reading is supplied by the author's " ++
          "own contemporaneous exposition and dissertation rather than by " ++
          "the published abstract."
        status := .sourceOnly },
      { claimId := "three_player_quitting_uniform_equilibrium_payoff"
        sourceLocator :=
          "Abstract, specialized to quitting games as in Solan 1999b " ++
          "Section 3"
        summary :=
          "The quitting specialization: every quitting game with at most " ++
          "three players has a uniform-equilibrium payoff. The Lean proof " ++
          "is independent of the source argument."
        status := .provedInLean
          "Literature.Papers.Solan1999.\
quittingGame_exists_uniformEquilibriumPayoff_of_card_le_three"
          "GameTheory.quittingGame_exists_uniformEquilibriumPayoff_of_card_le_three" } ]

end Literature.Papers.Solan1999
