import Literature.Catalog
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticSmallSurvivorDeletion

/-!
# Literature audit

Bibliography label: Solan 1999

E. Solan, *Three-player absorbing games*, Mathematics of Operations Research
**24**(3), 669–698 (1999), DOI `10.1287/moor.24.3.669`.  The published text was
read directly, as page images; it is a scan with no usable text layer, so no
statement here comes from an extracted text layer.

## The abstract says "undiscounted"; Definition 3.2 is the uniform notion

The abstract's headline sentence is "We prove that every three-player
absorbing game has an undiscounted equilibrium payoff", and the word *uniform*
appears nowhere in it.  The paper's own Definition 3.2 (p. 673) nevertheless
defines an equilibrium payoff as a vector `g` such that for every `ε > 0`
there are a horizon `t_ε` and a profile `σ_ε` under which every player's
expected average payoff over the first `t` stages is at least `g^i - ε` for
**every** `t > t_ε`, and every unilateral deviation's expected average over
the first `t` stages is at most `g^i + ε` for every `t > t_ε`, together with
the matching `liminf` and `limsup` bounds in the infinite game.

The finite-horizon half of that definition is this development's
`GameTheory.StochasticGame.IsUniformEquilibriumPayoff`: one fixed target,
delivered and deviation-capped over all sufficiently long finite horizons.
The paper's notion is therefore the uniform one, and it is strictly stronger
than the repository's because it also carries the `liminf` and `limsup`
clauses.  No secondary restatement is needed to reach the uniform reading, and
no positivity or sign hypothesis appears in the definition or in the theorem.

## Scope

Quitting games are the absorbing games in which every player has the two
actions continue and quit, so Theorem 3.3 covers every three-player quitting
game.  That specialization is proved independently in this development, from
the analytic Bellman germ of the punishment-normalized auxiliary game rather
than from the paper's vanishing-discount argument, and it delivers only the
finite-horizon half of Definition 3.2.  The broader absorbing-game theorem has
no Lean statement here.  The restriction to three players is the paper's own:
Section 9 exhibits a four-player absorbing game with a convergent sequence of
discounted equilibrium profiles at whose limit mixed action no
`ε`-equilibrium can be built, and the introduction states that existence for
`n ≥ 4` is not known.
-/

namespace Literature.Solan1999

open GameTheory StochasticGame

/-- **The quitting specialization of Theorem 3.3.**  Every finite quitting game
with at most three players has a uniform-equilibrium payoff.  The proof in this
development is independent of the paper, and its conclusion is the
finite-horizon half of the paper's Definition 3.2. -/
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
  bibliographyLocator := "Published source: Solan 1999"
  role := .nonzeroSumExistence
  paperEvidence := .primaryInspected
  auditStatus := .claimAuditInProgress
  claims :=
    [ { claimId := "equilibrium_payoff_is_the_uniform_notion"
        paperLocator := "Definition 3.2"
        summary :=
          "The paper's equilibrium payoff is one fixed target that, at every " ++
          "positive epsilon, some profile delivers to within epsilon over " ++
          "every sufficiently long finite horizon and caps every unilateral " ++
          "deviation by over every such horizon, together with the matching " ++
          "liminf and limsup bounds in the infinite game. This is the " ++
          "uniform notion, not merely the undiscounted one the abstract " ++
          "names."
        status := .paperOnly },
      { claimId := "min_max_value_exists_as_discounted_limit"
        paperLocator := "Definition 4.1 and Lemma 4.2"
        summary :=
          "The min-max value of each player in an absorbing game exists and " ++
          "is the limit of the discounted min-max values."
        status := .paperOnly },
      { claimId := "three_player_absorbing_equilibrium_payoff"
        paperLocator := "Theorem 3.3"
        summary :=
          "Every three-player absorbing game has an equilibrium payoff, in " ++
          "the sense of Definition 3.2."
        status := .paperOnly },
      { claimId := "four_player_limit_action_obstruction"
        paperLocator := "Introduction and Section 9"
        summary :=
          "A four-player absorbing game is exhibited with a convergent " ++
          "sequence of discounted equilibrium profiles at whose limit mixed " ++
          "action no epsilon-equilibrium can be built, and existence for " ++
          "four or more players is stated to be unknown."
        status := .paperOnly },
      { claimId := "three_player_quitting_uniform_equilibrium_payoff"
        paperLocator :=
          "Theorem 3.3, specialized to the two-action continue/quit case"
        summary :=
          "The quitting specialization: every quitting game with at most " ++
          "three players has a uniform-equilibrium payoff. The Lean proof is " ++
          "independent of the paper argument, and its conclusion is the " ++
          "finite-horizon half of Definition 3.2, without the liminf and " ++
          "limsup clauses."
        status := .provedInLean
          "Literature.Solan1999.\
quittingGame_exists_uniformEquilibriumPayoff_of_card_le_three"
          "GameTheory.quittingGame_exists_uniformEquilibriumPayoff_of_card_le_three" } ]

end Literature.Solan1999
