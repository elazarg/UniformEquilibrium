import Literature.Catalog

/-!
# Literature audit

Bibliography label: Simon 2007

R. S. Simon, *The structure of non-zero-sum stochastic games*, Advances in
Applied Mathematics **38**(1), 1–26 (2007),
DOI `10.1016/j.aam.2006.07.002`.  The paper was read from the source PDF as
rendered page images; the text layer drops Greek glyphs silently, so no
statement here comes from an extracted text layer.

Theorem 3 is the source that Ashkenazi-Golan, Krasikov, Rainer and Solan cite
for the three-branch characterization of `ε`-equilibrium existence in quitting
games.  It is stated in Section 4.4 for arbitrary quitting games, before the
topological spanning property of Section 5 is introduced, so it is not scoped
to the escape games of Theorem 4.  Its hypothesis is that the game has neither
stationary nor instant approximate equilibria, which is the negation of the
first two branches.

No claim below has a Lean statement.  The one-stage correspondence `E_ε` of
Section 4.2 compares each used action against the opposite endpoint, and is
written out clause for clause as `GameTheory.IsSupportPerfectRow`
(`UniformEquilibrium/Quitting/Cycles/WeightedRowMotionSeparation.lean`).  The
neighbouring `GameTheory.QuittingRowεPerfect`
(`UniformEquilibrium/Quitting/Classification/ExistenceBranches.lean`) prices
the same comparisons against the mixture value instead, following
Ashkenazi-Golan, Krasikov, Rainer and Solan's Definition 3.1, so the two are
related but not identical.  No theorem in this development states or uses the
correspondence, so it is recorded as a source claim only.
-/

namespace Literature.Papers.Simon2007

/-- Paper-level coverage record. -/
def record : Literature.PaperRecord where
  paperId := "simon_2007"
  bibliographyLabel := "Simon 2007"
  bibliographyLocator := "docs/references/00_BIBLIOGRAPHY.md :: Simon 2007"
  role := .nonzeroSumExistence
  sourceEvidence := .primaryInspected
  auditStatus := .claimAuditInProgress
  claims :=
    [ { claimId := "min_max_value_and_normal_players"
        sourceLocator := "Section 2.3 and Section 4.3"
        summary :=
          "The min-max value chi of a player is the infimum over opponent " ++
          "profiles of that player's best reply value. A player n is normal " ++
          "when the payoff from quitting alone is at least chi."
        status := .sourceOnly },
      { claimId := "one_stage_epsilon_equilibrium_correspondence"
        sourceLocator := "Section 4.2, the correspondences E and F"
        summary :=
          "At a continuation vector r, the set E of admissible one-stage " ++
          "rows is defined by the two support inequalities: a coordinate " ++
          "with positive quit probability gains at most epsilon by " ++
          "continuing, and a coordinate with quit probability below one " ++
          "gains at most epsilon by quitting."
        status := .sourceOnly },
      { claimId := "stationary_and_instant_approximate_equilibria"
        sourceLocator := "Section 4.3, definitions"
        summary :=
          "A quitting game has stationary approximate equilibria when some " ++
          "stationary profile is an epsilon-equilibrium at every positive " ++
          "epsilon, and instant approximate equilibria when at every " ++
          "positive epsilon some player quits surely at the first stage and " ++
          "is punished at the second to no more than her min-max plus " ++
          "epsilon."
        status := .sourceOnly },
      { claimId := "theorem_3_equivalences"
        sourceLocator := "Theorem 3"
        summary :=
          "For a quitting game with neither stationary nor instant " ++
          "approximate equilibria, existence of approximate equilibria is " ++
          "equivalent to each of the following, at every positive epsilon: " ++
          "a cyclic profile each of whose payoff vectors lies in the " ++
          "one-stage image at its successor, is epsilon-rational, and has " ++
          "positive quit mass somewhere in the period; finite orbits of " ++
          "epsilon-rational vectors near the feasible set of arbitrarily " ++
          "large total variation; an infinite orbit of epsilon-rational " ++
          "vectors of unbounded total variation; and the same for extended " ++
          "orbits."
        status := .sourceOnly },
      { claimId := "corollary_2_all_normal_players"
        sourceLocator := "Corollary 2"
        summary :=
          "If in addition every player is normal, the rationality qualifier " ++
          "may be dropped from the orbit condition."
        status := .sourceOnly },
      { claimId := "escape_games_have_approximate_equilibria"
        sourceLocator := "Theorem 4"
        summary :=
          "Every escape game has approximate equilibria. Escape games are " ++
          "defined by normality of all players together with a closed set " ++
          "satisfying a topological spanning property, and the theorem is " ++
          "proved by exhibiting the last condition of Theorem 3."
        status := .sourceOnly },
      { claimId := "conjecture_1_inhomogeneous_variation_bound"
        sourceLocator := "Conjecture 1"
        summary :=
          "The paper conjectures that the expected total variation bound " ++
          "proved for time-homogeneous Markov chains survives without time " ++
          "homogeneity. It is stated as open and is not used by Theorem 3."
        status := .sourceOnly },
      { claimId := "theorem_3_proof_steps_asserted_not_derived"
        sourceLocator :=
          "Theorem 3, proof of the implications from the orbit conditions " ++
          "and from existence of approximate equilibria"
        summary :=
          "Two steps of the proof are asserted rather than derived: the " ++
          "constant relating a total-variation gap to the probability that " ++
          "a quitting action was chosen, and the existence of a stage whose " ++
          "survival probability lands inside a prescribed interval, which " ++
          "needs that per-stage survival cannot jump across that interval. " ++
          "Both are repairable from the surrounding estimates, but neither " ++
          "is certified line by line by the printed text."
        status := .sourceOnly },
      { claimId := "printed_statement_defects"
        sourceLocator := "Lemma 5(2)(a), Lemma 8, and the definition of chi"
        summary :=
          "Three printed statements need repair: Lemma 5(2)(a) bounds a " ++
          "norm using a vector name that is never introduced, where the " ++
          "hypothesis and the proof both name the continuation vector; " ++
          "Lemma 8 repeats one pair where the proof establishes the other; " ++
          "and the min-max definition quantifies over one player index while " ++
          "defining the value for another. None is consumed here."
        status := .sourceOnly } ]

end Literature.Papers.Simon2007
