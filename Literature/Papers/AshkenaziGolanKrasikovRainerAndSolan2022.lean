import Literature.Catalog
import UniformEquilibrium.Quitting.Classification.ExistenceBranches
import UniformEquilibrium.Quitting.Classification.LCP.MatrixClasses

/-!
# Literature audit

Bibliography label: Ashkenazi-Golan, Krasikov, Rainer & Solan 2022

O. Ashkenazi-Golan, I. Krasikov, C. Rainer and E. Solan, *Absorption paths and
equilibria in quitting games*, Mathematical Programming (2022),
DOI `10.1007/s10107-022-01807-6`, arXiv:2012.04369.  The published text was
read directly for Section 3, the absorption-path definitions of Section 4, and
the matrix conditions of Section 5.

## The three branches of Theorem 3.4

Theorem 3.4 characterizes existence of `ε`-equilibria for every `ε > 0` by a
disjunction of three statements, and is attributed in the paper's own theorem
header to Simon 2007, Theorem 3, together with Solan and Vieille 2001,
Proposition 2.13.  The branches are stated as propositions in
`UniformEquilibrium/Quitting/Classification/ExistenceBranches.lean`, as
`GameTheory.QuittingStationaryεEquilibriumExistence`,
`GameTheory.QuittingInstantPunishmentεEquilibriumExistence` and
`GameTheory.QuittingSequentiallyεPerfectAbsorbingExistence`.  Those definitions
carry two deliberate deviations, recorded in that file's docstring; in
particular the second fixes the punishment continuation to a constant row,
which makes it a sufficient condition for the source's branch rather than a
restatement.  The characterization itself is not stated in Lean and is
recorded below as a source claim only.

`GameTheory.QuittingRowεPerfect` is the one-stage test of Definition 3.1 as
Remark 3.3 specializes it to a quitting game: the quitting and continuing
payoffs are compared against the row's own value `γ_n^i(x)`.  Simon's `E_ε`
compares each used action against the opposite endpoint instead; that form is
`GameTheory.IsSupportPerfectRow`, and it implies this one without being equal
to it.

## Printed defects

Four printed statements need repair before being quoted, and the Lean
interfaces use the repaired forms.

* **Definition 4.13, clause (SP.1)** tests `ε`-perfectness at a discrete jump
  `t` only when `π_t < 1`, so a jump that absorbs the remaining mass is left
  untested; clause (SP.2) covers only the continuous part of the path.
  Theorem 4.15's hypothesis excludes games that possess an `ε`-equilibrium
  terminating surely at the first stage, but not paths carrying such a jump.
  No formal statement in this development consumes the printed
  path/nonexistence equivalence.
* **Definition 5.1** prints the Q-matrix condition as "for every `q ∈ R`"
  where the problem's data is `q ∈ R^n`, and reports the Solan and Solan
  result as "if `R(Γ)` is not a Q-matrix, then `Γ` has a stationary
  0-equilibrium".  The cited theorem is about the principal submatrix on the
  normal players, not the full matrix `R(Γ)`, and concludes a stationary
  `ε`-equilibrium for every positive `ε`, not a `0`-equilibrium.
* **Definition 5.2** defines the `Q̄` property through "all its principal
  minors", but a minor is a determinant and cannot be a Q-matrix; the
  intended object is the principal submatrices, which is what
  `GameTheory.QuittingLCPClassification.IsProjectiveQBarMatrix` quantifies
  over.
* **Remark 5.5(3)** lists the second branch of the simplex convention as the
  existence of a convex combination `Rz` of the columns with `(Rz)_i = 0`
  whenever `z_i > 0`, omitting the nonnegativity `Rz ≥ 0` that Definition
  5.1 imposes through `w ∈ R^n_+`.  Without it the branch is too generous.
  `GameTheory.QuittingLCPClassification.HasHomogeneousSimplexSolution`
  restores the nonnegativity, and the split below is proved in both
  directions where the remark states only one.
-/

namespace Literature.Papers.AshkenaziGolanKrasikovRainerAndSolan2022

open GameTheory QuittingLCPClassification

variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- **Remark 5.5(3), in its repaired form.**  The simplex/projective `Q`
convention used by the quitting-game literature is the union of the textbook
`Q` property and the homogeneous singleton-LCP branch, the latter taken with
the nonnegativity the printed remark omits.  The two conventions therefore
coincide exactly after the simple stationary branch has been removed. -/
theorem projectiveQMatrix_iff_standard_or_homogeneous (M : ι → ι → ℝ) :
    IsProjectiveQMatrix M ↔
      IsStandardQMatrix M ∨ HasHomogeneousSimplexSolution M :=
  isProjectiveQMatrix_iff_standard_or_homogeneous M

/-- Paper-level coverage record. -/
def record : Literature.PaperRecord where
  paperId := "ashkenazi_golan_krasikov_rainer_and_solan_2022"
  bibliographyLabel := "Ashkenazi-Golan, Krasikov, Rainer & Solan 2022"
  bibliographyLocator :=
    "docs/references/00_BIBLIOGRAPHY.md :: " ++
      "Ashkenazi-Golan, Krasikov, Rainer & Solan 2022"
  role := .recentNonzeroSum
  sourceEvidence := .primaryInspected
  auditStatus := .claimAuditInProgress
  claims :=
    [ { claimId := "epsilon_perfectness_in_a_strategic_form_game"
        sourceLocator := "Definition 3.1"
        summary :=
          "A player is epsilon-perfect at a mixed action profile when no " ++
          "action beats the profile's own value by more than epsilon and no " ++
          "action in the support falls below it by more than epsilon."
        status := .sourceOnly },
      { claimId := "sequential_epsilon_perfectness_in_quitting_games"
        sourceLocator := "Definition 3.2 and Remark 3.3"
        summary :=
          "A player is sequentially epsilon-perfect at a strategy profile " ++
          "when, at every stage, she is epsilon-perfect in the one-shot game " ++
          "whose continuation payoff is the profile's own value conditional " ++
          "on survival to the next stage. Remark 3.3 writes the two " ++
          "resulting inequalities out for the quitting and continuing " ++
          "actions."
        status := .sourceOnly },
      { claimId := "epsilon_equilibrium_characterization"
        sourceLocator := "Theorem 3.4"
        summary :=
          "A quitting game admits an epsilon-equilibrium for every positive " ++
          "epsilon if and only if at least one of S.1, S.2 and S.3 holds. " ++
          "The theorem is attributed to Simon 2007 Theorem 3 together with " ++
          "Solan and Vieille 2001 Proposition 2.13."
        status := .sourceOnly },
      { claimId := "stationary_branch"
        sourceLocator := "Theorem 3.4, branch S.1"
        summary :=
          "For every sufficiently small positive epsilon the game admits a " ++
          "stationary epsilon-equilibrium."
        status := .sourceOnly },
      { claimId := "instant_punishment_branch"
        sourceLocator := "Theorem 3.4, branch S.2"
        summary :=
          "For every sufficiently small positive epsilon the game admits an " ++
          "epsilon-equilibrium in which one player quits with probability " ++
          "one at the first stage and, from the second stage on, all players " ++
          "punish her with a payoff epsilon-close to her min-max level."
        status := .sourceOnly },
      { claimId := "sequentially_perfect_absorbing_branch"
        sourceLocator := "Theorem 3.4, branch S.3"
        summary :=
          "For every sufficiently small positive epsilon there is an " ++
          "absorbing strategy profile at which every player is sequentially " ++
          "epsilon-perfect."
        status := .sourceOnly },
      { claimId := "error_exponent_bound"
        sourceLocator := "Theorem 3.5"
        summary :=
          "For sufficiently small positive epsilon, every absorbing profile " ++
          "at which all players are sequentially epsilon-perfect is an " ++
          "epsilon-to-the-one-sixth equilibrium. Attributed to Solan and " ++
          "Vieille 2001, Propositions 2.4 and 2.13."
        status := .sourceOnly },
      { claimId := "absorption_path_sequential_perfectness_endpoint_defect"
        sourceLocator := "Definition 4.13, clause SP.1"
        summary :=
          "The printed clause tests a discrete jump only when the " ++
          "post-jump absorption mass is strictly below one, so a jump that " ++
          "absorbs the remaining mass is untested, while clause SP.2 covers " ++
          "only the continuous part. The repaired form is not supplied here " ++
          "and no statement in this development consumes the printed " ++
          "definition."
        status := .sourceOnly },
      { claimId := "absorption_path_equivalence"
        sourceLocator := "Proposition 4.14 and Theorem 4.15"
        summary :=
          "A limit of sequentially epsilon-perfect absorption paths as " ++
          "epsilon tends to zero is a 0-path, and for a quitting game with " ++
          "neither a sure first-stage-terminating nor an all-continue " ++
          "epsilon-equilibrium, existence of epsilon-equilibria at every " ++
          "positive epsilon is equivalent to existence of a 0-path. The " ++
          "equivalence inherits the Definition 4.13 defect and is not used " ++
          "here."
        status := .sourceOnly },
      { claimId := "linear_complementarity_problem_definition"
        sourceLocator := "Definition 5.1"
        summary :=
          "The simplex form of the linear complementarity problem: find a " ++
          "nonnegative residual and a simplex weight over the columns and " ++
          "the right-hand side that are complementary coordinatewise. The " ++
          "printed text writes q in R rather than R to the n, and misreports " ++
          "the cited Solan and Solan result as giving a stationary " ++
          "0-equilibrium from failure of Q for the full matrix, where the " ++
          "cited theorem concerns the normal-player submatrix and concludes " ++
          "a stationary epsilon-equilibrium at every positive epsilon."
        status := .sourceOnly },
      { claimId := "qbar_matrix_definition"
        sourceLocator := "Definition 5.2"
        summary :=
          "A matrix is a Q-bar matrix when it and all of its principal " ++
          "submatrices are Q-matrices in the simplex convention. The printed " ++
          "text says principal minors, which are determinants and cannot be " ++
          "Q-matrices; the submatrix reading is the one used by " ++
          "GameTheory.QuittingLCPClassification.IsProjectiveQBarMatrix, " ++
          "which is weaker than the standard completely-Q property."
        status := .sourceOnly },
      { claimId := "small_qbar_matrix_characterizations"
        sourceLocator := "Remark 5.3"
        summary :=
          "Explicit characterizations of the Q-bar property for one-by-one, " ++
          "two-by-two and three-by-three matrices, the last by sign " ++
          "structure up to permutation conjugation together with a " ++
          "determinant condition."
        status := .sourceOnly },
      { claimId := "projective_q_convention_split"
        sourceLocator := "Remark 5.5(3)"
        summary :=
          "The simplex Q convention is the union of textbook Q and the " ++
          "homogeneous singleton-LCP branch. The printed second branch omits " ++
          "the nonnegativity of the residual that Definition 5.1 imposes; " ++
          "the checked statement restores it and proves both directions " ++
          "where the remark states only one."
        status := .provedInLean
          "Literature.Papers.AshkenaziGolanKrasikovRainerAndSolan2022.\
projectiveQMatrix_iff_standard_or_homogeneous"
          "GameTheory.QuittingLCPClassification.\
isProjectiveQMatrix_iff_standard_or_homogeneous" },
      { claimId := "qbar_matrix_sufficient_condition"
        sourceLocator := "Theorem 5.4"
        summary :=
          "If the game's solo-quit matrix is a Q-bar matrix then the game " ++
          "admits a continuous equilibrium. Remark 5.5(1) records that the " ++
          "condition is not tight and that the converse is unknown."
        status := .sourceOnly } ]

end Literature.Papers.AshkenaziGolanKrasikovRainerAndSolan2022
