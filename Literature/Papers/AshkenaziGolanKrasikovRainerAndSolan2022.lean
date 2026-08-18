import Literature.Catalog
import UniformEquilibrium.Quitting.Classification.ExistenceBranches
import UniformEquilibrium.Quitting.Classification.LCP.MatrixClasses

/-!
# Literature audit

Bibliography label: Ashkenazi-Golan, Krasikov, Rainer & Solan 2022

O. Ashkenazi-Golan, I. Krasikov, C. Rainer and E. Solan, *Absorption paths and
equilibria in quitting games*, Mathematical Programming (2022),
DOI `10.1007/s10107-022-01807-6`, arXiv:2012.04369.  The published text was
read for Definition 3.1, Theorem 3.4, Theorem 3.5, the absorption-path
sections, and the matrix conditions of Section 5.

## The three branches of Theorem 3.4

Theorem 3.4 characterizes existence of `ε`-equilibria for every `ε > 0` by a
disjunction of three statements, sourced to Simon 2007, Theorem 3, and to
Solan and Vieille 2001.  The branches are stated as propositions in
`UniformEquilibrium/Quitting/Classification/ExistenceBranches.lean`, as
`GameTheory.QuittingStationaryεEquilibriumExistence`,
`GameTheory.QuittingInstantPunishmentεEquilibriumExistence` and
`GameTheory.QuittingSequentiallyεPerfectAbsorbingExistence`.  Those definitions
carry two deliberate deviations, recorded in that file's docstring: the second
fixes the punishment continuation to a constant row, which makes it a
sufficient condition for the source's branch rather than a restatement.  The
characterization itself is not stated in Lean and is recorded below as a
source claim only.

## Printed defects

The paper's sequential-perfection definition for absorption paths tests a
discrete jump only when the post-jump absorption mass is strictly below one,
while the path definition and Remark 4.10 permit a sure terminal jump; the
continuous clause is empty for a sure first-stage example, and Proposition
4.14 and Theorem 4.15 add no terminal optimality test.  No formal statement in
this development consumes the printed path/nonexistence equivalence.
Definition 5.1 and Remark 5.3 carry further printed defects and are not quoted
here; only Definition 5.2 and Remark 5.5(3) are carried into Lean, as
`GameTheory.QuittingLCPClassification.IsProjectiveQBarMatrix` and
`projectiveQMatrix_iff_standard_or_homogeneous` below.
-/

namespace Literature.Papers.AshkenaziGolanKrasikovRainerAndSolan2022

open GameTheory QuittingLCPClassification

variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- **Remark 5.5(3).**  The simplex/projective `Q` convention used by the
quitting-game literature is the union of the textbook `Q` property and the
homogeneous singleton-LCP branch.  The two conventions therefore coincide
exactly after the simple stationary branch has been removed. -/
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
    [ { claimId := "epsilon_perfectness"
        sourceLocator := "Definition 3.1 and Definition 3.2"
        summary :=
          "Epsilon-perfectness of a one-shot profile, borrowed from Solan " ++
          "and Vieille: no action beats the profile's value by more than " ++
          "epsilon, and no action in the support falls short of it by more " ++
          "than epsilon. Sequential epsilon-perfectness applies that test " ++
          "at every stage against the continuation payoff."
        status := .sourceOnly },
      { claimId := "epsilon_equilibrium_characterization"
        sourceLocator := "Theorem 3.4"
        summary :=
          "A quitting game admits an epsilon-equilibrium for every positive " ++
          "epsilon if and only if at least one of S.1, S.2 and S.3 holds."
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
          "one at the first stage and is punished from the second stage on " ++
          "to within epsilon of her min-max level."
        status := .sourceOnly },
      { claimId := "sequentially_perfect_absorbing_branch"
        sourceLocator := "Theorem 3.4, branch S.3"
        summary :=
          "For every sufficiently small positive epsilon there is an " ++
          "absorbing strategy profile at which every player is " ++
          "sequentially epsilon-perfect."
        status := .sourceOnly },
      { claimId := "error_exponent_bound"
        sourceLocator := "Theorem 3.5"
        summary :=
          "The construction's accuracy bound, combining Solan and Vieille " ++
          "Proposition 2.4 with Proposition 2.13, carries the exponent " ++
          "epsilon to the power one sixth."
        status := .sourceOnly },
      { claimId := "absorption_path_equivalence_endpoint_defect"
        sourceLocator := "Definition of sequential perfection for absorption " ++
          "paths, Remark 4.10, Proposition 4.14 and Theorem 4.15"
        summary :=
          "The printed sequential-perfection definition tests a discrete " ++
          "jump only when the post-jump absorption mass is strictly below " ++
          "one, so a sure terminal jump is untested, while the path " ++
          "definition and Remark 4.10 permit one. The printed " ++
          "path/nonexistence equivalence is therefore not used here and no " ++
          "repaired bridge has been proved."
        status := .sourceOnly },
      { claimId := "qbar_matrix_definition"
        sourceLocator := "Definition 5.2"
        summary :=
          "A matrix is a Q-bar matrix when every nonempty principal " ++
          "submatrix is a Q-matrix in the simplex convention. This is " ++
          "GameTheory.QuittingLCPClassification.IsProjectiveQBarMatrix, and " ++
          "it is weaker than the standard completely-Q property."
        status := .sourceOnly },
      { claimId := "projective_q_convention_split"
        sourceLocator := "Remark 5.5(3)"
        summary :=
          "The simplex/projective Q convention is the union of textbook Q " ++
          "and the homogeneous singleton-LCP branch."
        status := .provedInLean
          "Literature.Papers.AshkenaziGolanKrasikovRainerAndSolan2022.\
projectiveQMatrix_iff_standard_or_homogeneous"
          "GameTheory.QuittingLCPClassification.isProjectiveQMatrix_iff_standard_or_homogeneous" },
      { claimId := "qbar_matrix_sufficient_condition"
        sourceLocator := "Theorem 5.4"
        summary :=
          "If the derived matrix is a Q-bar matrix then the quitting game " ++
          "has the continuous-equilibrium structure the section builds."
        status := .sourceOnly } ]

end Literature.Papers.AshkenaziGolanKrasikovRainerAndSolan2022
