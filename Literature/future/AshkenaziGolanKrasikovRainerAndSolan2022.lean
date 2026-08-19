import Literature.Catalog
import UniformEquilibrium.Quitting.Classification.ErrorExponentRefutation
import UniformEquilibrium.Quitting.Classification.TableExistenceBranches
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
Proposition 2.13.  The
characterization itself is not stated in Lean and is recorded below as a claim
of the paper with no Lean statement.

Those definitions carry two presentation choices, recorded in that file's
docstring.  The second branch fixes the punishment continuation to a constant
row where the paper leaves it an arbitrary behavior profile; the two existence
statements agree, so the
constant-row form is used as the canonical one and the paper form is derived
from it.

The three definitions also fix the payoff of never terminating to zero, where
the paper's model allows an arbitrary `r(C)`.  The branches over the paper's
model are stated in
`UniformEquilibrium/Quitting/Classification/TableExistenceBranches.lean` over
`GameTheory.QuittingLCPClassification.QuittingPayoffTable`, and each is
equivalent to the zero-never branch at the playerwise translated reward
`GameTheory.QuittingLCPClassification.QuittingPayoffTable.zeroNeverReward`.
The zero-never statements are therefore the normalized case by theorem and not
by convention.

The three branches are written out below, over a terminal reward and a
nontermination payoff, as `StationaryBranch`, `InstantPunishmentBranch` and
`SequentiallyPerfectAbsorbingBranch`, each with the equivalence theorem
identifying it with its payoff-table form.

`GameTheory.QuittingRowεPerfect` is the one-stage test of Definition 3.1 as
Remark 3.3 specializes it to a quitting game: the quitting and continuing
payoffs are compared against the row's own value `γ_n^i(x)`.  Simon's `E_ε`
compares each used action against the opposite endpoint instead; that form is
`GameTheory.IsSupportPerfectRow`, and it implies this one without being equal
to it.

## Printed defects

Five printed statements need repair before being quoted, and the Lean
interfaces use the repaired forms.

* **Theorem 3.5** is false as stated.  It concludes that every absorbing
  sequentially `ε`-perfect profile is an `ε ^ (1 / 6)`-equilibrium, dropping
  the stationary alternative of the result it cites, Solan and Vieille 2001,
  Proposition 2.4, restated there as Proposition 2.6.  The printed statement is
  written out below as `ErrorExponentBound` and its negation is
  `not_errorExponentBound`; the witness is the two-player game of
  `UniformEquilibrium/Quitting/Boundary/Repair/LocalGlobalCounterexample.lean`,
  packaged as the constant absorbing root sequence
  `GameTheory.localGlobalCounterexampleRoots`, whose rows are exactly
  `0`-perfect and whose generated profile has terminal regret one.  The
  disjunctive 2001 form is written out as
  `ErrorExponentStationaryAlternative`; no proof of it is supplied here, and it
  is not refuted by the same witness, whose game satisfies its stationary
  disjunct exactly.
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

namespace Literature.AshkenaziGolanKrasikovRainerAndSolan2022

open GameTheory QuittingLCPClassification

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## Section 3: the paper's payoff model

Section 3 lets a quitting game pay an arbitrary vector `r(C)` when nobody ever
quits, where the repository model pays zero.  The claims below therefore carry
a terminal reward `r` and that nontermination payoff as separate data.  A play
always means a behavior profile of `GameTheory.quittingGame`, whose states,
actions and transitions do not depend on either payoff, and approximate
equilibrium always means
`GameTheory.StochasticGame.IsεAsymptoticNash` for the payoff functional named
in the claim.
-/

/-- **The paper's expected payoff of a play.**  Each absorbed state `S` pays
`r(S)` weighted by its limiting absorption mass, and the mass that never
absorbs pays `r(C)`. -/
noncomputable def paperPayoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (never : Payoff ι) (profile : (quittingGame reward).BehaviorProfile)
    (who : ι) : ℝ :=
  (∑ S : {S : Finset ι // S.Nonempty},
      quittingAbsorbedMassLimit reward profile S * reward S who) +
    (1 - ∑ S : {S : Finset ι // S.Nonempty},
        quittingAbsorbedMassLimit reward profile S) * never who

/-- Nothing distinguishes the paper's model from the repository payoff table
whose terminal rewards are `r` and whose never payoff is `r(C)`: the two agree
at every profile and player.  The branches below may therefore be stated with
`paperPayoff` and still be reached by the payoff-table adapters. -/
theorem paperPayoff_eq_terminalPayoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (never : Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι) :
    paperPayoff reward never profile who =
      QuittingPayoffTable.terminalPayoff ⟨reward, never⟩ profile who := rfl

/-- What branch `S.2` means by a best-reply value, unfolded: the supremum of
the paper's payoff over all of one player's behavior replies to a fixed
opponent plan.  The suprema exist because the payoffs are bounded by the
table's reward bound. -/
theorem bestReplyValue_eq_iSup_paperPayoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (never : Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι) :
    QuittingPayoffTable.bestReplyValue ⟨reward, never⟩ profile who =
      ⨆ deviation : (quittingGame reward).BehaviorStrategy who,
        paperPayoff reward never
          (Function.update profile who deviation) who := rfl

/-- What branch `S.2` means by a min-max, unfolded: the infimum of those
best-reply values over all opponent plans, history-dependent ones included.
Neither the infimum nor the suprema are claimed to be attained. -/
theorem punishmentValue_eq_iInf_bestReplyValue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (never : Payoff ι)
    (who : ι) :
    QuittingPayoffTable.punishmentValue ⟨reward, never⟩ who =
      ⨅ alternative : (quittingGame reward).BehaviorProfile,
        QuittingPayoffTable.bestReplyValue ⟨reward, never⟩ alternative who :=
  rfl

/-! ## Section 3: the three branches of Theorem 3.4 -/

/-- **Theorem 3.4, branch S.1.**  At every positive tolerance some product row,
played after every history, is a terminal approximate equilibrium of the
paper's model at that tolerance.

Open: neither this branch nor the characterization is proved here. -/
def StationaryBranch (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (never : Payoff ι) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ root : ι → PMF Bool,
    (quittingGame reward).IsεAsymptoticNash (paperPayoff reward never) ε
      (quittingStationaryProfile reward root)

/-- The audited branch and the development's payoff-table branch
`QuittingPayoffTable.StationaryεEquilibriumExistence` are one statement, not
two that happen to agree: the proof is `rfl`, so no reading of the paper is
interposed between them.  Consequently
`QuittingPayoffTable.stationaryεEquilibriumExistence_iff` carries the audited
branch to the zero-never reward, where the repository states `S.1`. -/
theorem stationaryBranch_iff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (never : Payoff ι) :
    StationaryBranch reward never ↔
      QuittingPayoffTable.StationaryεEquilibriumExistence ⟨reward, never⟩ :=
  Iff.rfl

/-- **Theorem 3.4, branch S.2.**  At every positive tolerance there are a
player who quits with probability one at the first stage, a first-stage row
prescribing that, and a continuation profile played from the second stage on
holding that player within the tolerance of its min-max, such that the splice
is a terminal approximate equilibrium at that tolerance.

The punishment continuation is an arbitrary behavior profile, as in the paper.
`bestReplyValue_eq_iSup_paperPayoff` and
`punishmentValue_eq_iInf_bestReplyValue` write the two values out.

Open: neither this branch nor the characterization is proved here. -/
def InstantPunishmentBranch (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (never : Payoff ι) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ (quitter : ι) (root : ι → PMF Bool)
      (punish : (quittingGame reward).BehaviorProfile),
    root quitter = PMF.pure true ∧
      QuittingPayoffTable.bestReplyValue ⟨reward, never⟩ punish quitter ≤
        QuittingPayoffTable.punishmentValue ⟨reward, never⟩ quitter + ε ∧
      (quittingGame reward).IsεAsymptoticNash (paperPayoff reward never) ε
        (quittingRootThenContinuationProfile reward root punish)

/-- The audited branch and the development's payoff-table branch
`QuittingPayoffTable.InstantPunishmentεEquilibriumExistence` are one statement,
by `rfl`.  This is what makes the arbitrary punishment continuation audited
here answerable by the repository's constant-row branch:
`QuittingPayoffTable.instantPunishmentεEquilibriumExistence_iff` composes the
zero-never reduction with the shape equivalence
`GameTheory.quittingInstantPunishmentεEquilibriumExistence_iff_profilePunishment`. -/
theorem instantPunishmentBranch_iff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (never : Payoff ι) :
    InstantPunishmentBranch reward never ↔
      QuittingPayoffTable.InstantPunishmentεEquilibriumExistence
        ⟨reward, never⟩ :=
  Iff.rfl

/-- **Theorem 3.4, branch S.3.**  At every positive tolerance there is a
completely absorbing sequence of product rows whose row at each stage is
`ε`-perfect against the continuation vector that the sequence itself pays from
the next stage on.

`GameTheory.QuittingRowεPerfect` is the one-stage test of Definition 3.1 as
Remark 3.3 specializes it, and `GameTheory.IsCompletelyAbsorbing` is the
vanishing of the survival product, the paper's `P_x(θ < ∞) = 1`.

Open: neither this branch nor the characterization is proved here. -/
def SequentiallyPerfectAbsorbingBranch
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (never : Payoff ι) :
    Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ roots : ℕ → ι → PMF Bool,
    IsCompletelyAbsorbing roots ∧
      ∀ time : ℕ, QuittingRowεPerfect reward
        (fun who => paperPayoff reward never
          (quittingRootSequenceProfile reward roots (time + 1)) who)
        (roots time) ε

/-- The audited branch and the development's payoff-table branch
`QuittingPayoffTable.SequentiallyεPerfectAbsorbingExistence` are one statement,
by `rfl`.  The continuation vector audited here is the paper's own, so
`QuittingPayoffTable.sequentiallyεPerfectAbsorbingExistence_iff` may translate
both the rewards and that vector by the never payoff at once and land on the
zero-never form. -/
theorem sequentiallyPerfectAbsorbingBranch_iff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (never : Payoff ι) :
    SequentiallyPerfectAbsorbingBranch reward never ↔
      QuittingPayoffTable.SequentiallyεPerfectAbsorbingExistence
        ⟨reward, never⟩ :=
  Iff.rfl

/-! ## Section 3: Theorem 3.5 and the alternative its restatement dropped -/

/-- **Theorem 3.5 as printed.**  Every finite quitting game has a positive
threshold below which the following holds at every tolerance `ε`: whenever a
completely absorbing sequence of product rows has every row `ε`-perfect against
the continuation vector the sequence pays from the next stage on, the profile
it generates is a terminal `ε ^ (1 / 6)`-equilibrium.

The nontermination payoff is zero here, as in the paper's Section 3 statement
of Theorem 3.5. -/
def ErrorExponentBound : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι]
      (reward : {S : Finset ι // S.Nonempty} → Payoff ι),
    ∃ bound : ℝ, 0 < bound ∧
      ∀ ε : ℝ, 0 < ε → ε < bound →
        ∀ roots : ℕ → ι → PMF Bool, IsCompletelyAbsorbing roots →
          (∀ time : ℕ, QuittingRowεPerfect reward
              (quittingRootSequenceTailVector reward roots (time + 1))
              (roots time) ε) →
            (quittingGame reward).IsεAsymptoticNash
              (quittingTerminalPayoff reward) (ε ^ ((1 : ℝ) / 6))
              (quittingRootSequenceProfile reward roots 0)

/-- The printed bound and the development's
`GameTheory.QuittingSequentialPerfectionErrorExponent` are one statement, by
`rfl`.  `not_errorExponentBound` refutes the audited claim by transporting the
development's negation across this identification, so what is refuted is the
printed statement at the strength the paper gives it, not a strengthening of
it chosen to be refutable. -/
theorem errorExponentBound_iff :
    ErrorExponentBound ↔ QuittingSequentialPerfectionErrorExponent :=
  Iff.rfl

/-- **Theorem 3.5 as printed is false.**  The printed statement drops the
stationary alternative of the result it cites, Solan and Vieille 2001,
Proposition 2.4, restated there as Proposition 2.6.  The two-player witness
`GameTheory.localGlobalCounterexampleRoots` absorbs at its first stage, is
exactly `0`-perfect at every stage, and has terminal regret one. -/
theorem not_errorExponentBound : ¬ ErrorExponentBound :=
  fun hbound =>
    not_quittingSequentialPerfectionErrorExponent
      (errorExponentBound_iff.1 hbound)

/-- **The disjunctive form Theorem 3.5 dropped**, from Solan and Vieille 2001,
Propositions 2.4 and 2.6: under the hypotheses of `ErrorExponentBound`, either
the generated profile is a terminal `ε ^ (1 / 6)`-equilibrium, or the game has
a stationary terminal approximate equilibrium at every positive tolerance.

Open: no proof of the disjunction is supplied here.  It is not refuted by the
witness that refutes `ErrorExponentBound`, whose game satisfies the second
disjunct exactly. -/
def ErrorExponentStationaryAlternative : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι]
      (reward : {S : Finset ι // S.Nonempty} → Payoff ι),
    ∃ bound : ℝ, 0 < bound ∧
      ∀ ε : ℝ, 0 < ε → ε < bound →
        ∀ roots : ℕ → ι → PMF Bool, IsCompletelyAbsorbing roots →
          (∀ time : ℕ, QuittingRowεPerfect reward
              (quittingRootSequenceTailVector reward roots (time + 1))
              (roots time) ε) →
            (quittingGame reward).IsεAsymptoticNash
                (quittingTerminalPayoff reward) (ε ^ ((1 : ℝ) / 6))
                (quittingRootSequenceProfile reward roots 0) ∨
              ∀ tolerance : ℝ, 0 < tolerance → ∃ root : ι → PMF Bool,
                (quittingGame reward).IsεAsymptoticNash
                  (quittingTerminalPayoff reward) tolerance
                  (quittingStationaryProfile reward root)

/-- The disjunctive form audited here and the development's
`GameTheory.QuittingSequentialPerfectionStationaryAlternative` are one
statement, by `rfl`, so the proposition this record leaves open is the one the
development leaves open.  Its second disjunct is what separates it from
`ErrorExponentBound`: the game refuting that claim satisfies the disjunct
exactly, by
`GameTheory.quittingStationaryεEquilibriumExistence_localGlobalCounterexampleReward`. -/
theorem errorExponentStationaryAlternative_iff :
    ErrorExponentStationaryAlternative ↔
      QuittingSequentialPerfectionStationaryAlternative :=
  Iff.rfl

/-! ## Section 5: the matrix conditions -/

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
          "stationary epsilon-equilibrium. Stated over the paper's model, " ++
          "in which never terminating pays an arbitrary r(C). The " ++
          "playerwise translation adapter " ++
          "QuittingPayoffTable.stationaryεEquilibriumExistence_iff " ++
          "reduces it to the zero-never form " ++
          "GameTheory.QuittingStationaryεEquilibriumExistence."
        status := .openInLean
          "Literature.AshkenaziGolanKrasikovRainerAndSolan2022.\
StationaryBranch" },
      { claimId := "instant_punishment_branch"
        sourceLocator := "Theorem 3.4, branch S.2"
        summary :=
          "For every sufficiently small positive epsilon the game admits an " ++
          "epsilon-equilibrium in which one player quits with probability " ++
          "one at the first stage and, from the second stage on, all players " ++
          "punish her with a payoff epsilon-close to her min-max level. The " ++
          "punishment continuation is an arbitrary behavior profile; " ++
          "restricting it to a constant row leaves the existence " ++
          "statement unchanged, by " ++
          "GameTheory.quittingInstantPunishmentεEquilibriumExistence_iff_profilePunishment."
        status := .openInLean
          "Literature.AshkenaziGolanKrasikovRainerAndSolan2022.\
InstantPunishmentBranch" },
      { claimId := "sequentially_perfect_absorbing_branch"
        sourceLocator := "Theorem 3.4, branch S.3"
        summary :=
          "For every sufficiently small positive epsilon there is an " ++
          "absorbing strategy profile at which every player is sequentially " ++
          "epsilon-perfect. Stated over root sequences and over the paper's " ++
          "model's payoff table. The playerwise translation adapter " ++
          "QuittingPayoffTable.sequentiallyεPerfectAbsorbingExistence_iff " ++
          "reduces it to the zero-never form."
        status := .openInLean
          "Literature.AshkenaziGolanKrasikovRainerAndSolan2022.\
SequentiallyPerfectAbsorbingBranch" },
      { claimId := "error_exponent_bound"
        sourceLocator := "Theorem 3.5"
        summary :=
          "For sufficiently small positive epsilon, every absorbing profile " ++
          "at which all players are sequentially epsilon-perfect is an " ++
          "epsilon-to-the-one-sixth equilibrium. Attributed to Solan and " ++
          "Vieille 2001, Propositions 2.4 and 2.13, but stated without the " ++
          "stationary alternative that Proposition 2.4 carries. The printed " ++
          "statement is false: an exactly zero-perfect absorbing constant " ++
          "root sequence in a two-player game has terminal regret one."
        status := .refutedInLean
          "Literature.AshkenaziGolanKrasikovRainerAndSolan2022.\
ErrorExponentBound"
          "Literature.AshkenaziGolanKrasikovRainerAndSolan2022.\
not_errorExponentBound" },
      { claimId := "error_exponent_bound_stationary_alternative"
        sourceLocator :=
          "Theorem 3.5, corrected against Solan and Vieille 2001, " ++
          "Propositions 2.4 and 2.6"
        summary :=
          "The disjunctive form the 2022 restatement dropped: either the " ++
          "absorbing sequentially epsilon-perfect plan is an " ++
          "epsilon-to-the-one-sixth equilibrium, or the game has a " ++
          "stationary epsilon-equilibrium at every positive epsilon. It is " ++
          "an open proposition here and is not refuted by the witness that " ++
          "refutes the printed form: that game satisfies the stationary " ++
          "disjunct exactly, by GameTheory." ++
          "quittingStationaryεEquilibriumExistence_" ++
          "localGlobalCounterexampleReward, whose all-continue profile is " ++
          "a terminal zero-equilibrium by GameTheory." ++
          "isAsymptoticNash_quittingAlwaysContinue_localGlobalCounterexample."
        status := .openInLean
          "Literature.AshkenaziGolanKrasikovRainerAndSolan2022.\
ErrorExponentStationaryAlternative" },
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
      { claimId := "qbar_matrix_sufficient_condition"
        sourceLocator := "Theorem 5.4"
        summary :=
          "If the game's solo-quit matrix is a Q-bar matrix then the game " ++
          "admits a continuous equilibrium. Remark 5.5(1) records that the " ++
          "condition is not tight and that the converse is unknown."
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
          "Literature.AshkenaziGolanKrasikovRainerAndSolan2022.\
projectiveQMatrix_iff_standard_or_homogeneous"
          "GameTheory.QuittingLCPClassification.\
isProjectiveQMatrix_iff_standard_or_homogeneous" } ]

end Literature.AshkenaziGolanKrasikovRainerAndSolan2022
