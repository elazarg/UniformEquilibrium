# Semantic review of the frontier-map patch

Artifact: `math/notes/CODEX_COORDINATOR__FIN4_RESIDUAL_PARTITION.md`.
Whole-file SHA256:
`61c44fa0fe4b5fd27fdc7e9352cbecab371c5632d6c85911c0ea3c644bf41912`.
Reviewer: FRONTIER_SEMANTICS. Static source and mathematical audit;
no Lean command, build, tracked edit or Git mutation.

Scope: the newly added preface, from the three-level domain distinction
through the stationary-versus-source-F paragraph. The separate Hamiltonian
sign-test addition is assigned to the raw-domain reviewer and is not given
independent approval here.

Verdict: PASS. No unresolved semantic or quantifier objection.

The coordinate count is exact:4 own singleton entries,12 off-own singleton
entries and44 higher-coalition entries. Distinguishing necessary matrix cells,
overlapping sufficient reward regions and selected minimizing-object cases
prevents an unsupported exhaustive classification or coverage percentage.

The terminal all-errors characterization and its all-behavior positive-gap
negation agree with the exact source declarations audited in
`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`
and `UniformEquilibrium/Quitting/Terminal/ExploitabilityGap.lean`.
Reward robustness implies openness of the positive-gap set. Rational points
and avoidance of the finitely many nonzero exceptional polynomials may be
selected inside that open set; the explicit warning correctly prevents
transporting selected minima/laws through unrelated normalizations. An
own-zero native table has exact all-Never Nash, so its gap restriction must
indeed concern the absorbing subclass rather than all native profiles.

The exact finite-block no-go is stated with its essential absorbing and
punishment-admissible qualifiers. The inspected
`no_isQuittingBlockCertificate_solanPassivePaddedReward_one` gives an
explicit integral four-player example at epsilon=1 and excludes every
finite period in exactly this certificate language. The preface neither
inflates that to all behavior nor mistakes it for a counterexample.
The inspected fixed-box forward characterization has exactly the normality
and positive-own-level hypotheses stated here. Absorption-relative error,
boundedness and the punishment-value sure-root alternative are retained;
no arbitrary-data producer is claimed supplied by this equivalence.

The source taxonomy is consistent with the maintained SUM two-chamber,
least-Never two-bridge, and native observer-exact ten-case descriptions.
These are distinct optimization problems and selections. MAX ties and
harmonic inequalities cannot silently be assigned to a SUM or constrained
native minimizer. No surviving top-level source case is represented as
universally consumed. Finally, the finite-calendar actual source F is
correctly distinguished from the stationary UE alternative: it carries
constrained native minimum data and is not a stationary-equilibrium branch.

All qualifications needed for the user's frontier review are present.
