# Capped-clock rational finite-law producer dependencies

This note audits the rational consecutive-calendar producer described in
`math/exports/CAPPED_CLOCK_DEVIATION_DOMINATION_AND_QUIET_EXTENSION.md`.
It is a dependency map, not a proof-completion record. In particular, the
existing rational search modules are in `Research/`, are not imported by the
integrated production surface, and do not by themselves close the packet.

## Existing semantic source

The three-player child existence input is already checked as
`quittingGame_exists_uniformEquilibriumPayoff_of_card_eq_three`
(`UniformEquilibrium/Quitting/Classification/PlayerReindex.lean`). Given a
specified child target, its actual terminal approximate-Nash profiles are
supplied by
`quittingGame_terminalNash_all_errors_of_isUniformEquilibriumPayoff`
(`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`).

There are two existing finite-menu routes:

- `exists_finiteDeadlineTimingProfile_approximation`
  (`UniformEquilibrium/Quitting/Terminal/FiniteMenuFullProfileApproximation.lean`)
  approximates any actual behavioral profile by an actual finite timing-menu
  profile, with unrestricted terminal exploitability and prescribed-payoff
  control relative to that profile. The displayed deadline may be required to
  exceed any chosen lower bound.
- `isUniformEquilibriumPayoff_iff_finiteMenu_fullCap_target_approximation`
  (the same file) is the fixed-target equivalence. It produces one finite-menu
  law carrying both small unrestricted exploitability and small distance from
  the specified target.

Thus the packet's target-free producer may first choose the three-player
target given by the existing existence theorem. It need not assume an oracle
for an arbitrary real target. Choosing lower deadline one also avoids any
need for the executable rational code to accept a zero clock bound.

The exact capped-clock error transport is already checked by
`isεAsymptoticNash_quietLift_of_cappedClockCertificate`
(`UniformEquilibrium/Quitting/Classification/QuietExtension/CappedClockFixedTargetQuietExtension.lean`).
Its multiplier is the maximum of one and the sum of certificate weights. The
actual lifted profile is the existing Never lift, not a new semantic model.

## Exact consecutive-calendar response cap

`QuittingFiniteDeadlineTimingAction`
(`UniformEquilibrium/Quitting/Terminal/FiniteDeadlineTimingGame.lean`) is
definitionally `Option (Fin deadline)`: the prescribed menu consists of dates
strictly below the deadline and a separate Never action.

The finite list is already known to be behaviorally complete:

- `quittingFiniteDeadlineTimingProfile_pureTime_eq_never_add_of_le`
  (`UniformEquilibrium/Quitting/Terminal/FiniteDeadlineFullReplyCap.lean`)
  proves that every pure finite reply at or after the deadline has the same
  value as the deadline row.
- `quittingContinuationBestResponseValue_finiteDeadlineTimingProfile_eq_max`
  (the same file) identifies the unrestricted behavioral response cap with
  the maximum of the displayed finite timing-menu cap and that one late row.
  It explicitly covers deadline zero.
- `isFiniteClockStoppingLaw_finiteDeadlineTimingLaw`
  (`UniformEquilibrium/Quitting/Terminal/PivotRepairSmallValueSource.lean`)
  exposes the corresponding support statement for the complete stopping law.
  Its current owner is specialized, but the declaration itself is reusable.

The exact candidate list is therefore dates `0, ..., H - 1`, the late row
`H`, and Never. No extra response date, randomized-response optimizer, or cap
attainment assumption is missing.

## Existing rational approximation and checker

The game-independent denominator-clearing primitive is
`Math.SimplexApproximation.residualFloorCounts`
(`MathUE/SimplexApproximation.lean`). It floors every nonresidual coordinate
and assigns the remaining mass to a selected residual coordinate.

The existing executable specialization is the Fin4 Research implementation:

- `RationalFinFourRewardCode` and
  `RationalFinFourFiniteClockProfileCode`
  (`Research/Quitting/FinFourRationalFiniteClockProfile.lean`) are proof-free
  rational payloads.
- `RationalFinFourFiniteClockProfileCode.payoff`,
  `RationalFinFourFiniteClockProfileCode.deviationPayoff`,
  `RationalFinFourFiniteClockProfileCode.cap`, and
  `RationalFinFourFiniteClockProfileCode.exploitability` (the same file)
  evaluate the finite product profile and its complete pure-date/Never cap
  using exact rational arithmetic.
- `RationalFinFourFiniteClockProfileCode.candidateAt_surjective` and
  `RationalFinFourFiniteClockProfileCode.checkedCandidateAt` (the same file)
  give a fair proof-free enumeration and retain exactly the candidates passing
  the Boolean upper checker.
- `RationalFinFourFiniteClockProfileCode.verifiesUpper_sound` and
  `RationalFinFourFiniteClockProfileCode.checkedCandidateAt_sound` (the same
  file) decode a successful row to an actual behavioral profile whose literal
  unrestricted terminal exploitability is below the rational threshold.

The coordinate carrier `Math.ProbabilityMassFunction.FiniteClockAtom H`
(`MathUE/ProbabilityMassFunction/FiniteClockCoordinates.lean`) is
`Option (Fin (H + 1))`. Its final finite coordinate is
`Math.ProbabilityMassFunction.finiteClockAuxAtom H`, the reply date `H`; valid
profile codes force its prescribed mass to zero while retaining it in the
finite reply calculation. This is the same consecutive calendar used by the
packet.

The strict-margin completeness proof is also already present in
`Research/Quitting/FinFourRationalFiniteClockProfileCompleteness.lean`:

- `FinFourRationalFiniteClockProfileCompleteness.rationalMass` and
  `FinFourRationalFiniteClockProfileCompleteness.rationalCode` construct the
  common-denominator approximants;
- `FinFourRationalFiniteClockProfileCompleteness.rationalApproximant_tendsto`
  and
  `FinFourRationalFiniteClockProfileCompleteness.realExploitability_rationalApproximant_tendsto`
  prove same-calendar convergence of the profile coordinates and full cap;
- `FinFourRationalFiniteClockProfileCompleteness.nonempty_rationalUpperWitness`
  turns a strict real upper margin into a rational code for an arbitrary
  rational reward table; and
- `FinFourRationalFiniteClockProfileCompleteness.exists_checkedCandidateAt_of_realFiniteClockProfile`
  and
  `FinFourRationalFiniteClockProfileCompleteness.exists_checkedCandidateAt_of_finiteClockStoppingLaws`
  connect a real finite-clock source to discovery at a finite enumeration
  stage.

The last two public discovery theorems currently carry
`reward.normalized = true`. Their own module documentation and proof show that
this hypothesis is retained reward provenance, not a mathematical premise of
the rational approximation. The lower-level
`nonempty_rationalUpperWitness` has no normalization hypothesis.

This distinction is essential here: the packet's displayed singleton rows
contain entries equal to four, so their literal rational reward code is not
unit-normalized. No packet theorem may silently assert normalization, rescale
the table without transporting the requested accuracy, or apply the current
normalized discovery theorem directly.

## Actual semantic Nash endpoint

`RationalFinFourFiniteClockProfileCode.checkedCandidateAt_sound`
(`Research/Quitting/FinFourRationalFiniteClockProfile.lean`) already yields an
actual behavioral profile and a strict bound on
`quittingTerminalExploitability`. The standard consumer
`isεAsymptoticNash_of_quittingTerminalExploitability_le`
(`UniformEquilibrium/Quitting/Terminal/TerminalExploitability.lean`) converts
that bound to the literal all-behavior terminal approximate-Nash statement.
There is no remaining pure-response versus behavioral-response gap.

Conversely,
`quittingTerminalExploitability_le_of_isεAsymptoticNash` (the same file)
allows the child terminal-Nash source to be fed back into the finite-menu
approximation route. These declarations concern terminal payoffs; they do not
claim a finite-horizon identity for arbitrary evaluations.

## Prescribed pure-Never outsider

The packet's algorithm is more specific than merely finding an arbitrary
rational Fin4 profile: it enumerates rational child laws and then appends a
deterministic Never law for the outsider. The existing Fin4 checker permits
all four rational marginals. Its soundness theorem therefore does not state
that the decoded outsider is pure Never.

Residual-floor rationalization uses Never as the residual coordinate. Hence,
when its real source has an outsider marginal equal to pure Never, all of that
outsider's non-Never floor counts remain zero and the rational approximant is
again pure Never. This fact is not currently exposed by a named declaration
or retained as a field of the checked output. Until such a theorem is proved,
the existing unrestricted Fin4 enumerator must not be described as the
packet's literal "rational child profile, then append Never" producer.

There are two honest output scopes:

1. a rational parent-profile producer, using the existing unrestricted Fin4
   checker and making no prescribed-outsider claim; or
2. the packet's child-first producer, restricting the accepted profile to a
   pure-Never outsider and proving that both rational approximation and
   semantic decoding preserve that restriction.

The second scope is the one required for a literal formalization of the
algorithm in the packet.

## Existing-code-first next step

The smallest coherent next implementation should reuse the Fin4 Research
checker rather than introduce a parallel Fin3 rational PMF language.

1. Add a normalization-free corollary of
   `nonempty_rationalUpperWitness` and finite enumeration surjectivity for
   finite-clock stopping laws. It should have the conclusion of
   `exists_checkedCandidateAt_of_finiteClockStoppingLaws` without the false
   unit-normalization premise or conclusion.
2. Add the pure-Never preservation lemma for the residual-floor rational code
   and a checked-output restriction recording that the outsider marginal is
   still deterministic Never.
3. Compose the existing child existence, finite-menu approximation,
   capped-clock Never lift, normalization-free rational discovery, checker
   soundness, and terminal-exploitability Nash consumer. The result should
   take a rational Fin4 reward code, an owner, the actual capped-clock
   certificate on the corresponding owner reindexing of its real reward
   table, and a positive rational tolerance. It should return a finite checked
   stage/code together with the actual parent terminal Nash certificate.

The executable Fin4 code currently requires a positive clock bound. This is
not an obstacle to termination because
`exists_finiteDeadlineTimingProfile_approximation` permits lower deadline one.
The semantic deadline-zero response theorem is already checked. A separate
zero-clock executable branch is needed only if the public producer statement
must reproduce the packet's explicit `H = 0` acceptance case.

No new rational-density proof, full-cap case split, behavioral deviation
argument, or three-player existence proof is needed. The remaining work is a
normalization-honest, pure-Never-preserving composition of those existing
interfaces.
