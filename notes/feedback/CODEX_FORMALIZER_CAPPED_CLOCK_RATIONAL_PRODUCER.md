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

Both discovery theorems accept arbitrary rational reward tables. Neither
their hypotheses nor their conclusions require `reward.normalized = true`.
The shell-resolution caller retains normalization only for its separate
shell estimates.

This distinction is essential here: the packet's displayed singleton rows
contain entries equal to four, so their literal rational reward code is not
unit-normalized. The literal table can now feed rational discovery directly,
without rescaling or changing the requested accuracy.

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

Residual-floor rationalization uses Never as the residual coordinate.
`FinFourRationalFiniteClockProfileCompleteness.exists_checkedCandidateAt_of_finiteClockStoppingLaws_preserving_pureNever`
(`Research/Quitting/FinFourRationalFiniteClockProfileCompleteness.lean`)
returns a finite checked stage at the same clock and preserves the prescribed
outsider marginal exactly. The reusable coordinate constructor
`RealFiniteClockProfile.ofStoppingLaws` and its decoding identity in that file
serve both discovery variants.
`RationalFinFourFiniteClockProfileCode.behaviorStoppingLaw_toBehaviorProfile_eq_pureNever`
(`Research/Quitting/FinFourRationalFiniteClockProfile.lean`) proves that the
decoded behavioral profile has the same deterministic Never stopping law.

There are two honest output scopes:

1. a rational parent-profile producer, using the existing unrestricted Fin4
   checker and making no prescribed-outsider claim; or
2. the packet's child-first producer, restricting the accepted profile to a
   pure-Never outsider and proving that both rational approximation and
   semantic decoding preserve that restriction.

The child-only checker is
`RationalFinFourFiniteClockProfileCode.verifiesChildUpper`
(`Research/Quitting/FinFourRationalFiniteClockChildUpper.lean`). It requires a
valid code and a pure-Never owner, and tests only the surviving coordinates.
`cast_childExploitability_eq_deletedChildTerminalExploitability` in that file
identifies its rational maximum with the actual deleted game's unrestricted
terminal exploitability. `checkedChildCandidateAt_sound` proves soundness of
every emitted row, using the existing raw-code enumeration.

`FinFourRationalFiniteClockChildUpperCompleteness.exists_checkedChildCandidateAt_of_realFiniteClockProfile`
(`Research/Quitting/FinFourRationalFiniteClockChildUpperCompleteness.lean`)
proves finite discovery from a real finite-clock profile with a strict
child-only margin. The clock is unchanged and the owner marginal remains
exactly pure Never. It reuses the existing residual-floor approximation and
proves continuity of the masked survivor maximum. No reward normalization
is assumed.

`FinFourRationalFiniteClockChildProducer.realChildExploitability_ofDeletedChildStoppingLaws_eq`
(`Research/Quitting/FinFourRationalFiniteClockChildProducer.lean`) identifies
that masked maximum with the unrestricted exploitability of the actual
deleted-child stopping laws. Its source uses the canonical Never lift and
preserves the complete stopping laws, not just their terminal payoffs.
`FinFourRationalFiniteClockChildProducer.exists_checkedChildCandidateAt`
in the same file combines three-player existence, finite-menu approximation,
and rational discovery. For every rational Fin4 table, owner, and positive
rational threshold, it supplies a finite accepted stage with positive clock
and an exactly pure-Never owner. There is no remaining child-existence
hypothesis in this theorem.

## Checked original-parent consumer

`FinFourRationalCappedClockProducer.exists_checkedChildCandidateAt_and_rawParentTerminalNash`
(`Research/Quitting/FinFourRationalCappedClockProducer.lean`) feeds the literal
accepted child into the capped-clock Never-lift consumer and transports the
result back to the original Fin4 reward table. Given a rational upper bound
on the certificate's real multiplier, its checker threshold is the requested
error divided by that bound. The conclusion retains the accepted stage/code,
positive clock, exact pure-Never owner mass, the actual original-parent
terminal Nash certificate, and its owner's complete pure-Never stopping law.

`FinFourRationalCappedClockProducer.exists_rationalAmplification_checkedChildCandidateAt_and_rawParentTerminalNash`
in the same file supplies the rational bound and states its inequality
explicitly. Its only inputs are the rational reward table, the owner, the
actual real capped-clock certificate on the corresponding owner reindexing,
and a positive rational error. No child equilibrium, finite calendar,
normalization, or rational-weight certificate is assumed.

The generic deletion/reindex identity and exact terminal-exploitability
pullback belong to
`UniformEquilibrium/Quitting/Classification/PlayerReindexNaturality.lean`.
The executable-search composition remains Research-only. There is no
parallel Fin3 rational PMF language.

The executable Fin4 code currently requires a positive clock bound. This is
not an obstacle to termination because
`exists_finiteDeadlineTimingProfile_approximation` permits lower deadline one.
The semantic deadline-zero response theorem is already checked. A separate
zero-clock executable branch is needed only if the public producer statement
must reproduce the packet's explicit `H = 0` acceptance case.

This completes the child-first search-to-parent composition. The packet's
additional examples and inverse-row sharpness statements are listed in
[the coverage note](CODEX_FORMALIZER_CAPPED_CLOCK_COVERAGE.md).
