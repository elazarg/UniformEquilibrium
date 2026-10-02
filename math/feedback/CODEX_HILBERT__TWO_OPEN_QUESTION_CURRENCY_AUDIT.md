# Source review of the open mathematical questions

Identity: CODEX_HILBERT. Bounded source audit; no question or shared-index edits.
Both question files were read completely. This records their actual requested
conclusions, not an inference from their filenames.

## AKRS_THEOREM_3_4_REVERSE_S3_NULL_TAIL_GAP.md

The requested conclusion is the universal reverse implication: a finite
quitting table with arbitrary Never vector, carrying initially absorbing
row-perfect witnesses at every small error, has unrestricted terminal
approximate Nash profiles at every positive error. Different output profiles
are allowed. The question is still OPEN in this all-finite-cardinality scope.
It is genuinely conjecture-facing, not merely a Literature transcription
question: its universal form is equivalent to general finite-quitting
approximate-equilibrium existence.

However its STATUS/KNOWN-PROGRESS FRAMING NEEDS REVISION. The null-tail
subcase advertised by the title is no longer an independent open gap.
The exact production declarations are:

- `QuittingPayoffTable.solo_sub_never_le_of_positiveRestartSurvival` and
  `QuittingPayoffTable.solo_sub_never_le_of_completelyAbsorbing_not_everyRestart`
  in `Quitting/Classification/Existence/SequentiallyPerfectAbsorbingNullTailAlternative.lean`.
  A nonterminating restarted tail bounds every own singleton by Never plus
  the row error. The stronger first declaration does not need initial absorption.
- `QuittingPayoffTable.allContinueExactNash_or_everyRestartWitnesses` in the
  same file. Either all Continue is exact terminal Nash, or below one fixed
  threshold EVERY sufficiently accurate initially absorbing row-perfect
  witness terminates from every restart. The alternatives are inclusive.
- `universalStationaryExactEveryRestartSource_iff_approximateExistence` and
  `universalReverseSequentiallyPerfectAbsorbing_iff_universalApproximateEquilibriumExistence`
  in `Quitting/Classification/Existence/ReverseSequentiallyPerfectAbsorbingHardness.lean`.
  Even the stationary exact every-restart source implication is universally
  as hard as general approximate existence. The hard reduction adds ONE
  player; it is not an equivalence at a fixed cardinality such as Fin4.

These exact statements, including their quantifiers and the definition
`HasStationaryExactEveryRestartRowPerfectSource`, were read in place. They
agree with `docs/FRONTIER.md`, `docs/TOOLKIT.md`, and the completed record
`formalized/AKRS_REVERSE_S3_NULL_TAIL_AND_HARDNESS.md`.

Another checked solved subcase is now stronger than the question's quoted
unit-singleton/every-tail case:
`exists_terminalNash_of_all_normal_of_sequentiallyPerfectAbsorbing` and
`exists_uniformEquilibriumPayoff_of_all_normal_of_sequentiallyPerfectAbsorbing`
in `Quitting/Classification/Existence/NormalSequentiallyPerfectAbsorbingUniformPayoff.lean`.
They consume all-player punishment normality and the literal zero-Never S.3
source. Their Fin4 hard-residual wrappers are in the diagnostics file of
the same basename. They do not prove general arbitrary-Never, arbitrary-
cardinality reverse S.3 without their normality input.

Recommended revision: retain the actual open implication and its full
definitions, but retitle the heading as reverse S.3 after null-tail elimination;
replace the paragraph presenting null tails as work still needed by the
inclusive solved alternative; add the one-added-player hardness statement
and the all-normal solved subcase. Do not mark the full question resolved or
claim the hardness result is cardinality-preserving.

Self-containment is otherwise good: rewards, Never, restarted values including
null histories, four row-perfection clauses, unrestricted deviations, source
and conclusion quantifiers, and the supplied-profile counterexample are all
defined. The mathematical question is timeless; its historical frontier
description is what has become stale. The paper-facing
`HasSmallAbsorbingSequentiallyPerfectProfiles` definition and its equivalence
with the production S.3 predicate were also checked in
`Literature/AshkenaziGolanKrasikovRainerAndSolan2024.lean`; no paper claim is
being promoted merely because it appears in that lane.

## QUITTING_CONTROLLER_TESTER_DUALITY.md

The ACTUAL request is η(r)=0 for every Fin4 table, or an explicit positive
closed invariant barrier. It does NOT ask to reconstruct the already solved
controller–tester duality. It remains OPEN and directly conjecture-facing:
the sign question is exactly the Fin4 uniform-equilibrium problem in compact
terminal-semantic coordinates.

All displayed supporting facts match current production declarations:

- `quittingControllerTesterValue_eq_minimum_rawMaximumDebt` and
  `quittingControllerTesterValue_eq_zero_iff_exists_uniformEquilibriumPayoff`
  in `Quitting/ControllerTester/ControllerValue.lean`.
- `quittingUniformHorizonTargetValue_eq_controllerTargetValue` in
  `Quitting/ControllerTester/UniformHorizonValue.lean`. Its fixed-profile
  identity is established before taking the profile infimum; the question's
  fixed-target/all-long-horizon interpretation is not an illicit interchange.
- `QuittingControllerClosedInvariantBarrier`, its `carrier_subset` theorem,
  and `nonempty_closedInvariantBarrier_iff_le_controllerTesterValue` in
  `Quitting/ControllerTester/BarrierDuality.lean`.
- `terminalSemanticCarrier_eq_closure_neverGeneratedSemanticReachable` in
  `Quitting/Root/NeverGeneratedSemanticCarrier.lean`.

The declarations were read in place. They match the exact one-root formulas
in the question, including the opponent-only survival multiplier in the
Continue cap and the max with the root Quit value. The invariant-set language
is complete without a polyhedral/semialgebraic restriction, and the stated
floor η≥Γ does not presume an actual best response attaining Γ.

`formalized/QUITTING_CONTROLLER_TESTER_VALUE_AND_BARRIER_DUALITY.md` explicitly
records that formulation/duality has been solved and points to this file as
the remaining SIGN question. Current `docs/FRONTIER.md` and `docs/TOOLKIT.md`
say the same. New special-class producers and the canonical three-law repair
reduction do not establish the sign for arbitrary Fin4 rewards.

No substantive currency correction is needed. The title already says
controller–tester SIGN question. An optional one-sentence status note could
make explicit that duality is known and only the sign remains; optionally
write the fixed-target horizon quantifiers in one display. The definitions
and requested positive/negative conclusions are already self-contained and
timeless. The filename alone should not cause this open question to be
mistaken for its completed formalized representation theorem.

## Addendum: ESCAPE_AWARE_FIN4_CERTIFICATE_SEARCH.md

The entire107-line question was read and compared with the named hierarchy,
exact-scale, independent-checker, and semidecision declarations. Its HARD
conjecture-facing requests remain open: no positive-gap table is produced,
the zero-versus-positive infimum problem is not decided for every input,
and no specified new complete residual chamber is eliminated merely by
having the existing search machinery. The finite proof-producing machinery
itself is substantially more complete than the question's assumption paragraph
acknowledges.

Three mathematical specifications should be corrected or clarified.

1. Replace “finite feasible set R_M(r)” by “a finite-dimensional real
   semialgebraic feasible set with a finite polynomial presentation.” Its
   points range over real marginal masses and semantic coordinates; there
   are generally infinitely, indeed continuously, many feasible points.
   It is not a finite enumeration of all behaviors or semantic outcomes.

2. Distinguish exactness ON THE LIFT from a sound lower objective. For the
   named quantile hierarchy, an actual profile maps to its literal common
   semantic coordinates (U,B), accompanied by finite-clock witness centers.
   The objective is exactly max(0,max_i(B_i−U_i)) there, hence equals actual
   unrestricted exploitability on this lift. Other feasible outer points
   need not be realized by any profile. Thus the introduction can retain
   exactness if written in this precise form. The later general soundness
   contract Φ(E(σ))≤Expl(σ) is sufficient and is a legitimate WEAKER
   requirement for a proposed alternative relaxation, not a claim that the
   compressed finite-clock center preserves the original objective exactly.

3. “A terminating algorithm for every normalized four-player table” lacks
   an input model when the sixty rewards are arbitrary real numbers. The
   minimal repair is to require normalized RATIONAL reward tables, supplied
   as finite exact codes, as in the existing algorithmic declarations. An
   alternative real-oracle/computable-real model would need to be explicitly
   defined and its correctness/termination proved; neither follows from
   the current source. Likewise rational-polynomial proof checking for a
   FIXED real table is not automatic. Rational input or an explicit symbolic
   chamber with rational defining data resolves that ambiguity.

Rational restriction does not weaken the existential counterexample search:
the checked2-Lipschitz reward bound, scaling, and rational density transport
any real positive-gap table to a normalized rational positive-gap table.
It does not turn semidecision into a decision of a supplied real table.

Exact sources checked in place:

- `quantileClockOuterSemanticAssignment` and its objective-row theorem,
  `quantileClockLowerQueryFeasible_iff`, and the rational certificate lower
  bound in `Research/Quitting/EscapeAwareQuantileClockPolynomialLower.lean`.
  The common semantic point and finitely many real center assignments make
  the exact-on-lift meaning explicit.
- `finFourSingleShell_quantitative_bracket` and
  `finFourSingleShellLower_le_exploitabilityInf` in
  `Research/Quitting/FinFourSingleShellOuter.lean`; the exact rational
  expression system in `FinFourRationalSingleShellLower.lean`.
- `finFourExactScaleStep`, `exists_finFourExactScaleStep`, and
  `finFourExactScale_infimum_zero_or_lower_event` in
  `Research/Quitting/FinFourExactScaleResolution.lean`.
  At each positive rational scale the algorithm terminates with an actual
  small-regret finite-clock profile OR a genuine lower certificate. One
  upper event does not certify zero infimum; infinitely many required
  accuracies are not collapsed to one finite termination claim.
- `FinFourExactScaleCertificate.lower_verifies_infimum_sound` in
  `Research/Quitting/FinFourIndependentCertificateSoundness.lean`.
- `exists_finFourFixedTableCounterexampleStep_of_infimum_pos` in
  `Research/Quitting/FinFourFixedTableCounterexampleSearch.lean`, and
  `exists_finFourCounterexampleStep_iff_exists_real_infimum_pos` in
  `Research/Quitting/FinFourCounterexampleSemidecision.lean`.
  These are conditional fixed-rational-table completeness and global
  existential recursive enumerability, respectively. Nontermination
  supplies no zero-gap conclusion.

The current formalized records
`ESCAPE_AWARE_QUANTILE_CLOCK_SEMIALGEBRAIC_HIERARCHY.md` and
`EXACT_FIN4_SCALE_RESOLUTION_AND_COUNTEREXAMPLE_SEMIDECISION.md`, and the
maintained docs, agree with these boundaries. The question should list the
exact per-scale resolver and positive-gap semidecider as KNOWN, so that
option3 is clearly asking for a genuinely new chamber elimination rather
than reproduction of already checked certificate generation. “One complete
live residual chamber” should name or explicitly define the chamber and
the universal conclusion on it.

Finally, the positive-output specification should define its proof object.
A finite code plus a proved all-errors actual-profile guarantee may use the
existing fixed-payoff consumer; it need not be one common chronology or one
exact equilibrium profile. A bare relaxed flow or merely small value at one
scale is insufficient, as the question says. But a proved diagonal carrier
point WITH the checked density/terminal-all-errors consumer is not inherently
invalid merely because it is a carrier point. The wording should preserve
that legitimate route instead of requiring source-matched chronology.

These are specification/current-status fixes, not a resolution of the hard
question. No question file or shared index was edited.
