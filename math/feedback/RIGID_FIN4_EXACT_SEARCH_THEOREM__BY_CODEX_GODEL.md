# Adversarial review of rigid Fin4 exact search

Reviewer identity: `CODEX_GODEL`

## Verdict

**REVISE the supplied theorem document; PASS the narrowed mathematical result
for export after the scope corrections below are made.**

I found no counterexample to the per-accuracy scale resolver, the exact
interval-tree verifier, or the positive-gap semidecision corollary.  The
current document does, however, overidentify that result with a globally
terminating Fin4 decision procedure and with Output 4 of the rigid-inert
question.  Those claims must not enter the export packet.

The strongest result that passed this review is:

> For every normalized rational Fin4 reward table and rational `epsilon > 0`,
> a dovetailed exact search terminates with either (i) a finite rational
> interval tree proving that the all-behavior terminal exploitability infimum
> is at least `epsilon / 4`, or (ii) a rational finite-clock product profile
> whose all-behavior terminal exploitability is below `3 * epsilon / 4`.
>
> Consequently positive terminal exploitability for a fixed rational table is
> semidecidable.  After enumerating rational normalized tables as well, the
> existence of any real normalized Fin4 counterexample is semidecidable by a
> finite exact certificate, using the Lipschitz robustness of exploitability
> in the reward table.

On the zero-gap side the procedure is a productive infinite process: every
requested scale terminates and supplies a smaller-error profile.  No finite
stage certifies that all subsequent scales will take the upper branch.

## Claims checked

At level `N`, the artifact uses the semantic tube of radius `12 / N` around
literal product stopping laws with `8 * N + 1` finite dates and a separate
Never atom.  It minimizes

`max(0, B_0 - U_0, ..., B_3 - U_3)`

on that single shell.  It then dovetails exact interval subdivision for the
lower bound with exact enumeration of rational finite-clock laws for the upper
witness.

The relevant source declarations agree with the constants and semantics:

- `quantileClockSupport_fin4` and `quantileClockRadius_fin4` in
  `Research/Quitting/EscapeAwareQuantileClockHierarchy.lean` give
  `8 * N + 1` and `12 / N`;
- `escapeAwareQuantileClock_fin4_normalized_quantitative_bracket` in the same
  file gives the corresponding `24 / N` objective gap;
- `hasEscapeAwareQuantileClockCompression_of_normalized` in
  `Research/Quitting/EscapeAwareQuantileClockTransport.lean` is explicitly
  about the unrestricted behavioral cap and transports finite pure dates and
  Never in both directions; and
- `quittingGame_exists_uniformEquilibriumPayoff_of_terminalNash_all_errors` in
  `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`
  consumes actual terminal approximate Nash profiles at every positive error.

## Soundness audit

### Single-shell relaxation

The replacement of the maintained cumulative outer hierarchy by one final
shell is sound for this purpose.  Every actual semantic pair lies in the final
shell by common-quantile compression.  Conversely, the center of every point
in the shell is the semantic pair of an actual independent finite-clock
profile.  Since the objective is 2-Lipschitz in the coordinate sup metric, the
single-shell minimum `A_N` satisfies

`eta(r) - 24 / N <= A_N <= eta(r)`.

No nesting hypothesis is needed for this inequality.

### All-behavior cap encoding

The finite center is represented by four marginal laws, not an arbitrary
joint terminal law.  Joint terms are regenerated as products.  Each marginal
has finite dates and a separate Never coordinate.  The auxiliary zero-mass
date remains available as a pure deviation.

Against opponents supported before the auxiliary date, every later finite
quit date has the same payoff as that auxiliary date, while Never remains
distinct on the all-opponents-Never event.  An arbitrary behavioral deviation
induces a stopping-time law on `Nat` plus Never, and its payoff is affine in
that law.  Hence its value is bounded by the supremum of pure dates and Never;
for these finite opponents that supremum is the finite maximum encoded by the
artifact.  This covers late, randomized, and history-dependent behavioral
deviations rather than only stationary deviations.

### Interval-tree soundness and completeness

Each exact leaf is sound:

- an equality enclosure excluding zero contains no feasible point;
- a required-nonnegative enclosure with negative upper endpoint contains no
  feasible point; and
- an objective enclosure with lower endpoint at least `gamma` proves the goal
  throughout the box.

The closed children of a rational split cover the parent, so a verified finite
tree proves `gamma <= A_N`, and therefore `gamma <= eta(r)`.

The strict-margin completeness argument is also valid.  If `A_N > gamma`,
every point of the compact root box has one persistent strict reason: a
nonzero equality, a negative required inequality, or objective greater than
`gamma`.  Natural interval evaluation for the factored polynomial/max DAG
converges as every box diameter tends to zero.  The generator's normalized
widest-side rule shrinks every coordinate on every infinite branch.  Compactness
(equivalently, the finite-branching infinite-path argument) therefore forces a
finite closed tree.

### Per-scale termination

With

`N = floor(96 / epsilon) + 1`, `a = epsilon / 4`, and
`b = 3 * epsilon / 4`, one has `24 / N < epsilon / 4`.

- If `A_N > a`, strict-margin interval completeness terminates the lower
  search.
- If `A_N <= a`, a witnessing actual center has exploitability below
  `a + 24 / N < epsilon / 2`.  Rational density in the fixed finite product
  simplex leaves strict room below `b`, so complete rational enumeration
  terminates the upper search.

The equality case `A_N = a` is safely included in the upper branch.  Dovetailing
prevents starvation.

## Falsification attempts and implementation checks

I checked the following failure modes directly:

- a zero-minimum table with an unrelated local obstruction;
- a profitable deviation at the last represented opponent date;
- confusion of the auxiliary late quit with Never;
- a joint-law payload without marginal product provenance;
- an unattained semantic-pair payload presented as an upper certificate;
- a false root-level lower goal on the zero table; and
- mismatch between the direct finite-clock semantics and the generated outer
  expression system.

`pytest` is unavailable in the supplied environment.  The module and tests
compile with `py_compile`, and all nine test functions pass when called
directly.  I additionally ran **100 seeded exact-rational comparisons** between
`terminal_semantics` and point evaluation of `build_outer_problem`; all
payoff, cap, feasibility, and exploitability comparisons agreed.

The implementation is genuinely a generator as well as a verifier:
`ScaleSearch` alternates `TreeSearch` and `ProfileCandidateSearch`.  The CLI
currently exposes constants and certificate verification, but not the complete
scale search; that is a usability limitation, not a mathematical gap.

## Required corrections before export

1. **Do not call this a terminating table-level decision procedure.**  It
   terminates for each supplied accuracy.  The positive-gap branch eventually
   halts with a lower certificate; the zero-gap branch emits profiles forever
   and has no finite certificate that it will continue doing so.

2. **Do not claim that this consumes the strict inert component or answers
   `FIN4_INERT_MACHINE_CERTIFICATE_SEARCH.md`.**  A supplied
   `FinFourNormalizedStrictInertSingleDensityToll` inherits positive minimum
   debt from its external source.  The search then eventually gives a finite
   certificate of the already implied positive gap.  It neither proves that
   such an inert object exists, proves it impossible, nor compiles it to UE.
   The JSON certificates contain no inert-source witness, so “carried
   unchanged” can only mean external pairing and should not be advertised as a
   certificate field.

3. **Remove the claim that this is Output 4 of the rigid-inert question.**  It
   is instead a strict answer to the previously missing positive-gap
   semidecision/generator layer recorded in
   `ESCAPE_AWARE_FIN4_CERTIFICATE_SEARCH.md`.  It is not Output 2 there either:
   one upper certificate at one scale does not by itself imply a UE.  The
   all-upper infinite family does.

4. **State the cap-supremum subtlety.**  A certified bound
   `eta(r) >= gamma` is a valid positive semantic exploitability gap and rules
   out UE.  If the downstream interface requires an actually realized
   unilateral gain, arbitrary opponents need not attain their cap exactly.
   Approximate cap attainment gives `HasTerminalExploitabilityGap` at any
   smaller rational gap, for example `gamma / 2`; the packet must not silently
   claim actual attainment at `gamma`.

5. **Separate the implemented and unimplemented global enumeration.**  The
   fixed-table per-scale generator is implemented.  Enumeration of all
   rational tables and its fair global dovetailing are straightforward
   mathematical corollaries but are not commands in this artifact.

## Conjecture-facing change

With those corrections, the result makes a strict named change to
`ESCAPE_AWARE_FIN4_CERTIFICATE_SEARCH.md`: positive-gap Fin4 is recursively
enumerable by finite exact all-behavior certificates.  If a real Fin4
counterexample exists, reward robustness gives a rational one, and fair
enumeration eventually emits its finite lower tree.  Conversely every emitted
tree is sound.

This is meaningful exportable progress even though nontermination supplies no
positive proof of UE and the current strict inert component remains
unconsumed.

## Files inspected

- `../rigid_fin4_exact_search/RIGID_FIN4_EXACT_SEARCH_THEOREM.md`
- `../rigid_fin4_exact_search/rigid_fin4_exact_search.py`
- `../rigid_fin4_exact_search/tests/test_exact_search.py`
- `questions/ESCAPE_AWARE_FIN4_CERTIFICATE_SEARCH.md`
- `questions/FIN4_INERT_MACHINE_CERTIFICATE_SEARCH.md`
- `Research/Quitting/EscapeAwareQuantileClockTransport.lean`
- `Research/Quitting/EscapeAwareQuantileClockHierarchy.lean`
- `Research/Quitting/EscapeAwareQuantileClockPolynomialLower.lean`
- `Research/Quitting/FinFourProducerAtlas/NormalizedInertSingleDensityToll.lean`
- `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`
- `UniformEquilibrium/Quitting/Terminal/ExploitabilityGap.lean`
