# Export-gate audit of the executable proof architecture

Reviewer: `ARCHITECTURE_EXPORT_GATE`

Targets:

- `meta/EXECUTABLE_COMPACT_STATE.md`;
- `meta/GRAMMAR.md`;
- `meta/VANISHING_REACH_SUFFIX_NO_GO.md`; and
- `questions/QUITTING_COMPOSITIONALLY_SUFFICIENT_STATE.md`.

## Verdict

**The mathematics is mature, but the three-file package does not yet qualify
for `exports/` under the current question and export policy.**

This is not a mathematical rejection.  The independent audits have repaired
the substantive topology, legality, tightness, rank, and all-Never semantic
issues, and I found no new mathematical counterexample to the resulting
theorems.  The failure is at the conjecture-facing gate: the package proves a
sound sufficient architecture and two narrow impossibility boundaries, but it
does not instantiate that architecture on the remaining Fin4 construction,
and neither impossibility result excludes all adapter classes accepted by the
named question.

The files should remain canonical architecture records.  They should not be
copied to `exports/` merely because their internal mathematics has passed
review.

## Exact named-question comparison

The relevant named question is
`QUITTING_COMPOSITIONALLY_SUFFICIENT_STATE.md`.
It has two positive obligations:

1. construct a finite proof-relevant grammar and prove a coherent-diagonal
   theorem for tight, restriction-compatible actual executions; and
2. instantiate the grammar on the non-elementary operations used by the
   finite quitting-game construction and obtain a terminal approximation,
   charged return, consumed renewable exit, or positive-gap certificate.

The present package completes the first obligation, at the level of a
sufficient schema:

- `EXECUTABLE_COMPACT_STATE.md` proves total-variation reconstruction for the
  elementary stopping-law grammar under per-port tightness and positive reach;
- `GRAMMAR.md` adds closed selected edges, summable decoders, closed finite
  cases, bounded trace-visible rank, and pointwise post-limit rank; and
- its coherent-diagonal theorem produces one compatible actual execution and,
  with one initial port, one controller.

It does **not** complete the second obligation.  In particular, no theorem
shows that the current Fin4 regeneration, normalized inert, maximal-ray, or
source-attached minimum-return edges satisfy the displayed `ClosedSelect`,
`Decode`, or `TraceRank` certificates.  No arbitrary Fin4 source is sent to
one of the four accepted semantic outputs.

The acceptable-negative clause is also not met:

- the vanishing-reach theorem excludes graph-closing positive-reach suffixing
  after its reach and exact-source witness have been forgotten, and excludes
  ranks intrinsic only to the resulting law relation;
- it explicitly leaves open reach-weighted finite-precision consumers,
  summable source-faithful decoders, richer provenance, and external phase
  ranks;
- the maximal-root example excludes universal closed or vanishing-error
  **exact same-source absorption-maximal-root traces**, but explicitly leaves
  open approximate root equations, restricted domains, modified sources,
  other objectives, pointwise use after reconstruction, and
  construction-specific decoders.

The named negative answer requires exclusion of both the specified trace
adapter class and its specified renewable ranked enlargement, including
terminal and backward consumers.  Neither no-go proves that statement.

Thus the exact change is:

> the abstract grammar/reconstruction half of the named question is solved;
> its Fin4 instantiation remains open.

That is valuable frontier clarification, but under the literal export policy
it is still a conditional architecture whose construction-facing source
hypothesis is open.

## Audit against the export criteria

### 1. Exact self-contained statement

**Pass, modulo packet assembly.**  The component statements quantify the
finite player set, bounded standard quitting table, actual stopping laws,
tightness, reach, witnesses, errors, and rank data.  They are not currently a
single export-format theorem statement.

### 2. Complete definitions and proof

**Pass mathematically.**  The stopping-law compiler, Late/Never split,
elementary operations, closed selection, comparison transport, summable
decoder, pointwise rank, trace-visible rank, and diagonal proofs are complete
under their stated assumptions.  The two counterexamples are exact.

There are harmless presentation duplications that should not survive into an
export packet: the repeated definition of `tau_mu`, repeated `Anc`, repeated
Theorem 6 heading, and a stray display delimiter near the maximal-root
example.  The local reuse of `R` for both reward bound and relation should also
be removed.

### 3. Probability, information, stopping, and unilateral-deviation audit

**Pass.**  Strategies are represented by independent laws on
`Nat union {Never}`; the unique live public history makes this equivalent to
behavioral hazard sequences.  The cap is the supremum over all pure finite
stopping times and Never, hence over all behavioral unilateral replacements
by linearity.  The Late point is a compact response boundary, not an extra
legal behavioral action.  Total-variation estimates are uniform over the
complete unilateral strategy class.

### 4. Adapter/consumer or strict named boundary change

**Fail for export.**  The terminal-to-uniform consumer is genuine, but its
tight coherent vanishing-debt input is supplied rather than produced from the
current Fin4 source.  The pointwise rank consumer is similarly conditional on
a complete dispatch, terminal consumer, and backward map.  The no-go theorems
do not exclude all alternatives accepted by the named question.

### 5. Boundary tests

**Pass.**  The documents include:

- the tight positive reconstruction theorem;
- the uniform-clock/tester nonattainment and summable-budget obstruction;
- the exact arbitrary fibre over the zero-reach source;
- the protected-source unit separation and law-intrinsic self-loop; and
- the two-player exact maximal-root bifurcation, including vanishing-error
  approximate maximality within the exact-root set.

### 6. Source audit

**Incomplete as an export packet, although enough material exists to finish
it.**  A final packet would have to state explicitly:

- that the clock/tester nonattainment core is already checked in
  `UniformEquilibrium/Diagnostics/Quitting/PositiveDebtTerminalSemanticNonattainment.lean`,
  while the split-clock and summable-coordinate-budget formulations are the
  added ordinary mathematics;
- that stopping-law expectation is represented by
  `quittingRootSequenceHazardTerminalValue_eq_expect_stoppingLaw` in
  `UniformEquilibrium/Quitting/Paths/BehaviorStoppingPayoff.lean`;
- that the existing tight semantic realization boundary is represented by
  `quittingTerminalSemanticPair_eq_of_opponentTight_lawLimit` and the selected
  law-limit package in
  `UniformEquilibrium/Quitting/Terminal/OpponentTightTerminalSemanticRealization.lean`;
- that the downstream consumer is
  `quittingGame_isUniformEquilibriumPayoff_of_terminalNash_exact` in
  `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`;
  and
- that the canonical Fin4 maximal-prefix ray in current Research is a
  pointwise construction and is not invalidated merely by the universal
  trace-selector counterexample.

The contextual absorption-path citation should either be tied to a precise
paper statement or omitted; no paper theorem is needed for these proofs.

### 7. Independent review

**Pass for the mathematics.**  The final whole-document mathematical,
no-go/question, and structure audits report no unresolved objection after
repair.  Earlier topology, reconstruction, scope, adapter, conditioning, and
rank audits provide substantive falsification attempts.  An assembled export
packet would still need a final comparison audit ensuring that its compressed
statement has not gained strength relative to the reviewed source notes.

### 8. Lean handoff

**Not yet export-ready.**  The notes identify the checked terminal consumer
and several semantic sources, but do not yet give one narrow declaration map
for the abstract grammar, the exact maximal-root counterexample, and the
zero-reach suffix closure.  This is repairable, but it should be done only
after a conjecture-facing qualifying theorem exists.

## Narrowest packet that would qualify later

The narrowest honest export would not be the current three notes verbatim.  It
would be a single packet titled along the lines of:

> **Fin4 executable residual compilation through a tight certified
> stopping-law grammar**

Its new theorem would start from the already established source-attached Fin4
residual and provide, for every non-elementary edge actually used there, one
of the certified adapters in `GRAMMAR.md`.  It would then conclude one of the
four outputs in the named question.  The generic grammar theorem and the two
no-go examples would be lemmas and boundary tests inside that packet, not its
conjecture-facing conclusion.

Alternatively, an impossibility packet would qualify if it fixed one actual
remaining Fin4 construction and proved that no closed/summably decoded trace
adapter **and no specified external ranked repair with terminal and backward
consumers** can realize it.  The current zero-reach and maximal-root examples
do not establish that stronger negative statement.

## Recommendation

Do not place the present architecture package in `exports/`.  Use it to write
the new Fin4 adapter-instantiation question and to audit every proposed
residual edge.  Promote only when that question receives either an actual
Fin4 compilation/consumer or the fully scoped negative theorem allowed by its
contract.
