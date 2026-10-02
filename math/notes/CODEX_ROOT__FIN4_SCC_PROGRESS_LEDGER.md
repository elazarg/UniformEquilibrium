# Fin4 SCC progress ledger

Maintainer: `CODEX_ROOT`

Last updated: 2026-09-05

## Purpose

This is the canonical plain-text progress map for the four-player quitting-game
completion problem. It measures elimination of recurrent mathematical
obstructions, not the number of files, lemmas, estimates, packets, or
formalized lines.

The finite-roadmap reduction is represented in the checked Research
declarations `uniformPayoff_or_sourcePreservingCompletionOutcome` and
`FinFourCompletionMode.sameComponent_iff_eq`, in
`Research/Quitting/FinFourProducerAtlas/SourcePreservingCompletionAtlas.lean`.
Every hypothetical Fin4 counterexample enters one of two terminal components
on one retained source chronology. These are structural outputs, not
uniform-equilibrium consumers. The detailed source and theorem inventory remains in
`CODEX_ROOT__FIN4_PRODUCER_ATLAS_DIRECTED_KNOWLEDGE.md`.

## What an SCC means here

An SCC is a strongly connected component of a directed graph. Two nodes are
in the same SCC when each can reach the other by proved nonterminal
transitions. An SCC is maximal: every node mutually reachable with its members
belongs to it.

The nodes in this ledger are not individual payoff vectors, laws, or
behavioral profiles. Those spaces are infinite and usually continuous. A node
is a finite *type of source-attached obstruction*, such as `ForcedPair` or
`NormalizedInert`. It may have infinitely many instances carrying different
tables, profiles, laws, clocks, or payoff vectors.

A typed transition from node `A` to node `B` means that the output literally
contains the complete fields required to instantiate `B`. Merely proving that
some coordinate or carrier point resembles `B` does not create an edge.

For example, `uniformEscape` has a literal shift transition to another packet
of the same type.  Its infinitely many possible stream tails are instances of
one abstract terminal SCC.  Finer internal transitions such as forced-pair to
normalized-inert remain certificates inside a packet; they do not add modes to
the declared completion graph.

## Finite completion theorem

The mode type is

```text
cofinalSingleton | uniformEscape | minimumReturn.
```

Every no-UE Fin4 source produces a cofinal stream of actual singleton frames
on one fixed minimum-law chronology.  Framewise forced-pair construction,
finite-label stabilization, and the nonnegative actual-tail-excess dichotomy
give exactly one priority transition to `uniformEscape` or `minimumReturn`.
Both child packets retain the source, profiles, root stacks, dates, laws,
literal tails, fixed mass and gain floors, and exact own-debt subtraction.

The complete declared regular graph is

```text
cofinalSingleton ---> uniformEscape ---> uniformEscape ---> ...
                 \
                  ---> minimumReturn ---> minimumReturn ---> ...
```

There are no rank transitions.  The first mode has no self-loop and must leave
in one step.  The last two modes are closed under literal stream shift.
Therefore no fairness or rank-reset argument is needed.

## Counting rules

1. Count semantic components, not source-distinct tags. Two tags carrying the
   same recurrent semantic mechanism count as one SCC.
2. Use only proved typed transitions. A proposed adapter, matching labels, or
   equality of carrier points does not create an edge.
3. A component is eliminated only when one of the following is proved:
   - its source type is empty;
   - every realization reaches terminal approximate Nash profiles or a
     uniform-equilibrium payoff;
   - every realization reaches an exact positive admissible return consumed
     by the checked compiler; or
   - every realization makes a renewable strict decrease in a fixed finite
     rank, with the complete child source reconstructed.
4. Redirecting a node into another unresolved node is consolidation, not SCC
   elimination.
5. A one-time support drop without reconstruction of the complete atlas source
   is not a rank exit.
6. A conditional consumer without an arbitrary-source producer is not an
   outgoing atlas edge.
7. A no-go for a proof technique is recorded separately. It does not eliminate
   an atlas SCC unless it proves the actual source type impossible.

## Current score

- SCCs in the declared completion graph: 3
- Nonterminal entrance SCCs: 1 (`cofinalSingleton`)
- Terminal live SCCs: 2 (`uniformEscape`, `minimumReturn`)
- Former entrance SCCs eliminated before this graph: 1 (same-stage
  monodromy, representing two old leaf tags)
- Unclassified recurrent SCCs outside the declared graph: 0, by the exhaustive
  entrance and dispatch theorem

This is an exact finite roadmap count.  It is not a percentage-complete claim:
both terminal SCCs remain mathematically open.

## Current research compression beyond the declared graph

The checked three-mode graph above remains the authoritative source-level
atlas.  Later results substantially refine both terminal SCCs, but the full
composition has not yet been promoted as one checked transition theorem.
Accordingly the SCC count above is not silently changed here.

The strongest current research reduction is:

```text
positive-minimum source
  -> source-attached paid cap transition
  -> minimum-fibre chord or off-minimum paid port

minimum-fibre chord
  -> source-regenerated strict positive-debt-support child

off-minimum paid port
  -> two prescribed finite sure clocks
  -> at most two exact nonnegative cap installations
  -> a pure-clock exact-response system
  -> pure minimum hit or an entirely off-minimum literal response cycle
```

The finite pure-clock part is checked in production Lean.  It uses a response
alphabet of size at most six and returns within at most `6^4 = 1296` states.
Every selected mover makes an exact unrestricted behavioral best response,
gains at least `D_*/4`, and has zero own debt at the target.  The cycle ledger
also forces a nonmover payoff fall and a nonmover debt increase of at least
`D_*/12` somewhere on the cycle.

The two-sure activation theorem and the cap-band renewable support handoff are
currently independently reviewed ordinary mathematics rather than checked
components of the global atlas.  They remove two apparent residuals:

- a proper active set is selector-dependent, because every remaining player
  can be installed at a deterministic finite cap clock while one sure opponent
  screens the tail;
- a minimum-fibre cap-band response admits a strict support child with literal
  source regeneration, rather than only a one-time abstract support
  comparison.

The resulting candidate terminal component is the **source-attached
off-minimum finite response-cycle waist**.  Its arrows are complete-strategy
best-response replacements, not consecutive dates of one play.  Literal
return of the clock vector therefore does not give the Nash--Bellman identity,
root absorption charge, or punishment-floor annotations needed by the checked
near-return consumer.

An exact finite-menu Nashification does not remove this waist.  For a clock
alphabet ending at date `T`, the only unrestricted defect is the omitted late
date `T+1`.  Under no uniform payoff, every such finite timing Nash law has at
least three positive Never marginals; otherwise two sure-finite opponents
screen the boundary and the profile is already a full terminal Nash profile.
The independently reviewed omitted-clock handoff sharpens this boundary: the
`T+1` gain forces a uniformly positive singleton atom.  If both endpoints
approach the global minimum, their executable response chord yields strict
positive-debt-support descent with same-law source regeneration.  If an
endpoint stays uniformly off minimum, signed source retraction returns to the
same quantitative paid-port waist.  Thus the first omitted deadline is not a
separate recurrent component.

There is also a checked obstruction to using exact finite timing Nash
selection as a complete strategy class. For one normalized four-player table,
`quarter_lt_finiteDeadlineTimingNash_exploitability`
(`UniformEquilibrium/Diagnostics/Quitting/FinFourHardDeadlineTimingNashUniqueness.lean`)
gives unrestricted exploitability strictly greater than `1/4` for **every**
exact finite timing Nash law at **every** positive deadline. On the same table,
`comparisonProfile_exploitability` and
`comparisonTarget_isUniformEquilibriumPayoff`
(`UniformEquilibrium/Diagnostics/Quitting/FinFourHardDeadlineTimingNashBarrier.lean`)
provide actual finite-clock profiles of exploitability `1/L` and a fixed
uniform payoff. Thus this is not merely a failure of one Nash selector or of
one compact subsequence. A source theorem obtained from exact finite timing
Nash laws can still be useful under no UE, but it needs an additional
construction that leaves this restrictive class; choosing larger deadlines
alone is not such a construction. Arbitrary rational finite-clock profiles
with their complete date-or-Never deviation test are not excluded by this
regression.

A separate reviewed ordinary-mathematics reduction now controls approximate
finite timing sources uniformly. Under Fin4 no UE, there are fixed positive
numbers `e_*`, `rho` and a fixed integer `H` such that every finite timing
`epsilon`-Nash profile with `epsilon <= e_*` reaches its final `H` dates with
probability at least `rho`, at every deadline at least `H`. There is no
deadline-times-error hypothesis. The argument constructs support-accurate
roots by deleting bad Quit hazards with one whole-prefix budget, derives
punishment floors from the summable annotated limit spine, and excludes a
first small-reach crossing through the existing finite-forward consumer.
The source/profile is unchanged in the resulting reach statement.

This theorem supplies reach on a fixed positive neighborhood of finite Nash,
not just the incomplete exact-Nash class above. Its final window may still
have a positive omitted-date defect. No minimum-fibre identification,
renewable return, or terminal consumer is inferred. The proof and separate
reviews are in
`notes/CODEX_RENY__APPROXIMATE_FINITE_TIMING_NASH_AND_REACH.md`,
`feedback/CODEX_RENY__APPROXIMATE_FINITE_TIMING_NASH_AND_REACH__BY_CODEX_HILBERT.md`,
and `feedback/CODEX_RENY__APPROXIMATE_FINITE_TIMING_NASH_AND_REACH__BY_CODEX_SKEPTIC.md`.
This new reduction is not yet a checked Lean declaration and does not change
the declared SCC count.

Thus the present conjecture-facing task is not another entrance
classification.  It is to prove one genuinely global statement:

```text
positive global minimum + retained source ancestry
+ a literal off-minimum finite exact-response cycle
  -> temporal charged return, renewable minimum-fibre rank decrease,
     impossibility, or an exact positive-gap table.
```

Purely local response-cycle data cannot suffice: a four-state two-sure exact
response cycle exists in a game with an exact equilibrium and global minimum
debt zero.  Any successful orientation must use positive global minimum debt,
the retained source law/chronology, or both.

Relevant maintained records are:

- `formalized/FIN4_FINITE_PURE_CLOCK_EXACT_RESPONSE_CYCLE.md`;
- `formalized/FIN4_SIGNED_SOURCE_RETRACTION_AND_NEAR_MINIMUM_RESPONSE_CYCLE_CONTRACTION.md`;
- `notes/CODEX_HAHN__TWO_SURE_EXACT_CAP_ACTIVATION_AND_PURE_CYCLE_REDUCTION.md`;
- `notes/CODEX_SPINOZA__FOUR_DEADLINE_SEMANTIC_COMPRESSION_AND_SINGLE_HOST_BUBBLE.md`;
- `notes/CODEX_GROMOV__TWO_SURE_CLOCK_FINITE_RESPONSE_CYCLE_NOGO.md`; and
- `questions/FIN4_QUANTITATIVE_PAID_PORT_CONSUMER.md`.

An independent nonchronological line studies the feasible cone of terminal
laws of independent stopping clocks.  The sharp adjacent-pair and three-clock
triangle inequalities are real restrictions, but no reward table is known to
force incompatible pair-mass floors.  This is not presently an edge in the
source atlas.

## Current terminal SCCs

### T-001: Uniform escape

One fixed-label cofinal forced-pair stream has actual post-row tails `T_n` and
one `delta>0` with

```text
D(T_n) >= D_* + delta
```

at every retained rank.  The packet also retains fixed positive marked mass,
fixed paid gain, exact payer-debt subtraction, and the literal source tail.

Required consumer: terminal approximate Nash profiles, a positive cumulative
admissible return, contradiction with positive global minimality, or an actual
positive-gap realization.

### T-002: Minimum return

The same fixed-label source packet satisfies

```text
D(T_n) -> D_*.
```

The central obstruction is cross-coordinate cap leakage: one payer's debt is
reduced exactly by a fixed amount at each frame, but another unrestricted cap
may rise.  A successful rank exit must exclude support entry and reconstruct
the complete child source renewably.

Required consumer: terminal approximate Nash profiles, a positive cumulative
admissible return, renewable finite-rank source descent, impossibility, or an
actual positive-gap realization.

## Internal refinements, not additional SCCs

The following remain useful certificates inside the two terminal packets but
are no longer separate global modes:

- concentrated-collision residuals;
- forced-pair normalized-inert points;
- three-role endpoint-law return or ascent;
- one-time support handoffs;
- strict maximal rays, positive limiting roots, binding-cardinality three,
  full binding, and normalized flow;
- response squares, Jensen passports, and adjacent reentry traces.

They change the roadmap only if they consume an entire terminal packet or give
a source-preserving transition already covered by the finite mode type.

## Historical pre-completion-atlas ledger

The remainder of this file preserves the earlier partial-map analysis and its
methodological no-gos.  Its old score, node labels, and candidate progress
events are superseded by the finite completion theorem above; the detailed
obstructions remain useful when attacking the two terminal capstones.

## Eliminated SCCs

### E-001: Same-stage monodromy

Source tags represented:

- common-host monodromy;
- complementary-pair monodromy.

Verdict:

- eliminated;
- one semantic SCC, two source-distinct tags.

Reason:

The stored Fin4 monodromy trace is internally impossible. This is stronger
than consuming its two geometric refinements: the common underlying producer
is empty.

Checked evidence:

- `Research/Quitting/FinFourProducerAtlas/MonodromyImpossible.lean`;
- `not_nonempty_finFourMonodromyProducer`;
- `not_nonempty_finFourCommonHostMonodromyProducer`;
- `not_nonempty_finFourComplementaryPairMonodromyProducer`;
- `FinFourProducerResidual.withoutMonodromy`.

Historical effect:

The checked six-tag entrance contracts to four nonmonodromy tags. This is the
only presently counted SCC elimination.

Question status:

Resolved. The former common-host and complementary-pair question files are
historical resolution records, not active capstones.

## Confirmed live SCCs

### L-001: Forced-pair normalized-inert machine

Core transition:

```text
ForcedPair -> NormalizedInert -> ForcedPair
```

Why both edges are real:

- The normalized capstone is constructed from and retains the original
  forced-pair packet.
- Forgetting the extra normalized-inert decoration literally recovers that
  forced-pair packet.

Why it is not progress by itself:

- The forward edge adds a minimizer, unique-all-Continue cap information, and
  tent-toll or saturation data.
- The return edge spends none of those fields and has no decreasing rank.

Current possible exits or refinements:

- actual three-role endpoint-law regeneration;
- strict endpoint ascent;
- a saturated raw descendant, followed by host or full screening and then a
  concentrated packet;
- an unsaturated tent-toll or fixed-cap barrier;
- maximal-ray geometric refinements.

None currently consumes every realization of this SCC.

Active capstone:

`questions/FIN4_RENEWABLE_ORIENTATION_OR_COUNTEREXAMPLE.md`

This question is intentionally stated for the whole component. Solving only
one preferred forward arm does not answer it if another return edge remains.

Counterexample interpretation:

A Fin4 counterexample would have to realize this or a later completed SCC
indefinitely while retaining positive global minimum debt. Existing exact
regressions realize local circulation only at zero global minimum debt.

## Redirected branches that do not count as eliminated SCCs

### R-001: Quantitative tail escape

Current route:

```text
tail escape -> positive-mass purification -> concentrated packet
```

Status:

Redirected. The tail-escape label is no longer a terminal obstruction, but its
difficulty survives in the concentrated-packet consumer.

### R-002: Visible deleted-survival host

Current route:

```text
visible host -> host compression -> concentrated packet
```

Status:

Redirected by checked actual-source host-compression and fixed-endpoint
adapters.  The resulting concentrated/forced-pair consumer remains open.

### R-003: Fully screened Zeno source

Current route:

```text
full screening -> at most four finite-clock clears -> concentrated packet
```

Status:

Redirected by the checked finite-clock clearing family and its packet
consumer. The weighted cap-defect-to-admissible-return question remains
interesting but is optional for eliminating full screening.

### R-004: Strict-ray geometric cases

Labels include:

- finite all-Continue fixation;
- positive-absorption limiting root;
- binding cardinality three;
- full binding;
- ballistic or diffuse normalized flow.

Current route:

Every such node retains the originating forced-pair packet, which already has
the normalized return-or-inert dispatch.

Status:

Auxiliary refinements, not presently independent terminal SCCs. Their extra
geometry may help consume L-001, but merely classifying them does not eliminate
L-001.

## Open sink or adapter nodes

These nodes have no proved complete outgoing dispatch. Until their missing
edges are resolved, the complete SCC decomposition is unknown.

They may have independent node questions, but they are not counted as SCC
questions until their outgoing graph is complete. In particular,
`questions/FIN4_ATLAS_CONCENTRATED_SINGLETON.md` attacks O-001 without
asserting that O-001 is already a terminal SCC.

### O-001: Concentrated collision consumer

Available data:

- source-attached fixed-mass pure pair;
- minimum post-row tail;
- one zero marked coordinate;
- one fixed positive marked defect or paid move;
- exact mover-cap preservation and own-debt subtraction.

Missing edge:

Control cross-coordinate cap leakage sufficiently to obtain terminal
approximants, an exact admissible charged return, or renewable minimum-fibre
rank descent.

### O-002: Three-role target ascent

Available data:

An actual endpoint law with total debt strictly above the incoming minimum.

Missing edge:

A source-preserving return, contradiction, or finite-rank regeneration.

Active node question:

`questions/FIN4_THREE_ROLE_TARGET_ASCENT_CONSUMER.md`

### O-003: Support handoff

Available data:

A coherent one-time strict support inclusion between a half-mixture parent and
an endpoint, with tangent-family re-extraction.

Missing edge:

Reconstruct a complete `FinFourMinimumAtomProducer`, including the endpoint
joint law and causal atom, so that the support decrease is renewable.

Active node question:

`notes/CODEX_ROOT__RESOLVED_FIN4_RENEWABLE_CANONICAL_SUPPORT_HANDOFF.md`

### O-004: Unsaturated normalized-inert barrier

Available data:

A unique-all-Continue cap point with a global root-defect tent toll or
fixed-cap barrier.

Missing edge:

Convert the unsigned defect barrier into executable chronology, a terminal
contradiction, or a renewable finite rank.

Active focused questions:

- `questions/FIN4_STRICT_NORMALIZED_INERT_IMPOSSIBILITY_OR_MODEL.md`;
- `questions/FIN4_INERT_MACHINE_CERTIFICATE_SEARCH.md` for the exact negative
  or semialgebraic-impossibility route.

## Architecture no-gos that do not count as SCC elimination

The following are important, but they eliminate proposed methods rather than
actual recurrent source components:

- raw censored total variation is not a progress metric;
- exact retained-tail timing Nashification collapses to all Continue near the
  positive minimum;
- semantic or full-law recurrence does not control response reentry loss;
- a paid mover's exact debt decrease does not prevent cap leakage into another
  coordinate;
- a one-time strict support inclusion is not renewable source descent;
- aggregate root-defect charge is not an admissible payoff chronology;
- unilateral payoff gain is not the absorption charge used by the cumulative
  admissible-return compiler;
- normalized ballistic recurrence need not make the selected chain periodic;
- same-law or same-cap diagonal squares need not have a fixed-law feasible
  direction.

These results prevent repeated investment in false splices, but they do not
change the SCC score above.

## Candidate progress events

The score changes only when one of these occurs:

1. Prove O-001 has a terminal or renewable-rank consumer.
2. Prove O-002 returns to an existing source node or is impossible.
3. Complete O-003's source reconstruction and verify that its rank decrease is
   renewable.
4. Consume or eliminate O-004.
5. Prove that one of O-001 through O-004 feeds L-001, thereby completing the
   graph and possibly enlarging the known SCC.
6. Construct a positive-gap reward table that realizes a live SCC
   indefinitely. This settles Fin4 negatively rather than lowering the score.

## Question-maintenance policy

- Every confirmed live terminal or nonterminal SCC receives exactly one active
  capstone question.
- The question states the complete source packet for the component and accepts
  a terminal consumer, renewable rank exit, impossibility proof, or actual
  positive-gap realization.
- Different SCC questions are independently attackable once their input
  packets are self-contained.
- A node with unknown outgoing edges may have a node-consumer question, but it
  is not labeled an SCC capstone yet.
- An eliminated SCC has no active question; its old question files remain only
  as resolution records.
- When two components are proved mutually reachable, their questions are
  merged rather than maintained as falsely independent tasks.

## Change log

### 2026-08-28

- Replaced the provisional unknown-denominator map by the complete
  three-mode source-preserving atlas.
- Recorded the two exact terminal SCCs: uniform escape and minimum return.
- Reclassified normalized inert, three-role, support, strict-ray, and response
  objects as internal refinements rather than additional global modes.
- Established the initial conservative ledger.
- Counted one eliminated semantic SCC: same-stage monodromy.
- Distinguished its two source tags from the semantic SCC count.
- Recorded the live forced-pair normalized-inert SCC.
- Classified tail escape, deleted-survival host, full screening, and strict-ray
  geometry as redirects rather than SCC eliminations.
- Recorded four open nodes preventing a complete SCC denominator.
- Added exact node questions for three-role target ascent and renewable
  canonical support handoff.
- Updated host compression, full screening, singleton compression, and
  self-tail routing to their checked status.
- Added focused questions for direct strict-inert elimination and exact
  inert-machine certificate search.
