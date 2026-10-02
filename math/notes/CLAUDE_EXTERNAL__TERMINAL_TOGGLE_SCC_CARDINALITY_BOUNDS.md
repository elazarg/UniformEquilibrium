# Cardinality bounds for terminal toggle SCCs

Source and mathematical argument: Claude.  Codex Root audited and restated
the proof for the conference record.

## Current status

The finite graph theorem below is proved as ordinary mathematics.  It has not
been checked in Lean and has no downstream semantic consumer yet.  On `Fin 4`
it shows that every terminal strongly connected component of the full strict
membership-toggle graph contains a two-player coalition.  This is a useful
normal form, but it does not turn the component into a quitting chronology,
an admissible path, or a well-founded semantic descent.

The exact checked game input is
`QuittingTerminalExploitabilityWitness.exists_strictToggle_gain` in
`UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/StrictOrbit.lean`:
under a terminal exploitability witness, every coalition has a strict
profitable membership toggle.  The chronology and rank limitations are
recorded in `StaticCycleChronologyBarrier.lean` and
`StrictToggleWellFoundedBarrier.lean` in the same toggle diagnostics subtree.

## Setup

Let `I` be a finite player set of cardinality `n`.  On the Boolean cube of
coalitions, orient the edge between `A` and `A △ {i}` as

\[
A\longrightarrow A\mathbin\triangle\{i\}
\quad\Longleftrightarrow\quad
r_i(A\mathbin\triangle\{i\})>r_i(A),
\]

where the empty-coalition reward is zero.  Assume every vertex has an outgoing
edge.  Let `T` be a terminal strongly connected component of this full
directed graph.  Thus every improving toggle from a member of `T` remains in
`T`.

Put

\[
m=\min_{A\in T}|A|,
\qquad
M=\max_{A\in T}|A|.
\]

## Theorem

Every terminal component satisfies

\[
\boxed{m\le n-2\qquad\text{and}\qquad M\ge2.}
\]

### Upper-face proof

Suppose first that `m = n`.  Then `T = {I}`.  Terminality says every improving
toggle from `I` remains in `T`, but every toggle changes the coalition, so `I`
has no outgoing edge.  This contradicts the sink-free hypothesis.

Now suppose `m = n-1`.  Choose `A in T` of cardinality `n-1`, and let `x` be
its unique outsider.  An improving leave from `A` would have cardinality
`n-2`; terminality would put its target in `T`, contradicting minimality of
`m`.  Hence every improving toggle at `A` is a join.  Since `A` is not a sink,
the unique possible improving toggle is

\[
A\longrightarrow I
\]

by player `x`.

At `I`, every toggle is a leave.  Choose an improving leave by some player
`i`, and put `B=I\setminus\{i\}`.  Terminality gives `B in T`, and `|B|=n-1`
is again minimal.  Therefore no improving leave is possible from `B`; its
only possible improving toggle is the unique join by its outsider `i`:

\[
B\longrightarrow I.
\]

The two displayed strict inequalities compare the same player `i` at the
same adjacent coalitions in opposite directions, which is impossible.  Thus
`m <= n-2`.

### Lower-face proof

Suppose `M = 0`.  Then `T = {emptyset}`, again a sink.

Suppose `M = 1`.  At `emptyset`, some improving toggle must join a player
`j`; terminality puts `{j}` in `T`.  Since `{j}` has maximum cardinality, an
improving join from it would leave `T`.  Its required outgoing edge must
therefore be its only leave,

\[
\{j\}\longrightarrow\varnothing.
\]

This strictly reverses the preceding improvement by the same player `j`, an
impossibility.  Hence `M >= 2`.

## Fin4 corollary

For `I = Fin 4`, every terminal toggle SCC contains a coalition of cardinality
exactly two.

Indeed, the theorem supplies a vertex of cardinality at most two and one of
cardinality at least two.  A directed path between them inside the strongly
connected component changes cardinality by exactly one at each toggle, so it
passes through cardinality two.

The bound is sharp at the level of finite orientations: terminal classes with
minimum cardinality two can occur.  The supplied computation reported, among
21,298 sink-free random tables, terminal-class minimum cardinalities `0`, `1`,
and `2`, with `2` occurring 632 times and none at least `3`.  These counts were
not independently reproduced here and are retained only as experimental
evidence.

## Conjecture-facing meaning and limitation

This strengthens the terminal-SCC normal form in
`CLAUDE_EXTERNAL__PURE_TOGGLE_COLLAPSE_AND_SCC_BOUNDARY.md`: the unresolved
Fin4 recurrent object can always be rooted at an actual pair coalition.  It
therefore concentrates the remaining finite-label obstruction at pair level,
where complementary `2+2` geometry can become relevant.  It does not say that
the SCC contains a complementary pair, nor does it produce the earlier
singleton/common-host arm.

It is not yet a producer.  A pair vertex is a pure absorbing membership state;
the other vertices of its SCC are horizontal counterfactuals, not successive
reached times.  The remaining question is to consume a terminal toggle SCC
containing a pair into an executable approximate chronology, a charged exact
return, or a source-matched minimum-fiber rank exit.
