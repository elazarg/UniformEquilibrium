# All-nonempty serial endpoint closure does not enter the checked Fin4 no-cycle theorem

Author: SERIAL_ENDPOINT_AUDITOR

## Status

The proposed composition has a valid first half and an invalid second half.
Under the Fin4 hard residual, the singleton collision inequality and the
pure-nonsingleton all-behavior toggle inequality do give a serial strict
same-stage relation on all fifteen nonempty coalitions, over one fixed actual
profile, date, reach, and post-date tail.  Finite iteration therefore gives a
literal horizontal closed toggle cycle with a uniform gain floor.

That cycle does **not** contradict
`not_nonempty_finFourSameStageEndpointClosedSegment`.  The checked theorem is
about a different graph: its vertices are nonsingleton coalitions, a route to
a singleton is terminal, and every retained edge is one nonsingleton-to-
nonsingleton toggle.  The proof uses this terminal convention to exclude
pairs from a closed segment.  An all-nonempty cycle may alternate singletons
and pairs and need not contain any forbidden nonsingleton closed segment.

This conclusion independently reproduces the core result and boundary in
`ATLAS_FALSIFIER__CONCENTRATED_SINGLETON_FULL_GAP_TOGGLE_CYCLE.md`.  It is an
exact interface audit, not a new atlas contraction, and is not proposed for
export.

## Question audited

Let `reward` be a Fin4 quitting table with a terminal exploitability witness
of gap \(\gamma>0\) and the punishment-normal fields of the quantitative hard
residual.  Fix an actual behavioral profile \(\sigma\), a date \(t\), and
write \(L\) for the probability that the unique live history reaches \(t\).
For each nonempty coalition \(A\), let \(\rho_A\) be the literal sibling of
\(\sigma\) obtained by replacing only the root at \(t\) by the pure quitting
coalition \(A\).

Can the following two facts be combined into a serial endpoint dispatch on
all nonempty coalitions and then contradicted by the checked Fin4 same-stage
monodromy impossibility theorem?

1. At a singleton \(\{j\}\), some outsider \(o\) has
   \[
   r_o(\{j,o\})-r_o(\{j\})\ge\gamma.
   \]
2. At every pure nonsingleton coalition, continuation screening and positive
   minimum debt provide a strict best endpoint edge (indeed the terminal
   witness itself provides a toggle gain at least \(\gamma\)).

The answer is: the serial all-nonempty cycle is valid, but the proposed
contradiction is not.

## Exact sources inspected

- `QuittingTerminalExploitabilityWitness.exists_leave_or_join_gain` and
  `QuittingTerminalExploitabilityWitness.not_isQuittingSureExitSet` in
  `UniformEquilibrium/Quitting/Classification/TerminalExploitabilityToggles.lean`.
- `QuittingTerminalExploitabilityWitness.exists_atomicCollision_gain_of_normal`
  in
  `UniformEquilibrium/Quitting/Boundary/Repair/PunishmentNormalAtomicCollision.lean`.
- `QuittingSameStageEndpointEdge`, `QuittingSameStageSingletonRoute`, and
  `QuittingSameStageEndpointDispatch` in
  `Research/Quitting/SameStageEndpointMonodromy.lean`.
- `quittingPureNonsingleton_screenedDispatch` and
  `exists_pureNonsingletonScreened_terminalOrbit_or_closedSegment` in
  `Research/Quitting/PureNonsingletonCollisionScreening.lean`.
- `sameStageEndpointTrace_period_eq_two_of_effectiveSupport_card_le_four` and
  `not_nonempty_finFourSameStageEndpointClosedSegment` in
  `Research/Quitting/SameStageEndpointMonodromyImpossible.lean`.
- `quittingFinFourPositiveMassNonsingleton_nonempty_screenedEndpoint` in
  `Research/Quitting/FinFourPureNonsingletonCollisionScreening.lean`.

## 1. The all-nonempty serial relation is valid

For \(|A|\ge2\), apply the terminal exploitability witness to the pure
sure-exit profile with quitting coalition \(A\).  Under any unilateral
behavioral replacement at least one prescribed member of \(A\) still quits
immediately.  Thus the deviator's complete behavioral payoff is bounded by
the better of its two membership endpoints.  The checked declaration
`exists_leave_or_join_gain` consequently yields a player \(i\) such that

\[
r_i(A\mathbin\triangle\{i\})-r_i(A)\ge\gamma.
\tag{1}
\]

The target is nonempty: if \(i\in A\), then \(|A|\ge2\); if \(i\notin A\),
the toggle is a join.  Pure nonsingleton screening gives the same conclusion
with the weaker but source-attached floor \(D_*/4\) at the root and
\(LD_*/4\) in the whole profile.  The terminal witness gives the sharper
table-level floor \(\gamma\).

For \(A=\{j\}\), punishment normality and
`exists_atomicCollision_gain_of_normal` give an outsider \(o\ne j\) with

\[
r_o(\{j,o\})-r_o(\{j\})\ge\gamma.
\tag{2}
\]

Equations (1)--(2) select a nonempty strict toggle from every nonempty
coalition.  At the fixed reached row their literal payoff gains are

\[
U_i(\rho_{A\triangle\{i\}})-U_i(\rho_A)
 =L\bigl(r_i(A\triangle\{i\})-r_i(A)\bigr)
 \ge L\gamma.
\tag{3}
\]

All siblings have exactly the same behavior before and after date \(t\), and
the marked stage mass is exactly \(L\).  Since only the mover's prescribed
strategy changes, its unrestricted best-response envelope is unchanged, so

\[
d_i(\rho_{A\triangle\{i\}})
=d_i(\rho_A)-
 \bigl(U_i(\rho_{A\triangle\{i\}})-U_i(\rho_A)\bigr).
\tag{4}
\]

Choosing one outgoing toggle at each of the fifteen vertices and iterating
produces a simple literal closed cycle.  This is a valid source-preserving
horizontal producer.

## 2. Exact mismatch with the checked no-cycle theorem

`QuittingSameStageEndpointEdge` is indexed by

```text
source target : QuittingNonsingletonCoalition (Fin 4)
```

and its target is one single-player routed toggle of its source.
`QuittingSameStageEndpointDispatch` is not a serial relation on all nonempty
coalitions.  It is the disjunction

```text
QuittingSameStageSingletonRoute source
or
exists nonsingleton target, QuittingSameStageEndpointEdge source target.
```

For every pair, `quittingSameStageSingletonRoute_of_card_eq_two` makes the
first disjunct true without any payoff sign.  Consequently a dispatched
closed segment contains no pair.  This is the decisive input in
`sameStageEndpointTrace_period_eq_two_of_effectiveSupport_card_le_four`: every
vertex in a closed segment has cardinality at least three, so on support of
size at most four the cardinalities alternate between three and four.  The
segment is then forced to have period two, which exact positive mover-debt
subtraction rules out.

Once singleton vertices are allowed, this cardinality argument disappears.
For example, the simple cycle

\[
\{a\}\to\{a,b\}\to\{b\}\to\{b,c\}\to
\{c\}\to\{a,c\}\to\{a\}
\tag{5}
\]

uses only singleton and pair vertices.  It has no all-nonsingleton closed
subsegment at all.

Nor can one compress a pair-to-singleton-to-pair passage into a checked
endpoint edge.  The two steps generally have different movers and change two
Boolean coordinates.  The composite target is not a one-coordinate routed
coalition, the two gains belong to different payoff coordinates, and there
is no single-mover debt identity of the form required by
`QuittingSameStageEndpointEdge`.

Therefore neither
`not_nonempty_finFourSameStageEndpointClosedSegment` nor its generic
support-at-most-four parent theorem applies.

## 3. Exact finite regression for the attempted combinatorial inference

The failure is not merely a Lean typing inconvenience.  There are rational
reward tables whose pure membership graph has all the local properties used
by the proposed serial argument and contains (5).

Let the players be \(a,b,c,d\), and select the following outgoing edges:

\[
\begin{array}{llll}
a\to ab,&ab\to b,&b\to bc,&bc\to c,\\
c\to ac,&ac\to a,&d\to ad,&ad\to a,\\
bd\to b,&cd\to c,&abc\to ab,&abd\to ab,\\
acd\to ac,&bcd\to bc,&abcd\to abc.
\end{array}
\tag{6}
\]

Each edge toggles the unique player in the symmetric difference.  For every
selected edge \(A\to A\triangle\{i\}\), set

\[
r_i(A)=0,\qquad r_i(A\triangle\{i\})=1,
\tag{7}
\]

and set every reward coordinate not fixed by (7) to zero.  These assignments
are consistent: for a fixed player and opponent background, the corresponding
membership edge occurs at most once in (6), and no selected edge is paired
with its reverse.

Every nonempty coalition now has a selected strict best endpoint of gain one;
every singleton's selected edge is a join; and the first six selected edges
form (5).  Thus seriality, a common positive gain floor, exact same-stage
realization, common tail, and exact own-debt subtraction do not imply the
checked no-cycle conclusion.

This regression is deliberately not a positive-gap table: all own singleton
rewards are zero, so all-Never is an exact terminal Nash profile and the true
global minimum debt is zero.  Its role is exact and limited.  It proves that
the contemplated contradiction cannot use only the serial local consequences
of the hard residual; some additional global-minimum/source argument or a new
consumer of singleton-containing horizontal cycles would be necessary.

## 4. Strongest surviving statement and Lean handoff

The strongest sound composition is:

> From a source-attached singleton row under the Fin4 hard residual, construct
> a literal same-stage strict full-gap cycle on the nonempty Boolean cube,
> with one common past, reach, marked date, post-date tail, stage-mass floor,
> and exact mover-debt subtraction on every edge.

A suitable Research declaration would use a new vertex type of nonempty
coalitions and a new cycle structure, rather than coercing the output to
`QuittingSameStageEndpointDispatch`.  This exact theorem and its finer finite
geometry have already been developed in
`ATLAS_FALSIFIER__CONCENTRATED_SINGLETON_FULL_GAP_TOGGLE_CYCLE.md`; the present
audit supplies no reason to duplicate it in Lean.

To obtain a genuine closure one still needs one of:

1. a consumer of arbitrary source-matched singleton-containing horizontal
   toggle cycles;
2. a theorem using additional hard-residual provenance to force an
   all-nonsingleton subcycle; or
3. a chronological or minimum-fibre rank construction that uses more than
   seriality and the edgewise own-debt identities.
