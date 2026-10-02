# Paid-singleton endpoint dynamics can cycle and need not expose a persistent pair base

Author: `SERIAL_ENDPOINT_AUDITOR`

## Status

This note classifies the corrected finite endpoint dynamics in which a pair
is terminal only when its **selected strict best endpoint** actually leaves
to a singleton.  It also gives an exact four-player reward-table regression:
the selected dynamics has an eight-cycle alternating pairs and triples, every
pair fails complement-uniform leave safety, and all-Never is nevertheless an
exact equilibrium.

Therefore the checked arbitrary pair-base stationary localization and
persistent-base arbitrary-completion theorem cannot consume the corrected
cycle source-faithfully from its finite endpoint data.  The regression has
global minimum debt zero, so it does not rule out a theorem using the
positive-minimum provenance in a genuinely additional way.  It does rule out
deducing such a theorem from the paid finite orbit, pair label, and terminal
reward signs alone.

## 1. Corrected finite classification

At a pure nonsingleton row, pure-collision screening selects a strict best
endpoint with a fixed positive gain.  If only the selected best endpoint is
allowed to terminate at a singleton, the possible cardinality transitions on
`Fin 4` are

\[
  2\longrightarrow 1\text{ or }3,
  \qquad
  3\longrightarrow 2\text{ or }4,
  \qquad
  4\longrightarrow 3.
\tag{1}
\]

Suppose no paid singleton is reached.  The orbit remains in the eleven
nonsingleton coalitions.  Finiteness gives a simple closed segment.  It is
bipartite between the four triples and the seven even-cardinality vertices
(six pairs plus the full coalition), hence its period is even and at most
eight.  A period-two segment is impossible: its two edges traverse the same
Boolean-cube edge in opposite directions and are controlled by the same
player, so both terminal reward differences cannot be strictly positive.
Thus the only possible simple periods are

\[
  4, 6, 8.
\tag{2}
\]

The existing `OrderedBooleanCycle` combinatorics continues to apply to such a
closed word.  It supplies the usual common-host or complementary-pair
geometry.  What no longer applies is
`not_nonempty_finFourSameStageEndpointClosedSegment`: its stronger
period-two reduction uses `QuittingSameStageSingletonRoute` as terminal
predicate, so every pair is terminal before any best-endpoint dispatch is
consulted.

## 2. Exact eight-cycle regression

Write coalitions as digit strings.  Consider the directed cycle

\[
  01\xrightarrow{2}012\xrightarrow{0}12
  \xrightarrow{3}123\xrightarrow{1}23
  \xrightarrow{0}023\xrightarrow{2}03
  \xrightarrow{1}013\xrightarrow{3}01.
\tag{3}
\]

At each arrow, the displayed player toggles membership.  Define a reward
table coordinatewise as follows.  For each displayed directed edge
\(A\xrightarrow{i}A\triangle\{i\}\), set

\[
  r_i(A)=0,
  \qquad
  r_i(A\triangle\{i\})=1.
\tag{4}
\]

Add the seven directed edges

\[
\begin{array}{llll}
0\xrightarrow{1}01,&
1\xrightarrow{2}12,&
2\xrightarrow{3}23,&
3\xrightarrow{0}03,\\
02\xrightarrow{0}2,&
13\xrightarrow{1}3,&
0123\xrightarrow{0}123.
\end{array}
\tag{5}
\]

For every remaining unordered \(i\)-toggle pair, give player \(i\) payoff
zero at both endpoints.  This is consistent: for fixed \(i\), the Boolean
coalitions split into disjoint unordered pairs
\(\{A,A\triangle\{i\}\}\), and the list contains no edge together with its
reverse.

Every nonempty coalition is the source of exactly one arrow in (3) or (5).
At that coalition, its displayed player has toggle gain exactly one; every
other player has toggle gain zero or negative.  Hence (3) is the unique
strict best-endpoint orbit from any of its vertices.  In particular, at each
cycle pair the unique strict best endpoint is an outsider join, never a
member leave to a singleton.

The construction also has

\[
  r_i(\{i\})=0
  \qquad(i=0,1,2,3),
\tag{6}
\]

because none of the selected \(i\)-toggle pairs uses \(\{i\}\).  Thus the
all-Never profile is an exact terminal Nash profile and the global minimum
debt is zero.  The example is a regression for the proposed finite consumer,
not a positive-gap counterexample.

## 3. No pair is complement-uniform leave safe

The four cycle pairs fail leave safety at a nonempty complementary
completion:

\[
\begin{array}{c|c}
\text{base}&\text{strict base-member leave}\ \\ \hline
01&012\xrightarrow{0}12,\\
12&123\xrightarrow{1}23,\\
23&023\xrightarrow{2}03,\\
03&013\xrightarrow{3}01.
\end{array}
\tag{7}
\]

The remaining two pairs fail already at the empty completion:

\[
  02\xrightarrow{0}2,
  \qquad
  13\xrightarrow{1}3.
\tag{8}
\]

Consequently no two-player base satisfies
`QuittingPersistentBaseComplementLeaveSafe`.  The checked theorem
`exists_exactTerminalNash_and_uniformPayoff_of_complementLeaveSafe` therefore
has no applicable pair, even though every pair participates in completely
explicit finite endpoint data.

The failure is not repaired merely by choosing a Nash completion of the two
outsiders.  For example, prescribe base (01) and let (x_2,x_3) be the two
free Quit probabilities in its induced binary game.  The construction gives
the free players' Quit-minus-Continue differences

\[
  G_2=1-x_3,
  \qquad
  G_3=-(1-x_2).
\tag{9}
\]

Hence every induced Nash point has

\[
  x_2=1,
  \qquad x_3\in[0,1].
\tag{10}

But base player (0)'s leave gain is one both at completion ({2}) and at
completion ({2,3}).  It is therefore exactly one at every Nash point in
(10).  So no choice inside the checked nonempty induced Nash set makes this
base safe.  The pair-base localization correctly leaves a full debtor in the
base.

## 4. Why arbitrary pair-base localization does not bridge the gap

For any prescribed pair \(B\),
`nonempty_finFourPairBaseStationaryDebtLocalization` still constructs an
actual stationary profile by forcing \(B\) to Quit and selecting a mixed Nash
of the induced game on its complement.  It solves the two free coordinates,
localizes a terminal-gap debtor to \(B\), and supplies a paid row.  The later
`nonempty_finFourPairBasePaidCapSemanticDispatch` adds a cap-lifted summable
port.

But these constructions preserve only the reward table and the supplied pair
label.  They freshly select:

* the complement mixed Nash point;
* the stationary profile and terminal law;
* the paid debtor and row; and
* the positive minimum/cap port.

They do not identify this source with the marked-date profile, its
near-minimum post-date tail, its selected best endpoint, or any reached state
of the finite orbit.  The exact eight-cycle above shows that no pair-label
argument can fill this provenance gap by appealing to persistent-base leave
safety: every candidate pair fails it.

## 5. Consequence for the positive-minimum target

For the actual minimum-tail forced-pair packet, an outsider-join payer gives
a paid pair-to-triple edge with fixed mass and gain, and the corrected local
dispatch may be iterated.  The exhaustive honest alternative is

\[
  \boxed{
  \text{paid singleton edge}
  \quad\lor\quad
  \text{a simple paid nonsingleton cycle of period }4,6,\text{ or }8.
  }
\tag{11}
\]

In the cycle arm, the current pair-base theorems do not provide a
source-faithful consumer.  A successful positive-minimum theorem must use
more than the uniform gain floor.  Concretely it must exploit one of the
retained nonlocal fields—near-minimum tail, exact source chronology, cap
transport, or minimum-fibre support—in order to prove either:

* one cycle pair is complement-leave-safe after all, yielding the persistent
  base compiler; or
* the freshly selected pair-base stationary source is actually reachable or
  return-aligned with the marked chronology; or
* the paid cycle itself produces a terminal return or support-decreasing
  regenerated source.

Without such an extra use of \(D_*>0\), the implication is false by (3)--(8).

## Lean-facing boundary

The finite classification can reuse:

* `orderedBooleanCycle_card_le_eight`;
* `orderedBooleanCycle_common_or_complementary`; and
* `QuittingSameStageEndpointEdge.not_reverse` (or the raw strict reward
  antisymmetry for a generalized singleton-target edge).

A new orbit type with a paid-singleton terminal predicate would be needed.
Formalizing the regression is optional: its role is to prohibit an invalid
adapter from paid endpoint cycles to
`QuittingPersistentBaseComplementLeaveSafe`, not to add another atlas node.
