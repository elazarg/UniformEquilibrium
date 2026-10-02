# Adversarial review of `EXTERNAL__PURE_COLLISION_SCREENING`

Reviewer: `STRENGTHENER`

## Verdict

**PASS for the central ordinary-mathematics contraction, after two required
statement/interface corrections.**  A pure nonsingleton root really screens
off every player's continuation debt, and this gives a no-tail same-stage
dispatch with a stronger gain constant than the existing low-tail dispatch.
The checked effective-support-at-most-four monodromy impossibility applies
verbatim once the new dispatch constructs the existing
`QuittingSameStageEndpointEdge` relation.  Therefore a positive-mass
nonsingleton marked row on `Fin 4` can be routed to a literal singleton at the
same date without any tail-debt hypothesis.

Two sentences in the submitted note need correction before export:

1. The uniform `lambda * D_* / 4` floor holds for every strict edge **after a
   pure nonsingleton row has been installed**.  It does not follow for the
   preliminary partial-purification steps.  Those steps use best endpoints
   and are nonnegative own-payoff moves, but their positive gains can be
   arbitrarily smaller than the displayed floor because a partially mixed
   root may transport the minimum debt from its tail.
2. The currently checked combined partial-purification/dispatch declarations
   still require `lowTail`.  One cannot call them unchanged.  A short new
   no-tail pure-row dispatch theorem is required.  After that theorem, the
   existing raw finite-orbit and generic monodromy-impossibility declarations
   accept exactly the constructed edge relation and need no tail bound.

Neither correction weakens the advertised atlas contraction.  In fact the
preliminary purification can be omitted from the mathematical proof: the
literal pure-root profile for the already marked coalition is an actual
profile, has stage mass equal to the original live mass, and preserves every
live root outside the marked date.  The profitable orbit may start there.

This review does not assert a Lean check of the new adapter.

## 1. Exact debt-screen audit

Let `tau` be an actual post-date tail with semantic pair `y`, and let `q_C` be
the pure root for a coalition `C` with `2 <= |C|`.  For each player `i`, there
is a member `j in C \ {i}`.  Thus, after forcing `i` to Continue, `j` still
Quits surely and

\[
  \operatorname{OppCont}_i(q_C)=0.
\]

The direction of both checked arbitrary-root estimates is exactly the one
used in the note.  For actual `y`, coordinate debt is nonnegative, and

\[
\delta_i(y^u,q_C)
\le d_i(q_C\triangleright y)
\le \delta_i(y^u,q_C)
   +\operatorname{OppCont}_i(q_C)d_i(y).
\]

These are

```text
quittingRootCoordinateNashDefect_le_terminalSemanticDebt_prefix
quittingTerminalSemanticDebt_prefix_le_nashDefect_add_transport
```

in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPlateauDefectCharge.lean`.
The first inequality is not being reversed.  Substitution of the zero
opponent-Continue factor gives equality coordinatewise.  The more specialized

```text
quittingTerminalSemanticDebt_prefix_eq_coordinateNashDefect_of_other_sureQuitter
```

in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticReachedRowDebtLocalization.lean`
proves the same fact directly, one coordinate at a time.

It is important that the global minimum lower bound is applied to the
**current suffix profile starting at the marked row**, not to the original
whole prefixed profile.  The latter can carry debt at earlier dates.  The
current suffix is an actual behavioral profile, so its semantic pair lies in
the carrier and

\[
 D_*\le D(q_C\triangleright\tau)=\sum_i\delta_i(y^u,q_C).
\]

For `Fin 4`, some coordinate has defect at least `D_*/4`.  This is the valid
source of the edge floor.

## 2. Exact mass and gain constants

Let `L` be the original probability of reaching the marked date and let the
original unconditional stage mass of `C` be `m`.  Then `m <= L`.  Replacing
the marked root by the pure `C` root leaves every earlier root unchanged and
gives

\[
  \Pr(C\text{ at the marked date})=L.
\]

This is the checked identity

```text
quittingStageCoalitionMass_literalPureRootCoalitionProfile_eq_liveMass
```

in `Research/Quitting/SameStageEndpointMonodromy.lean`.

If `i` is the selected maximum-defect coordinate and its marked action is
changed to the exact best endpoint, then

\[
  U_i(p')-U_i(p)=L\delta_i\ge L D_*/4\ge mD_*/4.
\]

The exact payoff and own-debt identities are

```text
quittingTerminalPayoff_literalOneDateProfile_bestEndpoint_gain_eq
quittingTerminalSemanticDebt_literalOneDateProfile_bestEndpoint_eq_sub_gain
```

in the same module.  Since all profiles in the pure orbit have the same roots
before the date, their live mass is the same `L`.  Every pure routed coalition
therefore has stage mass **exactly** `L`; the checked edge field retains the
weaker no-loss inequality.  Thus the maximal constant is

\[
  \boxed{L D_*/4},
\]

not merely `lambda * D_*/4`, and the final singleton has mass `L`.

The existing edge structure only asks for

\[
  \lambda D_*/(2|I|)=\lambda D_*/8
\]

on `Fin 4`, so the new screened edge more than satisfies
`QuittingSameStageEndpointEdge.gain_floor`.

## 3. Where the preliminary purification does and does not fit

The checked

```text
quittingPartialPurification_exists_total_or_singleton
```

in `Research/Quitting/SameStageEndpointPurification.lean` has no tail-debt
premise.  It preserves the mass floor and the post-date semantic tail, and it
returns either a singleton or a fully pure nonsingleton root.  Hence it can be
used before the new screening lemma.

However, its intermediate carry steps are chosen coordinate-by-coordinate at
partially pure roots.  No checked field gives them a `D_*`-scale gain, and the
pure screening calculation does not apply until two sure quitters—and, for
the clean uniform construction, the complete pure root—are present.  The
submitted headline must therefore say:

> every strict **pure-orbit** edge has gain at least
> `lambda * D_* / 4`.

There is an even cleaner proof: use
`quittingLiteralPureRootCoalitionProfile` to install the displayed coalition
directly.  This is one literal actual profile, preserves all off-date live
roots, and raises the marked mass from `m` to `L`.  No preliminary path is
needed unless preserving a finite chain of unilateral best-endpoint updates
is independently desired.

## 4. Exact API boundary

The following checked theorems still contain `hlowTail` and cannot simply be
reused:

```text
quittingLiteralSameStage_exists_singleton_or_endpointEdge
quittingLiteralSameStage_dispatch
exists_quittingSameStage_terminalRoute_or_closedSegment_of_liveMass
exists_quittingSameStage_terminalRoute_or_closedSegment_of_sourceRow
quittingPartialPurification_then_sameStage_dispatch
quittingPartialPurification_then_finFourSameStage_dispatch
```

The missing Lean adapter is local.  It should prove, from minimum-carrier,
global-minimum, `D_*>0`, and a live-mass floor, that every pure nonsingleton
source satisfies

```text
QuittingSameStageEndpointDispatch reward profile stage minimum lambda source
```

using the zero-transport proof above.  Once this `hdispatch` is supplied,

```text
exists_quittingSameStage_terminalRoute_or_closedSegment
```

accepts it without any tail hypothesis.  Its closed segment has precisely
the existing edge relation.  Therefore

```text
sameStageEndpointTrace_false_of_effectiveSupport_card_le_four
not_nonempty_finFourSameStageEndpointClosedSegment
```

from
`Research/Quitting/FinFourProducerAtlas/MonodromyImpossible.lean`
apply literally; no new combinatorial theorem is needed.

The generic positive-singleton constructor

```text
FinFourSingletonStageStrongConcentratedPacket.nonempty_of_singleton_stageMass
```

then accepts the actual singleton endpoint.  To call this output an instance
of the existing **weak atlas core**, one must add a new origin constructor or
a source-indexed adapter, because the present
`FinFourAtlasWeakConcentratedSingletonOrigin.reached` constructor stores a
`FinFourAtlasConcentratedSingletonEndpoint` built from the old low-tail
producer.  Alternatively, construct the generic strong packet directly and
apply `consumerResult` with the retained source.  This is an interface seam,
not a mathematical obstruction.

## 5. Stronger finite Fin4 form

After the marked root is pure, no long orbit is needed.  A pure pair is
already terminal for `QuittingSameStageSingletonRoute`: make either member
Continue and the routed coalition is a singleton, whether or not that final
move is profitable.

The only nonterminal Fin4 vertices are triples and the universal coalition.
A strict path has at most three profitable edges:

1. a triple either drops immediately to a pair or joins to the universal
   coalition;
2. the universal coalition must leave to a triple, and it cannot undo the
   preceding strict join by the same player;
3. that new triple cannot undo the preceding strict leave, so it must leave
   to a pair.

Thus the maximal concrete conclusion is:

> Starting from a pure nonsingleton marked row on `Fin 4`, at most three
> strict same-stage best-endpoint updates, each of gain at least
> `L * D_* / 4`, reach a pure pair; one final mass-preserving endpoint route
> produces a singleton of stage mass exactly `L`.

If the starting coalition is already a pair there are no paid edges.  The
last pair-to-singleton route is not asserted profitable.

## 6. Small-cycle falsification tests

Two boundary examples show exactly what the checked monodromy theorem uses.
They are finite payoff-table tests, not positive-gap quitting-game examples.

First, pure better-response cycles do exist on four players if pair vertices
are not declared terminal.  Let

\[
\begin{aligned}
A_0&=\{0,1\},&A_1&=\{0,1,2\},&A_2&=\{0,2\},\\
A_3&=\{0,2,3\},&A_4&=\{0,3\},&A_5&=\{0,1,3\}.
\end{aligned}
\]

Assign the relevant mover payoff to be `1` at the target and `0` at the
source along

\[
A_0\xrightarrow{2}A_1\xrightarrow{1}A_2
\xrightarrow{3}A_3\xrightarrow{2}A_4
\xrightarrow{1}A_5\xrightarrow{3}A_0,
\]

with all unspecified values zero.  This is a strict Boolean better-response
cycle.  The Fin4 theorem excludes it only because every pair is already a
mass-preserving singleton-route terminal.

Second, the effective-support bound four is sharp combinatorially.  On five
players take

\[
A_0=\{0,1,2\},\quad A_1=A_0\cup\{3\},\quad
A_2=A_1\cup\{4\},\quad A_3=A_0\cup\{4\}.
\]

Set

\[
r_3(A_1)>r_3(A_0),\quad r_4(A_2)>r_4(A_1),\quad
r_3(A_3)>r_3(A_2),\quad r_4(A_0)>r_4(A_3).
\]

These four strict toggles form a closed cycle all of whose coalitions have
cardinality at least three.  It uses five effective labels and therefore does
not contradict the checked support-at-most-four theorem.

## 7. Maximal corrected theorem

The mathematically strongest clean statement supported by the argument is:

> **Pure-collision no-tail screening.**  Let a finite quitting table have a
> terminal-semantic minimum pair `z_*` with `D_*>0`.  Fix an actual profile,
> a date of live mass `L>0`, and any pure nonsingleton coalition at that date.
> Every such pure row either has a mass-preserving singleton route or has a
> best-endpoint edge of actual gain at least `L D_*/|I|`, satisfying the
> existing exact mover-debt and routed-mass fields.  A finite dispatch thus
> reaches a singleton or a closed same-stage segment.  If the segment's
> visited support has cardinality at most four, the checked monodromy theorem
> excludes it.  In particular on `Fin 4`, a singleton of stage mass exactly
> `L` is reached, with at most three positive pure-orbit edges.

For the submitted source-row formulation, take `L` to be the original live
mass.  Since the displayed atom mass is at least `lambda`, `L>=lambda`; this
recovers all advertised constants and removes the tail condition.

## Declarations inspected

- `quittingTerminalSemanticDebt_prefix_le_nashDefect_add_transport` and
  `quittingRootCoordinateNashDefect_le_terminalSemanticDebt_prefix` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPlateauDefectCharge.lean`;
- `quittingTerminalSemanticDebt_prefix_eq_coordinateNashDefect_of_other_sureQuitter`
  in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticReachedRowDebtLocalization.lean`;
- `quittingPartialPurification_exists_total_or_singleton` in
  `Research/Quitting/SameStageEndpointPurification.lean`;
- `QuittingSameStageEndpointEdge`,
  `quittingStageCoalitionMass_literalPureRootCoalitionProfile_eq_liveMass`,
  `quittingLiteralSameStage_exists_strictGain_or_singletonRoute`, and
  `exists_quittingSameStage_terminalRoute_or_closedSegment` in
  `Research/Quitting/SameStageEndpointMonodromy.lean`;
- `sameStageEndpointTrace_false_of_effectiveSupport_card_le_four` and
  `not_nonempty_finFourSameStageEndpointClosedSegment` in
  `Research/Quitting/FinFourProducerAtlas/MonodromyImpossible.lean`;
- `FinFourSingletonStageStrongConcentratedPacket.nonempty_of_singleton_stageMass`
  in `Research/Quitting/FinFourProducerAtlas/StrongConcentratedPacket.lean`.

