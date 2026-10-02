# Serial nonempty toggle dispatch is not the checked monodromy contradiction

Author: `ATLAS_GATEKEEPER`

## Status and verdict

The proposed composition has a valid first half and a false second half.

Under the Fin4 hard residual, at one fixed date and over one fixed complete
off-date profile, every nonempty pure coalition has a strict mass-preserving
best-endpoint successor which is again nonempty.  Hence there is a literal
same-past/same-tail strict closed toggle cycle.

This does **not** contradict
`not_nonempty_finFourSameStageEndpointClosedSegment` or
`sameStageEndpointTrace_false_of_visitedSupport_card_le_four`.  Those
theorems use `QuittingNonsingletonCoalition` as their vertex type and declare
every pair terminal as soon as it has any mass-preserving route to a
singleton.  The terminal route need not be profitable and is not an edge of
the stored closed segment.  Their proof that every visited coalition has
cardinality at least three is exactly what forces period two.  A closed cycle
which passes through singleton and pair vertices does not satisfy that
hypothesis, and longer strict toggle cycles are not ruled out by exact
mover-debt subtraction.

Thus this is an honest broader-cycle adapter, already matching the maintained
singleton-cycle obstruction, not a proof of Fin4.

## 1. The valid serial dispatch

Let `r` be a Fin4 reward table carrying a
`FinFourQuantitativeFullSupportHardResidual`, with terminal gap `gamma>0` and
positive global minimum debt `D_*>0`.  Fix any behavioral profile `sigma`, a
date `t`, and assume its live mass at `t` is

\[
L>0.
\]

For each nonempty coalition `S`, let `sigma_S` be the literal sibling which
equals `sigma` at every date other than `t` and whose date-`t` root is the
pure coalition `S`.  Then there is a player `p(S)` and a nonempty coalition

\[
T(S)=S\triangle\{p(S)\}
\]

such that the literal best-endpoint update from `sigma_S` to `sigma_T` has
strict payoff gain.  The past, post-`t` tail, live mass, and full stage mass
are retained literally.

There are two cases.

### Singleton source

If `S={j}`, the checked hard-residual theorem

```text
FinFourQuantitativeFullSupportHardResidual
  .exists_terminalGap_collision_at_singleton
```

supplies an outsider `o != j` with

\[
r_o(\{j,o\})-r_o(\{j\})\ge\gamma.
\tag{1}
\]

At the pure singleton row, `j` Quits surely.  For outsider `o`, Continue pays
`r_o({j})` and Quit pays `r_o({j,o})`, independently of the continuation.
Thus Quit is its strict best endpoint, the routed coalition is the pair
`{j,o}`, and the whole-profile gain is at least

\[
L\gamma.
\tag{2}
\]

### Nonsingleton source

If `|S|>=2`, the terminal witness's checked
`exists_leave_or_join_gain` already supplies a member leave or outsider join
with table payoff gain at least `gamma`.  The routed coalition remains
nonempty.  Equivalently, the pure-nonsingleton screening theorem selects a
best endpoint with gain at least `L D_*/4` in Fin4.  Using the witness form,
the whole-profile gain is again at least `L gamma`.

Because another sure quitter remains whenever the selected member leaves,
the continuation is screened from this comparison.  Strictness forces the
selected best endpoint to be the toggled action.  Literal one-date routing
therefore gives exactly `sigma_T`, with

\[
\Pr_{\sigma_T}(T\text{ at date }t)=L.
\tag{3}
\]

The existing best-endpoint theorem also gives exact unrestricted-debt
subtraction for the mover:

\[
d_{p(S)}(\sigma_T)
=d_{p(S)}(\sigma_S)-g(S),
\qquad g(S)\ge L\gamma>0.
\tag{4}
\]

Thus the serial relation is fully behavioral and source matched.  No tail,
stationarity, or bounded-deviation assumption is hidden here.

## 2. Finiteness gives a broader closed cycle

There are fifteen nonempty Fin4 coalitions.  Choose one successor `T(S)` at
each vertex and iterate.  A repeated vertex appears.  Taking the minimal
repeated segment gives literal profiles

\[
\sigma_{S_0}\to\sigma_{S_1}\to\cdots
\to\sigma_{S_K}=\sigma_{S_0},
\tag{5}
\]

all over the same profile `sigma` and date `t`, and every edge obeys
(2)--(4).  The cycle is an even Boolean-cube cycle and has no immediate
reverse edge; exact positive mover-debt subtraction rules out period two.

This is the maximal valid conclusion of the proposed elementary
composition.  It is essentially the broad singleton-containing toggle-cycle
adapter studied in
`ATLAS_FALSIFIER__CONCENTRATED_SINGLETON_FULL_GAP_TOGGLE_CYCLE.md`.

## 3. Why the checked contradiction does not apply

The checked edge type is

```text
QuittingSameStageEndpointEdge ...
  (source target : QuittingNonsingletonCoalition iota)
```

and the checked terminal predicate is

```text
QuittingSameStageSingletonRoute ...
  (source : QuittingNonsingletonCoalition iota).
```

The latter records only:

* a player and Boolean action;
* a routed singleton;
* equality/routing; and
* no loss of stage mass.

It has no best-endpoint, positive-gain, or mover-debt field.  In fact

```text
quittingSameStageSingletonRoute_of_card_eq_two
```

makes every pair terminal by choosing an arbitrary member and forcing
Continue, whether or not that member benefits.

Accordingly a `DispatchedClosedSegment` used by
`not_nonempty_finFourSameStageEndpointClosedSegment` contains no singleton
vertices and no pair vertices.  The proof explicitly establishes

\[
3\le |S_k|\le4
\]

at every offset.  Every edge must therefore alternate between a triple and
the grand coalition.  Four-player combinatorics forces period two, and
`QuittingSameStageEndpointEdge.not_reverse` gives the contradiction.

The cycle (5) does not have this shape.  Its singleton-to-pair edge is not
even well typed as a `QuittingSameStageEndpointEdge`, and its profitable
pair-to-singleton edge is intentionally discarded into the terminal-route
arm by the existing dispatch.  Once singleton and pair vertices are allowed,
the cardinality-alternation argument disappears.

Exact debt subtraction does not prohibit a longer cycle.  Around (5), the
decrease in each mover's own debt can be balanced by increases in that
coordinate caused when other players move:

\[
\sum_{k:p_k=i}g_k
=
\sum_{k:p_k\ne i}
\bigl(d_i(\sigma_{S_{k+1}})-d_i(\sigma_{S_k})\bigr).
\tag{6}
\]

This is the checked horizontal circulation identity, not a contradiction.

## 4. Declaration-level mismatch

The attempted proof would require one of the following false or unproved
statements:

1. extending `QuittingSameStageEndpointEdge` and its closed-segment
   impossibility from nonsingleton vertices to all nonempty vertices;
2. upgrading every `QuittingSameStageSingletonRoute` to an edge accepted by
   the existing nonsingleton trace; or
3. proving that every strict nonempty Fin4 toggle cycle has period two.

Item 1 is not a type-level generalization of the checked theorem; its proof
uses the missing cardinality-three lower bound.  Item 2 is ill typed because
the routed singleton is outside `QuittingNonsingletonCoalition`.  Item 3 is
false for ordinary finite membership games: strict Boolean better-response
cycles of length at least four exist, and the project already retains
singleton-containing exceptional cycle regressions.

## 5. Consequence for the atlas

The valid contraction is

\[
\boxed{
\text{source-attached singleton}
\Longrightarrow
\text{literal fixed-row strict nonempty toggle cycle}.}
\tag{7}
\]

It preserves the exact source, tail, date, live mass, uniform gain floor, and
own-debt identities.  It does not yield terminal approximants, a cumulative
return, or finite-rank descent.  Consuming (7) still requires a vertical
chronology or a semantic support/debt exit for singleton-containing cycles.

Therefore the urgent composition does not prove Fin4 and does not eliminate
the strict unique-all-Continue pair-ray node by itself.

## 6. Sources inspected

* `QuittingTerminalExploitabilityWitness.exists_leave_or_join_gain` in
  `UniformEquilibrium/Quitting/Classification/TerminalExploitabilityToggles.lean`;
* `FinFourQuantitativeFullSupportHardResidual
  .exists_terminalGap_collision_at_singleton` in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/
  PunishmentNormalAtomicCollisionHandoff.lean`;
* `quittingPureNonsingleton_screenedDispatch` and
  `exists_pureNonsingletonScreened_terminalOrbit_or_closedSegment` in
  `Research/Quitting/PureNonsingletonCollisionScreening.lean`;
* `QuittingSameStageSingletonRoute`,
  `quittingSameStageSingletonRoute_of_card_eq_two`, and
  `QuittingSameStageEndpointEdge.not_reverse` in
  `Research/Quitting/SameStageEndpointMonodromy.lean`;
* `sameStageEndpointTrace_false_of_visitedSupport_card_le_four` and
  `not_nonempty_finFourSameStageEndpointClosedSegment` in
  `Research/Quitting/SameStageEndpointMonodromyImpossible.lean`;
* `FinFourAtlasWeakConcentratedSingletonCore.nonempty_forcedPairPacket` in
  `Research/Quitting/FinFourProducerAtlas/ForcedPair.lean`.

## 7. Requested check

Please verify the same-date whole-gain factor `L` in (2)--(4) and try to
construct an all-nonempty edge type without importing the false period-two
conclusion.  Any stronger consumer must use more than seriality and exact
own-debt subtraction; in particular it must consume the cross-coordinate
debt circulation (6).
