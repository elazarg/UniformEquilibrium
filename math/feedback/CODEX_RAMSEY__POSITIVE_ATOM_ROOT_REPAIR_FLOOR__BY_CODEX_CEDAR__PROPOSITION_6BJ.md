# Review of Proposition 6BJ

Reviewer: `CODEX_CEDAR`

Claim checked: a selected nonprojective proper principal of cardinality two
or three, aligned against a collision-rooted four-cycle of strict solo
preemptions, has exactly the shorter-cycle and literal-helper incidences
listed in Proposition 6BJ.

## Verdict

**PASS in the stated finite sign-alignment scope.**  The pair/triple split is
exhaustive, all matrix/preemption orientations are correct, the new cycle
margin is positive but need not retain the terminal gap, and the marked
owner/collider role claims use no hidden semantic compiler.  No repair is
required.

## Orientation and quantitative margin

The exact dictionary is

```text
QuittingSoloPreempts reward eta u v
  <-> v!=u and M(v,u)<=-eta,
```

where `M=normalizedSoloMatrix reward`.  Thus the rooted four-cycle

```text
v0 -> v1 -> v2 -> v3 -> v0
```

gives precisely

```text
M(v1,v0), M(v2,v1), M(v3,v2), M(v0,v3)<=-gamma.
```

Every extra hard-principal sign used in the proposition is strict.  For each
displayed shorter cycle, take `eta` at most `gamma` and at most the negation
of each extra negative entry on that cycle.  Finiteness and strictness make
this minimum positive.  The inherited four-cycle edges are then at most
`-eta`, and each strict closing entry is also at most `-eta`.  This proves the
claimed `QuittingSoloPreempts reward eta` cycles and also confirms the scope
qualification that `eta` need not equal `gamma`.

## Card-two principal

The checked `cardTwoCrossing` theorem supplies distinct `u,v`, reciprocal
strict negativity

```text
M(u,v)<0,  M(v,u)<0,
```

and one positive helper for each receiver row, with both helpers outside
`K={u,v}`.

If `K` is adjacent on the four-cycle, one of the two entries is its inherited
edge and the reciprocal entry closes the strict two-cycle.  If `K` is
opposite, say `{v0,v2}`, the chord `M(v0,v2)<0` closes
`v0->v1->v2->v0`, while `M(v2,v0)<0` closes
`v2->v3->v0->v2`.  The same argument applies after rotation.  Adjacent and
opposite exhaust unordered pairs of four cycle vertices.

For `K={owner,collider}`, reciprocal negativity gives

```text
eps = r_{owner}(owner)-r_{collider}(owner)>0.
```

Apply `exists_leave_or_join_gain` to
`P={owner,collider}`.  A collider-leave output would give

```text
r_P(collider)+gamma <= r_{owner}(collider),
```

whereas the immediate collision certificate gives the reverse inequality
with another `gamma`.  Adding them forces `2*gamma<=0`, impossible.  Owner
leave therefore yields

```text
r_P(owner)+gamma <= r_{collider}(owner)
                  = r_{owner}(owner)-eps,
```

which is exactly (6BJ.3), or the toggle theorem returns an outsider joining
`P` by at least `gamma`.  Both card-two helpers are outside this literal pair,
as claimed.

If `K` is disjoint from `{owner,collider}`, both are two-element subsets of
`Fin 4`, so `K^c={owner,collider}`.  Each helper lies in `K^c`, hence in the
literal owner/collider pair, though the two helpers may coincide.  Complements
of adjacent pairs are adjacent and complements of opposite pairs are
opposite.  When the two pairs meet in one label, the two-point complement
contains the other collision role and one unmarked label; the crossing fields
alone do not choose between them.  The note therefore states exactly the
available incidence and no more.

## Card-three principal

The checked `cardThree_externalHelper_or_cyclicBoundary` theorem is exhaustive
for a selected nonprojective principal of cardinality three.  Its complement
is the singleton omitted vertex `{x}`.

In the external-helper arm, the structure identifies `x` as the positive
helper and supplies one harmed receiver in `K` with `M(harmed,x)>0`.  The
receiver cannot be the successor of `x` on the rooted four-cycle, because the
inherited edge gives `M(successor(x),x)<=-gamma<0`.  If `x` is the owner or
collider, that marked role is therefore literally the helper.  If it is
neither, the other three vertices contain both marked roles.  No stronger
receiver/role alignment follows from the structure, matching the proposition.

In the cyclic-boundary arm, write the four-cycle order as

```text
x -> a -> b -> d -> x.
```

The inherited signs are `M(b,a)<0` and `M(d,b)<0`.  A strict three-point
forward or reverse orientation has one negative and one positive
off-diagonal entry in every row and column.  A cyclic orientation containing
the directed chain `a->b->d` must close with `d->a`, i.e.
`M(a,d)<0`; the reciprocal three entries are positive.  Hence

```text
a -> b -> d -> a
```

is the claimed literal strict three-cycle, with the positive `eta` chosen as
above.

If `x=owner`, the inherited edge `owner->a` is a one-step tail into this
three-cycle and the distinct collider belongs to it.  If `x!=owner`, the
owner belongs to the three-cycle; the collider is outside precisely when
`x=collider`.  These cases exhaust the marked-role placements and establish
the stated rooted/one-tail mapping.

## Exhaustiveness and scope

`exists_nonprojectivePrincipal_card_two_or_three` supplies exactly the two
cardinality cases used in the proof.  Within cardinality two, four-cycle
distance gives adjacent/opposite; within cardinality three, the checked
dispatch gives external helper/cyclic boundary.  The owner/collider clauses
are refinements of those cases, not additional assumed alternatives.

The output is only a shorter strict sign/preemption cycle or a finite helper
incidence, potentially at a margin smaller than the terminal gap.  It does
not produce a Bellman root, reached chronology, sure-exit set, semantic-debt
descent, or all-behavior uniform-payoff consumer.  The note preserves these
nonclaims, so no unjustified compiler conclusion is present.

## Sources inspected

- `notes/CODEX_RAMSEY__POSITIVE_ATOM_ROOT_REPAIR_FLOOR.md`, Proposition 6BJ.
- `FullSupportHardPrincipalSize.lean`:
  `exists_nonprojectivePrincipal_card_two_or_three`.
- `FullSupportHardPrincipalDispatch.lean`: `cardTwoCrossing` and
  `cardThree_externalHelper_or_cyclicBoundary`.
- `PreemptionCycle.lean` and `PreemptionGateDictionary.lean`: the definition
  of `QuittingSoloPreempts` and its exact normalized-matrix orientation.
- `TerminalExploitabilityToggles.lean`: `exists_leave_or_join_gain`.
- `ImmediateSingletonCollision.lean`: the owner/collider collision
  certificate and its quantitative inequality.
- `ThreeByThreeZeroDiagonalQ.lean`: the exact forward and reverse strict
  cyclic orientations.
