# Four-cycle hard-principal alignment

Authors: `CODEX_RAMSEY`

Independent review:
[CODEX_CEDAR](../feedback/CODEX_RAMSEY__POSITIVE_ATOM_ROOT_REPAIR_FLOOR__BY_CODEX_CEDAR__PROPOSITION_6BJ.md)

Whole-packet review:
[CODEX_EULER](../feedback/FOUR_CYCLE_HARD_PRINCIPAL_ALIGNMENT__BY_CODEX_EULER.md)

This packet is exported at the user's explicit request for the complete
reviewed finite alignment program.  It proves finite same-label incidence and
strict cycle shortening, not a semantic compiler or chamber closure.

## Exact statement

Let

```text
reward : {S : Finset (Fin 4) // S.Nonempty} -> Payoff (Fin 4)
bound  : Real
residual : FinFourQuantitativeFullSupportHardResidual reward bound
certificate : QuittingImmediateSingletonCollision
  reward residual.witness.terminalGap.
```

Put

```text
o     = certificate.owner,
c     = certificate.collider,
gamma = residual.witness.terminalGap > 0,
M     = normalizedSoloMatrix reward.
```

Assume a marked collision-anchored geometry is one of the three rooted
four-cycle constructors.  Label its four distinct vertices in cycle order

```text
v0=o -> v1 -> v2 -> v3 -> v0,                       (1)
```

where the marker equation identifies `c` with exactly one of `v1,v2,v3`.
The four preemption edges say

```text
M(v1,v0), M(v2,v1), M(v3,v2), M(v0,v3) <= -gamma. (2)
```

Choose any proper nonprojective principal supplied by
`residual.exists_nonprojectivePrincipal_card_two_or_three`:

```text
K.card=2 or K.card=3,
not IsProjectiveQMatrix (principalMatrix M K).       (3)
```

Then the following exhaustive theorem-driven classification holds.

### A. Hard pair

Suppose `K={u,v}` has cardinality two.  The checked `cardTwoCrossing` theorem
gives

```text
M(u,v)<0,
M(v,u)<0,                                            (4)
```

and one positive packet helper for each receiver row outside `K`; the helpers
may coincide.

Every pair of a four-cycle is adjacent or opposite.

1. If `K` is adjacent, its cycle edge from (2) and its reverse entry from (4)
   form a strict reciprocal two-cycle.
2. If `K` is opposite, its two negative chord entries from (4), together with
   either two-edge arc of (1), form a strict directed three-cycle.

In either case there is an explicit `eta>0`, obtained by taking the minimum of
`gamma` and the finitely many strict reverse/chord margins, such that every
edge of the shorter cycle is

```text
QuittingSoloPreempts reward eta.
```

The theorem does not assert `eta=gamma`.

Two exact collision-role subcases are retained.

1. If `K={o,c}`, define

   ```text
   eps = reward({o})(o)-reward({c})(o) = -M(o,c)>0.
   ```

   Then at least one of the following holds:

   ```text
   reward({o,c})(o)+gamma+eps <= reward({o})(o),      (5)
   ```

   or

   ```text
   exists s notin {o,c},
     reward({o,c})(s)+gamma
       <= reward({o,c,s})(s).                         (6)
   ```

   Both packet helpers from `cardTwoCrossing` lie outside `{o,c}`.
2. If `K` is disjoint from `{o,c}`, then `K^c={o,c}`.  Consequently both
   existential packet helpers belong to the literal owner--collider pair,
   though they may coincide.  The complement pair has the same adjacency
   type as `{o,c}`.

If `K` meets `{o,c}` in exactly one player, the complement contains the other
collision role and one unmarked label, so no helper role is forced.

### B. Hard triple

Suppose `K.card=3` and let `x` be its unique omitted cycle vertex.  Apply

```text
residual.cardThree_externalHelper_or_cyclicBoundary.
```

1. **External-helper arm.**  The unique outside helper is literally `x`.
   It positively helps one receiver in `K`.  That receiver is not the
   successor of `x` in (1), because (2) makes the corresponding entry in
   column `x` strictly negative.  If `x=o` or `x=c`, that actual collision
   role is the helper; otherwise `K` contains both `o` and `c`.
2. **Cyclic-boundary arm.**  List the members of `K` after the omitted vertex
   in cyclic order:

   ```text
   x -> a -> b -> d -> x.
   ```

   The original cycle supplies

   ```text
   M(b,a)<0,
   M(d,b)<0.
   ```

   The strict three-point cyclic orientation forces

   ```text
   M(a,d)<0,
   ```

   and therefore the literal shorter cycle

   ```text
   a -> b -> d -> a.                                 (7)
   ```

   Taking `eta>0` below the three negative margins makes every edge of (7)
   `QuittingSoloPreempts reward eta`.

The marked-role geometry shortens on the same labels:

- if `x=o`, the original edge `o->a` is a one-step tail into (7), while the
  collider lies on (7);
- if `x!=o`, the owner lies on the rooted three-cycle (7);
- in the latter case the collider is outside (7) exactly when `x=c`, and
  otherwise the collider also lies on (7).

These are precisely the role patterns of the one-step-to-three and
rooted-three marked constructors, but at the possibly smaller margin `eta`.

## Conjecture-facing change

The finite marked-lasso program has seventeen constructors:

```text
8 with cycle length two,
6 with cycle length three,
3 rooted four-cycle constructors.
```

The reviewed two-cycle and three-cycle packets handle the first fourteen.
This theorem supplies the final theorem-driven pass for the last three.
Every selected hard principal on a rooted four-cycle now yields either:

```text
a shorter strict preemption cycle,
or a literal unique outside packet helper with exact collision-role incidence.
```

This completes the user-requested finite label-alignment classification.  It
does not eliminate the semantic geometries or close the full-support hard
residual.

## Definitions and assumptions

The normalized singleton matrix is

```text
M(i,j)=reward({j})(i)-reward({i})(i),
```

so `M(i,i)=0`.  A negative entry `M(v,u)<0` means that `u`'s singleton exit
strictly preempts receiver `v`; an inequality `M(v,u)<=-eta` is exactly
`QuittingSoloPreempts reward eta u v`.

`FinFourQuantitativeFullSupportHardResidual` stores the unrestricted terminal
exploitability witness, full-support normalized singleton packet, full normal
core, punishment-normality, and a proper nonprojective-principal obstruction
on one reward table.  Its packet masses are all strictly positive and satisfy
the normalized row-average inequalities.

`FinFourHardCardTwoCrossing` stores reciprocal negative entries on a hard pair
and positive helpers outside it.  A card-three hard principal is dispatched
to either `FinFourHardCardThreeExternalHelper` or
`FinFourHardCardThreeCyclicBoundary`.

## Proof

### 1. Pair distance and shorter cycles

Among four cyclic vertices, an unordered pair has graph distance one or two.
Distance one is adjacency; distance two is opposition.  Projective-Q failure
on a zero-diagonal pair gives both strict inequalities in (4).

For an adjacent pair, one direction is already an edge of (1), and the other
strict negative entry reverses it.  For an opposite pair, use one negative
chord to close the first length-two arc and the other chord to close the
complementary length-two arc.  Each is a three-cycle.  Since only finitely
many entries occur, the minimum of their positive strict margins and `gamma`
is positive and gives the common `eta`.

### 2. Owner--collider terminal alternative

Assume `K={o,c}` and apply the checked terminal-witness theorem

```text
residual.witness.exists_leave_or_join_gain {o,c}.
```

If the selected leaving member were `c`, its inequality would be

```text
reward({o,c})(c)+gamma <= reward({o})(c),
```

while the collision certificate says

```text
reward({o})(c)+gamma <= reward({o,c})(c).
```

Adding contradicts `gamma>0`.  Hence either the theorem selects an outsider
join, which is exactly (6), or the leaving member is `o` and

```text
reward({o,c})(o)+gamma <= reward({c})(o).
```

The hard-pair entry `M(o,c)<0` says

```text
reward({c})(o)+eps=reward({o})(o),
```

so (5) follows.  The helper statements are exact complement/cardinality
identities in `Fin 4`.

### 3. Card-three dispatch

Let `x` be the unique complement of `K`.  In the external-helper arm, the
structure's complement field makes its outsider equal to `x`.  Its positive
entry cannot be in the successor row of `x`, because that exact matrix entry
is at most `-gamma` by (2).  The owner/collider claims are then membership
identities.

In the cyclic-boundary arm, a strict orientation on three labels has one
negative incoming entry in each row.  The two known consecutive signs
`M(b,a)<0` and `M(d,b)<0` select the unique orientation and force the closing
sign `M(a,d)<0`.  This proves (7); taking the finite minimum gives `eta>0`.
Rotating the cycle to the owner, or retaining the omitted-owner tail, proves
the role mapping.

The pair/triple cardinality split and the existing card-three dispatch are
exhaustive, completing the proof.

## Probability and behavioral-deviation audit

The hard-principal incidence proof is deterministic finite matrix algebra.
It introduces no public randomization, conditioning, stopping-time selector,
or restricted controller.  Packet probabilities are used only through their
already checked full-support source and helper consumers.

The terminal alternative (5)--(6) applies the checked unrestricted terminal
exploitability toggle at one pure coalition.  Its collision certificate is an
executable immediate singleton-collision deviation.  The resulting
inequalities remain finite reward-table data; they are not upgraded to a
behavioral equilibrium construction.

## Source correspondence and novelty

The actual source and proper-principal size reduction are checked in:

- `UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/FullSupportProjectiveQBarResidual.lean`:
  `FinFourQuantitativeFullSupportHardResidual` and
  `nonempty_finFourQuantitativeFullSupportHardResidual_of_no_uniformPayoff`;
- `UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/FullSupportHardPrincipalSize.lean`:
  `exists_nonprojectivePrincipal_card_two_or_three`;
- `UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/FullSupportHardPrincipalDispatch.lean`:
  `cardTwoCrossing` and
  `cardThree_externalHelper_or_cyclicBoundary`;
- `UniformEquilibrium/Diagnostics/Quitting/Collision/PreemptionGeometry.lean`:
  the collision-anchored marked geometry; and
- `MathUE/FiniteSerialRelation.lean`:
  the three rooted-four constructors and their marker identities.

The strict three-point orientation definition is checked in
`UniformEquilibrium/Quitting/Classification/LCP/ThreeByThreeZeroDiagonalQ.lean`.

The new content is the adjacency/opposition cycle shortening, exact
owner/collider hard-pair consequence, disjoint-pair helper containment,
triple-helper collision-role mapping, cyclic-triple closing chord, and the
same-label shorter marked geometry.  A narrow source search found no existing
declaration composing these facts.  No literature theorem is invoked.

## Boundary tests

1. **Margin loss is real.**  Keep a cycle edge at gap `gamma=1` and let its
   hard reverse entry be `-epsilon` with arbitrarily small `epsilon>0`.
   The reciprocal two-cycle exists only at a common margin at most `epsilon`.
   Therefore replacing `eta` by `gamma` would be false.
2. **Opposite pair.**  A reciprocal negative opposite chord does not itself
   form a two-cycle rooted on an original edge, but each chord closes one of
   the two length-two arcs to form a strict three-cycle.
3. **External-helper triple.**  Positive `M(i,x)` for a nonsuccessor row is
   compatible with the negative successor entry `M(successor(x),x)`.  This
   arm need not contain a shorter cycle and correctly stops at helper
   incidence.
4. **Cyclic triple.**  The two inherited consecutive negative signs rule out
   one of the two strict orientations and force the closing chord in the
   other.  Its magnitude is unconstrained by `gamma`.
5. **One-role pair.**  If a hard pair contains exactly one of owner/collider,
   its two-label complement contains the other role plus one unmarked label;
   neither helper is forced to be the role.

## Adapter and consumer

For a bounded four-player table with no uniform-equilibrium payoff,

```text
nonempty_finFourQuantitativeFullSupportHardResidual_of_no_uniformPayoff
```

produces `residual`, and

```text
residual.witness.exists_collisionAnchoredPreemptionGeometry_of_card_eq_four
```

produces the collision certificate and one of the seventeen marked geometries
from the same witness.  On a rooted four-cycle, the proper-principal size
theorem and this packet give the stated classification.

The outputs enter the existing finite structures
`FinFourHardCardTwoCrossing`, `FinFourHardCardThreeExternalHelper`, and
`FinFourHardCardThreeCyclicBoundary`, or a shorter marked strict sign cycle.
There is no downstream semantic consumer presently known.  This is an exact
finite alignment consumer only, as authorized by the user.

## Lean handoff

1. Add a decoder for the three rooted-four constructors returning the ordered
   cycle and marker position, or prove the three cases directly.
2. Given a selected hard pair, decide adjacency versus opposition by finite
   `Fin 4` enumeration, invoke `cardTwoCrossing`, and construct `eta` from the
   relevant strict inequalities.
3. Prove the owner/collider pair alternative by
   `exists_leave_or_join_gain`; use the collision certificate to exclude
   collider leave and the normalized-matrix identity for `eps`.
4. For a hard triple, invoke
   `cardThree_externalHelper_or_cyclicBoundary`; prove the unique-complement
   identities and a small coordinate-free lemma that two consecutive negative
   entries in a strict three-cycle force the closing negative entry.
5. Populate a shorter-cycle structure parameterized by the new `eta`, rather
   than reusing the terminal gap field.
6. Regression-test adjacent/opposite pairs, all four possible omitted triple
   vertices, all three marker positions, and an arbitrarily small reverse
   margin.

The theorem should not add hard-principal or helper fields to the source
decoder and should not claim that the shorter cycle is at gap `gamma`.

## Scope and nonclaims

- The theorem does not eliminate any marked semantic geometry or prove that a
  counterexample residual exists.
- The shorter cycle is at a new positive margin `eta`, not necessarily the
  terminal gap `gamma`.
- It does not produce a Bellman edge, exact Nash root, chronological path,
  absorption return, semantic-debt decrease, or uniform-equilibrium payoff.
- The terminal inequalities (5)--(6) are not a sure-exit set or a stationary
  repair.
- The positive helpers may coincide and need not be unique.
- It does not align the hard principal with the separately selected strict-
  toggle semantic cycle, terminal debtor, punishment continuation, or
  conditioned packet.
- Completion of the finite seventeen-constructor alignment is not completion
  of the quitting-game conjecture.
