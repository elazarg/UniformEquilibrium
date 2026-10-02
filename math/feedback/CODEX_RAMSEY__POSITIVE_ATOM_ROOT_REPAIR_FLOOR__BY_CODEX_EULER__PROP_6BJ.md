# Review of Proposition 6BJ

Reviewer: `CODEX_EULER`

Verdict: **PASS** in the exact finite-alignment/noncompiler scope.  The hard
pair adjacency split, hard triple dispatch, shortened strict-cycle margins,
owner/collider incidences, helper-complement identities, and stopping point
all check.  No repair is required.

## Pair arm

Write the rooted four-cycle as

```text
v0 -> v1 -> v2 -> v3 -> v0,
```

so the cycle gives `M(v_{k+1},v_k)<=-gamma`.  A hard pair `K={u,v}` enters the
checked `cardTwoCrossing` theorem and therefore has both reciprocal entries
strictly negative.

- If `K` is adjacent, one negative entry is the original directed cycle edge
  and the other is the strict reverse edge, yielding a two-cycle.
- If `K` is opposite, either negative chord closes the corresponding two-edge
  arc of the four-cycle, yielding a three-cycle.

Taking `eta` below `gamma` and below the finitely many new strict negative
margins makes every displayed edge a literal `QuittingSoloPreempts reward eta`
edge.  The note correctly does not retain the original `gamma` on a new chord.

When `K={owner,collider}`, hard-pair negativity gives

```text
eps=reward({owner})(owner)-reward({collider})(owner)>0.
```

The terminal toggle at `{owner,collider}` cannot select collider leave, since
that inequality and the collision certificate would imply `2*gamma<=0`.
Owner leave composes exactly to

```text
reward({owner,collider})(owner)+gamma+eps
  <= reward({owner})(owner),
```

and the other arm is a literal outsider join by `gamma`.  Both packet helpers
are outside this pair.

If `K` is disjoint from the owner--collider pair, the two card-two sets are
complements in `Fin 4`, so both helpers belong to the owner--collider pair.
Complementation preserves adjacent versus opposite type.  If the intersection
has size one, the complement contains the other marked role and one unmarked
label, so no stronger helper identity is forced.  These cases exhaust pair
incidence.

## Triple arm

Let `x` be the unique omitted vertex.  The checked
`cardThree_externalHelper_or_cyclicBoundary` split is exhaustive.

In the external-helper arm, `K.compl={x}` identifies the helper literally as
`x`.  Its helped receiver cannot be the successor of `x`, because the original
cycle makes `M(successor(x),x)<0` while the helper field makes the same entry
positive.  If `x` is the owner or collider, that exact marked role is the
helper; otherwise the triple contains both marked roles.

In the cyclic-boundary arm, write

```text
x -> a -> b -> d -> x.
```

Restriction already gives `M(b,a)<0` and `M(d,b)<0`.  A strict three-point
cyclic orientation containing those two entries is forced to have
`M(a,d)<0`, with the three reverse entries positive.  Hence
`a -> b -> d -> a` is a literal strict three-cycle; choosing `eta` below its
three margins gives the claimed preemption cycle.

The marked mapping is exact.  If `x=owner`, the old edge `owner->a` is the
one-step tail and the collider lies on the new three-cycle.  Otherwise the
owner lies on that cycle; the collider is outside exactly when `x=collider`.
These are precisely the one-step-to-three and rooted-three incidences used in
the reviewed length-three alignment.

## Scope

The proposition makes a genuine finite cycle-length reduction in the hard
pair and cyclic-triple arms and identifies the unique helper in the remaining
triple arm.  It does not preserve the terminal-gap margin on new edges and
does not produce a Bellman root, reached chronology, sure-exit set, semantic
debt descent, or unrestricted equilibrium consumer.  Further annotation
splitting would have no theorem-driven content.  The stated stopping point is
therefore exact.
