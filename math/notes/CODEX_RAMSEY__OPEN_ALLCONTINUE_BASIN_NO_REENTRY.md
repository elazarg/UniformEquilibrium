# CODEX_RAMSEY — an open all-Continue basin has no exact re-entry

Author: `CODEX_RAMSEY`

## Current status

**Ordinary-mathematics theorem; independently reviewed PASS.**  The review is
[`CODEX_EULER`](../feedback/CODEX_RAMSEY__OPEN_ALLCONTINUE_BASIN_NO_REENTRY__BY_CODEX_EULER.md).
This note extracts the path-level consequence of the reviewed open-root basin in
Proposition 2 of
`notes/CODEX_CEDAR__FOUR_PLAYER_CONJECTURE_CAPSTONE.md`.  It is a no-go for an
exact finite return architecture, not a construction of a uniform payoff.

## Question and exact orientation

Let `reward` be a finite quitting table on a finite player type.  An exact
Nash--Bellman edge is written

```text
current = Succ(tail, root),
root is exact endpoint Nash against tail.
```

This is the orientation of `IsQuittingNashBellmanEdge` in
`UniformEquilibrium/Quitting/Bellman/Finite/NashBellmanSpine.lean`: the
predecessor `current` is listed first, while the semantic direction is from
`tail` to `current`.

Suppose `N` is a set of payoff vectors such that

```text
for every V in N, every exact root against V is all-Continue.       (H)
```

What finite exact chain can have its terminal tail in `N`?

## Proposition 1 (backward rigidity)

Let

```text
v_0, v_1, ..., v_L
q_0, q_1, ..., q_(L-1)
```

satisfy, for every `t<L`,

```text
v_t = Succ(v_(t+1),q_t),
q_t is exact endpoint Nash against v_(t+1).
```

If `v_L=V` for some `V in N`, then

```text
v_t=V                         for every t<=L,
q_t=all-Continue              for every t<L.             (1)
```

In particular every edge has zero absorption charge.

### Proof

Descend from `t=L-1` to `0`.  If `v_(t+1)=V`, hypothesis (H) makes `q_t`
all-Continue.  The all-Continue successor map is the identity, so

```text
v_t = Succ(V,all-Continue)=V.
```

This proves both assertions inductively.  The all-Continue product root has
absorption mass zero.  `QED`

The statement maps literally to `QuittingFiniteNashBellmanPath`: use
`quittingAnchoredPathValue_at_cutoff`,
`quittingAnchoredPathRoots_isZeroEndpointNash`, and
`quittingAnchoredPathValue_eq_successor`, followed by descending induction on
the finite cutoff.

## Corollary 2 (no absorbing cyclic block through the basin)

Under (H), no `V in N` satisfies

```text
IsQuittingCyclicContinuation reward V.
```

Indeed a cyclic continuation block is an anchored finite exact chain with
terminal value `V` and with at least one positive-absorption stage.
Proposition 1 makes every stage all-Continue, contradicting that positive
absorption clause.

More generally, an exact finite path cannot leave `N` and later re-enter it:
apply Proposition 1 to the prefix ending at the first purported re-entry
node.  Thus `N` is backward absorbing for the exact predecessor relation,
even though a head in `N` may have a genuinely nonlocal tail outside `N`.

## Application to the strict normal minimum plateau

For the `Fin 4` counterexample residual in the reviewed Propositions 1--2 of
Cedar's capstone note, there is an open neighborhood `N` of the positive-debt
minimum plateau payoff `U` satisfying (H).  Therefore:

1. no positive-absorption exact cyclic continuation block can be anchored at
   `U` or at any other terminal vector in `N`;
2. an exact finite Bellman path cannot exit this neighborhood and then return
   to it; and
3. the remaining conjecture-facing construction cannot be an exact closed
   block with terminal tail near `U`.

Choose any radius `r>0` whose open payoff ball `B(U,r)` lies in `N`.  Then a
sharper seam statement holds:

> **Corollary 3 (fixed seam floor for every charged exact block).**  Any
> finite exact Nash--Bellman block with terminal tail `V`, at least one
> positive-absorption stage, and origin payoff `U` must satisfy
> `dist(V,U)>=r`.

If `dist(V,U)<r`, then `V in N`, so Proposition 1 makes the entire block
constant and zero-charge, a contradiction.  In particular there is no
sequence of positive-charge exact blocks whose terminal tails converge to
`U`; eventually their terminal tails enter `N` and every such block becomes
the all-Continue identity block.  The same conclusion holds even if the
origin payoffs are allowed to vary: terminal convergence to `U` alone kills
all finite exact charge eventually.

There is also no exact infinite-path escape through an asymptotic approach:

> **Corollary 4 (exact convergence rigidity).**  Let `(v_t,q_t)_{t>=0}` be
> an infinite exact Nash--Bellman path and suppose `v_t -> U` for some
> `U in N`.  Then `v_t=U` and `q_t=all-Continue` for every `t`.

Because `N` is open, every sufficiently late `v_t` lies in `N`.  Each late
edge is therefore the identity, so the value sequence is eventually constant;
its limit makes that constant `U`.  Proposition 1 applied successively to
the finitely many earlier edges then propagates `U` and all-Continue back to
time zero.

The viable architectures must instead use at least one ingredient not covered
by this exact finite-chain statement: an approximate terminal seam whose
error is controlled in the uniform-payoff compiler, a different semantic
anchor outside `N`, or exact states whose payoff values do not converge to
the plateau.

## Boundary and nonclaims

- Root uniqueness is required throughout `N`, not merely at `U`.
- A predecessor head in `N` does not force its tail into `N`; the theorem is
  one-sided in the Bellman orientation.
- The result does not exclude a nonlocal one-edge predecessor mapping an
  outside tail to a head in `N`.
- It does not address approximate roots or approximate Bellman seams.
- An exact path converging to the interior point `U` is covered by Corollary
  4; a path remaining outside `N` and accumulating only on its boundary is
  not.
- It proves no terminal or uniform equilibrium payoff.

## Requested falsification

Please check the Bellman orientation, the descending induction for the
repository's `QuittingFiniteNashBellmanPath` indices, and whether the cyclic
block's positive-absorption clause is indeed contradicted without any hidden
floor or carrier hypothesis.
