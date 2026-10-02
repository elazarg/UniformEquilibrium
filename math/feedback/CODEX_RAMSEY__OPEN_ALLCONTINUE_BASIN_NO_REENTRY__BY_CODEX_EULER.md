# Review of `OPEN_ALLCONTINUE_BASIN_NO_REENTRY`

Reviewer: `CODEX_EULER`

## Verdict

**PASS.**  Propositions 1 and Corollaries 2--4 are valid ordinary
mathematics at their stated exact-root scope.  I found no repair affecting a
claim, constant, or quantifier.

## Claim audited

The hypothesis is a payoff set `N` for which every zero-error endpoint-Nash
product root against every tail `V in N` is the all-Continue root.  The note
claims:

1. an exact finite Nash--Bellman path whose terminal tail lies in `N` is the
   constant all-Continue path;
2. no positive-absorption exact cyclic continuation can be anchored in `N`;
3. if `B(U,r) subset N`, every charged exact finite block with terminal tail
   `V` has `dist(V,U)>=r`, even when the origins vary; and
4. an exact infinite Nash--Bellman path converging to `U in N` is identically
   `U` and all-Continue.

## Orientation and finite induction

`IsQuittingNashBellmanEdge reward current tail` in
`UniformEquilibrium/Quitting/Bellman/Finite/NashBellmanSpine.lean` says that
the root stored at `current` is zero-error endpoint Nash against `tail.1` and
that

```text
current.1 = quittingRootSuccessorPayoff reward tail.1 root.
```

Thus the note's convention

```text
v_t = Succ(v_(t+1),q_t)
```

has the repository's exact orientation.  Starting with `v_L=V in N`, the
root `q_(L-1)` is all-Continue; its successor is the identity, hence
`v_(L-1)=V`.  Descending induction repeats the same argument through every
earlier edge.  No floor, carrier, debt, or compactness hypothesis is used.

For a `QuittingFiniteNashBellmanPath`, the cited declarations in
`UniformEquilibrium/Quitting/Cycles/CycleMismatchContraction.lean` expose
exactly the needed facts:

```text
quittingAnchoredPathValue_at_cutoff
quittingAnchoredPathRoots_isZeroEndpointNash
quittingAnchoredPathValue_eq_successor.
```

Their indices put the root at `time` against the displayed value at
`time+1`, so there is no off-by-one issue.

## Cyclic and seam consequences

`IsQuittingCyclicContinuationBlock` in
`UniformEquilibrium/Quitting/Debt/Dynamic/CyclePinnedDebt.lean` consists of
an anchored exact path, equality of its origin payoff with its terminal
anchor, and a stage with strictly positive root absorption mass.
Proposition 1 makes every root of a block anchored at `V in N` all-Continue,
whose absorption mass is zero.  This directly contradicts the last field.

If `B(U,r) subset N` and a charged block had `dist(V,U)<r`, its terminal tail
would lie in `N`; the same argument would make it zero-charge.  The origin is
irrelevant to this implication, so the stronger statement for a sequence of
blocks with varying origins and terminal tails converging to `U` is also
correct.

The phrase “cannot exit and later re-enter” is correct in the displayed path
order: once some later tail node belongs to `N`, every earlier predecessor in
that finite prefix equals that node.  This remains one-sided.  A head in `N`
can still be produced by a single edge whose tail is outside `N`; the note
explicitly preserves this caveat.

## Infinite convergence

If `v_t -> U` and `N` is open with `U in N`, then `v_t in N` for all
sufficiently large `t`.  Consequently each sufficiently late `q_t` (whose
tail is `v_(t+1)`) is all-Continue and each late equality is
`v_t=v_(t+1)`.  The sequence is eventually constant, and convergence
identifies that constant with `U`.  Descending through the remaining finite
prefix then forces every earlier value to equal `U` and every earlier root to
be all-Continue.  Backward propagation therefore does reach arbitrary finite
origins; it does not make any assertion about approximate edges.

## Application and scope

The reviewed Proposition 2 of
`notes/CODEX_CEDAR__FOUR_PLAYER_CONJECTURE_CAPSTONE.md` supplies precisely an
open neighborhood on which all-Continue is the unique exact root, so it is a
legal source for hypothesis `(H)`.  The conclusion excludes exact charged
finite returns and exact convergent infinite paths into that basin.  It does
not exclude approximate root stacks, approximate seams, a nonlocal incoming
edge with outside tail, or paths accumulating only on the boundary of the
basin, and it produces no uniform-equilibrium payoff.  Those nonclaims are
stated accurately.

