# Never Mass Bounds the Horizontal Boundary Fibre

The proper-limit continuity theorem has a quantitative extension.  For a
convergent replacement family, all nonuniqueness of the compact horizontal
target is confined to the limiting replacement's Never event.

## Statement

Fix a player `p` and a compact stopping law `theta`.  Write

```text
q = theta({infinity}).
```

Consider two source sequences whose vectors of compact stopping laws converge
to the same limit and whose source `p`-caps converge to the same number.  Let
the two replacement-law sequences converge weakly to the same `theta`; they
need not be constant or equal term by term.  Let `z,z'` be any two semantic
cluster points of the resulting target profiles.  For reward bound `M`, the
following bounds hold:

```text
|U_i(z)-U_i(z')| <= 2 M q                    for every i,          (1.1)
|B_p(z)-B_p(z')| = 0,                                             (1.2)
|B_j(z)-B_j(z')| <= 2 M q                    for j != p.           (1.3)
```

There is a graph-level version of (1.3).  If the target completed response
graphs for `j != p` converge to `Gamma_j` and `Gamma'_j`, then, for a product
metric whose vertical coordinate is ordinary distance,

```text
Hausdorff(Gamma_j,Gamma'_j) <= 2 M q.                              (1.4)
```

For the mover `p`, horizontal replacement leaves the entire response graph,
not only its cap, unchanged along each source sequence.  Thus its target graph
is single-valued whenever its source graph has been retained in the joint
source state.

The total-variation diameter of the target terminal-law fibre is at most `q`
under the convention `TV = sup_event |mu(event)-nu(event)|`.

## Proof

For a finite cutoff `T`, split according to

```text
E_T = {p stops by T}.
```

For either replacement sequence, its complement has probability converging to

```text
e_T = theta({dates greater than T or infinity}),
```

and `e_T -> q`.

Finite-date atoms of both replacement sequences converge to the corresponding
atoms of `theta`.  On the event that `p` stops at one fixed `t <= T`, every prescribed outcome is
determined by the finite cylinder through `t`.  For another player, the entire
pure-time response menu converges uniformly: `p` is a tight opponent and every
deadline after `t` is equivalent to Continuing through `t`.  Summing these
uniformly convergent menus over the finitely many values `t <= T` shows that
the law, payoff, and cap contribution restricted to `E_T` has one common
limit along both source sequences.

The complement has probability `e_T` independently of every other player's
deviation.  A bounded payoff contribution on this event has absolute size at
most `M e_T`; two possible limits differ uniformly over the complete response
menu by at most `2 M e_T`.  The inequality

```text
|sup f - sup g| <= sup |f-g|
```

transfers the same bound through the behavioral supremum.  Letting
`T -> infinity` proves (1.1) and (1.3).

Player `p`'s opponents are unchanged by replacing `p`, so its cap is copied
exactly from the source, proving (1.2).  The law estimate follows from the
same event decomposition: the two measures have a common restriction of mass
`1-e_T`, and only their remaining mass can differ.

The uniform comparison is actually between the complete pure-time value
menus.  On `E_T`, every deadline after `T` is equivalent to Continuing through
`T`, so only finitely many clopen-cylinder values remain.  On the complement,
all deadline values differ by at most `2 M e_T`.  Hence the sup norm between
the two menus is eventually at most `2 M e_T` up to a vanishing error.  Closing
their graphs and passing to the limit proves (1.4).

## Sharpness of the scale

The four-player construction at the end of
`FIXED_DEADLINE_HORIZONTAL_CONTINUITY.md` gives a prescribed-payoff difference
exactly `q` with rewards in `[0,1]`.  Taking the two distinguishing rewards to
be `M` and `-M` gives difference exactly `2 M q`.  Thus (1.1) is sharp and no
universal `o(q)` ambiguity bound is possible.

## Interpretation

For convergent horizontal replacement families, limiting Never mass is an
explicit defect variable:

```text
q = 0:     the completed replacement relation is single-valued;
q > 0:     its semantic fibre has diameter O(q).
```

This suggests a smaller augmented state for replacement lanes in which the
replacement law and its Never mass are stored explicitly.  When `q=1`, the
bound permits the fully multivalued moving-scale behaviour in
`HORIZONTAL_REPLACEMENT_NO_GO.md`.  The response graph or a jointly closed
replacement diagram is still needed to retain which point of that fibre is
selected.

This result is proved here in ordinary mathematics and is not Lean-checked.

## Lean-facing target

The existing opponent-tight estimates should support declarations of the
following mathematical shape:

```text
quittingTerminalSemanticPair_update_replacement_tendsto_of_limitProper

quittingTerminalSemanticUpdateCluster_fiberDiameter_le_neverMass

quittingCompletedResponseGraph_updateCluster_dist_le_neverMass
```

The first is the `q=0` case.  The second compares two jointly selected source
and replacement sequences and therefore should retain both sequences in its
statement rather than compare independently chosen carrier points.
