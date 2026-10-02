# Full Replacement Kernels: Algebraic Closure and Tautology Risk

## 1. Multi-response kernels

The failure of unary response graphs suggests retaining mixed-coordinate
information.  For an actual profile with stopping-law vector `lambda`, a
subset `J` of players, and deterministic replacement times

```text
d_J in (Nat union {infinity})^J,
```

define

```text
K_(J,d_J)(lambda)
```

to be the complete terminal-outcome law when every player in `J` is replaced
by the displayed pure time and all players outside `J` retain their prescribed
stopping laws.  Payoff coordinates are its reward moments.

There are finitely many subsets and countably many pure-time tuples, so the
collection of all such finite-dimensional laws embeds in a countable product
of compact simplices.

The cases have familiar meanings:

```text
J = empty:          prescribed terminal law;
J = {i}:            player i's pure-time response kernel;
J = {i,p}:          the cross-kernel needed after replacing p;
J = all players:    deterministic quitting-time outcome.
```

## 2. Exact horizontal update on actual states

Replace player `p` by a stopping law `theta`.  For `p notin J`, independence
and the stopping-law mixture identity give

```text
K'_(J,d_J)
  = sum_(s in T) theta(s) K_(J union {p}, (d_J,s)).                (2.1)
```

For `p in J`, the query already overwrites player `p`, so

```text
K'_(J,d_J) = K_(J,d_J).                                          (2.2)
```

Thus the full multi-response kernel atlas is algebraically closed under
horizontal replacement.  Unary graphs fail precisely because they omit the
`|J| >= 2` coordinates needed in (2.1).

For a fixed `theta`, the infinite sum in (2.1) is a uniform limit of finite
coordinate sums because `theta` is a probability law and all rewards are
bounded.  It is therefore continuous in the product topology of the kernel
coordinates.

The word **fixed** is essential.  The boundary example in
`HORIZONTAL_REPLACEMENT_NO_GO.md` uses the same moving deadline `QuitAt (3m)`
on two source sequences.  Every fixed pure-time query has the same limiting
kernel on both sources, while the moving query selects different sides of an
escaping threshold.  Hence the raw full kernel atlas with pointwise product
topology does not make evaluation jointly continuous in a weakly convergent
replacement law.

## 3. Exact vertical prefix update

Prefix a product root `x`.  For a query `(J,d_J)`, players in `J` with deadline
zero Quit at the current root; those with positive or infinite deadline
Continue.  Players outside `J` use `x`.

If anyone quits, the current coalition determines the outcome.  If everyone
Continues, every finite positive deadline in `d_J` is decremented and the
tail kernel with that shifted query is used.  This gives a coordinatewise
finite affine recursion.  Therefore the multi-response kernel atlas also has
an exact vertical prefix law.

## 4. Caps and the remaining compactness defect

At an actual state, player `i`'s cap after any fixed context is the supremum
over the corresponding `i`-deadline coordinate.  The kernel atlas determines
it exactly.

But supremum over countably many product coordinates is not continuous.
Deadlines may escape to infinity while retaining a cap value not visible at
any fixed finite coordinate.  There are two repairs:

1. add the completed response graph or cap coordinate for every relevant
   context; or
2. close the graph of the whole replacement operation jointly.

The first repair proliferates contextual coordinates.  If contexts include
arbitrary stopping laws, their index set is uncountable.  A countable dense
family of rational finite-support laws may suffice because payoff and cap are
Lipschitz in a fixed opponent law under total variation, but no complete
minimality theorem was proved here.

## 5. Universal strategic compactification

At the extreme, store for every finite collection of replacement laws:

* the resulting terminal law and prescribed payoff;
* every player's behavioral cap there; and
* all further replacement values.

Taking the closure of the joint evaluation image gives a compact space on
which a fixed horizontal replacement is just reindexing.  This is a valid
existence construction, analogous to a compactification by all bounded
observables.

It is also close to tautological.  It stores the answer to every strategic
query rather than identifying a small sufficient state.  More importantly,
it does not solve temporal implementation: a horizontal better-reply edge
between two strategy profiles is not an all-Continue edge of one executable
quitting profile.

To include adaptively moving controls honestly, one must compactify the joint
graph

```text
(state, replacement law, target state),
```

not only the state.  The resulting transition is necessarily relational at
the all-Never boundary.

## 6. Why compact recurrence still does not prove equilibrium

Under a hypothetical positive terminal gap, every actual profile has a player
with a uniformly positive behavioral deviation.  Iterating such deviations
gives an infinite path of actual horizontal paid edges.  Compactness of any
of the states above gives recurrent subsequences.

This does not contradict anything.  Better-reply cycles occur in ordinary
finite games, and their edges are strategy replacements, not successive dates
of play.  To invoke the project's return compilers, the edges must be
Nash--Bellman or punishment-admissible temporal edges with one literal source
chronology.  State enlargement alone does not provide that verticalization.

Hence the full kernel atlas may be useful for **cap-leakage accounting**, but
it is not by itself the missing producer.

## 7. Sharp possible follow-up

The non-tautological question is whether pair kernels already suffice in
Fin4 for the currently surviving paid-pair transition.  The local update of
one player changes another player's cap through a two-player response surface.
If all later operations can be expressed using only pair contexts, then the
finite family

```text
ordinary law + unary completed graphs + pair response surfaces
```

might close the relevant SCC without the full replacement atlas.  If a third
replacement is needed before returning, a three-coordinate counterexample
should be sought immediately.
