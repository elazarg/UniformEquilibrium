# Review of paid-row Proposition 71

Reviewer: `CODEX_EULER`

Verdict: **PASS**.

I checked Proposition 71 and Corollary 71A in
[`CODEX_CEDAR__PAID_ROW_REENTRY.md`](../notes/CODEX_CEDAR__PAID_ROW_REENTRY.md),
including both base cases, the exact use of the punishment lower bound, and
rotation/reversal scope.

## Nonempty base

For the directed square

```text
B -> B+i -> B+i+j -> B+j -> B,
```

edgewise tightness gives exactly

```text
r_(B+i)(i)=P_i>r_B(i),
r_(B+j)(i)=P_i>r_(B+i+j)(i).
```

If every member of nonempty `B` Quits surely and `j` independently Quits
with probability `x in (0,1)`, date-zero absorption is certain regardless of
`i`.  Player `i`'s Quit endpoint is the strict convex combination of
`r_(B+i)(i)` and `r_(B+i+j)(i)`; its Continue endpoint is the strict convex
combination of `r_B(i)` and `r_(B+j)(i)`.  Each endpoint is strictly below
`P_i`, so the unrestricted cap is below `P_i`.  This contradicts the defining
inequality `P_i<=cap` for every opponent strategy.  No continuation or
stationarity subtlety remains because the base absorbs immediately.

## Empty base

For `B=empty`, the two `j` edges give

```text
r_(i,j)(j)=P_j>r_i(j),
0=P_j>r_j(j).
```

Let opponent `i` use a stationary hazard `x in (0,1)` and let all other
opponents Continue.  Quitting at a live date has value

```text
Q=(1-x)r_j(j)+x r_(i,j)(j)<0=P_j.
```

Never has value `r_i(j)<0`, since `i` eventually Quits almost surely.  A
deterministic Quit time has payoff a convex combination of `Q` and `r_i(j)`;
the same remains true after arbitrary behavioral randomization.  Hence the
unrestricted stopping cap is `max(Q,r_i(j))<P_j`, contradicting the same
punishment lower bound.  This verifies the sensitive final-leaver/zero-Never
case without assuming immediate absorption.

Every directed toggle square is obtained from the displayed orientation by
rotation, reversal, and exchange of its two coordinates, so the relabelling
claim is exact.  Hypercube cycles are even; a two-cycle would require strict
improvement in both directions along one edge, and the proposition excludes
length four.  Thus the tight simple-cycle arm has length at least six and is
empty for a two-player cube.

The scope is correctly static.  The result removes directed squares from the
edgewise punishment-tight orbit of Corollary 70A.  It supplies neither a
connector nor a chronology and makes no claim about tight cycles of length
six or more.

## Addendum: Corollary 71B

Verdict: **PASS**.

In a simple six-edge cube cycle every coordinate occurs an even number of
times.  A `4+2` multiplicity split is impossible: in a cyclic binary word
four copies of one label cannot be separated by only two copies of the other,
so two equal labels would be adjacent and the cycle would immediately
backtrack.  Hence exactly three distinct labels occur twice.

If the two occurrences of every label are antipodal in the six-letter cyclic
word, rotation and relabelling give `i,j,k,i,j,k`.  Otherwise simplicity
excludes adjacency and some label has cyclic distance two, producing a
subword `i,j,i`.

The two `i` edges in such a subword use opposite membership actions against
the two pure `j` rows.  With a nonempty common base, the strict-convexity
argument of Proposition 71 makes both `i` endpoints strictly below `P_i`.
With empty common base, the same one-opponent argument works except for the
orientation

```text
empty -> {i} -> {i,j} -> {j}.
```

The remaining multiset is `{j,k,k}`.  Avoiding adjacent equal labels forces
the suffix `k,j,k`, so the cycle must close through

```text
{j} -> {j,k} -> {k} -> empty.
```

For player `k` this gives
`r_(j,k)(k)=P_k>r_j(k)` and `0=P_k>r_k(k)`, exactly the forbidden empty-base
orientation already handled in Proposition 71.  Thus the `i,j,i` case is
also impossible and the stated antipodal word is forced.

This classifies only the selected-label word of a tight six-cycle.  It does
not classify which coalition translate/complement is visited, and it adds no
chronological or connector conclusion.
