# Feedback on `CODEX_NOETHER__QUIT_TIME_COMPACTIFICATION` — Round 41

## Claim checked

I independently falsified Section 61, Proposition 81: even a compact
finite-dimensional semialgebraic closed predecessor-serial relation with a
continuous polynomial charge can have `A_N` of order `sqrt(N)` while every
individual infinite path has finite total charge.

**Verdict: VALID ordinary mathematics.**  I found no mathematical objection.

## Carrier, graph, and boundary cases

The three labeled components `Z`, `P`, and `{o}` are disjoint compact
semialgebraic subsets of `R^3`.  Each of the four displayed graph pieces in
`(N183)` is cut out by polynomial equalities and weak inequalities on compact
parameter boxes.  Their finite union is therefore compact, semialgebraic, and
closed.  Allowing both edges when `s+e^2=1` is necessary and correctly makes
the graph closed.

Predecessors cover every case:

- `z_e` and `o` have their self-loops;
- `u_(e,s)` with `s<=e^2` has predecessor `z_e` through the entry edge;
- `u_(e,s)` with `s>=e^2` has predecessor `u_(e,s-e^2)` through the phase
  edge.

At `e=0`, the latter is the self-loop of every phase state; `u_(0,0)` also has
the entry predecessor.  At `s+e^2=1`, either the last phase edge or the exit
edge may be taken.  Thus predecessor seriality and viable infinite futures
survive all equality cases.

The polynomial `e*label*(2-label)` restricts to zero on `Z` and `{o}` and to
`e` on `P`, so it is continuous and nonnegative on `K`.

## Individual paths and phase count

A path either remains in a zero-charge component or selects one fixed
parameter `e>0`, enters `P` once, advances `s` by `e^2`, and then reaches
`o`.  Starting anywhere in the entry interval `0<=s<=e^2`, the number of
positive-charge phase states is at most `1/e^2+2`; the two-unit slack covers
both endpoint conventions.  Hence its total charge is at most
`1/e+2e<infinity`.  No path can return from `o` to a new parameter branch.

## Prefix optimization

For horizon `N`, any parameter-`e` path contributes at most

```text
min(N e,1/e+2e).
```

If `e<=1/sqrt(N)`, the first term is at most `sqrt(N)`.  If
`e>=1/sqrt(N)`, the second is at most `sqrt(N)+2`, since `e<=1`.  This proves
the upper bound uniformly, including `e=0` by the zero-charge convention.

For the lower bound, choose `e=1/sqrt(N)` and start at `u_(e,0)`.  The first
`N` states have `s=j/N` for `0<=j<N`, all lie in `P`, and each pays
`1/sqrt(N)`.  Their total is exactly `sqrt(N)`.  The indexing also works at
`N=1`.

## Exact scope

The example is an abstract semialgebraic relation, not a Nash--Bellman reward
table.  It decisively rules out semialgebraicity, finite dimension, and
polynomial charge as sufficient generic replacements for nesting or source
matching.  The remaining positive route must use the specific multilinear
endpoint/floor equations of the quitting relation.
