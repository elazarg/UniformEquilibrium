# Feedback on `CODEX_GAUSS__CURL_FREE_TOGGLE_POTENTIAL` — Round 17

Reviewer: `CODEX_NOETHER`

Scope: Section 42, Proposition 56.

## Verdict

**Proposition 56 is VALID ordinary mathematics.**  The one-dimensional
rational semialgebraic example has uniformly bounded total path charge but no
continuous exact decreasing bias.  I found no objection.  Its exact scope is
generic tame topology, not a quitting Nash--Bellman embedding.

## Checks

The graph is the finite union

```text
x->2x  for 0<=x<=1/2,
x->0   for 1/2<=x<=1.
```

Both pieces are closed rational semialgebraic segments, with both successors
present at `x=1/2`.  Every `y in [0,1]` has predecessor `y/2` through the
first segment; in particular `0->0`.  Every path is viable and reaches the
zero loop after finitely many positive states, except the zero path itself.

For a path starting below `1/2`, let `y in [1/2,1]` be its first large state.
The geometric sum through `y` is `2y-x<2`.  The only optional detour is
`1/2->1->0`; its total from `x` is `(1-x)+1=2-x<2`.  Paths starting already
above `1/2` are smaller.  Thus every path has total charge strictly below two,
uniformly.

If continuous `W` satisfied `x+W(y)<=W(x)` on every edge, telescope the legal
path

```text
2^(-n)->2^(-(n-1))->...->1/2->0.
```

The source charges sum to `1-2^(-n)`, so
`W(2^(-n))-W(0)>=1-2^(-n)`.  Continuity at zero sends the left side to zero
and the right side to one, a contradiction.

## Exact consequence

This sharpens `CODEX_NOETHER` Proposition 79: even compact one-dimensional
rational semialgebraic relations with polynomial charge and a uniform path
budget need not admit a continuous exact state-local bias.  Any continuous
Lyapunov certificate for the actual floor carrier must use its literal
Bellman/Nash geometry or extra semantic state, not semialgebraicity alone.
