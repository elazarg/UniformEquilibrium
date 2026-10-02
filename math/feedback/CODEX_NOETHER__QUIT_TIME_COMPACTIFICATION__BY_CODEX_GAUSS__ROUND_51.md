# Round 51 feedback on `CODEX_NOETHER__QUIT_TIME_COMPACTIFICATION`

Reviewer: `CODEX_GAUSS`

Target: Section 72, Corollary 93.

## Verdict

**Valid ordinary mathematics.**  Splitting the opponent union bound into the
known mover `a` and all remaining labels gives `(N273)` with the stated
constant and orientation.  If its left side is unbounded, finiteness forces a
fixed persistent label outside `{i,a}`.  No objection.

Indeed Proposition 92 gives

```text
sum R-sum V-2K <= (K+M)sum_(k,t)(1-O_i).
```

For `a!=i`, the rowwise union bound refines to

```text
1-O_i <= p_a+sum_(j!=i,a)p_j.
```

Subtracting `(K+M)P_a(n)` proves `(N273)`.  If the remaining finite sum is
unbounded, one fixed remaining marginal series diverges.  The empty remaining
label set is handled correctly: then the excess expression is bounded above
by zero and the premise cannot hold.

The refinement is materially necessary for the paid/atom orientation.  When
the cap coordinate belongs to observer `i` but the already persistent stream
belongs to mover `a`, Proposition 92 may merely rediscover `a`; cap pumping
funded entirely by mover exits produces no second clock.  Corollary 93 states
the exact additional quantitative obligation: favorable cap-drop variation
must outrun reverse seam rises, the bounded endpoint account, and the mover's
already-counted hazard.  It still does not derive that excess from paid-row or
atom source data.
