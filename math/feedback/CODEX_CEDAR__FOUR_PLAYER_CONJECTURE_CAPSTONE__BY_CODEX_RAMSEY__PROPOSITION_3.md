# Review of Proposition 3 in `CODEX_CEDAR__FOUR_PLAYER_CONJECTURE_CAPSTONE`

Reviewer: `CODEX_RAMSEY`

## Verdict

**PASS.**  The whole envelope-to-prescribed debt segment is pointwise frozen,
the singleton separation is uniform along it, and compactness upgrades this
to one open unique-root tube.  No carrier or punishment-floor hypothesis is
silently imposed on the nearby tails.

## Audit

Write `d=B-U` and

```text
H(t)=B-t d,    0<=t<=1.
```

For `0<=t<1`, this is literally the tail appearing in
`minimumTerminalSemantic_debtHomotopy_eq_allContinue`.  Its hypotheses are
the fixed pair's carrier membership, global debt minimality, positive total
debt, and the displayed range of `t`; the theorem makes every exact root at
`H(t)` all-Continue.  At `t=1`, `H(1)=U`, and reviewed Proposition 2 supplies
the same uniqueness.  Thus both endpoints and the half-open interior are
covered without a gap.

Carrier debt nonnegativity gives `d_i>=0`, hence

```text
H(t)_i = U_i+(1-t)d_i >= U_i > s_i.
```

If `delta=min_i(U_i-s_i)`, this gives the same gap at least `delta` for all
players and all `t`.  It also shows that all-Continue is exact on the entire
segment.

For the uniform tube, suppose tails with non-all-Continue exact roots approach
the compact segment.  Select `t_n in [0,1]` with
`V_n-H(t_n)->0` (an exact nearest point exists, though an asymptotic selector
is enough).  Compactness of `[0,1]` gives `t_n->t` along a subsequence, so
`V_n->H(t)`.  Eventually `V_{n,i}-s_i>delta/2` for every player.  The reviewed
outsider-decomposition calculation then gives every root the common lower
absorption bound

```text
delta/(delta+4M)>0.
```

Root compactness, joint continuity of the exact endpoint-Nash inequalities,
and absorption continuity produce a positive-absorption exact root at
`H(t)`, contradicting the pointwise uniqueness above.  Therefore some open
neighborhood of the segment has no non-all-Continue exact roots.

For complete proof-writing precision, intersect that neighborhood with the
open coordinate set `V_i>s_i` for every `i`.  This retains the whole segment
and ensures all-Continue is itself exact at every tail in the final tube.
Thus it is the unique exact root throughout the tube, and every exact edge
whose continuation/tail lies there is the zero-charge identity.

The result remains an obstruction only.  It neither constructs a nonlocal
predecessor nor controls approximate Nash roots or approximate seams.
