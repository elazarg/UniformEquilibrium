# Review of Proposition 3: terminal-near approximate paths

Reviewer: `CODEX_EULER`

Source reviewed:
[`CODEX_RAMSEY__STRICT_ALLCONTINUE_BASIN_LINEAR_DEFECT.md`](../notes/CODEX_RAMSEY__STRICT_ALLCONTINUE_BASIN_LINEAR_DEFECT.md)

Verdict: **PASS**.  The backward bootstrap, edge orientation, and constants
are correct.  I found no repair.

The initial shrink is legitimate: intersect the Proposition 1 neighborhood
with a bounded open neighborhood of the compact set `K`.  Its closure need
not remain inside the original neighborhood; only boundedness and containment
of `K` are used.  Finite-dimensional compactness then gives `rho>0` whose
open sup-norm collar around `K` lies in the shrunken `N`.  A common `C>0`
bounds both the fixed reward table and all payoff coordinates in `N`.

The Bellman orientation is exact.  At step `t`, the root is Nash against the
tail `V_(t+1)` and its successor/head is `V_t`.  Starting from the supplied
terminal node `V_L`, the backward induction first admits `V_(t+1)` and hence
may apply the local linear-defect estimate to `q_t`.  The one-edge estimate
then gives

```text
||V_t-V_(t+1)||_infinity <= 2C A(q_t)
                         <= 2C |I| epsilon_t/c.
```

No circular assumption that `V_t` is already local is made.  Summing the
already admitted later edges together with the current edge yields

```text
||V_t-V_L||_infinity <= 2C|I|E/c < rho/2.
```

Combining this with `dist(V_L,K)<rho/2` places `V_t` in the `rho` collar and
therefore in `N`, closing the induction.  Once every tail has been admitted,
the absorption estimates sum to `sum A(q_t)<=|I|E/c`.  The constant
`E<c rho/(4C|I|)` is exactly what makes the displacement strictly below
`rho/2`.

The arbitrary-length consequence also has the right quantifiers: terminal
distance and the **aggregate** error must tend to zero.  A vanishing maximum
row error with unbounded length is correctly excluded from the conclusion.
The result controls successor-linked paths only and does not rule out a
single incoming edge whose tail is outside the collar.
