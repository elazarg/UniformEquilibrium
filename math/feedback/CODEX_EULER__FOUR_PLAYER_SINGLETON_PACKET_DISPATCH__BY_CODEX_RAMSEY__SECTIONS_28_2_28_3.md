# Review of Propositions 28.2--28.3

Reviewer: `CODEX_RAMSEY`

Verdict: **PASS**.

## Proposition 28.2

The selected weights are nonnegative and sum to `H>0`, in both pure and
strict mixed arms.  Hence `K_d>0` forces a positive-weight cell with
`k_d^he>=K_d/H`, equivalently `H*k_d^he>=K_d`.  No assertion that this cell is
itself a Nash cell is used or needed.

When `T_he` is empty, the definition of the floor excess gives exactly
`chi_d-r_d(d)>0`.  When it is nonempty,

```text
k_d^he=r_T(d)-r_(T union {d})(d)>=K_d/H,
```

so `d` has the displayed strict outsider no-join margin.  The remaining
membership tests exhaust all players: members of `T`, outsiders other than
`d`, and the already controlled outsider `d`.  The empty-erasure convention
for a singleton member is correct.  If every test holds, they are precisely
`IsQuittingSureExitSet reward T`; otherwise the failing test cannot be `d`,
and the two residual alternatives in (28.16) are the exact finite negation.
The named sure-exit consumer supplies the unrestricted-behavior conclusion.

## Proposition 28.3

The oriented gain `G_y` is the weighted average of the oriented cell gains
`g_he`, so the same positive-weight extraction gives
`H*g_he>=G_y>0`.  The two action orientations are correct:

- for `j=0`, `y` joins and becomes a member of
  `P=O_he union {y}`, with no-leave margin `Delta_y^he`;
- for `j=1`, `y` leaves and becomes an outsider of `P=O_he`, with no-join
  margin `-Delta_y^he`.

In both cases `P` is nonempty because `d` belongs to `O_he`.  After fixing
`y`'s strict membership inequality, the remaining member-leave and
outsider-join tests exhaust every other label.  If they hold, the exact
sure-exit consumer applies; if one fails, it necessarily has a label distinct
from `y`, yielding exactly (28.21).  The empty-erasure convention is again
correct.

## Scope

Both results are finite pure-cell extractions from the repaired product law.
They preserve quantitative margins and reach an existing all-behavior
consumer only after all literal membership tests pass.  They do not claim the
extracted cell is a root equilibrium, do not iterate the resulting toggle,
and do not manufacture a chronology.  No repair is required.
