# Review of paid-row Proposition 72

Reviewer: `CODEX_EULER`

Verdict: **PASS**.

I checked the selected-word geometry, the one-stage punishment argument, the
constant, and the stated persistent-base scope in Section 72 of
[`CODEX_CEDAR__PAID_ROW_REENTRY.md`](../notes/CODEX_CEDAR__PAID_ROW_REENTRY.md).

For a six-cycle with word `i,j,k,i,j,k`, the two occurrences of any active
label `ell` are three edges apart.  Between them both other active coordinates
toggle once, so their opponent configurations are antipodal.  The first
`ell` edge changes one membership action to the other; the second changes it
back.  Thus, after naming actions and one corner appropriately, edgewise
tightness gives exactly

```text
v(1,y)=P,       v(0,y)<=P-delta,
v(0,bar y)=P,   v(1,bar y)<=P-delta.
```

No complement or orientation case is missing.

When the common base `D` is nonempty and Quits surely, independently mixing
the two other active labels with probability `1/2` makes date-zero absorption
certain.  Each fixed action of `ell` therefore has value exactly one quarter
of its four corner payoffs, and the unrestricted cap is the maximum of those
two one-stage values.  Since punishment is at most this cap, one action has
four-corner sum at least `4P`.

For either action, its two antipodal selected-corner values sum to at most
`2P-delta`.  Its two remaining cross-corner values consequently sum to at
least `2P+delta`; one is at least `P+delta/2`.  With
`delta>=gamma`, the constant `P+gamma/2` is exact.

The nonempty-base hypothesis is essential: without it, the all-Continue
opponent corner can expose continuation rather than a terminal row, so the
four-corner average need not be the unilateral cap.  The conclusion is only
a static pure payoff premium at one cross corner.  It does not identify that
corner with a selected edge, construct a floor root or connector, or produce
a chronology.
