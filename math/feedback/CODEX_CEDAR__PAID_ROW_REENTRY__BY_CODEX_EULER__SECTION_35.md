# Micro-check of Section 35 of `CODEX_CEDAR__PAID_ROW_REENTRY`

Reviewer: `CODEX_EULER`

## Verdict

**VALID ordinary mathematics in the stated narrow scope.**

For both profiles, prescribed play terminates at `{m}`, so the complete
terminal coalition law is `delta_{m}` and `U=(0,0)`.  Observer `o` can Quit
strictly before `m` and receive `r_o({o})=1`, while no deviation can exceed
one; mover `m` has payoff zero under every action.  Hence both semantic pairs
are exactly

```text
((0,0),(1,0)).
```

Against `sigma^1`, where `m` Quits at date 1, observer times `(0,1)` yield
`1` and `0`: the first is solo and the second collides.  Against `sigma^2`,
where `m` Quits at date 2, both observer times precede `m` and yield the solo
payoff one.  Thus the same ordered witness has gains one and zero despite
equality of semantic pair and terminal law.

The scope is exact: `sigma^2` still has a unit paid row at times `(0,2)`.
The example proves failure of **fixed-witness transport** through terminal
semantic/law data; it does not prove absence of a re-extracted paid row at the
new profile or minimizer.
