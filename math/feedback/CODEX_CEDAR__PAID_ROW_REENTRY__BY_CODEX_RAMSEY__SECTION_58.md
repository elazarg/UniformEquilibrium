# Review of CODEX_CEDAR paid-row re-entry, Section 58

Reviewer: `CODEX_RAMSEY`

Verdict: **PASS in the stated local-regression scope.**

For the table

```text
r({a})=(1,0),  r({b})=(0,1),  r({a,b})=(3,3),
```

the four semantic rows are exactly as displayed.  At `NN`, each player can
obtain one by quitting alone, so `B=(1,1)`.  At `Q_a N`, player `a` already
gets its solo value one and cannot improve; player `b` can join at date zero
for three, so `B=(1,3)`.  The other independent endpoint is symmetric.  At
`Q_a Q_b`, quitting simultaneously gives each player three and Continuing
gives zero, so `U=B=(3,3)`.  These are unrestricted behavioral caps: once an
opponent quits surely at date zero, no later behavior can improve on the
displayed immediate choice.

It follows exactly that each independent reset from `NN` has mover payoff
gain one, mover endpoint debt zero, total-debt increase one, and outsider-debt
increase two.  Immediate Quit attains the source cap and remains optimal at
the independent endpoint.  But the literal serial second step
`Q_a N -> Q_a Q_b` changes outsider `a`'s debt by zero and lowers total debt
from three to zero.  Thus the one-step fields used in Section 57 do not imply
its consecutive reached-step hypothesis.

The scope statement is correct.  `Q_a Q_b` is an exact terminal Nash sink and
the game has minimum debt zero.  This does not refute a theorem using the
positive-minimum/terminal-gap exclusions.  It only proves that common-base
independent resets, even with exact best-response endpoints and all the
listed transfer signs, do not concatenate formally without substantive new
input.
