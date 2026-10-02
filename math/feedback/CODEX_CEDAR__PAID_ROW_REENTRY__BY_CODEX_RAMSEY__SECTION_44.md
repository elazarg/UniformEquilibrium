# Review of Section 44 of `CODEX_CEDAR__PAID_ROW_REENTRY`

Reviewer: `CODEX_RAMSEY`

Status: `VALID SHARP MIXED-THRESHOLD FLOOR REGRESSION`

## Claim checked

Section 44 modifies only terminal rows omitting the sure owner `k` in the
Section 42 table.  It claims that the original sure-face root, unique outsider
completion, and positive premium remain unchanged, while one mixed outsider's
conditional indifference threshold falls strictly below punishment despite a
strict singleton gap for the other outsider.

## Punishment-floor audit

For player `a`, Never guarantees at least zero: every terminal coalition of
the opponents pays either zero or, on the retained `{k}` row, one.  Opponents
`k=Never`, `b=Quit` surely at date zero hold `a` to zero, since Continue gives
`r_a({b})=0` and Quit gives `r_a({a,b})=-1`.  Hence `P_a=0`.

Player `b` has only nonnegative rewards.  Opponents `k=Never`, `a=Quit` surely
hold both of `b`'s root actions to zero, so `P_b=0`.  Both outsiders Never
hold `k` to its zero solo/Never payoff, so `P_k=0`.  Thus the punishment floor
remains exactly zero despite the negative `a` rows.

## Sure-face and threshold audit

At the Section 42 root `p_k=1`, every reached terminal coalition contains
`k`.  None of the modified rows is therefore used.  The matching-pennies
outsider game, its unique completion `p_a=p_b=1/2`, the charge-one exact root,
and `k`'s premium `3/20` are unchanged.  The new solo payoff
`r_b({b})=1/2` gives the stated strict singleton gap above the floor.

Conditional on `k` Continuing, player `a` faces `b` mixing `1/2`.  Forced Quit
always pays `-1`, so `Q_a^C=-1`.  Forced Continue has zero absorbing
contribution and opponent Continue mass `R_a=1/2`.  Hence

```text
T_a=(Q_a^C-K_a^C)/R_a=(-1)/(1/2)=-2<P_a=0.
```

If `p_k<1` while the outsider probabilities stay fixed and `a` remains mixed,
the positive probability of the conditional-Continue row forces `a`'s gap to
zero there.  Its only possible tail coordinate is therefore `-2`, outside the
punishment-floor box.

## Verdict and scope

I found no punishment error, changed sure-face datum, or threshold arithmetic
error.  The example exactly refutes automatic derivation of condition `(43.5)`
from a strict singleton gap and the original unique-sure face.

It does not rule out dropping `a` from support, moving the outsider root
jointly with `k`, or paying the displacement along later edges.  The note
states this narrow scope correctly.
