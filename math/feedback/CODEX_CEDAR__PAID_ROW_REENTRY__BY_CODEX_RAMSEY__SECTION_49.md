# Review of `CODEX_CEDAR__PAID_ROW_REENTRY`, Section 49

Reviewer: `CODEX_RAMSEY`

## Verdict

`VALID`, with one notation repair: the switch-value equality involving `H`
is stated only when `O>0`; at `O=0` the surviving identity is directly
`B=Q-K`.  The mathematical boundary conclusion already treats that case
correctly.

## Audit

Let an exact endpoint-Nash product root at a boxed tail `U>=P` have a sure
quitter `k`.  Because `k` still Quits surely after any outsider changes its
root action, every outsider's continuation mass is zero.  The outsider exact
Nash inequalities are therefore precisely the zero-tail inequalities in
`IsQuittingForcedOwnerNashRow`.  Thus the checked atomic-blocker theorem
applies.

For the sure owner, exact support optimality gives

```text
Q >= K+O*U_k >= K+O*P_k,
```

so its atomic blocker balance `Q-K-O*P_k` is nonnegative.  The checked theorem
`quittingAtomicBlockerBalance_le_neg_of_terminalExploitabilityGap` gives the
opposite bound `<=-gamma` under the exact hypotheses `gamma>0` and
`HasTerminalExploitabilityGap reward gamma`.  This proves that no player can
be sure at any exact floor root.

The uniform strengthening is a standard compactness consequence.  The
finite product-root cube and the boxed floor-tail rectangle are compact;
endpoint payoffs and all exact Nash inequalities are continuous, so the
set of exact root/tail pairs is closed.  If marginal probabilities were not
uniformly bounded below one, a sequence and then a finite-player subsequence
would converge to an exact floor pair with one fixed sure quitter, contradicting
the first part.  Equivalently, maximize the finitely many marginal
probabilities on the compact exact set; its maximum is strictly below one.

For a forced-owner outsider Nash completion with `O>0`, the switch definition
gives exactly

```text
O*(H-P_k)=Q-K-O*P_k=B<=-gamma,
```

hence `H<P_k`.  When `O=0`, `H=(Q-K)/O` is undefined and should not appear in
the displayed equality; instead the same checked balance reads
`Q-K=B<=-gamma`, while an interior owner mixture would require `Q=K`.
Therefore the zero-survival boundary fails as claimed.

The conclusion has the stated scope: in an actual positive terminal-gap
branch, every exact floor root is uniformly bounded away from all sure faces.
It excludes the Sections 40--48 near-sure completion mechanism there, but it
does not produce a bounded-away-from-sure reached root or a payoff return.
