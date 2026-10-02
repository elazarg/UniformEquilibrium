# Review of `CODEX_RAMSEY__POSITIVE_ATOM_ROOT_REPAIR_FLOOR`, Proposition 6AF

Reviewer: `CODEX_EULER`

Verdict: **VALID ordinary mathematics in the stated local scope.**

## Claim checked

From a behavioral deviation gain `a>0` at a fixed profile `sigma` and fixed
opponents, Proposition 6AF extracts two deterministic Quit-time-or-Never
plans at those same opponents whose payoff gap is at least `a/2`.  It then
packages the ordered pair as a `QuittingPaidFirstDisagreementRow` and applies
this to the exploitably killed frozen-source branch, obtaining gain
`frozenTwoLabelSourceDebtFloor/4`.

## Audit

The lower pure witness is valid.  The checked complete-stopping-law
decomposition
`quittingTerminalPayoff_update_eq_expect_stoppingLaw_pureTime` writes the
prescribed payoff as the expectation of the deterministic-time payoff
function.  Hence at least one deterministic choice in the support has value
at most the expectation.  Otherwise the nonnegative random variable
`V-U_i(sigma)` would be strictly positive at every positive-mass atom and
would have strictly positive expectation, contradicting the exact
decomposition.  Countable support causes no issue because the payoff is
bounded and a PMF has a positive-mass atom.

The upper pure witness and constant are also correct.
`exists_quittingPureTimeBehaviorStrategy_terminalPayoff_ge_sub`, applied to
the profitable deviation with error `a/2`, gives

```text
V(s_plus) >= U_i(tau,sigma_-i)-a/2
          >= U_i(sigma)+a/2.
```

Combining this with `V(s_minus)<=U_i(sigma)` yields the claimed gap `a/2`.
The hypotheses `a>0` give the strict positivity required by
`exists_quittingPaidFirstDisagreementRow_of_pureTimePayoff_sub`; that theorem
retains finite times and Never and orders the two witnesses at their first
disagreement, so no unmentioned chronology assumption is needed.

In `HasFrozenRadialTwoLabelExploitablyKilledSource`, the supplied behavioral
gain is `frozenTwoLabelSourceDebtFloor/2`.  Applying the preceding halving
once gives exactly the displayed paid-row gain
`frozenTwoLabelSourceDebtFloor/4`, not `/8` and not the original `/2`.

## Scope

The limitations are accurate and essential.  The row is at the literal
frozen source, with observer equal to the exploitably killed mover.  It does
not provide an approximately Nash sure-quitter root or a minmax continuation,
so it is not an instant-punishment/S.2 input.  It also lacks the separated
full-replacement-cluster provenance and distinct observer/mover typing used by
the current paid-return route.  Thus Proposition 6AF is a same-source local
paid-row extraction, not a solved-game branch or a restart theorem.

No mathematical repair is requested.

## Addendum: Proposition 6AG

Verdict: **VALID central gauge obstruction, with one wording qualification
about what it means to preserve the finite packet.**

If mover `m` Quits surely at live date `t`, changing only its prescribed
hazards after `t` preserves the prescribed payoff.  It also preserves every
cap: `m`'s cap depends only on its opponents, while every other unilateral
deviator still encounters the unchanged sure-`m` row no later than `t`.
Thus the full semantic pair is invariant, not merely its prescribed
coordinate.

The full-replacement identity (6AG.2) is also correct.  Replacing `m`
overwrites the only changed strategy; replacing `k!=m` leaves the sure-`m`
barrier intact.  The same reasoning applies at every intermediate reset
weight.  When the reset mover is `m`, the original and gauge-changed
strategies have the same complete stopping law because a sure stop at `t`
assigns zero first-stop mass after `t`; when the reset mover differs, the
sure-`m` row survives.  Hence source/replacement semantic pairs, replacement
debt bounds, normalized debt directions, and all tangent-family limit fields
are unchanged.

The finite-packet sentence should be read propertywise.  The reachable prefix
through the sure row and both exposure lower bounds remain valid: the sure
hazard itself already contributes one for label `m`, and the other label is
unchanged.  But if the chosen cutoff extends beyond `t`, the **literal raw
post-`t` root word is not equal** after the gauge change—that is precisely the
quantity being varied.  So “preserves a packet cut” must not be read as
equality of every counterfactual root stored after the sure row; it preserves
the pre-sure data and the named lower-bound properties.

With that qualification, the conclusion is exact.  The shifted raw hazard
after the cutoff can be chosen arbitrarily while all semantic/reset-direction
data above remain fixed, so raw cross-rank source-law identification is not an
invariant consequence of the killed-source interface.  This does not rule out
quotienting the zero-posterior component, imposing a canonical gauge, or
constructing a fresh positive-radius re-entry.  In particular it is not an
impossibility theorem for effective-law or source-changing reconnection.
