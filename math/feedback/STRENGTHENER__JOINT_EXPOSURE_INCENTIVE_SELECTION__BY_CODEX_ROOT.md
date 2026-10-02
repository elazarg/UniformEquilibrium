# Review of joint exposure--incentive selection

Reviewer: `CODEX_ROOT`

## Claim reviewed

The note couples singleton exposure and owner incentive under the same
source stopping-law mixture.  It proves a sharp weighted selection inequality,
an anchored whole-completion version, a high-exposure/low-exposure polarity,
and a cofinal near-minimum consequence: either a fixed-mass owner completion
does not asymptotically worsen owner debt, or a source-matched completion
drains a fixed amount of owner debt and global minimality forces compensating
debt transfer to the other players.

## Verdict

**Pass as ordinary mathematics.**  The positive-anchor correction is
essential and valid: the zero-mean variables must be gains of complete
copied-prefix completions, not raw tail pure-time gains.  The result is
source-dependent and strictly stronger than the universal concentrated-packet
adapter.  It still has no consumer for the complementary debt leakage, so it
is not yet a complete conjecture-facing export.

## Abstract selection lemma

Let `H={s>lambda}` and `w=pi(H)`.  From `0<=s<=p` and `E[s]=mu`,

\[
 w\ge\frac{\mu-\lambda}{p-\lambda}.
\]

Since `E[Y]=0` and `Y<=d`,

\[
 E[Y1_H]=-E[Y1_{H^c}]\ge-d(1-w).
\]

Some supported point in `H` therefore satisfies

\[
 Y\ge-d\frac{1-w}{w}
 \ge-d\frac{p-\mu}{\mu-\lambda}.
\]

The derived debt factor `(p-lambda)/(mu-lambda)` is exact.  The two-point
quitting-game example realizes equality, so no stronger conclusion about an
active owner follows from these two moments alone.

## Positive-anchor semantics

Condition on the owner reaching the anchor and decompose its conditional
stopping law into deterministic conditional deadlines, including `Never`.
For each deadline, copy the entire pre-anchor strategy and every opponent.
The original behavioral strategy is exactly the mixture of these whole
completions.  Terminal payoff affinity therefore gives `E_alpha[Y]=0`.

This formulation retains all pre-anchor payoff terms automatically.  The raw
tail pure-time gain would not have mean zero when the anchor is positive and
would make the claimed selection invalid.

Changing only the owner's strategy leaves its unrestricted cap fixed.  Thus
the selected completion's owner debt is exactly `d-Y`.  The exposed singleton
mass has expectation equal to the source singleton mass after the anchor and
is bounded above by the copied anchor-reach probability.  All hypotheses of
the abstract lemma match.

## Polarity and near-minimum application

If some supported high-exposure completion has gain greater than `-kappa`, it
is almost safe for the owner.  Otherwise every high-exposure completion loses
at least `kappa`; zero mean forces a supported low-exposure completion with a
positive gain bounded below by

\[
 \kappa\frac{\mu-\lambda}{p-\mu}.
\]

The note's cofinal dichotomy follows by splitting according to the limsup of
the best high-exposure gain.  In the fixed-gain arm, owner-cap invariance gives
exact owner-debt subtraction.  Since the reference profiles have total debt
`D_*+o(1)` and every actual target has debt at least `D_*`, the other
coordinates' aggregate debt rise is at least the gain minus `o(1)`.  No sign
assumption on individual recipients is used.

When the singleton owner is inactive at the minimum, the high-exposure branch
keeps its debt vanishing.  A terminal exploitability gap must then be carried
by a fixed nonowner along a subsequence.  If two pure-time witnesses for that
nonowner first differed strictly after the marked singleton date, they would
coincide through the date at which the owner quits surely; play would absorb
there under both plans and their payoffs would be equal.  Hence a positive
paid row first disagrees no later than the mark, as claimed.

## Remaining boundary

The theorem produces one of two genuinely attached objects:

```text
fixed singleton exposure + asymptotically safe owner coordinate
```

or

```text
fixed owner debt drain + complementary near-minimum debt transfer
             + oppositely oriented high-exposure completion.
```

Neither controls the target's total debt from above, prevents entry of new
debt coordinates, preserves the old exact cap stack for the modified target,
or supplies a prescribed-payoff return.  A consumer still needs a
cross-coordinate leakage restriction or a renewable response square.

## Recommendation

Retain this as a high-priority reviewed producer candidate.  Before export,
seek a second independent falsification and decide whether the exact
source-attached polarity constitutes a named strict atlas contraction, or
whether it should be bundled with a consumer of the resulting complementary
transfer.
