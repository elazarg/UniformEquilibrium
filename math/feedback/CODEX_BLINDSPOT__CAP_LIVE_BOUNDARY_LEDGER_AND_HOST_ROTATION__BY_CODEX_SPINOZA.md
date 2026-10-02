# Review of cap-live boundary ledger and host rotation

Reviewer: `CODEX_SPINOZA`

Reviewed artifact:
`notes/CODEX_BLINDSPOT__CAP_LIVE_BOUNDARY_LEDGER_AND_HOST_ROTATION.md`,
exact SHA-256
`0fd90d0fafac4c8c931c568fa094cedf659494bf5eed6dd924cbb7c83bb82fc1`.

## Verdict

**PASS.** The cap-anchored playerwise debt identity, zero-joint
necessary-and-sufficient criterion, deleted-clock geometry, concatenation
ledger, and fixed aggregate payer conclusion are correct.  I found no
terminal compiler or source-renewal overclaim.

One scope point should remain explicit in downstream use: the Section 7
host clock is measured on the original premark word, whereas its unit ledger
is measured on the host-cleared endpoint word.  The note describes both
profiles separately and so is correct as a regression against the maintained
two-profile field list; it is not an example of one unchanged word having
both \(\beta_0=1\) and \(\Lambda_1=1\).

## Exact one-row and word identities

For player \(k\), the complete cap of a prefixed row is the maximum of the
Quit and Continue endpoints evaluated at the actual suffix cap
\(b_{t+1,k}\).  Inserting the prescribed mixture evaluated at that same cap
gives

\[
 B_k(x_t\star\sigma_{t+1})-U_k(x_t\star\sigma_{t+1})
 =c_{t,k}+a_t\bigl(b_{t+1,k}-u_{t+1,k}\bigr).
\]

The coefficient is full joint Continue mass: the player's own Continue
factor in the prescribed mixture multiplies the opponents' Continue factor
in the continuation endpoint.  Iteration gives exactly (2.1)--(2.2).  The
cap-diagonal formulation (2.5) is the same calculation because the complete
prefix cap depends only on the suffix cap.  Thus the purported host cap seam
really disappears when the actual suffix cap is retained; it has not been
dropped by an estimate.

With \(\alpha_n\to0\), boundedness of terminal debts and nonnegativity of all
ledger terms prove both directions of Corollary 2.2.  Compactifying the
bounded prescribed payoff vectors then supplies one fixed target for the
terminal acceptance theorem.  The exact cap--Nash specialization correctly
sets every local cap defect to zero.

## Deleted clocks and concatenation

For distinct \(i,j\), every per-date Continue factor occurs in
\(\beta_i\beta_j\) at least as often as in \(\alpha\), hence
\(\beta_i\beta_j\le\alpha\).  Therefore at most one deleted-survival limit is
positive when joint survival vanishes.  Finite-label subselection freezes a
rotating host but cannot average playerwise exploitability.

Both concatenation formulas have the stated orientation.  Deleted survival
multiplies.  The inner defect ledger is reached with the outer word's joint
survival, while the outer ledger is unscaled and nonnegative.  Consequently
a second serial host can erase deepest-tail sensitivity but cannot erase an
outer ledger floor.

## Positive-minimum payer and regression

The aggregate identity and global lower bound give

\[
 \liminf_n\Lambda(W_n,\tau_n)\ge D_*.
\]

Once the terminal term is at most \(D_*/2\), the finite bound
\(\Lambda\ge D_*/2\) follows.  Four-player pigeonhole then yields a fixed
player on a subsequence with playerwise ledger at least \(D_*/8\).  This is
only an aggregate-in-time payer, as the note correctly emphasizes.

In Section 7, after clearing the original sure host, the marked row with
player 2 sure has reached weight one.  Against zero suffix cap, player 1's
Quit endpoint is one and its prescribed Continue endpoint is zero, so the
cleared word has \(c_{\mathrm{marked},1}=\Lambda_1=1\) and exact debt one.
On the separate original premark word, player 0 sure gives the displayed
positive-host clock pattern.  This faithfully reproduces the prior
two-profile outsider regression and does not establish a one-word
host-plus-ledger invariant.

The exact remaining question is therefore the note's fixed payer/host split:
convert a diffuse positive playerwise ledger into source-attached temporal
charge, or show that its diffusion supplies an executable spine.  Neither is
claimed here.

## Exact-final standalone check

**PASS** for
/tmp/CAP_ANCHORED_ZERO_JOINT_LEDGER_AND_HOST_ROTATION_BOUNDARY.md,
exact SHA-256
ae649c0a57ee0f1e862c097335d39e41ce5335334474984029701c358bba647a.

The staged packet faithfully preserves the reviewed playerwise identity,
the zero-joint iff, the \(D_*/2\) aggregate and \(D_*/8\) fixed-payer
bounds, the two-host inequality, and the serial append orientation. Its
boundary test now says explicitly that the positive host clock belongs to
the original premark word while the unit ledger belongs to the distinct
host-cleared endpoint word. It makes no one-word invariant, paid-row,
renewal, or full-conjecture claim. All mandatory headings are present,
the future-export-relative local links resolve, and the control-byte scan
is clean.
