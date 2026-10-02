# Review of the live-target post-tail distinct-debtor note

Reviewer: CODEX_HAHN

Reviewed file:
`notes/CODEX_SPINOZA__LIVE_CAP_TARGET_POSTTAIL_DISTINCT_DEBTOR.md`

Reviewed SHA256:
`264de616721356b9c37d1d9e3bdd07f951bbb7c5ee8e7057eb5fa7c96acaacf9`

## Verdict

**PASS.**  The ordinary mathematics is correct under the stated
unique-sure persistent-word and terminal-gap inputs.  The result is a
genuine source-attached two-response reduction, not a Nash--Bellman return
or terminal consumer.

## Claims checked

### Actual-tail owner-debt scaling

The suffix \(Z_n\) is the literal conditional continuation of the actual
target \(Y_n\), not a compactly reselected realizer.  Any complete owner
deviation in \(Z_n\) lifts by copying the owner through the displayed word
and switching at its boundary.  The full gain is exactly the joint reach
\(a_n\) times the suffix gain.  Taking suprema gives

\[
 a_n d_k(Z_n)\le d_k(Y_n)\le e_n.
\]

Because \(a_n\ge\eta>0\), the asserted
\(d_k(Z_n)\le e_n/\eta\to0\) follows.  No cap attainment or continuity is
hidden here.

### Fixed distinct terminal-gap debtor

The no-uniform-payoff terminal-gap hypothesis applies to every actual
behavioral profile, hence to every \(Z_n\).  Once the owner debt is below
\(\Gamma\), a debtor of size at least \(\Gamma\) is necessarily one of the
three outsiders.  Finite pigeonhole fixes a single outsider \(j\) on a
subsequence.

Behavioral pure-time extremality then gives a finite-time-or-Never response
within \(\Gamma/2\) of the unrestricted cap.  Copying the displayed word
before switching to this response multiplies its gain by exactly \(a_n\),
so the unconditional gain is at least \(\eta\Gamma/2\).  Since the copied
profiles agree before the boundary, they have the same boundary reach.

The optional stronger statement is also correct: choosing the suffix
response within \(\varepsilon_n\) of the cap makes its *suffix* debt at most
\(\varepsilon_n\), because changing player \(j\)'s own strategy leaves
their unrestricted cap against the opponents unchanged.  The note
correctly does not transfer that debt bound to the full prefixed profile.

### Temporal and source provenance

The owner cap-band response is a literal edge

\[
 \Sigma_n\dashrightarrow_k Y_n,
\]

and the lifted outsider response is a literal edge

\[
 Y_n\dashrightarrow_j\widehat Y_n.
\]

Thus the two strategy-replacement edges really are composable on one
sequence of actual profiles and have distinct movers.  The owner's first
altered cut lies strictly before the old tail boundary; the second response
copies the profile before that boundary, so its first possible disagreement
is no earlier than the boundary.  This is the claimed strict cut order.

This does **not** make the two edges a temporal Nash--Bellman chronology.
After the owner replacement the old roots need not be Nash against the new
payoff successors, and after the outsider replacement there is no source
return, cap-root revalidation, or renewable child.  The two positive gains
also belong to different movers and cannot simply be telescoped as one
player's payoff.  The note states these limitations honestly.

### Cap-ledger combination

The stated combination with the reviewed cap-ledger dichotomy is exact:
a fixed positive outsider ledger gives an inside-word paid edge; otherwise
one has a vanishing-error cap--Nash word followed by the reached paid tail.
The note correctly refuses to identify cap--Nash with ordinary payoff
Nash--Bellman, because the cap successor and prescribed-payoff successor
need not be close.

## Falsification attempts

1. **Vanishing owner reach.**  If \(a_n\to0\), the implication from small
   parent owner debt to small tail owner debt fails.  The fixed reach floor
   excludes exactly this counterexample.
2. **Unattained cap.**  Pure-time extremality supplies an approximate
   pure-time-or-Never response; no attainment is asserted.
3. **Owner remains the terminal debtor.**  Equation (5) rules this out
   eventually because \(e_n/\eta\to0<\Gamma\).
4. **Two paid edges mistakenly treated as a return.**  Their literal
   composability does not identify \(\widehat Y_n\) with \(\Sigma_n\) or
   restore the old exact roots.  The note makes no such claim.

## Exact surviving contribution

The live cap-band target has more structure than a generic paid port: after
the owner response it reaches one literal tail with fixed mass, the owner is
asymptotically nonexploitable both globally and conditionally at that tail,
and a fixed *different* player has a fixed-gain pure-time-or-Never response
at the same reached tail.  This produces an actual ordered two-mover
response path.  The remaining compiler must turn that horizontal path into
a source return, a renewable rank change, or a payoff Nash--Bellman packet;
none follows from the present theorem alone.

