# Review of strict endpoint re-exactification trichotomy

Reviewer: `FORCED_PAIR_REVIEW`

Source:
[`ATLAS_GATEKEEPER__STRICT_ENDPOINT_REEXACTIFICATION_TRICHOTOMY.md`](../notes/ATLAS_GATEKEEPER__STRICT_ENDPOINT_REEXACTIFICATION_TRICHOTOMY.md)

Verdict: **PASS for the exact sibling-prefix account (9)--(12), the
minimum-sibling support handoff, the stated exactness boundary, and the
corrected direct packet construction from the minimum exactification
sequence.  STRENGTHEN the sibling-charge arm by adding its literal paid-row
decoder.  The corrected source-facing reduction is export-worthy as an atlas
contraction: minimum exactification enters the already named concentrated
consumer independently of the copied sibling.**

The new source charge is real chronology data, but its strict surcharge is
algebraically the copied sibling's off-minimum excess.  It does not make the
copied word exact on the source branch.  The fixed positive charge does yield
a source-matched all-behavior paid row, more strongly than the note states;
however, neither that row nor the independent terminal-gap paid row rules out
an inert cap lift.  This no longer leaves a new predecessor node, because the
exactified endpoint sequence itself has already entered the existing
concentrated packet consumer.

## 1. Exactness audit

Write (E_n) for the killed-mover endpoint, (X_n) for its source sibling,
and (W_n) for the finite root word selected as an exact cap--Nash stack over
(E_n).  Put

\[
 V_n=W_n\triangleright E_n,
 \qquad
 U_n=W_n\triangleright X_n,
\]

and let (c_n) be the product of the word's joint Continue masses.

The note correctly asserts exactness only on the (E_n/V_n) branch:

\[
 D(V_n)=c_nD(E_n),
 \qquad
 d_p(V_n)=c_nd_p(E_n)=0.
\]

No root of (W_n) is assumed exact against the corresponding source-sibling
successor cap.  On that branch one must use the arbitrary-root identity

```text
quittingTerminalSemanticDebt_prefix_eq_capDefect_add_continueMass_mul
```

rather than exact cap scaling.  The source note respects this distinction.
The exact four-player regression it cites is relevant: changing the deep
strategy of (p) can change another player's suffix cap, so copying a root
which was exact over (E_n) need not leave it exact over (X_n).

The copied profiles (U_n,V_n) still differ only in (p)'s strategy.  Thus
(p)'s full cap is common to both.  The pure-pair endpoint kills all of
(p)'s endpoint debt, and the common word transports the marked payoff gain
with factor (c_n).  Consequently the note's later facts

\[
 d_p(U)>0,
 \qquad
 d_p(V)=0
\]

in the minimum-sibling arm are sound.  They do not require source-side
exactness of (W_n).

## 2. Equations (9)--(12): PASS

For the literal prefix chain of (U_n), let

\[
 r_{n,i}:=
 \sum_{t<h_n}s_{n,t}\Delta_{n,t,i},
\]

where (Delta_{n,t,i}) is player (i)'s coordinate root defect against the
actual source-branch successor cap and (s_{n,t}) is the reached prefix
weight.  The checked finite debt account gives coordinatewise

\[
 d_i(U_n)=r_{n,i}+c_nd_i(X_n).
\tag{R1}
\]

Every summand is nonnegative.  Summing (R1) over four players and defining

\[
 R_n:=\sum_i r_{n,i}
\]

gives exactly

\[
 \boxed{D(U_n)=R_n+c_nD(X_n).}
\tag{R2}
\]

This is the note's (9).  It is a literal-prefix theorem; it does not assert
that any row is Nash.

Since every (U_n) is an actual profile, (D(U_n)\ge D_*).  Therefore

\[
 R_n\ge D_*-c_nD(X_n).
\]

Under

\[
 c_n\to c=D_*/L,
 \qquad
 D(X_n)\to D_*,
\]

the lower limit is

\[
 \liminf_nR_n\ge(1-c)D_*
 =\frac{D_*(L-D_*)}{L}>0.
\]

Thus (10) is correct.

Rearranging (R2) gives the exact identity

\[
 R_n-(1-c_n)D_*
 =D(U_n)-D_*+c_n(D_*-D(X_n)).
\tag{R3}
\]

The last term tends to zero.  Hence along every subsequence on which either
side has a limit,

\[
 \lim_n\bigl(R_n-(1-c_n)D_*\bigr)
 =\lim_n\bigl(D(U_n)-D_*\bigr).
\tag{R4}
\]

Equations (11)--(12) are therefore correct.  The displayed limit in the
source note should retain (c_n) inside the left expression, as in (R4), or
explicitly say that replacing it by (c) changes the expression by (o(1)).

The interpretation also needs one qualification.  The term
((1-c_n)D_*) is the minimum-debt absorption payment.  The strict surcharge
is exactly the copied source sibling's whole-debt excess, up to (o(1)).  It
is not a second independent scalar obstruction; its additional information
is the distribution of that excess among concrete rows of the common word.

## 3. Minimum copied sibling: PASS

If (D(U_n)\to D_*), then clusters (U,V) lie on the same positive minimum
fibre, (d_p(U)>0), and (d_p(V)=0).  Literal half stopping-law mixtures of
the two (p)-strategies satisfy coordinate debt convexity.  Global
minimality forces equality in every coordinate, so the mixture cluster (H)
has

\[
 \operatorname{supp}^{+}d(H)
 =\operatorname{supp}^{+}d(U)\cup\operatorname{supp}^{+}d(V)
\]

and

\[
 \operatorname{supp}^{+}d(V)
 \subsetneq
 \operatorname{supp}^{+}d(H).
\]

The checked tangent-family extractor at (H) and minimum-fibre
re-extraction at (V) apply exactly as in the reviewed canonical endpoint
packet.  Again, the rank parent is the new half-mixture point (H), not
necessarily (U) or the original (X_n) limit.

## 3A. Corrected direct packet from the minimum exactification: PASS

The source note's corrected Section 4 is valid and makes the copied-sibling
split downstream rather than predecessor-level.

Let (T) be the routed nonempty coalition at the killed-mover marked row in
(E_n), and let (t_n) be its shifted date in
(V_n=W_n\triangleright E_n).  Freeze (T) after the already permitted
finite-label subsequence.  If the endpoint row before fresh exactification
has stage-mass floor (\lambda>0), literal prefix transport gives

\[
 \operatorname{StageMass}(V_n,t_n,T)
   =c_n\operatorname{StageMass}(E_n,\text{old mark},T).
\tag{P1}
\]

Because (c_n\to D_*/L>0), after deleting finitely many ranks one may take,
for example,

\[
 \rho:=\frac{D_*}{2L}\lambda>0
\]

as a uniform packet resolution.  This finite deletion should be represented
either by reindexing the profile family itself or by one strict packet
subsequence; it is not a quantifier gap.

The remaining `QuittingReprojectionConcentratedPacket` fields are literal:

* `profiles n := V_n` after the reindexing;
* `subseq := id`, which is strictly monotone;
* `mark n := t_n` and `cutoff n := t_n+1`;
* `scale n := 1/(n+1)`, positive and tending to zero;
* (P1) supplies `stageMass`;
* the actual spine identity and carrier membership supply `semanticPrefix`;
* positive unconditional stage mass implies positive root incidence; and
* the marked root is the literal best endpoint of (p), so its coordinate
  root defect against the actual post-mark prescribed payoff is exactly zero.
  Hence the normalized `defect_tendsto` numerator is identically zero.

The outer word does not alter the root or tail at the shifted mark except by
shifting its date.  In particular, endpoint-side cap exactness of the outer
word is not needed to prove the packet's marked zero-defect field; literal
best-endpoint selection at the pure marked row proves it.

The routed coalition always contains a player other than owner (p).  If
(p) leaves the original pair, (T) is the other member's singleton.  If
(p) joins, (T) contains the original pair and (p).  Thus one can choose

\[
 \texttt{other}\ne p,
 \qquad
 \texttt{other}\in T,
\]

as required by

```text
QuittingTerminalExploitabilityWitness.
  concentratedPacket_singletonStrategic_or_collisionMinimumResidual
```

using the retained terminal witness and original positive global minimum.
The exact checked output is

\[
 \boxed{
 \texttt{HasQuittingConcentratedSingletonStrategicDispatch}
 \ \lor\ 
 \operatorname{Nonempty}
   (\texttt{QuittingConcentratedCollisionMinimumResidual}).}
\tag{P2}
\]

No convergence of whole source debt is required by this generic consumer.
Thus even the packet construction alone suffices for (P2).  Here the source
contains more:

\[
 D(V_n)\to D_*,
\]

and its literal post-mark tail is the original retained minimum-return tail.
Consequently, in the nonsingleton case one can invoke the stronger existing
collision compiler

```text
ConcentratedCollisionFourRole.
  packet_eventually_tailEscape_or_threeRoleTransfer
```

with `hsourceDebt`.  The packet-tail excess tends to zero while the escape
threshold (\rho D_*/2) is fixed positive, so the tail-escape alternative is
eventually false.  Hence sufficiently late rows carry actual
`ThreeRoleTransfer` data; finite pigeonhole can then enter the existing fixed
three-role/limit-chord output.  Equivalently, any collision residual selected
by (P2) has minimum total debt at its tail cluster.

The singleton branch is exactly the named strategic singleton output, not a
terminal equilibrium.  The nonsingleton branch is exactly the maintained
collision/three-role residual, not a support descent.  This is nevertheless a
strict atlas contraction: no condition on (D(U_n)) is needed to enter those
already existing nodes.

### Source indexing and provenance

There is no target-family mismatch.  The packet profile family is the actual
sequence (V_n), not the old (E_n) family with an unrelated target field.
The varying word lengths are absorbed into the explicit marks (t_n).
Deleting an eventual prefix and freezing (T) can be done before defining
the family.

The generic packet type itself forgets the old source, exactification words,
and copied siblings.  A Fin4 atlas theorem should therefore return it inside
a dependent wrapper storing the original strict endpoint source and the
selected (W_n).  That is a Lean packaging seam only; every consumer premise
in (P2) refers to the same actual (V_n) packet.

Most importantly, (U_n) is irrelevant to (P1)--(P2).  Whether the copied
sibling is minimum or strictly off minimum merely supplies extra rank or
charge information attached to a packet which has already been dispatched.

## 4. The reached charge has a stronger literal paid-row decoder

The note says that (18) is not itself an exact path edge.  That is correct,
but it understates the literal deviation data available from (R_n).

From

\[
 R_n=\sum_{i\in I}r_{n,i}
\]

and (|I|=4), some player (i_n) has

\[
 r_{n,i_n}\ge R_n/4.
\tag{R5}
\]

Equation (R1) and tail-debt nonnegativity imply

\[
 d_{i_n}(U_n)\ge r_{n,i_n}\ge R_n/4.
\tag{R6}
\]

Fix any (0<\gamma_n<R_n/4).  The quitting-game pure-time representation of
the behavioral cap supplies a deterministic Quit date or Never whose payoff
against (U_{n,-i_n}) is more than
(U_{i_n}(U_n)+\gamma_n).  The prescribed stopping law of (i_n) writes
(U_{i_n}(U_n)) as the bounded average of the same pure-time payoffs.
Therefore one pure time in the prescribed law's support lies below the
selected receiving pure time by at least (gamma_n).  Applying

```text
exists_quittingPaidFirstDisagreementRow_of_pureTimePayoff_sub
```

gives a literal

```text
QuittingPaidFirstDisagreementRow reward U_n i_n gamma_n.
```

This proof is the local-profile version of

```text
HasTerminalExploitabilityGap.exists_supported_pureTimePayoff_sub_at
HasTerminalExploitabilityGap.exists_paidFirstDisagreementRow_at.
```

It covers finite dates, arbitrarily late dates, Never, and unrestricted
behavioral deviations.  After freezing the player on a subsequence, the
lower bound (10) allows any fixed

\[
 0<\gamma<\frac{(1-c)D_*}{4}
\]

eventually.  In the strict-surcharge arm one may instead use any fixed number
strictly below one quarter of the corresponding lower bound for (R_n).

There is also an independent stronger-in-a-different-direction decoder.  The
positive global minimum implies

\[
 \max_i d_i(\sigma)\ge D_*/4
\]

at every actual profile (sigma).  Thus every (U_n), irrespective of
(R_n), carries a paid first-disagreement row of every fixed gain

\[
 0<\gamma<D_*/4.
\]

Equivalently, under the maintained terminal exploitability witness, the
checked actual-profile paid-row theorem supplies the project's fixed full
gap.  The (R_n)-decoder is valuable because it is quantitatively tied to
the copied word's debt account, but its first-disagreement date need not lie
inside (W_n), and its observer need not be a fixed rowwise defect maximizer.

## 5. Why the paid-row strengthening does not consume arm (18)

Attach the decoded paid row to (U_n) and invoke the checked cap-lifted
summable-port construction.  Its exact alternatives are:

\[
 \text{charged near-return}
 \quad\lor\quad
 \text{quantitative debt descent}
 \quad\lor\quad
 \text{literal inert stall}.
\]

Under the terminal exploitability witness, the charged near-return arm is
impossible because its checked consumer yields a uniform-equilibrium payoff.
The remaining output is still

\[
 \text{quantitative real debt descent}
 \quad\lor\quad
 \text{inert all-Continue stall}.
\]

The descent limit is a carrier point and need not regenerate the common word,
the killed mover, or the pair atom.  In the inert arm the paid row shifts
losslessly, while every selected exact cap root at (U_n) is all Continue.
This is compatible with (W_n) having positive source-side defects, because
(W_n) is exact only over (E_n), not over (U_n).

Nor does the sum (R_n) yield a bounded-depth localization.  The word lengths
(h_n) may diverge, so a fixed total reached charge need not give one row of
fixed charge.  The pure-time paid-row decoder packages a player's cumulative
debt into one first-disagreement witness, but it does not turn the rows of
(W_n) into exact prescribed-payoff Bellman edges.  Therefore no existing
exact-path compiler consumes (18).

I tested the natural repair of fresh exactification on the source branch.  It
returns precisely to the normalized-passport descent-versus-inert boundary:
positive-absorption exact roots can lower real debt, while a unique
all-Continue cap correspondence blocks a restart.  The endpoint-side exact
word gives no lower-hemicontinuity or state-matching theorem for this new
source exactification.

A second tempting repair is to reuse the (R_n)-decoded response pair on the
exact endpoint branch and form a signed response rectangle.  This also lacks
one exact datum.  Realizing a source-branch cap defect uses a tail strategy
approaching the cap of the (X_n)-tail.  Endpoint-side exactness controls
root responses evaluated at the cap of the (E_n)-tail.  Those two tail
strategies and cap values need not agree.  Hence exactness over (E_n) does
not give the opposite sign for the same two behavioral responses decoded
from (R_n).  Reselecting an endpoint-optimal tail response destroys the
source equality which summed to (R_n).  Thus the common-response square
needed by the curvature/rectangle consumers is not produced by this account.

## 6. Reverse-chord tangent shortcut: unavailable at the checked interface

At the minimum endpoint limit (V), the killed mover satisfies (d_p(V)=0).
The reverse chord (V\to U) changes only (p)'s complete behavioral
strategy and creates positive (p)-debt.  This is a genuine inactive-support
entry direction.

It does not instantiate `QuittingPositiveMinimumDebtTangentFamily` directly.
That structure defines

```text
replacement :
  ∀ mover : {who // who ∈ quittingPositiveDebtSupport base}, ...
```

so replacement movers are indexed only by coordinates already active at the
minimum base.  Player (p) is not such a coordinate at (V).

There is no source-preserving reparametrization by an active mover in the
supplied data.  The literal profiles (U_n,V_n) differ only in (p)'s
strategy; changing an active player's strategy would be a different chord
with different opponents and cap provenance.  A generic tangent family can
be freshly extracted at (V), but its active-mover replacements need not
recover the reverse sibling chord or its common word.

One honest refinement is available.  Along the literal stopping-law segment
from (V) toward (U):

* if some nontrivial segment remains on the minimum fibre, its far endpoint
  has (p) active and the return to (V) gives the same half-chord support
  descent; while
* if every positive mixture leaves the minimum fibre, the chord is exactly an
  inactive-mover support-entry path not represented by the present tangent
  family.

The second arm has no checked consumer.  Calling it an active tangent by
relabeling the mover would lose literal source provenance.

## 7. Audit of the normalized-minimization split

The source note correctly distinguishes two levels:

1. the closed arbitrary-prefix normalized slice, whose minimizer is either
   off minimum with unique all Continue or has minimum-return actualizers;
2. the narrower event that those actualizers are produced by exact cap stacks
   over the killed endpoint.

Only level 2 supports the copied-sibling account above.  Exact-root
correspondences are closed but not lower hemicontinuous, so a minimum point in
the arbitrary-prefix closure cannot silently be replaced by a raw exact-stack
sequence.  The note explicitly preserves this restriction.

The claim that a fresh screened paid toggle can always rebase the normalized
slice should cite its exact hard-residual adapter in a future formal packet.
It is not used in equations (9)--(18), and I did not treat that local adapter
as part of the sibling-account proof.

## 8. Export verdict

The corrected trichotomy is mathematically sound after the minor limit
notation repair.  Its principal source-facing conclusion is now a strict
atlas reduction:

\[
\begin{array}{c}
\text{strict killed-mover endpoint}\\
\Longrightarrow\\
\text{off-minimum normalized-passport inert minimizer}\\
\quad\lor\quad
\text{existing concentrated singleton/collision consumer output}.
\end{array}
\]

When the minimum return is realized by exact cap stacks, the actual \(V_n\)
family directly supplies the packet.  The copied sibling \(U_n\) then gives
optional extra information: minimum-sibling support descent or strict reached
defect charge.  Failure to consume that extra charge does not reopen the
predecessor, because \(V_n\) has already entered the maintained packet nodes.

This corrected atlas contraction is **PASS for export** provided the packet:

* states the eventual reindexing and fixed routed label explicitly;
* returns a dependent wrapper if old strict-endpoint/word provenance must be
  available downstream;
* states the exact checked output (P2), not a terminal-equilibrium conclusion;
* records that a nonsingleton packet additionally reaches the existing
  three-role compiler because both whole-source and tail debts return to the
  minimum; and
* leaves the off-minimum unique-all-Continue normalized-passport node open.

The sibling-charge decoder should be included as a strengthening or retained
secondary theorem, but no claim should be made that it independently removes
the inert paid-cap branch.

## Checked declarations inspected

* `quittingTerminalSemanticDebt_prefix_eq_capDefect_add_continueMass_mul`,
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticOwnStrategyTransport.lean`;
* `QuittingTerminalSemanticPrefixChain.debt_zero_eq_sum_reached_defect_add_tail`,
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticDirectedTransport.lean`;
* `quittingTerminalSemanticDebt_prefix_eq_continueMass_mul_of_capNash`,
  `UniformEquilibrium/Diagnostics/Quitting/TerminalCapNashEndpointTransport.lean`;
* `sSup_range_pureTimeGain_eq_terminalDebt` and
  `exists_pureTimeGain_gt_individualValue_sub`,
  `Research/General/RandomDeviationAuditGame.lean`;
* `exists_quittingPaidFirstDisagreementRow_of_pureTimePayoff_sub`,
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPaidFirstDisagreement.lean`;
* `HasTerminalExploitabilityGap.exists_supported_pureTimePayoff_sub_at` and
  `HasTerminalExploitabilityGap.exists_paidFirstDisagreementRow_at`,
  `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/ActualProfileTerminalGapPaidCap.lean`;
* `QuittingPaidCapLiftedSource.exactTrichotomy`,
  `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/PaidCapPortExactTrichotomy.lean`;
* `QuittingActualProfileTerminalGapPaidCapPort.quantitativeDebtDescent_or_inertStall`,
  `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/ActualProfileTerminalGapPaidCap.lean`;
* `QuittingTerminalExploitabilityWitness.concentratedPacket_singletonStrategic_or_collisionMinimumResidual`,
  `Research/Quitting/ConcentratedSingleton/StrategicDispatch.lean`;
* `ConcentratedCollisionFourRole.packet_eventually_tailEscape_or_threeRoleTransfer`,
  `Research/Quitting/ConcentratedCollisionFourRoleMonodromy.lean`; and
* `QuittingPositiveMinimumDebtTangentFamily`,
  `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/PositiveMinimumDebtTangentFamily.lean`.
