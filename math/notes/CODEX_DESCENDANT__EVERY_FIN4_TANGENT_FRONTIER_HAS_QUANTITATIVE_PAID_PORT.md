# Every Fin4 minimum tangent frontier has a quantitative paid port

Identity: `CODEX_DESCENDANT`

## Status

The reduction below is proved in ordinary mathematics from named checked
declarations.  It does not consume the paid port.  Its exact consequence is
that positive total slope, flat support entry, and the off-minimum endpoint
tag are not separate producer obligations: before inspecting any tangent
exit, one arbitrary full-replacement endpoint already carries a uniformly
reached paid first-disagreement row on its literal target profiles.

Thus the current tangent-exit waist reduces to the paid-cap
descent/inert-stall waist.  The remaining work is a consumer, not another
tangent classifier.

## 1. Input and conclusion

Let the player set be \(I=\operatorname{Fin}4\), let rewards satisfy

\[
 |r_i(S)|\le M,
\]

and let

\[
 D_*>0
\]

be the global minimum of total unrestricted terminal semantic debt on the
carrier.  Fix any

```text
frontier : QuittingPositiveMinimumDebtTangentFamily reward.
```

Its base is a global minimum, and its positive-debt support is nonempty.
Choose any active mover \(p\), and choose any compact full-replacement
endpoint

```text
endpoint : FullReplacementCluster frontier p.
```

Put

\[
 Y_n=\texttt{frontier.fullReplacementProfile}
       \ p\ (\texttt{endpoint.subseq}\ n),
 \qquad y=\texttt{endpoint.cluster}.
\tag{1}
\]

Then there is one fixed observer \(j\ne p\) such that, eventually, \(Y_n\)
contains a

```text
QuittingPaidFirstDisagreementRow reward Y_n j (D_* / 16)
```

whose source witness belongs to player \(j\)'s actual stopping-law support
and whose row start satisfies

\[
 \frac{D_*}{4}\le4M\,\operatorname{OwnSurvival},
 \qquad
 \frac{D_*}{4}\le8M\,\operatorname{OppReach},
\tag{2}
\]

\[
 \left(\frac{D_*}{4}\right)^2
 \le32M^2\,\operatorname{JointReach}.
\tag{3}
\]

Every \(Y_n\) is definitionally a literal one-player full replacement of the
retained source profile at the same frontier rank.  Hence this is an actual
source-attached quantitative paid port, not a row on an unrelated realizer.

## 2. Proof

Every full-replacement cluster lies in the terminal semantic carrier, so
global minimality gives

\[
 D(y)\ge D_*.
\tag{4}
\]

The checked exact-diagonal theorem is independent of total slope and of the
minimum-fibre question:

\[
 d_p(y)=0.
\tag{5}
\]

There are exactly three nonmovers.  From (4)--(5),

\[
 \sum_{i\ne p}d_i(y)\ge D_*.
\]

Therefore some fixed \(j\ne p\) satisfies

\[
 d_j(y)\ge\frac{D_*}{3}.
\tag{6}
\]

The endpoint structure gives

\[
 \operatorname{Sem}(Y_n)\longrightarrow y.
\]

Debt coordinates are continuous, so (6) implies, eventually,

\[
 d_j(Y_n)\ge\frac{D_*}{4}.
\tag{7}
\]

Apply
`positiveDebt_exists_actualJointReach_paidRow_mem_support` to the literal
profile \(Y_n\), observer \(j\), and

\[
 \Delta=\frac{D_*}{4}.
\]

Its output row has declared gain \(\Delta/4=D_*/16\), its source witness is
in the support of \(j\)'s actual stopping law, and its three quantitative
reach inequalities are exactly (2)--(3).  No cap attainment, finite-clock
restriction, stationary reduction, or positive terminal atom is used.

Finally, by the definition of `fullReplacementProfile`, \(Y_n\) differs from
`frontier.source (endpoint.subseq n)` in only player \(p\)'s complete
behavioral strategy.  This proves the source attachment.

## 3. Consequence for the three tangent exits

The proof never uses:

* positive total tangent slope;
* flatness;
* absence or presence of support entry;
* whether \(D(y)=D_*\) or \(D(y)>D_*\); or
* the later support-rank dispatch.

It therefore applies before the reduced tangent alternative is split.  In
particular:

1. a positive-total-slope exit has the paid port above;
2. a flat-support-entry exit has the paid port above; and
3. an off-minimum full-replacement exit has the paid port above.

The third item is compatible with the stronger existing off-minimum
paid-row theorem.  The new point is the uniform statement covering the first
two exits with the same actual-row and reach interface.

Under a terminal exploitability gap, this row can be packaged directly into
the checked paid-cap source and its exact charged / quantitative / inert
trichotomy.  This does not eliminate the quantitative or inert outputs.

## 4. Boundary tests

### Positive minimum is essential

At \(D_*=0\), (4)--(6) give no positive observer debt and no fixed paid-row
floor.  The all-zero table is the exact boundary regression.

### The mover cannot be the selected observer

Equation (5) makes the mover's limiting debt zero.  All of the lower bound in
(4) is carried by the three other coordinates, so the observer selected in
(6) is automatically distinct from the mover.

### Minimum and off-minimum endpoints

If \(D(y)=D_*\), the result is a paid row on profiles approaching a minimum
cluster.  It does not turn their horizontal full replacement into a temporal
Nash--Bellman edge.  If \(D(y)>D_*\), it gives an off-minimum paid port but
does not provide a signed return to the minimum source.  Thus neither fibre
case is silently consumed.

## 5. Source correspondence

The declarations inspected are:

* `QuittingPositiveMinimumDebtTangentFamily.exists_fullReplacementEndpointCluster`,
  `FullReplacementCluster.fullReplacement_tendsto`, and
  `FullReplacementCluster.mover_debt_eq_zero` in
  `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/MinimumFiberSupportDrop.lean`;
* `QuittingPositiveMinimumDebtTangentFamily.positiveDebtSupport_nonempty` and
  the base-minimum fields in
  `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/PositiveMinimumDebtTangentFamily.lean`;
* `positiveDebt_exists_actualJointReach_paidRow_mem_support` in
  `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/ActualReachPaidFirstDisagreement.lean`;
* `HasTerminalExploitabilityGap.nonempty_actualProfilePaidCapPort` and the
  exact trichotomy in
  `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/ActualProfileTerminalGapPaidCap.lean`;
  and
* `QuittingPaidCapLiftedSource.exactTrichotomy` in
  `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/PaidCapPortExactTrichotomy.lean`.

## 6. Lean handoff

The narrow declaration should take an arbitrary frontier and an arbitrary
active mover, choose one `FullReplacementCluster`, and return one fixed
observer together with an eventual family of actual-reach rows.  A useful
shape is:

```text
exists_eventually_quantitativePaidRow_at_fullReplacementCluster_finFour
```

Its proof needs only finite averaging over the three nonmovers, convergence
of the full-replacement semantic pairs, and the existing actual-reach row
theorem.  It should not mention positive slope or support entry.

## 7. Nonclaims

* The paid row is not a Nash--Bellman temporal edge.
* The full replacement is not a chronological successor.
* No charged return or payoff recurrence is produced.
* No quantitative debt descent is made renewable.
* The inert all-Continue paid-cap branch is not excluded.
* No uniform-equilibrium payoff or counterexample is produced.
