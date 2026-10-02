# Every Fin4 minimum tangent frontier has a quantitative paid port

Authors: `CODEX_DESCENDANT`

Independent reviews:
[`PAIRED_HULL_REVIEW`](../feedback/CODEX_DESCENDANT__EVERY_FIN4_TANGENT_FRONTIER_HAS_QUANTITATIVE_PAID_PORT__BY_PAIRED_HULL_REVIEW.md),
[`SOCIAL_WEIGHT_REVIEW`](../feedback/CODEX_DESCENDANT__EVERY_FIN4_TANGENT_FRONTIER_HAS_QUANTITATIVE_PAID_PORT__BY_SOCIAL_WEIGHT_REVIEW.md)

## Exact statement

Let \(I=\operatorname{Fin}4\), and let

\[
r:\{S\subseteq I:S\ne\varnothing\}\longrightarrow\mathbb R^I
\]

be a quitting-game reward table satisfying

\[
 |r_i(S)|\le M
 \qquad(i\in I,\ S\ne\varnothing)
\tag{1}
\]

for some \(M\ge0\).  For an actual behavioral profile \(\sigma\), write

\[
 U_i(\sigma)
\]

for its terminal payoff,

\[
 B_i(\sigma)=\sup_{\tau_i}U_i(\sigma[i\leftarrow\tau_i]),
 \qquad
 d_i(\sigma)=B_i(\sigma)-U_i(\sigma),
 \qquad
 D(\sigma)=\sum_{i\in I}d_i(\sigma),
\tag{2}
\]

where the supremum is over every unilateral behavioral strategy.

Fix

```text
frontier : QuittingPositiveMinimumDebtTangentFamily reward.
```

Let \(x=\texttt{frontier.base}\), and put

\[
 D_*=D(x)>0.
\tag{3}
\]

The frontier fields say that \(x\) lies in the terminal semantic carrier and
globally minimizes total unrestricted debt there.  Choose an arbitrary

```text
p : {who // who ∈ frontier.positiveDebtSupport}
```

and an arbitrary

```text
endpoint : FullReplacementCluster frontier p.
```

For each \(n\), define the literal actual target profile

\[
 Y_n=
 \texttt{frontier.fullReplacementProfile}\ p\
   (\texttt{endpoint.subseq}\ n),
\tag{4}
\]

and write \(y=\texttt{endpoint.cluster}\).

Then there are one fixed player \(j\ne p\) and one \(N\in\mathbb N\) such
that, for every \(n\ge N\), there exists

```text
row_n : QuittingPaidFirstDisagreementRow
          reward Y_n j (D_* / 16)
```

with all of the following properties.

First, the row's source witness is in the support of player \(j\)'s actual
complete stopping law in \(Y_n\).  Second, if
\(\operatorname{OwnSurvival}(row_n)\) is \(j\)'s survival to its start,
\(\operatorname{OppReach}(row_n)\) is the opponents' live mass there, and
\(\operatorname{JointReach}(row_n)\) is their product, then

\[
 \frac{D_*}{4}
 \le4M\,\operatorname{OwnSurvival}(row_n),
 \qquad
 \frac{D_*}{4}
 \le8M\,\operatorname{OppReach}(row_n),
\tag{5}
\]

and

\[
 \left(\frac{D_*}{4}\right)^2
 \le32M^2\,\operatorname{JointReach}(row_n).
\tag{6}
\]

Finally, every \(Y_n\) is definitionally a one-player complete-strategy
replacement of the retained actual source

```text
frontier.source (endpoint.subseq n)
```

by player \(p\), using the frontier's literal selected replacement strategy
at that same rank.  Thus the row family is attached to the supplied tangent
source; it is not selected on an unrelated realizer of \(y\).

The conclusion holds before inspecting whether the tangent family terminates
at positive total slope, flat support entry, or an off-minimum
full-replacement endpoint.

## Conjecture-facing change

This strictly narrows the maintained quantitative paid-port question.
The maintained renewable support trace lists three terminal row-producer
tags:

\[
 \text{positive slope},\qquad
 \text{flat support entry},\qquad
 \text{off-minimum paid endpoint}.
\]

The theorem proves that no case split is needed to reach the quantitative
paid-port waist.  Every tangent frontier, through any active mover and any
of its full-replacement clusters, already supplies a literal target row with
one fixed observer, a fixed gain \(D_*/16\), actual stopping-law support, and
the three reach floors (5)--(6).  Hence positive slope and flat support entry
are no longer separate paid-row producer obligations.

This does not consume the paid port.  The charged-return output of the
existing paid-cap trichotomy is terminally consumed, but its quantitative
debt-descent and exact all-Continue inert outputs remain open.  The existing
renewable minimum-fibre support descent also remains useful; the present
reduction shows only that every tangent frontier may instead be routed to the
same paid waist.

## Definitions and assumptions

At each live date the four players independently randomize between Continue
and Quit.  The public history before absorption records only the number of
past all-Continue stages, so an arbitrary behavioral strategy induces a
complete stopping law on

\[
 \overline{\mathbb N}=\mathbb N\cup\{\mathrm{Never}\}.
\]

The cap in (2) ranges over all such behavioral strategies, including Never,
arbitrarily late stopping, and randomized unbounded clocks.  No stationary,
finite-horizon, finite-memory, or cap-attainment restriction is imposed.

`FullReplacementCluster` retains a strict subsequence of the actual
full-replacement profiles and convergence of their complete semantic pairs.
It does not assert that the abstract cluster \(y\) is behaviorally attained.
All rows in the theorem live on the actual profiles \(Y_n\), not on \(y\).

The paid first-disagreement row compares two pure stopping times against the
same literal opponents.  Either stopping time may be Never.  Its source
witness is required to have positive mass in the observer's prescribed
stopping law, and (5)--(6) concern the actual prefix reach to the first
disagreement date.

## Proof

The endpoint cluster belongs to the same terminal semantic carrier on which
the frontier base is globally minimizing.  Therefore

\[
 D(y)\ge D_*.
\tag{7}
\]

For every full-replacement cluster, exact diagonal extraction makes the
mover's limiting debt vanish, independently of total slope and independently
of whether the endpoint remains on the minimum fibre:

\[
 d_p(y)=0.
\tag{8}
\]

All carrier debts are nonnegative.  Since Fin4 has exactly three nonmovers,
(7)--(8) give

\[
 \sum_{i\ne p}d_i(y)=D(y)\ge D_*.
\tag{9}
\]

Thus one fixed nonmover \(j\ne p\) satisfies

\[
 d_j(y)\ge\frac{D_*}{3}.
\tag{10}
\]

The endpoint field gives

\[
 \operatorname{Sem}(Y_n)\longrightarrow y.
\tag{11}
\]

Debt coordinates are continuous on the terminal semantic carrier.  From
(10)--(11), after some finite rank,

\[
 d_j(Y_n)\ge\frac{D_*}{4}.
\tag{12}
\]

Apply
`positiveDebt_exists_actualJointReach_paidRow_mem_support` to the literal
profile \(Y_n\), observer \(j\), reward bound \(M\), and

\[
 \Delta=\frac{D_*}{4}.
\]

The theorem accepts exactly the unrestricted debt lower bound (12).  It
returns a paid first-disagreement row of declared gain

\[
 \frac{\Delta}{4}=\frac{D_*}{16},
\]

retains the source witness in the support of \(j\)'s actual stopping law, and
gives

\[
 \Delta\le4M\,\operatorname{OwnSurvival},
 \quad
 \Delta\le8M\,\operatorname{OppReach},
 \quad
 \Delta^2\le32M^2\,\operatorname{JointReach}.
\]

These are (5)--(6).  The exact definition of
`frontier.fullReplacementProfile` gives the asserted one-player source
attachment.  This proves the theorem.

## Boundary tests

### Zero minimum

If \(D_*=0\), (9) yields no positive observer debt and the fixed row floor
vanishes.  The all-zero reward table is an exact regression: every debt is
zero, so no positive row can be inferred.  Positivity in (3) is essential.

### Minimum-fibre endpoint

If \(D(y)=D_*\), the three nonmovers still carry total debt \(D_*\), so the
proof and constants are unchanged.  The theorem does not turn the horizontal
full replacement into a temporal Nash--Bellman edge or contradict global
minimality.

### Strictly off-minimum endpoint

If \(D(y)>D_*\), the same lower bound applies.  The resulting paid row has
literal ancestry from the minimum source, but no signed path back to that
source is inferred.

### Endpoint support rotation

No relation between the positive-debt supports of \(x\) and \(y\) is used.
Even if the endpoint support is disjoint from the base support, (8)--(10)
select a nonmover debtor at the endpoint.  Thus support entry, support loss,
and support rotation do not create an omitted case.

## Source correspondence

The incoming tangent family and its base minimum are in
`UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/PositiveMinimumDebtTangentFamily.lean`.
The arbitrary-mover endpoint, its literal target profiles, their semantic
convergence, and the unconditional zero-mover identity are:

* `QuittingPositiveMinimumDebtTangentFamily.exists_fullReplacementEndpointCluster`;
* `FullReplacementCluster.fullReplacement_tendsto`; and
* `FullReplacementCluster.mover_debt_eq_zero`

in
`UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/MinimumFiberSupportDrop.lean`.

The complete behavioral localization, including stopping-law support and all
three reach inequalities, is
`positiveDebt_exists_actualJointReach_paidRow_mem_support` in
`UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/ActualReachPaidFirstDisagreement.lean`.

The reduced tangent exit list and its conditional consumers are in
`UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/FlatCirculationSupportRankElimination.lean`.
The general paid source, exact cap lift, and charged / quantitative / inert
trichotomy are in
`UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/PaidCapLiftedSummablePort.lean`
and
`UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/PaidCapPortExactTrichotomy.lean`.

The terminal exploitability gap already produces some paid row at every
actual profile through
`HasTerminalExploitabilityGap.exists_paidFirstDisagreementRow_at`.  That does
not duplicate the theorem here: it does not fix an observer from the
full-replacement cluster, place the row on this literal target subsequence,
or supply the quantitative own-, opponent-, and joint-reach floors.  The new
content is the composition of the unconditional zero-mover endpoint theorem,
Fin4 debt averaging, endpoint convergence, and the actual-reach row theorem.

No external paper result is used.

## Adapter and consumer

The arbitrary-data adapter is checked.  A positive global minimum produces a
`QuittingPositiveMinimumDebtTangentFamily` through
`nonempty_positiveMinimumDebtTangentFamily`.  Its positive-debt support is
nonempty, every active mover has a `FullReplacementCluster`, and the theorem
above produces the quantitative row on the literal cluster profiles.  No
additional source selection is required.

The immediate checked downstream interface is `QuittingPaidCapLiftedSource`.
Package one of the actual rows together with the retained global minimum,
construct its summable cap port, and apply
`QuittingPaidCapLiftedSource.exactTrichotomy`.  This gives exactly one of:

1. a cumulative charged admissible near-return, whose checked consumer gives
   a uniform-equilibrium payoff;
2. quantitative semantic-debt descent; or
3. literal all-Continue inert stall with the paid row shifted losslessly.

Only the first output is terminally consumed.  The packet strictly contracts
the tangent producer side into this already named waist; it does not solve
the remaining consumer side.

## Lean handoff

A narrow theorem can be added beside `FullReplacementCluster.mover_debt_eq_zero`:

```text
exists_eventually_quantitativePaidRow_at_fullReplacementCluster_finFour
```

Its inputs should be the reward bound, an arbitrary Fin4 frontier, an active
mover, and one supplied `FullReplacementCluster`.  Its output should fix one
nonmover observer and return an eventual family of
`QuittingPaidFirstDisagreementRow` objects with gain \(D_*/16\), source
support, and the three inequalities (5)--(6).

The proof should:

1. rewrite \(D_*\) as the base debt sum;
2. use `endpoint.cluster_mem` and `frontier.base_minimum` for (7);
3. use `endpoint.mover_debt_eq_zero` and four-player finite averaging for
   (10);
4. transport the safe \(D_*/4\) threshold through
   `endpoint.fullReplacement_tendsto`; and
5. apply `positiveDebt_exists_actualJointReach_paidRow_mem_support`.

Useful exact tests are a minimum-fibre endpoint, a strict off-minimum
endpoint, an endpoint whose support rotates away from the base support, and
the \(D_*=0\) all-zero boundary table.  The theorem must not require positive
total slope, flatness, support entry, a finite terminal atom, or cap
attainment.

## Scope and nonclaims

* The paid row is not a Nash--Bellman temporal edge.
* The full replacement is a horizontal strategy change, not a chronological
  successor.
* No positive absorption charge is extracted from the row.
* No charged return or payoff recurrence is produced.
* Quantitative debt descent is not made renewable.
* The inert all-Continue paid-cap branch is not excluded.
* No terminal approximate Nash profile, uniform-equilibrium payoff, or
  positive-gap counterexample is produced.

## Lean formalization record

This packet's original content is preserved above with pre-record SHA-256
`a6e20d336098a97c48d6f44ecf62b3c75b0a7bd0123aef1ff3b29f9fb808b74e`.
It was integrated at production commit
`a777a49684bf2ccb6bb41b48bf608605f9ed50c0`.

The final owner is
`UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/FullReplacementQuantitativePaidPort.lean`.
Its public surface is:

* `QuittingPositiveMinimumDebtTangentFamily.FinFourFullReplacementQuantitativePaidPort`,
  which stores the fixed nonmover, the limiting `D_*/3` debt floor, the
  eventual `D_*/4` debt floor, actual source-supported rows of gain `D_*/16`,
  and the exact `4M`, `8M`, and `32M²` reach inequalities;
* `QuittingPositiveMinimumDebtTangentFamily.fullReplacementProfile_subseq_eq_update`,
  which records the literal full-replacement update on the retained source
  subsequence;
* `QuittingPositiveMinimumDebtTangentFamily.nonempty_finFourFullReplacementQuantitativePaidPort`,
  which constructs the port from any supplied Fin4 tangent frontier, active
  mover, and full-replacement cluster; and
* `QuittingPositiveMinimumDebtTangentFamily.nonempty_finFourFullReplacementQuantitativePaidPort_of_positiveMinimum`,
  which selects the frontier, mover, cluster, and port from a supplied
  `HasPositiveMinimumTerminalSemanticDebt` witness.

Evidence seals are `M` and `L` for the full packet theorem.  The last theorem
provides branch-local `A` from the actual compact positive-minimum source
interface.  There is no downstream `C`: the paid rows are not consumed by a
return, descent, regeneration, renewal, terminal-approximation, or
uniform-equilibrium theorem.

The checked result makes no positive-slope, flat-support-entry, finite-atom,
cap-attainment, full-debt-residual, or minimum-fibre endpoint assumption.
It does not identify the horizontal full replacement as a chronological or
Nash--Bellman edge, select one row uniformly in rank, produce a charged
return, make debt descent renewable, exclude the all-Continue inert branch,
or prove a Nash profile, uniform-equilibrium payoff, or counterexample.  The
packet's boundary discussions are explanatory tests rather than separately
formalized regression declarations.
