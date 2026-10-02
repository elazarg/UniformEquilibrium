# Review: minimum-floor repair to exact port and strict-curl no-go

Reviewer: `CODEX_DESCENDANT`

Date: 2026-08-31

Verdict: **PASS with minor exposition/API repairs.**  I found no
mathematical obstruction to the minimum-floor repair, its fixed paid-row
output, or the strict-port regression.  The result is a genuine reduction to
the existing summable exact-port waist, not a consumer of that waist.

## Claim checked

The note claims two things.

1. If actual Fin4 hard-residual profiles converge semantically to a positive
   global minimum, they can be made punishment-floor safe while retaining a
   fixed positive pure-time gap.  The only nontrivial case is a minimum with
   one positive debt coordinate; there a vanishing complete stopping-law
   mixture repairs the possible floor deficit.
2. A strict off-minimum response curl alone does not provide the same-profile
   punishment floor needed by the checked exact-port theorem.

Both claims survive review.

## 1. Minimum inequalities

At a positive global minimum, the checked singleton margin gives

\[
 B_i-r_i(\{i\})\ge D_*.
\]

Subtracting \(d_i=B_i-U_i\) gives

\[
 U_i-r_i(\{i\})\ge D_*-d_i=\sum_{k\ne i}d_k.
\]

Combining this with the hard residual's all-player punishment normality is
exactly enough to conclude \(\operatorname{Pun}_i\le U_i\).  If at least two
debt coordinates are positive, every right-hand side is strictly positive,
so semantic convergence gives an eventual same-profile punishment floor.
This part is correct.

## 2. Unique-debtor repair

Suppose \(d_p=D_*>0\) and all other limiting debts vanish.  For actual
approximants \(\sigma_n\), an \(\varepsilon_n\)-optimal pure stopping time
\(q_n^+\) satisfies

\[
 a_n:=V_p^n(q_n^+)-U_p^n\ge D_*/2
\]

eventually.  The deficit
\(f_n=(\operatorname{Pun}_p-U_p^n)_+\) tends to zero.  Mixing the complete
stopping law of \(p\) with the atom at \(q_n^+\), with weight
\(\theta_n=2f_n/a_n\) when \(f_n>0\), raises the prescribed payoff of \(p\)
by exactly \(2f_n\).  Thus it repairs the floor and \(\theta_n\to0\).

This must be understood as the canonical behavioral realization of the
convex mixture of the two complete stopping laws, not as pointwise mixing of
their hazards.  That realization is available as
`quittingStoppingLawMixtureBehaviorStrategy`; the terminal-law and payoff
affinity statements are checked in
`TerminalSemanticStoppingLawMixture.lean` and
`TerminalSemanticStoppingLawDebtConvexity.lean`.

For every other player, prescribed payoff changes by \(O(\theta_n)\), while
the limiting floor margin is at least \(D_*\).  Hence all other floors remain
safe eventually.  The stronger statement that the entire semantic pair is
retained is also valid, but should be justified explicitly:

* the mover's cap is unchanged because its opponents are unchanged;
* for a nonmover, every unilateral-deviation payoff changes by at most a
  reward-bound constant times \(\theta_n\), uniformly over the deviation;
  taking the supremum gives the same bound for its cap; and
* the complete terminal law is an exact convex mixture, so its total
  variation from the source law is at most \(\theta_n\).

The current note states semantic retention but only directly explains payoff
and law retention.  Adding the uniform cap argument would close this small
expository gap.

## 3. Fixed paid gap

The original stopping law of \(p\) averages the pure-time values, so one
supported time \(q_n^-\) has value at most \(U_p^n\).  Since the mixture
changes only \(p\)'s prescribed law, the opponents—and hence every pure-time
deviation value of \(p\)—are unchanged.  Therefore

\[
 V_p(q_n^+)-V_p(q_n^-)\ge a_n\ge D_*/2.
\]

`exists_quittingPaidFirstDisagreementRow_of_pureTimePayoff_sub` accepts both
finite times and `Never` and does not require the source witness to remain in
the support of the mixed prescribed law.  Thus any fixed smaller positive
gain gives the claimed literal paid row.  No cap attainment is assumed.

## 4. Exact-port invocation

`QuittingPaidRowFloorSafeSource.exists_markedExactOrbit_alternative_of_witness`
has precisely the needed same-profile hypotheses: an actual paid row and the
all-player punishment floor.  With a terminal exploitability witness it gives

\[
 \text{uniform payoff}
 \quad\lor\quad
 \text{summable all-Continue semantic port with positive paid-suffix reach}.
\]

The note states this conclusion accurately and does not mislabel the second
arm as a forward chronology or as AGKRS S.3 data.  Source attachment is
external provenance: the checked floor-safe structure itself does not store
the incoming minimum chronology.  The construction nevertheless keeps the
actual repaired profile literally as the orbit's suffix, so that distinction
does not invalidate the reduction.

## 5. Strict-curl regression

The four-player table in Section 6 checks out exactly.

* \(X\to E\) is an exact best response of player \(m\), of gain \(d\), since
  \(\ell\) quits surely at date zero.
* \(E\to Z\) is an exact best response of player \(o\), of gain one.
* The displayed common-response curl for \(o\) is one, and \(o\)'s debt at
  \(Z\) is zero.
* For player \(\ell\), a pure time \(q\) gives payoff
  \(1-\Pr(T=q)\), where \(T\) is the first opponent stopping time, including
  `Never`.  A probability law on the countably infinite set
  \(\mathbb N\cup\{\infty\}\) has atoms of arbitrarily small mass.  Hence
  every opponent profile gives cap one to \(\ell\), and therefore
  \(\operatorname{Pun}_\ell=1\).
* At both \(E\) and \(Z\), \(\ell\)'s prescribed payoff is zero.  Thus either
  literal paid edge can be based at a profile which fails the floor.

The example is correctly presented only as an interface regression; it has
no positive-global-minimum provenance and is not a counterexample to UE.

## Requested minor revisions

Before export or Lean handoff, I recommend only these local repairs.

1. State that the repair uses
   `quittingStoppingLawMixtureBehaviorStrategy`, rather than an informal
   pointwise behavioral mixture.
2. Add the uniform-over-deviations cap estimate establishing full semantic
   convergence of the repaired profiles, or weaken item 2 of the theorem to
   the payoff/law data actually needed by the exact port.
3. In the regression, say explicitly that both \(E\) and \(Z\) fail the
   \(\ell\)-floor; this makes the connection to either orientation of the
   paid-row decoder immediate.

These are not mathematical blockers.  The main result is suitable for a
Lean-facing packet after those clarifications, with the honest endpoint that
the summable outward port remains unconsumed.

## Checked source boundary

I inspected the exact statements and proof surfaces of:

* `minimumTerminalSemantic_singletonMargin`;
* the Fin4 hard residual's `all_punishmentNormal` field;
* `quittingStoppingLawMixtureBehaviorStrategy` and its stopping-law
  realization theorem;
* terminal-law/payoff affinity and cap convexity under complete stopping-law
  mixtures;
* `exists_quittingPaidFirstDisagreementRow_of_pureTimePayoff_sub`; and
* `QuittingPaidRowFloorSafeSource.exists_markedExactOrbit_alternative_of_witness`.

This review establishes ordinary mathematical soundness of the new adapter.
It does not assert that the adapter itself is already present as one compiled
Lean declaration.

## Addendum: actual-reach strengthening

I separately checked the later Section 3 strengthening against the scratch
declarations in `fable/lean/FableDebtActualReach.lean` and
`fable/lean/FableActualReachSupport.lean`.

At the repaired profile,

\[
 d_p(\widetilde\sigma_n)=d_p^n-\theta_na_n\longrightarrow D_*.
\]

Thus \(\Delta=D_*/2\) is below this debt eventually.  The scratch theorem
constructs a paid row of gain \(\Delta/4\), which is exactly

\[
 D_*/8.
\]

It also proves

\[
 \Delta^2\le 32M^2\,
 \Pr(\text{all players survive strictly before the row start}).
\]

Substituting \(\Delta=D_*/2\) gives the equivalent reach floor

\[
 \Pr(\text{joint entry at the row start})
 \ge {D_*^2\over128M^2}.
\]

So both constants in the revised note are correct.  The support wrapper also
genuinely selects its source witness in the support of the repaired player's
prescribed complete stopping law, and its proof establishes that the row
start is no later than that supported finite source time (with `Never`
handled separately).  This is compatible with the exact port: after the
summable outward prefixes, the positive prefix-survival limit multiplies the
fixed positive joint-entry floor of the unchanged paid suffix.

One qualification should remain explicit.  Support of the source pure time
does **not** give a uniform lower bound on its atom, nor does it ensure that
the opponents survive from the row start all the way to that source time.
Accordingly it supplies joint entry reach at the first-disagreement start,
not the later near-minimum/Nash cut required by a two-cut or AGKRS producer.
The note's statement that the later cut remains missing is therefore
correct.
