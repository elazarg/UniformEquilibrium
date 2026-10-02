# Review of signed source retraction and near-minimum response chord

Reviewer: PAIRED_HULL_REVIEW

Scope reviewed: Sections 11--12 of
[CODEX_DESCENDANT__PAID_CYCLE_FINITE_MEMORY_AND_SOURCE_REPROJECTION_OBSTRUCTION.md](../notes/CODEX_DESCENDANT__PAID_CYCLE_FINITE_MEMORY_AND_SOURCE_REPROJECTION_OBSTRUCTION.md).

## Verdict

**PASS as ordinary mathematics, with two bounded statement repairs.**

Proposition 11.1 has the correct orientation, exact debt telescope, and safe
constants. Theorem 12.1 also gives a genuine source-regenerated strict-support
child from a near-minimum exact full-response edge carrying a fixed target
atom. Consequently the near-minimum response-cycle arm is not a live
horizontal SCC: it enters the existing renewable support lane.

The two repairs are:

1. Theorem 12.1 must explicitly assume or carry the incoming Fin4 hard
   residual (equivalently an incoming complete FinFourMinimumAtomProducer)
   before claiming that its causalizations are complete same-residual
   producers. The chord mathematics itself needs only the positive global
   minimum, but that table-level residual field cannot be manufactured by
   causalization.
2. Corollary 12.2 should explicitly say that mover, selected cycle-edge type,
   terminal coalition, and every later compactification are fixed by one
   composed subsequence. Finiteness of the response alphabet, the \(1296\)
   cycle bound, and finiteness of the coalition set make this routine.

These are typing/quantifier repairs, not missing mathematical alternatives.

## 1. Four-step signed retraction

Write the coordinate-replacement path from source to cycle vertex as

\[
 S=Z^0\longrightarrow Z^1\longrightarrow\cdots\longrightarrow Z^4=X.
\]

If \(D(X)-D(S)=\delta>0\), telescoping gives an \(r<4\) with

\[
 D(Z^{r+1})-D(Z^r)\geq\delta/4.
\]

The note correctly reverses this edge: \(A=Z^{r+1}\) is the more
off-minimum endpoint and \(B=Z^r\) is one coordinate closer to \(S\). If
\(i\) is the replaced player and

\[
 g=U_i(B)-U_i(A),\qquad
 \Delta=D(A)-D(B),
\]

then own-cap invariance gives exactly

\[
 \Delta
 =g+\sum_{j\ne i}\bigl(d_j(A)-d_j(B)\bigr).
\tag{R.1}
\]

If \(g\geq\Delta/2\), then \(g\geq\delta/8\). Otherwise the three
nonmovers contribute more than \(\delta/8\), so one contributes at least
\(\delta/24\). Splitting

\[
 d_j(A)-d_j(B)
 =\bigl(B_j(A)-B_j(B)\bigr)
  +\bigl(U_j(B)-U_j(A)\bigr)
\]

then gives the stated \(\delta/48\) cap-fall or payoff-rise alternative.
No sign is reversed: \(A\to B\) is a literal retraction toward the source,
and positive \(g\) is a genuine payoff gain on that reverse edge.

The subsequential split in Corollary 11.2 is exhaustive. If
\(\limsup E_n>0\), choose \(E_n\geq\varepsilon\) and eventually
\(D(S_n)-D_*\leq\varepsilon/2\). Otherwise \(E_n\to0\). Finite label
selection fixes the retraction coordinate and one of the three outputs.

This is a strict advance over bare replacement ancestry. The paid-reverse
arm is a literal source-oriented unilateral edge from an endpoint with
\(D(A)\geq D_*+\delta/4\); pure-time disintegration may attach its actual
first-disagreement row. The nonmover arm remains only a signed semantic
externality and has no current chronological consumer.

## 2. Near-minimum full-response chord

Let \(Y_n\) install an exact unrestricted cap-attaining response for mover
\(i\) at source \(X_n\). Opponents are unchanged, so

\[
 B_i(Y_n)=B_i(X_n),\qquad
 U_i(Y_n)=B_i(X_n),\qquad
 d_i(Y_n)=0.
\tag{R.2}
\]

Mixing only \(i\)'s complete stopping law is an ordinary independent
behavioral strategy: against fixed opponents, the induced stopping-time law
is the corresponding convex mixture. Prescribed payoff and the complete
terminal law are affine. For a nonmover, every fixed unrestricted response
payoff is affine in this mixture and its supremum is convex; the mover cap is
constant. Thus

\[
 d_j(H_n^s)
 \leq(1-s)d_j(X_n)+s d_j(Y_n)
\]

for every player. The global lower bound and the two endpoint limits squeeze
the sum to \(D_*\). At one common compact limit, every coordinate slack is
nonnegative and their sum is zero, so all coordinate inequalities are
equalities. In particular,

\[
 d_i(y)=0,\qquad d_i(x)\geq g_0,\qquad
 d_i(h^s)=(1-s)d_i(x)>0.
\]

Every debt-positive coordinate of \(y\) is debt-positive in \(h^s\), while
\(i\) lies in the latter support and not the former. Since \(D_*>0\), the
child support is nonempty. This proves the strict inclusion and the Fin4
cardinality bound.

## 3. Atom, causalization, and copied prefix

The target's fixed \(K\)-stage atom survives with its full mass in \(Y_n\)
and with at least \(s\lambda\) in \(H_n^s\): on the component choosing the
target stopping law, opponents and the literal marked date are unchanged.
This statement concerns the actual moving dates, not merely a time-forgetting
limit law.

Once the incoming hard residual is made explicit, the supplied-family
source-faithful minimum causalization applies separately to the \(Y_n\) and
\(H_n^s\) families. It retains the supplied suffix profiles and marks while
choosing exact cap--Nash prefix words. Copying the word chosen for \(H_n^s\)
onto \(Y_n\) gives a literal common-prefix one-player edge. Joint survival
tends to one, hence every opponent-deleted survival does as well. The
reviewed complete-cap estimate then covers early Quit, arbitrary late clocks,
mixed clocks, and Never. The positive-minimum singleton moat selects the
tail-cap branch at both limiting minimum endpoints. No Nash property of the
copied word against \(Y_n\) is asserted or needed.

Thus the paired ancestry and regenerated strict-support child are sound.

## 4. Application to a pure-clock response cycle

Every cycle edge is an exact unrestricted behavioral best response with gain
at least \(D_*/4\), and its target mover debt is zero. In the near-minimum
arm both endpoints approach \(D_*\). A pure-clock target is either all Never
or terminates in one deterministic nonempty coalition at its earliest finite
date, with unconditional mass one. The all-Never case cannot occur
cofinally under the positive-minimum hard residual. Finite selection hence
fixes one mover, edge type, and nonempty coalition \(K\), with
\(g_0=D_*/4\) and \(\lambda=1\). Theorem 12.1 applies.

This materially contracts the paid-cycle question:

\[
 \text{uniformly off-minimum cycle}
 \Longrightarrow
 \begin{cases}
 \text{paid reverse source edge},\\
 \text{signed nonmover cap/payoff retraction},
 \end{cases}
\]

whereas a near-minimum cycle gives a regenerated strict-support child.
It does **not** by itself consume the downstream paid-cap trichotomy or the
ordinary tangent exits. Accordingly the sentence that “only the middle
output remains untyped for a terminal consumer” should be read narrowly as
a statement about entry into existing interfaces, not as a claim that the
other two outputs already yield a terminal uniform payoff.

## 5. Boundary checks

- Exact cap attainment is essential: an \(o(1)\)-best response would leave a
  residual mover debt and remove the strict zero used in the support drop.
- Both endpoint debts must tend to \(D_*\); one minimum endpoint and one
  off-minimum endpoint do not force coordinatewise affine equality.
- A positive limiting law atom alone is weaker than the supplied moving-date
  mass used here; the source-faithful causalization needs the latter data.
- The common prefix is a behavioral edge, not a Nash--Bellman temporal edge.
- The result is a one-use entry into the renewable support trace, not a rank
  on arbitrary outer-atlas returns.

With the two bounded repairs in the verdict, Sections 11--12 are sound and
genuinely reduce the exact paid-response-cycle residual.

## 6. Delta review: actual paid-row replacement of the signed externality

Candidate rechecked:
`/tmp/FIN4_SIGNED_SOURCE_RETRACTION_AND_NEAR_MINIMUM_RESPONSE_CYCLE_CONTRACTION.md`.
The bytes I reviewed had SHA-256
`7fb6a1f853bde2025c30fde9a140f2539d94121e77a215397bd4e8f9682c40d3`;
this differs from the earlier hash named in the review request, so any later
packaging edit should preserve or re-audit the argument below.

**Verdict: PASS for the strengthening.**  The former signed nonmover
cap/payoff output can indeed be replaced by an actual source-supported paid
first-disagreement row at the same literal retraction hybrid.

For the selected forward hybrid edge, put

\[
 \Delta=D(A)-D(B)\geq\delta/4,
 \qquad g=U_i(B)-U_i(A).
\]

Own-cap invariance gives

\[
 \Delta=g+\sum_{j\ne i}(d_j(A)-d_j(B)).
\]

If \(g<\Delta/2\), the three nonmovers contribute more than
\(\delta/8\), so one fixed \(j\ne i\) has

\[
 d_j(A)-d_j(B)\geq\delta/24.
\]

Debt nonnegativity at \(B\) therefore gives the literal source debt
\(d_j(A)\geq\delta/24\).  This is exactly the input, at the actual profile
\(A\), to
`positiveDebt_exists_actualJointReach_paidRow_mem_support`; there is no
carrier reselection and no change of opponents.  With
\(\rho=\delta/24\), its returned row has declared gain \(\rho/4=
\delta/96\), source witness in the actual stopping-law support, and the
three displayed own-survival, opponent-live, and joint-reach inequalities.

In the uniform cycle arm,
\(D(X_n)-D(S_n)\geq\varepsilon/2\).  Hence the selected edge has
\(\Delta\geq\varepsilon/8\).  The direct reverse gain is at least
\(\varepsilon/16\); otherwise one nonmover has debt at least
\(\varepsilon/48\), and applying the checked theorem with that smaller
fixed floor gives gain \(\varepsilon/192\) and exactly (6a)--(6b).
Finite player/output selection fixes the retraction mover and paid-row
observer on one subsequence.

This delta strengthens typing, not downstream consumption: the new row is a
literal chronological paid interface at a hybrid actual profile, but the
paid-cap/return waist is still open exactly as the candidate states.

### Final packet delta

I rechecked the final candidate at SHA-256
`49777d61b4bb486bd08f1e6b2b0680bf22898bd6f4bccab318d05bc56cfa23e9`.
The paid-row argument and constants are unchanged. The two presentation
repairs are now explicit: global indices satisfy (m_N=N+k_N\geq N), and
the regeneration order is (H_n^s\rightsquigarrow W_n), followed by
(P_n=W_n\star Y_n), followed by causalization of the supplied literal
(P_n) family at its shifted marks. The paired wrapper stores
(A_n=W_n\star H_n^s\to P_n) and the (P_n)-based child chronology.
**Final verdict: PASS.**

### Paid-row typing of the direct reverse-gain arm

I checked the final strengthening at SHA-256
`457b994ef4f7ace66865467f56e50a09e3bbb314e8ae7e3be779cc3bbdfc368f`.
It is valid. On the direct arm, own-cap invariance gives

\[
 d_i(A)=B_i(A)-U_i(A)=B_i(B)-U_i(A)
 \ge U_i(B)-U_i(A)=g.
\]

Thus (g\geq\delta/8) gives literal debt (d_i(A)\geq\delta/8) at
the same actual hybrid. Applying the checked actual-reach theorem there with
observer (i) produces a supported row of declared gain
(\delta/32). In the uniform cycle normalization
(\delta\geq\varepsilon/2), this is gain at least
(\varepsilon/64), with the stated (\varepsilon/16) debt/reach input.
Hence both uniform off-minimum outputs are now literal paid-row ports; no
externality-only output remains. **PASS remains final.**
