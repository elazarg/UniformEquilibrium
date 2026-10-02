# Review of the two-block full-debt fork seam

Reviewer: PAIRED_HULL_REVIEW  
Date: 2026-08-31  
Verdict: **REVISE — the exact seam and regression are sound, with two
bounded statement repairs**

## Claim checked

The note tests whether the strongest actual-reach full-debt response fork can
be iterated through literal exact cap--Nash prefixes. It claims:

1. an old exact root pays an explicit Nash seam when a mixed binding player's
   continuation cap rises;
2. a fresh uniquely-all-Continue exactification preserves literal ancestry
   but contributes zero exact-root charge;
3. a second profitable response remains horizontal rather than becoming a
   second Nash--Bellman block; and
4. an exact four-player \(D_*=0\) table realizes two such source-compatible
   responses while every fresh target root is uniquely all Continue.

The mathematical core survives. The note should not yet be exported because
Section 3 omits a survival hypothesis and conflates pointwise positive
absorption with the quantitative charged sequence arm.

## 1. Exact cap seam: PASS

With

\[
 E_j(b,x)=Q_j(x_{-j})-C_j(x_{-j};b_j),
 \qquad
 H_j(x)=\prod_{k\ne j}x_k(C),
\]

the tail-cap dependence is exactly

\[
 E_j(b',x)=E_j(b,x)-H_j(x)(b'_j-b_j).
\]

The coordinate defect formula

\[
 \delta_j(b,x)
 =x_j(C)(E_j(b,x))_+
  +x_j(Q)(-E_j(b,x))_+
\]

has the stated orientation. If the old root mixes \(j\), exactness forces
\(E_j(b,x)=0\). A positive cap rise \(\Delta_j\) therefore gives

\[
 \delta_j(b',x)=x_j(Q)H_j(x)\Delta_j.
\]

The pure-Quit formula and the stability of a pure-Continue coordinate under
a nonnegative cap rise are also correct. The formula is coordinatewise:
other cap changes do not enter player \(j\)'s root comparison.

## 2. Literal successor and horizontal typing: PASS

For

\[
 \widehat X=p\star X,\qquad \widehat Y=p\star Y,
\]

the literal suffix after the displayed root of \(\widehat Y\) is \(Y\).
Keeping the old root is exact precisely when all new coordinate root defects
vanish against \(B(Y)\). A second application of the actual-reach fork
theorem returns another unilateral comparison of complete profiles; it does
not make that comparison a root--successor edge.

The distinction between a paid first-disagreement row and a literal
positive prescribed-row packet is essential and correctly stated. A
counterfactual pure-time comparison does not prove that the prescribed
profile plays the worse action at the marked row, so the identity

\[
 \mathrm{gain}=\mathrm{liveMass}\cdot\mathrm{rowDefect}
\]

cannot be invoked without the additional literal-endpoint hypothesis.

The radial-fork discussion is also sound. A full best response may kill the
mover debt. A sufficiently small partial mixture preserves full debt by
continuity, but generally leaves a positive prescribed marked-row defect.
That defect is horizontal source data, not exact chronological charge.

## 3. Required repair: positive survival in (3.2)

The statement

\[
 d_i(p\star Y)=s(p)d_i(Y)>0
\]

does not follow from “\(Y\) is full debt” alone. One must also know

\[
 s(p)>0.
\]

A root with a sure quitter has \(s(p)=0\) and kills every prefixed debt
coordinate even when every \(d_i(Y)\) is positive.

There are two honest repairs.

1. Add \(s(p)>0\) to the local statement.
2. In the intended positive-global-minimum setting, derive it after proving
   that \(p\) is exact against \(B(Y)\):

   \[
   D_*\le D(p\star Y)=s(p)D(Y).
   \]

   Since \(D_*>0\), this forces \(s(p)>0\).

The second repair is preferable because it records exactly where positive
global-minimum provenance is used. It must not be imported into the
\(D_*=0\) regression.

## 4. Required repair: pointwise absorption is not the charged sequence arm

Section 3 says that if fresh exactification at \(B(Y)\) has positive
absorption, it is “the already routed charged arm.” Pointwise positivity is
not enough for that sequence-level conclusion. Along source approximants the
maximum exact-root absorption may be positive at every rank and still tend
to zero.

The correct split is:

- a cofinal uniform positive lower bound gives the quantitative charged arm;
- absorption tending to zero enters the checked vanishing-response
  maximal-root/reset/off-minimum reduction; and
- exact zero at one target means the only product root is all Continue.

The note's zero-charge conclusion remains valid in the last case. Replace the
one sentence so it does not silently consume the vanishing-positive branch.

## 5. Unique all-Continue and zero-charge extension: PASS

If all Continue is the unique exact root at \(B(Y)\), prefixing it has:

- literal successor \(Y\);
- unchanged prescribed payoff;
- cap
  \(\max\{r_i(\{i\}),B_i(Y)\}=B_i(Y)\), since exactness supplies the
  singleton inequalities; and
- zero absorption.

Iteration therefore gives arbitrarily many literal exact rows but zero total
exact charge. Shifting the horizontal response behind these rows preserves
ancestry and does not turn it into a Nash--Bellman edge. This is precisely the
zero-charge barrier claimed by the note.

## 6. Four-player regression: PASS

The reward table calculations are exact.

For \(X_0\), immediate all-player quitting at date one gives

\[
 U(X_0)=0,\qquad B(X_0)=(1,1,1,1).
\]

After player \(i\) Continues with probability \(\lambda\),

\[
 U(X_1)=(\lambda,0,0,0),\qquad
 B(X_1)=(1,1+\lambda,1,1),
\]

so

\[
 d(X_1)=(1-\lambda,1+\lambda,1,1),\qquad D(X_1)=4.
\]

The literal marked-row defect of \(i\) is \(1-\lambda\). After player \(k\)
is changed similarly,

\[
 U(X_2)=(\lambda,0,\theta,0),
\]

\[
 B(X_2)=(1,1+\lambda,1,1+\theta),
\]

and

\[
 d(X_2)=(1-\lambda,1+\lambda,1-\theta,1+\theta).
\]

Thus both moves have unit source reach, positive gain, conservative aggregate
debt transfer, and literal target-to-next-source compatibility.

At either target cap, movers \(i,k\) get zero from Quit and one from
Continue against every opponent root, including the all-Continue
continuation. Spectators \(j,\ell\) get zero from Quit and at least one from
Continue on opponent absorption, with a positive displayed continuation cap
at all Continue. Continue therefore strictly dominates for all four players,
so all Continue is the unique exact product root.

At all Never, every solo payoff is zero and every cap is zero. Hence the
global minimum is indeed \(D_*=0\). The example is an exact regression
against a purely local two-fork implication, not a candidate counterexample.

## 7. Packaging correction

The note contains visibly damaged inline mathematics and one malformed
qquad in (4.4). These are not mathematical gaps, but they must be repaired
before any gate. The final version should use normal Markdown/LaTeX
delimiters consistently.

## Disposition

After adding positive survival or deriving it from \(D_*>0\), and after
separating uniformly charged fresh roots from vanishing-positive roots, the
note is a sound and useful Priority-1 no-go:

\[
\text{two actual profitable forks}
\not\Longrightarrow
\text{two positive exact chronological blocks}.
\]

It isolates the first retained-root seam and shows that fresh all-Continue
exactification preserves ancestry only by spending zero charge. It does not
consume the full-debt chamber; the remaining theorem must use positive
global-minimum provenance to charge/eliminate the seam or must change the
root--tail fibre while retaining actual reach.

## Delta review of Section 7: two consecutive full responses

Date: 2026-08-31  
Delta verdict: **REVISE — the literal two-response construction is sound;
the advertised fixed leakage and regenerated-source conclusion need one
explicit argument/hypothesis each**

### Literal target-to-next-source typing: PASS

After selecting the first minimum cluster on one subsequence, the second
responses are taken against the literal opponents of (X_n^1). Thus
(X_n^1) is definitionally the second source, not merely another realizer of
(x^1). Compactifying (X_n^2) along a further subsequence preserves the
same (x^0,x^1) limits and both response sequences. No horizontal response
is called a Nash--Bellman row.

The debt floors are correct. A stabilized maximum-debt player (p) at
(x^0) has (d_p(x^0)\ge D_*/4). At a minimum first target,
(d_p(x^1)=0), so some (q\ne p) has

\[
d_q(x^1)\ge D_*/3.
\]

An (o(1))-best response by (q) gives (d_q(x^2)=0) at every selected
target cluster. If also (d_p(x^2)=0), the positive-debt support has
cardinality at most two. This is a genuine strict support comparison with
the full support of (x^0).

### Exact reactivation identity: PASS

When (r=d_p(x^2)>0),

\[
r=(B_p(x^2)-B_p(x^1))+(U_p(x^1)-U_p(x^2))
\]

follows exactly from (d_p(x^1)=0). The two half-size alternatives are
correct. In the cap arm, a response asymptotically optimal against the
literal (X_n^2) opponents earns the displayed cap difference relative to
the same response against the (X_n^1) opponents. In the payoff arm, finite
terminal-law expansion gives one signed label. Since the Never reward is
zero, the positive label can in fact be chosen nonempty.

### The (D_*/12) leakage floor is not currently proved in the note

The present text only gives (r/2) and (r/32). The reactivated debt (r>0)
need not itself have a uniform lower bound. Therefore a claim of a
(D_*/12) reactivation floor would be unsupported.

There is, however, a short stronger aggregate repair. Minimum-fibre equality
and the killed (q)-debt give

\[
\sum_{i\ne q}\bigl(d_i(x^2)-d_i(x^1)\bigr)=d_q(x^1)\ge D_*/3.
\]

Among the three nonmovers, one fixed (i\ne q) therefore satisfies

\[
d_i(x^2)-d_i(x^1)\ge D_*/9,
\]

and hence certainly the advertised weaker (D_*/12) floor. Splitting this
debt rise gives either

\[
B_i(x^2)-B_i(x^1)\ge D_*/18
\]

or

\[
U_i(x^1)-U_i(x^2)\ge D_*/18.
\]

The second arm yields a fixed nonempty terminal label with signed contribution
at least (D_*/288) (sixteen labels including Never; the Never contribution
is zero). If the author prefers the round (D_*/12) leakage floor, the
corresponding weaker cap and label constants are (D_*/24) and
(D_*/384). This aggregate account is the correct source of a uniform
certificate; it is not the possibly tiny (p)-reactivation (r).

### Source regeneration needs its missing entrance hypothesis

The support-(le2) conclusion is valid from the hypotheses stated in Section
7. The further sentence that the existing minimum-source regeneration step
applies is not valid from those hypotheses alone. Regeneration needs the
Fin4 hard-residual/global-source input which supplies a positive finite atom
at the selected joint-law minimum, followed by causalization of the same
(X_n^2) subsequence. Section 7 should either add this hypothesis and name
that adapter, or stop at the attained joint-law minimum cluster and its
literal response ancestry.

The two response passports can remain external provenance through that
causalization, but the bare regenerated minimum-source record does not by
itself encode the two horizontal edges. This distinction should be explicit.

### Wide chamber: PASS conditionally on the ratio theorem

Once the independently reviewed debt-ratio contraction is available, a
minimum-fibre second target indeed lies outside
(eta<D_*<2eta); Theorem A also excludes (D_*=\eta). Hence the surviving
minimum-return case is in (D_*\ge2eta). This is a dependency on that
ordinary-mathematics theorem until its Lean integration, not an internal
consequence of the two-response argument.

### Final delta disposition

The four-profile/same-subsequence construction is a real source-compatibility
advance. After adding the aggregate leakage identity and either adding the
hard-residual atom hypothesis or weakening the regeneration sentence, the
section gives the exhaustive honest output

\[
\text{off-minimum paid exit}
\quad\lor\quad
\text{two-zero support-}\le2\text{ cluster}
\quad\lor\quad
\text{fixed cap-switch or signed-law certificate}.
\]

None of the last two certificates is yet a chronological return or a terminal
consumer.
