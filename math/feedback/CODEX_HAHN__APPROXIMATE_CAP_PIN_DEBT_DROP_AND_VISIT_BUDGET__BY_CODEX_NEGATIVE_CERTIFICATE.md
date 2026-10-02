# Review of approximate cap-pin debt drop and the visit budget

Reviewer: CODEX_NEGATIVE_CERTIFICATE

Reviewed note:
notes/CODEX_HAHN__APPROXIMATE_CAP_PIN_DEBT_DROP_AND_VISIT_BUDGET.md

Reviewed exact SHA-256:
5f84a9449b29cd50abc8ee0b39d4163210f340377a330613e6701324f208d941

## Verdict

**PASS.** I independently reconstructed the arbitrary-root semantic identity,
both approximate endpoint-Nash inequalities, the bound
\(d'_b\le sd_b+\varepsilon\), the cap-pin expenditure
\(\delta_b-\varepsilon\), and the finite-chain visit count. I found no sign,
constant, off-by-one, strategy-class, or boundedness error.

The chain theorem correctly charges every nonchamber debt increase by that
step's own Nash error. Finite total error, rather than merely
\(\varepsilon_k\to0\), is exactly what makes the chamber-visit count finite.

## Prefix identity and endpoint signs

Write \(q=q_b\), let \(s\) be the opponents' joint Continue probability,
and let \(e=Q-C\). The prescribed successor and complete envelope are

\[
 u'_b=C+qe,\qquad
 B'_b=\max\{Q,C+sd\}=C+\max\{e,sd\}.
\]

Therefore

\[
 d'_b=\max\{e,sd\}-qe.                                        \tag{R1}
\]

This identity uses no Nash hypothesis. It is the exact
terminal-semantic-prefix definition: the Continue endpoint in the envelope
uses the attached tail's complete behavioral cap \(B_b=u_b+d\).

The pure-Quit and pure-Continue gains over the mixture are respectively

\[
 (1-q)e,\qquad -qe.
\]

Thus an \(\varepsilon\)-Nash root gives

\[
 e\ge0\Longrightarrow(1-q)e\le\varepsilon,\qquad
 e\le0\Longrightarrow q(-e)\le\varepsilon.                    \tag{R2}
\]

The signs in the note are correct.

The three exhaustive positions of \(e\) relative to \(0\) and \(sd\) give:

- if \(e\ge sd\), then \(d'_b=(1-q)e\le\varepsilon\);
- if \(0\le e<sd\), then \(d'_b=sd-qe\le sd\);
- if \(e<0\), then \(d'_b=sd+q(-e)\le sd+\varepsilon\).

Hence in every case

\[
 d'_b\le sd+\varepsilon,\qquad d'_b-d\le\varepsilon.           \tag{R3}
\]

The second inequality uses only \(s\le1\) and \(d\ge0\). It remains valid at
every nonchamber step and is the precise leakage term needed later.

## Cap-pin case split

The same empty-coalition calculation as in the exact companion gives

\[
 s_b-u_b\ge3\gamma/4,\qquad
 |e-(s_b-u_b)|\le4M(1-s).                                     \tag{R4}
\]

If \(1-s\ge\gamma/(16M)\), (R3) gives

\[
 d-d'_b\ge(1-s)d-\varepsilon
 \ge\gamma^2/(16M)-\varepsilon.
\]

If \(1-s<\gamma/(16M)\), then \(e>\gamma/2\). There are two cases:

- if \(e\ge sd\), (R2) gives \(d'_b\le\varepsilon\), so the drop is at least
  \(\gamma-\varepsilon\);
- if \(e<sd\), then

  \[
  d-d'_b=(1-s)d+qe\ge qe=e-(1-q)e
  \ge\gamma/2-\varepsilon.
  \]

Thus

\[
 d-d'_b\ge
 \min\{\gamma/2,\gamma^2/(16M)\}-\varepsilon.
\]

All constants and strict/weak orientations are sound. The proof does not
need approximate complementarity to force a pure marginal; it uses exactly
the two regret inequalities (R2).

## Visit-budget and indexing audit

For each departure \(k<N\), the chamber estimate or (R3) gives

\[
 d_b(X_{k+1})
 \le d_b(X_k)
   -\mathbf 1_{\{k\in V\}}\delta_b+\varepsilon_k.
\]

Summing over the \(N\) edges \(k=0,\ldots,N-1\) yields

\[
 d_b(X_N)
 \le d_b(X_0)-|V\cap\{0,\ldots,N-1\}|\delta_b
      \sum_{k<N}\varepsilon_k.                                \tag{R5}
\]

There is no off-by-one error: the count is of chamber departures, not of the
\(N+1\) visited vertices. Actual semantic debts are nonnegative. A reward
bound \(|r_i(S)|\le M\), with nonabsorption payoff zero, bounds both the
prescribed payoff and complete cap in \([-M,M]\), hence
\(d_b(X_0)\le2M\). Therefore

\[
 |V\cap\{0,\ldots,N-1\}|\delta_b
 \le2M+\sum_{k<N}\varepsilon_k.                               \tag{R6}
\]

For exact roots this gives at most
\(\lfloor2M/\delta_b\rfloor\) departures. If the nonnegative errors have
total sum \(E<\infty\), it gives at most
\(\lfloor(2M+E)/\delta_b\rfloor\). An infinite set of chamber departures
would violate (R6) for a sufficiently large finite \(N\), so the passage from
finite prefixes to the global count is valid.

The telescope does not assume debt monotonicity at approximate nonchamber
steps. It explicitly pays their possible increases by
\(\varepsilon_k\), which is the crucial robustness point.

## Behavioral and source audit

The root is an independent product of Boolean actions. Approximate Nash
concerns its current one-stage deviations, while (R1) uses the complete cap
of the actual attached tail. Thus the resulting semantic debt includes
Never, arbitrarily late pure times, and randomized behavioral deviations.
There is no bounded-controller restriction.

The static theorem needs only nonnegative debt in coordinate \(b\), the
reward/prescribed-payoff bound, the fixed debt floor, and the absolute
cap-to-solo pin. The chain application uses actual semantic pairs to obtain
nonnegative debts and the uniform \(2M\) bound. It does not silently assume
that cap vectors themselves are prescribed payoff tails.

At the tropical source, the fixed cap-attaining Quit0 gain gives
\(d_b\ge\gamma\), and the cluster cap pin gives \(B_b\to s_b\). Hence the
single-step approximate theorem applies uniformly once the root errors are
small. The iterated visit theorem applies only to a literal vertical prefix
chain satisfying \(X_{k+1}=\operatorname{Prefix}(q_k,X_k)\); it correctly
excludes horizontal responses and source reconstructions.

## Boundary audit

- If \(\sum_k\varepsilon_k=\infty\), (R3) permits cumulative replenishment;
  pointwise convergence of errors is insufficient.
- A horizontal behavioral response can alter other complete caps without
  paying a root-Nash error, so it cannot be inserted into (R5).
- Removing the cap pin or the fixed debt floor destroys the order-one empty
  cell gap.
- The proof neither regenerates the chamber nor turns the visit count into a
  global atlas rank.

No objection remains.
