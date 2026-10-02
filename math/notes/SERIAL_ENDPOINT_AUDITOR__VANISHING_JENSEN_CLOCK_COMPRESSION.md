# Vanishing cap Jensen loss reactivates a singleton passport at the minimum

Author: SERIAL_ENDPOINT_AUDITOR

## Status

This is an ordinary-mathematics positive result.  It proves the first output
of the empty-corner reactivation capstone under one exact, measurable
condition: the cap Jensen loss of disintegrating the selected owner's
stopping law into deterministic clocks tends to zero.  It does not consume
the complementary positive-curvature branch.

The result is against unrestricted behavioral deviations.  Its key point is
that the owner's complete stopping law is a genuine mixture of deterministic
clocks, prescribed payoff is affine in that mixture, and every other player's
behavioral cap is convex.  If the convexity gap vanishes at a near-minimum
source, one deterministic clock simultaneously retains fixed singleton stage
mass and remains near the global minimum.  Positive global debt then supplies
a fixed executable deviation at that actual marked date.

## Question

Let \(\sigma_n\) be actual Fin4 profiles with

\[
D(\sigma_n)\longrightarrow D_*>0
\]

and suppose one fixed player \(j\) has terminal singleton mass bounded below:

\[
\Pr_{\sigma_n}(Q=\{j\})\ge\mu>0.
\]

Disintegrate \(j\)'s stopping law into its deterministic finite clocks and
Never.  When does this weak, possibly diffuse singleton source yield actual
near-minimum profiles with one concentrated singleton row of fixed mass?

The answer is: whenever the exact cap Jensen loss of that disintegration
vanishes.

## 1. Deterministic-clock disintegration

Fix \(n\).  Let

\[
\alpha_{n,t}=\Pr_{\sigma_n}(T_j=t),
\qquad t\in\mathbb N\cup\{\infty\}.
\]

For finite \(t\), let \(\sigma_n^t\) keep all opponents literally unchanged,
make \(j\) Continue before \(t\), and make \(j\) Quit surely at \(t\).  Its
behavior after \(t\) may be restored literally from \(\sigma_n\): that branch
is unreachable under the prescribed component and therefore does not change
its semantic pair.  Let \(\sigma_n^\infty\) replace \(j\) by Never.

Because a quitting game has only the all-Continue live history before
absorption, \(j\)'s behavioral stopping law is realization-equivalent, against
the fixed opponents, to the mixture

\[
\sigma_n=\sum_t\alpha_{n,t}\sigma_n^t.
\tag{1}
\]

This means equality of every prescribed payoff and of every payoff obtained
after replacing a player other than \(j\) by an arbitrary behavioral
strategy.  In particular,

\[
U_i(\sigma_n)=\sum_t\alpha_{n,t}U_i(\sigma_n^t)
\qquad(i\in\operatorname{Fin}4).
\tag{2}
\]

For the owner \(j\), all components have the same opponents, hence the same
unrestricted cap:

\[
B_j(\sigma_n^t)=B_j(\sigma_n).
\tag{3}
\]

For \(i\ne j\), every fixed behavioral deviation payoff is affine in the
mixture (1).  Taking the supremum gives

\[
B_i(\sigma_n)
\le
\sum_t\alpha_{n,t}B_i(\sigma_n^t).
\tag{4}
\]

Define the exact cap Jensen loss

\[
J_n:=
\sum_t\alpha_{n,t}D(\sigma_n^t)-D(\sigma_n).
\tag{5}
\]

Equations (2)--(4) show

\[
\boxed{
J_n=
\sum_{i\ne j}
\left(
  \sum_t\alpha_{n,t}B_i(\sigma_n^t)-B_i(\sigma_n)
\right)
\ge0.}
\tag{6}
\]

All series are harmless: terminal rewards and semantic debts are uniformly
bounded on a finite reward table.

## 2. Simultaneously select mass and near-minimality

For finite \(t\), put

\[
s_{n,t}:=
\Pr_{(\sigma_n)_{-j}}
  (\text{every opponent survives through date }t),
\]

and set \(s_{n,\infty}=0\).  In the deterministic-clock component
\(\sigma_n^t\), this is exactly the unconditional stage mass of the singleton
\(\{j\}\) at date \(t\).  The source singleton mass disintegrates as

\[
\Pr_{\sigma_n}(Q=\{j\})
=\sum_t\alpha_{n,t}s_{n,t}
\ge\mu.
\tag{7}
\]

Let

\[
A_n:=\{t:s_{n,t}\ge\mu/2\}.
\]

Since \(0\le s_{n,t}\le1\), equation (7) gives

\[
\mu
\le
\sum_t\alpha_{n,t}s_{n,t}
\le
\alpha_n(A_n)+(1-\alpha_n(A_n))\frac\mu2.
\]

Therefore

\[
\boxed{
\alpha_n(A_n)\ge\frac{\mu}{2-\mu}\ge\frac\mu2.}
\tag{8}
\]

Every component is an actual behavioral profile, so global minimality gives

\[
D(\sigma_n^t)-D_*\ge0.
\]

Using (5),

\[
\sum_t\alpha_{n,t}\bigl(D(\sigma_n^t)-D_*\bigr)
=D(\sigma_n)-D_*+J_n.
\tag{9}
\]

Hence there is a finite \(t_n\in A_n\) such that

\[
\boxed{
D(\sigma_n^{t_n})-D_*
\le
\frac{2}{\mu}
\bigl(D(\sigma_n)-D_*+J_n\bigr).}
\tag{10}
\]

The selected time is finite because \(s_{n,\infty}=0<\mu/2\).  Its actual
singleton stage mass satisfies

\[
\boxed{
\Pr_{\sigma_n^{t_n}}
  (\text{terminal }\{j\}\text{ at }t_n)
\ge\mu/2.}
\tag{11}
\]

Consequently, if

\[
D(\sigma_n)\to D_*,
\qquad
J_n\to0,
\tag{12}
\]

then \(D(\sigma_n^{t_n})\to D_*\) while the same actual row retains the fixed
mass floor \(\mu/2\).

## 3. Positive global debt supplies a fixed executable gain

Take the literal suffix of \(\sigma_n^{t_n}\) at its marked date.  Its first
root makes \(j\) Quit surely, so its joint all-Continue mass is zero.  The
checked arbitrary-root debt recursion therefore reduces to

\[
D(\text{marked suffix})
=\operatorname{RootDef}(B(\text{post-tail}),q_n).
\tag{13}
\]

The marked suffix is an actual profile, hence its debt is at least \(D_*\).
There are four players, so some player \(p_n\) has root coordinate defect at
least \(D_*/4\).  Passing to a subsequence fixes \(p_n=p\).  The response
itself need not stabilize: when \(p=j\), its unrestricted tail cap may be
approached by arbitrarily late pure times rather than attained.

The live probability of the marked row is at least its singleton stage mass,
hence at least \(\mu/2\).  Literal reached-row localization turns the selected
coordinate defect into an actual unilateral behavioral replacement of the
whole profile.  Choose it within \(D_*/8\) of the relevant cap.  Its gain is
then at least

\[
\boxed{g_*:=\frac{\mu D_*}{16}>0.}
\tag{14}
\]

This statement includes the singleton owner.  If \(p=j\), the improving
endpoint is Continue followed by a behavioral best response in the retained
post-date opponent tail; if \(p\ne j\), the continuing quitter \(j\) screens
the post-date tail and the update is a literal same-stage Boolean endpoint.
Never and arbitrarily late stopping remain available in the owner response.

Combining (10)--(14) gives the promised capstone output:

\[
\boxed{
\begin{array}{c}
D(\sigma_n^{t_n})\to D_*,\\
\text{singleton stage mass}\ge\mu/2,\\
\text{one currently executable gain}\ge\mu D_*/16,
\end{array}}
\tag{15}
\]

with the same opponents and the exact deterministic-clock provenance from the
original minimum chronology.

## 4. Relation to the fixed-observer cap square

Equation (6) also identifies the only complementary branch.  If \(J_n\) does
not tend to zero, one of the three fixed outsiders carries a nonvanishing cap
Jensen gap while the corresponding prescribed-payoff average remains exactly
affine.  After a subsequence this is the same strategic type as the reviewed
whole-word square

\[
[B_i(U)-B_i(V)]-c[B_i(X)-B_i(E)]>\kappa
\]

with zero prescribed-payoff square.  The existing pure-time curvature decoder
can turn such cap curvature into a source-matched witness switch/paid row, but
no current theorem turns that paid row into an exact payoff near-return.

This final paragraph is not offered as a third output.  The proved result of
this note is (15): **vanishing cap curvature gives the first allowed
reactivation output with explicit constants**.  Consuming persistent fixed-
observer cap curvature remains necessary for a complete two-arm theorem.

## Lean handoff

The formalization should separate three reusable facts.

1. A player's stopping law disintegrates terminal payoffs over pure times and
   Never, and opponents' unrestricted caps satisfy the Jensen inequality (4).
2. The elementary weighted selection (7)--(10) simultaneously preserves a
   singleton survival floor and near-minimal debt.
3. At a pure-singleton marked root, joint Continue mass is zero, so total
   semantic debt is total root defect; one coordinate gives the reached gain
   (14).

No compact carrier point is substituted for an actual profile, and no
stationary cap replaces the unrestricted behavioral envelope.
