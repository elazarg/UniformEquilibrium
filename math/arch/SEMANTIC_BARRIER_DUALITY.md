# Semantic Bellman and barrier duality

Let

\[
\mathcal Z_R=[-R,R]^I\times[-R,R]^I,
\qquad z=(u,b),
\]

and let \(T_x\) be the exact semantic prefix map

\[
T_x(u,b)_i
=
\left(
g_i(x)+c(x)u_i,\,
\max\{q_i(x),a_i(x)+\chi_i(x)b_i\}
\right).
\tag{1}
\]

Let

\[
e_\infty=(0,(r_i(\{i\})^+)_{i\in I})
\]

be the all-Continue boundary, and let \(\mathcal K_r\) be the terminal-semantic
carrier. Finite-word density says

\[
\mathcal K_r
=
\overline{\{T_we_\infty:w\text{ a finite word}\}}.
\tag{2}
\]

## 1. Prescribed-target Bellman equation

For a target \(v\), define

\[
\ell_v(u,b)
=
\max\left\{\|u-v\|_\infty,\max_i(b_i-u_i)\right\},
\]

and

\[
Q_v(z)
=
\inf_{w\in X^{<\omega}}\ell_v(T_wz),
\tag{3}
\]

where the empty word is allowed. Splitting finite words into the empty word
and a first root gives

\[
\boxed{
Q_v(z)
=
\min\left\{
\ell_v(z),
\inf_{x\in X}Q_v(T_xz)
\right\}.}
\tag{4}
\]

The inner operation is an infimum, not necessarily a minimum.

For every fixed finite word, \(z\mapsto\ell_v(T_wz)\) is continuous.
Therefore \(Q_v\), as a pointwise infimum of continuous functions, is bounded
and upper semicontinuous.

## 2. Function-barrier dual

Let \(q\) range over bounded upper-semicontinuous functions on \(\mathcal Z_R\)
satisfying

\[
q(z)\le\ell_v(z),
\qquad
q(z)\le q(T_xz)
\quad(z\in\mathcal Z_R,\ x\in X).
\tag{5}
\]

Iteration gives

\[
q(z)\le q(T_wz)\le\ell_v(T_wz),
\]

so \(q\le Q_v\). Conversely, equation (4) shows that \(Q_v\) itself satisfies
(5). Thus \(Q_v\) is the pointwise greatest feasible barrier and

\[
\boxed{
W_r(v)=Q_v(e_\infty)=\max_q q(e_\infty).}
\tag{6}
\]

For an arbitrary behavioral profile, choose finite Never-tail truncations
\(z_m=T_{w_m}e_\infty\to z_\sigma\). Monotonicity and upper
semicontinuity give

\[
q(e_\infty)
\le\limsup_m q(z_m)
\le q(z_\sigma)
\le\ell_v(z_\sigma).
\tag{7}
\]

This is why the dual uses upper, rather than lower, semicontinuity.

## 3. Target-free dual

Put

\[
d(u,b)=\max_i(b_i-u_i)
\]

and

\[
q_r^*(z)=\inf_{w\in X^{<\omega}}d(T_wz).
\tag{8}
\]

Then \(q_r^*\) is the greatest bounded upper-semicontinuous function
satisfying

\[
q\le d,
\qquad
q\le q\circ T_x
\quad(x\in X),
\]

and

\[
\boxed{
\eta(r)=q_r^*(e_\infty)
=
\max_q q(e_\infty).}
\tag{9}
\]

## 4. Closed invariant-set dual

The carrier \(\mathcal K_r\) is the smallest closed set containing
\(e_\infty\) and satisfying

\[
T_x(\mathcal K_r)\subseteq\mathcal K_r
\quad(x\in X).
\]

Indeed, every such set contains every finite-word orbit point and hence its
closure (2). Consequently

\[
\boxed{
\eta(r)
=
\max\left\{
\gamma:
\begin{array}{l}
\exists C\subseteq\mathcal Z_R\text{ closed},\
e_\infty\in C,\\
T_x(C)\subseteq C\ \forall x,\
d(z)\ge\gamma\ \forall z\in C
\end{array}
\right\}.}
\tag{10}
\]

The pair \((\eta(r),\mathcal K_r)\) attains this maximum.

## 5. Positive-gap decoding

Suppose a function or invariant-set certificate proves

\[
d(U(\sigma),B(\sigma))\ge\Gamma>0
\]

for every behavioral profile \(\sigma\). For each profile, some player has
debt at least \(\Gamma\). For every \(0<\gamma<\Gamma\), the definition of
that player's cap supplies an actual complete behavioral replacement with
gain at least \(\gamma\). The supremum need not be attained at
\(\gamma=\Gamma\); choosing \(\gamma=\Gamma/2\) is always valid.

For algebraic rewards, a semialgebraic invariant set or a suitably
upper-semicontinuous piecewise-polynomial barrier reduces soundness to
universal real-polynomial inequalities after splitting the finitely many max
branches.

## Scope

The canonical witnesses \(Q_v\), \(q_r^*\), and \(\mathcal K_r\) encode the
value itself. They prove logical completeness of the barrier language, not
that a finite, semialgebraic, or otherwise effective certificate always
exists. The four-player problem remains the sign question

\[
\eta(r)=0\quad\text{for every four-player table }r.
\]
