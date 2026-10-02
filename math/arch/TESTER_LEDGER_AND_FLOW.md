# Exact tester ledger and occupation flow

Fix a finite nonempty player set \(I\), a quitting reward table \(r\), and

\[
R=\max_{\varnothing\ne S\subseteq I}\max_{i\in I}|r_i(S)|.
\]

Let \(X=[0,1]^I\) be the product-root space. For \(x\in X\), define

\[
p_x(S)=\prod_{j\in S}x_j\prod_{j\notin S}(1-x_j),
\qquad
c(x)=p_x(\varnothing).
\]

For each player \(i\), let

\[
p_x^{-i}(A)
=
\prod_{j\in A}x_j
\prod_{\substack{j\notin A\\j\ne i}}(1-x_j),
\qquad
\chi_i(x)=p_x^{-i}(\varnothing),
\]

and put

\[
g_k(x)=
\sum_{\varnothing\ne S\subseteq I}p_x(S)r_k(S),
\tag{1}
\]

\[
q_i(x)=
\sum_{A\subseteq I\setminus\{i\}}
p_x^{-i}(A)r_i(A\cup\{i\}),
\tag{2}
\]

\[
a_i(x)=
\sum_{\varnothing\ne A\subseteq I\setminus\{i\}}
p_x^{-i}(A)r_i(A).
\tag{3}
\]

Thus \(g_k\) is the prescribed absorbing contribution, \(q_i\) is player
\(i\)'s payoff from Quitting now, and

\[
a_i(x)+\chi_i(x)w
\]

is its payoff from Continuing now with continuation value \(w\).

## 1. Finite-dimensional chronological ledger

For a prescribed row sequence \(x^0,x^1,\ldots\), define

\[
\ell_t=
\left(Y_t,S_t,(P_{i,t},L_{i,t},M_{i,t})_{i\in I}\right)
\]

from

\[
Y_0=0,\quad S_0=1,\quad
P_{i,0}=0,\quad L_{i,0}=1,\quad M_{i,0}=-R
\]

by

\[
\begin{aligned}
Y'_k&=Y_k+Sg_k(x),&
S'&=Sc(x),\\
P'_i&=P_i+L_i a_i(x),&
L'_i&=L_i\chi_i(x),\\
M'_i&=\max\{M_i,P_i+L_iq_i(x)\}.
\end{aligned}
\tag{4}
\]

The coordinates have the exact forms

\[
S_t=\prod_{s<t}c(x^s),
\qquad
Y_{k,t}=\sum_{s<t}S_sg_k(x^s),
\tag{5}
\]

\[
L_{i,t}=\prod_{s<t}\chi_i(x^s),
\qquad
P_{i,t}=\sum_{s<t}L_{i,s}a_i(x^s).
\tag{6}
\]

The estimates

\[
|g_k(x)|\le R(1-c(x)),
\qquad
|a_i(x)|\le R(1-\chi_i(x))
\]

give

\[
|Y_{k,t}|\le R(1-S_t),
\qquad
|P_{i,t}|\le R(1-L_{i,t}),
\tag{7}
\]

and

\[
|P_{i,t}+L_{i,t}q_i(x^t)|\le R.
\tag{8}
\]

Therefore every ledger coordinate remains in a fixed compact interval; the
reachable-state closure is compact and every update (4) is continuous.

The prescribed payoff is

\[
U_k(\sigma)=Y_{k,\infty}.
\tag{9}
\]

For player \(i\), first Quitting at date \(t\) gives

\[
V_i(t)=P_{i,t}+L_{i,t}q_i(x^t),
\tag{10}
\]

while Never gives

\[
V_i(\infty)=P_{i,\infty}.
\tag{11}
\]

Hence the complete unrestricted behavioral cap is

\[
\boxed{
B_i(\sigma)
=
\max\left\{
\sup_{t\in\mathbb N}
\bigl(P_{i,t}+L_{i,t}q_i(x^t)\bigr),
P_{i,\infty}
\right\}
=
\max\{M_{i,\infty},P_{i,\infty}\}.}
\tag{12}
\]

Indeed, a behavioral replacement induces a probability law on
\(\overline{\mathbb N}=\mathbb N\cup\{\infty\}\), and its payoff is the
corresponding mixture of the values (10)–(11). Conversely, every such law is
implemented by its conditional hazards. If its remaining mass becomes zero,
all later hazards are arbitrary because those dates are unreachable.

For four players the forward ledger has dimension \(17\).

## 2. Exact occupation-flow primal

Fix the opponents' prescribed rows and one tester \(i\). Write

\[
q_t=q_i(x^t),\qquad
a_t=a_i(x^t),\qquad
\chi_t=\chi_i(x^t),\qquad
L_t=\prod_{s<t}\chi_s.
\]

A feasible occupation flow is a sequence of nonnegative triples
\((y_t,s_t,k_t)\) satisfying

\[
y_0=1,\qquad
s_t+k_t=y_t,\qquad
y_{t+1}=\chi_tk_t.
\tag{13}
\]

Its payoff is

\[
\mathcal P_i(y,s,k)
=
\sum_{t\ge0}(s_tq_t+k_ta_t).
\tag{14}
\]

Every behavioral hazard gives such a flow. Conversely,

\[
h_t=
\begin{cases}
s_t/y_t,&y_t>0,\\
0,&y_t=0
\end{cases}
\]

purifies every feasible flow exactly. The series (14) is absolutely
convergent because

\[
\sum_ts_t\le1,\qquad
\sum_tk_t(1-\chi_t)\le1,\qquad
|a_t|\le R(1-\chi_t).
\]

## 3. Never-sensitive Bellman dual

Let \(w=(w_t)\) range over bounded sequences satisfying

\[
w_t\ge q_t,
\qquad
w_t\ge a_t+\chi_tw_{t+1},
\qquad
\liminf_{t\to\infty}L_tw_t\ge0.
\tag{15}
\]

Then

\[
\boxed{
B_i(\sigma)
=
\sup_{\text{flows satisfying (13)}}\mathcal P_i
=
\inf_{w\text{ satisfying (15)}}w_0.}
\tag{16}
\]

For weak duality, telescope

\[
y_tw_t
\ge
s_tq_t+k_ta_t+y_{t+1}w_{t+1}.
\]

Since \(0\le y_t\le L_t\),

\[
y_tw_t\ge\min\{0,L_tw_t\};
\]

the transversality condition removes the terminal boundary term.

For the reverse inequality, let \(w_t\) be the true best-response value
against the opponent tail beginning at \(t\). It is bounded, obeys

\[
w_t=\max\{q_t,a_t+\chi_tw_{t+1}\},
\]

and satisfies transversality. If \(L_t\to0\), this follows from boundedness. If
\(L_t\to L_\infty>0\), the conditional probability of any later opponent
absorption under Never is

\[
1-\frac{L_\infty}{L_t}\longrightarrow0,
\]

so the tail Never payoff tends to zero and \(\liminf w_t\ge0\).

Finally, every pure finite stopping time and Never is itself a feasible flow.
Equation (12) therefore makes the primal supremum at least \(w_0=B_i(\sigma)\).
Together with weak duality and dual feasibility, all three values in (16)
are equal. This argument does not require an infinite greedy policy or
attainment of the pure-time supremum.

For a finite window with an exact terminal cap \(\beta\), replace
transversality by \(w_m\ge\beta\) and add \(y_m\beta\) to the primal objective.
Finite backward induction attains the common value.

## Scope

The ledger is a finite-dimensional sufficient state for evaluating one
prescribed chronology against every unilateral behavioral tester. It does
not select a low-debt chronology or make arbitrary literal suffixing a
compact, depth-uniform state operation.
