# Finite-window semantic value

The forward ledger in TESTER_LEDGER_AND_FLOW.md gives an exact
model-predictive optimization whose terminal certificate covers every
behavioral deviation, including Never and dates beyond the optimized window.
Its limiting value is exactly the original uniform-horizon objective.

## 1. Exact finite-word endpoint

For each player put

\[
s_i=r_i(\{i\}),
\qquad
s_i^+=\max\{s_i,0\}.
\]

After a finite controller word, prescribe all players to Continue forever.
At ledger state

\[
\ell=(Y,S,P,L,M),
\]

the exact terminal semantic pair is

\[
\widehat U_i(\ell)=Y_i,
\qquad
\widehat B_i(\ell)=\max\{M_i,P_i+L_is_i^+\}.
\tag{1}
\]

The first term in the cap records every elapsed stopping date. The second
records both a later solo Quit and Never in the all-Continue tail.

For a fixed target \(v\), define

\[
G_v(\ell)
=
\max\left\{
\|Y-v\|_\infty,
\max_i(\widehat B_i(\ell)-Y_i)
\right\}.
\tag{2}
\]

If \(F_x\) is one ledger update, let

\[
(\mathcal Pf)(\ell)=\min_{x\in[0,1]^I}f(F_x\ell).
\]

The exact \(m\)-window value is

\[
V_m(v)
=
(\mathcal P^mG_v)(\ell_0)
=
\min_{x^0,\ldots,x^{m-1}}
G_v(F_{x^{m-1}}\cdots F_{x^0}\ell_0).
\tag{3}
\]

Compactness and continuity give attainment. Every minimizer is an actual
finite product-root word followed by all Continue, and (2) evaluates its
complete terminal behavioral exploitability.

## 2. Compact semantic prefix state

Let

\[
\mathcal Z_R=[-R,R]^I\times[-R,R]^I
\]

with coordinates \(z=(u,b)\). For a product root \(x\), define

\[
T_x(u,b)_i
=
\left(
g_i(x)+c(x)u_i,\,
\max\{q_i(x),a_i(x)+\chi_i(x)b_i\}
\right).
\tag{4}
\]

The first coordinate is prescribed Bellman prefixing. The second is the exact
unrestricted cap: Quit now or Continue into the tail cap.

The all-Continue boundary state is

\[
e_\infty=(0,(s_i^+)_{i\in I}).
\tag{5}
\]

Let

\[
\mathcal K_r
=
\overline{\{(U(\sigma),B(\sigma)):\sigma\text{ behavioral}\}}
\tag{6}
\]

be the terminal-semantic carrier. Then

\[
\boxed{
\mathcal K_r
=
\overline{\{T_we_\infty:w\text{ a finite product-root word}\}}.}
\tag{7}
\]

### Proof of finite-word density

Take an arbitrary profile \(x^0,x^1,\ldots\) and replace every row after
date \(m-1\) by all Continue. Prescribed payoffs converge by absolute
convergence.

For player \(i\), write

\[
L_t=\prod_{s<t}\chi_i(x^s),
\qquad
P_t=\sum_{s<t}L_sa_i(x^s),
\qquad
Q_t=P_t+L_tq_i(x^t).
\]

The original cap is

\[
B_i=\max\{\sup_tQ_t,P_\infty\},
\tag{8}
\]

whereas the truncated cap is

\[
B_i^{[m]}
=
\max\left\{
\max_{t<m}Q_t,\,
P_m+L_ms_i^+
\right\}.
\tag{9}
\]

If \(L_\infty s_i^+=0\), equation (9) converges immediately to (8). Otherwise
\(L_\infty>0\) and \(s_i>0\). Positivity of the infinite product implies
\(\chi_i(x^t)\to1\), and

\[
|q_i(x^t)-s_i|
\le2R(1-\chi_i(x^t))
\longrightarrow0.
\]

Hence

\[
Q_t\longrightarrow P_\infty+L_\infty s_i.
\]

The apparent extra tail value in (9) is therefore already a limit of genuine
finite stopping-date values and is bounded by \(\sup_tQ_t\). Thus every
actual semantic pair is a limit of finite-word pairs. Taking closures gives
(7); the reverse inclusion is immediate because finite-word profiles are
actual.

Appending an all-Continue row to a finite word already followed by the
all-Continue tail changes no semantic pair. Therefore the exact-length
reachable sets can be padded, and

\[
\boxed{
V_m(v)\downarrow
\min_{(u,b)\in\mathcal K_r}
\max\left\{
\|u-v\|_\infty,
\max_i(b_i-u_i)
\right\}.}
\tag{10}
\]

## 3. Equality with the uniform-horizon objective

For a fixed profile \(\sigma\), define its horizon-\(H\) exploitability

\[
E_H(\sigma)
=
\max_i\sup_{\tau_i}
\left[
U_i^H(\sigma[i\leftarrow\tau_i])-U_i^H(\sigma)
\right],
\tag{11}
\]

and its terminal exploitability

\[
d(\sigma)=\max_i(B_i(\sigma)-U_i(\sigma)).
\tag{12}
\]

Then

\[
\boxed{E_H(\sigma)\longrightarrow d(\sigma).}
\tag{13}
\]

For the lower bound, fix one player attaining \(d(\sigma)\) and one terminal
replacement within \(\delta\) of its cap. The two fixed finite-horizon payoffs
converge to their terminal payoffs.

For the upper bound, \(\sigma\) is a terminal
\((d(\sigma)+\delta)\)-Nash profile. The strict terminal-to-uniform theorem
gives one threshold after which every player and every complete behavioral
replacement has horizon gain at most \(d(\sigma)+2\delta\). This includes a
different maximizing replacement for every \(H\). Letting \(\delta\downarrow0\)
proves (13).

For a prescribed target \(v\), put

\[
\begin{aligned}
W_r(v)=\inf_\sigma\inf_N\sup_{H\ge N}
\max\Bigl\{
&\|U^H(\sigma)-v\|_\infty,\\
&E_H(\sigma)
\Bigr\}.
\end{aligned}
\tag{14}
\]

Fixed-profile payoff convergence and (13) give

\[
\boxed{
W_r(v)
=
\min_{(u,b)\in\mathcal K_r}
\max\left\{
\|u-v\|_\infty,
\max_i(b_i-u_i)
\right\}
=
\lim_{m\to\infty}V_m(v).}
\tag{15}
\]

This is an offline quantifier value: the controller selects an entire profile.
It is not, without another theorem, the value of an online feedback game
against observed tester choices.

## 4. Target-free value

Allow the controller to select its target:

\[
\eta(r)=\min_{v\in[-R,R]^I}W_r(v).
\]

For fixed \((u,b)\), the optimal target is \(v=u\). Therefore

\[
\boxed{
\eta(r)
=
\min_{(u,b)\in\mathcal K_r}\max_i(b_i-u_i).}
\tag{16}
\]

Every coordinate debt is nonnegative on the carrier. Consequently

\[
\boxed{
\eta(r)=0
\quad\Longleftrightarrow\quad
r\text{ has a uniform-equilibrium payoff}.}
\tag{17}
\]

If a carrier minimizer \((u_*,b_*)\) has value zero, then \(b_*=u_*\).
Finite-word profiles converging to this point have terminal exploitability
tending to zero and payoffs tending to the one fixed target \(u_*\); terminal
selection yields the uniform payoff. The converse follows by converting a
uniform payoff into terminal approximate Nash profiles at every accuracy.

## Scope

Equations (15)–(17) give an exact complete controller–tester formulation and
finite-window approximation. They do not decide whether \(\eta(r)=0\) for
every four-player table or produce a table with \(\eta(r)>0\).
