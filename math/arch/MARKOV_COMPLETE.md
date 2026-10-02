# Exact counterfactual Markov order

This file classifies the information needed to update a labelled
counterfactual terminal-law state under arbitrary unilateral behavioral
replacement. It is an exact information theorem, not a compactness or
uniform-equilibrium theorem.

## 1. Counterfactual laws

Let \(I\) be a finite player set, \(n=|I|\ge1\), and

\[
\overline{\mathbb N}=\mathbb N\cup\{\infty\}.
\]

Along the unique all-Continue history, a behavioral strategy for player \(i\)
induces a stopping law \(\mu_i\in\Delta(\overline{\mathbb N})\). The players'
stopping times are independent. Conversely, every such law is realized by
its conditional hazards.

Let \(\Omega\) record Never and the labelled terminal quitting coalition,
optionally together with its date. Let

\[
\Phi:\overline{\mathbb N}^{I}\longrightarrow\Omega
\]

be the deterministic terminal map. For \(A\subseteq I\) and a vector of pure
stopping times \(t_A\), define

\[
K_\sigma(A,t_A)
=
\Phi_\#\left(
\bigotimes_{j\in A}\delta_{t_j}
\otimes
\bigotimes_{j\notin A}\mu_j
\right).
\tag{1}
\]

The order-\(k\) state \(\mathcal K_k(\sigma)\) consists of these labelled laws
for all \(|A|\le k\). These are coalition-outcome laws, not merely laws of
reward vectors; reward aliases may erase information used below.

For a fully pure vector \(t_I\), put

\[
\Gamma(t_I)=\delta_{\Phi(t_I)}.
\tag{2}
\]

This law is universal and independent of \(\sigma\).

## 2. Replacement formula

Replace player \(i\) by a behavioral strategy whose stopping law is \(\nu_i\).
For every intervention set \(A\),

\[
K_{\sigma[i\leftarrow\nu_i]}(A,t_A)
=
\begin{cases}
K_\sigma(A,t_A),&i\in A,\\[1.5ex]
\displaystyle
\int_{\overline{\mathbb N}}
K_\sigma^+\bigl(A\cup\{i\},t_A\oplus(i\mapsto s)\bigr)
\,d\nu_i(s),&i\notin A,
\end{cases}
\tag{3}
\]

where \(K_\sigma^+\) agrees with \(K_\sigma\) below full order and equals
\(\Gamma\) at full order. Formula (3) is disintegration in the new independent
stopping-time coordinate.

It follows that \(\mathcal K_{k+1}\) determines the successor
\(\mathcal K_k\). At \(k=n-1\), the only apparently missing order-\(n\)
queries are universal fully pure laws. Therefore \(\mathcal K_{n-1}\) is
closed under arbitrary unilateral replacement, and order \(n\) adds no
profile-dependent information.

## 3. Lower-order separation

Fix \(0\le k\le n-2\). Choose a hidden player \(h\), a blocker set

\[
B\subseteq I\setminus\{h\},
\qquad |B|=k+1,
\]

and dates \(a<b<c\). Put \(R=I\setminus(B\cup\{h\})\). Define two
deterministic profiles by

\[
T_h^\sigma=b,
\qquad
T_h^{\sigma'}=c,
\]

\[
T_j^\sigma=T_j^{\sigma'}=a\quad(j\in B),
\qquad
T_j^\sigma=T_j^{\sigma'}=c\quad(j\in R).
\tag{4}
\]

For every intervention on at most \(k\) players, either \(h\) is overwritten
or at least one blocker remains at date \(a\). Hence

\[
\mathcal K_k(\sigma)=\mathcal K_k(\sigma').
\tag{5}
\]

Choose \(b_0\in B\), replace \(b_0\) by pure time \(c\), and in the successor
query intervene on \(B\setminus\{b_0\}\), also at time \(c\). Under \(\sigma\),
\(h\) Quits alone at \(b\); under \(\sigma'\), every player Quits at \(c\).
The successor order-\(k\) laws are different, even when the terminal date is
omitted and only coalition labels are retained.

Thus \(\mathcal K_k\) is not self-closed for any \(k\le n-2\).

### Classification

Within the labelled pure-intervention hierarchy,

\[
\boxed{k_{\min}=n-1.}
\tag{6}
\]

For four players, the first replacement-closed order is \(3\). This is not a
lower bound on every conceivable state encoding; it is the exact answer
within the hierarchy \(\mathcal K_k\).

## 4. Lossless compression to marginal stopping laws

Assume \(n\ge2\). The state \(\mathcal K_{n-1}\) is losslessly equivalent,
on actual profiles, to the labelled tuple

\[
\mathbf M(\sigma)=(\mu_i)_{i\in I}.
\tag{7}
\]

To recover a finite atom \(\mu_i(\{t\})\), choose an anchor \(a\ne i\),
intervene on every player except \(i\), put \(a\) at time \(t\), and put every
other intervened player at Never. The terminal coalition is exactly
\(\{i,a\}\) precisely when \(T_i=t\). To recover the Never atom, put every
opponent at Never; the terminal outcome is Never precisely when
\(T_i=\infty\).

Conversely, equation (1) reconstructs every counterfactual law from the
marginals. On this compressed state, replacement is coordinate overwrite:

\[
\mathbf M(\sigma[i\leftarrow\nu_i])
=
(\mu_1,\ldots,\mu_{i-1},\nu_i,\mu_{i+1},\ldots,\mu_n).
\tag{8}
\]

This is a minimality statement only up to lossless recovery of
\(\mathcal K_{n-1}\). It does not exclude a different state designed for a
weaker collection of queries.

## 5. Quantitative replacement stability

Use the dual total-variation norm and define

\[
d_k(K,L)
=
\sup_{|A|\le k,\,t_A}
\|K(A,t_A)-L(A,t_A)\|_{\mathrm{TV}}.
\tag{9}
\]

Let \(U_i^\nu\) denote the update (3). Convexity gives

\[
d_{n-1}(U_i^\nu K,U_i^\nu L)
\le d_{n-1}(K,L),
\tag{10}
\]

and

\[
d_{n-1}(U_i^\nu K,U_i^{\nu'}L)
\le d_{n-1}(K,L)+\|\nu-\nu'\|_{\mathrm{TV}}.
\tag{11}
\]

Thus recursive replacement is exact and nonexpansive in this operational
metric.

## 6. Payoffs and unrestricted behavioral caps

Let \(\bar r_\ell:\Omega\to\mathbb R\) be the bounded terminal reward. Then

\[
U_\ell(K)=\int_\Omega \bar r_\ell\,dK(\varnothing),
\tag{12}
\]

while player (i)'s pure-time menu and unrestricted behavioral cap are

\[
G_i^K(s)=\int_\Omega \bar r_i\,dK(\{i\},s),
\qquad
B_i(K)=\sup_{s\in\overline{\mathbb N}}G_i^K(s).
\tag{13}
\]

An arbitrary behavioral replacement is a probability mixture of pure times,
so its payoff is the corresponding mixture of \(G_i^K(s)\). Hence order \(1\)
already determines current payoffs and all unrestricted unilateral caps.
What order \(1\) generally does not determine is its own state after a
replacement.

The resulting information classification is

\[
\begin{array}{c|c}
\text{task}&\text{least order established in this hierarchy}\\ \hline
\text{current prescribed payoff}&0\\
\text{current unrestricted behavioral caps}&1\\
\text{one update of order }k&k+1\\
\text{recursive update at fixed order}&n-1.
\end{array}
\]

## 7. Scope

This theorem closes recursive unilateral replacement on actual profiles. It
does not by itself provide:

- a compact topology with one modulus uniform over every suffix depth;
- the literal off-path policy after a history of zero survival probability;
- a finite global strategic net;
- realization of every compact boundary transition; or
- a terminal or recurrent synthesis theorem.

Those distinctions are developed in `SUFFIX_INFORMATION_OBSTRUCTION.md` and
`STATE_TOPOLOGIES_AND_APPROXIMATION.md`.
