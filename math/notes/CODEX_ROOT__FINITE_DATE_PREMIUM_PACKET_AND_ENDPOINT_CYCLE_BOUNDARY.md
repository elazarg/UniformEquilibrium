# Finite-date premium packet and endpoint-cycle boundary

Author: CODEX_ROOT, preserving the mathematical content of ../TANGENT.md

## Current status

The large-premium theorem and the exact own-debt identities below are proved
as ordinary mathematics. The endpoint-cycle example is a no-go for ranks
depending only on finite horizontal labels. None of these statements produces
a Bellman chronology, minimum-fiber regeneration, or a Fin4 terminal-gap
counterexample.

Mathematical audit:
[TANGENT__BY_CODEX_ROOT.md](../feedback/TANGENT__BY_CODEX_ROOT.md).

## 1. Own-strategy endpoint updates transfer rather than destroy debt

Let \(\tau'\) differ from \(\tau\) only in player \(q\)'s complete behavioral
strategy, and set

\[
G=U_q(\tau')-U_q(\tau)>0.
\]

Player \(q\)'s opponents are unchanged, so its unrestricted behavioral cap is
unchanged:

\[
B_q(\tau')=B_q(\tau).
\]

Consequently

\[
d_q(\tau')=d_q(\tau)-G.
\tag{1}
\]

For total debt,

\[
D(\tau')-D(\tau)
=
-G+\sum_{k\ne q}\bigl(d_k(\tau')-d_k(\tau)\bigr).
\tag{2}
\]

If \(D(\tau)\le D_*+\varepsilon\), global minimum provenance supplies only

\[
\sum_{k\ne q}\bigl(d_k(\tau')-d_k(\tau)\bigr)\ge G-\varepsilon.
\tag{3}
\]

This is a lower bound on compensating debt created elsewhere. It neither puts
\(\tau'\) near the minimum fiber nor prevents new debt coordinates from
appearing.

## 2. Exact large-premium packet

Fix a player \(j\), put \(C=I\setminus\{j\}\), and define

\[
f_j
=
\min\left(
0,\min_{\varnothing\ne S\subseteq C}r_j(S)
\right),
\qquad
\pi_j=r_j(\{j\})-f_j.
\]

Assume a terminal exploitability gap \(\gamma>0\) and

\[
\pi_j\ge\gamma.
\tag{4}
\]

Then there is a literal deterministic profile \(\sigma\), a date
\(a\in\{0,1\}\), and an actual profile

\[
\tau=\sigma[j\leftarrow Q_a^j]
\]

such that:

\[
U_j(\tau)-U_j(\sigma)\ge\gamma,
\qquad
d_j(\tau)=0,
\tag{5}
\]

and \(Q_a^j\) is an attained exact unrestricted behavioral best response.

Moreover, the terminal gap at \(\tau\) selects a player \(q\ne j\) and an
attained best response

\[
Q_b^q,\qquad b\in\{0,1,\infty\},
\]

with gain at least \(\gamma\).

### Proof

If \(f_j=0\), prescribe all players Never. Quitting at date zero gives
\(r_j(\{j\})=\pi_j\ge\gamma\), while Never gives zero.

Otherwise choose nonempty \(S_*\subseteq C\) with
\(f_j=r_j(S_*)\). Prescribe everyone Continue at date zero, exactly the
players of \(S_*\) Quit at date one, and all remaining behavior Never.
Against these deterministic opponents, player \(j\)'s pure-time values are

\[
V_j(Q_0)=r_j(\{j\}),
\quad
V_j(Q_1)=r_j(S_*\cup\{j\}),
\quad
V_j(Q_t)=V_j(Q_\infty)=f_j\quad(t\ge2).
\]

Every behavioral response is a probability mixture of these three endpoint
values, so a best response is attained by \(Q_0\) or \(Q_1\). It improves on
the prescribed Never strategy by at least
\(r_j(\{j\})-f_j=\pi_j\).

At \(\tau\), player \(j\)'s debt is zero. Hence the terminal gap must be owned
by some \(q\ne j\). Every opponent of \(q\) has deterministic stopping time
zero, one, or infinity, so \(q\)'s behavioral cap is attained among
\(Q_0,Q_1,Q_\infty\).

Thus the large-premium arm produces an exact literal finite-date profile
packet, not merely a static reward inequality.

## 3. These updates are not chronological edges

The arrows

\[
\sigma\longrightarrow\tau\longrightarrow
\tau[q\leftarrow Q_b^q]
\]

are counterfactual replacements of complete profiles. The second profile is
not the all-Continue continuation reached from the first. In general there is
no Bellman identity

\[
U(\tau)
=
\operatorname{SuccPayoff}(x,U(\tau')).
\]

Therefore a return in this profile graph is not a cumulative admissible
near-return and is not an exact punishment-floor chronology.

## 4. Exact horizontal debt-token cycles

Fix a player \(j\) that Quits surely at the reached row and two other players
\(a,b\). Choose nonsingleton rewards so that

\[
\begin{aligned}
r_a(\{j,a\})&>r_a(\{j\}),\\
r_b(\{j,a,b\})&>r_b(\{j,a\}),\\
r_a(\{j,b\})&>r_a(\{j,a,b\}),\\
r_b(\{j\})&>r_b(\{j,b\}).
\end{aligned}
\]

Set all unused membership-toggle differences to zero or orient them
nonprofitably. The pure sure-exit roots then carry the strict cycle

\[
\{j\}\to\{j,a\}\to\{j,a,b\}\to\{j,b\}\to\{j\}.
\tag{6}
\]

The four displayed margins may all equal one. At each vertex exactly the next
mover carries the selected positive toggle debt; its update removes that debt
and passes the token to the next mover. The positive-debt support cardinality
and routed-coalition cardinality data can return exactly.

Only nonsingleton reward coordinates, apart from already fixed singleton
values at \(\{j\}\), are needed. Thus the construction can preserve a chosen
singleton matrix or singleton blocker.

This proves that no universally decreasing rank can depend only on

\[
(\text{mover},\text{recipient},\text{positive-debt support},
\text{routed coalition},\text{principal size}).
\]

The example is not asserted to have \(D_*>0\) or a positive terminal gap. It
does not refute a rank using full positive-minimum source provenance.

## Remaining producer

Both the small-premium collision packet and the exact large-premium packet
still require one of:

- a prescribed-payoff Nash--Bellman chronology;
- source-regenerated strict finite-rank descent; or
- terminal approximate Nash profiles.

A cycle of exact best responses in the horizontal profile graph supplies none
of these by itself.

## Nonclaims

This note does not:

- prove either premium arm consumable;
- place an endpoint target on the minimum fiber;
- prevent debt support entry;
- turn exact finite-date best responses into a temporal equilibrium block; or
- construct a four-player terminal-gap table.
