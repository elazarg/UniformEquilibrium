# Opponent-tight realization of positive-minimum semantic limits

Author: CHATGPT_EXTERNAL

Status: TWO INDEPENDENT REVIEWS AND FINAL PACKET GATE PASS; EXPORTED FOR FORMALIZATION

First independent review:

- feedback/POS_DEBT_REAL__BY_CODEX_RAMSEY.md

Second independent review and falsification audit:

- feedback/CHATGPT_EXTERNAL__OPPONENT_TIGHT_POSITIVE_MINIMUM_REALIZATION__BY_CODEX_EULER.md

Final packet gate:

- feedback/OPPONENT_TIGHT_TERMINAL_SEMANTIC_REALIZATION_PACKET_GATE__BY_CODEX_MINER.md

Export:

- exports/OPPONENT_TIGHT_TERMINAL_SEMANTIC_REALIZATION.md

That audit validates the opponent-tight unrestricted-cap convergence and the
one-proper-clock minimum argument. It requires every escape statement to
remain relative to the selected compactified realizing subsequence, and
distinguishes late-or-Never mass in the approximants from literal common Never
mass in the limiting laws. The second audit additionally requires a finite
player type with at least two players and the repository's compact stopping-law
topology on WithTop Nat. The statement below incorporates those repairs.

Source: ../POS_DEBT_REAL.md

## Question

Let \(I\) be a finite player type with \(2\le |I|\). Let actual behavioral
profiles \(\sigma_n\) have terminal semantic pairs
converging to a carrier point \(z=(u,b)\). Under what additional stopping-law
condition is \(z\) itself realized by an actual behavioral profile? What does
nonattainment look like when \(D(z)=D_*>0\) is the positive global minimum?

## Opponent-tight realization theorem

Pass to a subsequence on which every complete stopping law
\(\mu_i^n\), viewed as a repository CompactStoppingLaw, converges weakly on
\[
\overline{\mathbb N}=\operatorname{WithTop}\mathbb N
\]
with its one-point compactification topology to a law \(\mu_i\). Let
\(\sigma_\infty\) be the actual behavioral profile reconstructed from these
limiting laws. Put

\[
M_{-i}^n=\min_{j\ne i}T_j^n.
\]

Assume opponent tightness:

\[
\boxed{
\forall i,\quad
\lim_{H\to\infty}\limsup_{n\to\infty}
\Pr(M_{-i}^n>H)=0.} \tag{OT}
\]

Then

\[
\boxed{\operatorname{Sem}(\sigma_\infty)=z.} \tag{1}
\]

### Prescribed payoffs

For fixed \(H\), payoff truncated to absorption by time \(H\) is a finite
polynomial in the point masses at \(0,\ldots,H\), hence converges under weak
law convergence. The omitted payoff has magnitude at most

\[
R\,\Pr(\min_iT_i^n>H)
\le R\,\Pr(M_{-i_0}^n>H)
\]

for any fixed \(i_0\). Opponent tightness, followed by \(H\to\infty\), proves
\(U(\sigma_n)\to U(\sigma_\infty)\).

### Behavioral caps

For player \(i\), let

\[
v_{i,n}(t)=U_i(\sigma_n[i\leftarrow Q_i^t]),
\qquad t\in\overline{\mathbb N}.
\]

Every fixed finite \(t\) has
\(v_{i,n}(t)\to v_{i,\infty}(t)\). If \(s,t>H\), including Never, then the two
deviations coincide whenever an opponent stops by \(H\). Thus

\[
|v_{i,n}(s)-v_{i,n}(t)|
\le2R\,\Pr(M_{-i}^n>H). \tag{2}
\]

Compare both tails to \(H+1\), use finite-time convergence at \(H+1\), and
apply opponent tightness also to the limiting opponents. This gives

\[
\sup_{t\in\overline{\mathbb N}}
|v_{i,n}(t)-v_{i,\infty}(t)|\to0. \tag{3}
\]

Pure-time extremality now implies

\[
B_i(\sigma_n)\to B_i(\sigma_\infty),
\]

proving (1) against the unrestricted behavioral strategy class.

## Two proper clocks suffice

Call \(\mu_i\) proper if \(\mu_i(\{\infty\})=0\). If two distinct limiting
laws are proper, then every player has at least one proper opponent.
Weak convergence to that proper law gives (OT), so the semantic limit is
actual.

Consequently, every compactified realizing subsequence of a nonattained
semantic point has at most one proper limiting clock. After a further
subsequence there are a player \(i\) and \(\kappa>0\) such that

\[
\forall H,\qquad
\limsup_n
\Pr(T_j^n>H\ \text{for every }j\ne i)\ge\kappa. \tag{4}
\]

The player \(i\) and \(\kappa\) belong to the selected compactified
subsequence; this is not a uniform statement over every realizing sequence.

## Exactly one proper clock at a positive global minimum

Assume \(D(z)=D_*>0\), and exactly one limiting law is proper, belonging to
player \(k\). Let \(\widehat\sigma\) be the profile of limiting laws and write
\(\widehat b_k=B_k(\widehat\sigma)\).

The proper clock \(T_k\) makes total absorption tight, so

\[
U(\widehat\sigma)=u. \tag{5}
\]

It is also a proper opponent for every \(j\ne k\), hence

\[
B_j(\widehat\sigma)=b_j\qquad(j\ne k). \tag{6}
\]

Global minimality gives

\[
\widehat b_k\ge b_k. \tag{7}
\]

Every fixed finite time passes to the limit and was bounded by the
approximating cap. Therefore

\[
\beta_k^{\mathrm{fin}}
:=\sup_{t<\infty}
U_k(\widehat\sigma[k\leftarrow Q_k^t])
\le b_k. \tag{8}
\]

If \(\widehat b_k=b_k\), the point is attained. Thus nonattainment forces

\[
\widehat b_k>b_k\ge\beta_k^{\mathrm{fin}},
\]

so the unique excess cap witness at the limiting actual profile is Never.

Set

\[
q_{-k}=\prod_{j\ne k}\mu_j(\{\infty\})>0,
\qquad s_k=r_k(\{k\}).
\]

Dominated convergence along finite \(t\to\infty\) gives

\[
U_k(\widehat\sigma[k\leftarrow Q_k^t])
\longrightarrow
\widehat b_k+q_{-k}s_k. \tag{9}
\]

Combining (8)--(9) yields

\[
\boxed{s_k<0,\qquad
0<\widehat b_k-b_k\le -q_{-k}s_k.} \tag{10}
\]

Thus the sole discontinuous cap coordinate is the proper player's; the jump
is a strict Never advantage supported on the common Never event of all its
opponents, and it requires a negative singleton reward.

## Exhaustive residual

For any fixed compactified realizing subsequence of a nonattained positive
global minimum, exactly one of the following remains:

1. no limiting clock is proper, so every player has a positive Never atom; or
2. exactly one clock is proper, and the negative-singleton Never jump
   (7)--(10) occurs.

If all singleton rewards are nonnegative, only the all-player escape arm is
possible.

This is a realization theorem under opponent tightness and a sharp
classification of the one-proper-clock failure. It does not prove universal
attainment of the positive minimum and does not construct a positive-gap
table.

## Review request

Check the topology on \(\overline{\mathbb N}\), continuity of finite cylinder
events, the limiting tail bound used in (3), the quantifiers in (4), and the
minimum-debt argument in (5)--(10). Search narrowly for an existing checked
declaration that already packages opponent-tight cap convergence or the
negative-singleton Never-jump classification.
