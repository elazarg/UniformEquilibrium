# A persistent cap child has either a shifted cap or negative payoff holonomy

Author: CODEX_SPINOZA

## Status

**Exact ordinary mathematics; proved dichotomy, no terminal consumer.** In
the nested terminal-cap-child sequence, every outsider payoff displacement
caused by the fixed owner's cap update has an exact affine recurrence and
finite total variation. Hence it has a limit. For the fixed outsider whose
debt is transported uniformly through the sequence, recursive cap selection
has only two outcomes:

1. after finitely many front resets, one fixed old cap is shifted forever; or
2. front Quit0 resets occur infinitely often, and then the owner's cap update
   lowers that outsider's payoff by one fixed amount in the limit.

Thus bounded capacity and nesting do yield signed structure. They do not
force a near-return: the limiting cross-coordinate displacement may be
nonzero, and positive far-end reach makes such holonomy natural. The two
outputs are respectively a two-label far-end cap packet and a cofinal
source-attached strict toggle. Neither is presently an accepted exact
Nash--Bellman return.

## Input

Use the notation and conclusions of
CODEX_SPINOZA__NESTED_TERMINAL_CAP_CHILD_FIXED_DEBTOR_TRANSPORT. Thus

\[
 \tau^{n+1}=q^n::\tau^n,\qquad
 \zeta^{n+1}=\bar q^n::\zeta^n,
\]

where \(\bar q^n\) is obtained from the exact root \(q^n\) by forcing the
fixed owner \(b\) to Continue. Put

\[
 h_{n,i}=q_i^n,\qquad
 \bar c_n=\prod_{i\ne b}(1-h_{n,i}).
\]

Assume

\[
 \sum_n\sum_i h_{n,i}<\infty,\qquad
 \prod_n\bar c_n>0.                                         \tag{1}
\]

Write

\[
 U^n=U(\tau^n),\qquad W^n=U(\zeta^n),\qquad
 \Delta_i^n=W_i^n-U_i^n.                                    \tag{2}
\]

Fix an outsider \(j\ne b\) and a number \(\delta>0\) such that

\[
 d_j(\zeta^n)\ge\delta\qquad(n\ge R).                        \tag{3}
\]

The fixed-observer transport theorem supplies (3) with
\(\delta=C_\infty\Gamma\) after choosing the terminal-gap observer once at
\(\zeta^R\).

Choose \(M>0\) bounding every reward coordinate. Then every prescribed payoff
coordinate also lies in \([-M,M]\).

## 1. Exact signed recurrence

Fix an outsider \(i\ne b\). Couple the current root laws \(q^n\) and
\(\bar q^n\) by retaining every outsider action and changing only \(b\)'s
Bernoulli action from Quit probability \(h_{n,b}\) to pure Continue.

Let \(\mu_n(S)\) be the probability that the set of quitting outsiders
\(I\setminus\{b\}\) is exactly \(S\), under their common root marginals.
Direct Bellman subtraction gives

\[
 \boxed{
 \Delta_i^{n+1}
 =\bar c_n\Delta_i^n+h_{n,b}G_{n,i},}                        \tag{4}
\]

where

\[
\begin{aligned}
G_{n,i}
={}&\bar c_n\bigl(U_i^n-r_i(\{b\})\bigr)\\
 &+\sum_{\varnothing\ne S\subseteq I\setminus\{b\}}
   \mu_n(S)\bigl(r_i(S)-r_i(S\cup\{b\})\bigr).
                                                                    \tag{5}
\end{aligned}
\]

Indeed, on the event \(S\ne\varnothing\), the barred law pays \(r_i(S)\),
whereas the original law mixes \(r_i(S)\) and \(r_i(S\cup\{b\})\).
On \(S=\varnothing\), the barred law continues to \(W_i^n\), whereas the
original law mixes \(U_i^n\) with the singleton outcome \(\{b\}\).
This proves (4)--(5).

The reward bound gives

\[
 |G_{n,i}|\le4M.                                             \tag{6}
\]

Since \(|\Delta_i^n|\le2M\),

\[
 |\Delta_i^{n+1}-\Delta_i^n|
 \le2M(1-\bar c_n)+4Mh_{n,b}.                               \tag{7}
\]

Both right-hand series are summable by (1). Therefore

\[
 \sum_n|\Delta_i^{n+1}-\Delta_i^n|<\infty,                  \tag{8}
\]

and every \(\Delta_i^n\) has a finite limit \(\Delta_i^\infty\).
Unrolling (4) gives the exact signed formula

\[
 \Delta_i^\infty
 =\left(\prod_{n\ge R}\bar c_n\right)\Delta_i^R
  +\sum_{k\ge R}h_{k,b}G_{k,i}
       \left(\prod_{n>k}\bar c_n\right).                     \tag{9}
\]

Nothing in bounded capacity forces the two terms in (9) to cancel.

## 2. Recursive cap clocks

At \(\zeta^n\), player \(b\) Quits surely by date \(n\). Every outsider cap
is therefore attained at a pure time in

\[
 \{0,\ldots,n,\operatorname{Never}\}.
\]

For player \(j\), select caps recursively across
\(\zeta^{n+1}=\bar q^n::\zeta^n\). At the new root a complete cap either
Quits immediately or Continues and uses a selected cap at \(\zeta^n\).
Hence the selected cap times obey

\[
 T_{n+1,j}\in\{0,T_{n,j}+1\},                                \tag{10}
\]

where \(\operatorname{Never}+1=\operatorname{Never}\).

Call the first choice a reset and the second a shift. If only finitely many
resets occur, then after the last reset one fixed complete cap in one fixed
finite child is shifted through every later prefix. This is the first arm of
the theorem.

## 3. Infinitely many resets force negative holonomy

It remains to consider an infinite sequence of reset indices \(n\), meaning
that Quit at the new root is a complete cap for \(j\) at \(\zeta^{n+1}\).
Write

\[
 E_n^{\rm old}
 =Q_j(q^n_{-j})-C_j(q^n_{-j};U_j^n),
\]

\[
 \bar E_n
 =Q_j(\bar q^n_{-j})-C_j(\bar q^n_{-j};W_j^n).               \tag{11}
\]

Because \(c_n>0\), player \(j\) has positive Continue probability at the
exact old root \(q^n\). Exact Nash therefore gives

\[
 E_n^{\rm old}\le0.                                         \tag{12}
\]

At a reset, the complete cap is the root Quit endpoint. The prescribed
payoff at \(\zeta^{n+1}\) mixes that endpoint with the Continue endpoint
using own Quit probability \(h_{n,j}\). Therefore

\[
 d_j(\zeta^{n+1})=(1-h_{n,j})\bar E_n.                       \tag{13}
\]

The persistent debt floor (3) gives

\[
 \bar E_n\ge\delta.                                          \tag{14}
\]

Let

\[
 \bar s_{n,j}=\prod_{\ell\ne b,j}(1-h_{n,\ell}).
\]

Changing only \(b\)'s root action and its continuation tail gives the exact
gap comparison

\[
 \bar E_n-E_n^{\rm old}
 =-\bar s_{n,j}\Delta_j^n+R_n,                               \tag{15}
\]

where a direct coupling of the Quit endpoint, the Continue absorbing
numerator, and the old continuation term gives

\[
 |R_n|\le6Mh_{n,b}.                                         \tag{16}
\]

Combining (12), (14), and (15) yields, at every reset,

\[
 -\bar s_{n,j}\Delta_j^n
 \ge\delta-6Mh_{n,b}.                                       \tag{17}
\]

By (1), \(h_{n,b}\to0\) and \(\bar s_{n,j}\to1\). At every sufficiently late
reset,

\[
 \Delta_j^n\le-\delta/2.                                    \tag{18}
\]

There are infinitely many such indices, while (8) says that
\(\Delta_j^n\) converges. Hence

\[
 \boxed{\Delta_j^\infty\le-\delta/2<0.}                     \tag{19}
\]

This is the second arm: cofinally many exact front cap resets force a fixed
negative cross-coordinate payoff holonomy.

## 4. What signed telescoping does and does not give

Equation (8) is stronger than mere compactness: the displacement path has
finite total variation. It gives a signed limit without passing to a
subsequence. Equation (19) shows that the infinite-reset branch cannot
approach a source return in the outsider payoff coordinate.

Even the exceptional cancellation \(\Delta_j^\infty=0\) would not by itself
give a summable chronological seam. From (4) and (9), cancellation only
bounds \(|\Delta_j^n|\) by a tail of the summable root-hazard series. Such
tails need not themselves be summable. The scalar pattern

\[
 h_{n,b}\asymp n^{-2},\qquad
 \Delta_j^n\asymp n^{-1}
\]

has summable increments and zero limit but nonsummable displacement values.
A sparse subsequence can make the values summable, but the literal transition
between two selected depths contains every skipped root and therefore every
intermediate Nash seam. Sparse reindexing is not a source-compatible
concatenation.

## 5. Consumer audit

The finite-reset arm supplies two fixed labels at the same far-end suffix:
the sure clock of \(b\) and a fixed old complete cap of \(j\), both shifted
through a nested sequence with positive suffix reach. The roots
\(\bar q^n\), however, are not known Nash for the outsiders.

The infinite-reset arm supplies cofinally many literal sources at which
Quit0 is \(j\)'s cap with fixed gain at least \(\delta\), and (19) identifies
the fixed externality causing the reset. This is a source-attached strict
toggle. It is still a horizontal cap response at a child of the exact root
block, not an exact Nash--Bellman predecessor.

The punishment-floor split does not change this conclusion. A floor-safe
child starts the checked summable marked exact orbit. An underfloor child
starts an exact dynamic-debt tail whose joint absorption is summable by
summable_dynamicDebtTailAbsorptionCharge_of_floorViolation_of_positiveDebt.
Those re-solved roots need not equal \(\bar q^n\), so neither construction
removes the signed seam (15).

No named finite-clock, adjacent-deadline, paid-port, or exact-spine consumer
accepts either arm without an additional source-compatible Nash
re-equilibration.

## Boundary tests

### Finite total variation is not summability of the seam

A convergent nonzero constant sequence has zero increment variation and an
infinite sum of absolute values. Thus (8) cannot be substituted for the
summable Nash-error hypothesis of an approximate-spine compiler.

### The sign in the reset branch is forced

At a reset with positive debt, Quit is above the prescribed Continue
endpoint. The old exact root has Quit no better than Continue. Removing
\(b\)'s current Quit probability changes the two current endpoint terms only
by \(O(Mh_{n,b})\). Therefore the remaining order-one sign must be
\(-\Delta_j^n>0\): the owner cap child lowers \(j\)'s continuation payoff.
The opposite sign would contradict (14) at late reset indices.

### The result is not a game-level counterexample

The scalar \(n^{-2}/n^{-1}\) pattern only falsifies an attempted summability
inference from (4). It is not asserted to arise from a positive-gap quitting
table. The game-level theorem is the exact dichotomy (10), (19) under the
supplied nested-child data.

## Source correspondence

The nested identity and fixed-observer transport are in
notes/CODEX_SPINOZA__NESTED_TERMINAL_CAP_CHILD_FIXED_DEBTOR_TRANSPORT.md,
frozen at SHA-256
6d813418986400654a0c93fd8e54469b9d965fd61fdefee848cf7c9803c9e956.

The positive-survival cap-clock and bounded-capacity theorem is Section 10 of
notes/CODEX_SPINOZA__RECURSIVE_LITERAL_U_ROOT_PREFIX_LEDGER_AND_STALL.md,
frozen at reviewed SHA-256
3823bb3e816de7d3328b0a82045dae42daae9f3cd3a937b7b50bf7a3370052ee.

The exact one-step payoff identities are instances of
quittingTerminalPayoff_update_rootThenContinuation_eq and the ordinary
Bellman endpoint decomposition. The underfloor summability theorem is in
UniformEquilibrium/Quitting/Debt/Dynamic/PunishmentFloorViolation.lean.

## Scope and nonclaims

The theorem proves finite total variation of every cross-coordinate
displacement and the shifted-cap versus negative-holonomy dichotomy for one
fixed persistent debtor. It does not prove that the forced-owner child roots
are exact or approximate Nash for outsiders.

The negative limit (19) is a macroscopic externality, not a debt decrease or
a semantic return. The shifted-cap arm is a fixed far-end response, not a
persistent marginal hazard on an accepted Nash--Bellman spine. No uniform
equilibrium or contradiction to positive global debt is proved.

## Next exact question

Can the negative-holonomy arm be converted by a quitting-specific
two-coordinate index theorem into a root-Nash re-equilibration that preserves
the sure \(b\)-clock? Failing that, can the shifted-cap arm be represented as
a two-label terminal block whose endpoint is an actual source for the checked
two-cut consumer rather than a horizontal response sibling?
