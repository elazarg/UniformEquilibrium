# The raw maximum-debt superlevel is never prefix invariant

Author: `CODEX_HAHN`

## Status

**Exact dimension-independent no-go theorem in ordinary mathematics; not
Lean-checked.**  For every bounded quitting table with at least two players,
the simplest closed invariant-set ansatz

\[
 \{(u,b):\max_i(b_i-u_i)\ge\gamma\}
\]

fails universal product-root invariance at every positive feasible floor.
The counterexample state and one-player mixed root are explicit.

This explains why an exact negative barrier must encode more semantic
geometry than its desired debt floor.  It does not rule out the linearly
relaxed contact-cone template or any other proper semialgebraic superset of
the terminal-semantic carrier.

## 1. Exact statement

Let `I` be finite with at least two players, let

\[
 |r_i(S)|\le R,
 \qquad R>0,
\]

and let

\[
 \mathcal Z_R=[-R,R]^I\times[-R,R]^I.
\]

For `z=(u,b)`, put

\[
 d(z)=\max_i(b_i-u_i).
\]

For every `gamma` with

\[
 0<\gamma\le2R,
\]

define the raw debt superlevel

\[
 P_\gamma=\{z\in\mathcal Z_R:d(z)\ge\gamma\}.
\tag{1}
\]

### Theorem 1.1

For every such reward table and `gamma`, there exist `z in P_gamma` and an
independent product root `x` such that

\[
 d(T_xz)<\gamma.
\tag{2}
\]

Consequently `P_gamma` is never an all-root invariant semantic barrier.

## 2. One-player root formulas

Fix a player `k` and let only `k` Quit at the new root, with probability
`t in (0,1)`.  Put `s_i=r_i({i})`.

For an outsider `i != k`, exact semantic prefixing gives two cap branches.
The Continue-branch debt is

\[
 (1-t)(b_i-u_i).
\tag{3}
\]

The Quit-branch debt is

\[
 (1-t)s_i+t r_i(\{i,k\})
 -\bigl((1-t)u_i+t r_i(\{k\})\bigr).
\tag{4}
\]

The actual prefixed debt is the maximum of (3) and (4).

For the root player `k`, all opponents Continue, so its cap is

\[
 \max\{s_k,b_k\},
\]

while its prescribed payoff is

\[
 t s_k+(1-t)u_k.
\tag{5}
\]

These are exact unrestricted behavioral-cap formulas.  The root has only one
stage, but the Continue branch in (3) and (5) retains the complete tail cap.

## 3. Proof of Theorem 1.1

There are two cases.

### Case A: some singleton reward is below the upper bound

Choose `j` with

\[
 s_j<R
\]

and choose a distinct player `k`.  Define the semantic state

\[
 b_i=R\quad(i\in I),
 \qquad
 u_j=R-\gamma,
 \qquad
 u_i=R\quad(i\ne j).
\tag{6}
\]

Then player `j` has debt `gamma`, all other debts are zero, and hence
`z in P_gamma`.

Use the one-player `k` root above.  Player `j`'s Continue debt is
`(1-t)gamma < gamma`.  Its Quit-branch debt tends, as `t` tends to zero, to

\[
 s_j-(R-\gamma)<\gamma.
\]

Hence both branches are below `gamma` for every sufficiently small positive
`t`.

For every outsider `i` different from `j` and `k`, the Continue debt is zero
and the Quit-branch debt tends to `s_i-R <= 0`; it is therefore below
`gamma` for all sufficiently small positive `t`.

Finally (5), with `u_k=b_k=R`, gives root-player debt

\[
 t(R-s_k)\le2Rt,
\]

which is below `gamma` for small positive `t`.  Finiteness of the player set
allows one common choice of `t`.  Every prefixed debt is then below `gamma`.

### Case B: every singleton reward equals the upper bound

Now `s_i=R` for every player.  Choose any player `j` and use the same state
(6), with `k=j`.  Formula (5) gives player `j` debt

\[
 (1-t)\gamma<\gamma.
\]

For an outsider `i`, the Continue debt is zero and (4) reduces to

\[
 t\bigl(r_i(\{i,j\})-r_i(\{j\})\bigr),
\]

whose positive part is at most `2Rt`.  Again every coordinate debt is below
`gamma` for sufficiently small positive `t`.  This proves (2).  QED

## 4. Consequences for barrier synthesis

The raw superlevel (1) is closed and has the desired positive debt floor.  If
it contains all-Never, it would be the smallest possible formula one might
try before encoding carrier geometry.  The theorem shows that its failure is
universal and local: no table search can repair it.

The bad state (6) is generally not a terminal-semantic carrier point.  This
is precisely the issue.  A sound invariant-set certificate may choose a
proper closed set containing the carrier and omit (6), but it must give an
independently checkable description of that additional geometry.

The companion contact-cone ansatz does this at the floor.  It excludes the
one-active-debt state (6) when its maximum debt is exactly `gamma`, because a
true positive barrier contact must instead have all debts equal, positive
singleton moats, and the harmonic first-order inequality.  Those conditions
must relax away from the floor so that the all-Never seed can still enter.

## 5. Source correspondence and nonclaims

The formulas are direct specializations of the exact unrestricted semantic
prefix map `quittingTerminalSemanticPrefix`.  The full-box, all-product-root
invariance requirement is the checked closed-set dual in
`formalized/QUITTING_CONTROLLER_TESTER_VALUE_AND_BARRIER_DUALITY.md`.

- Restricting roots to exact Nash roots would evade the theorem but would not
  certify all behavioral profiles.
- Restricting states to the unknown carrier would also evade it but would
  reintroduce the original global membership problem.
- The theorem proves no uniform-equilibrium payoff and produces no negative
  table.  It eliminates only the raw debt-superlevel grammar.

