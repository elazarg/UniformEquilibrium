# The unique-sure cap segment contains a source-attached double-debt point

Author: CODEX_SPINOZA

## Status

**Exact ordinary mathematics; genuine source-attached reduction, not
Lean-checked and not yet a Nash--Bellman consumer.** The actual approximate
cap handoff from the unique-sure inner-root branch can be interpolated in
stopping-law space. At the exact point where the sure owner's debt crosses
\(D_*/4\), the global minimum of total debt forces a distinct outsider to
carry debt at least \(D_*/4\) at the same actual profile.

Thus the zero-survival persistent-inner-mark branch supplies two co-sourced
full debts while retaining the original exact-prefix ancestry and the
owner's special Continue-then-tail cap response. The remaining gap is
temporal: applying either response changes the source against which the other
was profitable, and the interpolated source is not itself an exact
Nash--Bellman node.

## 1. Input

Use Theorem 3.1 of
CODEX_SPINOZA__UNIQUE_SURE_INNER_ROOT_ACTUAL_APPROXIMATE_CAP_HANDOFF.
For all sufficiently large \(n\), there are an actual source \(\rho_n\), a
fixed unique-sure owner \(k\), an actual response \(\beta_{n,k}\), and its
child

\[
 \chi_n=\rho_n[k\leftarrow\beta_{n,k}]
\tag{1}
\]

such that

\[
 d_k(\rho_n)\ge D_*/2,\qquad
 d_k(\chi_n)\le\varepsilon.
\tag{2}
\]

Choose

\[
 0<\varepsilon<D_*/16,\qquad \gamma:=D_*/4.
\tag{3}
\]

The opponents of \(k\) are identical in \(\rho_n\) and \(\chi_n\), and
\(\beta_{n,k}\) forces Continue at the capacity-selected inner root before
using an approximate cap response in the original literal tail.

## 2. Exact stopping-law segment

Let \(\mu_n\) and \(\nu_n\) be the complete stopping laws of player \(k\) in
\(\rho_n\) and \(\chi_n\), respectively. For \(0\le\lambda\le1\), set

\[
 \mu_n^\lambda=(1-\lambda)\mu_n+\lambda\nu_n.
\tag{4}
\]

Every probability law on \(\mathbb N\cup\{\mathrm{Never}\}\) is realized by
one behavioral quitting strategy through its conditional hazards. Replace
only player \(k\)'s law in \(\rho_n\) by this realization and call the actual
profile \(\sigma_n^\lambda\). Then

\[
 \sigma_n^0=\rho_n,\qquad \sigma_n^1=\chi_n.
\tag{5}
\]

Because the opponents are fixed, player \(k\)'s complete cap is constant on
the segment, while its prescribed payoff is affine in its own stopping law.
Therefore

\[
 d_k(\sigma_n^\lambda)
 =(1-\lambda)d_k(\rho_n)+\lambda d_k(\chi_n).
\tag{6}
\]

No continuity assertion at the all-Never boundary is being used: (4) is a
literal total-variation affine segment of two fixed laws, and both the
prescribed payoff and every fixed-response payoff are affine in that law.

## 3. Co-source theorem

### Theorem 3.1

For every sufficiently large \(n\), there is
\(\lambda_n\in(0,1)\) and an outsider \(j_n\ne k\) such that at the one
actual profile

\[
 \zeta_n:=\sigma_n^{\lambda_n}
\tag{7}
\]

one has

\[
 d_k(\zeta_n)=D_*/4,\qquad
 d_{j_n}(\zeta_n)\ge D_*/4.
\tag{8}
\]

After a subsequence, \(j_n=j\) is one fixed player distinct from \(k\).

Moreover, replacing \(k\)'s strategy in \(\zeta_n\) by the same retained
\(\beta_{n,k}\) gains at least

\[
 D_*/4-\varepsilon>3D_*/16.
\tag{9}
\]

Player \(j\) has a deterministic finite-or-Never response at \(\zeta_n\)
with gain at least \(D_*/8\).

### Proof

Equations (2)--(3) and the affine identity (6) give a unique
\(\lambda_n\in(0,1)\) with \(d_k(\sigma_n^{\lambda_n})=\gamma\).
The profile \(\zeta_n\) is actual. Global minimality of total unrestricted
debt gives

\[
 \sum_i d_i(\zeta_n)\ge D_*.
\tag{10}
\]

After subtracting the owner coordinate \(\gamma=D_*/4\), the three outsider
debts sum to at least \(3D_*/4\). One of them is therefore at least
\(D_*/4\), proving (8). Finite pigeonhole fixes its label.

The cap of \(k\) is unchanged along the segment. Since
\(\beta_{n,k}\) pays within \(\varepsilon\) of that cap, its gain from
\(\zeta_n\) is at least \(d_k(\zeta_n)-\varepsilon\), proving (9).
Pure-time extremality for \(j\)'s complete cap gives a deterministic finite
quit time or Never with gain arbitrarily close to \(d_j(\zeta_n)\), hence at
least \(D_*/8\). QED

### Corollary 3.2: outer exact ancestry is retained as a passport

In the persistent-inner-mark application, \(\rho_n\) is the literal inner
descendant of one finite word of exact payoff roots over the original reset
tail. The source \(\zeta_n\) is obtained from that descendant by one
one-player stopping-law interpolation. The response in (9) still forces
Continue at the same inner root and then uses the same literal tail response.

If the outer exact word has joint survival bounded below, copying it before
using either source profile transports all displayed gains with exactly that
joint-survival coefficient. This retains source ancestry and temporal
position; it does not say that the interpolated profile is an exact
successor of the word.

## 4. Temporal dispatch and exact remaining seam

Fix the outsider's deterministic response supplied by Theorem 3.1.
Relative to the capacity-selected inner cut, it is exactly one of:

1. Quit at that cut;
2. Quit at a strictly later finite cut; or
3. Never.

The owner response begins at the inner cut by replacing its current mixture
with Continue and then changing only the reached tail. Thus cases 2--3 give
a literal ordered two-cut fork, while case 1 gives two co-sourced current-cut
responses with distinct player labels.

This ordering is real, but it does not make a Nash--Bellman block. At
\(\zeta_n\), the inner product row differs from the exact root \(q_n\) in
player \(k\)'s marginal, so the original root complementarity equations no
longer hold. Applying the owner's response also changes the outsider's
payoff comparison, and applying the outsider's response changes the owner's
cap comparison. Neither gain is preserved at the other's child.

Consequently the theorem supplies the source-coherence missing from two
separately chosen debtors, but not the compatibility missing from the
already reviewed co-source/two-fork machinery. A consumer must re-solve the
joint finite response menu or control the signed cross-effects; common
source and ordered clocks alone do not do so.

## Sources inspected

- notes/CODEX_SPINOZA__UNIQUE_SURE_INNER_ROOT_ACTUAL_APPROXIMATE_CAP_HANDOFF.md;
- notes/CODEX_SPINOZA__PERSISTENT_INNER_MARK_DELAYED_PAID_SOURCE_OR_SURE_HANDOFF.md;
- formalized/FINITE_CLOCK_DOUBLE_FULL_GAP_COSOURCE.md;
- UniformEquilibrium/Quitting/Root/TerminalDebtPrefix.lean;
- UniformEquilibrium/Quitting/Root/LiteralPrefixDeviationTransport.lean;
- UniformEquilibrium/Quitting/Cycles/BehaviorPureTimeExtremality.lean; and
- UniformEquilibrium/Quitting/Paths/BehaviorStoppingLaw.lean and
  MathUE/Probability/StoppingLawReconstruction.lean.

## Boundary and nonclaims

- The segment uses convexity of one player's stopping-law simplex, not
  pointwise mixing of infinitely many hazards.
- The outsider label is fixed only after a subsequence.
- The owner response in (9) is the retained \(\varepsilon\)-cap response,
  not an attained complete cap.
- The two responses are profitable at the same actual source, but neither is
  asserted profitable after the other is applied.
- The source is an actual one-player replacement descendant of the exact
  inner source, not a new exact Nash--Bellman node or a minimum realizer.
- No return, renewable rank, terminal approximate Nash profile, or
  uniform-equilibrium payoff is claimed.

## Next exact question

On the two-strategy rectangle generated by the retained owner response and
the outsider's selected pure-time response, does quitting-game chronology
force either a boundary point with both within-menu regrets zero and small
outside debt, or a signed cross-effect of fixed size that can be charged to
the original exact-prefix capacity? A generic finite-game response rectangle
does not suffice; any positive answer must use the root ancestry retained in
Corollary 3.2.
