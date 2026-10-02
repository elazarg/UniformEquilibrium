# Two sure clocks turn every finite cap child into a universal-prefix descendant

Author: `CODEX_HAHN`

## Status

**Exact ordinary mathematics; source-linked sibling strengthening, not
Lean-checked and not a consumer.** Once a renewed source retains two distinct
prescribed finite sure clocks, every later deterministic finite-clock cap
child is semantically a finite arbitrary-prefix descendant of its actual
parent, not merely a sibling over a common shifted tail. Therefore the
greatest target-free universal-prefix barrier is nondecreasing on both the
vertical exact-prefix phases and the horizontal cap-child seams.

The total barrier increase along an infinite alternating renewal is summable.
This does not control the positive capacity recharge: a bounded monotone
barrier may be exactly flat on every horizontal seam.

## Question

Does the two-sure-clock property orient the barrier values of the linked
parent/cap-child sibling words without assuming stationarity?

## 1. Tail-independent two-clock words

Let \(I\) be finite. Let \(w=(w^0,\ldots,w^H)\) be a finite word of product
roots. Suppose there are distinct players \(a,b\) such that, under the
prescribed word, each Quits surely no later than date \(H\).

For every terminal-semantic tail \(z\), write \(T_wz\) for evaluation of the
word over that tail.

### Theorem 1.1

For any two tails \(z,z'\),

\[
 \boxed{T_wz=T_wz'.}
\tag{1}
\]

The equality includes prescribed payoff and every unrestricted behavioral
cap.

### Proof

Prescribed play absorbs by date \(H\), so its payoff does not see the tail.
Fix a deviator \(i\). If \(i=a\), player \(b\)'s sure clock remains; if
\(i=b\), player \(a\)'s remains; and if \(i\notin\{a,b\}\), both remain.
Thus under every complete unilateral replacement, absorption occurs by
date \(H\). The deviating payoff is identical over \(z\) and \(z'\) for
every behavioral response, including Never and arbitrarily late stopping.
Taking the supremum over the same response class proves equality of the cap
coordinate. This holds for every \(i\), proving (1).

## 2. A finite cap child is a descendant of its actual parent

Let \(\sigma\) be an actual profile with two distinct prescribed finite sure
clocks. Change one player \(k\)'s complete strategy to a deterministic finite
clock and call the actual child \(\tau\). The replacement either preserves
both old sure clocks or replaces one of them by another finite sure clock for
the same player. Hence \(\tau\) still has two distinct sure-clock players.

Choose a common finite deadline \(H\) for two of them, and let \(w\) be
\(\tau\)'s literal root word through \(H\). The two-clock semantic truncation
gives

\[
 \operatorname{Sem}(\tau)=T_wz_{\rm tail}
\tag{2}
\]

for its literal shifted tail \(z_{\rm tail}\). Theorem 1.1 lets us replace
that tail by the actual parent semantic pair:

\[
 \boxed{\operatorname{Sem}(\tau)=
 T_w\operatorname{Sem}(\sigma).}
\tag{3}
\]

Thus the horizontal update is a genuine edge in the universal-prefix
preorder. No stationarity or common-tail identification is needed.

This theorem applies after the second distinct-owner installation in the
renewed positive-survival cap-clock construction. The earlier sure clock is
shifted but not removed, and the new deterministic cap supplies the second.
All later finite cap installations retain at least two distinct sure-clock
players.

## 3. Barrier monotonicity along the full alternating renewal

Let

\[
 s_m\longrightarrow p_m\dashrightarrow s_{m+1}
\]

be the later alternating phases: \(p_m=T_{v_m}s_m\) is a finite exact
Nash--Bellman prefix descendant, and \(s_{m+1}\) is the deterministic finite
cap child of \(p_m\). Let

\[
 Q(z)=\inf_u d(T_uz)
\]

be the greatest target-free universal-prefix barrier. Prefix monotonicity and
(3) give

\[
 Q(s_m)\le Q(p_m)\le Q(s_{m+1}).
\tag{4}
\]

Hence \(Q(s_m)\) and the interleaved sequence

\[
 Q(s_0),Q(p_0),Q(s_1),Q(p_1),\ldots
\]

are nondecreasing. Since \(Q\) is bounded on the semantic reward box,

\[
 \sum_m\bigl(Q(p_m)-Q(s_m)\bigr)
 +\sum_m\bigl(Q(s_{m+1})-Q(p_m)\bigr)<\infty.
\tag{5}
\]

In particular, both the vertical and horizontal barrier increments tend to
zero.

## 4. Exact limitation

Let \(\Phi\) be bounded exact-block capacity-to-go and put

\[
 K_m=\Phi(s_{m+1})-\Phi(p_m),\qquad
 L_m=Q(s_{m+1})-Q(p_m).
\]

Equation (4) proves \(L_m\ge0\), and (5) proves \(\sum_mL_m<\infty\).
This is the favorable sign for the scalarization

\[
 \widetilde\Psi=\Phi-\lambda Q,
\]

whose horizontal seam would be controlled by

\[
 K_m-\lambda L_m\le\varepsilon_m.
\tag{6}
\]

But neither (4) nor the positive-minimum level bound supplies a lower modulus
for \(L_m\) in terms of the capacity recharge \(K_m\). The barrier can remain
flat while the horizontal update restores exact-block capacity. Therefore
(3)--(5) orient the linked siblings but do not prove (6).

## Source correspondence

The exact complete-semantic two-clock truncation and persistence through
renewal are in
`notes/CODEX_HAHN__TWO_RENEWED_SURE_CLOCKS_GIVE_FINITE_COMPLETE_SEMANTICS.md`,
frozen at SHA-256
`e596e78d2476e72d7cc561a77b4b7507c24a3ac682dc69946ffc23629bbc735d`.
The sibling factorization without this strengthening is in
`notes/CODEX_SPINOZA__FINITE_CAP_CHILD_BARRIER_ANCESTRY_AND_FLATNESS.md`,
reviewed at SHA-256
`1e53b6b85cfa7d7fdaf2749418d8b9c713d6ec69498dd63c804c32dac86e99f6`.
Universal-prefix barrier monotonicity is
`quittingControllerWordInf_le_finitePrefixSemanticEval` in
`UniformEquilibrium/Quitting/ControllerTester/FunctionBarrierDuality.lean`.
The conditional capacity/barrier scalarization is in
`notes/CODEX_SPINOZA__LINKED_SIBLING_BARRIER_CAPACITY_LYAPUNOV_CRITERION.md`.

## Boundary tests and nonclaims

1. One sure clock is insufficient. The owner of that clock can deviate past
   it and see the tail, so (1) can fail in its cap coordinate.
2. A Never cap response is not a finite word and is not covered. The renewed
   positive-survival branch used here supplies a deterministic finite cap.
3. The finite deadline may vary with the renewal phase; no uniform deadline
   is needed for (1)--(5).
4. The result gives an exact semantic descendant, not an exact Nash--Bellman
   horizontal edge. The word \(w\) need not be Nash at any row.
5. No strict barrier increment, capacity bound, terminal approximate Nash
   profile, renewable rank, or uniform-equilibrium payoff is proved.

## Next exact question

At a positive-minimum structured cap collar, does asymptotic equality
\(Q(s_{m+1})-Q(p_m)\to0\) for these fully screening cap-child words force
their horizontal capacity recharge to vanish, or can a positive-gap Fin4
source realize a flat barrier and fixed recharge simultaneously?
