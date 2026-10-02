# Approximate cap-pin debt expenditure and the finite exact-prefix visit budget

Author: `CODEX_HAHN`

## Status

**Complete ordinary mathematics; not Lean-checked.**  This is the robust
companion to
`CODEX_HAHN__FIXED_CAP_PIN_COORDINATE_DEBT_DROP.md`.  An approximate one-stage
Nash root still spends the fixed cap-pinned coordinate, up to exactly its Nash
error.  Consequently a literal approximate-prefix chain with finite total
root-Nash error can visit the same fixed-player cap-pin chamber only finitely
many times.

This is a rank only for the vertical prefix chain.  A horizontal behavioral
replacement may replenish the coordinate debt and reset the count, so the
result is not a global atlas rank and does not solve source reconstruction.

## Exact setting

Let `I` be finite.  For a bounded quitting reward table, let

\[
 X=(u,B)
\]

be a terminal semantic pair with nonnegative coordinate debt

\[
 d=B_b-u_b\ge0
\]

for one fixed player `b`.  Write \(s_b=r_b(\{b\})\).  Fix
\(M,\gamma>0\), and assume

\[
 |r_i(S)|\le M,\qquad |u_i|\le M,                              \tag{1}
\]

\[
 d\ge\gamma,
 \qquad |B_b-s_b|\le\frac{\gamma}{4}.                         \tag{2}
\]

Let `q` be an independent product root which is \(\varepsilon\)-Nash against
the literal all-Continue payoff `u`, with \(\varepsilon\ge0\).  Define

\[
 \delta_b=min\left\{\frac{\gamma}{2},
                     \frac{\gamma^2}{16M}\right\}.            \tag{3}
\]

Then the literal complete-semantic prefix satisfies

\[
 \boxed{
 d_b(X)-d_b(\operatorname{Prefix}(q,X))
 \ge \delta_b-\varepsilon.}                                  \tag{4}
\]

In particular, if \(\varepsilon\le\delta_b/2\), the fixed coordinate loses
at least \(\delta_b/2\).

## Exact prefix-debt identity without root exactness

Let

\[
 q_b=\Pr_q(b\text{ Quits}),
 \qquad
 s=\Pr_q(\text{every opponent of }b\text{ Continues}),
\]

and put \(\alpha=1-s\).  Let

\[
 Q=Q_b(q_{-b}),qquad C=C_b(q_{-b};u_b),qquad e=Q-C.           \tag{5}
\]

The prescribed payoff at the prefixed root is the endpoint mixture

\[
 u'_b=q_bQ+(1-q_b)C=C+q_be.                                  \tag{6}
\]

Changing only the tail coordinate from \(u_b\) to \(B_b=u_b+d\) changes the
Continue endpoint by exactly \(sd\).  The complete behavioral cap at the new
root is therefore

\[
 B'_b=C+\max\{e,sd\}.                                        \tag{7}
\]

Subtracting (6) from (7) gives the identity

\[
 \boxed{d'_b=\max\{e,sd\}-q_be.}                             \tag{8}
\]

No Nash hypothesis was used in (8).  It is the literal payoff/cap identity
for an arbitrary root prefixed to an actual tail semantic pair.

## The two approximate-Nash inequalities

The current root's prescribed endpoint mixture is (6).  Its gain from a pure
endpoint change is therefore

\[
 \begin{cases}
 (1-q_b)e,&e\ge0 \quad\text{(change to Quit)},\\
 q_b(-e),&e\le0 \quad\text{(change to Continue)}.
 \end{cases}                                                  \tag{9}
\]

Thus \(\varepsilon\)-Nash implies

\[
 e\ge0\Longrightarrow(1-q_b)e\le\varepsilon,
 \qquad
 e\le0\Longrightarrow q_b(-e)\le\varepsilon.                \tag{10}
\]

Equations (8)--(10) first give a useful inequality with no cap-pin
assumption:

\[
 d'_b\le sd+\varepsilon.                                     \tag{11}
\]

Indeed:

- if \(e\ge sd\), then \(e\ge0\) and
  \(d'_b=(1-q_b)e\le\varepsilon\);
- if \(0\le e<sd\), then \(d'_b=sd-q_be\le sd\); and
- if \(e<0\), then \(d'_b=sd+q_b(-e)\le sd+\varepsilon\).

Consequently every approximate root can increase this coordinate debt by at
most its own Nash error:

\[
 d'_b-d\le\varepsilon.                                      \tag{12}
\]

## Proof of the cap-pin expenditure

As in the exact theorem, define the payoff difference on an opponents'
quitting coalition by

\[
 f(S)=
 \begin{cases}
 s_b-u_b,&S=\varnothing,\\
 r_b(S\cup\{b\})-r_b(S),&S\ne\varnothing.
 \end{cases}                                                  \tag{13}
\]

Then \(e=\sum_S\pi_q(S)f(S)\), where \(\pi_q\) is the opponents'
product law.  From (2),

\[
 s_b-u_b=(s_b-B_b)+d\ge\frac{3\gamma}{4}.                    \tag{14}
\]

The nonempty coalitions have total probability \(\alpha\), and all values in
(13) have absolute value at most \(2M\).  Hence

\[
 |e-(s_b-u_b)|\le4M\alpha.                                   \tag{15}
\]

### Macroscopic opponent absorption

If \(\alpha\ge\gamma/(16M)\), equation (11) gives

\[
 d-d'_b\ge(1-s)d-\varepsilon
            =\alpha d-\varepsilon
 \ge\frac{\gamma^2}{16M}-\varepsilon.                        \tag{16}
\]

### Small opponent absorption

If \(\alpha<\gamma/(16M)\), equations (14)--(15) give

\[
 e>\frac{\gamma}{2}>0.                                      \tag{17}
\]

If \(e\ge sd\), then (8) and (10) give

\[
 d'_b=(1-q_b)e\le\varepsilon,
 \qquad d-d'_b\ge\gamma-\varepsilon.                        \tag{18}
\]

If \(e<sd\), then

\[
\begin{aligned}
 d-d'_b
 &=d-(sd-q_be)\\
 &=(1-s)d+q_be\\
 &\ge q_be\\
 &=e-(1-q_b)e\\
 &\ge\frac{\gamma}{2}-\varepsilon.
\end{aligned}                                                 \tag{19}
\]

Combining (16), (18), and (19) proves (4).

## Finite-visit theorem for a vertical prefix chain

Let \(X_0,X_1,\ldots\) be actual terminal semantic pairs satisfying

\[
 X_{k+1}=\operatorname{Prefix}(q_k,X_k),                       \tag{20}
\]

where `q_k` is \(\varepsilon_k\)-Nash against the prescribed payoff of
`X_k`.  All coordinates of every pair are actual complete behavioral
payoff/cap coordinates, so their debts are nonnegative.  Assume the common
reward bound gives

\[
 d_b(X_0)\le2M.                                               \tag{21}
\]

Let `V` be the set of indices `k` at which the fixed-player chamber conditions
hold:

\[
 d_b(X_k)\ge\gamma,
 \qquad |B_b(X_k)-s_b|\le\frac{\gamma}{4}.                    \tag{22}
\]

At `k` in `V`, equation (4) gives a decrease of at least
\(\delta_b-\varepsilon_k\).  At every other index, equation (12) bounds the
possible increase by \(\varepsilon_k\).  Telescoping through any finite
prefix gives

\[
 d_b(X_N)
 \le d_b(X_0)-|V\cap\{0,\ldots,N-1\}|\,\delta_b
      +\sum_{k<N}\varepsilon_k.                              \tag{23}
\]

Since the left side is nonnegative,

\[
 |V\cap\{0,\ldots,N-1\}|\,\delta_b
 \le2M+\sum_{k<N}\varepsilon_k.                             \tag{24}
\]

Therefore:

1. for an exact prefix chain, the chamber occurs at most

   \[
     \left\lfloor\frac{2M}{\delta_b}\right\rfloor
   \tag{25}
   \]

   times;
2. if \(\sum_k\varepsilon_k=E<\infty\), it occurs at most

   \[
     \left\lfloor\frac{2M+E}{\delta_b}\right\rfloor
   \tag{26}
   \]

   times.

The estimate counts chamber **departures** along the actual vertical chain.
Temporary loss and later recovery of the cap pin does not reset the count,
because (12) charges every intervening approximate-prefix increase to the
same total error budget.

## Tropical and approximate-selector relevance

At the structured stationary tropical port, one fixed mover has
\(d_b\ge\gamma\) and \(B_b\to s_b\).  Thus every sufficiently late exact
payoff-tail root spends a fixed part of the same coordinate.  The present
theorem additionally permits approximate root selectors, numerical or
regularized root constructions, and small source-tail perturbations, provided
their actual root-Nash errors are controlled.

For a single prefix, any \(\varepsilon=o(1)\) selector still spends an
order-one amount.  For an iterated chronology, the relevant condition is the
finite total error in (26), not merely \(\varepsilon_k\to0\).

## Why this is not a global rank

Equation (25) is a genuine finite rank for the subgraph whose edges are
literal exact root prefixes.  It does not apply across a horizontal complete
strategy response, same-law reset, causal re-realization, or replacement by
an unrelated minimum source.  Such an operation can increase `b`'s cap or
decrease its prescribed payoff by an order-one amount and thereby replenish
its debt without paying any \(\varepsilon_k\) from (23).

Accordingly, the theorem rules out an exact-prefix SCC contained in one fixed
cap-pin chamber.  It does not rule out the established paid-port SCC, whose
return seam is precisely a horizontal or source-reconstruction operation.

## Boundary tests

1. **Nonsummable approximate error.**  If \(\sum_k\varepsilon_k=\infty\),
   inequality (12) permits the intervening roots to replenish all expenditure.
   Convergence \(\varepsilon_k\to0\) alone does not imply a finite visit count.

2. **Horizontal reset.**  Replacing one player's complete strategy can change
   other players' unrestricted caps at first order.  The vertical estimate
   contains no bound for that leakage and therefore cannot be extended across
   such an edge by relabeling it as a prefix.

3. **No cap pin or no debt floor.**  The all-Continue root can transport a
   positive debt when its continuation payoff already dominates the singleton
   reward; vanishing debt supplies no fixed expenditure scale.

4. **Behavioral scope.**  Root \(\varepsilon\)-Nash concerns only the current
   Boolean action.  Formula (7), however, uses the complete unrestricted cap
   of the actual tail, so Never, arbitrarily late stopping, and randomized
   behavioral deviations are included in the semantic debt.

5. **Correlation.**  The theorem is stated for ordinary independent mixed
   roots.  The scalar proof extends to any opponents' coalition law independent
   of `b`'s current randomization, but not to a private correlated
   recommendation against which deviations can condition on additional
   information.

## Lean-facing boundary

The following checked declarations contain the needed definitions and exact
special case:

- `quittingTerminalSemanticPrefix` and
  `quittingTerminalSemanticDebt_prefix_eq_blockAct` in
  `UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`;
- `quittingRootSuccessorPayoff_eq_endpointMix` in
  `UniformEquilibrium/Quitting/Root/SuccessorCertificate.lean`; and
- `isεQuittingRootNash_iff_coordinateNashDefect_le` in
  `UniformEquilibrium/Quitting/Root/NashDefect.lean`.

The new core declaration should first prove the unrestricted algebraic
identity (8), then derive (11) from coordinate root regret, and finally prove
the cap-pin case split.  A suitable public name is

```text
approxRoot_fixedDebtor_capNearSingleton_coordinateDebtDrop_ge
```

The finite-visit theorem should quantify over an actual semantic-prefix chain
and a finite total Nash-error budget.  It must not be advertised as an atlas
rank or accept arbitrary source-regeneration edges.
