# Review of the charged-block response to the Fin4 spine question

**Reviewer:** `SOCIAL_WEIGHT_REVIEW`  
**Verdict:** mathematically sound reduction, but no durable new consumer.

## Claim audited

The response proposes to replace direct persistent-spine selection by the
following conditional route:

1. find finite exact Nash--Bellman blocks in one compact carrier with
   unbounded total marginal hazard;
2. use compact recurrence to select charge-bearing blocks with close
   endpoints;
3. concatenate them across summable endpoint seams, obtaining a
   summable-residual spine with one fixed persistent marginal; and
4. invoke the one-persistent or several-persistent consumer.

It also observes that a forward exact cap-prefix ray becomes an exact
Nash--Bellman block after reversing its cap annotations, and that independently
chosen finite-horizon minimizers do not supply the required source-compatible
concatenation.

## 1. Concatenation and seam constants

The concatenation argument is correct.  If the previous exact block expects
tail (u), while the next block begins at (w), and

\[
 \lVert u-w\rVert_\infty\le\eta,
\]

then the old last root has Bellman residual at most (eta).  The response's
(2\eta) root-Nash bound is valid but not sharp.

For quitting roots, the endpoint difference is (1)-Lipschitz in the
player's continuation coordinate.  Therefore an exact endpoint-Nash root at
(u) is endpoint-(eta)-Nash at (w), not merely
endpoint-(2eta)-Nash.  This is checked as

`isεQuittingRootEndpointNash_of_tail_close`

in `UniformEquilibrium/Quitting/Root/TailStability.lean`.  The generic
three-term comparison of prescribed and deviating payoffs gives the
conservative factor two, so it is not a correctness error.

The compact-cover extraction is also correct.  In Fin4 one edge has total
marginal hazard at most four.  Marking cumulative levels (5j) and applying
pigeonhole to (N+1) marked states in an (N)-set cover yields a contiguous
subblock with endpoint diameter below the cover mesh and hazard at least
(5-4=1).

This whole construction is already present in checked form through

- `HasUnboundedFiniteExactNashBellmanHazardCapacity`,
- `exists_summableResidualNashBellmanSpine_of_unboundedCapacity`, and
- the one- and two-persistent consumers in
  `SummableResidualNashBellmanSpine.lean` and
  `SummableResidualPersistentClosure.lean`.

Thus the response's concatenation lemma is correct but duplicated.

## 2. Reversed cap-block orientation

The cap calculation is correctly oriented.  On a forward exact cap-prefix
ray,

\[
 z_{t+1}^{B}=F_{x_t}(z_t^{B}),
 \qquad x_t\text{ exact Nash against }z_t^{B}.
\]

Hence the reversed list

\[
 z_b^{B},x_{b-1},z_{b-1}^{B},\ldots,x_a,z_a^{B}
\]

satisfies the chronological convention

\[
 v_s=F_{y_s}(v_{s+1}),
 \qquad y_s\text{ exact Nash against }v_{s+1}.
\]

The exact cap identity, not semantic proximity, is essential here.

The limitation is equally essential: this is an exact **abstract cap
Nash--Bellman block**.  Reversal does not make it the forward-time suffix of
the behavioral source from which the prefix ray was constructed.  Its far
cap endpoint is not automatically the next actual source, law, marked atom,
or response passport.  Thus the calculation does not supply the restart
required by the rewritten question.

## 3. Finite-chain minimizers

The displayed one-step inequality is correct.  Put

\[
 m_K=\min\sum_i d_i
\]

over length-(K) zero-boundary exact chains, let (P_K) be the selected
sum-minimizer, and prepend any bounded exact predecessor (x_K) of its initial
point.  If (d_i^K) is the debt vector at the initial point of (P_K), exact
debt transport gives

\[
 d_i^{\mathrm{prepend}}
   =c_{-i}(x_K)d_i^K.
\]

Since the prepended chain is an admissible length-(K+1) competitor,

\[
 m_{K+1}
 \le \sum_i c_{-i}(x_K)d_i^K
 =m_K-\sum_i(1-c_{-i}(x_K))d_i^K.             \tag{3.1}
\]

The sequence (m_K) is nonnegative and antitone.  Therefore (3.1) implies

\[
 \sum_i(1-c_{-i}(x_K))d_i^K\longrightarrow0. \tag{3.2}
\]

This is not new: the admissible prepend and antitonicity are checked in
`FiniteDynamicDebtMonotonicity.lean`; exact coordinate transport is the
`IsQuittingDebtEdge` identity in `DebtAugmentedEdge.lean`; and the stronger
calibrated loss bound is
`quittingFiniteDynamicDebt_sumMinimizer_prependPoint_calibrated` in
`FiniteDynamicDebtCalibration.lean`.

Equation (3.2) is nevertheless weaker than a vanishing root hazard.  Hazard
may be carried by players whose corresponding successor-debt weights vanish.
In the zero-loss limit, one positive debt coordinate permits a solo-owner
root, while two positive debt coordinates force all Continue; these are
already the checked classifications in `DebtAugmentedEdge.lean`.

Most importantly, the minimizers (P_K) for separate horizons need not be
nested, share an endpoint, or be legal continuations of one another.  Thus
(3.1)--(3.2) produce no concatenable source path.  Literal prepend matches
the predecessor only to the chosen (P_K); it does not identify the resulting
length-(K+1) competitor with (P_{K+1}).  This is exactly the
source-reprojection gap, not a new capacity consumer.

## 4. Durable delta

There is no new conjecture-facing theorem beyond the maintained waist.
The durable content is the following clean formulation:

> Once a positive-minimum source produces renewable exact charged blocks
> whose inter-block semantic/source seams are summable, the persistent label
> and unrestricted behavioral consumer are already automatic.

What remains absent is the producer:

\[
 \text{positive-minimum actual source}
 \longrightarrow
 \text{renewable charged exact blocks with summable source seams}.
\]

Ordinary convergence of annotations gives seam (o(1)).  Repetition needs
seam (o(\text{charge})), and the checked Fin4 ambient returned-block gap
rules out that relative estimate on late windows of any one exact spine.
Bounded exact-block capacity rules out obtaining it from unrelated blocks by
an unbounded-capacity argument.

The rewritten
`questions/FIN4_TWO_PERSISTENT_EXACT_SPINE_SELECTION.md` correctly asks to
consume this bounded-capacity, all-summable source branch rather than asking
for another ordinary exact-spine selector.
