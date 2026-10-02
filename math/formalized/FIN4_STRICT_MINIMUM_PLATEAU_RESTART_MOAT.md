# Fin4 strict-minimum plateau restart moat

Authors: CODEX_STRENGTHEN; Math Conference synthesis

Independent review:
[source and boundary gate](../feedback/CODEX_STRENGTHEN__FIN4_NONZERO_PERSISTENT_SPINE_SELECTION__BY_CODEX_SOURCE_GATE.md)

## Exact statement

Fix a four-player quitting reward table and assume that it has no
uniform-equilibrium payoff. The checked strict-minimum plateau theorem
supplies a compact debt segment \(P\), an open set \(O\) containing \(P\),
and uniqueness of the pure all-Continue exact root throughout \(O\).

There is \(\rho>0\) such that

\[
 a\in P,\ z\notin O\quad\Longrightarrow\quad
 \lVert z-a\rVert\ge\rho. \tag{1}
\]

If a finite exact Nash--Bellman block has terminal continuation \(z\) and
contains a root with positive absorption, then \(z\notin O\), and hence

\[
 \inf_{a\in P}\lVert z-a\rVert\ge\rho. \tag{2}
\]

Now let \(B_k\) be finite exact Nash--Bellman blocks, let \(z_k\) be the
terminal continuation of \(B_k\), and suppose a proposed chronology restarts
after \(B_k\) at an actual anchor \(a_k\in P\). Put

\[
 e_k=\lVert z_k-a_k\rVert.
\]

If \(\sum_k e_k<\infty\), then only finitely many \(B_k\) contain a
positively absorbing root. Consequently this construction has summable total
marginal Quit hazard and cannot produce a persistent player.

If all rewards and Bellman annotations have sup norm at most \(M>0\), every
exact block beginning in \(P\) and containing positive absorption has total
marginal-hazard charge at least

\[
 \sum_t\sum_i q_{t,i}\ge\frac{\rho}{2M}. \tag{3}
\]

Finally, let \((v_t,x_t)\) be a bounded exact Nash--Bellman spine with every
marginal hazard series summable. Its values converge to some \(v_\infty\).
Either the spine is the literal constant all-Continue spine at
\(v_\infty\), or

\[
 v_\infty\notin O,\qquad
 \operatorname{dist}(v_\infty,P)\ge\rho. \tag{4}
\]

## Conjecture-facing change

This eliminates the direct summable-seam restart route in
[the nonzero-persistent spine question](../questions/FIN4_TWO_PERSISTENT_EXACT_SPINE_SELECTION.md):
charge-bearing exact blocks cannot repeatedly return to the strict-minimum
plateau through summable metric endpoint seams.

A successful construction must instead use a nonlocal return whose
executable error is not an ordinary endpoint jump to \(P\), or discharge the
positive minimum debt before returning. This is a no-go, not the missing
producer.

## Proof

The segment \(P\) is compact and is contained in the open set \(O\).
Compactness therefore gives \(\rho>0\) such that

\[
 \bigcup_{a\in P}B(a,\rho)\subset O,
\]

which is (1).

The checked all-Continue basin-rigidity theorem says that a finite exact
Nash--Bellman block whose terminal continuation belongs to \(O\) contains
only all-Continue roots. Its contrapositive says that a block with any
positively absorbing root has terminal continuation outside \(O\). Equation
(1) then gives (2).

Every charge-bearing restart block has \(e_k\ge\rho\). A summable
nonnegative sequence has only finitely many terms at least \(\rho\).
All remaining blocks have zero absorption at every root and hence every
marginal Quit probability is zero. The finitely many exceptional finite
blocks contribute only finite total hazard.

For (3), write \(\alpha_t\) for root absorption. Bellman prefixing and the
bound \(M\) give

\[
 \lVert v_t-v_{t+1}\rVert_\infty\le2M\alpha_t.
\]

Endpoint separation, the triangle inequality, and
\(\alpha_t\le\sum_iq_{t,i}\) yield

\[
 \rho
 \le\lVert v_0-v_n\rVert_\infty
 \le2M\sum_{t<n}\alpha_t
 \le2M\sum_{t<n}\sum_iq_{t,i},
\]

proving (3).

For the last assertion, summability of every marginal implies summability of
root absorption. The same Bellman variation estimate makes \(v_t\) Cauchy,
while \(x_t\to\mathbf C\). If \(v_\infty\in O\), then eventually
\(v_{t+1}\in O\), uniqueness forces \(x_t=\mathbf C\), and Bellman equality
gives \(v_t=v_{t+1}\). The tail is constantly \(v_\infty\). Backward
induction using uniqueness at \(v_\infty\) makes the entire spine the
constant all-Continue spine. Otherwise \(v_\infty\notin O\), and (1) gives
(4).

## Probability and strategy audit

- Root absorption and marginal hazards are literal probabilities under
  simultaneous independent product actions.
- Exact root Nash is tested against every unilateral mixed root replacement.
- Basin rigidity concerns exact Nash--Bellman blocks; no stationary cap is
  substituted for an unrestricted behavioral cap.
- The result introduces no bounded-horizon or stopping-time truncation.
- It is an obstruction to a producer, not itself an equilibrium consumer.

## Boundary tests

1. A zero-absorption all-Continue block may remain inside \(O\).
2. Restarting at unrelated off-plateau points is outside the theorem.
3. A nonsummable sequence of endpoint seams may cross the moat infinitely
   often; summability is essential.
4. Known zero-minimum inert-ray regressions do not satisfy the positive
   strict-minimum plateau hypothesis.

## Source correspondence

The checked inputs are:

- exists_finFour_strictMinimumPlateau_openDebtHomotopyTube_of_no_uniformPayoff
  in UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticFinFourStrictMinimumPlateauIsolation.lean;
- anchoredPath_terminal_not_mem_of_positiveAbsorption,
  le_dist_terminal_of_positiveAbsorption_of_ball_subset_allContinueBasin,
  and exactNashBellmanPath_eq_anchor_of_tendsto_unique_allContinue in
  UniformEquilibrium/Quitting/Bellman/Finite/AllContinueBasinRigidity.lean;
- isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash, used by the
  existing basin/tube adapter.

The new content is the compact-segment uniformization, the sequence restart
corollary, the quantitative departure cost, and the segment-uniform
all-summable separation.

## Adapter and consumer

The actual-data adapter is the checked Fin4 no-uniform-payoff strict-minimum
plateau theorem. Its output directly supplies \(P\) and \(O\). The consumer
is negative: it eliminates every plateau-return construction whose ordinary
metric seams are summable.

## Lean handoff

Suggested declarations:

1. a compact-subset/open-set lemma producing a uniform ball radius;
2. a segment-uniform wrapper around the checked pointwise basin-distance
   theorem;
3. finite_chargeBearingBlocks_of_summable_plateauRestartSeams;
4. hazardCharge_ge_plateauMoat_div_two_mul_bound;
5. exactSpine_eq_constantAllContinue_or_limit_separated_from_plateau.

The implementation should reuse the existing plateau and basin-rigidity
modules and should not introduce a new source structure.

## Scope and nonclaims

- This does not produce a persistent spine or a uniform payoff.
- It does not forbid nonmetric, amortized, or law-changing source returns.
- The one-time lower bound \(\rho/(2M)\) is not a renewable rank.
- It does not say every all-summable spine is constant; a nonconstant one has
  its limit outside the plateau tube.

## Lean formalization record

Pre-formalization packet SHA-256:
`914451c4221060c5179025a06c6a1cf3546317f2b03956a6164131b9f06ec19a`.

The implementation landed in commit
`bdbfe5b7047067c36197f25fb34bc8ab981798b2`.  The generic restart and hazard
estimates are in
`UniformEquilibrium/Quitting/Bellman/Finite/AllContinueBasinRestartMoat.lean`;
the Fin4 no-uniform-payoff adapter is in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticFinFourMinimumFiberRestartMoat.lean`.

The principal checked declarations are
`exists_uniform_terminal_separation_of_positiveAbsorption`,
`finite_positiveAbsorptionBlocks_of_summable_restartSeams`,
`summable_hazardCharge_of_summable_restartSeams`,
`moat_div_two_mul_bound_le_hazardCharge`,
`eq_constantAllContinue_or_limit_uniformlySeparated`,
`exists_finFour_minimumFiber_uniformRestartMoat_of_no_uniformPayoff`, and
`finFour_noUniformPayoff_constantAllContinue_or_limit_uniformlySeparated`.

Evidence seals are `M`, `L`, and `A` for the Fin4 no-uniform-payoff source of
the minimum-fibre moat.  There is no semantic-closure `C`: the last theorem is
a checked restriction on a supplied exact spine, not a spine producer.  It
does not eliminate either final alternative, forbid law-changing or
nonmetric returns, turn the one-block hazard floor into a renewable rank, or
produce a uniform-equilibrium payoff.
