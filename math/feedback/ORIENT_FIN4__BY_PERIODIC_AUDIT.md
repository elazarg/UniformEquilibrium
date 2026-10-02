# Independent audit of `ORIENT_FIN4`: periodic cap near-return

## Status

The periodic cap-near-return lemma is mathematically sound after its order
convention and contraction hypotheses are made explicit.  It genuinely
controls the complete behavioral best-response cap, not only stationary or
finite-horizon deviations.  It is a useful new conditional consumer.

Two repairs are required before the surrounding packet can be accepted:

1. the strict-ray application must split off blocks with zero opponent
   contraction before writing the ratios in (8)--(9); and
2. the passage from a fixed-sign block cap displacement in (9) to the
   normalized pointwise assertion (h_i<0, \lambda_i=0) in (10) is not
   established by the displayed hypotheses or by the inspected normalized-flow
   interfaces.

Thus Section 1, and Section 2 with the stated contraction qualification,
survive.  Section 3 currently overstates what failure of the consumer proves.

## Claim audited

Let

\[
  b_{t+1}=P_{q_t}(b_t),\qquad
  q_t\in\operatorname{Nash}(b_t),
\]

and let the chronological word be the *reverse-indexed* outward-prefix word

\[
  W=q_{m-1}*\cdots*q_0.
\]

If every player's opponents have positive probability of absorbing during one
copy of (W), then the periodic repetition (W^\omega) satisfies

\[
 d_i(W^\omega)
 \le
 \frac{|b_{m,i}-b_{0,i}|}{1-c_{-i}(W)}
 +
 \frac{|b_{m,i}-b_{0,i}|}{1-c(W)}.
\]

Here the debt uses the unrestricted behavioral best-response envelope.

## 1. Indexing and Bellman order

The indexing is correct, but the note should explain it because it is opposite
to the usual chronological indexing.  The ray is built by outward prefixing:

\[
 b_1=P_{q_0}(b_0),\quad
 b_2=P_{q_1}(b_1),\quad\ldots
\]

Consequently (q_{m-1}) is played first and (q_0) last in the finite word.
Starting with continuation (b_0), backward evaluation gives

\[
 P_W(b_0)
 =P_{q_{m-1}}(\cdots P_{q_0}(b_0)\cdots)
 =b_m.
\]

Likewise, for player (i), single-stage exact Nash at (q_0), then (q_1),
and so on proves by finite backward induction that

\[
 R_{W,i}(b_{0,i})=b_{m,i}.
\]

No chronological mismatch was found.  A formal statement should either retain
this outward-prefix convention explicitly or reindex the chronological phases
as (r_t=q_{m-1-t}).

## 2. Prescribed fixed point

The prescribed block operator is affine:

\[
 P_W(x)=h_W+c(W)x.
\]

The playerwise assumptions (c_{-i}(W)<1) imply (c(W)<1), since
(c(W)\le c_{-i}(W)).  Therefore periodic prescribed play absorbs almost
surely and has the unique fixed point (u^\omega=P_W(u^\omega)).  Subtracting
(P_W(b_0)=b_m) gives exactly

\[
 u_i^\omega-b_{0,i}
 =\frac{b_{m,i}-b_{0,i}}{1-c(W)}.
\]

This is consistent with
`quittingCyclicTerminalValue_eq_rootSuccessorPayoff` and the contraction
machinery in
`UniformEquilibrium/Quitting/Cycles/PeriodicCompiler.lean`.

## 3. Unrestricted behavioral cap

For fixed periodic opponents, define (R_{W,i}(x)) as the supremum over every
behavioral policy of (i) during the next finite copy of (W), with scalar
continuation (x) after complete survival.  This is legitimate in a quitting
game: while play is live there is only the all-Continue public history at each
date, so arbitrary behavioral replacements reduce to arbitrary date-dependent
hazards (including the policies that ultimately Never quit).

For each finite-block policy, dependence on (x) is affine with coefficient
equal to the probability of reaching the next copy.  That probability is at
most the fixed opponents' survival probability (c_{-i}(W)).  Taking suprema
therefore preserves the common Lipschitz bound

\[
 |R_{W,i}(x)-R_{W,i}(y)|
 \le c_{-i}(W)|x-y|.
\]

Because (c_{-i}(W)<1), opponent survival over repeated copies tends to zero
uniformly over the deviator's behavior.  Finite-block truncations therefore
show that the complete behavioral cap is the unique fixed point of
(R_{W,i}).  This is the same survival mechanism used by
`quittingCyclicHazardTerminalValue_le_of_isZeroRootNash` and
`isZeroAsymptoticNash_quittingCyclicBehaviorProfile_of_certificate` in
`PeriodicCompiler.lean`; those declarations explicitly range over arbitrary
behavioral deviations through the live-hazard bridge.

Thus the contraction estimate for (B_i^\omega), and hence the displayed debt
bound, are valid.  Never and arbitrarily late stopping are not omitted.

## 4. Exact hypotheses that should be stated

The theorem should state the following data rather than leave them implicit:

- a nonempty finite player set and a finite reward table;
- a positive block length;
- the outward-prefix order (W=q_{m-1}*\cdots*q_0);
- `q_t` is exact root Nash against the continuation vector `b_t`;
- (b_{t+1}=P_{q_t}(b_t));
- for every player (i), (c_{-i}(W)<1).

No attainment of the infinite behavioral supremum is needed.  Approximate
tail optimizers plus contraction prove the fixed-point equality.  The reward
bound is automatic for a finite table, but should be named if the block
operator is developed abstractly.

A family for which the maximum normalized seam tends to zero gives terminal
approximate Nash profiles.  To conclude existence of one uniform-equilibrium
payoff, invoke the compact target-selection theorem
`quittingGame_exists_uniformEquilibriumPayoff_of_terminalNash_all_errors` in
`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`.

## 5. Zero-denominator branch in the ray application

Equations (8)--(9) are not meaningful without a convention or a preliminary
split when

\[
 1-c_{-i}(W_{K,N})=0.
\]

This can occur even when the word has positive *joint* absorption: all
absorption may be generated by player (i) alone.  For that player, replacing
its strategy by Never can prevent absorption forever, and the periodic
best-response operator is not contractive.  The cap-near-return lemma supplies
no bound in this case, including when the cap displacement also vanishes and
the displayed quotient would be (0/0).

The repaired strict-ray dispatch should therefore be:

1. a cofinal deleted-clock obstruction, meaning some player has
   (c_{-i}(W)=1) on the relevant blocks; or
2. blocks with (c_{-i}(W)<1) for every player, on which the normalized ratios
   are defined and the periodic consumer/fixed-sign extraction applies.

An extended-real quotient convention is possible, but it does not remove the
need to record the (0/0) noncontracting case separately.

## 6. The unsupported normalized-seam inference

With positive denominators, failure of the near-return condition does yield,
after finite pigeonhole extraction, a fixed player, fixed sign, and positive
constant satisfying a block inequality of the form (9).  That conclusion is
sound at the finite-block cap level.

It does **not** by itself yield (10).  The inspected
`QuittingTailNormalizedCapFlow` interface separates two different first-order
objects:

- `cap_increment` controls one-step cap displacement through the solo matrix
  and current hazard; and
- `endpoint_decomposition` and `subseq_collision_nonpos` produce the signed
  complementarity vector involving tail and collision limits.

A signed lower bound on a sum of cap increments divided by opponent-deleted
absorption has not been shown to select a pointwise limit coordinate of the
second object.  The fixed sign in (9) may also be positive or negative, while
the inequality (h\le0) has a fixed orientation; “after orienting the sign”
cannot reverse that inequality.  Additional hypotheses controlling the
relation between block opponent absorption, total hazard, current/tail hazard
averages, and the normalized endpoint decomposition would be needed.

The safe surviving conclusion is:

> Failure of the periodic consumer, away from the deleted-clock branch,
> produces a fixed-player, fixed-sign finite-block cap seam per unit of
> opponent absorption.

Calling it a missing binding player with (h_i<0) is premature.

## Sources inspected

- `UniformEquilibrium/Quitting/Cycles/PeriodicCompiler.lean`:
  `quittingStationaryContinueMass_le_fixedOpponentsContinueMass`,
  `abs_sub_quittingCyclicTerminalValue_le`,
  `quittingCyclicHazardTerminalValue_le_of_isZeroRootNash`,
  `isZeroAsymptoticNash_quittingCyclicBehaviorProfile_of_certificate`.
- `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`:
  `quittingGame_exists_uniformEquilibriumPayoff_of_terminalNash_all_errors`.
- `Research/Quitting/ForwardExactCapTailFlow.lean`:
  `QuittingTailNormalizedCapFlow`,
  `QuittingTailNormalizedCapFlow.subseq_collision_nonpos`,
  `QuittingTailNormalizedCapFlow.subseq_collision_complementarity`.
- `Research/Quitting/ForwardExactCapTailFirstOrder.lean`:
  `tailNormalized_capFlow_tendsto`, `tailNormalizedCapFlow`.
- `Research/Quitting/FinFourProducerAtlas/StrictRayTailNormalizedCapFlow.lean`:
  the actual strict-ray adapter and its normalized-flow certificate.

## Verdict

The periodic lemma is a genuine result and is suitable for repair and further
review.  It gives an unrestricted-behavior consumer for cap-near-return blocks.
The full `ORIENT_FIN4` packet is not yet export-ready because its normalized
description of the failure branch is unsupported and its zero-contraction
case is underspecified.
