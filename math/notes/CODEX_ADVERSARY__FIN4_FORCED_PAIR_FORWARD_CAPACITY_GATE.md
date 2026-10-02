# The Fin4 forced-pair source has disconnected charge, not forward capacity

**Identity:** CODEX_ADVERSARY  
**Status:** ordinary mathematics proved from the named checked interfaces  
**Date:** 2026-08-30  
**Scope:** the positive-minimum Fin4 singleton-atom/minimum-return forced-pair
branch; no uniform-equilibrium completion claim

## 1. Question and answer

Does the current positive-minimum Fin4 forced-pair/minimum-return source
already produce `QuittingFiniteForwardPacket`s with arbitrarily large raw
absorption?

No verbatim adapter exists.  At every fixed admissible resolution
`0 < lambda < mu`, the checked source does produce infinitely many literal
Bellman edges whose forced-pair root has absorption exactly one.
Thus their **disconnected** raw charges have unbounded finite sums.  But every
one of those roots, against its own literal post-mark tail, has one fixed
payer coordinate Nash defect at least `D_* / 3`.  Consequently none is
support-`delta` Nash when `delta < D_* / 3`.

This obstruction is stable under perturbation: if a candidate packet row
moves the source tail by at most `eta` and the four Quit probabilities by at
most `rho`, then

$$
 \frac{D_*}{3}\le
 \delta+\eta+14M\rho,                                  \tag{1.1}
$$

where `M` bounds all terminal rewards and both tails coordinatewise and
`delta` is the candidate row's support error.  Hence a vanishing-error packet
adapter must make a nonperturbative root or tail change at every charged
source row.  Merely concatenating, taking a subsequence, or making a small
seam repair cannot work.

Independently, the terminal gap gives a finite-dimensional capacity bound for
all accurate exact-Bellman packets in the behavioral payoff box.  This is the
correct complementary alternative: in a hypothetical counterexample branch,
arbitrarily large accurate raw capacity is impossible.  Proving it from the
source would instead contradict the branch and establish a uniform payoff.

## 2. Exact source data used

Let `source` be a `FinFourMinimumAtomProducer` in the singleton-atom arm, let

$$
 D_*:=D(\texttt{source.point.1})>0,
 \qquad \mu:=\texttt{source.point.2(some source.atom.terminal)}>0,
$$

and choose `0 < lambda < mu`.  The checked declaration

`FinFourMinimumAtomProducer.nonempty_minimumReturnForcedPairFamilyCapstone`

fixes one owner chronology and one table outsider before this resolution.  A
resolution capstone supplies a packet and a fixed payer `p`.  For every
selected index `n`, write

* `q_n` for `payerAdapter.sourceRoot`;
* `v_n` for the prescribed payoff coordinate of
  `payerAdapter.sourceTail`; and
* `a(q_n)` for root absorption.

The exact source fields used below are:

1. `payerDefect_floor`:

   $$
   d_p(q_n,v_n)\ge D_*/3;                               \tag{2.1}
   $$

2. the literal-pure-root construction used in
   `forcedPair_stageMass_eq_liveMass` (equivalently, its proof through
   `quittingProfileLiveRoot_literalPureRootProfile_self`):

   $$
   a(q_n)=1;                                             \tag{2.2}
   $$

   the checked `lambda_lt_forcedPairStageMass` additionally certifies that
   this sure-absorption row is reached with unconditional mass greater than
   `lambda` in its source profile;

3. `forcedPair_postDateSpine_eq_reference` and the corresponding cross-tail
   declarations: `v_n` is the literal post-date child of the displayed
   source row, not an independently selected continuation;

4. `forcedPairSpineDebtExcess_tendsto_zero`: the post-date source tails
   return to the minimum debt level.

No target profile is asserted cap--Nash or near-minimal, and no equality
identifies one edge's current value with the next edge's tail value.

## 3. The disconnected-charge theorem

### Theorem 3.1

For every natural number `N`, the first `N` selected forced-pair roots satisfy

$$
 \sum_{n<N}a(q_n)=N.                                    \tag{3.1}
$$

Each pair `(v_n,q_n)` is an exact one-row Bellman edge in the forward
orientation: prefixing the literal tail by `q_n` gives its actual current
payoff.  Nevertheless, for every

$$
 0\le\delta<D_*/3,                                     \tag{3.2}
$$

`q_n` is not `IsQuittingRootSupportApproxNash` against `v_n`, for every
`n`.  Therefore no finite sequence of these literal edges, in any order, is
a positive-charge `QuittingFiniteForwardPacket` at tolerance `delta`.

### Proof

At the selected date the forced-pair target profile is definitionally the
literal pure root of its routed two-player coalition.  Its conditional root
coalition probability, hence its total root absorption, is one.  Summing
proves (3.1).  Separately, `lambda_lt_forcedPairStageMass` proves that the
source actually reaches the row with mass greater than `lambda`; (3.1) is not
an artefact of conditioning on a null history.

For the strategic statement, support-`delta` endpoint optimality implies the
usual weighted endpoint `delta`-Nash condition by
`isQuittingRootEndpointNash_of_supportApproxNash`.  Equivalently, every
coordinate Nash defect is at most `delta`; this is
`isεQuittingRootNash_iff_coordinateNashDefect_le` after the standard endpoint
equivalence.  At the fixed payer, (2.1) would then give

$$
 D_*/3\le d_p(q_n,v_n)\le\delta,
$$

contrary to (3.2).  A forward packet requires the support field at every
row, so even one such literal charged row is forbidden.  QED.

The source therefore supplies arbitrarily large raw charge only after one
forgets both the support condition and the successor matching between
different edges.  This is exactly the distinction hidden by summing the
marked masses alone.

## 4. Quantitative root--tail perturbation moat

The preceding exclusion is robust and finite-dimensional.

### Lemma 4.1 (coordinate-defect Lipschitz bound)

Let `x,y` be two product roots on a finite player set, let `v,w` be two tail
vectors, and fix player `p`.  Suppose all reward coordinates and all
coordinates of `v,w` have absolute value at most `M`.  Put

$$
 \rho_i=|x_i-y_i|,
 \qquad \eta_p=|v_p-w_p|,
$$

where a root coordinate denotes its Quit probability.  Then

$$
 |d_p(x,v)-d_p(y,w)|
 \le \eta_p+2M\rho_p+4M\sum_{j\ne p}\rho_j.            \tag{4.1}
$$

### Proof

Against the opponents' product law, let `G_p(x_{-p},v)` be Quit payoff minus
Continue payoff.  The coordinate defect has the exact form

$$
 d_p(x,v)=(1-x_p)[G_p(x_{-p},v)]_+
          +x_p[-G_p(x_{-p},v)]_+.                       \tag{4.2}
$$

For fixed `x_p`, the right side is 1-Lipschitz in `G_p`; for fixed `G_p` it
is `|G_p|`-Lipschitz in `x_p`, and `|G_p|\le2M`.

Couple each opponent Bernoulli marginal maximally.  The probability that at
least one opponent action differs is at most
`sum_{j != p} rho_j`.  On a mismatch the Quit-minus-Continue sample value
changes by at most `4M`.  On a match the only tail dependence occurs when all
opponents Continue, and contributes at most `eta_p`.  Hence

$$
 |G_p(x_{-p},v)-G_p(y_{-p},w)|
 \le\eta_p+4M\sum_{j\ne p}\rho_j.
$$

Combining this with (4.2) proves (4.1).  QED.

### Corollary 4.2 (Fin4 source moat)

Let `(q_n,v_n)` be a forced-pair source row and let `(y,w)` be a proposed
replacement row with support error `delta >= 0`.  If

$$
 \|w-v_n\|_\infty\le\eta,
 \qquad \max_i|y_i-q_{n,i}|\le\rho,
$$

then

$$
 \boxed{D_*/3\le\delta+\eta+14M\rho}.                  \tag{4.3}
$$

Indeed support-`delta` gives `d_p(y,w)<=delta`; combine this with (2.1)
and Lemma 4.1, using one own coordinate and three opponent coordinates.  In
particular, keeping the root verbatim forces

$$
 \delta+\eta\ge D_*/3.                                 \tag{4.4}
$$

This excludes infinitesimal tail sewing of the source edges.  If both
`delta` and `eta` tend to zero, at least one Quit marginal must move a fixed
distance of order `D_*/M`.

## 5. Explicit fixed-carrier capacity barrier

The source's terminal-gap witness has some `gamma>0`.  Put

$$
 B=\operatorname{quittingRewardBound}(r),
 \qquad C=2+7B,
 \qquad
 \delta_*=
 \frac{(\sqrt{C^2+12\gamma}-C)^2}{144}.                 \tag{5.1}
$$

For `0<delta<delta_*`, let

$$
 N_\delta=\left\lceil\frac{6B}{\delta}\right\rceil+1. \tag{5.2}
$$

The behavioral payoff box `[-B,B]^(Fin 4)` has a sup-metric cover by at most
`N_delta^4` closed balls of radius `delta/3`.  The independently reviewed
compact-cover capacity theorem in
`CODEX_ADVERSARY__QUANTITATIVE_SUPPORT_PACKET_CAPACITY.md` therefore gives:

### Theorem 5.1

Every `QuittingFiniteForwardPacket` in the behavioral payoff box, with
support error `delta` and its required punishment-floor field, satisfies

$$
 \boxed{
 \sum_{t<H}a(q_t)<2N_\delta^4.}                         \tag{5.3}
$$

The proof is finite-dimensional.  If the charge reached the right side, the
grid labels would give two values in one `delta/3` cell with intervening raw
charge at least one.  Reversing that block produces a single-seam
projective lasso; the checked lasso/path compiler gives an unrestricted-
behavior terminal profile of exploitability at most

$$
 12\delta+2C\sqrt\delta<\gamma,
$$

contradicting the terminal-gap witness.

Thus, inside the positive-gap branch, an accurate source-realized forward
orbit cannot have arbitrary raw absorption.  This is not merely absence of a
current declaration: it is an explicit capacity barrier.  Conversely, any
proof that the forced-pair source does produce packets beyond (5.3), at every
small tolerance, is already a contradiction proof and hence a uniform-payoff
proof.

## 6. What remains genuinely open

The current source-to-capacity implication fails at two exact interfaces.

1. **Strategic repair.**  The source's charged literal roots have payer
   defect at least `D_*/3`.  By (4.3), vanishing support error requires a
   nonlocal root or continuation replacement; no small perturbation suffices.
2. **Successor compatibility.**  Each source row is a literal Bellman edge,
   but the current value of one selected edge is not identified with the tail
   value of the next.  Minimum return controls only the scalar debt of those
   tails, not their payoff-vector seam or a common behavioral continuation.

A valid producer must solve both simultaneously while retaining the
punishment floor.  Theorems 3.1 and 4.2 rule out the verbatim and
infinitesimal versions; Theorem 5.1 gives the exact quantitative target that
any successful nonlocal construction would have to violate and thereby
consume the counterexample branch.

## 7. Narrow source audit

Checked declarations inspected:

* `QuittingFiniteForwardPacket` and
  `exists_singleSeamProjectiveLasso_of_finiteForwardPackets` in
  `UniformEquilibrium/Quitting/Projective/FiniteForwardProjectiveLasso.lean`;
* `IsQuittingRootSupportApproxNash` in
  `UniformEquilibrium/Quitting/Boundary/Repair/SupportEnlargementAlternative.lean`;
* `isQuittingRootEndpointNash_of_supportApproxNash` in
  `UniformEquilibrium/Quitting/Paths/SupportWitnessClockCollapse.lean`;
* `quittingRootCoordinateNashDefect_eq_actionProbability_mul_posPart` and
  `isεQuittingRootNash_iff_coordinateNashDefect_le` in
  `UniformEquilibrium/Quitting/Root/NashDefect.lean`;
* `FinFourMinimumAtomProducer.nonempty_minimumReturnForcedPairFamilyCapstone`,
  `FinFourOwnerCompressedMinimumReturnForcedPairPacket.payerDefect_floor`,
  `lambda_lt_forcedPairStageMass`, `forcedPair_stageMass_eq_liveMass`,
  `forcedPair_postDateSpine_eq_reference`, and
  `forcedPairSpineDebtExcess_tendsto_zero` in
  `Research/Quitting/FinFourProducerAtlas/MinimumReturnForcedPair.lean`;
* `quittingProfileLiveRoot_literalPureRootProfile_self` in
  `Research/Quitting/SameStageEndpointMonodromy.lean`, used by the checked
  forced-pair stage-mass proof;
* `FinFourMinimumReturnPacket.tailDebt_tendsto_minimum` in
  `Research/Quitting/FinFourProducerAtlas/SourcePreservingCompletionAtlas.lean`;
* `exists_close_pair_with_large_charge_gap_of_finite_labels` in
  `MathUE/FiniteChargedReturn.lean`; and
* the downstream lasso/path declarations listed in
  `CODEX_ADVERSARY__QUANTITATIVE_SUPPORT_PACKET_CAPACITY.md`.

No literature claim is used.  No Lean file or export was changed.

## 8. Concrete next check

The minimal surviving producer question is no longer whether marked mass can
be summed.  It is:

> Can one use the paid endpoint move to construct a replacement root--tail
> pair lying outside the moat (4.3), yet with exact Bellman successor in the
> behavioral payoff box, support error tending to zero, and a punishment-
> floor-compatible successor that can be iterated?

Any positive answer reaches the finite-forward consumer; any negative answer
must control genuinely nonperturbative switches, since local compactness and
minimum-return debt convergence are now insufficient.
