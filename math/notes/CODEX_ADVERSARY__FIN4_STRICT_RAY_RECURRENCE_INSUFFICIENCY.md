# Strict-ray recurrence insufficiency in the Fin4 hard residual

**Identity:** CODEX_ADVERSARY  
**Date:** 2026-08-30  
**Status:** Proved in ordinary mathematics: neither the raw strict exact-cap
ray nor iteration of the current one-step paid/reset successor supplies either
recurrence target proposed in gpt/NONZERO_PERSIST_ATTEMPT_2.md. Every
sufficiently late positive-hazard exact block cut from either chain has a
uniform positive normalized endpoint seam, every increasing reverse-window
compactification of the raw ray converges to the
all-Continue phantom, and every indefinitely renewed maximal paid/reset chain
has summable total marginal hazard. A high-debt exact return would give a
genuine capacity-slice rank, but no inspected returned child has both the
required history compatibility and a uniform debt gap. This is a source-data
insufficiency theorem, not a proof of the Fin4 conjecture. The underlying
finite-stack debt estimates are Lean-checked; their assembly here is ordinary
mathematics.

## Question

Assume a four-player quitting table has no uniform-equilibrium payoff and
consider an actual strict forward exact-cap tail

\[
 (c_t,x_t)_{t\geq0}
\]

coming from the positive-minimum source, where

\[
 c_{t+1}=F_{x_t}(c_t),\qquad
 x_t\text{ is exact root Nash against }c_t.
\tag{1}
\]

Write

\[
 h_t=\sum_{i\in\operatorname{Fin}4}\Pr_{x_t}(i\text{ Quits}),\qquad
 H[a,b]=\sum_{t=a}^{b-1}h_t.
\]

The checked strict-ray interface gives \(h_t>0\),
\(\sum_th_t<\infty\), and \(c_t\to c_\infty\).

Can raw finite segments of this ray produce either:

1. normalized near-returns
   \(\lVert c_b-c_a\rVert_\infty/H[a,b]\to0\); or
2. a compact shift-invariant exact-spine hull excluding all all-Continue
   phantoms?

The answer is no for the raw ray data.

## 1. Cyclic closure of one exact open block

Consider any bounded finite exact Nash--Bellman block

\[
 B=(w_0,y_0,w_1,\ldots,y_{L-1},w_L),\qquad L\geq1,
\]

with

\[
 w_k=F_{y_k}(w_{k+1}),\qquad
 y_k\text{ exact root Nash against }w_{k+1}.
\]

Let

\[
 H(B)=\sum_{k<L}\sum_i\Pr_{y_k}(i\text{ Quits}),\qquad
 \Delta(B)=\lVert w_L-w_0\rVert_\infty.
\]

Close the block cyclically by retaining the phase values
\(w_0,\ldots,w_{L-1}\) and roots \(y_0,\ldots,y_{L-1}\), but feeding \(w_0\)
instead of \(w_L\) to the last root. This is a
QuittingReturnedProductBlock after the evident cyclic indexing.

### Lemma 1 (cyclic closure error)

For \(\operatorname{Fin}4\), the returned block satisfies

\[
 \operatorname{BellmanError}\leq4\Delta(B),\qquad
 \operatorname{EndpointRegret}\leq4\Delta(B).
\tag{2}
\]

Hence

\[
 \operatorname{BellmanError}+\operatorname{EndpointRegret}
\leq8\Delta(B).
\tag{3}
\]

### Proof

Every phase except the return phase remains exact. At the return phase, for
every coordinate \(i\),

\[
\begin{aligned}
 |w_{L-1,i}-F_{y_{L-1}}(w_0)_i|
 &=
 |F_{y_{L-1}}(w_L)_i-F_{y_{L-1}}(w_0)_i|\\
 &\leq\Delta(B),
\end{aligned}
\]

by one-row tail Lipschitz continuity. Summing over four coordinates gives the
first inequality in (2).

Exact root Nash at tail \(w_L\), together with
\(|w_{L,i}-w_{0,i}|\leq\Delta(B)\), gives
\(\Delta(B)\)-endpoint Nash at tail \(w_0\) by
isεQuittingRootEndpointNash_of_tail_close. The endpoint-regret summand for
one player is exactly its coordinate Nash defect. Therefore it is at most
\(\Delta(B)\) at the return phase and zero at every other phase. Summing over
four players proves the second inequality. ∎

The factor \(8\) is not important, but recording it prevents a hidden
phase-count factor: the estimate is independent of \(L\).

## 2. A hard-residual lower bound on normalized seams

The checked
hasAmbientReturnedBlockRelativeErrorGap_of_fourPlayer_counterexample says
that for every common coordinate bound \(K\), there are constants
\(\delta>0\) and \(\gamma>0\) such that every returned product block with

\[
 0<H\leq\delta
\]

obeys

\[
 \gamma H\leq
 \operatorname{BellmanError}+\operatorname{EndpointRegret}.
\tag{4}
\]

Combining (3) and (4) gives the following.

### Theorem 2 (small-hazard normalized-return exclusion)

For every bounded exact Fin4 Nash--Bellman block in a hypothetical
counterexample,

\[
 0<H(B)\leq\delta
 \quad\Longrightarrow\quad
 \boxed{\frac{\Delta(B)}{H(B)}\geq\frac{\gamma}{8}.}
\tag{5}
\]

This is an ordinary wrapper around the checked returned-block gap.

Apply it to a reversed strict-ray segment

\[
 c_b,x_{b-1},c_{b-1},\ldots,x_a,c_a.
\tag{6}
\]

Equation (1) makes (6) an exact chronological block with charge \(H[a,b]\)
and seam \(\lVert c_b-c_a\rVert_\infty\). Since \(h_t\) is nonnegative and
summable,

\[
 H[a,b]\leq\sum_{t\geq a}h_t\longrightarrow0
 \quad\text{uniformly in }b>a.
\]

Therefore there is \(A\) such that for every \(b>a\geq A\),

\[
 \boxed{
 \frac{\lVert c_b-c_a\rVert_\infty}{H[a,b]}
 \geq\frac{\gamma}{8}.}
\tag{7}
\]

In particular, no sequence of strict-ray intervals with \(a_n\to\infty\)
can satisfy the normalized near-return condition (NR) of Attempt 2.

This is stronger than the scalar ballistic illustration: the positive
normalized drift floor is forced by the actual Fin4 hard-residual
returned-block theorem.

## 3. Reverse-window compactification is forced to the phantom

For \(n\geq1\), read the first \(n\) forward ray edges chronologically
backwards. At chronological coordinate \(k<n\), its current value and root
are

\[
 V^{(n)}_k=c_{n-k},\qquad X^{(n)}_k=x_{n-1-k}.
\tag{8}
\]

Because \(\sum_th_t<\infty\), \(h_t\to0\). Every marginal Quit probability is
bounded by \(h_t\), so

\[
 x_t\longrightarrow C,
\tag{9}
\]

where \(C\) is the pure all-Continue root. Together with \(c_t\to c_\infty\),
for every fixed chronological coordinate \(k\),

\[
 (V^{(n)}_k,X^{(n)}_k)
 \longrightarrow(c_\infty,C).
\tag{10}
\]

### Theorem 3 (unique reverse-window limit)

Every projective/diagonal compact limit of reverse strict-ray blocks whose
lengths tend to infinity is

\[
 ((c_\infty,C),(c_\infty,C),\ldots).
\tag{11}
\]

The limit is an exact all-Continue phantom. Indeed, the exact finite-window
relations are closed; alternatively, the checked cap-limit inequality
\(r_i(\{i\})\leq c_{\infty,i}\) says directly that \(C\) is exact Nash
against \(c_\infty\).

The same proof applies to arbitrary intervals
\([a_n,b_n)\) with \(b_n-a_n\to\infty\): necessarily \(b_n\to\infty\), and
for fixed \(k\) the head coordinate uses time \(b_n-k\to\infty\).

Consequently, the compact hull canonically generated by longer and longer
raw reverse segments cannot exclude every all-Continue phantom. Its only
infinite raw-ray limit is already one.

## 4. Why the retained source mark does not survive

In the reverse word (8), the original source \(c_0\) is the terminal value at
coordinate \(n\). More generally, any fixed finite initial source fragment
at forward dates \(0,\ldots,J\) occurs only within \(J\) coordinates of the
terminal end. As \(n\to\infty\), those marked coordinates leave every fixed
head window.

Thus a terminal source flag, finite ancestry label, retained minimum-law
witness, or any other decoration supported on a fixed initial source
fragment converges pointwise to the unmarked stream. Adding a global tag that
is constant at every coordinate does not help Theorem 1: after forgetting
the tag, the root/value spine in (11) is still a forbidden phantom.

The precise surviving requirement is stronger:

> A source mark can exclude the phantom in a closed shift hull only if it is
> renewed at bounded gaps in the chronological direction, or if it forces a
> closed positive-activity condition at some bounded future coordinate.

Neither property is present in QuittingForwardExactCapTail. A renewable mark
is already a return/regeneration theorem, not bookkeeping added after
compactification.

## 5. What remains possible

The no-go is scoped to raw strict-ray segments and source decorations that
remain at their terminal end. It does not exclude:

1. a nonlocal handoff producing blocks that are not late subsegments of the
   strict ray;
2. an early anchor \(a\) with \(c_a=c_\infty\) and intervals
   \(b_n\to\infty\), for which the hazard need not vanish;
3. a renewable source regeneration that moves an actual minimum source back
   to bounded chronological distance; or
4. a direct terminal or rank consumer bypassing recurrence.

Cases 2--3 would already be new nonlocal source information. They are not
consequences of cap convergence, positive row activity, maximality, or the
retention of the time-zero source.

## 6. Exact cost of a high-debt return

There is a clean quantitative statement behind the proposed nonlocal route.
Let \(\pi\) be an actual terminal profile, let \(B\) be a finite exact
cap--Nash root stack, and write

\[
 D_1=D(\pi),\qquad
 D_0=D(B\mathbin{\|}\pi),\qquad
 P(B)=\prod_{r\in B}c(r),
\]

where \(c(r)\) is joint all-Continue probability. Put

\[
 A_w(B)=1-P(B),\qquad
 A_\Sigma(B)=\sum_{r\in B}(1-c(r)).
\]

Thus \(A_w\) is absorption before the suffix is reached and \(A_\Sigma\) is
the unweighted row-absorption charge.

### Theorem 4 (high-to-near-minimum return charge)

Assume (0<D_{\max}) and

\[
 0\leq\varepsilon<\delta,\qquad
 D_*+\delta\leq D_1\leq D_{\max},\qquad
 D_0\leq D_*+\varepsilon.
\tag{12}
\]

Then

\[
 A_\Sigma(B)\geq A_w(B)
   =\frac{D_1-D_0}{D_1}
   \geq\frac{\delta-\varepsilon}{D_{\max}}.
\tag{13}
\]

The same lower bound holds for the sum of the marginal hazards in \(B\).

### Proof

Exact cap--Nash prefixing gives

\[
 D_0=P(B)D_1.
\]

This is exactly
`quittingTerminalDebtSum_capNashRootStack_eq`. Hence the equality in (13)
holds. The two inequalities in (12) give
\(D_1-D_0\geq\delta-\varepsilon>0\), and
\(D_1\leq D_{\max}\) gives the last inequality. Finally
\(1-P(B)\leq A_\Sigma(B)\), and one-stage absorption is at most the sum of
the marginal quit probabilities. The checked theorem
`debtExcess_sub_error_div_debt_le_capNashStackAbsorptionSum` is the direct
unweighted version of the same calculation. `QED`

### Conditional capacity-slice consequence

Suppose a finite nonnegative source-history potential \(\Phi\) has the
genuine extension property

\[
 \Phi(s)\geq H(B)+\Phi(s')
\tag{14}
\]

whenever a returned child \(s'\) is attached to its parent \(s\) through the
literal exact block \(B\). If every recursive return satisfies (12) with one
fixed \(\delta>\varepsilon\), then with

\[
 \kappa=(\delta-\varepsilon)/D_{\max}>0
\]

equation (14) gives \(\Phi(s')\leq\Phi(s)-\kappa\). Therefore
\(\lceil\Phi/\kappa\rceil\) strictly decreases. This is a valid
natural-valued rank. The conclusion uses both parts of the contract: a
uniform gap and an injection of every child continuation into the same
parent history by literal concatenation. Equality of residuals, equality of
minimum debt, or construction of a new causal chronology does not imply
(14).

## 7. The current bounded-distance reset mark is real but summable

The present paid/reset packet does contain one renewable mark at uniformly
bounded chronological distance. In
`MaximalOneStepPaidResetRegeneration`, the descendant profile is literally
one maximal exact cap--Nash prefix of the source profile. The descendant keeps
the same positive minimum, the zero-debt reset coordinate, and positive
opponent incidence. Thus, as ordinary mathematics, the theorem
`maximalOneStepPaidResetRegeneration_or_uniqueAllContinue` may be reapplied to
the descendant. This is stronger than a recurrent finite tag: it is a nested
actual one-edge predecessor construction.

It nevertheless cannot create the required persistent clock.

### Theorem 5 (renewed reset-chain finite-hazard budget)

Let \(\sigma_n\) be any indefinitely iterated maximal paid/reset chain, let
\(r_n\) be its displayed maximal root, and put

\[
 D_n=D(\sigma_n),\qquad
 a_n=1-c(r_n),\qquad
 h_n=\sum_{i\in\operatorname{Fin}4}q_i(r_n).
\]

Here \(\sigma_{n+1}=r_n\mathbin{\|}\sigma_n\), and let \(D_*>0\) be the
common retained global minimum. Then

\[
 D_{n+1}=(1-a_n)D_n,
\tag{15}
\]

and for every \(N\),

\[
 D_*\sum_{n<N}a_n
 \leq D_0-D_N
 \leq D_0-D_*.
\tag{16}
\]

Consequently

\[
 \sum_na_n<\infty,
 \qquad
 \sum_nh_n\leq4\sum_na_n<\infty.
\tag{17}
\]

In particular no player has a nonsummable marginal along this regenerated
source-index word. If iteration stops instead, the checked alternative is
exactly `HasUniqueAllContinueAtCap`.

### Proof

The maximal root is exact cap--Nash, so the one-row debt identity gives (15).
Global minimality gives \(D_n\geq D_*\). Hence

\[
 D_n-D_{n+1}=a_nD_n\geq a_nD_*.
\]

Summing telescopes and proves (16). For every player, its marginal quit event
is contained in the event that somebody quits, so \(q_i(r_n)\leq a_n\).
There are four players, giving \(h_n\leq4a_n\) and (17). `QED`

Under the hypothetical no-uniform-payoff assumption, Theorem 2 also applies
to every sufficiently small positive-hazard finite block cut from these
nested prefixes after reversing it into chronological order. Since (17)
makes all late block hazards small, their normalized endpoint seam remains at
least \(\gamma/8\). Thus the renewable reset mark supplies neither
persistence nor normalized near-returns.

The scalar sequence

\[
 D_n=D_*+2^{-n},\qquad
 a_n=\frac{2^{-n-1}}{D_*+2^{-n}}
\tag{18}
\]

is the sharp interface regression: the same mark is renewed every one step,
every debt descent is strict, and (15) holds, but the drops and absorption
charges tend to zero and their total is finite. Therefore no theorem using
only finite-state mark recurrence, one-step exactness, and strict descent can
produce a uniform \(\kappa\).

## 8. Audit of the remaining proposed marks

1. **Minimum atom.** `FinFourMinimumAtomProducer` stores one minimum
   semantic/law point and a `QuittingMinimumLawCausalSuffixAtom`.
   `FinFourMinimumAtomChronology` supplies arbitrarily long exact prefix
   stacks, but the stacks for different ranks are not nested. Its marked atom
   lies in the suffix profile, with no bounded gap or child-extension field.

2. **Strict positive-root handoff.** A
   `FinFourStrictRayPositiveRootReturn` really is one exact semantic prefix,
   and `returnedDebt_eq_limit_sub_charge` is the one-row instance of (13).
   In the equality arm, however, `FinFourStrictRayMinimumLawHandoff.fresh` is
   obtained by causalizing the returned carrier point anew. Its fields are
   `residual_eq` and `point_eq`; there is no embedding of the fresh chronology
   into the incoming ray history. In the strict arm there is not even a child
   source. Thus this packet pays a one-time charge but does not preserve one
   history capacity across regeneration.

3. **Canonical support renewal.** The repository now has a genuine discrete
   renewable rank:
   `CanonicalPairMinimumEndpointSupportRankHandoff.nonempty_renewalCertificate`
   and `canonicalPairRenewableTransition_rank_lt`. Its recursive portion has
   length at most three because positive-debt support strictly shrinks. This
   correctly consumes the minimum-fibre support-descent lane, but terminates
   at positive tangent slope, flat support entry, or off-minimum paid first
   disagreement. The checked umbrella explicitly leaves their consumers
   conditional and supplies no horizontal Nash--Bellman compiler. It is not a
   persistent chronology.

4. **Normalized strict endpoint and three-role reset.** The normalized
   strict-endpoint equality arm retains actual profiles whose debts return to
   the minimum, but `StrictEndpointNormalizedReturn.lean` explicitly does not
   transport exactness across the horizontal paid update. The three-role
   ascent reset has a positive `riseScale` and a pure-time path of length at
   most seven, but those unilateral strategy updates are not cap--Nash
   Bellman rows. Its fixed-law `returned` object is a carrier point, not a
   literal history child. Neither object satisfies (14).

5. **Deadline row.** A
   `QuittingFiniteDeadlineCompatibleNashFamily` would be a renewable
   projective mark and already implies a uniform-equilibrium payoff. The
   current producer proves only deadlinewise Nash existence.
   `HasFiniteCompatibleQuittingTimingNashChains` and the compact adapter
   `FiniteCompatibleChainsProduceProjectiveNashFamily` remain hypotheses;
   independently selected adjacent deadlines are not an inverse system.

The precise surviving source obligation is therefore not “find a finite
mark.” One such mark and even one nested exact reset successor already exist.
What is missing is either a direct consumer for the unique-all-Continue/inert
and renewable terminal exits, or a returned child carrying both a uniform
high-debt gap and the literal extension map required by (14).

## Boundary tests

1. **Ballistic scalar flow.** If
   \(c_{t+1}-c_t=h_td\), \(h_t>0\), and \(\sum_th_t<\infty\), then every
   interval has
   \[
   |c_b-c_a|/H[a,b]=|d|.
   \]
   This realizes the qualitative behavior of (7).

2. **Exact positive return.** If \(\Delta(B)=0<H(B)\), cyclic repetition is
   an exact persistent spine. For \(H(B)\leq\delta\), (4) forbids such a
   block in a hypothetical Fin4 counterexample.

3. **Escaping mark.** A flag placed at the terminal coordinate of a
   length-\(n\) reverse word is zero at every fixed coordinate for all large
   \(n\). Its product-topology limit cannot distinguish the phantom.

4. **Renewed but vanishing mark.** Equation (18) renews the same label every
   step and has a strict exact debt drop every time. Bounded return time alone
   does not give a uniform capacity slice.

## Source audit

I inspected:

- QuittingForwardExactCapTail, its exactNash and forward fields,
  totalHazard_summable, cap_tendsto, and singleton_le_capLimit in
  Research/Quitting/ForwardExactCapTailFlow.lean;
- quittingTerminalSemanticPrefix_envelope_eq_rootSuccessorPayoff_of_capNash
  in
  UniformEquilibrium/Diagnostics/Quitting/TerminalCapNashEndpointTransport.lean,
  which supplies equation (1) for cap coordinates;
- QuittingReturnedProductBlock, bellmanError, endpointRegret,
  relativeError_gap_of_noHomogeneous, and
  hasHomogeneousSimplexSolution_of_vanishing_returnedBlocks in
  UniformEquilibrium/Quitting/Stationary/ReturnedBlockTangentObstruction.lean;
- HasAmbientReturnedBlockRelativeErrorGap and
  hasAmbientReturnedBlockRelativeErrorGap_of_fourPlayer_counterexample in
  UniformEquilibrium/Diagnostics/Quitting/FourPlayerReturnedBlockGap.lean;
- isεQuittingRootEndpointNash_of_tail_close in
  UniformEquilibrium/Quitting/Root/TailStability.lean;
- quittingRootCoordinateNashDefect_eq_actionProbability_mul_posPart and
  quittingRootTotalNashDefect_le_card_mul_of_isεQuittingRootNash in
  UniformEquilibrium/Quitting/Root/NashDefect.lean;
- all_marginalQuitHazards_summable_of_no_uniformPayoff in
  UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/FullSupportHardNashBellmanSpine.lean;
- quittingTerminalDebtSum_capNashRootStack_eq and
  debtSumInf_mul_capNashStackAbsorptionSum_le_debtDrop in
  UniformEquilibrium/Diagnostics/Quitting/TerminalCapNashChronology.lean;
- debtExcess_sub_error_div_debt_le_capNashStackAbsorptionSum in
  UniformEquilibrium/Diagnostics/Quitting/TerminalCapNashRenewalObstruction.lean;
- FinFourMinimumAtomProducer in
  Research/Quitting/FinFourProducerAtlas/Source.lean and
  FinFourMinimumAtomChronology in
  Research/Quitting/FinFourProducerAtlas/MinimumSingletonClockCompression.lean;
- FinFourStrictRayPositiveRootReturn,
  returnedDebt_eq_limit_sub_charge, and
  FinFourStrictRayMinimumLawHandoff in
  Research/Quitting/FinFourProducerAtlas/StrictRayPositiveRootReturn.lean;
- MaximalOneStepPaidResetRegeneration and
  maximalOneStepPaidResetRegeneration_or_uniqueAllContinue in
  Research/Quitting/PaidCapMaximalOneStepRegeneration.lean;
- CanonicalPairRenewalCertificate,
  canonicalPairRenewableTransition_rank_lt, and
  nonempty_renewalCertificate in
  Research/Quitting/FinFourProducerAtlas/CanonicalPairRenewableSourceRank.lean;
- consume_renewalTerminalExit and the conditional
  exists_uniformEquilibriumPayoff_of_renewalExitConsumers in
  Research/Quitting/FinFourProducerAtlas/CanonicalPairMinimumEndpointRenewal.lean;
- the actualizer interfaces and no-horizontal-exactness boundary in
  Research/Quitting/FinFourProducerAtlas/StrictEndpointNormalizedReturn.lean;
- FinFourThreeRoleAscentResetHandoff, riseScale, and length_le_seven in
  Research/Quitting/FinFourProducerAtlas/ThreeRoleAscentResetHandoff.lean;
- QuittingFiniteDeadlineCompatibleNashFamily and its uniform-payoff consumer
  in
  UniformEquilibrium/Diagnostics/Quitting/FiniteDeadlineProjectiveCompatibility.lean,
  and HasFiniteCompatibleQuittingTimingNashChains in
  Research/Quitting/FiniteDeadlineCompatibleNashChains.lean;
- Theorems 1--3 and the strict-ray orientation in
  gpt/NONZERO_PERSIST_ATTEMPT_2.md.

All deductions in this note are ordinary mathematics assembled from those
interfaces. No Lean implementation was attempted.

## Concrete next question

Can one of the three canonical renewal terminal exits or the unique
all-Continue paid/reset cap produce a returned **literal exact history child**
with fixed constants \(\delta>\varepsilon\geq0\), so that:

\[
 D_{\rm tail}\geq D_*+\delta,\qquad
 D_{\rm head}\leq D_*+\varepsilon,
\]

and every continuation of the child embeds by concatenation into the same
parent history capacity?

Theorem 4 would then give the natural capacity-slice rank. Theorem 5 shows why
the present one-step reset renewal is insufficient without the uniform gap,
and Theorem 3 rules out recovering the missing extension map by an unmarked
diagonal compact limit.
