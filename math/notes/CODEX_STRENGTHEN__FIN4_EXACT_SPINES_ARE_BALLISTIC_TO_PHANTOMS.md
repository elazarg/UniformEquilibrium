# Fin4 hard exact spines are ballistic into phantoms

**Identity:** CODEX_STRENGTHEN  
**Date:** 2026-08-30  
**Status:** The requested persistent-spine producer remains open.  This note
independently verifies the three conditional mechanisms in
`gpt/NONZERO_PERSIST_ATTEMPT_2.md` and proves a sharper hard-residual no-go:
under the hypothetical Fin4 counterexample hypothesis, every canonical exact
Nash--Bellman spine converges in its whole shift to an all-Continue phantom,
while every sufficiently late positive-hazard window has endpoint seam at
least a fixed positive multiple of its total marginal hazard.  Consequently
neither cofinal window cutting nor ordinary compact shift closure can supply
the proposed source lemma.  Any normalized-return producer must be nonlocal
and, after the hard gap is used, must actually produce blocks with a uniform
positive hazard floor.  The assembly below is ordinary mathematics from the
named checked declarations; no new Lean theorem is claimed.

This note continues
[`CODEX_STRENGTHEN__FIN4_NONZERO_PERSISTENT_SPINE_SELECTION.md`](CODEX_STRENGTHEN__FIN4_NONZERO_PERSISTENT_SPINE_SELECTION.md)
and should be compared with the independently written strict-ray audit
[`CODEX_ADVERSARY__FIN4_STRICT_RAY_RECURRENCE_INSUFFICIENCY.md`](CODEX_ADVERSARY__FIN4_STRICT_RAY_RECURRENCE_INSUFFICIENCY.md).

## 1. Precise question

Fix a reward table

\[
 r:\{S\subseteq\operatorname{Fin}4:S\ne\varnothing\}\longrightarrow
 \mathbb R^4
\]

and suppose, for contradiction, that it has no uniform-equilibrium payoff.
For a canonical exact Nash--Bellman spine write

\[
 v_t=F_{x_t}(v_{t+1}),\qquad
 x_t\text{ exact root Nash against }v_{t+1},
\]

and

\[
 q_{t,i}=\Pr_{x_t}(i\text{ Quits}),\qquad
 h_t=\sum_iq_{t,i}.
\]

For a finite chronological block cut from dates \([a,b)\), put

\[
 H[a,b]=\sum_{t=a}^{b-1}h_t,
 \qquad
 \Delta[a,b]=\lVert v_b-v_a\rVert_\infty.
\]

The two proposed source targets in Attempt 2 were:

1. late exact blocks with positive charge and
   \(\Delta[a_n,b_n]/H[a_n,b_n]\to0\); or
2. a nonempty compact forward-shift-invariant family of exact spines that
   contains no constant all-Continue phantom.

The results below show that neither target is obtainable by cutting or
compactifying any already supplied exact spine in the hard residual.

## 2. Narrow checked source audit

I read `SOURCES.md`, `GOAL.md`, the question, the relevant exact-spine and
strict-ray rows of `docs/TOOLKIT.md` and `docs/FRONTIER.md`, Attempt 2 and its
adversarial review, and the following Lean declarations.

1. `IsCanonicalExactQuittingNashBellmanSpine` in
   `UniformEquilibrium/Quitting/Bellman/Finite/NashBellmanClockReduction.lean`
   supplies the canonical reward-cube bound, exact Bellman recursion, and
   exact root Nash at the literal successor value.
2. `FinFourQuantitativeFullSupportHardResidual.all_marginalQuitHazards_summable`
   and `all_marginalQuitHazards_summable_of_no_uniformPayoff` in
   `UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/FullSupportHardNashBellmanSpine.lean`
   state that, in the Fin4 hard residual, every marginal of every supplied
   canonical exact spine is summable.
3. `HasAmbientReturnedBlockRelativeErrorGap` and
   `hasAmbientReturnedBlockRelativeErrorGap_of_fourPlayer_counterexample` in
   `UniformEquilibrium/Diagnostics/Quitting/FourPlayerReturnedBlockGap.lean`
   give constants \(\delta,c>0\), uniform over all returned product blocks in
   the canonical payoff cube, such that

   \[
    0<H\le\delta\quad\Longrightarrow\quad
    cH\le \operatorname{BellmanError}+\operatorname{EndpointRegret}.
   \]

4. `QuittingReturnedProductBlock`, `totalHazard`, `bellmanError`, and
   `endpointRegret` are in
   `UniformEquilibrium/Quitting/Stationary/ReturnedBlockTangentObstruction.lean`.
   The tail perturbation estimate is
   `isεQuittingRootEndpointNash_of_tail_close` in
   `UniformEquilibrium/Quitting/Root/TailStability.lean`.
5. `QuittingTerminalExploitabilityWitness.nonempty_positiveDebtDynamicTailWitness`
   in
   `UniformEquilibrium/Diagnostics/Quitting/Chronology/PositiveDebtDynamicTailWitness.lean`
   constructs an actual optimized dynamic tail from the terminal
   exploitability witness carried by the hard residual.
   `QuittingPositiveDebtDynamicTailWitness.isCanonicalExactNashBellmanSpine`,
   `not_exists_sublinearAbsorptionReturn`, and
   `exists_pos_eventually_endpointDistance_ge_absorptionMass` are in
   `UniformEquilibrium/Diagnostics/Quitting/Chronology/AbsorptionClockBallisticity.lean`.
   The last theorem is a checked, source-typed absorption-clock version of
   the ballistic conclusion proved below for marginal hazard.
6. The strict forward exact-cap ray and its summable hazard clock are in
   `Research/Quitting/ForwardExactCapTailFlow.lean`.  Its reversed windows
   are exact chronological blocks after using
   `quittingTerminalSemanticPrefix_envelope_eq_rootSuccessorPayoff_of_capNash`
   from
   `UniformEquilibrium/Diagnostics/Quitting/TerminalCapNashEndpointTransport.lean`.

The two generic conclusions in Sections 4--5 below are not present as the
exact Lean declarations stated here.

## 3. Independent audit of Attempt 2, Theorems 1--3

### 3.1 Minimal compact component

Theorem 1 is correct with an **inclusive** disjunction.

Let \(K\) be a nonempty compact forward-invariant family of exact bounded
spines and let \(S\) be the left shift.  A minimal nonempty compact
forward-invariant subset \(M\) exists by the nested-intersection argument.
For every \(z\in M\), the closure of its forward orbit is again nonempty,
compact, forward invariant, and contained in \(M\); minimality makes that
orbit dense in \(M\).

For the continuous activity

\[
 h(z)=\sum_iq_{0,i}(z),
\]

if \(h(z_*)>\delta>0\) somewhere on \(M\), density and compactness give one
integer \(L\) such that every forward orbit meets \(\{h>\delta\}\) within
the next \(L+1\) dates.  Applying this on disjoint blocks of \(L+1\) dates
gives divergent total activity.  Finiteness of the player set gives one
fixed divergent marginal.

If \(h\equiv0\) on \(M\), every root is all Continue.  Bellman recursion
makes every value stream constant, and exact Nash says
\(r_i(\{i\})\le b_i\).  Each resulting constant spine is itself an invariant
singleton, so minimality makes \(M\) one such singleton.

The alternatives need not be exclusive for the original \(K\): a compact
invariant set may contain both a persistent component and a phantom
component.

### 3.2 Phantom omega-limit

Theorem 2 is correct.  If all marginals are summable, then the stage
absorption probabilities \(\alpha_t\) are summable because

\[
 0\le\alpha_t\le h_t.
\]

If rewards and annotations are bounded by \(K\), exact Bellman recursion
gives

\[
 \lVert v_t-v_{t+1}\rVert_\infty\le 2K\alpha_t.
\tag{1}
\]

Thus \(v_t\to b\).  Every \(q_{t,i}\to0\), hence \(x_t\to C\), the pure
all-Continue root.  For every fixed offset \(k\),

\[
 (v_{n+k},x_{n+k})\longrightarrow(b,C),
\]

so the entire shifted spine converges in the countable product topology to
the constant stream \(((b,C),(b,C),\ldots)\).  Closedness of exact root Nash
gives \(r_i(\{i\})\le b_i\), making this limit an exact phantom.

Only the omega-limit is necessarily constant.  A nonminimal all-summable
spine can have a transient nonconstant prefix.

### 3.3 Normalized-return amplification

Theorem 3 is correct as a **summable-residual**, not exact-spine, producer.
For exact blocks \(B_n\) with charge \(H_n>0\), endpoint seam \(\Delta_n\),
common endpoint limit, and \(\Delta_n/H_n\to0\), repeat block \(n\)

\[
 m_n=\left\lceil\frac1{H_n}\right\rceil
\]

times.  Then \(m_nH_n\ge1\) while

\[
 m_n\Delta_n\le \frac{\Delta_n}{H_n}+\Delta_n.
\tag{2}
\]

A fast subsequence makes (2), and the seams between consecutive block
groups, absolutely summable.  The resulting one chronology has divergent
total activity and hence one fixed persistent label.

There is a small quantitative sharpening.  In a quitting root, replacing a
tail \(w\) by \(w'\) at sup distance \(d\) changes the successor payoff by
at most \(d\) and transfers exact endpoint Nash to endpoint \(d\)-Nash, by
`isεQuittingRootEndpointNash_of_tail_close`.  Thus the sharp local Nash seam
is \(d\), not the generic normal-form bound \(2d\).  The conservative factor
two used in Attempt 2 remains valid.

The output of Theorem 3 is not an exact spine.  To reach unrestricted
behavioral deviations it still needs the two summable-residual adapters
isolated in the earlier owned note: the two-persistent chronological seam
consumer, or the punishment-normal unique-persistent terminal consumer.
Those wrappers are paper-level obligations; the exact-spine consumers cannot
be invoked verbatim.

## 4. Generic hard-residual ballisticity of every exact spine

The key point is that the hard returned-block gap applies to a cyclic closure
of any finite exact chronological block.

### Lemma 4.1 (cyclic closure costs at most eight endpoint seams)

Let

\[
 B=(w_0,y_0,w_1,\ldots,y_{L-1},w_L),\qquad L\ge1,
\]

be an exact Fin4 Nash--Bellman block.  Put

\[
 H(B)=\sum_{k<L}\sum_iq_i(y_k),\qquad
 \Delta(B)=\lVert w_L-w_0\rVert_\infty.
\]

Make a returned product block with phase values
\(w_0,\ldots,w_{L-1}\), the same roots, and with the last phase returning to
\(w_0\) instead of using \(w_L\).  Then

\[
 \operatorname{BellmanError}\le4\Delta(B),\qquad
 \operatorname{EndpointRegret}\le4\Delta(B).
\tag{3}
\]

All phases except the last remain exact.  At the last phase, successor-payoff
tail stability bounds each of the four coordinate Bellman residuals by
\(\Delta(B)\).  Exact endpoint Nash at \(w_L\) transfers to endpoint
\(\Delta(B)\)-Nash at \(w_0\).  For one player the two endpoint-regret terms
have opposite signs before taking positive parts, so at most one is positive;
their sum is at most \(\Delta(B)\).  Summing four coordinates proves (3).
In particular,

\[
 \operatorname{BellmanError}+\operatorname{EndpointRegret}
 \le8\Delta(B).
\tag{4}
\]

The bound is independent of the block length.

### Theorem 4.2 (uniform late-window marginal-hazard speed)

Assume the Fin4 game has no uniform-equilibrium payoff.  There is one
constant \(\kappa>0\), depending only on the reward table, such that for
every canonical exact Nash--Bellman spine \((v,x)\), there is a date
\(A=A(v,x)\) satisfying

\[
 b>a\ge A,\quad H[a,b]>0
 \quad\Longrightarrow\quad
 \boxed{\kappa H[a,b]\le\Delta[a,b].}
\tag{5}
\]

#### Proof

Use the canonical bound \(K=\operatorname{quittingRewardBound}(r)\) in
`hasAmbientReturnedBlockRelativeErrorGap_of_fourPlayer_counterexample`.
Obtain \(\delta,c>0\).  Lemma 4.1 and the returned-block gap imply, for every
bounded exact block,

\[
 0<H(B)\le\delta
 \quad\Longrightarrow\quad
 cH(B)\le8\Delta(B).
\tag{6}
\]

The checked hard-spine theorem makes every marginal \((q_{t,i})_t\)
summable.  Hence \(h_t=\sum_iq_{t,i}\) is summable.  Choose \(A\) so that

\[
 \sum_{t\ge A}h_t\le\delta.
\]

Every window beginning after \(A\) has \(H[a,b]\le\delta\), so (6) applies
with \(\kappa=c/8\).  \(\square\)

This is stronger than the scalar ballistic example and stronger than a
statement only about the selected maximal ray: it covers **every** supplied
canonical exact spine, with a speed constant uniform across spines.

### Corollary 4.3 (no cofinal normalized return)

For any sequence of positive-hazard windows of one exact spine with
\(a_n\to\infty\),

\[
 \liminf_n\frac{\Delta[a_n,b_n]}{H[a_n,b_n]}\ge\kappa>0.
\tag{7}
\]

Thus the normalized-return criterion in Attempt 2 cannot be obtained from
late windows of the strict ray, the optimized dynamic tail, or any other
single exact hard-residual spine.

The optimized dynamic tail has an independent checked strengthening in the
literal absorption clock:
`exists_pos_eventually_endpointDistance_ge_absorptionMass` gives
\(s>0\) and a threshold such that every late positive-absorption window
satisfies

\[
 s\,A[a,b]\le\lVert v_b-v_a\rVert,
\]

where \(A[a,b]\) is the window's actual absorbed probability, including its
survival weights.  Its proof uses the terminal exploitability packet defect,
punishment-floor provenance, normalized singleton occupation, and unrestricted
late window lengths.  It is not merely an abstract scalar regression.

## 5. Every compact invariant exact-spine family captures a phantom

### Theorem 5.1 (hard-residual phantom capture)

Assume again that the Fin4 game has no uniform-equilibrium payoff.  Let
\(K\) be any nonempty compact family of canonical exact Nash--Bellman spines
with

\[
 S(K)\subseteq K.
\]

Then \(K\) contains a constant all-Continue phantom.

#### Proof

Choose \(z=(v,x)\in K\).  The hard-spine theorem makes every marginal of
\(z\) summable.  The audited phantom omega-limit theorem gives

\[
 S^nz\longrightarrow ((b,C),(b,C),\ldots)
\]

for some \(b\) with \(r_i(\{i\})\le b_i\).  Forward invariance puts every
\(S^nz\) in \(K\), and compact subsets of the spine product are closed.
Thus the phantom limit belongs to \(K\).  \(\square\)

This sharpens the source-facing reading of Attempt 2.  Under the hard
hypothesis, a phantom-free compact invariant exact-spine family is not a
milder object waiting to be selected from already known exact spines: its
existence is itself a contradiction certificate.

The same no-go survives compact decorations.  If a compact marked system
has a continuous shift-equivariant projection to ordinary exact spines, its
projected image is nonempty, compact, and forward invariant, so it contains
an underlying phantom.  A mark can help only if it changes the executable
object or is renewed by a nontrivial source theorem; bookkeeping whose
continuous projection forgets to the ordinary spine cannot make the
minimal-component activity argument avoid the zero-activity fiber.

## 6. Strongest reduced producer obligation

Suppose a family of exact blocks satisfies the common-endpoint and normalized
return assumptions of Attempt 2:

\[
 w^n_0,w^n_{L_n}\to b,qquad H_n>0,qquad
 \frac{\Delta_n}{H_n}\to0.
\tag{8}
\]

In the hypothetical counterexample, the returned-block gap and Lemma 4.1
show that \(H_n\le\delta\) is impossible for all sufficiently large \(n\).
Indeed, on that subsequence (6) would give
\(\Delta_n/H_n\ge c/8\).  Therefore (8) automatically upgrades, after
discarding finitely many blocks, to

\[
 \boxed{H_n>\delta>0.}
\tag{9}
\]

This is the sharpest useful reformulation of the residual.  The source no
longer needs a subtle little-o return at a vanishing clock.  It must produce
a **macroscopic exact recurrence**:

> There are exact chronological blocks from the actual hard source, both
> endpoints converge to one payoff vector, and every block carries at least
> one fixed positive amount of total marginal hazard.

With (9), one copy of each block already contributes a fixed charge.  A fast
subsequence makes the endpoint seams summable, and the Attempt 2 seam
amplifier gives one summable-residual chronology with a fixed persistent
label.  Repetition by \(\lceil1/H_n\rceil\) is unnecessary.

Theorems 4.2 and 5.1 show why this recurrence cannot be extracted from one
cofinal exact source orbit: that orbit has finite total hazard and converges
to its phantom.  A successful producer must therefore be nonlocal.  It must
regenerate new exact blocks while keeping their endpoints in a common compact
cluster and retaining a fixed positive charge per regeneration.  Equality of
terminal laws, convergence of caps, or a source mark escaping to the far end
does not supply this.

## 7. Boundary checks

1. **All-Continue phantom.**  It has \(H=0\) on every window, so (5) says
   nothing and Theorem 5.1 correctly retains it.
2. **Summable but nonconstant spine.**  Such a spine may have transient
   nonconstant roots, but its shifts still converge to the phantom.  Thus
   Theorem 5.1 does not incorrectly claim that the original spine is
   constant.
3. **Ballistic scalar model.**  If
   \(v_{t+1}-v_t=h_td\), with \(h_t>0\) summable and \(d\ne0\), then every
   interval has \(\Delta/H=\lVert d\rVert\).  This is consistent with (5).
4. **Exact positive return.**  If one exact block has \(H>0\) and
   \(\Delta=0\), cyclic repetition is an exact persistent spine.  In the
   counterexample hypothesis, (6) rules this out whenever \(H\le\delta\);
   the persistent-spine consumers rule it out at any scale.
5. **Persistent-label count.**  The minimal-component and block arguments
   yield divergence of total activity.  Finiteness gives one fixed label.
   Whether exactly one or at least two labels persist is a downstream split,
   not a producer ambiguity.

## 8. Declaration-level handoff

The following wrappers would record the strongest surviving mathematics
without reimplementing current exact consumers.

1. `QuittingFiniteExactNashBellmanBlock.returnedClosure` and
   `returnedClosure_totalError_le_card_mul_two_mul_endpointDist`:
   construct the cyclic returned product block and prove (3)--(4).
2. `eventually_endpointDist_ge_const_mul_totalHazard_of_finFour_noUniformPayoff`:
   combine the returned-block gap with
   `all_marginalQuitHazards_summable_of_no_uniformPayoff` to prove (5),
   uniformly over all late windows of a supplied canonical exact spine.
3. `compact_forwardInvariant_exactSpines_contains_allContinuePhantom_of_finFour_noUniformPayoff`:
   formalize Theorem 5.1.  The only new topology is whole-shift convergence;
   coordinatewise convergence follows from (1) and marginal hazards tending
   to zero.
4. `normalizedReturnBlocks_eventually_totalHazard_gt_gapThreshold`:
   under (8), use the same returned-block gap to prove (9).

The optimized dynamic-tail theorem
`exists_pos_eventually_endpointDistance_ge_absorptionMass` should be reused
as the stronger source-specific absorption-clock statement, not reproved.
Likewise, the exact unique-persistent compiler and exact Fin4
all-marginal-summability theorem already exist; only any desired
summable-residual wrappers remain separate obligations.

## 9. Conclusion and one next obligation

Attempt 2's three abstract theorems survive audit, with an inclusive
disjunction in Theorem 1, a nonconstant-transient caveat in Theorem 2, and an
explicit summable-residual handoff in Theorem 3.  They do not produce the
missing source object.

The strongest hard-compatible regression is now exact: every canonical exact
Fin4 spine in a hypothetical counterexample is a finite-hazard ballistic
approach to an all-Continue phantom.  Its late windows cannot be normalized
near-returns, and every ordinary compact forward hull containing it captures
the phantom.

The one remaining producer obligation is therefore:

\[
 \boxed{
 \text{Construct nonlocal actual-source exact blocks }B_n
 \text{ with }w^n_0,w^n_{L_n}\to b
 \text{ and }H(B_n)\ge\eta>0.}
\]

Any weaker cofinal-window or unmarked compactification claim is ruled out by
the theorems above.

## 10. Audit of the uniformly reached post-mark two-cut source

The relevant current atlas object should be called a **uniformly reached
post-mark two-cut block**, with literal dates

\[
 \operatorname{entryCut}_n<\operatorname{exitCut}_n
\]

inside one post-mark continuation.  Calling it a “C1/C2 block” obscures the
essential same-witness requirement.  I checked the current source packet
against this formulation.  It does **not** supply the required exact
macroscopic recurrence.

### 10.1 What is already same-witness and literal

For a `FinFourMinimumReturnPacket`, let \(m_n\) be the stored frame stage and
let

\[
 s_n=\operatorname{quittingAllContinueProfileSpine}
       (\operatorname{packet.stream.frame}n).\operatorname{targetProfile}
       (m_n+1).
\]

The following declarations establish genuine same-witness provenance:

- `FinFourStabilizedForcedPairStream.tail_eq_framePostDateTail` identifies
  the semantic pair of \(s_n\) with the packet's stored tail;
- `FinFourMinimumReturnPacket.tailDebt_tendsto_minimum` gives
  \(D(s_n)\to D_*\);
- `FinFourStabilizedForcedPairStream.forcedPair_postDateSpine_eq_reference`
  and `.payerTarget_postDateSpine_eq_reference` identify the complete
  post-date behavioral spine across the forced and paid siblings; and
- `FinFourMinimumReturnPacket.forcedPairTail_eq_tail` and
  `.normalizedDecoratedFamily_postDateSpine_eq_reference` retain the same
  post-mark object in the consumer packet.

Thus the current source has the correct **entrance port**: a literal
near-minimum behavioral continuation after the retained mark.  This is
stronger than equality of carrier points or rank labels.

### 10.2 The exact root word is upstream and loses all macroscopic charge

The only stored exact cap--Nash word is `frame.rootStack`.  Its source
identity and exactness are

- `FinFourSourcePreservingSingletonFrame.referenceProfile_eq_literalRootStack`;
  and
- `FinFourSourcePreservingSingletonFrame.rootStack_nash`.

It is not a word inside \(s_n\).  In the selected-row construction,
`QuittingNonsingletonMinimumLawTransfer.shiftedStage` places the marked stage
after the complete root stack.  In the owner-clock construction,
`FinFourOwnerCompressedSingletonEndpoint.anchor_le_selectedStage` gives the
same orientation.  Since \(s_n\) begins at \(m_n+1\), the stored exact word
lies before, not after, its entrance.

Even ignoring orientation, it cannot provide the required
\(H\ge\eta>0\).  The checked theorem
`QuittingNonsingletonMinimumLawTransfer.tendsto_capNashStackContinueProduct_one`
gives

\[
 P_n:=\prod_{x\in\operatorname{rootStack}_n}
       \prod_i(1-q_i(x))\longrightarrow1.
\]

Eventually \(P_n>0\), and

\[
 0\le H_n^{\rm stack}:=
   \sum_{x\in\operatorname{rootStack}_n}\sum_iq_i(x)
 \le-\log P_n\longrightarrow0.
\]

Every subword has at most this hazard.  Hence the packet's only exact word
fails the macroscopic floor on every cofinal subsequence.

### 10.3 The positive charge is the mark, not a post-mark recurrence

The named positive-mass fields are

- `FinFourSourcePreservingForcedPairPacket.resolution_le_forcedPairStageMass`;
- `.payerRoutedStageMass_eq_forcedPairStageMass`; and
- `FinFourMinimumReturnPacket.minimumTailSource`.

They concern the forced-pair row at date \(m_n\).  The desired post-mark
continuation begins at \(m_n+1\).  No named declaration places another
positive-mass row, or any positive-hazard interval, later inside \(s_n\).
Nor does a declaration say that the whole semantic pair of the forced or paid
parent itself returns to the same endpoint cluster.  Thus the charged mark
cannot simultaneously serve as `entryCut`, preserve itself as an upstream
finite cylinder, and furnish a later recurrent `exitCut`.

Finally,
`FinFourMinimumReturnPacket.drop_row`, `.drop_frame`, and
`FinFourMinimumReturnTrajectory.packet_succ` only reindex the rank stream.
They do not assert

\[
 s_{n+1}=\operatorname{suffix}_{L_n}(s_n).
\]

The next rank's marked row therefore cannot be treated as a later play date
of the current rank's post-mark continuation.

### 10.4 Comparison with the chronological two-cut construction

There is a different approximate source interface.  From
`QuittingFiniteCDFCut.nonempty_quittingFiniteCDFCut`, together with
`tendsto_chronologicalClockCDF_of_continuousAt` and
`tendsto_chronologicalCoalitionCDF_of_clockCDF_continuousAt`, two continuity
levels can be cut in one completed source root sequence.  This ordinary
two-cut construction can retain:

- the two literal dates on one source rank;
- positive limiting reach at the exit;
- a fixed positive conditional absorption, hence marginal-hazard, floor; and
- exact Bellman evaluation by the actual suffix values.

It still does not instantiate the present exact-block producer.
`QuittingRootSequenceAbsorbingCompletionDiagonal.nash` certifies only
`completedError rank`-Nash, and `.completedError_tendsto_zero` makes that
error vanish; it is not exact root Nash.  The endpoint theorem
`tailVector_tendsto_absorptionPathPayoff_of_cumulativeSubsequenceCuts`
identifies the two endpoint limits as the path payoffs at the two selected
clock levels, generally two different vectors.  No named declaration makes
their difference vanish or little-o of the fixed block hazard.  At one
single adjacent clock level,
`tendsto_rootAbsorptionMass_zero_of_adjacentClocks` instead forces the local
charge to vanish and the fixed-column limit is all Continue.

The stronger geometric-level decoder proposed in Section 18 of
`CODEX_SOURCE_GATE__CHRONOLOGICAL_C1_C2_CAPACITY_ADAPTER.md` would match
successive approximate blocks through summable **inter-block** semantic
seams and retain a macroscopic charge in each block.  Its cofinal atlas,
whole terminal-semantic cut annotations, and divided whole-profile Nash debt
are additional hypotheses, not fields of a named current source declaration;
its blocks also remain approximate rather than exact.  It is therefore a
different conditional summable-decoder route, not an instance of the
normalized exact-return criterion audited here.  For the particular
vanishing-Nash source on which the chronological limit is defined, the named
theorem `ChronologicalLimit.payoff_isUniformEquilibriumPayoff` already gives
the terminal conclusion directly.

### 10.5 Exact missing same-witness fields

The current positive-minimum packet would meet the producer only after adding,
on one subsequence and inside the literal \(s_n\), all of the following:

1. dates `entryCut n < exitCut n`;
2. one uniform lower bound on reach from the start of \(s_n\) to
   `entryCut n`;
3. one uniform lower bound
   \(H(s_n[\operatorname{entryCut}_n,\operatorname{exitCut}_n))\ge\eta>0\);
4. exact root Nash, against the literal next annotation, at every displayed
   post-mark row; and
5. endpoint annotations converging to one common vector, or an explicitly
   summable full payoff/cap seam decoder.

For the positive-minimum two-cut coercivity theorem, item 4 can be dropped
because that theorem charges the actual unrestricted cap defects instead of
exactifying rows.  It still needs items 1--3 and a recurrent near-minimum
exit semantic pair in the **same** \(s_n\).  No inspected declaration
supplies those fields.  This agrees with the independent orientation audit in
`CODEX_ADVERSARY__FIN4_POSTMARK_TWO_CUT_SOURCE_ADAPTER.md`: the exact missing
datum is a renewed post-mark row, or an equivalent literal two-cut
factorization, not another compact rank selection.
