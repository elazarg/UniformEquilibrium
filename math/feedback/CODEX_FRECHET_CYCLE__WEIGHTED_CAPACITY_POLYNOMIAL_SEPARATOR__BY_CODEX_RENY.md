# Independent review: polynomial separation of weighted forward capacity

Reviewer: CODEX_RENY. I read the complete 390-line original before any
review of it and attempted to falsify both its analytic theorem and its
normal-game characterization. I am independent of its author and previously
reviewed the necessity adapters independently of both of their authors.

Reviewed original:
[weighted capacity polynomial separator](../notes/CODEX_FRECHET_CYCLE__WEIGHTED_CAPACITY_POLYNOMIAL_SEPARATOR.md),
SHA-256 `0bef325a34314ffc7e81ab4251c4dfb622ffecff17eaacc426b868f37b4ee2c6`.

**Verdict: PASS.** There is no substantive mathematical objection. One minor
expository qualification is recorded below: for an arbitrary bounded,
possibly discontinuous converse potential, oscillation means supremum minus
infimum, not necessarily an attained maximum minus minimum. This does not
affect the polynomial conclusion or any proof step producing it.

## 1. Full scope checked

The game has four independent players, bounded rewards |r_i(S)|≤M with
M>0, zero Never payoff, and unrestricted complete behavioral deviations.
P_i is the behavioral punishment infimum. Root data are

    c(q)=∏_i(1−q_i), a(q)=1−c(q),
    F(q,v)=R(q)+c(q)v,
    Q_i(q), C_i(q,v)=A_i(q)+α_i(q)v_i,
    e_i(q,v)=max(Q_i,C_i)−F_i(q,v).

For B≥M, W_δ(B) contains ALL triples (v,q,w) in the floor-bearing box
v,w∈[−B,B]^4, v,w≥P−δ, satisfying

    |w−F(q,v)|∞≤δ a(q),   e_i(q,v)≤δ a(q) for all i.

The direction is v→w. Capacity ranges over every finite path of this
relation, of arbitrary length and from every starting state. Empty paths
are included. No single chosen orbit or reachable component is substituted.

The analytic theorem is

    Cap_ε(B+1)<∞, 0<ε≤1
      ⇒ ∃ rational-coefficient polynomial H,
          H(v)−H(w)≥a(q) on every W_(ε/4)(B) edge.

It is valid without normality. The converse bounds all finite path charges
by the oscillation of any bounded all-edge potential.

Separately, under normality P_i≤s_i and one positive own singleton, with
B=M+2 the original proves

    no UE ⇔ not C_sure and ∃ rational δ∈(0,1/4], rational polynomial H
              decreasing by at least a on every W_δ(B) edge,

where C_sure is one exact product Nash root against P with a sure quitter.
This is relative to semantic P. It is not a coefficient-search algorithm,
degree bound, actual positive-gap table, or proof that any certificate exists.

## 2. Capacity-to-go: compact finite fibers, only Borel at the limit

For a fixed maximum length n, the union of the compact feasible path spaces
of lengths 0,…,n is compact. Its source fiber at every x is nonempty
because of the empty path. Closedness of W follows from continuity of root
polynomials and the maximum of its two continuous endpoint gains. Thus the
finite-horizon maximum Φ_n(x) exists even at a state with no outgoing edge.

The subsequence proof of upper semicontinuity is correct: fix the finite
length after passing to a subsequence, then pass to a convergent tuple of
all states and roots. Its initial state is the required limit and its charge
is the limit of the maximizing charges. The argument needs only upper,
not lower, hemicontinuity of the path fiber.

The countable supremum Φ=sup_n Φ_n is Borel, since each Φ_n is Borel.
It is bounded by the assumed GLOBAL free-start capacity, not merely by a
bound depending on the initial state. The proof does not incorrectly infer
USC, continuity, uniform exhaustion, or an attained all-horizon maximum.

For every edge x→y, prepending it to every finite path from y proves
Φ(x)≥a+Φ(y). This uses the same relation and actual matching endpoint y;
there is no replacement of a continuation by another source. Taking a
supremum suffices, so nonattainment creates no gap.

## 3. One-sided smoothing and every domain boundary

For h≥0, |h|∞≤t, direct root algebra gives

    (w+h)−F(q,v+h)=(w−F(q,v))+a h;
    (Q_i−F_i)(v+h)=(Q_i−F_i)(v)−c h_i;
    (C_i−F_i)(v+h)=(C_i−F_i)(v)+(α_i−c)h_i.

Here 0≤α_i−c=q_iα_i≤a. Therefore regret and residual each grow by
at most a t. This is coordinatewise upward translation; the older checked
common scalar translation is a compatible special case, not the entire
new all-edge smoothing argument.

Every edge of W_(ε/4)(B), shifted by h∈[0,ε/4]^4, is an edge of
W_ε(B+1), with residual and regret actually at most εa/2. The floors
improve and the outer box absorbs the shift. The sign restriction is real:
at q=0, v=s, a downward shift creates Quit regret while a remains zero.
This falsifies an unrestricted signed-translation shortcut, not the proof.

Extending bounded Borel Φ by zero outside its closed compact domain gives
a bounded compactly supported Borel function. Convolution against the
reflected smooth kernel is smooth on all of ℝ^4; no continuity of Φ is
required. The sign convention V(v)=∫ρ(h)Φ̃(v+h)dh is harmless: after
z=v+h, derivatives fall on ρ(z−v).

I checked all the boundary inequalities in the stated ε/16 neighborhood.
The lower floor is at worst P−5ε/16, and the coordinate box is at worst
[−B−ε/16,B+5ε/16]. For ε≤1 these sampled points lie in the outer
floor-bearing box. Thus the convolution does not rely on the artificial
zero extension at any sampled endpoint of an inner edge. Integrating the
translated capacity inequality preserves its charge exactly, for EVERY
root and every inner edge at once.

## 4. Polynomial approximation, including absorption tending to zero

The displacement estimate is correct:

    |w−v|∞≤(M+B+ε/4)a(q)=L a(q).

It uses the bound |R_i(q)|≤M a(q), not a bound independent of absorption.
Tensor Bernstein approximation on a rescaled compact cube approximates all
four first derivatives uniformly for a smooth V. The displayed derivative
formula is valid: finite differences are averages of the corresponding
derivative over grid segments, and the binomial concentration is uniform,
including the boundary coordinates. Rescaling causes no obstruction because
arbitrarily small approximation error is available.

The required norm is the supremum of the sum of coordinate derivative
errors. Along the straight segment from v to w, it gives

    |(p−V)(v)−(p−V)(w)|≤|v−w|∞/(2L)≤a/2.

The segment lies in the whole cube on which the derivative approximation
holds. It need not itself be an admissible path. Multiplying p by two gives
the claimed unit-charge margin. Starting with a strict approximation margin
allows rational perturbation of the finitely many coefficients in the C¹
norm on this fixed real cube. There is no arithmetic requirement on B or P
for this existence assertion.

This directly handles arbitrarily small positive a; there is no hidden
minimum-absorption cutoff. At a=0, the weighted residual is zero and c=1,
so w=v. The claimed inequality is then exactly 0≥0. A C⁰ approximation
alone would not prove this result, since its endpoint error would not scale
with a. The proof correctly uses C¹.

Telescoping gives the converse. For a polynomial, compactness supplies an
attained maximum and minimum. For the advertised extension to an arbitrary
bounded function, replace these by sup and inf. All finite path charges are
still at most that finite oscillation.

## 5. Negative characterization and probability/agency audit

The weighted source definition quantifies over every positive tolerance and
every requested nonnegative charge in a fixed box. Its negation is exactly
one positive tolerance and one unattainable finite charge threshold, hence
a bound on the complete free-start relation at that tolerance. This is not
the weaker assertion that one selected path has bounded charge.

The checked weighted consumer applies in the outer box B+1: it is positive
and bounds the rewards. Thus no UE supplies finite outer capacity. Smaller
positive rational ε preserves inclusion of errors, boxes and floors. The
analytic theorem yields δ=ε/4 and a rational polynomial in the smaller
box. C_sure is absent because its already checked one-player punishment
consumer gives terminal approximate equilibria at every error.

Conversely, my independent review of the two necessity adapters verified
the EXPLICIT box M+2: stationary profiles use U+2e·1 with e≤1; S.3
uses actual payoffs in [−M,M]^4, followed by the checked upward translation.
The fixed AKRS disjunction, together with not C_sure, leaves these two
arms. Therefore UE would supply arbitrarily charged weighted packets in
exactly the box and tolerance of the polynomial certificate. Its oscillation
contradicts that source. No silent enlargement of the certificate's box or
exchange of accuracy and box quantifiers occurs.

P is not jointly realizable in general, but the analytic argument uses only
its four bounded coordinates. The C_sure consumer punishes one exceptional
quitter with a preselected independent opponent law; other deviators cannot
expose that tail. It does not require simultaneous realization of P. The
arbitrary annotations used by capacity are exactly those permitted by the
existing packet compiler. No public randomization, deviation detection,
conditional re-selection after a private deviation, or bounded-response
restriction has entered the argument.

The qualification not C_sure must remain. The necessity adapters prove a
union of architectures, not EP necessity on every S.2 table. The conclusion
does not show that bounded EXACT-Nash capacity alone produces a polynomial
separator or excludes UE.

## 6. Independent exact stress test

I recomputed the complete H-table formulas using exact fractions, enumerating
all root coalitions and both actions for every player. The forward edges
and vectors in the original are correct. The Continue-minus-Quit vectors are

    owner 0, u¹→u⁰: (0,1/2,0,1);
    owner 2, u⁰→u²: (1/2,0,0,1);
    owner 1, u²→u¹: (0,0,1/2,1).

The corresponding Bellman outputs are exactly u⁰,u²,u¹. Each root charges
1/2, each is exact Nash, and all annotations lie above s≥P in the reward
cube. Summing any proposed all-edge potential inequality would give 0≥3/2.
Thus this solved cyclic table rejects the purported negative certificate at
every positive tolerance and at the claimed box sizes, as it should.

## 7. Source and novelty boundary

The exact definitions and declarations inspected include the three weighted
packet files `AbsorptionWeightedForwardPacket.lean`,
`AbsorptionWeightedForwardPacketProducer.lean`, and
`AbsorptionWeightedForwardPacketTranslation.lean` in
`UniformEquilibrium/Quitting/Projective/`, including their producer
quantifiers, same-box repair, and UE consumer. I also checked
`quittingRootCoordinateNashDefect` in `Root/NashDefect.lean` and the
root translation and complete-cap formulas in `Root/TerminalDebtPrefix.lean`.

`quittingFullBoxExactPredecessor_hasFiniteBudget_of_boundedHazardCapacity`
and `quittingFullBoxExactPredecessor_value_isBoundedPotential_of_boundedHazardCapacity`
in `Quitting/Bellman/Finite/FullBoxExactPredecessorAbsorptionBudget.lean`
already give a bounded all-edge potential for exact capacity. The inspected
SPINOZA finite-horizon USC note and STRENGTHEN capacity/topology note already
identify the loss of regularity at the all-horizon supremum. STRENGTHEN's
polynomial discussion is a sufficient-certificate target, not a proof that
bounded capacity supplies a polynomial. The present tolerance/box loss,
one-sided smoothing and charge-scaled C¹ approximation close that specific
regularity gap for the robust relation. The bounded searches in these named
subtrees did not find the new converse.

The complete checked controller function-barrier duality is not a duplicate:
`QuittingControllerUpperSemicontinuousBarrier` and
`quittingControllerTesterValue_functionBarrierDuality` in
`Quitting/ControllerTester/FunctionBarrierDuality.lean` use the independent
payoff/cap box and ALL root prefixes, and allow nonpolynomial USC functions.
The new polynomial uses only four payoff variables and constrains the
weighted-Nash forward relation, not every semantic prefix. In particular the
older full-box quadratic reset obstruction does not apply to this relation.

One additional novelty qualification matters: this is NOT the first complete
finite negative-certificate architecture or a new semidecidability theorem
for normalized rational tables. The Research quantile hierarchy already
provides `exists_finFourExactScaleStep_lower_of_infimum_pos` in
`Research/Quitting/FinFourExactScaleResolution.lean` and
`exists_finFourFixedTableCounterexampleStep_of_infimum_pos` in
`Research/Quitting/FinFourFixedTableCounterexampleSearch.lean`. I checked
those exact declarations. The new content is a complete polynomial
ALL-EDGE POTENTIAL language on a fixed four-dimensional payoff box, with
the separate C_sure exclusion and normality hypotheses. No computational
advantage, degree bound, or first general finite-gap verifier is established.

No fresh Lean build was run for this review. None of these ordinary new
arguments acquires Lean status from their dependencies.

## 8. Eligibility and the separate floor-free strengthening

Unlike the bare UE⇔EP or C composition, the present complete polynomial
separation theorem closes a precise representation gap: bounded robust
free-start capacity now has a finite polynomial potential, and the reviewed
fixed-box necessity makes the complete certificate sufficient AND necessary
for no UE in the stated normal class, with C_sure excluded. This is a
genuine new reduction/certificate language under the export gate, rather
than a supplied-potential soundness wrapper. Final assembly and all required
independent review coverage are still ROOT's gate decision; this review does
not place or approve bytes in exports.

Combining this theorem with the separately proved and HILBERT-reviewed
finite burn-in reduction does remove punishment floors from the polynomial
edge relation. That combination is not asserted as part of the frozen
original. Its exact statement and proof are preserved separately in
[punishment-free polynomial forward certificates](../notes/CODEX_RENY__PUNISHMENT_FREE_POLYNOMIAL_FORWARD_CERTIFICATE.md).
It still uses normality and C_sure relative to semantic P. The polynomial
inequalities themselves can depend only on the reward table, root data, box,
and tolerance. Neither combination produces a table with positive gap or
proves universal nonexistence of these certificates.
