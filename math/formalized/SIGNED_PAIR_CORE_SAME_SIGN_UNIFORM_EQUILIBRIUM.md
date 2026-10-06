# Signed pair cores with same-sign joining comparisons

## 1. Raw criterion and uniform-equilibrium conclusion

Let I be a finite nonempty player set. At every live date, players
independently choose Quit or Continue. The first nonempty quitting
coalition S absorbs at a fixed vector r(S)∈ℝ^I, paid thereafter.
Live-stage rewards and perpetual continuation are zero. Past actions
are public. Strategies and unilateral deviations are unrestricted
behavioral strategies with independent private randomization. No
public correlation or bounded-memory restriction is added.

Write s_i=r_i({i}). A nonempty A⊆I is a positive-premium trap if
every i∈A has some S⊆A containing i with r_i(S)>s_i. No singleton
is a trap. Unions of traps are traps, since all old witnesses remain
available. The union C of all traps is the greatest premium core,
with C=∅ if there are no traps. These definitions use the actual
reward table and impose no premium-sign assumption.

Suppose either C=∅ or C={i,j} for distinct players i,j. In the
pair case define

    d_i=r_i({i,j})−r_i({j}),
    d_j=r_j({i,j})−r_j({i}).                         (1)

**Uniform-equilibrium theorem.** For four players with s≥0, if the
core is empty, or the core is a pair and d_i d_j≥0, then the
original quitting game has a uniform-equilibrium payoff. There is
one vector u such that for every ε>0 there are a behavioral profile
and a horizon threshold N₀ whose expected average payoff is within
ε of u at every N≥N₀, while every complete unilateral deviation
has expected average payoff at most u_i+ε. The target u is fixed
before accuracy.

For the pair, both players may strictly prefer joining, or both may
strictly prefer leaving; either gap may also vanish. Participant
premiums elsewhere may have either sign. The opposite-strict-sign
case is not asserted. The criterion is finite raw data: no strategy,
root selector, continuation annotation, degree value, or controller
is supplied as input.

The new mechanism produces a suitable root rather than requiring
every exact root to return. It removes the global nonnegative-premium
premise from the same-sign pair-core branch. A smooth full-root
potential is excluded analytically under d_i d_j>0; the zero-gap
strategic boundary follows separately by reward closure.

## 2. Exact roots and signed support facts

For q∈[0,1]^I let μ_q be its independent product coalition law,
c(q)=μ_q(∅), and a(q)=1−c(q). At a continuation annotation v,
the literal successor is

    w(v,q)=c(q)v+∑_{S≠∅}μ_q(S)r(S).                 (2)

Player k's forced action endpoints are

    Q_k(q)=∑_{T⊆I\{k}}μ_{−k}(T)r_k(T∪{k}),
    C_k(v,q)=μ_{−k}(∅)v_k
                  +∑_{∅≠T⊆I\{k}}μ_{−k}(T)r_k(T).

An exact root is Nash for this finite two-action game. Equivalently,
w_k≥Q_k,C_k for every k, where w_k=q_k Q_k+(1−q_k)C_k.
Thus q_k>0 implies w_k=Q_k≥C_k; an interior hazard implies equality
of both endpoints. Exact roots exist at every annotation. Annotations
need not be realized by strategies.

Let C={i,j}. Because C is itself a trap and singletons are not,
both pair participant rewards strictly exceed their own singletons.
Every nonempty active support A≠C is not a trap: a trap would be
contained in C and could not be a proper nonempty subset of that
pair. Hence some k∈A has

    r_k(S)≤s_k for every S⊆A containing k.

Averaging all actual within-support coalitions gives, at an exact root,

    w_k=Q_k≤s_k.                                    (3)

No equality of participant rewards is needed. All simultaneous
larger coalitions are retained.

For every outsider k∉C and T⊆C we also have

    r_k(T∪{k})≤s_k.                                 (4)

Otherwise C∪{k} would be a trap, retaining the pair witnesses for
i,j and using T∪{k} for k. Therefore every outsider's forced-Quit
endpoint is at most its singleton on a core-only root. This is an
UPPER bound, not a protected successor floor.

If C=∅, the argument for (3) applies on every nonempty support,
even without Nash when phrased for the active Quit endpoint. This
is exactly the product-low condition.

## 3. A concrete fixed-point index fact

Let F:ℝⁿ→[0,1]ⁿ be continuous, with a unique fixed point p.
Suppose F is C¹ near p and det(Id−DF(p))≠0. Then

    sign det(Id−DF(p))=+1.                          (5)

The point p may be on a boundary face of the unit cube. To prove
the statement, use the larger open cube Ω=(−1,2)ⁿ and
z=(1/2,...,1/2). The homotopy

    q↦q−[(1−t)F(q)+tz],   0≤t≤1,

has no zero on ∂Ω, because the bracket lies in the unit cube.
At t=1 its degree is +1. Thus q−F(q) has total degree +1 on Ω.

Set D=Id−DF(p). Invertibility supplies m>0 with ‖Du‖≥m‖u‖.
Differentiability gives, on a sufficiently small sphere about p,

    ‖p+u−F(p+u)−Du‖≤(m/2)‖u‖.

The straight-line comparison to Du has no boundary zero there, so
the local degree is sign det D. Since p is the unique root, excision
identifies it with the total degree. This proves (5). There is no
half-index: p is interior to Ω.

The relevant implemented degree primitives are
`ambientDegree_homotopy` and `ambientDegree_affineRootField_eq_sign_det`
in `MathUE/Topology/AmbientDegreeHomotopyNormalization.lean`,
`ambientDegree_excision` in `MathUE/Topology/AmbientDegreeProperties.lean`,
and `ambientDegree_of_selfMap_eq_one` in
`MathUE/Topology/AmbientDegreeSelfMapNormalization.lean`.
The local nonlinear-to-linear comparison above supplies the required
adapter; no game-specific index oracle is assumed.

## 4. Producing a low-successor root below a singleton

Assume C={i,j} and d_i d_j>0. If the pure pair is exact at any
annotation, it is exact at every annotation: each player has another
sure quitter among its opponents. At source v=r({i,j}) it has
successor v and absorption one. This is both an actual pure terminal
equilibrium and an immediate obstruction to any positive full-root
potential drift. We may therefore exclude this case in the remaining
root-selection argument.

**Selected-return assertion.** At every annotation v with v_h<s_h
for at least one player h, there exists an absorbing exact root whose
successor has some coordinate at most its singleton.

All Continue is not Nash at such a source, so every exact root
absorbs. Call a root bad if w>s in every coordinate. By (3), a bad
root has support exactly C. On that face the two gaps g=Q−C are

    g_i=s_i−v_i+(v_i−s_i+d_i)q_j,
    g_j=s_j−v_j+(v_j−s_j+d_j)q_i.                    (6)

A core hazard cannot be sure while the other is interior: the other's
gap would be the nonzero d. Both sure hazards give the excluded pure
pair. Hence a bad root must be fully mixed on C, with the unique
possible coordinates

    p_i=(v_j−s_j)/(v_j−s_j+d_j),
    p_j=(v_i−s_i)/(v_i−s_i+d_i),
    p_k=0 for k∉C.                                  (7)

A zero denominator cannot solve an interior active equation. Whenever
(7) is interior, α_i=v_i−s_i+d_i has the sign of d_i, and α_j
has the sign of d_j. Indeed 0<u/(u+d)<1 implies that u and d
have the same strict sign. Consequently α_i α_j>0.

Use the FULL polynomial endpoint gaps, extended to all real hazard
coordinates, and define

    F_v(q)_k=min(1,max(0,q_k+g_k(q))).                (8)

This continuous map takes ℝ^I into the unit cube. Its fixed points
are precisely all exact Nash roots: g_k≤0 at q_k=0, g_k≥0 at
q_k=1, and g_k=0 in the interior are exactly the clipping conditions.

If every root were bad, (7) would be the unique fixed point. At
that point every outsider gap is STRICTLY negative, since (4) gives

    Q_k≤s_k<w_k=C_k.

Therefore all outsider rows of F_v are locally constant zero. The
core rows are locally q_k+g_k, since their hazards are interior.
Ordering the two core coordinates first, the derivative of q−F_v(q)
at p has the block form

    [[0,−α_i,*], [−α_j,0,*], [0,0,Id]],

with determinant −α_i α_j<0. The starred derivatives include all
larger-coalition interactions; no restricted-face equation has replaced
them. Their values do not affect this block-triangular determinant.

Equation (5) rules out this unique negative-index fixed point. Exact
Nash existence therefore supplies a nonbad root, proving selected
return. There is no outsider tie-removal perturbation: the strict
inactive inequalities follow from badness itself.

## 5. Strict analytic exclusion

Fix |r_k(S)|≤M and B>M. A full exact-root unit-absorption potential
is a function H satisfying

    H(w(v,q))+a(q)≤H(v)                             (9)

for every v∈[−B,B]^I and every exact root q. The claim is that no
C¹ H on a neighborhood of the box satisfies (9) under the strict
pair hypothesis. Singletons may be signed in this analytic statement.

The successor formula gives

    ‖w−v‖∞≤(M+B)a.

For every player k, without any participant-sign condition,

    Q_k≥s_k−2M a.                                  (10)

Indeed only nonempty opponent coalitions can change the forced-Quit
payoff from s_k, by at most 2M; their total probability is at most a.

### Signed singleton-face drift

Let x∈∏[s_k,B] and x_j=s_j. Property (9) implies

    ∇H(x)·(x−r({j}))≥1.                            (11)

Here is a direct signed proof. Set b_j=0. For k≠j set b_k=0 if
x_k>s_k, and otherwise b_k=max(0,r_k({k,j})−r_k({j})). At a
small t>0 take source v=x+t b/(1−t) and only player j active,
with hazard t. Positive corrections occur only at binding coordinates
strictly below B, so the source stays boxed. Player j is indifferent.
Every other player's Continue-minus-Quit gap is

    (1−t)(x_k−s_k)+t[b_k+r_k({j})−r_k({k,j})]≥0

for sufficiently small t, including upper-box coordinates. The root
is exact, its absorption is t, and its successor is
x+t(b+r({j})−x). Apply (9), divide by t, and differentiate.
The two b terms cancel, proving (11).

### One compact domain for all selected successors

If the pure-pair alternative from Section 4 holds, its fixed successor
already contradicts (9). Otherwise minimize H on

    D={v∈[−B,B]^I: v_k≤s_k for some k}.

This set is compact and nonempty. If a minimum x had a coordinate
strictly below its singleton, selected return would produce an
absorbing exact root with successor in the SAME D, contradicting
the minimum and (9). Thus x belongs to the lower boundary
L={x∈∏[s_k,B]: some x_k=s_k}.

Let J={k:x_k=s_k} and g=∇H(x). Nonbinding interior partials vanish;
upper-box partials are nonpositive, because their permitted negative
variations stay on L. If J contained just j, the j term of (11)
would be zero. Its remaining terms would be nonpositive: interior
terms vanish, and upper-box displacements B−r_k({j}) are positive.
This contradicts (11). Therefore |J|≥2.

Increasing a binding coordinate while retaining another binding one
stays on L. Hence g_k≥0 for every k∈J. Fix such k, and take
v=x−εe_k for small ε>0. This source is boxed and below a singleton.
Choose the produced absorbing root, with successor w∈D. Minimality
and drift give

    H(v)−H(x)≥H(v)−H(w)≥a.

Nash, (10), and the displacement estimate imply

    s_k−2Ma≤Q_k≤w_k≤s_k−ε+(M+B)a,
    ε≤(3M+B)a.

It follows that

    [H(x−εe_k)−H(x)]/ε≥1/(3M+B).

Its limit is −g_k≤0, a contradiction. The proof does not require
convergence of selected roots, any individual successor floor, or
membership of every root successor in D.

## 6. Fin4 consumer and the weak strategic boundary

For Fin4, nonnegative own singletons imply normality by
`isQuittingNormalPlayer_of_singleton_nonneg` in
`UniformEquilibrium/Quitting/Classification/AbnormalPlayers.lean`.
No sign condition on other participant premiums enters this theorem.

If some singleton is positive, absence of a uniform-equilibrium payoff
would produce a rational polynomial potential on the complete robust
root relation in box M+2, by
`quittingGame_not_exists_uniformEquilibriumPayoff_iff_noSureRoot_and_rationalPotential`
in `UniformEquilibrium/Quitting/Projective/PolynomialForwardCertificateCharacterization.lean`.
The SAME polynomial restricts to every boxed exact root by
`isQuittingFullExactRootPotential_of_robustPotential` in
`UniformEquilibrium/Quitting/Projective/ExactRootPotentialRestriction.lean`.
It is C¹ and contradicts Section 5 with B=M+2. If all s_k=0,
all Never is itself exact at every horizon.

For d_i d_j=0, perturb only passive singleton entries. If exactly
one gap is zero, change its passive entry slightly so that its gap
has the same strict sign as the other. If both are zero, lower both
passive entries slightly, making both gaps positive. This changes
no participant reward, own singleton, or trap, and produces arbitrarily
close tables satisfying the strict theorem.

Reward closure yields a fixed target for the original game. The exact
declaration is `exists_uniformEquilibriumPayoff_of_arbitrarily_close_reward_tables`
in `UniformEquilibrium/Quitting/Terminal/TerminalExploitabilityRewardRobustness.lean`.
Concretely, choose nearby equilibrium targets in one common compact
box and take a convergent subsequence with limit u. Changing rewards
uniformly by δ changes every prescribed or deviating expected average
payoff by at most δ. For each requested accuracy, first choose one
nearby target sufficiently close to u, then its profile and horizon
threshold. They work in the original game for every larger horizon.
The limit u was selected before accuracy. No weak analytic exclusion
is inferred from this closure argument.

For an empty core, (3) proves the exact predicate
`HasProductLowQuittingPremium` in
`UniformEquilibrium/Quitting/Classification/ProductLowQuittingPremium.lean`.
The semantic consumer is `exists_uniformEquilibriumPayoff_of_productLowPremium`
in `UniformEquilibrium/Quitting/Classification/Existence/ProductLowPremiumUniformPayoff.lean`.

## 7. A fully signed mutual-join table

Here is a complete rational table with s=(1,0,0,0).

| S | r(S) |
|---|---|
| 0 | (1,−1,−1,−1) |
| 1 | (2,0,2,−1) |
| 2 | (2,−1,0,2) |
| 3 | (0,2,−1,0) |
| 01 | (1,0,−1,−1) |
| 02 | (1,−1,0,−1) |
| 03 | (2,2,−1,1) |
| 12 | (2,0,0,1) |
| 13 | (0,0,1,0) |
| 23 | (2,1,0,0) |
| 012 | (1,0,0,−1) |
| 013 | (1,0,−1,0) |
| 023 | (1,−1,0,0) |
| 123 | (0,0,0,0) |
| 0123 | (−1,−2,−2,−2) |

Only players 0 and 3 at pair03 have positive participant premiums.
Thus the only trap is 03 and d₀=d₃=2. Every player has a negative
participant premium at the grand coalition. In particular no nonempty
set of globally nonnegative-premium players exists.

At the sure-pair product law both active Quit rewards exceed their
singletons, so product-low fails. A positive-weight aggregate-leave
test at trap03 also fails even weakly: each proper singleton leaves
one strictly positive weight times the positive gap 2. The example
does not disguise a protected individual leaver.

In table order, pure coalitions have strictly improving players

    1,3,1,0,0,0,2,2,0,3,0,1,0,1,0,

with respective gains

    1,1,1,2,1,1,1,2,1,2,1,2,1,1,1.

Every withdrawal retains another quitter. All Never fails because
player 0 has positive singleton reward.

### A bad and a good root at the same source

At v=(3,−1,4,2), the exact root q=(1/2,0,0,1/2) has

    Q=(3/2,0,0,1/2),
    C=w=(3/2,1/2,1/4,1/2).

Its successor is strictly above all singletons although v₁<s₁.
Its inactive gaps are −1/2 and −1/4; its local determinant is −16.
It is not legitimate to assert that every exact root returns.

At the SAME source, q=(0,2/3,0,1/3) instead has

    Q=(10/9,0,0,0),
    C=w=(14/9,0,17/9,0).

This is another full exact root. Its active players 1 and 3 return
exactly to their singleton levels. These roots exhibit the distinction
used by the selected-return theorem directly.

### Bounded source comparisons

The singleton matrix with receiver rows is

    Γ=[[0,1,1,−1],[−1,0,−1,2],
       [−1,2,0,−1],[−1,−1,2,0]].

Its child123 block A has det A=7,
A⁻¹=[[2,4,1],[1,2,4],[4,1,2]]/7, and A1=1. For h>0,
Az≥h1 and complementarity force all child coordinates positive:
a zero coordinate would make its cyclic predecessor row nonpositive.
Hence z=h1. At h=0, a zero propagates to all coordinates, and an
all-positive homogeneous solution contradicts invertibility. Therefore
the full homogeneous problem has only zero: a positive pivot h would
leave pivot residual h>0. The full matrix is R₀.

At offset (1,−1,−1,−1), the child is (1+h)1 and the pivot
residual is 2+h. The unique root is (0,1,1,1), with active
determinant 7. Its degree is +1, so the degree-not-one exit does not
apply. The only triple with nonnegative inverse is 123; its passive
inverse row is (−1/7,5/7,3/7). Triples 012,013,023 have negative
inverse entries −2,−2/3,−2/3 respectively. The full inverse has
entry −5/7 in row0,column2. No pair has two positive off-diagonal
entries, and principal03 is R₀ but non-Q at offset (−1,−1).
The full matrix is not being called non-Q.

For a literal response quotient, rows in a target block must have
equal sums over every source block. These exact witnesses exclude
thirteen partitions:

| Partition | Rows | Source block | Unequal sums |
|---|---|---|---|
| 01 / 2 / 3 | 0,1 | 2 | 1,−1 |
| 02 / 1 / 3 | 0,2 | 1 | 1,2 |
| 03 / 1 / 2 | 0,3 | 1 | 1,−1 |
| 0 / 12 / 3 | 1,2 | 12 | −1,2 |
| 012 / 3 | 0,1 | 012 | 2,−2 |
| 03 / 12 | 0,3 | 12 | 2,1 |
| 0 / 13 / 2 | 1,3 | 2 | −1,2 |
| 02 / 13 | 0,2 | 02 | 1,−1 |
| 013 / 2 | 0,1 | 2 | 1,−1 |
| 0 / 1 / 23 | 2,3 | 1 | 2,−1 |
| 01 / 23 | 0,1 | 01 | 1,−1 |
| 023 / 1 | 0,2 | 1 | 1,2 |
| 0123 | 0,1 | 0123 | 1,0 |

Only the discrete partition and 0|123 survive. At q=(t,0,0,0),
the latter block's full response coordinates are t,t,t+t², so it
also fails. The relevant tracked declarations are
`exists_uniformEquilibriumPayoff_of_r0Degree_ne_one` in
`UniformEquilibrium/Quitting/Classification/LCP/SingletonDegreeCriterion.lean`,
`exists_finset_r0Degree_eq_sum_sign_det` in
`MathUE/LinearProgramming/R0DegreeSum.lean`,
`PassiveRowInverseCriterion.exists_uniformEquilibriumPayoff_of_raw_nonnegativeInverse_triple`
in `UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/RawPassiveRowInverseCriterion.lean`,
and `quittingSingletonBlockRowSum_eq_of_responseInvariant` in
`UniformEquilibrium/Quitting/Stationary/ResponseInvariantQuotient.lean`.

### Every proper child defeats a universal quiet-lift debt bound

Thirteen proper children have the following exact terminal Nash
profiles: the stated coalition quits surely at date zero, and every
other child player chooses Never. If a deviation prevents absorption,
the prescribed future is Never.

| Child | Sure coalition | Profitable omitted player | Gain |
|---|---|---|---|
| 0 | 0 | 1 | 1 |
| 1 | 1 | 3 | 1 |
| 2 | 2 | 1 | 1 |
| 3 | 3 | 0 | 2 |
| 01 | 1 | 3 | 1 |
| 02 | 2 | 1 | 1 |
| 03 | 03 | 2 | 1 |
| 12 | 1 | 3 | 1 |
| 13 | 3 | 0 | 2 |
| 23 | 2 | 1 | 1 |
| 012 | 1 | 3 | 1 |
| 013 | 03 | 2 | 1 |
| 023 | 2 | 1 | 1 |

Every child join or withdrawal is nonprofitable. A sole quitting
owner who instead keeps play alive faces Never opponents and cannot
exceed its nonnegative singleton. These comparisons cover all complete
behavioral deviations. All prescribed profiles have zero Never mass.

For child123 use a repeated three-date cycle of solo half-hazards in
order3,1,2. Its values, in child-coordinate order1,2,3, are exactly
(1,0,0),(0,1,0),(0,0,1). Every participant reward within this child
is its singleton zero, so every forced-Quit endpoint is zero. The
owner is indifferent and every Continue equation is exact. Opponent
geometric absorption proves full terminal Nash, with zero joint Never.
The quiet player0 has value [4·0+2·2+2]/7=6/7. Quitting at the
first player3 half-hazard gives (1+2)/2=3/2, a gain of 9/14.

Thus, for every proper child, some omitted player violates every
universal bound by a fixed finite nonnegative weighted sum of child
deviation debts plus a fixed multiple of joint Never. The exact
quantifier compared is that in
`withdrawalFutureJoin_quietLift_outsideDebt_le_add_neverExcess` in
`UniformEquilibrium/Quitting/Classification/QuietExtension/WithdrawalFutureJoinDebt.lean`.
This does not exclude selecting a special child profile by another
method, nor every stationary or chronological producer.

## 8. Why opposite strict signs need another mechanism

The following complete finite rule specifies another table. For every
nonempty S except the grand coalition, assign r₀,r₁ according to
S∩{0,1}:

| Core intersection | r₀(S) | r₁(S) |
|---|---:|---:|
| empty | 0 | 2 |
| 0 | 1 | −1 |
| 1 | 3 | 0 |
| 01 | 2 | 1 |

Set r₂(S)=0 when 2∈S, otherwise −1 when the core intersection
is {1}, and 3 in all other cases. Set r₃(S)=0 when 3∈S and
1 otherwise. Override r(0123)=(0,−1,−1,−1). The singleton
vector is (1,0,0,0), the sole trap is 01, and d₀=−1,d₁=2.
Every player has a negative premium at the grand coalition.

At v=(0,2,3,1), player3 has C₃=1 at every root and Q₃≤0.
Therefore q₃=0 at every exact root. The changed grand row cannot
then affect any other player's endpoint, even when its own action
is forced. The core gaps are g₀=1−2q₁ and g₁=4q₀−2,
independently of q₂. Boundary values q₀=0 and q₀=1 contradict
best responses. Hence q₀=q₁=1/2. At this mixture Q₂=0,C₂=2,
so q₂=0.

The unique exact root is (1/2,1/2,0,0), with successor
(3/2,1/2,2,1)>s. Its inactive gaps are −2,−1, and its local
determinant is −(−2)(4)=8>0. A positive index is consistent with
uniqueness and total degree +1. This falsifies the same selected-root
assertion for opposite strict signs. It is NOT a UE counterexample.

## 9. Source correspondence and formalization handoff

The raw core definitions are `IsQuittingPremiumTrap` and
`quittingPremiumCore` in
`UniformEquilibrium/Quitting/Classification/QuittingPremiumCore.lean`.
The existing `quittingPremiumCore_outsider_reward_eq_singleton` there
and `exactRootSuccessor_active_eq_singleton_of_support_ne_pair_core`
in `UniformEquilibrium/Quitting/Classification/QuittingPremiumCoreExactRoot.lean`
require `HasNonnegativeOwnQuittingPremium`. The present proof instead
uses the signed upper bounds (3)–(4).

The current `exists_uniformEquilibriumPayoff_of_pairPremiumCore_weakLeave`
in `UniformEquilibrium/Quitting/Classification/Existence/QuittingPremiumCoreUniformPayoff.lean`
also requires nonnegative participant premiums and a weak-leave ordering.
The table in Section 7 satisfies neither premise. This is a precise
implementation-scope difference, not a claim of publication novelty or
an exhaustive search over all possible equilibrium producers.

Exact Nash existence is `exists_isZeroQuittingRootNash` in
`UniformEquilibrium/Quitting/Root/NashExistence.lean`. The signed
singleton probe's existing derivative conclusion is
`IsQuittingFullExactRootPotential.singletonFace_drift` in
`UniformEquilibrium/Quitting/Projective/FullExactRootPotentialFaceDrift.lean`.
The displacement input is
`abs_quittingRootSuccessorPayoff_sub_tail_le_reward_add_source_mul_absorptionMass`
in `UniformEquilibrium/Quitting/Root/BoundedSuccessorDisplacement.lean`.
The relevant strict potential predicate is
`IsQuittingFullExactRootPotential` in
`UniformEquilibrium/Quitting/Projective/ExactRootPotentialRestriction.lean`.

The new chain to formalize is: signed pair-core support inequalities
→ complete clipped-map classification of bad roots → negative local
index and an actual selected returning root → strict full-potential
exclusion on one compact low-coordinate domain → the existing Fin4
polynomial consumer → weak same-sign UE by passive reward closure.
The degree primitives are named in Section 3, and the local adapter
is explicit. No strategic witness remains assumed after the raw table
criterion is checked. No speculative repository refactor is required.

The analytic theorem is finite-player and permits signed singletons.
The stated semantic conclusion is Fin4 with nonnegative own singletons.
The weak conclusion is strategic only. Opposite strict signs, larger
premium cores, arbitrary finite quitting games, and completeness of a
bounded controller are not established here. This packet supplies
ordinary mathematical evidence, not a claim that its new theorem has
already been implemented or checked in Lean.

## Implementation coverage

The full weak original-game UE criterion, including the empty-core exit,
is represented by
`exists_uniformEquilibriumPayoff_of_empty_or_signed_pair_core_weakSameSign`
(`UniformEquilibrium/Quitting/Classification/Existence/SignedPairCoreRewardClosure.lean`).
Its strict producer is
`exists_uniformEquilibriumPayoff_of_signed_pair_core_strictSameSign`
(`UniformEquilibrium/Quitting/Classification/Existence/SignedPairCoreUniformPayoff.lean`).
Both take raw rewards and the stated comparisons, not strategies or roots.

The actual bad-root derivative and second-root producer are
`signed_pair_core_badRoot_hasFDerivAt_and_negative_det`
(`UniformEquilibrium/Quitting/Classification/SignedPairCoreBadRoot.lean`) and
`exists_exactRoot_singletonSublevel_of_signed_pair_core`
(`UniformEquilibrium/Quitting/Classification/SignedPairCoreSelectedReturn.lean`).
The finite-player selected-return adapter in the latter file composes with
`not_isQuittingFullExactRootPotential_of_selectedSingletonSublevelReturn`
(`UniformEquilibrium/Quitting/Projective/SelectedSingletonSublevelReturnSmoothDrift.lean`).
The pure-pair alternative is retained explicitly by the strict producer;
it is not silently treated as a selected-return hypothesis.

This coverage does not label every literal fixture, exclusion of another
raw source, or boundary example above kernel-checked. Such comparisons
remain ordinary supporting mathematics unless separately represented by
a named declaration. They do not supply another counterexample-class
restriction beyond the implemented main weak UE theorem.
