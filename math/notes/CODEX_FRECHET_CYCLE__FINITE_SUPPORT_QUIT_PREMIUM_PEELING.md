# Finite active-support peeling for nonnegative own-quitting premiums

Author: CODEX_FRECHET_CYCLE.

Status: complete ordinary-mathematical proof, frozen for independent review.
The finite table condition below is proved equivalent to a common-boundary
property of ALL exact root Nash successors on every padded box. It implies
the exclusion of arbitrary C¹ unit-drift functions and, for Fin4 with
nonnegative own singleton levels,
all-accuracy weighted packets and a uniform-equilibrium payoff through the
reviewed polynomial alternative. No Lean implementation or export is claimed.

Existing-class status is deliberately separate: an independent source check
is tracing whether the finite table condition directly instantiates a broader
Solan--Vieille root-selection consumer. The analytic separator is NOT claimed
necessary as a proof method or the first route to this class. The constant-own
subclass is already covered by the unit-solo theorem and elementary closure.

## 1. Finite data and the raw support test

Let I be a finite nonempty player set, with terminal rewards r(S)∈ℝ^I at each
nonempty coalition S⊆I, and zero payoff on Never. Put s_i=r_i({i}). Assume

    d_i(S):=r_i(S)−s_i≥0                    whenever i∈S.           (NN)

Every passive reward r_i(S) with i∉S remains arbitrary signed. Fix M≥0 with
|r_i(S)|≤M, and B>M. The singleton values may be signed in the root theorem.

The finite support-peeling condition is

    For EVERY nonempty A⊆I, there exists i∈A such that
        d_i(S)=0 for EVERY coalition i∈S⊆A.                    (SP)

This is a condition on finitely many ACTUAL reward entries. It supplies no
strategy, selected equilibrium, return word, cap, or prescribed payoff.
For Fin4 it quantifies the fifteen nonempty active supports; each subsidiary
test is a finite collection of exact reward equalities.

### Equivalent ordered form

Condition (SP) holds if and only if the players admit an ordering
i₁,…,i_n such that every strict own-quitting premium requires the presence
of an earlier player:

    d_(i_m)(S)>0 and i_m∈S
        ⇒ there is ℓ<m with i_ℓ∈S.                             (ORD)

Proof. Starting from A=I, select i₁ by (SP), remove it, select i₂ from the
remaining set, and repeat. At the moment i_m is removed it has no positive
premium on a coalition entirely contained in the remaining set. Hence any
coalition paying it a positive premium contains an earlier removed player.
Conversely, in any nonempty A choose its earliest player i_m. No coalition
S⊆A containing i_m can pay a positive premium, since (ORD) would require
an earlier member of A. By (NN), every such premium equals zero.

This is a hyperedge/order condition, not acyclicity of the directed graph
which connects a rewarded player to EVERY other member of a rewarding
coalition. A premium may require one earlier player and also contain later
players; drawing all those pairwise edges can create irrelevant cycles.

The one-exception class is a special case: order the constant-own players
first and the sole premium recipient last. (SP) also permits several
recipients, for example player 1 rewarded only when 0 is in the coalition,
player 2 rewarded only when 0 or 1 is in it, and player 3 rewarded only when
some earlier player is in it. These descriptions constrain rewards only at
coalitions where the named player itself quits.

## 2. Actual root quantities and boundary

For q∈[0,1]^I define independent coalition probabilities and Bellman values by

    p_q(S)=∏_(i∈S)q_i ∏_(i∉S)(1−q_i),
    c(q)=∏_i(1−q_i),       a(q)=1−c(q),
    R(q)=Σ_(S≠∅)p_q(S)r(S),
    F(q,v)=R(q)+c(q)v.

Let α_i(q)=∏_(j≠i)(1−q_j), and let G_i(q) be the expected absorbing
Continue contribution from nonempty opponent coalitions. Then the two pure
endpoints are

    Q_i(q)=Σ_(T⊆I\{i})p_(q,−i)(T)r_i(T∪{i}),
    C_i(q,v)=G_i(q)+α_i(q)v_i,
    F_i(q,v)=q_iQ_i(q)+(1−q_i)C_i(q,v).

Exact root Nash means F_i=max(Q_i,C_i) for every i. Finite-game Nash
existence supplies such roots at every annotation v; this is not a statement
of full behavioral equilibrium against a realizing tail.

Write

    K_B=[−B,B]^I,
    C_B=∏_i[s_i,B],
    L_B={w∈C_B : w_i=s_i for at least one i}.

For arbitrary bounded tables, F(q,v)∈K_B when v∈K_B, and

    |F_i(q,v)−v_i|≤(M+B)a(q).                                 (1)

The box padding is strict: −B<s_i<B. No semantic carrier or punishment floor
is imposed on the source v.

## 3. Exact finite-table/common-boundary equivalence

THEOREM. Under (NN), the following are equivalent for EVERY fixed B>M:

1. The actual table satisfies (SP).
2. For every v∈K_B and every exact root Nash equilibrium q against v,
   positive absorption implies F(q,v)∈L_B.

### 3.1 The support test forces every root onto the boundary

By (NN), Q_i(q)≥s_i for every root and every player. Consequently every
exact Nash successor w satisfies w_i=max(Q_i,C_i)≥s_i.

If a(q)>0, let A={i:q_i>0}, a nonempty set. Choose i∈A from (SP).
Opponents outside A Continue surely. Every coalition with positive
probability in i's Quit endpoint is therefore a subset of A containing i,
and every one of its rewards equals s_i. Hence Q_i(q)=s_i.
Since i actively prescribes Quit and is exactly best responding,

    w_i=Q_i(q)=s_i.

Thus w∈L_B. The argument covers pure/sure components, mixed components,
and zero-probability components simultaneously; no root is selected favorably.

### 3.2 Failure produces an exact interior successor in every padded box

Suppose (SP) fails at a nonempty A⊆I. For each i∈A there is a coalition
S_i with i∈S_i⊆A and d_i(S_i)>0. Necessarily |A|≥2, since singleton
premiums vanish.

For 0<t<1 set q_i(t)=t when i∈A and q_j(t)=0 otherwise. Every opponent
coalition contained in A\{i} occurs with positive probability. By (NN) and
the one strict premium at S_i,

    Q_i(q(t))>s_i                           for every i∈A.        (2)

All α_i(q(t)) are positive. For i∈A choose the continuation coordinate

    v_i(t)=[Q_i(q(t))−G_i(q(t))]/α_i(q(t)).                    (3)

Then Continue equals Quit exactly. Moreover q(t)→0, Q_i(q(t))→s_i,
G_i(q(t))→0, and α_i(q(t))→1, so v_i(t)→s_i. Strict box padding ensures
v_i(t)∈(−B,B) for all sufficiently small t.

For j∉A choose v_j(t)=B. Its Continue endpoint tends to B and its Quit
endpoint tends to s_j<B. Hence it strictly prefers Continue for all
sufficiently small t. Its Continue endpoint is also strictly above s_j.
There are finitely many players, so one small t works for every condition.

The resulting q(t) is therefore an exact Nash root against v(t)∈K_B.
Its absorption is positive. Active players receive the strictly-above-solo
values in (2); inactive players receive their strictly-above-solo Continue
values. Thus

    F_i(q(t),v(t))>s_i                       for EVERY i,           (4)

so its successor is not in L_B. In fact its upper coordinates are also
strictly below B because a>0 and M<B. This proves the converse.

This converse is a limitation of THIS common-boundary mechanism. It is NOT
a positive-gap counterexample and does not assert that some other invariant
stratified set, recurrent word, or UE construction is impossible.

## 4. Arbitrary smooth drift is impossible under the support test

Assume (NN) and (SP). Suppose a C¹ function H on a neighborhood of K_B
satisfies

    H(v)−H(F(q,v))≥a(q)                                         (5)

at every exact Nash root against every v∈K_B. Minimize H over the nonempty
compact L_B, obtaining x, and let J={i:x_i=s_i}.

If J={i}, choose a solo root q_i=t>0, all other q_j=0. The owner's
endpoints both equal s_i. For each j≠i the exact endpoint difference is

    C_j−Q_j=(1−t)(x_j−s_j)
                 +t[r_j({i})−r_j({i,j})].                     (6)

It is strictly positive at t=0, so small t makes this an exact Nash root.
Its successor lies in L_B by Section 3 and its charge is t, contradicting
minimality and (5). This calculation permits arbitrary positive pair premiums.
For a one-player set there are no outsider conditions.

If |J|≥2, the segment x+t e_i stays in L_B for small t≥0 whenever i∈J.
Therefore ∂_iH(x)≥0 for all i∈J. For small ε>0 lower only those
coordinates:

    v_ε=x−ε1_J∈K_B,
    [H(v_ε)−H(x)]/ε → −Σ_(i∈J)∂_iH(x)≤0.                     (7)

Choose any exact Nash root q_ε against v_ε. It is not all-Continue since
every i∈J gains ε by quitting at the all-Continue root. Its successor
w_ε lies in L_B by Section 3 and is coordinatewise at least s. Hence (1)
gives, for i∈J,

    ε≤w_ε,i−v_ε,i≤(M+B)a(q_ε).

Minimality and (5) would imply

    1/(M+B)≤[H(v_ε)−H(x)]/ε,

contrary to (7). Upper-box coordinates are unchanged throughout the
lowering. This proves the C¹ exclusion without convexity, a selected-root
branch, or a positive-gap premise.

## 5. Nonnegative-singleton Fin4 consequence and source handoff

Assume I=Fin4, s_i≥0 for every i, and (NN),(SP). This includes, but is not
restricted to, s=(1,0,0,0). Immediate Quit guarantees at
least s_i to every player against every independent opponent law. All-Never
opponents give player i at most max(s_i,0)=s_i, with equality available by
quitting. Thus the unrestricted semantic punishment vector is exactly

    P=s.                                                        (8)

The earlier independent checks of the one-exception subclass used the same
lower/upper argument; its use here requires only (NN), not (SP).

Take any M>0 bounding the rewards. If floor-free weighted free-start capacity
in K_(M+2) were finite at some δ>0, it would be finite at ε=min(δ,1).
The reviewed analytic separator, with inner radius M+1, would produce a
rational polynomial with unit drift at ALL tolerance-ε/4 edges in that
inner box. Exact root/Bellman edges are among them, contradicting Section 4.
Consequently

    Cap⁰_δ(M+2)=∞                            for EVERY δ>0.        (9)

This is the full source quantifier: in ONE fixed box, at every accuracy,
finite weighted packets of arbitrarily large total charge exist, with no
supplied starting payoff, actual tail, schedule, or equilibrium witness.
It is not an effective packet-length or search-termination estimate.

By (8), normality holds. Checked floor-input removal turns (9) into the
floor-bearing packet source in the same box, and the checked weighted-packet
consumer gives one fixed uniform-equilibrium payoff for unrestricted
behavioral deviations, including Never and arbitrarily late finite quits.
The separate sure-root alternative is not assumed false or produced. This
direct packet consumer does not require a positive singleton. If one instead
uses the fixed-box no-UE characterization, its positive-singleton hypothesis
holds whenever some s_i>0. In the remaining case s=0, all-Never is directly
an exact Nash equilibrium: a unilateral deviation can produce only its own
zero singleton or Never. Its zero payoff is a uniform-equilibrium payoff.

Exact dependencies, kept distinct from this new ordinary proof:

- finite root existence: `exists_isZeroQuittingRootNash` in
  `UniformEquilibrium/Quitting/Root/NashExistence.lean`;
- reviewed analytic separator:
  `math/exports/POLYNOMIAL_FORWARD_CERTIFICATES_WITHOUT_PUNISHMENT_FLOORS.md`,
  SHA-256 `14191a09b4a42149e0c893666603d85b2e2f1fb3bcd0240af0e0619aaeefc9d6`;
- checked floor-input removal:
  `hasFloorFreeAbsorptionWeightedFiniteForwardPackets_iff_weighted` in
  `UniformEquilibrium/Quitting/Projective/FloorFreeForwardPacketInputRemoval.lean`;
- checked full semantic consumer:
  `quittingGame_exists_uniformEquilibriumPayoff_of_absorptionWeightedPackets`
  in `UniformEquilibrium/Quitting/Projective/AbsorptionWeightedForwardPacketProducer.lean`
  (imported by `AbsorptionWeightedForwardPacketTranslation.lean`);
- the all-zero boundary is also covered by
  `quittingGame_isUniformEquilibriumPayoff_zero_of_zeroSolo` in
  `UniformEquilibrium/Quitting/Punishment/ZeroSoloDisjunct.lean`.

Only the root theorem is asserted for arbitrary finite I. The stated
semantic corollary uses the inspected Fin4 analytic/semantic composition.
A potentially shorter Solan--Vieille consumer is being compared independently;
it is not needed as an unverified premise of the proof above.

## 6. Comparison with acyclic solo preemption

The checked production definition `QuittingAugmentedSoloPreemptionEdge` in
`UniformEquilibrium/Quitting/Classification/Existence/AcyclicSoloPreemption.lean`
has player-to-player edge i→j precisely when i≠j and

    r_j({i})<s_j.

It adds bottom-to-player edges for positive singletons and player-to-bottom
edges for negative singletons. The theorem
`exists_uniformEquilibriumPayoff_of_acyclic_augmentedSoloPreemption` consumes
acyclicity of that graph. These edges concern PASSIVE singleton coordinates,
not the own-coalition premiums d_i(S). Conditions (NN),(SP) leave all those
passive singleton entries free and impose no augmented-solo acyclicity.

For an exact hypothesis separation, one may choose every passive singleton
reward r_j({i})=s_j−1. Then every distinct pair has both directed solo
preemption edges. At the same time any own-premium pattern satisfying (ORD)
is allowed, including a strict premium. This only separates the hypotheses;
it does not purport to defeat every other known UE class.

Likewise the old weak-solo preference condition d_i(S)≤0 intersects (NN)
in the zero-premium class. That class is already covered after positive
perturbation/scaling. A strict positive premium survives such affine column
changes and is not removed by that elementary normalization argument.

Narrow searches of the named solo-preemption, solo-exit-preference,
membership-toggle, and stationary chamber sources did not locate a stated
finite-support peeling theorem. This is not a claim of a complete literature
survey. Existing conditional root-choice theorems may already supply its
semantic consumer and must be credited if the independent source check
identifies one.

## 7. Exact boundary tests

All tests below use canonical s=(1,0,0,0) and full tables specified by a
default rule plus listed exceptions. They test the geometry, not absence of UE.

### Two exceptional simultaneous quitters can destroy the boundary

Start with r_i(S)=s_i for every nonempty S and every i. Change just the
coalition {0,1} to

    r({0,1})=(2,1,1,1).

Then the own premiums of both 0 and 1 at that pair are positive, while the
last two changed coordinates are passive. All own premiums are nonnegative.
(SP) fails at A={0,1}. The root q=(1,1,0,0) is exact Nash against EVERY
continuation: player 0 gets 2 versus 1 by leaving, player 1 gets 1 versus
0 by leaving, and each outsider gets 1 versus 0 by joining. Its successor
is (2,1,1,1), strictly above s in every coordinate. Thus there is no retained
singleton face. This root is itself a pure terminal equilibrium: the test
does NOT suggest a positive gap or failure of UE.

### A negative premium can destroy the lower orthant

Again start from r_i(S)=s_i for all coordinates. Change

    r_0({0,1})=0,       r_0({1})=−1.

Only player 0 has a nonconstant own-quitting reward, but its pair premium
is negative. At q=(1,1,0,0), player 0 gets 0 versus −1 by leaving;
player 1 is indifferent at 0; the other players are also indifferent at 0.
The root is exact against every continuation and its successor is the zero
vector, violating the lower bound w_0≥s_0=1. Therefore (NN) cannot simply
be omitted from this boundary argument.

### Zero premiums recover the already covered class

When every d_i(S)=0, (SP) holds for every ordering, the root theorem reduces
to the constant-own-reward argument, and canonical UE is already covered by
the Solan--Vieille theorem plus the explicitly recorded small-perturbation
closure. No new coverage is claimed for this boundary case.

## 8. Remaining check

The exact mathematical questions for review are the equivalence in Section 3
(especially the inactive-player constraints in its converse), the all-root
minimizer argument, and the semantic source quantifiers. The source question
is whether (SP) has already been stated as a raw-table class, or instead is
a new explicit adapter into an existing conditional root-choice consumer.
Failure of (SP) leaves the wider negative-certificate and general UE problems
open; this note does not extend its conclusion to that residual.
