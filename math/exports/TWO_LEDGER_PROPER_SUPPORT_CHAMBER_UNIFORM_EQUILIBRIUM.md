# Two weighted ledgers and proper-support cap chambers

This is an ordinary-mathematical finite-reward class theorem. Its raw
adapter is not implemented in Lean. The conclusion uses the existing
actual semantic carrier and full-behavior uniform-payoff consumer.
No arbitrary-table theorem or exact terminal-Nash existence is asserted.
Throughout, E is maximum coordinate debt, not total debt.

## 1. Exact finite data and theorem

Let I be any finite set with at least two players. A quitting game has
arbitrary finite real reward vectors r(S) for every nonempty S subset I,
zero live payoff and zero Never payoff. Players use independent private
randomness; every unilateral behavioral replacement is allowed. Put
s_i=r_i({i}) and assume s_i>=0. Fix nonzero weights a_i>=0. For every
nonempty proper S define TWO DIFFERENT polynomials in the raw rewards:

    H_a(S)=sum_i a_i[r_i(S)-s_i],
    J_a(S)=sum_(i notin S) a_i[r_i(S union{i})-r_i(S)].

Assume the following finite guards.

1. H_a(S)>=0 for every nonempty proper S, and H_a({j})>0 for at least
   one player j.
2. J_a(S)<=0 for every nonempty proper S.
3. Every nonempty proper A has a flat participant: there is i in A such
   that r_i(S)<=s_i for EVERY nonempty S subset A containing i. Equivalently
   there is no proper nonempty premium trap, with the full coalition left
   unrestricted.
4. The directed graph with i->j, i!=j, exactly when
   r_j({i,j})>r_j({i}) has no directed cycle contained in a proper subset
   of I. Equivalently every nonempty proper induced subgraph has a sink.

THEOREM. These raw hypotheses imply a uniform-equilibrium payoff in the
original game against unrestricted behavioral deviations. There is ONE
fixed vector v such that, for every epsilon>0, some behavioral profile
and horizon threshold deliver payoffs within epsilon of v and cap every
complete unilateral deviation by v_i+epsilon at EVERY larger horizon. No profile,
continuation, best response, root selector, invariant carrier, or small
error sequence is an input. In particular the grand-row rewards enter
only guard2 on penultimate coalitions and guard3 does not constrain the
full coalition.

The strict singleton clause follows automatically when the singleton
comparison matrix Gamma, Gamma_ii=0 and Gamma_ij=r_i({j})-s_i, is full
standard-Q. Indeed the complementary problem at offset-minus-ones supplies
x>=0 with Gamma x>=ones. Thus a*Gamma x>0, so a*Gamma e_j>0 for some j.
This is H_a({j})>0. The direct clause avoids imposing standard-Q when
unnecessary; it does not infer the other guards from standard-Q.

## 2. Actual full semantics, seed and compact constrained domain

A behavioral profile is equivalently independent private laws on the
finite dates together with Never: before absorption the only public
history is repeated all Continue. For an actual profile let U_i be its
terminal expected payoff and B_i the supremum over ALL complete
unilateral behavioral replacements. This is equivalently the supremum
over every pure finite deadline and Never, since payoff is affine in
the replacement law. The source cap need not be attained.
Put d_i=B_i-U_i>=0 and E=max_i d_i.

The closure of all actual pairs(U,B) is a compact subset of a finite
Euclidean reward box. It retains B>=U. It need not be convex, and a
point in this closure need not be an actual clock profile.

For any fixed product root q, put alpha_i=product_(j!=i)(1-q_j),
Q_i=E[r_i(A union{i})], and b_i=E[r_i(A)1_(A nonempty)], where A is
the independently drawn opponent quitter set at that root. Complete
prefix semantics, including every future response and Never, is

    U_i'=q_i Q_i+(1-q_i)(b_i+alpha_i U_i),
    B_i'=max{Q_i,b_i+alpha_i B_i}.                     (0)

This fixed-root map is continuous, preserves the actual closed carrier,
and is the only strategy concatenation used below. The cap-root stage
game pays r(S) at a nonempty root coalition and B at all Continue;
finite mixed Nash existence supplies a FULL Nash root, including the
inequalities of every zero-hazard player.

Let player j Quit0 surely and every other player Never. Its ACTUAL full
semantics is

    U_i=r_i({j}),
    B_j=s_j,
    B_i=max{r_i({j}),r_i({i,j})} for i!=j.

For j every finite deadline pays s_j and Never pays0, so B_j=s_j uses
s_j>=0. For each
other player, Quit0 and a positive finite deadline/Never give exactly
the two displayed rewards. Every private response law is a mixture of
these complete pure responses. Thus there is no deadline truncation.

Write L_a(B)=sum_i a_i(B_i-s_i). Since B>=U coordinatewise,
L_a(B)>=H_a({j})>0. If E=0 this actual profile already supplies the
terminal Nash and fixed-target uniform conclusion. Otherwise set
lambda=L_a(B)/E>0 using THIS produced profile.

Let S_actual be the closed carrier of all actual full pairs(U,B),
without any convexification. It is compact and invariant under every
fixed product root. The following closed subset is nonempty:

    C={(U,B) in S_actual:
          min_i(B_i-s_i)<=0, L_a(B)>=lambda E(U,B)}.       (1)

No global lower bound B>=0 is needed or asserted.

## 3. Exact cap-root identities and full-support exclusion

At any actual semantic pair use the two-action finite root game with
all-Continue continuation B. For a root q put c=product_i(1-q_i), and
let Q_i and C_i be its forced-Quit and forced-Continue endpoints, the
latter retaining the full suffix cap B_i. Every exact Nash root obeys

    B'=cB+sum_(S nonempty) p_q(S)r(S),
    B_i'-U_i'=c(B_i-U_i),                 E'=cE.          (2)

These identities extend to the closed actual carrier for any fixed
selected root. No continuity of Nash selection or cap attainment is
used. A root with some q_i=1 gives E'=0 immediately, hence a diagonal
in the actual carrier and the desired conclusion. We may therefore
assume no such root occurs when proving a contradiction to no UE.

If q has full support and every q_i<1, write z_i=q_i/(1-q_i)>0. Active
indifference divided by opponent joint survival gives the literal identity

    B_i-s_i=sum_(empty!=A subset I\{i}) z_A
                           [r_i(A union{i})-r_i(A)].

Consequently

    L_a(B)=sum_(empty!=S proper subset I) z_S J_a(S)<=0. (3)

At a positive-E point of C, however, L_a(B)>=lambda E>0. Thus EVERY
cap-Nash root there has proper support, unless it already supplies a
zero-debt diagonal by c=0.

## 4. Preservation under every remaining cap-Nash root

Let A={i:q_i>0} be proper and nonempty. Guard3 supplies a flat i in A.
Every forced-Quit coalition for i is a subset of A containing i, hence
Q_i<=s_i. Supported Nash optimality gives B_i'=Q_i<=s_i, including sure
probabilities. Thus the low-cap condition is preserved.

All terminal root coalitions are nonempty proper subsets, so guard1 and
(2) give

    L_a(B')=cL_a(B)+sum_(S nonempty) p_q(S)H_a(S)
            >=cL_a(B)>=lambda cE=lambda E'.             (4)

All Continue simply fixes the pair. Therefore EVERY cap-Nash root from
a positive-E chamber point either supplies the conclusion outright or
remains in C with E'=cE. This is preservation on the stated actual domain, not a
claim of universal root escape at arbitrary actual pairs.

## 5. Escape is needed only at the attained minimum

Suppose C has attained minimum E*>0, at(U*,B*). If any B_i*<s_i,
all Continue is not Nash (Quit pays s_i), so finite-game Nash existence
supplies a nonzero root. It yields a smaller-E point in C by the preceding
argument, or a diagonal, a contradiction.

Otherwise every B_i*>=s_i. The low set

    L={i:B_i*=s_i}

is nonempty and PROPER, since L_a(B*)>0. Guard4 gives a sink i in L.
Let only i Quit at the root with a sufficiently small p in(0,1).
Owner i is indifferent because its two endpoints are s_i and B_i*=s_i.
For another player j, Continue minus Quit is exactly

    (1-p)(B_j*-s_j)+p[r_j({i})-r_j({i,j})].            (5)

For j in L this is nonnegative because i is a sink. For j outside L
the first gap is strictly positive, so (5)>=0 for all sufficiently
small p>0, simultaneously by finiteness. This is a nonzero FULL Nash
root, including every inactive player's inequality, not a Nash root
of only the owner subgame.

Its prefix remains in C and has E'=(1-p)E*<E*, a contradiction. Hence
the compact minimum is zero. Diagonal membership produces actual
profiles with full terminal regret tending to zero and payoffs converging
to ONE fixed target. The existing full-behavior uniform consumer gives
the theorem. Strategy-class completeness, arbitrary-game preservation,
and an algorithm for one convergent root spine are NOT claimed.

## 6. Exact four-player test

Take I=Z/4 and unit weights. Own singletons are1, the opposite singleton
recipient gets4, the other two singleton recipients get0. On the
adjacent pair {i,i+1}, recipient i gets-1, i+1 gets2, and BOTH outsiders
get3/2. On an opposite pair both participants get0 and BOTH outsiders
get2. On any triple the three participants get-1 and its omitted
recipient gets10. Every grand recipient gets9. All Never rewards0.

The exact finite ledgers are

    H(singleton)=1, H(adjacent pair)=0,
    H(opposite pair)=0, H(triple)=3;
    J(singleton)=-3, J(adjacent pair)=-5,
    J(opposite pair)=-6, J(triple)=-1.

Positive own premiums in a PROPER coalition occur only at the successor
participant of an adjacent pair. A trap therefore must contain every
predecessor and is all4. The positive insertion graph is exactly the
directed Hamiltonian cycle i->i+1, so both guards3/4 hold. The sole-owner0
seed has

    U=(1,0,4,0), B=(1,2,4,0), E=2, L=3, lambda=3/2.

Here every proper RAW terminal surplus is nonnegative. No additional
Nash-conditioned polynomial inequality is required.

## 7. Whole weight and boxed-charge comparisons on this test

These are bounded comparisons, not an exhaustive producer census. For
the sole full trap, every nonzero nonnegative upper-average weight fails
the grand test, which is8sum_i w_i>0. For a global weighted FLOOR,
sum the four singleton inserted-premium inequalities: their left sides
sum to -2sum_i w_i<0. Thus no nonzero nonnegative floor weights work.
The pair OUTSIDER changes do not affect these singleton inserted premiums.

For the only full trap, P(S)=sum_(i notin S)[r_i(S union{i})-1] and
J(S) have the exact values

    singleton: P=-2,J=-3;
    adjacent pair: P=-4,J=-5;
    opposite pair: P=-4,J=-6;
    triple: P=8,J=-1.

Every valid boxed-charge selection therefore has delta<=2,tau>=8,
gap<=3,loss<=1. Its maximal threshold is at most

    4sqrt(2/8)(3+2/8)=13/2 <4+4*10.

Thus the WHOLE boxed-charge predicate, and its support-local
upper-average alternative, fail. This is not failure of merely one
selected weight or coefficient tuple.

## 8. No stationary exact Nash on the test

First there is no stage Nash root with a sure player, for ANY continuation.
If i is sure, opposite i+2 has joining-minus-Continue differences-4,
-5/2 or-1 as zero, one or two other nonowners quit, so strictly Continues.
Predecessor i-1 then has differences-1 or-5/2 and strictly Continues.
Successor i+1 joins for2 versus0. Owner i then receives-1 and withdraws
for0, a contradiction.

Now suppose q is stationary exact terminal Nash. All q_i<1 by this
argument, and q is nonzero because all Never has a profitable Quit1.
Every stationary pure-Never response has nonnegative payoff, as all
passive rewards are nonnegative, so all B_i=U_i>=0.

Full support is impossible: its eventual terminal law has strictly
positive singleton probabilities and EVERY terminal H>=0 (including
grand H=32), hence sum B-4>0; (3) instead gives sum B-4<0.
One active owner is impossible because its successor prefers joining2
to passive0. For adjacent two-player support, the successor's Never
value is0 whereas its Quit value is1+a>0. For opposite two-player
support, Never gives4 whereas Quit gives1-b<1.

For support three rotate to q=(a,b,c,0), with a,b,c>0. Player0 has

    Q0=1-2b-c+bc,
    b0=c(4-(5/2)b),
    Q0-b0=1-2b-5c+(7/2)bc>=0,

the last inequality following from active indifference
Q0=b0+(1-b)(1-c)B0 and B0>=0. Thus b<1/2 and
c<=(1-2b)/(5-(7/2)b)<=1/5. Player1's Quit endpoint is

    Q1=1-2c+a(1-c)>=1-2c>=3/5.

Its Never payoff is2ac/(a+c-ac)<=2c<=2/5, since only the simultaneous
opposite pair {0,2} gives it a nonzero passive reward. But stationarity
and a positive own hazard imply its full value equals this Never
payoff: opponents terminate surely, and exact root indifference
U1=b1+alpha1 U1 solves U1=b1/(1-alpha1). Contradiction.

Hence every stationary exact Nash is excluded. This defeats every sound
raw producer whose conclusion is an exact stationary product profile,
without restricting its parameter choices. It does not exclude small
stationary regret or independently audit all nonstationary producers.


## 9. Bounded singleton, quotient and normal-core comparisons

All comparisons in Sections7--11 concern the EXACT witness in Section6,
not the open neighborhood in Section12 or every member of the class.
They are bounded whole-selection comparisons, not an exhaustive producer
census or a claim excluding unknown implicit-function neighborhoods.

Its singleton comparison matrix and inverse are

    Gamma=[0,-1,3,-1; -1,0,-1,3; 3,-1,0,-1; -1,3,-1,0],
    det Gamma=45,
    Gamma^-1=(1/15)[2,3,7,3;3,2,3,7;7,3,2,3;3,7,3,2].

Every principal block of size>=2 is invertible; an axis homogeneous
complementary solution fails a negative external neighbor entry. Thus
Gamma is R0. At offset ones its entire strictly complementary root set
is the empty support, four adjacent supports with coordinates(1,1), and
four triples with rotated coordinates(1/2,5/2,1/2). Opposite supports
and full support have a negative active coordinate. The principal
determinant index sum is1-4+4=1. Therefore Gamma is standard-Q, has
degree1, and misses the degree-not-one singleton exit. Every deleted
triple has determinant6 and a negative inverse diagonal, defeating all
child choices in
`PassiveRowInverseCriterion.exists_uniformEquilibriumPayoff_of_raw_nonnegativeInverse_triple`,
`UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/RawPassiveRowInverseCriterion.lean`.

For actual response quotients put H_i(q)=(1-alpha_i)Q_i-b_i, NOT either
weighted ledger of Section1. The singleton block-row test on all15
partitions leaves only discrete, all-block,02|13,01|23,03|12,
02|1|3,0|13|2. The first three are actual invariant quotients, with
matrices Gamma,[1],[[3,-2],[-2,3]] and degree1/positive determinant.
The remaining candidates fail actual response equality:

| blocks | q | unequal residuals |
| --- | --- | --- |
| 01\|23 | (0,0,1/2,1/2) | H0=-1, H1=-25/16 |
| 03\|12 | (0,1/2,1/2,0) | H0=-25/16, H3=-1 |
| 02\|1\|3 | (0,0,0,1/2) | H0=3/4, H2=0 |
| 0\|13\|2 | (0,0,1/2,0) | H1=0, H3=3/4 |

The actual criterion is `QuittingResponseInvariantOnUnitCube`, and its
necessary singleton test is
`quittingSingletonBlockRowSum_eq_of_responseInvariant`, both in
`UniformEquilibrium/Quitting/Stationary/ResponseInvariantQuotient.lean`.
The nonnegative-inverse quotient exit additionally requires a NEGATIVE
determinant in
`finFour_exists_uniformEquilibriumPayoff_of_responseQuotient_nonnegative_inverse`,
`UniformEquilibrium/Diagnostics/Quitting/FinFourResponseQuotientCriterion.lean`.
None of the actual quotients meets it.

Every player has a negative singleton-comparison row entry and positive
participant premium, so the full normal/premium core remains all4.
The positive singleton-comparison edges form an opposite matching, not a
directed four-cycle. Protected/common-participant assumptions also fail:
every player has an outgoing adjacent participant reward-1 below its
singleton1. In particular the convention requiring participant rewards
AT LEAST own singleton is not being confused with an upper bound.

## 10. Whole persistent-base and universal quiet-child comparisons

There is NO full stage Nash with any sure label for any continuation,
by Section8. Thus every sound full induced-base/free-set producer which
would furnish such a root fails over its entire base/free selection.

For singleton base i, the full-complement induced Nash point is uniquely:
successor i+1 sure, opposite and predecessor Continue. The strict
opposite/predecessor endpoint comparisons in Section8 prove uniqueness
without assuming owner optimality. Owner payoff is-1 and withdrawal
gives0. Its punishment value is0: Never guarantees nonnegative passive
payoff against any opponents, while a sure successor holds its entire
cap to0. Its empty-opponent probability is0, so adding a punishment
continuation cannot repair the floor excess1. This is the actual
induced game of
`UniformEquilibrium/Quitting/Root/PersistentBaseInducedGame.lean`
and the semantics of
`singletonBase_inducedNash_floorExcess_semantics` in
`UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/LargeBaseStationarySemanticHandoff.lean`.
The argument retains every omitted-player join test; it does not check
only the displayed pure child and infer all free mixed choices.

For EVERY nonempty proper child C, choose j in C with j+1 outside C.
The child profile sole-j-Quit0/others-Never is exact full child Nash:
the predecessor's join gives-1 instead of0, the opposite's join gives0
instead of4, and the favorable successor is absent. All child debts and
joint-Never mass are0. In the full quiet lift missing successor j+1
can Quit0 for2 instead of0.

Consequently every universal raw certificate bounding outsider debt by
nonnegative weighted child debts plus any finite joint-Never residual
fails, for EVERY child and every weight/kind choice. In particular this
contradicts the concluded inequalities of
`quittingLiftDeletedProfile_outsideDebt_le_add_neverExcess_of_withdrawalFutureJoin`
in `UniformEquilibrium/Quitting/Classification/QuietExtension/WithdrawalFutureJoinFixedTarget.lean`
and
`quietLift_outsideBehaviorDeviationDebt_le_weighted_childDebt_add_slack`
in `UniformEquilibrium/Quitting/Classification/QuietExtension/CappedClockChildDeletionAdapter.lean`.
It does not exclude a different selector allowed to choose only another,
favorable child equilibrium.

## 11. Named stationary and finite-calendar comparisons

Section8 excludes every sound raw producer whose conclusion is an EXACT
stationary Nash profile, including all its parameter/support choices.
It does not exclude stationary approximate families, general calendars,
or a class merely because the witness is far from its stated center.

Every pair has a nonpositive participant, and each triple has a mate
pair with joining gap-4. Thus pair templates requiring both positive
participants and triple templates requiring all strict member joins
fail every selection. In the named four-joint phase templates with
singleton opposite favorites, relabeling fixes the mate permutation;
their required positive scheduled member rewards are absent. This
compares their explicit literal guards, not unknown larger IFT radii.

The named positive four-singleton calendar has two chronological
orientations, up to relabeling. Its entire positive proper owner-field
solution is explicit. Write u_l in(0,1) for chronological Continue
probabilities. Owner indifference is

    E_l=u_l[4-4u_(l+1)+u_(l+1)u_(l+2)]-1=0.

For a=u0-u2,b=u1-u3,

    E0-E2=4(1-u1)a-u2(4-u0)b,
    E1-E3=u3(4-u1)a+4(1-u2)b.

The coefficient determinant
16(1-u1)(1-u2)+u2u3(4-u0)(4-u1)>0, so a=b=0.
Writing u0=u2=x,u1=u3=y gives(4+xy)(x-y)=0. The common
equation is(u-1)(u^2-3u+1)=0, with UNIQUE proper solution
u=(3-sqrt(5))/2. At an owner's root the next and preceding
nonmate prescribed values are respectively u and1. Their Quit
endpoint is u+(1-u)r_i({i,owner}), giving cross-pair caps0 and1.
An incoming participant reward2 violates one of them in either
orientation. This excludes the entire named positive owner solution
set, not only a symmetric guess. Longer words and boundary hazards
remain outside this comparison.

The passive-triple cap-chamber class with pair outsider rewards1 does
not contain this witness. Its literal singleton rows force identity
recipient scaling and zero translation under any recipient-affine
relabeling preserving those rows, so pair outsiders3/2 and2 cannot
be obtained by that transport either. This is only one comparison;
the whole base, child, weight, charge and stationary comparisons above
are needed to avoid relying on fixed-row syntactic difference alone.

## 12. A full sixty-coordinate open region

There is an open reward-coordinate region, not just a boundary family.
Take the Section6 table but replace both adjacent-pair outsider rewards
by7/4 and both opposite-pair outsider rewards by9/4. Keep every other
coordinate unchanged. With unit weights its exact ledgers are

    H(singleton)=1, H(each pair)=1/2, H(triple)=3;
    J(singleton)=-3, J(adjacent pair)=-11/2,
    J(opposite pair)=-13/2, J(triple)=-1.

On each proper A choose i in A whose predecessor is absent from A.
Every nonsingleton S subset A containing i has its participant reward
at least1 BELOW own singleton. The positive insertion graph is still
exactly i->i+1; all directed nonzero sign tests have absolute margin
at least1. Own singleton signs have margin1.

Perturb ALL sixty coordinates independently by entrywise distance
delta<1/100, including own singletons and grand coordinates. Each
H changes by at most8delta and each J by at most6delta. Every relevant
participant-premium and insertion comparison changes by at most2delta.
Thus all H stay strictly positive, all J stay strictly negative, own
singletons stay positive, the same proper flat witnesses remain valid,
and the same insertion graph persists. Every table in this full open
ball satisfies the theorem. No uniform strategy/profile/horizon is
claimed over the ball. The bounded source census of Sections7--11 was
for the ORIGINAL Section6 witness and is not silently extended to
every point of this neighborhood.

## 13. Actual-data adapter, boundaries and narrow Lean handoff

The input consists only of the finite reward table, nonnegative weights,
and the four raw guards. Sections2--5 produce an actual seed, a nonempty
compact constrained carrier and a zero-debt point. No strategic witness,
continuous Nash selector, convexity, public signal, or return word is an
input. The diagonal produces one fixed target before accuracy.

The existing checked semantic declarations used are:

* `quittingTerminalSemanticCarrier`,
  `exists_terminalProfile_sequence_tendsto_semanticPair`,
  `quittingTerminalSemanticCarrier_isCompact`,
  `continuous_quittingTerminalSemanticPrefix`, and
  `quittingTerminalSemanticPrefix_mem_carrier` in
  `UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`;
* `exists_isZeroQuittingRootNash` in
  `UniformEquilibrium/Quitting/Root/NashExistence.lean`;
* `quittingTerminalSemanticDebt_prefix_eq_continueMass_mul_of_capNash`
  and `quittingTerminalSemanticPrefix_envelope_eq_rootSuccessorPayoff_of_capNash`
  in `UniformEquilibrium/Quitting/Root/CapNashRootStack.lean`;
* `isUniformEquilibriumPayoff_of_diagonal_mem_terminalSemanticCarrier`
  in
  `UniformEquilibrium/Quitting/Classification/Existence/UniformPayoffTerminalSemanticCarrier.lean`.

The signed proper-support low-cap step is already represented by
`exists_successor_le_singleton_of_exactRoot_nontrap_support` in
`UniformEquilibrium/Quitting/Classification/CommonQuittingPremiumLeaver.lean`.
Trap definitions and negation are in
`MathUE/FiniteCoalitionPremiumCore.lean` and
`UniformEquilibrium/Quitting/Classification/QuittingPremiumSupportPeelingOrder.lean`.
The different weighted ledgers are compatible with the literal
`quittingWeightedLeaveSum` and `quittingWeightedInsertedPremium` of
`UniformEquilibrium/Quitting/Classification/WeightedQuittingTrapLeavers.lean`;
the latter equals H_a+J_a at a nonempty proper coalition, and is
NOT either guard separately. The whole boxed predicates used above are
`QuittingTrapChargeCoefficients`,
`QuittingTrapChargeCoefficients.threshold_of_cardinality_four`, and
`HasBoxedQuittingNashCharges` in `BoxedQuittingNashCharges.lean`,
`BoxedQuittingNashChargeOdds.lean`, and `BoxedQuittingNashChargeReturn.lean`
under the same classification directory.

A narrow formalization can implement the four finite guards, the actual
sole-owner seed, the two exact weighted prefix/odds ledgers, preservation
on positive-debt chamber points, and the minimum-specific sink root,
then invoke the named diagonal consumer. It should not add carrier
convexity, cap attainment, a B>=0 hypothesis, or a continuous selector.

Weak H/J inequalities and zero weight coordinates are allowed. An all-sure
cap-Nash root closes the argument immediately; no no-sure raw condition
is required. Full graph cycles are permitted; only proper induced cycles
are excluded. Nothing is claimed when the strict singleton seed clause
fails, when a proper premium trap remains, or when the insertion graph
contains a proper cycle. In particular standard-Q supplies the seed but
does not supply preservation/escape guards for arbitrary table data.
