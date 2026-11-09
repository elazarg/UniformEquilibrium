# Signed solo/triple producer: exact source-overlap audit

The complete rational table audited here IS SOLVED by the accompanying signed
solo/triple raw producer: an exact absorbing period-two Nash profile alternates
solo1 and joint013, with player2 quiet. This is an original-game UE result,
not a positive-gap example, a minimizing source, or a counterexample. The
prior producer failures below remain valid; they never excluded every dynamic
law or every favorable selected child equilibrium.

The complete input is the fifteen-row `rows` dictionary in
[the exact completion checker](../experiments/FIN4_SIGNED_PIVOT_COMPLETION_CHECK.py),
which is also included literally in the producer packet. Coalition masks use
bit i for player i. Run from the repository root with
`python math/experiments/FIN4_SIGNED_PIVOT_COMPLETION_CHECK.py`. It requires
Python3 and SymPy, reconstructs every source-screen check, and stores no
subdivision payload. This is ordinary mathematical/computational evidence,
not a Lean build. The comparison original game is R_i(A)=1+Z_i(A), retaining
zero live and Never rewards; own singleton levels are1.

The producer independently computes its two-phase hazards and values from
this table. Its embedded exact checker certifies the equilibrium itself.
The separate completion checker above certifies the named earlier-source
failures. Neither checker is a theorem that all reward tables admit this
architecture.

## 1. Full stationary and actual-punishment root classes

For opponent survival H_i, forced-Quit expectation Q_i, and passive immediate
expectation P_i, form F_i=(1-H_i)Q_i-P_i. Any nonzero stationary terminal Nash
profile has F_i<=0,=0,>=0 according as owner i is quiet, mixed, or sure.
These are necessary for original R as well as native absorbing Z. The
checker excludes all 3^4-1=80 patterns, in 2071 rational subdivision nodes.

For actual original punishment tails, the literal Never response gives
the continuation cap minus one at least

    L_i=min({-1} union {Z_i(A): A nonempty, i notin A})
       =(-10,-3,-3,-3).

Thus a sure owner's necessary comparison is
G_i=Q_i-P_i-H_i L_i>=0. Every nonsure owner facing a sure owner has H_i=0,
so its F and G signs coincide. The checker excludes all 3^4-2^4=65 patterns
containing a sure owner, in 294 nodes. This includes arbitrary actual
punishment tails, not just stationary or Never tails.

Every free polynomial has coordinate degree at most two. On each dyadic
box the checker converts to tensor degree-two Bernstein coefficients;
strict wrong signs exclude an inequality, and a strict sign excludes an
equality. Midpoint subdivision is exact integer arithmetic after clearing
positive denominators. Active-equation multiplication by an exact principal
inverse supplies additional necessary equalities. For a no-sure support S
of size at least two, F_S=-Gamma_SS q+R(q), with every term of R degree at
least two. Its exact coefficient-sum/inverse bound gives t<=D t^2 at a
root, where t=max q_i. The selected origin cube t<=2^-E, 2^E>D, therefore
contains no nonzero root. Sole-owner supports are exact affine intervals.
No terminal box is left unresolved and no subdivision payload is stored.

All principal Gamma_SS of size at least two are invertible, and every
singleton column has a negative entry. These also exclude stationary
approximation at hazards tending to zero: a normalized nonnegative limit
x would satisfy Gamma x>=0 and x_i(Gamma x)_i=0; singleton support violates
the first condition, while larger support violates principal invertibility.
Consequently the whole stationary output class has a positive regret floor
at this table. No conclusion about unrestricted absorbing regret follows.

Exact formal source interfaces are
`isZeroAsymptoticNash_stationary_iff_endpointNash_and_boundary` in
`UniformEquilibrium/Quitting/Stationary/EndpointCompiler.lean` and
`exists_sureFirst_isεAsymptoticNash_iff` in
`UniformEquilibrium/Quitting/Root/FirstStageAdapter.lean`.
This excludes the outputs of stationary collision, jackpot, row-weight,
inverse-column stationary, and sure-first punishment producers, whenever
their theorem conclusion has precisely one of these forms.

The complete concrete persistent-base selections also fail. A nonempty
base of size at least two has H_i=0 for every owner; its accepted free-Nash,
base-leave, and outsider-join conditions extend to a full sure-coordinate
root. For singleton base p the accepted owner inequality is
Q_p-P_p-H_p(mu_p-1)>=0, where mu_p is its actual original punishment value;
mu_p-1>=L_p implies the screened G signs. This includes every base, every
disjoint free carrier, and every induced Nash point. The relevant sources
are `PersistentBaseConcreteGap.lean` and `PersistentBaseNashSemanticAdapter.lean`
under `UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/`.
The separate accepted empty-base interior solution has literal residual F
on active and passive owners (`EmptyBaseSemanticDispatch.lean`), so it is
excluded by the stationary census. This covers the three accepted branches
of the named `StrictToggleSemanticDispatch` source; it does not assert any
unrestricted UE obstruction.

## 2. All proper universal child quiet-lift selectors

For each proper nonempty child C, the following one-date child profile is
exact terminal Nash, absorbs surely, and has a profitable outsider join.
After that date all child players use Never. A sole sure owner who deviates
Continue can quit later at original own payoff one, so its normalized
continuation cap is zero; this is included in the checked endpoint signs.

| Child mask | Sure owners / hazards | Profitable outsider |
|---|---|---|
|1,3|sure0|2|
|2,6,7|sure1|3|
|4,5|sure2|3|
|8,10,12,14|sure3|0|
|9,13|sure0 and sure3|1|
|11|q=(1,9/2029,0,4/17)|2|

For child11 the child0 gap is 4903/34493>0, child1 and child3 are exactly
indifferent, and outsider2 gains 41091/34493>0. All fourteen profiles have
zero child debt and zero joint Never mass.

Therefore no universal outside-debt bound by nonnegative child-debt weights
plus a bounded joint-Never term holds for any child. The exact common
consumer is `withdrawalFutureJoin_quietLift_outsideDebt_le_of_jointNever_zero`
in `Classification/QuietExtension/WithdrawalFutureJoinDebt.lean`.
`WithdrawalFutureJoinKind` in `WithdrawalFutureJoinRaw.lean` has the five
patient, deadline, evaluated-security, terminal-security, cancellation
kinds; the proper-child sources in `WithdrawalFutureJoinFixedTarget.lean`
require a certificate for every outsider. Hence all five kinds, every
proper child, all weights and floors, and the advancing-only subcase fail.
This does not exclude a producer selecting one favorable child equilibrium
instead of guaranteeing the lift for every child equilibrium.

## 3. Complete coefficient-weight and quotient tests

Write H(A)=Z(A), Jinc(A)_i=1_(i notin A)[Z_i(A+i)-Z_i(A)], and
K(A)_i=Z_i(A+i). Exact duals are

    H(6)=(-10,-3,-5,-3)<0,
    Jinc(1)+Jinc(5)+Jinc(8)=(1,23,7/2,9/2)>0,
    20K(13)+K(3)=(-72,-606,-30,-1000)<0,
    K(14)=(3,10,3,3)>0.

They respectively exclude every nonzero nonnegative weight satisfying all
proper H>=0, all proper Jinc<=0, all inserted K>=0, or all inserted K<=0.
This covers the full-proper payoff premise of
`MARKED_SUPPORT_ORIENTATION_LEDGER_UNIFORM_EQUILIBRIUM.md`, the joining
premise of `SUPPORT_FILTERED_WEIGHTED_LEDGERS_UNIFORM_EQUILIBRIUM.md`, and
the global floor predicate `HasGlobalQuittingWeightedFloor` in
`Classification/WeightedQuittingTrapLeavers.lean`. The full player set is
an actual premium trap: every player has a positive participant reward
(use masks15,7,5,9 for players0,1,2,3). Therefore the trap-leaver predicate
cannot evade the failed nonzero global floor by having no traps.
Numbers of weights and support filters cannot repair these individual
strict dual obstructions.
The K(14) vector also supplies a proper-support product-high point.

For all fourteen nondiscrete player partitions, the checker finds two
coefficients of merged F rows with a nonzero determinant. Thus the rows
cannot become proportional under any positive constant recipient scales.
This excludes `QuittingResponseInvariantOnUnitCube` and its polynomial
version in `Stationary/ResponseInvariantQuotientPolynomial.lean` for every
merged partition. The discrete partition retains Gamma, whose determinant
is six and whose inverse is strictly positive. At offset -1, every LCP
solution satisfies x=Gamma^-1(1+w)>0, so w=0 and the unique active Jacobian
has positive determinant. Its R0 degree is therefore one, also after
positive row scaling, failing the named degree-not-one quotient selector.

## 4. Marked invariance inside every player's reward box

The tested predicate is universal Nash preservation of
min_(i in M) u_i<=0 for each nonempty M, with u restricted to the Cartesian
product of the native playerwise reward ranges including zero.
It is NOT invariance only on the actual strategic carrier.

Three rational controls suffice for all fifteen choices of M. The first is

    q=(0,7/10,3/10,17/20),
    u=(0,-131/7,19,724/105).

It is a Nash root with every output coordinate positive and both u0=0 and
u1<0, hence defeats every mark containing0 or1. The other hazards are

    (3/20,1/200,7/10,1/5), (7/10,1/200,0,3/100).

For these set u_i=(Q_i-P_i)/H_i, making every endpoint comparison an
equality. They defeat respectively marks{2},{2,3} and mark{3}. The checker
verifies all endpoint conditions, all fifteen mark choices, and every
playerwise lower/upper reward bound exactly. These controls do not establish
actual-source realizability, and they do not refute invariance restricted to
an arbitrarily small neighborhood. Those stronger scopes remain unclaimed.

## 5. Pair, actual-source, and complete weak return prerequisites

All three pair partitions fail at least one strict scheduled joining gain
J_i,mate-Gamma_i,mate>0 and at least one scheduled J_i,mate>=0. These are
necessary in `FINITE_INVARIANT_CONE_PAIR_UNIFORM_EQUILIBRIUM.md`, the
positive-inverse asymmetric pair producer, and the signed-inverse-column
producer (strict positive Gamma^-1 forces its column signs all positive).
There is no mutually positive singleton pair and no all-nonpositive
participant recipient, defeating the corresponding friendly-matching,
flat-recipient-anchor, and passive-threshold prerequisites under every role.
The full inverse is positive, but both inverse-positive principal triples
012 and013 have outside inverse row (-1/4,-5/4,-1/4), so every passive-inverse
child selection fails.

The stronger participant-cap condition (1) in
`CALENDAR_POLYTOPE_UNIFORM_EQUILIBRIUM.md` fails for every nonempty marked
set, ordered partition, and positive weight choice. If the mark meets123,
use coalition123: all its participant rewards (10,3,3) are positive, so the
first marked block meeting that coalition has positive weighted sum. If
the mark is{0}, use grand coalition reward Z0=3. This argument uses the
source's ALL-coalition cap domain, not a proper-only substitute.
`ACTUAL_MARKED_SOURCE_NEIGHBORHOOD_UNIFORM_EQUILIBRIUM.md` §8.1 keeps two
nonpositive participant rows throughout its chosen epsilon<=1/100
neighborhood. Every row of this completion has a positive participant
entry, excluding every labeling of that stated family. These raw failures
are independent of the virtual controls in §4, which do not satisfy every
passive-Never cap bound and are not declared actual.

The zero J03 boundary is checked against FULL necessary conditions, not
just a failed strict-premium sign. For all24 roles, weakening every strict
sign in the following named initial tests still leaves a negative primitive:

* `SCALAR_SINGULAR_CIRCUIT_UNIFORM_EQUILIBRIUM.md` §§3--4;
* `CODEX_COORDINATOR__COMPLETE_SOLO_RETURN_GEOMETRY.md` §7, requiring BOTH
  its macro pair and reset pair in the same four-role assignment;
* `CORE_FREE_JOINT_RETURN_UNIFORM_EQUILIBRIUM.md` §1;
* `JOINT_QUITTING_NEGATIVE_VALUE_UNIFORM_EQUILIBRIUM.md` §1.

The maxima over roles of their minimum primitive are respectively
-2,-2,-4/5,-3. Their complete sign lists appear in the checker; the
original source hypotheses have been checked against these lists. These
strict obstructions also exclude the closures of those raw criteria.

The general `THREE_OWNER_JOINT_RETURN_UNIFORM_EQUILIBRIUM.md` §1 allows
more singleton signs. Weakening its six initial conditions leaves exactly
roles(1,0,3,2) and(1,2,0,3). The first has nonsingular elimination
b=2/5,D=1/5 and the required hazard x=-2, strictly impossible. The second
has b=7/2957,D=2894/2957,x=7/1447 but requires U0=C+lambda*a0>0 with
lambda>0, whereas C=-14/1475 and a0=-8759/2950. No positive lambda can work,
including an escaping sequence; both signs persist nearby. These exact
full-source failures exclude the closure too. Every Gamma column also has
a positive off-diagonal entry, excluding the negative-pivot-column
prerequisites of `ZERO_PREMIUM_JOINT_PHASE_UNIFORM_EQUILIBRIUM.md` and
`ONE_JOINT_PHASE_WITH_DIFFUSE_SOLO_EXITS.md` under every relabeling and in
their closures.

## 6. The actual new producer and the closest old return algebra

The new roles are (r,j,k,o)=(1,0,3,2). The shared owner's native value is0
at both phases. Its exact Q_r=P_r=0 equations give

    M=[-2,-6;1,-2], h=(-10,3),
    (u,v)=M^-1 h=(19/5,2/5), q0=5/24, q3=5/7.

Let b be the unique root in(5526/10^6,5527/10^6) of

    175496570 b^2-12603641 b+64295=0,

and put

    s=(-348b^2-1080b+35)/(2(-174b^2+139b+35)).

The two rows are qA=(0,s,0,0) and qB=(5/24,b,0,5/7). The four active
comparisons vanish exactly; all four quiet gaps are strictly negative.
The phase-A native player3 value lies in(-.292,-.291), and its participant
premium J31=-4/5 is negative. Native phase-B player0 also has negative
value. Negative native continuation therefore does not prevent the direct
one-date return. Every player-deleted opponent cycle contracts, so all
prescribed and deviated profiles absorb almost surely. Only for this reason
does adding own levels back preserve every terminal comparison.

The existing semantic consumer is
`isUniformEquilibriumPayoff_quittingCyclicTerminalValue_of_certificate`
in `UniformEquilibrium/Quitting/Cycles/PeriodicCompiler.lean`; the adjacent
`isZeroAsymptoticNash_quittingCyclicBehaviorProfile_of_certificate` gives
exact terminal Nash. Their inputs include the supplied hazards, policy
values, every root comparison, and playerwise opponents-only contraction.
They do not select hazards from arbitrary reward data. The new raw linear
solve, finite quadratic-root selection, direct quiet tests, and exact
payoff formulas construct every such input.

The closest prior algebra is section1 of
`THREE_OWNER_JOINT_RETURN_UNIFORM_EQUILIBRIUM.md`. Map its roles(0,1,2,3)
to actual(0,2,3,1). Its triple023 is actual013 and its solo3 is actual solo1.
Its linear elimination gives

    d=2,e=1,a3=-6,v=-2,w=-3,t3=10,omega=-2,
    J0=-10,J1=14,b_old=5/7,D=24/7,x=5/24.

Thus the shared-owner linear solve and subsequent quadratic return mechanism
already occur there. They should be reused rather than counted as new
operations. That old raw producer nevertheless fails: its c>0 is actual
J31=-4/5, and its U2>0 is the new profile's negative phase-A player3 value.
In its notation, C=5/2,a0=-199/2,T=45/38,a2=-25231/95 and
U2=T+lambda*a2<0 at lambda=b/(1-b). The all24-role check in section5
excludes every alternate role of the FULL old criterion as well.

The complete-solo-return note permits signed joining rewards but its scalar
classification retains positive outer endpoints. Its separate positive-
continuation raw producer requires a pair with both participant premiums
positive; no current pair has this property. Hence it supplies no prior
producer for the present game. The new contribution is a signed direct-return
class and the complete nondegenerate proper singleton/overlapping-triple
decision test, not a claim to have invented the linear/quadratic elimination.

## 7. Further named periodic and cyclic-child source comparisons

The implemented
`exists_periodThreeClearedGapData_and_uniformPayoff_of_visible_affine_reward`
in `UniformEquilibrium/Quitting/Examples/Cyclic/FourPlayerOverlappingPeriodThreePositiveAffineCylinder.lean`
uses the fixed visible radius1/50000000 about its literal center, followed by
positive recipient scales and shifts. Every singleton coordinate is visible.
The center has reciprocal positive singleton-difference pairs01 and23,
each direction3; those signs persist in the stated box and under positive
row scaling. The present Gamma has no reciprocal positive pair. Thus every
relabeling of that actual raw cylinder fails. This is a fixed-domain test,
not an assertion about an unspecified maximal continuation neighborhood.

The raw statements in `CYCLIC_CHILD_WITH_ONE_JOINT_PHASE.md`,
`NEGATIVE_PREMIUM_CYCLIC_CHILD_UNIFORM_EQUILIBRIUM.md`,
`GLOBAL_TWO_JOINT_CYCLIC_CHILD_UNIFORM_EQUILIBRIUM.md`,
`REPEATED_SOLO_EXIT_WITH_POSITIVE_OUTSIDER_BUFFER.md`, and
`ONE_JOINT_PHASE_WITH_DIFFUSE_SOLO_EXITS.md` require a pivot singleton
column negative at every other receiver. Every column of the present Gamma
has a positive off-diagonal entry. Thus their raw classes fail in every
role, including positive row scaling. The implemented `CyclicChildJointPhase.RawTable`
and `CyclicChildJointPhase.exists_uniformPayoff` in
`UniformEquilibrium/Quitting/Cycles/CyclicChildJointPhaseSource.lean`
have this same literal negative-column requirement.

There IS a signed cyclic triple013 in this matrix. Its existence alone
is not a four-player producer: its outside inverse row is negative, as
section5 checks. No blanket absence of cyclic triples is claimed. No claim
is made about an unspecified maximal radius in the qualitative full-
dimensional cyclic-child neighborhood theorem.

`TRIPLE_SINGLETON_COLLISION_BOX_UNIFORM_EQUILIBRIUM.md` requires all six
internal directed joining increments positive before any subset selection.
Every current triple has a negative such increment (use01 in012/013,
23 in023, and12 in123), so every triple/subset role fails. Its singleton
and triple are also disjoint, unlike the new overlapping architecture.
`THREE_OWNER_JOINT_POSITIVE_PASSIVE_TRIPLE_UNIFORM_EQUILIBRIUM.md` is a
stationary producer and is excluded by section1's complete stationary census.
The fixed `SIGNED_COLLISION_BRIDGE_UNIFORM_EQUILIBRIUM.md` singleton source
requires a reciprocal positive pair, absent here under every relabeling.

As a further necessary-source check, punishment normality does not provide
an old exit. For players0,1,2,3 use sure opponent coalitions{1,2},{0},{3},{2}.
Their native Quit/Never endpoint pairs are(-30,-10),(-6,-2),(-3,-1),(0,-1).
`quittingPunishmentValue_le_pureRowCap` in
`UniformEquilibrium/Quitting/Punishment/ContinueFloor.lean` bounds the actual
original punishment values by-9,-1,0,1, respectively, all <=own singleton1.
This shows the necessary normality bounds hold; it is not an additional
nonexistence theorem or a punishment-only equilibrium producer.

## 8. Admission scope

This audit checks named raw criteria over their complete relevant selections:
stationary supports, actual sure-first tails, persistent base/free/Nash choices,
proper universal child lifts, all weights in the specified domains, all
quotient partitions, all finite role assignments and the stated weak/closure
variants. Their failure is compatible with the NEW absorbing two-phase
solution. It is not a certificate that every conceivable earlier UE theorem
or arbitrary supplied strategic interface fails.

The new statement is an actual-data producer; it assumes no minimizing law,
positive gap, observer constrained attainment, favorable child equilibrium,
or selected periodic certificate. Its inputs are raw arithmetic tests and
at most two computed real roots. It therefore requires no exceptional
conditional admission. A simple selected root and strict quiet guards
produce an open neighborhood in all60 original coordinates. The independent
unbounded freedoms concern exactly the24 unused recipient/coalition entries
and the14 monotone quiet-player changes stated in the packet; other passive
rows are not silently declared free. General Fin4 remains open.
