# Uniform equilibrium from a nonconvex full-cap chamber

## Exact statement

Let I=Z/4Z. Live and Never payoffs are0. Choose arbitrary finite real
numbers K_i,G_i, for i in I, satisfying

    K_i>=7,                     G_i<K_i.                  (1)

At the first finite quitting date the nonempty quitting coalition S
receives the following ORIGINAL terminal reward vector:

    singleton{i}: own1, opposite recipient i+2 gets4, neighbors0;
    adjacent pair{i,i+1}: donor i gets-1, successor i+1 gets2,
                         both outsiders get1;
    opposite pair: members0, outsiders1;
    triple I\{i}: members get-1, outsider i gets K_i;
    grand coalition I: recipient i gets G_i.              (2)

Labels are modulo4. Prescribed private clocks are independent laws on
Nat union{Never}. Responses are ALL complete behavioral replacements,
including every finite deadline, Never, and arbitrary private mixtures.

Theorem. For EVERY raw table(1)--(2), there is a fixed vector v and a
sequence of actual independent behavior profiles whose prescribed
terminal payoffs and FULL unilateral caps both tend to v. Consequently
v is a uniform-equilibrium payoff for the original quitting game.

There is no upper bound on K_i, no lower bound on G_i, and no aggregate
condition on the grand row. The conclusion is table-by-table, with no
uniform rate over this unbounded parameter set. An exact terminal Nash
profile, stationary Nash profile, or explicit calendar is not asserted.

## Conjecture-facing change

This is an unconditional raw-data existence class, not a consumer of
assumed strategies or continuation certificates. Its new step is a
nonconvex chamber in the CLOSED ACTUAL prescribed-payoff/FULL-cap
carrier. A positive-debt point in this chamber cannot have a full-support
cap-Nash root. Every surviving root preserves the chamber and scales all
debts by its joint Continue mass. Compact constrained minimization then
forces a diagonal in the actual carrier.

This differs from minimizing debt on the entire carrier, where a positive
minimum can be trapped at caps strictly above the own-singleton values.
The literal actual seed and its invariant inequalities are essential;
they are not supplied by cap-Nash debt scaling alone. No convexification,
continuous Nash selector, or persistent exact-root spine is used.

Section7 gives an exact K_i=10,G_i=9 member and bounded WHOLE-selection
comparisons with applicable existing producer families. In particular
its singleton degree is1, its actual response quotients give no
degree-not-one exit, and it has NO exact stationary Nash profile. This
does not claim noncoverage of every conceivable certificate or of an
unknown distant implicit-function neighborhood. The full Fin4 conjecture
and arbitrary-table production remain open.

## Strategic inputs

No strategic input is assumed. The proof produces or obtains:

* an actual independent seed, including its exact FULL caps, in Section3;
* a nonempty compact constrained carrier from that seed;
* a cap-Nash root by finite mixed Nash existence, or explicitly on an axis;
* exclusion of sure and full-support roots where needed, directly from
  the raw rewards;
* an attained zero-debt semantic pair by compact minimization; and
* actual terminal approximants with one fixed payoff target from actual
  carrier membership, followed by the full-behavior uniform consumer.

There is no assumed clock profile, best-reply maximizer, return word,
punishment law, strategic selection function, or vanishing-error source.

## 1. Full semantics and source correspondence

For an actual independent profile p, let U_i be its prescribed terminal
payoff and B_i the supremum over ALL complete unilateral replacements.
Write

    d_i=B_i-U_i>=0,                 D=max_i d_i.

Never encounters only passive rewards0,1,4,K_i, or Never0. Hence B_i>=0,
even for very negative G_i. For each fixed table all rewards, U_i and B_i
are bounded. Let S be the closure of ALL actual pairs(U,B). It is compact,
inherits d_i>=0 and B_i>=0, and is invariant under every fixed product
root prefix. No convexity is assumed.

At a product root q in[0,1]^4 set

    c=product_i(1-q_i),    alpha_i=product_(j!=i)(1-q_j),
    Q_i=E[r_i(A union{i})],
    b_i=E[r_i(A)*1_(A nonempty)],

where A is the independent opponent quitter set at that root. Exact full
prefix semantics is

    U_i'=q_i Q_i+(1-q_i)(b_i+alpha_i U_i),
    B_i'=max{Q_i,b_i+alpha_i B_i}.                       (3)

The two-action stage game with continuation B pays r at a nonempty root
quit set and B upon all Continue. If q is ANY exact mixed Nash root of
this finite game, each player's mixture attains its larger endpoint:

    B_i'=q_i Q_i+(1-q_i)(b_i+alpha_i B_i),
    d_i'=c d_i,                   D'=cD.               (4)

Finite mixed Nash existence is unconditional. Cap attainment is not
needed. For a fixed root, (3) is continuous in(U,B), so it preserves the
closed actual carrier at limiting pairs even if the root is Nash only
at the limit, not at approximating profiles.

The existing checked source facts are:

* `quittingTerminalSemanticCarrier`,
  `exists_terminalProfile_sequence_tendsto_semanticPair`,
  `quittingTerminalSemanticCarrier_isCompact`,
  `continuous_quittingTerminalSemanticPrefix`, and
  `quittingTerminalSemanticPrefix_mem_carrier` in
  `UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`;
* `exists_isZeroQuittingRootNash` in
  `UniformEquilibrium/Quitting/Root/NashExistence.lean`;
* `quittingTerminalSemanticDebt_prefix_eq_continueMass_mul_of_capNash`
  and
  `quittingTerminalSemanticPrefix_envelope_eq_rootSuccessorPayoff_of_capNash`
  in `UniformEquilibrium/Quitting/Root/CapNashRootStack.lean`;
* `isUniformEquilibriumPayoff_of_diagonal_mem_terminalSemanticCarrier`
  in
  `UniformEquilibrium/Quitting/Classification/Existence/UniformPayoffTerminalSemanticCarrier.lean`.

These are generic checked semantic results. The raw-family chamber
invariance and its zero-debt conclusion below are the new ordinary
mathematics to be formalized.

## 2. No sure cap-Nash root

This exclusion holds for ANY real continuation B. Suppose player i
Quits surely. Opposite i+2 has joining-minus-Continue differences

    -4, -2, G_(i+2)-K_(i+2),

according as zero, one, or two of the other nonowners Quit. All are
strictly negative by(1), so the opposite strictly Continues. Predecessor
i-1 then has joining differences-1 or-2, so also strictly Continues.
Successor i+1 strictly joins for2 instead of0. The original sure owner
i now gets-1 and can withdraw for0, a contradiction.

Every cap-Nash root therefore has q_i<1 for all i. Its positive
coordinates are interior, so their Quit and Continue endpoints agree.

## 3. An actual full-cap seed and its compact chamber

Let players0,2 Never. Independently, each of players1,3 Quits at date0
with probability1/2 and otherwise Never. Exact values and FULL caps are

    U=(1/4,5/4,1/4,5/4),
    B=(1/2,5/2,1/2,5/2),
    D=5/4,                    sum B-4=2.                (5)

For recipient0 or2, the pure responses Quit0, any positive finite date,
Never pay respectively1/4,1/2,1/4. For recipient1 or3 they pay
1/2,5/2,2. Every response law is a mixture of these pure responses.
Thus these are full caps, not a sampled-deadline annotation. No variable
passive-triple or grand reward is encountered. An outsider's Quit0 can
form a triple, but its own reward there is the FIXED participant reward-1.

Consider the nonempty compact set

    C={(U,B) in S: min_i B_i<=1,
                       sum_i B_i-4 >= (8/5)D(U,B)}.     (6)

The seed proves nonemptiness. We prove preservation under EVERY cap-Nash
prefix from a POSITIVE-debt point of C. Preservation at zero debt is
unnecessary, since a diagonal already supplies the conclusion.

## 4. Root supports at positive-debt chamber points

### 4.1. Full support is impossible

Suppose q has full support and put z_i=q_i/(1-q_i)>0. For recipient i
let x=z_(i-1), y=z_(i+2), w=z_(i+1), T=xy+xw+yw, V=xyw.
The exact odds numerators of Quit and the opponent-stop term are

    P_i=1+2x-w-T+G_i V,
    N_i=4y+T+K_i V.

Because alpha_i=1/product_(j!=i)(1+z_j), active indifference gives

    B_i=P_i-N_i=1+2x-w-4y-2T+(G_i-K_i)V.

With Z=sum_i z_i, E2=sum_(i<j)z_i z_j, and V_i the product of the three
opponent odds, summation yields

    sum_i B_i=4-3Z-4E2+sum_i(G_i-K_i)V_i<4.             (7)

But positive debt in C implies sum B>=4+(8/5)D>4. Hence EVERY cap-Nash
root at such a point has support at most three. This is a DERIVED
support restriction, not an imposed root alphabet. It removes any need
for a grand-row charge inequality or an upper bound on G_i.

### 4.2. Every surviving root preserves a low cap

A singleton-support root owned by i has output cap B_i'=Q_i=1.

For an adjacent active pair rotate to q=(a,b,0,0). Active equalities give

    B0=(1-2b)/(1-b),       B1=(1+a)/(1-a),
    B0'=Q0=1-2b<1.

B0>=0 forces b<=1/2. For an opposite active pair q=(a,0,b,0),

    B0=(1-5b)/(1-b),       B2=(1-5a)/(1-a),
    B0'=Q0=1-b<1.

Thus a,b<=1/5 and sum_i q_i<=1 in the opposite case.

For support three, rotate the missing label to3 and write q=(a,b,e,0),
with all a,b,e>0. Direct raw endpoints are

    Q0=1-2b-e+be,       b0=(4-3b)e,
    Q2=1-a+b-2ab,       b2=(4-3b)a.

Active equality and B>=0 give

    1-2b-5e+4be>=0,
    1-5a+b+ab>=0.

Hence b<=1/2, a<=(1+b)/(5-b)<=1/3, and
e<=(1-2b)/(5-4b)<=(1-2b)/3. In particular

    sum_i q_i=a+b+e<=2/3+b/3<=5/6<1,
    B0'=Q0<1.                                         (8)

No varied reward occurs in these ACTIVE endpoint equalities. The
inactive player's Nash condition may involve K_i or G_i; it is retained
by finite-game Nash existence, not replaced by these necessary bounds.
Together with(7), these cases prove min B'<=1 for every nonzero root
at a positive-debt chamber point. All Continue preserves its input cap.

## 5. The total-cap ledger and minimization

Let P1 be the root probability of exactly one Quit, P_adj and P_opp the
two kinds of double Quit, and P_(3,i) the probability that exactly
I\{i} Quits. Section4 excludes full support at positive-debt chamber
points, so their root grand probability P4 is0. Total rewards are5 on
a singleton,3 on an adjacent pair,2 on an opposite pair, and K_i-3
on triple I\{i}. Equation(4) gives

    sum B'-4=c(sum B-4)+H,
    H=P1-P_adj-2P_opp+sum_i(K_i-7)P_(3,i).             (9)

If every q_j<1 and sum_j q_j<=1, then P1>=2P2, where
P2=P_adj+P_opp. To prove this, set z_j=q_j/(1-q_j), Z=sum z_j.
For Z>0, Cauchy gives

    sum_j q_j=sum_j z_j/(1+z_j)
                 >= Z^2/(Z+sum_j z_j^2).

The premise sum q_j<=1 implies2E2=Z^2-sum z_j^2<=Z. Multiplying by
c yields2P2<=P1. The zero root is immediate.

The opposite and three-support roots satisfy this premise by Section4.
Since K_i>=7,

    H=(P1-2P2)+P_adj+sum_i(K_i-7)P_(3,i)>=0.

For an adjacent pair, H=a+b-3ab>=0 because b<=1/2: if b<=1/3 this
is immediate, and otherwise its minimum over0<=a<=1 is1-2b>=0.
For singleton support H=q_i>=0; all Continue gives H=0.

Therefore EVERY cap-Nash prefix from a positive-debt point of C obeys

    min B'<=1,       sum B'-4>=c(sum B-4),       D'=cD,

and remains in C. No grand-row total has been assumed.

Let (U*,B*) attain the minimum D* of D on C. Suppose D*>0. Its cap sum
exceeds4 and its minimum cap is at most1. There is a NONZERO exact
cap-Nash root:

* If min B*<1, all Continue is not Nash. Finite mixed Nash existence
  supplies a nonzero root.
* Otherwise all caps are>=1 and some exceed1. Choose a cycle edge
  i to i+1 with B_i*=1 and B_(i+1)*>1, and let only i Quit with

      0<p<min{1,(B_(i+1)*-1)/(B_(i+1)*+1)}.

  Owner i is indifferent. Successor Continue is
  (1-p)B_(i+1)*>1+p, its Quit endpoint. Predecessor Continue is at
  least1-p>=1-2p, its Quit endpoint. Mate Continue is at least
  4p+1-p>=1-p, its Quit endpoint. Thus this is a nonzero exact Nash
  root using only singleton and pair rewards.

By Section2 all q_j<1, and nonzero q gives c<1. Its prefix remains in C
but has D'=cD*<D*, a contradiction. Consequently D*=0, so U*=B*.
Diagonal membership in S supplies actual independent profiles with U and
FULL B converging to the SAME target v=U*. Their maximum complete
terminal regret tends to0. The source correspondence in Section1 gives
the asserted fixed-target uniform-equilibrium payoff.

A root appearing only at the minimizing limit is legitimate because its
FIXED prefix map is continuous and preserves S. It need not be Nash at
nearby approximating caps. No Nash-selector continuity or convergence
of one exact-root spine is used.

## 6. Boundary tests

* K_i=7 is allowed. Its triple coefficient in(9) is0, not negative;
  every other required term remains nonnegative.
* The symmetric data K_i=L,G_i=L-1 work for EVERY finite L>=7.
  Thus the theorem has no hidden large-reward upper bound.
* K_i=7,G_i=-H for EVERY H>=0 are allowed. Full caps stay nonnegative
  by Never, though the reward bound and compact carrier depend on H.
* Grand coordinates can approach their K_i arbitrarily closely from
  below. The no-sure comparison remains strictly negative separately
  for each table; no uniform margin as G_i tends to K_i is asserted.
* At G_i=K_i for ALL i, the no-sure lemma is false: all players Quit0
  is already an exact terminal Nash profile, because withdrawing earns
  exactly the same K_i. This boundary is not a UE counterexample.
* If all G_i>K_i, all players Quit0 is a strict terminal Nash profile.
  Thus the hypotheses are sufficient structural conditions, not a
  necessary classification of UE tables.
* For a K_i<7 the corresponding charge in(9) becomes negative; the
  present proof does not infer preservation. No claim of nonexistence
  outside the stated class is made.

## 7. Exact surviving-center and bounded source comparisons

Take K_i=10,G_i=9 for every recipient. The following comparisons concern
this ONE exact member, not disjointness of the entire family from all
older existence classes. They show that the new theorem supplies actual
new counterexample-class narrowing rather than a stronger profile on
an already admitted raw class.

### 7.1. Singleton degree and actual response quotients

The singleton comparison matrix, with diagonal0 and off-diagonal
r_i({j})-r_i({i}), is

    Gamma=[0,-1,3,-1; -1,0,-1,3; 3,-1,0,-1; -1,3,-1,0],
    det Gamma=45,
    Gamma^-1=(1/15)[2,3,7,3;3,2,3,7;7,3,2,3;3,7,3,2].

It is R0. Every principal block of size at least2 is invertible, so a
nonzero homogeneous complementary solution cannot have that support;
an axis solution fails a negative external neighbor entry. At offset
ones, the ENTIRE strictly complementary root set consists of the empty
root, four adjacent supports with active coordinates(1,1), and four
triples with rotated active coordinates(1/2,5/2,1/2). Opposite supports
would have negative active coordinates and the full solution is negative.
The principal-determinant indices sum1-4+4=1. Thus the degree-not-one
singleton exit is unavailable, despite the positive inverse.

Every deleted triple has determinant6 and a negative inverse diagonal.
This defeats EVERY child choice in
`PassiveRowInverseCriterion.exists_uniformEquilibriumPayoff_of_raw_nonnegativeInverse_triple`
in
`UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/RawPassiveRowInverseCriterion.lean`.
The positive singleton-comparison edges form an opposite matching, not
a directed four-cycle, so the signed-four-cycle singleton hypotheses
cannot be supplied by relabeling.

Actual response invariance is stronger than matrix symmetry. The
necessary singleton block-row test on all15 partitions leaves seven:
discrete, all-block,02|13,01|23,03|12,02|1|3,0|13|2.
The first three are actual invariant quotients, with matrices Gamma,
[1], and[[3,-2],[-2,3]], respectively. Each has positive determinant
and degree1. The remaining four fail equality of the ACTUAL response
residual H_i=(1-alpha_i)Q_i-b_i on the block-constant cube:

| blocks | hazard vector | unequal residuals |
| --- | --- | --- |
| 01\|23 | (0,0,1/2,1/2) | H0=-7/8, H1=-23/16 |
| 03\|12 | (0,1/2,1/2,0) | H0=-23/16, H3=-7/8 |
| 02\|1\|3 | (0,0,0,1/2) | H0=3/4, H2=0 |
| 0\|13\|2 | (0,0,1/2,0) | H1=0, H3=3/4 |

This uses `QuittingResponseInvariantOnUnitCube` and
`quittingSingletonBlockRowSum_eq_of_responseInvariant` in
`UniformEquilibrium/Quitting/Stationary/ResponseInvariantQuotient.lean`.
In particular,
`finFour_exists_uniformEquilibriumPayoff_of_responseQuotient_nonnegative_inverse`
in `UniformEquilibrium/Diagnostics/Quitting/FinFourResponseQuotientCriterion.lean`
requires a NEGATIVE determinant as well as nonnegative inverse. None of
the actual quotients meets it; a matrix-only candidate is insufficient.

### 7.2. Every exact stationary Nash component is excluded

Section2 excludes sure hazards. Support0 leaves Quit gain1. With one
active i, successor i+1 has Never value0 and positive Quit value. With
two adjacent active players, the successor also has Never value0 and
positive Quit value. With two opposite active players, either Never
value is4 while its Quit value is at most1. In every case an interior
stationary clock cannot be a full best reply.

For support three rotate to q=(a,b,e,0). Stationary indifference uses
the endpoints in Section4 and gives

    Q0=1-2b-e+be, b0=(4-3b)e,
    Q1=1+a-2e-ae, b1=ae.

Because b0>0, Q0=b0/(b+e-be)>0, so b<1/2. Also
(5/2)e<b0=Q0(b+e-be)<(1+e)/2, whence e<1/4.
For the displayed upper bound, use Q0<1-2b and the exact identity

    (1+e)-2(1-2b)(b+e-be)
                    =(1-e)(1-2b+4b^2)+4be>=0.

But Q1>1/2 and b1/(a+e-ae)<=e<1/4, a contradiction.

For full support use the odds notation of Section4, and put
L_i=x_i+y_i+w_i, T_i=x_i y_i+x_i w_i+y_i w_i,
V_i=x_i y_i w_i, A_i=L_i+T_i+V_i. At K=10,G=9,

    P_i=1+2x_i-w_i-T_i+9V_i,
    N_i=4y_i+T_i+10V_i.

Stationary indifference would require
F_i=N_i(1+A_i)-P_i A_i=0 for every i. Exact expansion yields

    sum_i F_i=sum_i z_i+Q(z)
      +sum_i[9V_i+3T_i(2y_i+w_i)+2T_i^2
              +V_i(-x_i+5y_i+2w_i)+3T_i V_i+V_i^2],

    Q(z)=2sum_i z_i^2+(z0-z2)^2+(z1-z3)^2
                                      +7sum_i z_i z_(i+1).

Every term is nonnegative after grouping2T_i^2-x_i V_i: its six
monomial coefficients are2,2,2,3,4,4. Moreover sum z_i>0. Hence the
four F_i cannot all vanish. This excludes EVERY exact stationary Nash
profile, and therefore every sound raw producer whose conclusion is
such a profile, independently of its parameter selections or thresholds.
It says nothing about the stationary regret infimum or general clocks.

### 7.3. Whole trap, weight and charge selections

Define an inserted premium by r_i(S union{i})-1. The sole nonempty
premium trap is all4: a trap must be closed under the entire directed
incoming participant-premium cycle of rewards2. Every player's outgoing
participant reward-1 also defeats the common/protected-participant floor
requiring all its participant rewards to be at least its singleton1.

Every nonzero nonnegative upper-average weight w fails the grand test,
which is8sum_i w_i>0. For the GLOBAL weighted-floor test
sum_i w_i[r_i(S union{i})-1]>=0 for EVERY S, summing the four singleton
tests gives-2sum_i w_i<0. Thus no permitted positive or nonzero
nonnegative reweighting rescues either criterion. The global floor
definition is `HasGlobalQuittingWeightedFloor` in
`UniformEquilibrium/Quitting/Classification/WeightedQuittingTrapLeavers.lean`.

For the full trap and every NONEMPTY PROPER coalition S define

    P(S)=sum_(i notin S)[r_i(S union{i})-1],
    L(S)=sum_(i notin S)[r_i(S union{i})-r_i(S)].

These are the inserted-premium and OUTSIDER insertion sums, not member
withdrawal sums. Their exact values are

    singleton: P=-2, L=-3;
    pair:      P=-4, L=-4;
    triple:    P=8,  L=-1.

Any boxed-charge coefficients delta,tau,gap,loss must therefore satisfy
delta<=2, tau>=8, gap<=3, loss<=1. Their charge is at most

    4sqrt(delta/tau)(gap+delta*loss/tau)
      <=4sqrt(2/8)(3+2/8)=13/2 < 4+4*10.

Thus the whole boxed predicate fails, not just one coefficient choice.
The actual definitions are `QuittingTrapChargeCoefficients`,
`quittingTrapInsertedPremiumSum`, and `quittingTrapLeaveSum` in
`UniformEquilibrium/Quitting/Classification/BoxedQuittingNashCharges.lean`.
Together with the failed upper-average alternative, this also defeats
that mixed upper-or-charge source on its only trap.

### 7.4. Whole induced-base and universal quiet-lift selections

An accepted full induced-base row, retaining all omitted-player joins
and base-player leaves, would give a full stage Nash root with a sure
player. Section2 excludes EVERY such root, regardless of the base,
free carrier, or continuation. At the center the full-complement induced
Nash sets can also be read directly: singleton base has only its
successor join; adjacent/opposite bases have all outsiders Continue;
triple base has its outsider Continue. The rejected owner/base gains
are respectively-1,-1,-4,-2, and the grand withdrawal gain is-1.
Actual punishment values are0: Never guarantees nonnegative payoff,
and a sure successor singleton holds the player's entire cap to0.
Thus a singleton punishment-tail comparison cannot repair its owner
gap. These are the actual base/free games of
`UniformEquilibrium/Quitting/Root/PersistentBaseInducedGame.lean`.

For ANY nonempty proper child C choose j in C whose successor j+1 is
outside C. Such j exists because C is not closed under the whole cycle.
In the child, sole j Quit0 and everybody else Never is exact full Nash:
the predecessor's join gives-1 instead of0, the opposite's join gives0
instead of4, and the successor is absent. The child's joint-Never mass
is0. In its full quiet lift, missing successor j+1 can Quit0 for2
instead of0. Hence ALL child debts and the Never residual are0, while
one outsider's full debt is2.

This excludes EVERY child and EVERY weight choice in universal raw
certificates bounding outsider debt by weighted child debts plus a
finite joint-Never residual. In particular it contradicts the conclusion
of `quittingLiftDeletedProfile_outsideDebt_le_add_neverExcess_of_withdrawalFutureJoin`
in
`UniformEquilibrium/Quitting/Classification/QuietExtension/WithdrawalFutureJoinFixedTarget.lean`
for any proposed raw certificate, and the corresponding weighted-debt
consumer `quietLift_outsideBehaviorDeviationDebt_le_weighted_childDebt_add_slack`
in
`UniformEquilibrium/Quitting/Classification/QuietExtension/CappedClockChildDeletionAdapter.lean`
with ANY finite Never slack, since the child's Never mass is0. It does
not rule out a new consumer restricted to selecting a favorable child
equilibrium.

### 7.5. Bounded calendar-template comparisons

Every triple contains a donor join with gain-1 or an opposite join with
gain-4. Thus all selections requiring six strict joining inequalities
inside one triple fail. Every pair partition leaves an incoming reward2
outside someone's scheduled pair: an involutive mate relation cannot
contain all four directed predecessor edges. This violates the common
cross-pair cap at most1 in the crossed and two-pair join-cap templates,
under EVERY partition. Also every actual pair has a nonpositive member;
there is no pair with both participant rewards positive. In particular
the literal four-joint-pair templates requiring positive participant
rewards on every scheduled pair cannot apply, nor their local version
with center rewards at least2 and radius at most1/2. The template
requiring both favorite pair rewards above(5+sqrt(5))/2 also has no pair.

The positive four-singleton word with each opposite favorite two phases
later has only two chronological orientations, up to relabeling. Its
WHOLE positive owner-field solution can be calculated. Let u_l in(0,1)
be chronological Continue probabilities. Owner indifference is

    E_l=u_l[4-4u_(l+1)+u_(l+1)u_(l+2)]-1=0.

Put a=u0-u2 and b=u1-u3. Opposite differences are

    E0-E2=4(1-u1)a-u2(4-u0)b,
    E1-E3=u3(4-u1)a+4(1-u2)b.

Their coefficient determinant is
16(1-u1)(1-u2)+u2u3(4-u0)(4-u1)>0. Hence a=b=0.
Writing u0=u2=x,u1=u3=y, the remaining difference is
(4+xy)(x-y)=0. The common equation factors as
(u-1)(u^2-3u+1)=0, giving the UNIQUE proper positive solution
u=(3-sqrt(5))/2. At an owner's root the next and preceding nonmate's
prescribed values are respectively u and1, by direct singleton-path
evaluation using u[4(1-u)+u^2]=1. Their immediate Quit endpoint is
u+(1-u)r_i({i,owner}); the necessary cross-pair caps are respectively0
and1. An incoming reward2 violates one of them in either orientation.
This excludes that entire positive singleton-word architecture, not
merely its symmetric guess. It does not exclude longer calendars or
an unnamed distant neighborhood with unquantified radius.

These are bounded comparisons over the stated complete selections,
not an exhaustive classification of every conditional verifier. No
inference from simple distance to another theorem's center is used.

## 8. Adapter, consumer, and narrow Lean handoff

The actual-data adapter takes arbitrary K,G satisfying(1), constructs
the literal finite reward function(2), and proves a diagonal member of
its actual terminal semantic carrier. It does not take a cap vector,
Nash root, strategy, punishment, or semantic diagonal as an input.

The downstream endpoint is
`isUniformEquilibriumPayoff_of_diagonal_mem_terminalSemanticCarrier`.
Its hypotheses are supplied directly by Sections1--5, so the conclusion
uses unrestricted unilateral behavioral replacements and a fixed payoff
target, not bounded-controller testing or varying targets.

A narrow implementation can define this literal Fin4 reward family and
prove the following ordinary-mathematics lemmas in order:

1. No exact root Nash has a sure quitter, for arbitrary continuation.
2. A full-support cap-Nash root forces(7).
3. At B>=0, each support of size at most three satisfies the low-cap
   bound and nonnegative charge(9).
4. The explicit independent seed has full semantic pair(5).
5. The compact chamber(6) has a diagonal by attained debt minimization.
6. The named actual-semantic consumer yields existence of a uniform
   equilibrium payoff for every K,G satisfying(1).

Likely definitions are `quittingTerminalSemanticPair`,
`quittingTerminalSemanticCarrier`, `quittingTerminalSemanticPrefix`,
`IsεQuittingRootNash`, and the full semantic debt from
`UniformEquilibrium/Quitting/Root/CapNashRootStack.lean`. Fin4 support
enumeration can be literal; no new LCP theorem, root selector,
classifying state machine, or speculative repository refactor is needed.
The chamber and the literal seed must be PROVED, not encoded as assumed
structure fields. The new table-specific conclusion is ordinary
mathematics here, not an asserted checked Lean declaration.

## Scope and nonclaims

The result supplies a fixed uniform payoff for the complete raw family
(1)--(2). It does not settle arbitrary Fin4 or all finite quitting games,
produce an exact terminal Nash profile, identify an explicit limiting
payoff, give a convergence rate, or prove bounded-calendar completeness.
It uses no public correlation or convexity of independent-law payoffs.

The transferable mechanism is constrained minimization in an ACTUAL
semantic carrier, with an ACTUAL seed and reward-proved positive-debt
escape invariants. The unresolved arbitrary-table step is to produce
such a seed and closed region, or a different legal global operation.
Neither the unconstrained global minimum nor cap-Nash debt scaling
alone supplies that missing step.
