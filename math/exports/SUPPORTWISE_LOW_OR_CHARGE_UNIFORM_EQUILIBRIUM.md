# Supportwise low rewards or charges with same-sign pair exceptions

This is an ordinary mathematical reward-table theorem, with an existing
uniform-payoff consumer. Its new raw producer has not been checked in Lean.

## Conjecture-facing change

Each support with at least three active players can independently use either
product lowness or a finite boxed-charge bound. Mutually profitable pairs are
allowed when their two joining comparisons have the same weak sign. The
proof combines these tests in one selected-root producer and gives original
uniform equilibrium. The complete table below has a four-player premium core
and lies outside the preceding core, ledger, stationary, persistent-base,
and phase admissions specified below. The comparison checks their complete raw choices.
No strategy, continuation, selected root or return controller is an input.
The full Fin4 conjecture remains open.

## Finite game and raw hypotheses

The players are I={0,1,2,3}. At each natural date they independently choose
Continue or Quit. The first nonempty quitter coalition S absorbs at a finite
reward vector r(S); live and perpetual-Continue rewards are zero. Strategies
and unilateral replacements are unrestricted behavioral laws, with private
independent randomization. Write s_i=r_i({i})>=0, Z_i(S)=r_i(S)-s_i, and
M=max_(S nonempty,i)|r_i(S)|.

For a product root q, let Q_i(q) be the forced-Quit payoff. A support A is
FULL-SUPPORT PRODUCT-LOW if every root with support exactly A has some
active i with Q_i(q)<=s_i. Proper roots suffice: strict opposite inequalities
at a root with sure hazards persist after perturbing those hazards inward.

For every mutual-positive pair {i,j}, meaning
J_ij=Z_i({i,j})>0 and J_ji>0, require

    d_ij d_ji>=0,  d_ij=r_i({i,j})-r_i({j}).                (P)

For EACH support A of size m=3 or4, require at least one of:

- A is full-support product-low; or
- A passes the following finite boxed-charge test.

For every nonempty proper T subset A, define

    P_A(T)=sum_(i in A\T)[r_i(T union{i})-s_i],
    L_A(T)=sum_(i in A\T)[r_i(T union{i})-r_i(T)].

There must be positive constants D_A,tau_A,G_A,L_Astar with

    |T|=1:       P_A(T)<=-D_A, L_A(T)<=-G_A;
    2<=|T|<=m-2: P_A(T)<=0,    L_A(T)<=0;
    |T|=m-1:     P_A(T)<=tau_A,L_A(T)<=-L_Astar,

    K_A=m(D_A/tau_A)^(1/(m-2)),
    C_A=K_A(G_A+L_Astar D_A/tau_A)>sum_(i in A)s_i+mM.     (C)

Empty cardinality ranges impose nothing. Nontrap supports automatically
pass the product-low alternative, so the test may equivalently be restricted
to premium traps. No strategic root, annotation or continuation is supplied.

**Theorem.** These conditions imply a uniform-equilibrium payoff for r:
one target is fixed before accuracy, and for each accuracy one behavioral
profile and one threshold work at every larger horizon against all complete
unilateral deviations. Moreover, the native table Z has absorbing full-debt
infimum zero. Hence every nonnegative recipient-row raise of Z has a uniform
equilibrium as well, even if that raise no longer passes the displayed bound.

## Full endpoint semantics and strategic inputs

For q in [0,1]^4, let p_q(S) be the independent product probability of
coalition S, c=p_q(empty), and H_i=product_(j!=i)(1-q_j). At a continuation
annotation v, define

    Q_i(q)=sum_(T subset I-i) p_(q,-i)(T) r_i(T+i),
    C_i(v,q)=H_i v_i+sum_(empty!=T subset I-i) p_(q,-i)(T) r_i(T),
    w_i(v,q)=q_i Q_i(q)+(1-q_i)C_i(v,q).

An exact root is a Nash equilibrium of this finite two-action game:
q_i>0 implies Q_i>=C_i, and q_i<1 implies C_i>=Q_i. Finite mixed Nash
existence gives such a root at every annotation. Its support is {i:q_i>0}.
An annotation is an arbitrary vector, not an assumed strategy payoff.

Every input to the theorem is a comparison on the finite reward table.
The proof produces selected exact roots; the named semantic consumer
produces the behavioral profiles and fixed uniform target. No root selector,
continuation, clock, equilibrium, punishment, or source minimum is supplied.
Before absorption the only live public history is repeated all Continue.
Independent private stopping laws therefore represent all behavioral
strategies; complete replacements include every finite deadline and Never.

For an actual profile P, U_i is its prescribed terminal payoff and B_i is
the supremum payoff over EVERY complete unilateral replacement of player i.
Let D=sum_i(B_i-U_i), N_i be the original probability that i Never quits,
and nu=product_i N_i. Subscripts on U,B,D specify the reward table. The
native absorbing debt infimum A_Z is inf D_Z over actual profiles with
nu=0. All caps are finite because rewards are bounded. A replacement is a
mixture of pure deadlines and Never, so their supremum equals the full cap.

## Charged supports have no all-high root on one common box

First assume every product in (P) is strictly positive. The finitely many
strict gaps in (C) allow one number M<B<M+2 with

    C_A>sum_(i in A)s_i+mB                                (9)

for all supports assigned the charge alternative. If there are none, choose
any such B. At continuation v in [-B,B]^4, write C_i(v,q) for the forced
Continue offer, w_i=q_iQ_i+(1-q_i)C_i, c=product_i(1-q_i), and p_q(T) for
the product coalition probability. Every successor stays in the same box.

Suppose an exact Nash root has w_i>s_i for every i and support A of size
at least three. Product-low supports are impossible since active Q_i=w_i.
For a charged support, the exact whole-cube identity is

    sum_(i in A)(1-q_i)(Q_i-C_i)
      =c sum_(i in A)(s_i-v_i)
        +sum_(empty!=T proper subset A)p_q(T)L_A(T).        (10)

The left side is zero at a Nash root: active nonsure owners are indifferent,
and sure owners have zero prefactor. If some but not all hazards in A are
sure, choose a nonsure active i. The coalition A\{i} has positive probability
and a strictly negative L coefficient; c=0 and all other coefficients are
nonpositive. This contradicts (10). If all are sure, each inequality at
A\{i} gives a profitable withdrawal. Thus all active hazards are proper.

Put z_i=q_i/(1-q_i)>0, U=sum_A z_i, and
E=sum_(i in A)product_(j in A\{i})z_j. Sum the inequalities Q_i>s_i after
dividing each by its opponent Continue probability. Using (C) gives

    0<sum_T P_A(T)product_(j in T)z_j<=-D_A U+tau_A E.

The elementary symmetric-mean bound E<=U^(m-1)/m^(m-2) follows by averaging
unequal coordinates at a maximum with fixed U. Hence U>K_A. Divide (10) by
c and use D_A U<tau_A E to obtain

    sum_A(s_i-v_i)>=G_A U+L_Astar E
        >(G_A+L_Astar D_A/tau_A)U>C_A,

contrary to (9) and the box bound. Every all-high root is therefore supported
on a pair; a singleton has active Quit offer exactly its singleton.

## Pair indices and generic annotations produce selected return

If any pure pair is Nash, its comparisons are independent of v because each
owner faces another sure quitter. Playing it at the first date is an actual
absorbing terminal Nash profile and supplies UE directly. Otherwise fix an
annotation v with some v_h<s_h. All Continue is not Nash. Under the contrary
assumption that every exact root has w>s, the preceding argument leaves only
mutual-positive pairs {i,j}.

Let u_i=v_i-s_i and A_i=u_i+d_ij. Pair gaps are

    Q_i-C_i=-u_i+A_i q_j, Q_j-C_j=-u_j+A_j q_i.             (11)

One sure and one nonsure active hazard would force a nonzero d to vanish;
both sure give the excluded pure pair. Thus a bad root is interior on its
pair and is the unique possible candidate

    q_j=u_i/A_i, q_i=u_j/A_j.                             (12)

Interiority implies A_i and d_ij have the same sign, hence A_i A_j>0.
For each candidate and outsider k, multiply its full inactive gap after
substitution (12) by A_i A_j. The result is a polynomial in v whose coefficient
of v_k is -d_ij d_ji!=0: the opponent survival numerator is d_ij d_ji.
Exclude the zeros of these finitely many polynomials and the denominator
hyperplanes. Their complement is one open dense annotation set, fixed before
any roots are chosen.

At such a generic source every bad pair root has strictly negative inactive
gaps. Extend all endpoint polynomials to real hazards and define

    F_v(q)_k=min(1,max(0,q_k+Q_k(q)-C_k(v,q))).              (13)

Fixed points are exactly all finite-game Nash roots. Near a bad root the
inactive rows are constant zero and the active rows are unclipped. The full
ambient derivative of Id-F_v has pair block [[0,-A_i],[-A_j,0]] and an
identity inactive block; all higher-coalition effects remain in the upper
off-diagonal block. Its determinant is -A_i A_j<0.

There are finitely many bad roots, at most one per unordered pair, each with
local index -1. On (-1,2)^4, homotopy of F_v to the constant half-vector has
no boundary fixed point since all images lie in [0,1]^4. Total degree is +1,
contradicting the sum of the negative local indices. Therefore every generic
boxed v below a singleton has an exact root with some successor w_i<=s_i.

For any other boxed v below a singleton, approximate it by generic boxed
sources with the same strict below-singleton condition. Compactness of the
root cube and closed Nash inequalities give a limiting exact root whose
successor still has a coordinate <=s. The root cannot become All Continue,
which is not Nash at the limiting source. No continuous selector is required.

This supplies HasBoxedSelectedSingletonSublevelReturn on the box B. The
existing declaration
`exists_uniformEquilibriumPayoff_of_selectedSingletonSublevelReturn_of_reward_bound`
in `UniformEquilibrium/Quitting/Classification/Existence/SelectedSingletonSublevelReturnUniformPayoff.lean`
consumes the supplied return property, nonnegative singletons, M<B, and
B<=quittingRewardBound(r)+2. The last inequality follows from B<M+2.
No literal-core or ledger hypothesis is an input to that consumer.

## Weak products and the native absorbing conclusion

For each zero product in (P), perturb only the two passive singleton entries.
Give a zero gap the strict sign of its nonzero partner, or make both positive
if both vanish. Distinct pairs use distinct entries. All participant rewards,
own singleton levels, product-low predicates and P_A coefficients stay fixed.
Only singleton L_A coefficients can change, by O(delta), and the reward bound
changes by at most delta. Reduce each positive G_A slightly. The strict
threshold gaps in (C) persist for sufficiently small perturbations. Thus
arbitrarily close tables satisfy the strict theorem. Compactness of payoff
targets and reward continuity give one target for the original table, exactly
as in
`exists_uniformEquilibriumPayoff_of_arbitrarily_close_reward_tables` in
`UniformEquilibrium/Quitting/Terminal/TerminalExploitabilityRewardRobustness.lean`.

To obtain native absorbing debt, increase EVERY recipient's rewards on every
nonempty coalition by a fixed sufficiently small epsilon>0. Product-low and
joining data remain unchanged. Charge coefficients remain unchanged, while
the right side of (C) rises by at most 2m epsilon; all strict gaps persist.
The resulting table R is Z raised by c_i=s_i+epsilon>0 and has UE by the
theorem just proved. Native own zero makes finite deadlines tending to infinity
converge to literal Never. Every finite response gains c_i under the raise,
whereas Never gains c_i(1-N_{-i}). Hence for every actual profile

    B_i^R=B_i^Z+c_i, U_i^R=U_i^Z+c_i(1-nu),
    D_R=D_Z+nu sum_i c_i.                                (14)

The existing
`quittingTerminalDebtSumInf_pos_iff_not_exists_uniformEquilibriumPayoff` in
`UniformEquilibrium/Quitting/Terminal/TerminalDebtSumInf.lean`
gives actual profiles with D_R->0. Thus D_Z->0 and original joint Never
nu->0. Move the smallest original marginal Never mass to a finite date.
It is at most nu^(1/4); the repair changes four prescribed values and three
opponent-dependent caps by at most 2M_Z nu^(1/4) each. Consequently

    A_Z<=D_Z+14M_Z nu^(1/4)->0,

where M_Z=max(1,max|Z|). Every nonnegative recipient-row raise preserves debts
on these absorbing profiles, and the terminal approximate-Nash consumer gives
its fixed uniform target. No escaping finite mass is relabelled Never.

## Finite product-low certificates and exact scope

The product-low alternative contains no strategic witness. For a triple
A={i,j,k}, it is equivalent to the finite feasibility of w>=0, sum_A w=1,

    w_i J_ij+w_j J_ji<=0 for every pair in A,
    sum_(i in A)w_i Z_i(A)<=0.                            (15)

Dividing positive-Quit inequalities by the opponent hazards gives the strict
linear system J_ij y_k+J_ik y_j+Z_i(A)>0 with y>0. The elementary separating
alternative is exactly (15); feasibility at y>=0 perturbs to y>0.

For full support, a sufficient finite certificate is nonzero w>=0 with
sum_(i in S)w_i Z_i(S)<=0 for every nonempty S subset I. The weighted root
identity sum_i w_i q_i(Q_i-s_i)=sum_S p_q(S)sum_(i in S)w_i Z_i(S) proves
the claim. Weights may vanish. Neither this sufficient full-support certificate
nor the supportwise disjunction is asserted necessary for UE.

Choosing product-low at every larger support recovers the preceding closure;
choosing charges at every premium trap recovers the existing mixed-charge
mechanism. Supports may choose independently. The proof uses the same ambient
index and boxed-charge calculations, with the two alternatives meeting at a
single selected-return conclusion. The new raw producer has not been checked
in Lean. Arbitrary Fin4 remains open outside these hypotheses.

## 7. Separating reward table and boundary tests

All own rewards are one. This is the complete ORIGINAL table, in recipient
order 0,1,2,3; live and perpetual-Continue rewards are zero.

| S | r(S) |
| --- | --- |
| 0 | (1,0,4,0) |
| 1 | (0,1,0,4) |
| 2 | (4,0,1,0) |
| 3 | (0,4,0,1) |
| 01 | (-1,1,249/100,149/100) |
| 02 | (3,199/100,2,199/100) |
| 03 | (2,149/100,149/100,-1) |
| 12 | (149/100,-3,1,449/100) |
| 13 | (199/100,0,199/100,0) |
| 23 | (249/100,149/100,-1,1) |
| 012 | (-1,-1,-1,10) |
| 013 | (-1,5/4,10,-1) |
| 023 | (-1,10,-1,-1) |
| 123 | (10,-1,-1,2) |
| 0123 | (5,-1,5,-1) |

Write Z=r-1 on nonempty coalitions. The only mutually positive participant
pair is 02, with premiums (2,1) and joining gaps (-1,-2). The triple
certificates of the finite-test section are e1 on 012, e3 on 023, and (e1+e3)/2 on
013 and 123. The grand certificate is (e1+e3)/2. Direct substitution in
(15) and the grand certificate checks all inequalities, including zero coefficients. Thus the
theorem applies.

A premium trap is a nonempty A such that every i in A has some coalition
S subset A containing i with Z_i(S)>0. The greatest trap here is I:
02 witnesses owners 0,2, while 013 witnesses owner 1 and 123 witnesses
owner 3. The literal signed pair-core criterion therefore fails. Global
product-lowness fails at every proper positive root on 02. A supportwise
upper-average test also fails on that pair, and a boxed-charge certificate
requires at least three owners; their mixed supportwise criterion cannot
cover it. Every owner has a negative participant premium somewhere, so
no player has the global nonnegative-participant property.

### 7.1 Every nonnegative payoff-ledger selection fails

For a nonzero weight w>=0, a payoff ledger requires
H_w(S)=sum_i w_i Z_i(S)>=0 on every nonempty proper S. The exact vector
identity

    93 Z(01)+53 Z(03)+17 Z(12)+83 Z(23)
                    =(-1,-34/25,-73/50,-11/10)

contradicts these inequalities for EVERY such w. A finite family of
weights cannot help. The singleton comparison matrix and its inverse are

    Gamma=[0,-1,3,-1; -1,0,-1,3; 3,-1,0,-1; -1,3,-1,0],
    Gamma^-1=[2,3,7,3; 3,2,3,7; 7,3,2,3; 3,7,3,2]/15.

An arbitrary strictly positive coordinate matrix P cannot evade this test:
requiring sum_i(P Z(S))_i>=0 on every proper S supplies the positive H
weight 1^T P, already impossible, regardless of any additional product-cover
or cone parameters and reference grand reward.

The support-filtered version also fails completely. Its singleton ledger
conditions give w Gamma>=0. Invertibility and the strictly positive inverse
then force EVERY coordinate of w positive. All proper supports are therefore
safe and must satisfy the same H inequalities, already impossible.

For a nonnegative inserted-premium floor, singleton sets 1 and 3 give

    -2w0-w3>=0,       w0-w1-2w2>=0.

Their sum is strictly negative for nonzero w>=0. Thus every such floor
weight fails as well. These failures are preserved by positive recipient
scalings: absorb the scales into the weights.

The full trap cannot use the raw aggregate boxed-charge criterion either.
Its singleton premium and joining bounds force D<=1,G<=2; its grand
premium and leave bounds force tau>=4,Lstar<=5. Hence every coefficient
choice has charge at most 13/2, below sum s+4M=44.
A scaling-uniform check is also available. With Z'_i=lambda_i Z_i,
lambda_i>0, put t=max(lambda0,lambda2). The required middle premium
bound at 12 gives lambda3<=2lambda0. Singleton bounds then give
D<=4t,G<=4t, while tau>=4t and Lstar<=5t. Consequently
4 sqrt(D/tau)(G+Lstar D/tau)<=36t. The passive triple rewards in
rows 0 and 2 give M>=9t after any nonnegative own-level raise, so the
required strict charge threshold is at least 36t and is impossible.

### 7.2 No stationary equilibrium on any boundary support

All passive original rewards are nonnegative. Never therefore guarantees
nonnegative payoff. Suppose j is a sure quitter. Its opposite owner j+2
has strictly negative joining differences against every coalition containing
j. In the order of the other two hazards (0,0),(1,0),(0,1),(1,1), these
four differences are:

| j | Opposite owner's four gaps |
| --- | --- |
| 0 | (-2,-349/100,-249/100,-5) |
| 1 | (-4,-249/100,-249/100,-11) |
| 2 | (-1,-249/100,-349/100,-5) |
| 3 | (-4,-6/25,-249/100,-11) |

The opposite owner Continues. The predecessor j-1 then has two negative
gaps, respectively (-1,-249/100), (-1,-249/100), (-3,-249/100), and
(-1,-249/100). It Continues too. The successor j+1 now has positive gap
1,1,1,2, respectively, and Quits surely. Owner j receives -1,-3,-1,-1
instead of zero by withdrawing. Thus no stationary equilibrium has a sure
quitter. This checks mixtures and boundary choices of the other players.

All Never fails at own reward one. A sole active owner fails at its cyclic
successor. On adjacent pair supports 01,12,23,30, the successor has Never
payoff zero and Quit payoff 1,1,1,1+q3, respectively. On pair 02, owner 0
gets four from Never and at most three from Quit; on pair 13, owner 1 gets
four from Never and at most one from Quit. All pair supports fail.

It remains to check four proper triple supports. Write b_i for the passive
one-stage offer, H_i for opponent survival, and Q_i for forced Quit, in
ORIGINAL rewards. At a stationary active owner with contracting opponents,
Q_i=b_i/(1-H_i)>=b_i. Put epsilon=1/100.

On 013 let (a,b,c)=(q0,q1,q3). Owner 3 gives

    Q3-b3=1-2a-5b+(7/2+epsilon)ab>=0.

Affine endpoint checks force a<=1/2 and b<=1/5. Thus Q0>=3/5, while
Never0<=2b<=2/5. On 123 let (a,b,c)=(q2,q3,q1). Owner 1 gives

    Q1-b1=1-4a-5b+(11/2+epsilon)ab>=0.

The same endpoint check forces a<=1/4 and b<=1/5. Now Q2>=3/5 while
Never2<=2b<=2/5. Both supports are impossible.

On 012 put (a,b,c)=(q0,q1,q2). The exact relevant endpoints are

    Q0=1-2b+2c-2bc,       b0=4c-(5/2+epsilon)bc,
    Q1=1-4c+2ac,         b1=(2-epsilon)ac.

The inequality Q1>=b1 gives c<=1/(4-epsilon)<1/3. Active owner 1's
Never value is at most 2c, giving c>=1/6. The inequality Q0>=b0 gives
b<1/2. Owner 0's stationary residual is

    (1-H0)Q0-b0
      =b(1-2b)-c[3-(3/2+epsilon)b-2c(1-b)^2].

The bracket exceeds 3-151/200-2/3>3/2. The residual is therefore at
most 1/8-(3/2)(1/6)=-1/8, contradicting indifference.

On 023 put (a,b,c)=(q0,q2,q3). Here

    Q3=1-2a,             b3=(2-epsilon)ab,
    Q2=1+a-2c-ac,        b2=4a-(5/2+epsilon)ac,
    Q0=1+2b+c-5bc,       b0=4b-(3/2+epsilon)bc.

Active owner 3 gives

    b=a(1-2a)/[(5-epsilon)a-2a^2-1].

Its numerator and denominator are positive. The bound b<=1 gives
a>=1/(4-epsilon)>1/4; Q2>=b2 gives a<=1/3 and
c<1/6. The displayed b function decreases, since its derivative numerator
is -(8-2epsilon)a^2+4a-1<0. Consequently b>=1/(4-3epsilon)>1/4
and Q0<=1+2b. But the numerator of Never0-(1+2b) is

    b(3-2b)-c[1+(5/2+epsilon)b-2b^2]
                      >=5/8-2/6=7/24>0.

This excludes the last proper triple.

### 7.3 No full-support stationary equilibrium or stationary closure

For positive proper odds z define D=product_i(1+z_i), z_S=product_(i in S)z_i,
H(S)=sum_i Z_i(S), and J(S)=sum_(i outside S)[Z_i(S+i)-Z_i(S)].
At a full stationary Nash profile, summing the indifference equations
and separately averaging the actual absorbing rewards gives

    sum_(S nonempty) z_S H(S)
                =(D-1) sum_(S nonempty proper) z_S J(S).       (8)

Every H outside the pair rows is nonnegative. Five pair values are -1/50;
H(02)=249/50. Every proper J is <=-2. Therefore the left side of (8)
is at least -(1/50)sum_(i<j)z_i z_j, whereas the right side is at most

    -2(D-1)sum_i z_i <= -4 sum_(i<j)z_i z_j.

Strictly positive odds make equality impossible. Together with Section 7.2,
this excludes EVERY stationary profile, not merely fixed selected roots.

The singleton matrix is R0: if p>=0, Gamma p>=0 and p_i(Gamma p)_i=0,
then p=0. Indeed every principal block of size at least two is invertible:
pair determinants are -1 or -9, triple determinants are 6, and the full
determinant is 45. A singleton support fails at an external negative entry.
In fact there is a positive full-debt gap over ALL stationary profiles of
this original table. Otherwise take profiles with debt tending to zero.
A nonzero limiting hazard gives a stationary equilibrium by continuous
payoff and endpoint formulas; for a sole active limiting owner its positive
own reward makes Never unprofitable. This contradicts Sections 7.2--7.3.

If the hazards tend to zero, normalize them by their sum and pass to a
simplex limit p. The absorbing singleton law tends to p, so the limiting
payoff is 1+Gamma p. Immediate Quit tends to one, giving Gamma p>=0.
When p_i<1, Never against the opponents tends to
1+(Gamma p)_i/(1-p_i); comparison with the prescribed value gives
p_i(Gamma p)_i<=0. If p_i=1 that product is zero directly, because Gamma_ii=0.
Thus p is a nonzero homogeneous complementary vector, contradicting R0.
All Never itself has positive debt, so is not a missing case. Reward
continuity gives the same exclusion in a neighborhood. This covers both
moving-hazard stationary approximation and reward closure of exact stationary
producers, with all support, weight, cone and scale choices included.

### 7.4 Complete persistent-base and deletion tests

For a singleton persistent sure base {j}, induced Nash for free players and
outsider no-join conditions make all nonowners best respond to j. The strict
cascade of Section 7.2 forces the successor sure. Its action removes every
possible punishment-tail value from j's Continue endpoint, leaving the
strict owner withdrawal gain 1,3,1,1. Every free-set and induced mixed-root
selection therefore fails. With a base of size at least two, every player
faces a sure opponent; all owner, free and outsider comparisons would make
the full root Nash, already excluded by the same cascade.

The exact persistent-base interfaces are
`quittingSingletonBaseOwnerFloorExcess` and
`quittingPersistentLargeBaseExcess_nonpos_iff` in
`UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PersistentBaseConcreteGap.lean`,
and `exists_uniformPayoff_of_persistentBase_inducedNash_signs` in
`UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PersistentBaseNashSemanticAdapter.lean`.
This exclusion includes their punishment-floor selections; it is stronger
than the absence of stationary repetition of one induced row.

For any nonempty proper child set S, choose i in S with i+1 outside S.
Such an i exists because the successor map is a four-cycle. Sole-i stopping
is an absorbing exact Nash profile of that child: every other retained
owner has a strictly negative joining comparison. The omitted successor
has positive joining gain 1,1,1,2. Thus a universal nonnegative weighted
child-debt plus Never bound for the quiet lift fails at zero child debt and
zero Never. This tests every proper child, including all free calendar
choices. It does not exclude a conditional adapter supplied with a specially
selected safe child strategy.
The actual universal bounds used for this comparison are
`quietLift_outsideBehaviorDeviationDebt_le_weighted_childDebt_add_neverExcess`
in `UniformEquilibrium/Quitting/Classification/QuietExtension/CappedClockPositiveSingletonQuietExtension.lean`
and `withdrawalFutureJoin_quietLift_outsideDebt_le_add_neverExcess`
in `UniformEquilibrium/Quitting/Classification/QuietExtension/WithdrawalFutureJoinDebt.lean`.
Their child debt and Never terms vanish on the displayed child profiles.

### 7.5 Complete pair, phase and return screens

For the three pair partitions, list the two directed joining gaps on each
pair. They are

    01|23: (-1,1),(-1,1);
    02|13: (-1,-2),(-4,-4);
    03|12: (2,-1),(-3,1).

Thus no partition has all four joining gaps nonnegative. This rules out
all alternating-pair criteria requiring that sign condition, including
arbitrary positive-inverse, invariant-cone, bounded-corner or proof-weight
choices. Since Gamma^-1 is strictly positive, a signed-column requirement
Gamma^-1 diag(sigma)>0 forces every sigma positive and yields the same
obstruction. Every passive native pair entry is strictly positive, also
excluding pair criteria that require even one scheduled passive pair reward
to be nonpositive or negative.

There is only one mutually positive participant pair. Hence no partition
has four nonnegative participant premiums: each other pair has a strictly
negative endpoint. This excludes the nonnegative common-premium pair
criteria and the stated local or paid-joint templates requiring a positive
participant perfect matching. The favorite pairs 02 and 13 both have their
participant rewards strictly BELOW their passive singleton rewards, so no
favorite-pair funded-boundary choice with both joining gains positive works.
A template requiring even ONE above-singleton favorite participant also
fails, since all four favorite joining gaps are negative. For a negative
friendly-pair phase criterion with common normalized favorite singleton a,
common crossing singleton -b, and ONE common scheduled participant premium
Pi, the singleton equalities force the favorite matching 02|13 and equal
recipient normalizations. The four normalized participant premiums are then
proportional to (2,1,-1,-1), so cannot equal one Pi. This last exclusion does
not rely on a passive-reward sign, which such a criterion need not impose.
The cross pair 03 has positive premium Z0(03)=1. Thus neither an all-cross
nonpositive participant template nor an all-cross strictly-below-singleton
phase template works; every crossing pair in fact has a nonnegative
participant endpoint. Favorite-pair templates requiring every favorite
participant premium to be nonpositive fail on 02.

Reciprocal singleton signs are symmetric. Any cyclic or joint-return
criterion requiring Gamma_ij<0<Gamma_ji therefore fails under every
relabeling and positive recipient scaling. The four principal triple
singleton blocks have determinant 6 and negative inverse diagonal entries,
so none passes a nonnegative-inverse triple-extension test.

A broader three-owner joint-return selector does not require that reciprocal
sign pattern. Its relevant necessary tests, written in roles 0,1,2,3, are

    Gamma03>0, Gamma23<0, Z2(23)>0,
    J0+J1 b=0, 0<b<1,
    J0=e a3+d v, J1=e(t3-a3)-(omega+e)v,
    e=Gamma32, d=-Gamma30, w=Z3(02), v=Z3(23),
    a3=Z3(03), t3=Z3(023), omega=w+d-e.

The only positive crossing participant is actual owner0 on 03. The first
line therefore forces role2=actual0, role3=actual3, then role0=actual1
and role1=actual2. In this UNIQUE assignment J0=7 and J1=-201/50, so the
only linear root b=350/201 is inadmissible. Positive row scaling multiplies
J0,J1 by the same positive factor. The complete finite selector fails
before any later quadratic or continuation choice is made.

### 7.6 Marked-block, potential and boundary comparisons

For an ordered nonpositive-anchor criterion, let C be its nonempty marked
set, partitioned into ordered blocks with strictly positive weights. Its
first block meeting a coalition must have nonpositive weighted participant
premium. Coalition02 forces C disjoint from {0,2}. Thus C is a nonempty
subset of {1,3}, and its complementary set contains02. But every possible
marked row has Z1(02)=Z3(02)=99/100>0, contradicting the criterion's
mandatory nonpositive passive rewards on complementary coalitions. This
exhausts every marked subset, block ordering and weight choice.

The strict toggle-improvement cycle

    0 -> 01 -> 1 -> 12 -> 2 -> 23 -> 3 -> 03 -> 0

has gains (1,1,1,3,1,1,2,1), excluding every global ordinal toggle potential.
Positive recipient scaling and shifts on nonempty coalitions preserve these
strict gains. Criteria whose conclusion is an exact stationary profile are
already excluded by Sections 7.2--7.3, independently of their weight or
parameter choices.

These are exclusions of the exact raw selections described, not a claim
that every possible nonstationary equilibrium architecture is absent.
In particular an unspecified neighborhood radius or a conditional verifier
for supplied strategic data is not treated as an exhausted raw producer.

For a zero-product boundary test, change only r0(2) from four to three.
The pair02 gaps become (0,-2), while every participant certificate and
premium-core witness remains unchanged. The theorem's weak closure applies.
If instead r0(2)=2, the pair product is negative and that hypothesis fails;
no nonexistence conclusion is inferred from this failure.

## 8. Source correspondence and formalization handoff

The proof allows each support of size at least three to choose product
lowness or a boxed charge, while pair exceptions use their computed negative
indices. A literal two-player premium-core assumption is unnecessary. The existing raw
producer `exists_exactRoot_singletonSublevel_of_signed_pair_core` in
`UniformEquilibrium/Quitting/Classification/SignedPairCoreSelectedReturn.lean`
requires that literal core. Its index calculation and the proof here use
full four-player Nash endpoints, including quiet-player comparisons.

The relevant derivative result is
`pairNash_hasFDerivAt_and_negative_det_fullClippedDisplacement` in
`UniformEquilibrium/Quitting/Root/PairFullClippedJacobian.lean`.
The needed degree primitives are `ambientDegree_homotopy` and
`ambientDegree_affineRootField_eq_sign_det` in
`MathUE/Topology/AmbientDegreeHomotopyNormalization.lean`,
`ambientDegree_excision` in
`MathUE/Topology/AmbientDegreeProperties.lean`, and
`ambientDegree_of_selfMap_eq_one` in
`MathUE/Topology/AmbientDegreeSelfMapNormalization.lean`.
Finite additivity handles all possible bad pairs, not only one pair.

Define the raw higher-support predicate by restricting
`HasProductLowQuittingPremium` from
`UniformEquilibrium/Quitting/Classification/ProductLowQuittingPremium.lean`
to supports of cardinality at least three. Prove the selected-return
producer from the supportwise alternatives and strict pair products, split the pure-pair
Nash exit, and apply the exact consumer in the selected-return proof. Passive singleton
perturbations and the reward-closure declaration in the weak-products proof provide
weak pair products. No strategic witness belongs in the raw predicate.

The exact existing charge bound is
`QuittingTrapChargeCoefficients.threshold_lt_singletonSourceCharge` in
`UniformEquilibrium/Quitting/Classification/BoxedQuittingNashChargeOdds.lean`.
The native debt conclusion uses the terminal debt-infimum equivalence stated
above; the resulting absorbing approximate equilibria supply one fixed target
by `quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors`
in `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`.
All producer steps not supplied by these named declarations are proved here.
No new Lean verification is asserted.

For games with nonnegative own singletons, every counterexample must therefore
have either a mutually positive participant pair with opposite strict joining
gaps, or a support of size three or four that is not product-low AND fails
every boxed-charge parameter choice. Failure of these tests does not construct
a counterexample. Arbitrary games in this remaining disjunction are unresolved.
