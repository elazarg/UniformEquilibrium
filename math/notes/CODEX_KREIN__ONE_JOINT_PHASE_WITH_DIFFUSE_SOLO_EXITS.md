# One joint phase with diffuse solo exits

Ordinary mathematical draft. This is not a checked Lean theorem.

## Exact statement

There are four players I={0,1,2,3}. A finite quitting game specifies a
vector r(S) in R^4 for every nonempty S⊆I. At each live date players
independently choose Quit or Continue. The first nonempty quitting
coalition S absorbs at reward r(S); perpetual continuation pays zero.
Before absorption the stage reward is zero. Strategies and unilateral
deviations may be arbitrary behavioral strategies with independent private
randomization and observation of the public history. There is no public
correlating device.

Choose finite real parameters

    a,b,c,h_1,h_2,h_3>0,       abc>1,
    u,v<1,                    xi,eta>0,
    q_2,q_3≤0.

Put D=abc−1, s_1=1−u, s_2=1−v, L=ac+a+1, and

    nu_1=(ac*h_2+c*h_1+h_3)/D,
    nu_2=(ab*h_3+a*h_2+h_1)/D,
    nu_3=(bc*h_1+b*h_3+h_2)/D,
    R_low=1+(s_1*nu_1+s_2*nu_2)/nu_3,
    R_high=1+ac*s_1+a*s_2.

Choose R_low<R<R_high. Prescribe

    r({0})   = (1,−h_1,−h_2,−h_3),
    r({1})   = (u,0,b,−1),
    r({2})   = (v,−1,0,c),
    r({3})   = (R,a,−1,0),
    r({0,1}) = (1+xi,eta,q_2,q_3).                       (1)

The only further restrictions on the reward table are

    r_2({0,2})≤0,  r_2({1,2})≤0,  r_2({0,1,2})≤0,
    r_3({0,3})≤0,  r_3({1,3})≤0,  r_3({0,1,3})≤0.       (2)

Every unspecified reward coordinate is arbitrary and finite. In particular,
there is no upper bound on eta, on the two participant rewards at {2,3},
or on any coordinate of the four-player coalition.

**Theorem.** Every table (1)-(2) has one fixed uniform equilibrium payoff.
More precisely, the table produces a target V and, for every ε>0, actual
independent finite stopping laws on a common finite time menu such that
their terminal payoff is within ε of V in every coordinate and their
terminal exploitability against every complete behavioral deviation is
at most ε. Thus one profile and one horizon threshold at each accuracy
give payoff delivery and equilibrium for every sufficiently long horizon.

The selected nonpivot laws also have optimal unrestricted pivot-repair
value at most ε. The target precedes ε; rates and continuation values
used to select that target are produced by the proof, not assumed.

## Conjecture-facing change

This is a raw-table producer for a four-player class with a positive
simultaneous-quitting premium for both members of one actual prescribed
pair. Every table in the class strictly violates the product-low premium
criterion. The proof combines an explicit pivot-first rate selection with
refinement of its two solo phases. The refinement permits arbitrary
participation rewards away from the six undiffused outsider coordinates
in (2).

The class is not all four-player quitting games. The prescribed singleton
sign geometry, interval condition, collision harms in (1), and six
inequalities (2) remain assumptions. The result produces approximate
terminal equilibria; an exact finite periodic equilibrium is asserted
only under the additional cap in the corollary below.

## Strategic inputs

No strategy, stopping law, continuation target, cycle, or fixed point is
supplied as a hypothesis. The proof constructs all four rates, three
coarse continuation values, an accuracy-dependent refinement, actual
independent behavioral strategies, finite censored laws, and one fixed
target from the numerical table conditions.

All expectations used in the deviation comparisons are conditional only
on the live public history at the relevant date. The final payoff and
regret bounds are unconditional. A deviation can change the player's
entire future strategy, including Never, and need not be stationary,
periodic, or finitely supported.

## Proof

### 1. The parameter interval and a pivot branch

The positive vector nu satisfies

    a*nu_3−nu_2=h_1,
    b*nu_1−nu_3=h_2,
    c*nu_2−nu_1=h_3.

Consequently

    R_high−R_low=[(c*s_1+s_2)h_1+s_1*h_3]/nu_3>0.       (3)

Put Y=D/(bL), so 0<Y<c/(c+1)<1. For 0≤y≤Y set

    H_j(y)=h_j(1−y)−q_j*y>0,                    j=2,3.

For 0<y≤Y and

    0≤k<K(y)=min(by/H_2(y), [c−(c+1)y]/H_3(y)),

define

    z=(H_3(y)k+y)/[c(1−y)],
    d=1+by+[1−H_2(y)]k,
    w=[by−H_2(y)k]/d,
    p=1+xi*y.

Here d=1+k+[by−H_2(y)k]>0 and 0<z,w<1. Define

    P(k,y)=p+
      { (p−u)y/(1−y)+(p−v)z }/[(1−z)w].                (4)

For each fixed y, z increases strictly in k, while

    w_k=−[H_2(y)+by]/d²<0.

Both p−u and p−v are positive, so P increases strictly in k. As k tends
to K(y), either w tends to zero or z tends to one; the positive numerator
in (4) stays away from zero. Therefore P tends to infinity.

At k=0,

    P_0(y)=p+
      [(c+1)p−cu−v]*(1+by)/[b(c−(c+1)y)].               (5)

This function is continuous and strictly increasing on [0,Y]: each
positive factor in its second summand increases, and its rational factor
increases strictly. Its endpoints satisfy

    P_0(0)=1+[c*s_1+s_2]/(bc)<R_low,
    P_0(Y)=L*(1+xi*Y)−ac*u−a*v
          =R_high+xi*Y*L>R_high.                        (6)

The first inequality follows from nu_1/nu_3>1/b and
nu_2/nu_3>1/(bc), consequences of the three identities above. The
second equality follows by substituting Y in
(1+bY)/[b(c−(c+1)Y)]=a.

Thus there is a unique y_star∈(0,Y) with P_0(y_star)=R. For each
0<y<y_star there is a unique k_R(y)∈(0,K(y)) with P(k_R(y),y)=R.
Set k_R(y_star)=0. Strict monotonicity and fixed local brackets around
each root prove continuity in the interior. At y_star, any fixed small
positive k has P(k,y_star)>R, so the same upper-bracket argument proves
k_R(y)→0. Finally k_R(y)≤by/H_2(y)=O(y), which gives k_R(y)→0 at zero.

### 2. Closing the remaining scalar equation

The limit tau=lim_(y→0) k_R(y)/y exists and satisfies

    R=F(tau),
    F(t)=1+[s_1+s_2*(1+h_3*t)/c]/(b−h_2*t).             (7)

Indeed k_R(y)/y is bounded. Multiplying (4) by (1−z)w/y shows that
every subsequential limit t satisfies

    (R−1)(b−h_2*t)=s_1+s_2*(1+h_3*t)/c.

The right side is positive, excluding t=b/h_2. There is exactly one
solution,

    tau=[b(R−1)−s_1−s_2/c]/[h_2(R−1)+s_2*h_3/c]>0.

Every subsequential limit is this number. The positive fractional function
F strictly increases on [0,b/h_2), and the identities for nu give
F(1/nu_1)=R_low. Hence tau>1/nu_1.

Along the branch k=k_R(y), define

    G(y)=h_1*k+z−a*w*(1−z)
          +eta*k*[1−(1−z)(1−w)/(1+k)].                  (8)

It is continuous on (0,y_star]. Since k,z,w=O(y), its eta term is
O(y²) for every fixed finite eta. Therefore

    lim_(y→0) G(y)/y
      =h_1*tau+(1+h_3*tau)/c−a*(b−h_2*tau)
      =(D/c)*(nu_1*tau−1)>0.                            (9)

At y_star one has k=0. Clearing the positive denominator
c(1−y_star)(1+by_star) shows that G(y_star) has the sign of
y_star*(bL*y_star−D), which is negative because y_star<Y.
The intermediate value theorem supplies a selected y∈(0,y_star)
with G(y)=0. Set k=k_R(y) and x=k/(1+k). This produces all four
rates x,y,z,w in (0,1), without a bound on eta or a uniqueness assertion
for (8). Fix this selection once, before choosing the accuracy.

### 3. Coarse values and exact Continue transport

Use a joint row A with hazards (x,y,0,0), a solo row B with hazard z
for player 2, and a solo row C with hazard w for player 3. Set t=eta*x
and define the four coordinates explicitly by

    V_A=(p,t,w/(1−w),0),
    V_C=((1−w)p+Rw, (1−w)t+aw, 0, 0),
    V_B,0=v*z+(1−z)*V_C,0,
    V_B,1=(1−z)*V_C,1−z,
    V_B,2=0,
    V_B,3=c*z.                                          (10)

Equations (4) and (8) say respectively

    V_B,0=(p−uy)/(1−y),       V_B,1=k(h_1+eta).          (11)

At A the pivot's Quit payoff is p and its Continue payoff is
uy+(1−y)V_B,0=p. Player 1's Quit payoff is t and its Continue payoff
is −h_1*x+(1−x)V_B,1=t. The actual A values for players 2 and 3 are

    [by−H_2(y)k]/(1+k)=w/(1−w),
    [−H_3(y)k−y+c*z*(1−y)]/(1+k)=0.

These formulas include q_2 and q_3 on the actual collision {0,1}.
The B and C recurrences follow directly from the singleton vectors (1).
Every pure-Continue endpoint equals its corresponding displayed value,
and the prescribed policy satisfies the full vector recurrence.

All nonpivot values are nonnegative. The pivot values are at least one:
V_A,0=p>1, (11) gives
V_B,0−1=(xi+1−u)y/(1−y)>0, and
V_C,0=(V_B,0−v*z)/(1−z)>1. The two solo owners have value zero both
before and after their own row. At A, conditions (2) bound the forced-Quit
payoffs of players 2 and 3 by zero. Thus the nondiffuse joint row already
has every required action comparison in the original table.

### 4. Refining solo rows

For a positive integer n put

    z_n=1−(1−z)^(1/n),       w_n=1−(1−w)^(1/n).

Repeat A, then n consecutive solo player-2 rows of hazard z_n, then n
consecutive solo player-3 rows of hazard w_n. The identities

    (1−z_n)^n=1−z,          (1−w_n)^n=1−w

preserve each block's aggregate hazard. The terminal coalition law is
unchanged, so the actual initial payoff is the fixed vector V_A for every n.

Within the player-2 block, a remaining aggregate hazard rho∈[0,z] gives
value rho*r({2})+(1−rho)*V_C. It lies on the segment between V_B and
V_C. Similarly the values within the player-3 block lie on the segment
between V_C and V_A. These values retain the coordinatewise singleton
floor s=(1,0,0,0), and the current solo owner has value zero throughout
its block. Exact policy evaluation and exact pure-Continue transport
therefore hold at every refined date.

Let

    C=max({0} union
      { (r_i({i,j})−s_i)_+ : j∈{2,3}, i≠j }),
    e_n=C*max(z_n,w_n).                                  (12)

At a solo j-row of hazard delta, a different player's forced-Quit payoff
is s_i+delta*(r_i({i,j})−s_i), at most s_i+C*delta and hence at most
its displayed value plus e_n. The solo owner's Quit payoff equals its
zero value. All forced-Quit endpoints at A were already bounded without
error. Thus every forced-Quit endpoint on the refined path is at most
its value plus e_n, and e_n→0.

### 5. Every complete deviation incurs only one error

Fix n and a player i. Add e_n to its displayed value at every date.
If Continue has immediate expected absorbing reward a and opponent
survival probability q≤1, exact transport says a+q*V_next=V. Hence

    a+q*(V_next+e_n)≤V+e_n.

Quit is also bounded by V+e_n. The same bound holds for every mixed
behavioral action conditional on the live history. Iterating these two
inequalities bounds the deviator's terminal payoff by V_A,i+e_n plus
a bounded surviving remainder.

Its opponents have the same survival product over one refined period
as over one coarse period. For each deviator this product is

    product_(j≠i)(1−q_j^*)<1,
    (q_0^*,q_1^*,q_2^*,q_3^*)=(x,y,z,w).

It does not depend on the deviator's strategy. The remainder therefore
tends geometrically to zero. This gives terminal exploitability at most
e_n against every behavioral deviation, including late and Never
deviations. The argument does not multiply e_n by the number of visits.
Equivalently, direct telescoping charges the error only when the deviator
first Quits while live; that event occurs at most once.

The same zero-remainder argument applied to the exact policy recurrence
identifies the displayed values with the actual payoff, so there is no
unproved value annotation. It also bounds all values by any bound on
the absolute original rewards.

### 6. Finite laws, pivot repair, and uniform payoffs

Each player's complete stopping law is induced by its periodic independent
hazards. Censor every marginal after K refined periods by moving all later
finite atoms to Never. The sum of changed marginal masses is

    tau_K=(1−x)^K+(1−y)^K+(1−z)^K+(1−w)^K→0,            (13)

independently of n. If M bounds the absolute ORIGINAL rewards, product
coupling bounds prescribed payoff change by 2M*tau_K. The same coupling
with an arbitrary fixed deviator bounds its payoff change by 2M*tau_K.
Thus the censored profile has terminal exploitability at most

    e_n+4M*tau_K,

and payoff error at most 2M*tau_K relative to V_A. Choose n first and
K second to make both smaller than any prescribed positive accuracy.
The censored laws live on one finite time menu. With the three nonpivot
laws fixed, their optimal pivot repair does no worse than the displayed
feasible pivot law, proving the claimed repair bound.

The standard fixed-target terminal-to-uniform theorem now applies:
arbitrarily accurate terminal Nash profiles whose terminal values approach
one fixed target give a uniform equilibrium payoff at that target. It
retains one actual profile from this family for every requested accuracy
and one threshold for all sufficiently large finite horizons. No horizon
threshold is required to be uniform across different accuracies.

### Exact-Nash corollary under participant caps

If every nonsingleton T≠{0,1} additionally satisfies r_i(T)≤s_i for
each participant i∈T, then C=0. Already the original three-row profile
has all Quit endpoints bounded by (10). The same complete-deviation
argument proves exact terminal Nash, with target V_A. All four rates
are selected by the same proof; this corollary does not assume a cycle.

## Boundary tests

At the product root with player-0 and player-1 hazards both 1/2 and all
other hazards zero, the two and only active players have singleton-relative
Quit premiums xi/2 and eta/2, both positive. Thus every table (1)-(2)
strictly violates `HasProductLowQuittingPremium`. This remains true under
sufficiently small reward perturbations.

An exact rational instance has a=b=c=2, h_1=h_2=h_3=1, u=v=0,
q_2=q_3=−1, xi=1, eta=17/11, and R=1735/368. Its selected rates and
three values are

    (x,y,z,w)=(1/11,1/4,7/30,4/15),
    V_A=(5/4,17/121,4/11,0),
    V_B=(5/3,14/55,0,7/15),
    V_C=(50/23,7/11,0,0).

Equations (4),(8),(10),(11) hold by rational arithmetic. Another instance
has a=b=c=2, all h_j=1, u=1/2, v=−1/2, q_2=−2, q_3=−3, xi=1,
eta=62786/809, R=321377/96330, and

    (x,y,z,w)=(1/101,1/4,53/300,195/599),
    V_A=(5/4,62786/81709,195/404,0).

Here R_low=3<R<6=R_high, and eta is far above the bound required by a
monotonicity argument for the nonpivot equation alone. The pivot-first
construction uses no such bound.

For an exact test of the refinement, take the first instance and the
completion described below, then change only r_2({2,3}) to any beta>0.
The coarse row C gives player 2 value zero, while quitting there gives
beta*w>0, so the coarse profile is not Nash. The refined profile has
the identical target, and the full deviation gain is at most beta*w_n→0.
This demonstrates why the enlarged theorem asserts approximate profiles
and why arbitrary positive participation rewards require the refinement.

### A completion outside the proper-child F/J criteria

For the first rational instance, define every remaining coalition by

    r_0(S)=1 if 0∈S, and R*1_(3∈S) otherwise;
    r_j(S)=0 if j∈S,
           −1 if j∉S and 0∈S,
           2*1_(pred(j)∈S)−1_(succ(j)∈S) otherwise,

with the cycle 1→2→3→1, and replace r_0({0,1}),r_1({0,1}) by 2,17/11.
Every proper nonempty child S has an exact child Nash profile with joint
Never zero and an omitted player with strictly positive deviation debt:

1. For S⊆{1,2,3} of size one or two, one child quits surely at date zero.
   With two children choose the owner giving the other reward 2. A missing
   child receives −1 and can join for zero.
2. For S={1,2,3}, repeat solo hazards 1/2 in order 1,2,3. The cycle's
   three-player values are (0,1,0), (0,0,1), (1,0,0), so it is exact Nash.
   The quiet pivot payoff is R/7<1, whereas quitting at the first phase
   gives 3/2.
3. If 0∈S and 3∉S, every child quits surely at date zero. Withdrawal
   lowers each participating nonpivot's payoff to −1, and lowers the
   pivot's payoff to zero. The pair {0,1} only increases its members'
   own rewards. A missing child receiving −1 can join for zero.
4. If {0,3}⊆S and 2∉S, child 3 alone quits surely at date zero. The
   pivot receives R>1 and retained player 1 receives 2; missing player 2
   receives −1 and can join for zero.
5. For S={0,2,3}, child 2 quits surely, pivot 0 quits with probability
   2/3, and child 3 quits with probability 1/R at date zero. Player 3's
   Continue payoff is zero; the pivot's Continue payoff is one; and
   child 2's Continue payoff is negative. Their Quit payoffs are 0,1,0.
   Omitted player 1 receives (2/R−3)/3<0 and joins for zero.

These cases cover all fourteen proper nonempty children. Each of the five
F/J withdrawal labels has the implication

    outside debt ≤ sum_i c_i*(child debt_i)+rho*(child joint Never),

with nonnegative coefficients. The displayed exact child profiles make
the right side zero and the left side positive. Therefore this particular
completion admits no full proper-child F/J family of any of the five
kinds. This separation is not asserted for arbitrary completions (2).

## Source correspondence

The positive and finite-law endpoints are existing declarations, distinct
from the ordinary raw-data producer above:

- `QuittingInfinitePathQuitErrorCertificate` and
  `QuittingInfinitePathQuitErrorCertificate.isεAsymptoticNash_and_delivers`
  in `UniformEquilibrium/Quitting/Paths/InfinitePathSupersolution.lean`
  require exact policy and Continue transport, a uniform Quit error,
  bounded values, and vanishing opponent survival. Sections 3-5 produce
  every field. The same file's
  `isUniformEquilibriumPayoff_of_arbitrarily_small_infinitePath_quitError`
  is a direct fixed-target consumer.
- `exists_uniform_quittingMeshScale` in
  `UniformEquilibrium/Quitting/Terminal/TargetTail/InfiniteSingletonMesh.lean`
  and `singletonArcCycle_isTerminalNash_and_hasValue` in
  `UniformEquilibrium/Quitting/Cycles/SingletonArcCycle.lean` already
  implement singleton subdivision and its nonaccumulating error bound
  for supplied paths. They do not select this mixed joint/solo path
  from (1)-(3).
- `quittingGame_uniformPayoffWitnesses_of_terminalTargetAcceptance_family`
  in `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`
  retains the actual finite censored profiles in Section 6 as uniform
  witnesses at the fixed target.
- `exists_objective_minimizer_eq_behavioral_infimum` in
  `UniformEquilibrium/Quitting/Terminal/PivotRepairBehavioralInfimum.lean`
  identifies the finite pivot optimization with the complete behavioral
  repair infimum. The constructed pivot marginal is a feasible competitor.
- `isUniformEquilibriumPayoff_of_isQuittingBlockCertificate` in
  `UniformEquilibrium/Quitting/Cycles/BlockPeriodicProfile.lean` consumes
  the exact capped-class corollary. It does not produce its rates.
- `HasProductLowQuittingPremium` in
  `UniformEquilibrium/Quitting/Classification/ProductLowQuittingPremium.lean`
  and `exists_uniformEquilibriumPayoff_of_productLowPremium` in
  `UniformEquilibrium/Quitting/Classification/Existence/ProductLowPremiumUniformPayoff.lean`
  concern a strictly excluded raw-table hypothesis, as shown above.
- `withdrawalFutureJoin_quietLift_outsideDebt_le_add_neverExcess` in
  `UniformEquilibrium/Quitting/Classification/QuietExtension/WithdrawalFutureJoinDebt.lean`
  supplies the common five-kind bound used in the completion test.

For that same completion, the singleton comparison matrix is

    M=[[0,−1,−1,R−1],
       [−1,0,−1,2],
       [−1,2,0,−1],
       [−1,−1,2,0]],              3<R<7.

It has full normal core: every row has a distinct negative witness.
It has no nonzero homogeneous LCP solution. If x_0>0, nonnegative
child residuals force every child coordinate positive; complementarity
then gives x_1=x_2=x_3=x_0. The pivot residual (R−3)x_0 is positive,
a contradiction. If x_0=0, any positive child coordinate forces all
three positive, and their invertible cyclic matrix forces them zero.

At offset (1,−1,−1,−1), child residual feasibility forces all three
children positive; complementarity gives x_j=1+x_0. The pivot residual
1+(R−3)(1+x_0)>0 forces x_0=0. This is the unique solution. Its
inactive residual is strict and its active determinant is 7>0. Thus
`exists_finset_r0Degree_eq_sum_sign_det` in
`MathUE/LinearProgramming/R0DegreeSum.lean` gives degree one, and
`isStandardQ_of_r0Degree_ne_zero` in `MathUE/LinearProgramming/R0Degree.lean`
gives standard Q. The homogeneous, non-Q, and nonunit-degree exits therefore
do not consume this completion.

The {0,1} principal has two negative off-diagonal entries: offset (−1,−1)
has no standard LCP solution, and its homogeneous residual inequalities
force zero. Thus the full matrix fails projective Q-bar. For the positive
three-child cyclic matrix A, the pivot's inverse row has middle entry
(R−7)/7<0. Every other triple has a row whose two off-diagonal entries
are negative, preventing an entrywise nonnegative inverse. The full
inverse has entry (0,1)=−(4R−7)/(7(R−3))<0. These exclude the applicable
nonnegative-inverse/passive-row tests, including
`exists_uniformEquilibriumPayoff_of_strictInverse_passiveRows` in
`UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/StrictInversePassiveRowCycle.lean`.

The same exact fixture has no nontrivial response-invariant partition.
The necessary first-order condition
`quittingSingletonBlockRowSum_eq_of_responseInvariant` in
`UniformEquilibrium/Quitting/Stationary/ResponseInvariantQuotient.lean`
requires rows in a common block to have equal sums over every block.
There are fourteen nondiscrete partitions of four players:

- For a single merged pair {0,1}, its two entries in singleton column 3
  require R−1=2, hence R=3. Each other merged pair has a remaining
  singleton column comparing −1 with 2. All six partitions fail.
- For two pairs, {0,1}|{2,3} has within-{2,3} row sums −1 and 2;
  {0,2}|{1,3} has within-{1,3} row sums 2 and −1;
  {0,3}|{1,2} has within-{0,3} row sums R−1 and −1.
  All three fail.
- Each triple containing 0 has a remaining singleton column with entries
  both −1 and 2. Only {0}|{1,2,3} survives this first-order test.
- For one full block, the child row sums are all zero and the pivot
  row sum is R−3. Equality would require R=3, which is false.

For the remaining partition take player-0 hazard x∈(0,1] and common
child hazard zero. Direct evaluation of the undiscounted individual
response field gives

    F_1=x+eta*x²,             F_2=F_3=x.

Indeed a child's absorbing Continue contribution is −x. Player 1's
forced-Quit payoff is eta*x, whereas players 2 and 3 have forced-Quit
payoff zero; opponent absorption is x. The definition
`quittingDiscountedDisplacement` in
`UniformEquilibrium/Quitting/Stationary/DiscountedDisplacement.lean`
at discount complement zero is exactly this expression. Since eta>0,
actual response invariance fails as well. Thus no nondiscrete partition,
including one unrelated to a reward automorphism, supplies a quotient
producer on this fixture. The discrete partition is the ambient matrix,
whose degree is one as computed above.

These are specific implementation-overlap checks, not a claim that all
producer predicates in the repository have been classified. The cited
existing declarations are source correspondences; the new real-variable
selection and its actual-data adapter remain ordinary mathematics here.

## Adapter, consumer, and Lean handoff

An actual table satisfying the finite numerical conditions provides every
input to Sections 1-2. One can formalize the scalar monotonicity, continuous
root branch, and endpoint sign change in game-independent mathematics.
The game adapter then supplies (10), refines the two explicit solo blocks,
and builds `QuittingInfinitePathQuitErrorCertificate` for each positive
accuracy. The existing exact-delivery and uniform-payoff consumers conclude
the result. For finite laws, combine (13) with product payoff coupling and
the finite pivot optimizer's competitor bound.

The certificate must be constructed from the table, not placed among the
assumptions of the theorem. No build or Lean trust assertion is made here.
Likely narrow formalization checks are the scalar selector, the literal
four-coordinate recurrences, and the mixed joint/solo refinement adapter;
the existing full-deviation comparison should be reused.

## Scope and nonclaims

This theorem is a special-class existence producer with unrestricted
deviations, not a completeness theorem for periodic profiles. It gives no
counterexample to the arbitrary four-player or finite-player conjecture.
The exact child obstructions are confined to the explicitly specified
completion, and exclude F/J certificates rather than child equilibria in
general. Neither the fixed target nor the source rewards change with the
requested accuracy.
