# Boxed Nash charges beyond nonnegative linear floors

## 1. Finite raw hypotheses and the uniform-payoff conclusion

Let I be a finite nonempty player set. At each live date players
independently choose Continue or Quit. The first nonempty quitting
coalition S absorbs at reward vector r(S), received thereafter.
Live stages and perpetual continuation pay zero. Strategies and
unilateral deviations are arbitrary behavioral strategies based on
the game's public history, with independent private randomization.
No correlation device or memory restriction is added.

Write s_i=r_i({i}) and M=max_{S nonempty,i}|r_i(S)|. A nonempty
set A is a premium trap if every i in A has some S contained in A,
containing i, such that r_i(S)>s_i. Singletons are never traps.
For every nonempty proper T contained in A define two different sums:

    P_A(T)=sum_{i in A minus T}[r_i(T union {i})-s_i],
    L_A(T)=sum_{i in A minus T}[r_i(T union {i})-r_i(T)].

Assume every premium trap A has size m>=3 and admits positive
numbers d_A,tau_A,g_A,l_A with the following finite raw bounds:

    |T|=1:       P_A(T)<=-d_A,    L_A(T)<=-g_A;
    2<=|T|<=m-2: P_A(T)<=0,       L_A(T)<=0;
    |T|=m-1:     P_A(T)<=tau_A,   L_A(T)<=-l_A.       (1)

An empty intermediate range imposes no condition. The constants may
differ from trap to trap. Require also

    C_A=m*(d_A/tau_A)^(1/(m-2))
                 *(g_A+l_A*d_A/tau_A)
          > sum_{i in A}s_i+m*M.                    (2)

With no traps the tests are vacuous. Rewards and participant premiums
may have either sign; there are no additional inequalities on
coalitions not appearing in (1). In particular a protected player
or a nonnegative weighted forced-Quit floor is not an input.

**Uniform-payoff theorem.** For I=Fin4, if every own singleton s_i
is nonnegative and (1)-(2) hold, the original game has a uniform-
equilibrium payoff. There is one target u such that for every
epsilon>0 a behavioral profile and a horizon threshold work for
every larger finite horizon: its expected average payoff is within
epsilon of u, and every complete unilateral deviation pays at most
u_i+epsilon. The target is fixed before accuracy.

For Fin4, all traps must have size three or four. The two thresholds
are explicitly

    C_3=3*(d/tau)*(g+l*d/tau),
    C_4=4*sqrt(d/tau)*(g+l*d/tau).

Both sizes may occur in the same table; every trap must pass its own
test. These are finite reward conditions, not hypotheses about an
equilibrium, root selection, continuation annotation, or controller.
The proof is an existence argument through the actual full Nash
relation, not a strategy-class completeness assertion.

## 2. Exact roots and elementary estimates

For q in [0,1]^I let mu_q be its independent product coalition law,
c(q)=mu_q(empty), and a(q)=1-c(q). At a source v, the successor is

    w(v,q)=c(q)*v+sum_{S nonempty}mu_q(S)*r(S).       (3)

For player i, its two forced action values are

    Q_i(q)=sum_{T subset I minus {i}}mu_{-i}(T)*r_i(T union {i}),
    C_i(v,q)=mu_{-i}(empty)*v_i
                   +sum_{T nonempty}mu_{-i}(T)*r_i(T).

An exact root is a mixed Nash equilibrium of this finite one-stage
game, with continuation reward v after all Continue. Equivalently,
w_i=q_i*Q_i+(1-q_i)*C_i is at least Q_i and C_i for every i.
If q_i>0, support optimality gives w_i=Q_i>=C_i. If 0<q_i<1,
then Q_i=C_i=w_i. Finite-game Nash existence supplies an exact
root for every v; v need not be a strategically realized payoff.

For B>M and |v_i|<=B, formula (3) keeps w in the same box and gives

    norm(w-v)_infinity <= (M+B)*a(q).                (4)

Without any premium sign condition,

    Q_i(q)>=s_i-2M*a_{-i}(q)>=s_i-2M*a(q),           (5)

because the Quit reward is s_i on opponent nonabsorption and differs
from it by at most2M otherwise. A full exact-root unit-absorption
potential is a function H satisfying

    H(w(v,q))+a(q)<=H(v)                            (6)

for every source in the box and every exact root. Inactive players,
all simultaneous coalitions, and sure hazards remain in this relation.

## 3. A return lemma on a reward-sized source box

There are finitely many traps. The strict margins in (2) allow one
common B with M<B<M+2 such that

    C_A>sum_{i in A}s_i+|A|*B                        (7)

for every trap. If there are no traps any such B works.

We prove that EVERY absorbing exact root at EVERY source in this
box has a successor with some coordinate at most its own singleton.
Let A={i:q_i>0}, which is nonempty by absorption. If A is not a
trap, some k in A satisfies r_k(S)<=s_k for every S contained in A
and containing k. Averaging gives Q_k<=s_k, and support optimality
gives w_k=Q_k. It remains to rule out a trap support A with all
active Quit values Q_i>s_i.

For any support A, the exact aggregate-gap identity is

    sum_{i in A}(1-q_i)*(Q_i-C_i)
       =c(q)*sum_{i in A}(s_i-v_i)
          +sum_{empty != T proper-subset A}mu_q(T)*L_A(T). (8)

Indeed, multiplication by 1-q_i converts each opponent-coalition
probability into the corresponding full product probability. Its
empty term is c(q)*(s_i-v_i). Summing over i leaves exactly the
displayed coefficients for nonempty proper coalitions. This identity
does not divide by a hazard and remains valid on the whole cube.

If some but not all active hazards are sure, c(q)=0. Choose a
nonsure active player i. The coalition A minus {i} has positive
probability and strictly negative L coefficient by (1). Every other
coefficient is nonpositive, so the right side of (8) is negative.
The left side is nonnegative by supported Nash optimality, a
contradiction. If every active hazard is sure, (1) at A minus {i}
instead says r_i(A)<r_i(A minus {i}), a profitable withdrawal.
This separate case is necessary because both sides of (8) vanish
at the all-sure profile. Therefore all active hazards are interior.

Set z_i=q_i/(1-q_i)>0 on A and write

    U=sum_{i in A}z_i,
    E=sum_{i in A}product_{j in A minus {i}}z_j.

Dividing the positive quantity Q_i-s_i by its positive opponent
Continue probability and summing over i gives the exact polynomial

    0<sum_{empty != T proper-subset A}
           P_A(T)*product_{j in T}z_j <= -d_A*U+tau_A*E.

Thus

    d_A*U<tau_A*E.                                 (9)

The elementary symmetric-mean bound is

    E<=U^(m-1)/m^(m-2).

Here is a proof including boundary vectors. Maximize E at fixed
nonnegative sum U. The maximum is positive and hence has at least
m-1 positive coordinates. Holding all but coordinates a,b fixed,
E has the form ab*e_{m-3}(rest)+(a+b)*e_{m-2}(rest). Whenever
a,b are unequal at such a maximum, the first coefficient is positive,
and averaging a,b increases E strictly. Thus all coordinates at the
maximum equal U/m, giving the displayed bound. For m=3 the first
coefficient is e_0=1. From (9) we conclude

    U>m*(d_A/tau_A)^(1/(m-2)).                     (10)

All active players are indifferent. Divide (8) by the positive
empty-coalition probability and use (1), (9), and (10):

    sum_{i in A}(s_i-v_i)
      =sum_{empty != T proper-subset A}
                      [-L_A(T)]*product_{j in T}z_j
      >=g_A*U+l_A*E
      >(g_A+l_A*d_A/tau_A)*U
      >C_A.                                        (11)

But a boxed source has the left side at most sum_A s_i+m*B,
contradicting (7). This proves the asserted universal boxed return.
The crucial information is the cost imposed by the Nash equalities,
not a globally nonnegative forced-Quit floor.

## 4. Boxed return excludes a smooth full-root potential

This analytic step holds for any finite nonempty I and signed s.
Assume the return property just proved on [-B,B]^I. Suppose a C1
function H on a neighborhood of this box satisfies (6).

First record its singleton-face derivative inequality. If x_i>=s_i
for all i and x_j=s_j, then

    grad H(x) dot (x-r({j}))>=1.                    (12)

For a direct proof, let b_j=0. For i!=j set b_i=0 when x_i>s_i,
and b_i=max(0,r_i({i,j})-r_i({j})) when x_i=s_i. At small t>0,
use source v(t)=x+[t/(1-t)]b and a solo hazard t for player j.
Positive corrections occur only at singleton-binding coordinates,
strictly below B. Player j is indifferent, and for i!=j,

    C_i-Q_i=(1-t)*(x_i-s_i)
                    +t*(b_i+r_i({j})-r_i({i,j}))>=0

for all sufficiently small t. Thus this is an exact root, even when
some uncorrected coordinates are upper-box faces. Its successor is
x+t*(b+r({j})-x) and its absorption is t. Apply (6), divide by t,
and differentiate. The b terms cancel and give (12).

Minimize H on the compact nonempty set

    D={v in [-B,B]^I: some v_i<=s_i}.

If the minimum x had a strict singleton deficit, all Continue would
not be Nash. Any exact root would absorb and return to D, strictly
lowering H by (6). Hence x>=s and at least one coordinate binds.
Let J={i:x_i=s_i}. If J had a unique member j, every other
interior partial derivative would vanish and every upper-face partial
would be nonpositive. The j displacement in (12) is zero, and all
upper-face displacements B-r_i({j}) are positive. The left side of
(12) would be nonpositive, a contradiction. Therefore |J|>=2.
Increasing any binding coordinate retains another binding coordinate
and stays in D, so every binding partial derivative is nonnegative.

Choose k in J and a small epsilon>0. At v=x-epsilon*e_k every
exact root absorbs. Choose one, with absorption a>0 and successor
w in D. Nash, (4), and (5) yield

    s_k-2M*a<=Q_k<=w_k<=s_k-epsilon+(M+B)*a,
    epsilon<=(3M+B)*a.                              (13)

Minimality on D and drift give

    H(x-epsilon*e_k)-H(x)>=a>=epsilon/(3M+B).

After division by epsilon, the left side tends to -partial_k H(x),
which is nonpositive. The right side is strictly positive. This
contradiction excludes H. No root convergence, continuous selector,
protected coordinate, or absorption lower bound is required.

## 5. The original Fin4 semantic consumer

Nonnegative own singletons make every player normal, independently
of other reward signs. The existing four-player polynomial-obstruction
theorem says that, if some own singleton is positive and no uniform-
equilibrium payoff exists, a rational polynomial potential exists for
the full robust relation on the fixed box M+2. Restriction to exact
roots gives (6) on that box. Restriction again to the smaller B in
(7) preserves the SAME table and SAME polynomial. Section4 gives a
contradiction. If every own singleton is zero, all Never is already
an exact uniform equilibrium: a unilateral quitter receives zero.

This proves the theorem in Section1. The consumer's conclusion is the
actual fixed-target uniform finite-horizon notion with unrestricted
behavioral deviations. No strategic realization of the artificial
sources v, no bounded-controller completeness result, and no auxiliary
game's no-equilibrium hypothesis is used. The analytic theorem for
arbitrary finite I does not extend this semantic conclusion beyond
the Fin4 consumer.

## 6. A proper triple core with no nonnegative linear floor

Here is a complete table, with s=(1/10,1/10,1/10,1) and M=31/10.

| S | r(S) |
|---|---|
| 0 | (1/10,21/10,-9/10,2) |
| 1 | (-9/10,1/10,21/10,2) |
| 2 | (21/10,-9/10,1/10,0) |
| 3 | (-9/10,-9/10,-9/10,1) |
| 01 | (3/5,-9/10,11/10,2) |
| 02 | (-9/10,11/10,3/5,2) |
| 03 | (31/10,-9/10,-9/10,0) |
| 12 | (11/10,3/5,-9/10,2) |
| 13 | (-9/10,21/10,-9/10,0) |
| 23 | (-9/10,-9/10,21/10,0) |
| 012 | (1/5,1/5,1/5,2) |
| 013 | (21/10,21/10,-9/10,0) |
| 023 | (21/10,-9/10,21/10,0) |
| 123 | (-9/10,21/10,21/10,0) |
| 0123 | (21/10,21/10,21/10,0) |

The only trap is A=012. Each core pair has one positive premium
1/2 and one negative premium -1; its directed cycle makes the
triple a trap. Player3 has no positive participant premium, so no
larger set is a trap. For core singleton T, P_A(T)=-1/2 and
L_A(T)=-3/2. For core pair T, P_A(T)=1/10 and L_A(T)=-9/10.
Thus d=1/2,tau=1/10,g=3/2,l=9/10 give C_A=90>48/5.
For strict slack in all raw bounds take instead
d=2/5,tau=1/5,g=7/5,l=4/5, giving C_A=18>48/5.
All own singletons and trap-structure signs are strict, so a full
sixty-coordinate neighborhood is admitted by this raw criterion.

There is no nonzero nonnegative vector lambda with
sum_i lambda_i*(Q_i(q)-s_i)>=0 for EVERY product law q. Testing
the three sure-singleton core laws gives

    (1/2)*lambda_2-lambda_1-lambda_3>=0,
    (1/2)*lambda_0-lambda_2-lambda_3>=0,
    (1/2)*lambda_1-lambda_0-lambda_3>=0.

Their sum is -(lambda_0+lambda_1+lambda_2)/2-3*lambda_3>=0,
forcing lambda=0. The test laws need not be Nash. This exact failure
explains why their forced-Quit geometry does not contradict the
Nash-dependent theorem.

No pure quitting coalition is an equilibrium. The singletons have
the profitable joins exhibited below. In core pairs01,02,12 a
participant gains3 by withdrawal, and in core triple012 every
participant gains9/10. Player3 gains2 by withdrawal from every
nonsingleton coalition containing3 except pair23; at pair23 player0
gains3 by joining. All Never is defeated by a positive singleton.

### Why the source box cannot be omitted

On this SAME table take

    q=(9/10,9/10,9/10,0),
    v=(-863/10,-863/10,-863/10,1).

The exact endpoints are

    Q=(17/125,17/125,17/125,1/1000),
    C=w=(17/125,17/125,17/125,1981/1000).

The active players are indifferent and player3 strictly Continues.
This is an exact absorbing root with successor above every singleton.
Its source lies far outside the reward-sized box. Universal return
at arbitrary unbounded annotations is false, even on an admitted
table. A second rational test is q=(6/7,6/7,6/7,0) and
v=(-413/10,-413/10,-413/10,1), with active Q=C=11/98 and
outsider Q=1/343,C=673/343.

### Exact proper-child debt tests

For thirteen proper children use a sure singleton owner at date zero
and Never for all other child players. The pairs below are
(owner,omitted player):

    0:(0,2), 1:(1,0), 2:(2,1), 3:(3,0),
    01:(0,2), 02:(2,1), 03:(0,2), 12:(1,0),
    13:(1,0), 23:(2,1), 013:(0,2), 023:(2,1),
    123:(1,0).

Every child player other than the owner weakly prefers Continue;
the owner cannot exceed its nonnegative singleton by delaying alone.
These are exact Nash profiles against complete behavioral deviations,
not merely first-date checks. Their child debts and joint Never
probabilities are zero. Each omitted player gains3/2 by joining,
except child3, where the gain is4.

For child012 use repeated solo phases in order2,0,1, each with
aggregate hazard1/2. Relative to its singleton vector, the phase
values are (1,0,0), (0,1,0), (0,0,1). Refine each solo phase
into n equal hazards alpha_n=1-2^(-1/n). Continue is exact,
values retain singleton floors, and every Quit excess is at most
alpha_n/2. The common-error supersolution caps every behavioral
deviation by that same error, and geometric opponent survival
removes the remainder. Child regret therefore tends to zero and
joint Never is zero. Quiet player3 receives6/7, whereas quitting
at the first microdate pays1-alpha_n, a gain1/7-alpha_n.

Consequently, for EVERY proper nonempty child there is an omitted
player for whom no fixed finite nonnegative weighted-child-debt-plus-
Never bound can hold universally over child profiles. This excludes
that universal bound, not every possible selected quiet chronology.

## 7. A full four-player core with exact child witnesses

This distinct table has s=(1,0,0,0) and M=3.

| S | r(S) |
|---|---|
| 0 | (1,-1,-1,-1) |
| 1 | (2,0,2,-1) |
| 2 | (2,-1,0,2) |
| 3 | (0,2,-1,0) |
| 01 | (-1,-2,2,2) |
| 02 | (-1,2,-1/2,2) |
| 03 | (1/2,2,2,-2) |
| 12 | (3,-1/2,-2,2) |
| 13 | (3,-2,2,-1/2) |
| 23 | (3,2,-2,-2) |
| 012 | (-1,-2,-2,2) |
| 013 | (-1,-2,2,-2) |
| 023 | (-1,2,-2,-2) |
| 123 | (3,-2,-2,-2) |
| 0123 | (11/10,1/10,1/10,1/10) |

Every nonsingleton proper participant premium is negative and every
grand participant premium is1/10. Hence I is the only trap.
The four singleton P coefficients are -9/2; the L coefficients
in order0,1,2,3 are -3/2,-13/2,-13/2,-9/2. For every pair,
P=-4 and L=-8. For every triple, P=1/10 and L=-19/10.
Taking d=9/2,tau=1/10,g=3/2,l=19/10 gives

    C_I=348*sqrt(45)>13=sum_i s_i+4M.

All coefficient bounds can be made strict, for example by choosing
d=4,tau=1/5,g=1,l=3/2. This yields124*sqrt(20)>13.
The analytic criterion has a full raw neighborhood. For the strategic
theorem retain nonnegative singletons: the displayed point has three
zero singletons and hence is a boundary point of that restriction.
Raising those three singleton-own entries slightly preserves all
strict coefficient and trap margins and gives an interior admitted
point with all own singletons positive.

There is again no nonzero nonnegative forced-Quit floor weight.
Sum its putative inequalities over the four sure-singleton product
laws. Each player's three pair premiums consist of -1/2,-2,-2,
so the sum equals -(9/2)*sum_i lambda_i. Nonnegativity forces
every lambda_i to vanish.

The profitable singleton-join cycle is0 to2 to1 to3 to0, each
gain being1/2. These are the ONLY profitable joins against those
singletons. For every proper nonempty child an edge of this cycle
leaves the child. Its owner can quit surely while the other child
players choose Never, giving an exact behavioral Nash child profile
and an omitted-player gain1/2. Explicit (owner,omitted) choices are

    0:(0,2), 1:(1,3), 2:(2,1), 3:(3,0),
    01:(0,2), 02:(2,1), 03:(0,2), 12:(1,3),
    13:(3,0), 23:(2,1), 012:(1,3), 013:(0,2),
    023:(2,1), 123:(3,0).

Child regret and joint Never are exactly zero in all fourteen cases.
This gives the same universal quiet-debt exclusion as Section6,
without a limiting refinement. No pure equilibrium is hidden in the
table: the singletons have the join cycle; improving participants
for pairs01,02,03,12,13,23 are0,0,3,2,1,2, with gains
3,3,1,4,4,1; every triple participant gains4 by withdrawal;
every grand participant gains19/10. All Never is defeated by player0.

## 8. Bounded implementation-overlap checks

Both fixtures have an empty set of players with globally nonnegative
participant premiums, so protected-floor leaver criteria do not
apply. The all-sure law on each table's trap has every active Quit
premium1/10, excluding product-low and the older nonpositive
supportwise weighted-participant-premium condition. Sections6-7
exclude every nonzero nonnegative forced-Quit floor weight, not only
a selected normalization. Thus the weighted-floor raw criterion
cannot apply. The full-core fixture additionally lies outside any
criterion whose greatest premium core must have size at most three.

The full-core singleton matrix, with receiver rows and owner columns,
is

    Gamma=[[0,1,1,-1],[-1,0,-1,2],
           [-1,2,0,-1],[-1,-1,2,0]].               (14)

The triple-core fixture's matrix is the same matrix under the
permutation old0 to3, old1 to0, old2 to1, old3 to2. Its child123
in (14) has strictly positive inverse, determinant7, and sends the
all-one vector to itself. A positive homogeneous pivot forces child
coordinates equal to that pivot and has positive pivot residual.
At pivot zero the homogeneous child has only zero. Hence Gamma is
R0. At offset(1,-1,-1,-1) the unique complementarity root is
(0,1,1,1), with inactive residual2 and active determinant7, giving
degree+1. Thus this matrix does not pass the degree-not-one exit.

Only child123 has a nonnegative inverse, and its passive inverse
row is(-1/7,5/7,3/7). Negative inverse entries for children012,
013,023 are respectively -2,-2/3,-2/3. The full inverse has
entry -5/7 in row0,column2. No pair has both off-diagonal entries
positive. Principal03 is R0 but non-Q: its matrix is
[[0,-1],[-1,0]] and the offset(-1,-1) is infeasible.

A literal response quotient requires equal singleton block-row sums
for players in the same block. The following table lists, for each
nontrivial excluded partition of (14), two same-block rows, a block
of columns, and their unequal sums. The only other partitions are
the discrete partition and0|123.

| Partition | Rows | Column block | Sums |
|---|---|---|---|
| 01 / 2 / 3 | 0,1 | 01 | 1,-1 |
| 02 / 1 / 3 | 0,2 | 02 | 1,-1 |
| 03 / 1 / 2 | 0,3 | 1 | 1,-1 |
| 0 / 12 / 3 | 1,2 | 12 | -1,2 |
| 0 / 13 / 2 | 1,3 | 13 | 2,-1 |
| 0 / 1 / 23 | 2,3 | 1 | 2,-1 |
| 012 / 3 | 0,1 | 012 | 2,-2 |
| 013 / 2 | 0,1 | 013 | 0,1 |
| 023 / 1 | 0,2 | 023 | 0,-2 |
| 01 / 23 | 0,1 | 01 | 1,-1 |
| 02 / 13 | 0,2 | 02 | 1,-1 |
| 03 / 12 | 0,3 | 12 | 2,1 |
| 0123 | 0,1 | 0123 | 1,0 |

For the full-core table, at q=(t,0,0,0) the three child response
coordinates are t-2t^2,t-t^2/2,t-2t^2, breaking0|123. For the
triple-core table, at q=(0,0,0,t) its three core responses are
t+3t^2,t+2t^2,t+2t^2, breaking the permuted candidate3|012.
These expressions use the zero-discount residual
a_{-i}*Q_i minus the unnormalized nonempty passive reward.

These are exact comparisons with the named raw matrix, quotient,
premium and universal quiet-debt gates, not an exhaustive audit of
every stationary equilibrium or selected chronology. The full-core
table has negative participant premiums at every pair, so a producer
requiring a mutual-positive-premium pair cannot consume it through
that hypothesis. No uniform-equilibrium nonexistence or strategy-
class obstruction is inferred from these bounded exclusions.

## 9. Source declarations and Lean handoff

The semantic and analytic dependencies are these existing declarations:

- `exists_isZeroQuittingRootNash` in
  `UniformEquilibrium/Quitting/Root/NashExistence.lean` supplies finite
  exact-root existence at any source.
- `abs_quittingRootSuccessorPayoff_sub_tail_le_reward_add_source_mul_absorptionMass`
  in `UniformEquilibrium/Quitting/Root/BoundedSuccessorDisplacement.lean`
  supplies (4).
- `IsQuittingFullExactRootPotential.singletonFace_drift` in
  `UniformEquilibrium/Quitting/Projective/FullExactRootPotentialFaceDrift.lean`
  is (12), using the collision-adjusted probe proved directly above.
- `isQuittingNormalPlayer_of_singleton_nonneg` in
  `UniformEquilibrium/Quitting/Classification/AbnormalPlayers.lean`
  supplies normality without participant-premium sign assumptions.
- `quittingGame_not_exists_uniformEquilibriumPayoff_iff_noSureRoot_and_rationalPotential`
  in `UniformEquilibrium/Quitting/Projective/PolynomialForwardCertificateCharacterization.lean`
  supplies the Fin4 obstruction with the actual reward bound M.
- `isQuittingFullExactRootPotential_of_robustPotential` and
  `IsQuittingFullExactRootPotential.mono_box` in
  `UniformEquilibrium/Quitting/Projective/ExactRootPotentialRestriction.lean`
  restrict the same polynomial first to exact roots, then to B.

The source comparisons inspect `SupportwiseQuittingPremiumBalanceAt.lean`
and `SupportwiseQuittingPremium.lean` under
`UniformEquilibrium/Quitting/Classification/`, the product-low
implication in `SupportwiseQuittingPremiumProductLow.lean`, and
`Existence/SupportwisePremiumUniformPayoff.lean` in that subtree.
Supportwise balance implies product-low; it is not a weaker raw
hypothesis. The inverse consumer is
`PassiveRowInverseCriterion.exists_uniformEquilibriumPayoff_of_raw_nonnegativeInverse_triple`
in `UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/RawPassiveRowInverseCriterion.lean`.
The degree comparison uses
`finFour_singleton_r0Degree_eq_one_of_no_uniformPayoff` in
`UniformEquilibrium/Diagnostics/Quitting/FinFourSingletonDegreeCriterion.lean`
and `exists_uniformEquilibriumPayoff_of_r0Degree_ne_one` in
`UniformEquilibrium/Quitting/Classification/LCP/SingletonDegreeCriterion.lean`.
The block-row necessary condition is
`quittingSingletonBlockRowSum_eq_of_responseInvariant` in
`UniformEquilibrium/Quitting/Stationary/ResponseInvariantQuotient.lean`.
The quiet bound compared in Sections6-7 is
`withdrawalFutureJoin_quietLift_outsideDebt_le_add_neverExcess` in
`UniformEquilibrium/Quitting/Classification/QuietExtension/WithdrawalFutureJoinDebt.lean`.
The diffuse child witness uses the exact-Continue common-error
consumer in `UniformEquilibrium/Quitting/Paths/InfinitePathSupersolution.lean`.

The intended formalization is one raw boxed-charge predicate whose
fields are only trap cardinalities, positive real constants, and
(1)-(2). The main producer proves universal low-successor return
on some B with M<B<M+2. The same-D minimum lemma excludes a C1
full-root potential; the named restriction and polynomial declarations
then give the Fin4 uniform-payoff theorem. For Fin4 the threshold
can be formalized by its two explicit cardinality cases, avoiding
general real powers. No potential, root selection, equilibrium,
controller, protected floor, or strategic target belongs among the
raw predicate's supplied fields. This packet is ordinary mathematics;
it asserts no new Lean-check or integration status.
