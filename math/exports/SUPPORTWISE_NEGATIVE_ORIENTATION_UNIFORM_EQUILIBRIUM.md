# Supportwise negative orientation on positive Quit regions

Ordinary mathematics, not a new Lean verification. This extends supportwise
low-or-charge existence by admitting larger supports on which every active
Quit payoff can be positive.
The additional condition is a polynomial test on the reward table. The exact
game below passes it, fails the Low/Charge-only criterion, and escapes
the earlier raw admissions audited below. Fin4 remains open.

Conditional triple orientation is an existing method. The new coverage comes
from combining it with independent Low/Charge support tests without a
mandatory nonnegative payoff ledger. The separating table
defeats every ledger choice, not just one selected weight.

## 1. Raw theorem and semantics

There are four players I={0,1,2,3}, independent private Continue/Quit actions,
zero live and Never rewards, and finite reward vectors r(S) at the first
nonempty quitting coalition. A unilateral deviation replaces one complete
behavioral strategy. Set s_i=r_i({i})>=0, Z_i(S)=r_i(S)-s_i, and
M=max_(i,S nonempty)|r_i(S)|. A uniform-equilibrium payoff is one fixed target
before accuracy, with one profile and threshold for each accuracy valid at
every larger horizon against every complete unilateral replacement.

For a support A and positive odds z in R^A, put z_T=product_(j in T)z_j and

    Phi_i^A(z)=sum_(empty!=T subset A-i) z_T [r_i(T+i)-r_i(T)],
    R_i^A(z)=sum_(T subset A-i) z_T Z_i(T+i), i in A.       (1)

For every pair ij with Z_i(ij)>0 and Z_j(ij)>0, require

    d_ij d_ji>=0, where d_ij=r_i(ij)-r_i(j).              (2)

For EACH support A of size m=3 or4, assign one of three raw tests:

**Low.** Every independent root with support exactly A has some active
forced-Quit payoff Q_i<=s_i. Equivalently, no z>0 makes every R_i^A(z)>0;
strict failure at a sure boundary persists after an inward perturbation.

**Charge.** For every nonempty proper T subset A define

    P_A(T)=sum_(i in A\T)[r_i(T+i)-s_i],
    L_A(T)=sum_(i in A\T)[r_i(T+i)-r_i(T)].

There are D,tau,G,Lstar>0 satisfying

    |T|=1:       P_A(T)<=-D, L_A(T)<=-G;
    2<=|T|<=m-2: P_A(T)<=0,  L_A(T)<=0;
    |T|=m-1:     P_A(T)<=tau,L_A(T)<=-Lstar;
    C_A=m(D/tau)^(1/(m-2))*(G+Lstar D/tau)
                                       >sum_(i in A)s_i+mM.  (3)

Empty cardinality ranges impose nothing.

**Orientation.** The following finite-polynomial implication holds:

    z>0 and R_i^A(z)>0 for every i in A
                 IMPLIES (-1)^m det D Phi^A(z)<0.        (4)

This condition is restricted to positive Quit premiums; the determinant may
have the opposite sign elsewhere. Section 3 gives finite coefficient
certificates. No strategic root, continuation, index value, selector, clock,
punishment or equilibrium is supplied.

For weak products in (2), impose this assignment restriction: every
mutual-positive pair with zero joining product is contained in NO support
assigned Orientation. Such supports may instead pass Low or Charge.
There is no assignment restriction when all products in (2) are positive.

**Theorem.** These tests imply a uniform-equilibrium payoff for r. They also
imply A_Z=0, where A_Z is the infimum of total full behavioral deviation debt
over absorbing profiles for the native table Z. Consequently every
nonnegative recipient-row raise of Z has a uniform-equilibrium payoff.

Low is a vacuous special case of (4), but its separate label preserves the
weak-pair closure of the Low/Charge theorem. All that previous coverage is
retained by assigning only Low and Charge.

## 2. Producer and semantic consumer

For q in [0,1]^4, let p_q be its product coalition law and
H_i=product_(j!=i)(1-q_j). At an arbitrary annotation v define

    Q_i=sum_(T subset I-i) p_(q,-i)(T) r_i(T+i),
    C_i=P_i+H_i v_i,
    P_i=sum_(empty!=T subset I-i) p_(q,-i)(T) r_i(T),
    w_i=q_i Q_i+(1-q_i)C_i.

Full Nash means q_i>0 implies Q_i>=C_i and q_i<1 implies C_i>=Q_i.
Finite mixed Nash existence applies. An annotation is not an assumed actual
continuation payoff. Call a root bad if w_i>s_i for all four players.

First split off any full Nash root at any annotation with at least two sure
quitters. Every player then faces a sure opponent, so all comparisons are
independent of the annotation. Playing this root at the first date is an
absorbing equilibrium against every complete deviation. Hence assume no
such root exists.

Initially suppose the pair products in (2) are strict. Choose a common
M<B<M+2 such that C_A>sum_A s_i+mB on every charged support. Low excludes
bad roots directly. For Charge, the identity at a bad Nash root is

    0=c sum_A(s_i-v_i)
           +sum_(empty!=T proper subset A)p_q(T)L_A(T),
    c=product_i(1-q_i).                                  (5)

One sure owner makes the right side strictly negative: a coalition missing
a nonsure active owner has positive probability and negative penultimate L.
Two sure owners were already split off. Thus the root is proper. With
U=sum_A z_i and E=sum_i product_(j in A-i)z_j, positivity of the Quit
premiums and (3) give DU<tau E. The bound E<=U^(m-1)/m^(m-2), followed by
(5) divided by c, gives

    sum_A(s_i-v_i)>C_A,

contradicting |v_i|<=B. Hence Low and Charge supports have no bad roots in
the box. Singleton roots are not bad either.

### One-sure oriented roots have a zero column

Suppose a bad root has oriented support A and exactly one sure owner i.
Every other active owner j is proper. Its indifference gives

    0=Q_j-C_j
      =[product_(k in A\{i,j})(1-q_k)] partial_i Phi_j^A(z). (6)

The partial derivative does not depend on z_i. Also partial_i Phi_i=0.
Thus the entire i-column of D Phi is zero for EVERY artificial positive
choice of z_i. As z_i tends to infinity, the corresponding proper hazards
converge to the original bad root. All active Quit premiums remain positive
for large finite z_i, contradicting (4). This covers both triples and the
four-player support without an extra boundary hypothesis.

A bad pair has two positive participant premiums. One sure owner and one
proper owner would force the latter's nonzero joining gap to vanish, so it
too is proper. Its odds map is Phi_i=d_ij z_j, Phi_j=d_ji z_i and its
determinant is -d_ij d_ji<0.

### The full ambient index produces the selected return

For a proper support A and quiet owner k, active indifference and a quiet
tie impose

    v_i=s_i+Phi_i^A(z), i in A,
    v_k=s_k+sum_(empty!=T subset A)z_T[r_k(T+k)-r_k(T)].    (7)

Including the other free annotation coordinates, this is a polynomial
image of R^3 in R^4. It has measure zero: on each bounded cube a Lipschitz
cover by O(h^-3) cubes has image volume O(h). Countably many cubes and
finitely many supports retain measure zero. Thus a dense set of boxed
annotations has no quiet tie at any proper root. Thus no genericity
assumption on the reward table is required.

Fix such an annotation below at least one singleton. All Continue is not
Nash. Suppose every root is bad. The preceding steps leave only proper
pairs and oriented supports. Extend the endpoint polynomials to real q and
clip coordinatewise:

    F_v(q)_i=min(1,max(0,q_i+Q_i(q)-C_i(v,q))).           (8)

Its fixed points are exactly the full Nash roots. At a root the quiet rows
are locally constant zero and active rows are unclipped. Active indifference
gives

    D_q(Q-C)=diag(H_i) D_z Phi^A diag((1+z_i)^2).         (9)

The full determinant of Id-D F_v therefore has sign
(-1)^m det D Phi^A<0. Quiet coordinates contribute an identity block;
their cross effects are retained in the off-diagonal block. Every root is
isolated. The root set is compact, hence finite, and every local index is -1.
On (-1,2)^4 homotopy of F_v to the constant half-vector has no boundary
fixed point, since its image stays in [0,1]^4. Total degree is +1, a
contradiction. Some exact root therefore has a successor coordinate <=s_i.

Approximate any other boxed below-singleton annotation by these generic
annotations. Compactness and the closed full Nash inequalities give the
same selected return. The limiting root cannot be All Continue at a strict
deficit. The existing declaration
`exists_uniformEquilibriumPayoff_of_selectedSingletonSublevelReturn_of_reward_bound`
in `UniformEquilibrium/Quitting/Classification/Existence/SelectedSingletonSublevelReturnUniformPayoff.lean`
consumes precisely this property, s_i>=0 and
M<B<M+2<=quittingRewardBound(r)+2. It produces the behavioral profiles and
one fixed uniform target. No continuous selector is needed.

### Weak products and absorbing debt

Strictify zero pair products by perturbing only passive singleton entries:
a zero gap takes its nonzero partner's sign, or both zeros become positive.
The assignment restriction ensures no assigned Phi or R changes. Low
participant data stay fixed; the finitely many strict charge margins
survive. The reward-closure declaration
`exists_uniformEquilibriumPayoff_of_arbitrarily_close_reward_tables` in
`UniformEquilibrium/Quitting/Terminal/TerminalExploitabilityRewardRobustness.lean`
therefore supplies the weak case. Without the assignment restriction this
perturbation need not preserve the orientation condition; no unrestricted
weak-boundary claim is made.

For the native conclusion, raise every recipient's rewards on every
nonempty coalition by one sufficiently small epsilon>0. All tests persist:
premiums and joining differences are unchanged and the charge threshold
right sides rise by at most 2m epsilon. Put c_i=s_i+epsilon>0 and R=Z+c.
For an actual profile let U_i be payoff, B_i the supremum over all complete
deviations, D=sum_i(B_i-U_i), and nu the product of original Never masses.
Native own-zero rewards make finite-deadline payoffs converge to Never;
hence B_i^R=B_i^Z+c_i and

    D_R=D_Z+nu sum_i c_i.                               (10)

The declaration
`quittingTerminalDebtSumInf_pos_iff_not_exists_uniformEquilibriumPayoff` in
`UniformEquilibrium/Quitting/Terminal/TerminalDebtSumInf.lean`
gives actual profiles with D_R tending to zero. Thus D_Z and nu tend to zero.
Move the smallest marginal Never mass, at most nu^(1/4), to a finite date.
The resulting absorbing profile has total debt at most
D_Z+14M_Z nu^(1/4), with M_Z=max(1,max|Z|), so A_Z=0. Nonnegative row raises
preserve debt on these absorbing approximants. The fixed-target consumer is
`quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors` in
`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`.
All deadline and Never comparisons cover every behavioral deviation, since
before absorption the only live public history is repeated all Continue.

## 3. Finite orientation certificates

For A={a,b,c}, set B_i=r_i(abc)-r_i(A-i). The determinant is multiaffine:

    det D Phi=(d_ab+B_a z_c)(d_bc+B_b z_a)(d_ca+B_c z_b)
             +(d_ac+B_a z_b)(d_cb+B_c z_a)(d_ba+B_b z_c). (11)

Its unconditional positivity on z>0 is equivalent to all eight coefficients
being nonnegative with at least one positive. Necessity follows by isolating
a negative coefficient indexed by S: set z_j=t on S and z_j=t^-4 outside
S. Its monomial uniquely dominates as t tends to infinity.

For m=4 each derivative entry uses only the two variables outside its row
and column. Each variable is absent from two distinct rows of every
determinant term. Thus every variable has degree at most two, giving at most
81 coefficients. All coefficients nonpositive with one negative suffice for
(4) unconditionally; necessity is not asserted in this case.

The conditional criterion is stronger. Put P=(-1)^(m+1)det D Phi. It is
enough to exhibit the exact polynomial identity

    W P=K+sum_(i in A) A_i R_i,                         (12)

where W is nonzero with nonnegative coefficients, and K,A_i all have
nonnegative coefficients with at least one nonzero. On z>0 and R_i>0,
both W and the right side are strictly positive. Bounded-degree searches
for this certificate reduce to finite coefficient equalities and inequalities.
The theorem does not assert completeness of such searches.

## 4. A whole-game separation example

Here is the complete ORIGINAL table, with all own singletons one.

| S | r_0 | r_1 | r_2 | r_3 |
| --- | --- | --- | --- | --- |
| 0 | 1 | 0 | 4 | 0 |
| 1 | 0 | 1 | 0 | 4 |
| 2 | 4 | 0 | 1 | 0 |
| 3 | 0 | 4 | 0 | 1 |
| 01 | -1 | 1 | 249/100 | 149/100 |
| 02 | 3 | 199/100 | 2 | 199/100 |
| 03 | 2 | 149/100 | 149/100 | -1 |
| 12 | 149/100 | -3 | 1 | 449/100 |
| 13 | 199/100 | 0 | 199/100 | 0 |
| 23 | 249/100 | 149/100 | -1 | 1 |
| 012 | -1 | 3 | -1 | 10 |
| 013 | -1 | 5/4 | 10 | -1 |
| 023 | -1 | 10 | -1 | -1 |
| 123 | 10 | -1 | -1 | 2 |
| 0123 | -1 | -1 | -1 | 101/100 |

The only mutual-positive pair is 02, with gaps (-1,-2). Supports 013 and
123 pass Low with weights (e1+e3)/2; 023 passes with e3. These weights make
every weighted participant coefficient on the respective support nonpositive.

For 012 put (x,y,z)=(z0,z1,z2). Then

    Phi=(-y-z-(249/100)yz,
          x-3z+(101/100)xz,
         -2x+y-(349/100)xy),
    R=(-2y+2z-2yz, 2z(x-2), x(1-2y)).                  (13)

Writing P=det D Phi gives the exact factorization

    P=(x-2)A(y,z)+K(y,z),
    A=551/100+(2443/200)y+(85547/10000)z
                                      +(8777001/500000)yz,
    K=201/50+(1147/100)y+(5797/5000)z
                                      +(1630701/250000)yz. (14)

Every displayed coefficient is positive. R1>0 forces x>2, so P>0.
Equivalently 2zP=R1 A+2zK certifies (12). Its constant coefficient is -7,
so the unconditional orientation test fails. At odds (3,1/10,1),
R=(8/5,2,12/5)>0, so Low fails as well. Charge is impossible on this triple:
P_012({0})=1>0. Under arbitrary positive recipient scalings this coefficient
is lambda2>0. Thus the supportwise criterion allowing only Low/Charge fails over
all its assignments and positive recipient scalings, even though (4) succeeds.

Full support passes Charge. Its singleton P values are (-1,-3,-2,-2) and
singleton L values (-2,-4,-3,-3). All six middle P are nonpositive, and
all middle L are at most -99/50. Its penultimate P values are 1/100 or -2,
and penultimate L are -899/100 or -11. With M=10, take

    D=1, G=2, tau=1/100, Lstar=899/100.

The threshold is 36040>sum_i s_i+4M=44. Thus this table has UE by the theorem.
Its premium core is all four players: pair02 witnesses owners0,2, triple013
witnesses owner1, and triple123 witnesses owner3.

### Stationary profiles and all stationary limits are excluded

All passive original rewards are nonnegative, so Never guarantees at least
zero. If j is sure, its opposite owner j+2 has the following four joining
gaps, at the four pure choices of the remaining two hazards:

| j | Opposite owner's four gaps |
| --- | --- |
| 0 | (-2,-349/100,-249/100,-11) |
| 1 | (-4,-249/100,-249/100,-899/100) |
| 2 | (-1,-249/100,-349/100,-11) |
| 3 | (-4,-6/25,-249/100,-11) |

Their order is immaterial; every convex combination is negative. The opposite
owner Continues. The predecessor j-1 then has two negative gaps, respectively
(-1,-249/100), (-1,-249/100), (-3,-249/100), and (-1,-249/100), so Continues.
The successor j+1 now has positive gap1,1,1,2 and Quits surely. Owner j's
withdrawal gain is1,3,1,1. Thus no stationary profile has a sure owner,
including every mixture of the others.

All Never fails at own reward one. A sole active owner fails at its cyclic
successor. On adjacent pair supports01,12,23,30, the successor has Never
payoff zero and Quit payoff1,1,1,1+q3, respectively. On02, owner0 gets four
from Never and at most three from Quit; on13, owner1 gets four from Never
and at most one from Quit. Every pair support fails.

At a proper stationary active owner, Q_i=P_i/(1-H_i)>=P_i. On013 put
(a,b,c)=(q0,q1,q3). Owner3 gives

    Q3-P3=1-2a-5b+(351/100)ab>=0.

Affine endpoint checks force a<=1/2,b<=1/5. Hence Q0>=3/5 while
Never0<=2b<=2/5, impossible. On123 put (a,b,c)=(q2,q3,q1). Owner1 gives

    Q1-P1=1-4a-5b+(551/100)ab>=0.

Endpoint checks force a<=1/4,b<=1/5, so Q2>=3/5 while Never2<=2b<=2/5.

On023 put (a,b,c)=(q0,q2,q3). The relevant endpoints are

    Q3=1-2a,       P3=(199/100)ab,
    Q2=1+a-2c-ac,  P2=4a-(251/100)ac,
    Q0=1+2b+c-5bc, P0=4b-(151/100)bc.

Owner3's indifference gives
b=a(1-2a)/[(499/100)a-2a^2-1], with positive numerator and denominator.
Its upper bound b<=1 implies a>=100/399>1/4. The comparison Q2>=P2
gives a<=1/3 and c<1/6. The displayed b function decreases: its derivative
numerator is -(399/50)a^2+4a-1<0. Thus b>=100/397>1/4 and Q0<=1+2b.
The numerator of Never0-(1+2b) is

    b(3-2b)-c[1+(251/100)b-2b^2]>=5/8-2/6=7/24>0,

another contradiction. For012,
put (a,b,c)=(q0,q1,q2). Its original endpoints are

    Q0=1-2b+2c-2bc,       P0=4c-(251/100)bc,
    Q1=1-4c+6ac,          P1=(199/100)ac.

Stationary indifference gives Q0=P0/(b+c-bc)>=P0. The inequality
1-2b-2c+(51/100)bc>=0 implies b,c<1/2 by affine endpoint bounds.
The stationary residual for owner0 is

    0=b(1-2b)-c[3-(151/100)b-2c(1-b)^2].                (15)

The bracket exceeds 3-151/200-1>1 and b(1-2b)<=1/8, so c<1/8.
But Q1>1/2, while its Never value
P1/(a+c-ac)<(199/100)/8<1/4, a contradiction.

For full proper support write D=product_i(1+z_i),
W_k=sum_(|S|=k)z_S, H(S)=sum_i Z_i(S), and
J(S)=sum_(i outside S)[Z_i(S+i)-Z_i(S)]. Stationary indifference and
the absorbing payoff identity require

    sum_(S nonempty)z_S H(S)
                =(D-1)sum_(S nonempty proper)z_S J(S).   (16)

Here all singleton/triple H are nonnegative, all pair H>=-1/50,
H(I)=-599/100, and every proper J<=-99/50. The left side is at least
-W2/50-599W4/100. Since (D-1)W1>=2W2+4W4, the right side is at most
-99W2/25-198W4/25, strictly smaller. No full proper stationary profile exists.

Finally the singleton comparison matrix is unchanged:

    Gamma=[0,-1,3,-1; -1,0,-1,3; 3,-1,0,-1; -1,3,-1,0],
    Gamma^-1=[2,3,7,3; 3,2,3,7; 7,3,2,3; 3,7,3,2]/15.

It is R0: a complementary p>=0 with Gamma p>=0 and p_i(Gamma p)_i=0
must be zero. Indeed every principal block of size at least two is
invertible: pair determinants are -1 or -9, triple determinants6, and full
determinant45. A singleton support fails at an external negative entry.

Suppose stationary profiles had debt tending to zero. A nonzero limiting
hazard would give an exact stationary equilibrium by continuous absorbing
payoff and endpoint formulas; if only one owner remained active, its positive
own reward makes Never unprofitable. If hazards tend to zero, normalize by
their sum and pass to a simplex limit p. Absorbing payoffs tend to1+Gamma p.
Immediate Quit tends to1, giving Gamma p>=0. For p_i<1, Never against the
opponents tends to1+(Gamma p)_i/(1-p_i); the vanishing-debt comparison gives
p_i(Gamma p)_i<=0. For p_i=1 that product is zero directly. This contradicts
R0. All Never itself has positive debt. Reward continuity therefore preserves
a positive stationary debt gap in a neighborhood, excluding approximate
stationary and reward-closure stationary producers too.

### Complete selections in the other earlier raw admissions

The following comparisons define the raw necessary tests they exclude and
range over their complete weights, roles and other choices.

- A payoff ledger requires H_w(S)=sum_i w_i Z_i(S)>=0 for all nonempty
  proper S and a nonzero w>=0. The exact identity
  93Z(01)+53Z(03)+17Z(12)+83Z(23)=(-1,-34/25,-73/50,-11/10)
  makes every such weight impossible. A finite nonempty family cannot help,
  independently of any marked set, physical floor or orientation choice.
  For support-filtered ledgers the singleton conditions give w Gamma>=0;
  invertibility and Gamma^-1>0 then force w>0, so every proper support is
  safe and must satisfy the same impossible inequalities. A strictly positive
  coordinate matrix P yields the positive H weight1^T P and also fails.
  Positive recipient scalings can be absorbed into w in all these arguments.
- A nonnegative inserted-premium floor needs
  sum_(i outside S)w_i Z_i(S+i)>=0 for every nonempty proper S. Singleton
  sets1 and3 imply -2w0-w3>=0 and w0-w1-2w2>=0. Their sum is strictly
  negative for every nonzero w>=0. Every weight fails. Global product lowness
  and support-local nonpositive Quit averages fail on positive pair02.
  Each owner has both a positive and a negative participant premium, so
  neither a globally nonpositive omitted owner nor a globally nonnegative
  protected owner exists, under any role assignment.
- A premium trap is a nonempty A for which every i in A has a positive
  participant premium on some coalition contained in A. The full-core
  witnesses above exclude every literal two-player or mixed-triple core
  selection. In particular the checked declarations
  `exists_uniformEquilibriumPayoff_of_mixedSignTriple_core` and
  `exists_uniformEquilibriumPayoff_of_weakMixedSignTriple_core` in
  `UniformEquilibrium/Quitting/Classification/Existence/MixedSignTripleCoreUniformPayoff.lean`
  and `UniformEquilibrium/Quitting/Classification/Existence/MixedSignTripleCoreRewardClosure.lean`
  require that literal triple core. Weak joining perturbations preserve
  participant premiums. The Low/Charge-only criterion fails on012 as proved
  above; the full-support charge succeeds and is not an obstruction.
- The sure cascade also excludes every persistent-base/free-set/punishment
  selection: a one-owner base forces its successor sure and leaves a strict
  withdrawal gain; a larger sure base would itself give full Nash, already
  impossible. This is stronger than excluding stationary repetition alone.
  The exact interfaces are `quittingSingletonBaseOwnerFloorExcess` and
  `quittingPersistentLargeBaseExcess_nonpos_iff` in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PersistentBaseConcreteGap.lean`,
  and `exists_uniformPayoff_of_persistentBase_inducedNash_signs` in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PersistentBaseNashSemanticAdapter.lean`.
- For any nonempty proper child S choose i in S with i+1 outside S, possible
  because successor is a four-cycle. Sole-i stopping is exact child Nash:
  all retained other owners have negative joining gaps. Its omitted successor
  has gain1,1,1,2 respectively. Thus every proposed universal bound by a
  nonnegative weighted child debt plus child Never fails at zero debt and
  zero Never. This checks all14 children and all clocks, not a supplied
  specially selected safe child. The relevant exact bounds are
  `quietLift_outsideBehaviorDeviationDebt_le_weighted_childDebt_add_neverExcess`
  in `UniformEquilibrium/Quitting/Classification/QuietExtension/CappedClockPositiveSingletonQuietExtension.lean`
  and `withdrawalFutureJoin_quietLift_outsideDebt_le_add_neverExcess` in
  `UniformEquilibrium/Quitting/Classification/QuietExtension/WithdrawalFutureJoinDebt.lean`.
- The three pair partitions have directed joining gaps
  01|23: (-1,1),(-1,1); 02|13: (-1,-2),(-4,-4);
  03|12: (2,-1),(-3,1). Thus no partition meets four nonnegative joining
  tests, under any positive row scaling. Since Gamma^-1>0, a signed-column
  test Gamma^-1 diag(sigma)>0 forces every sigma positive and leaves this
  obstruction. Every passive native pair reward is positive, so all choices
  requiring even one scheduled nonpositive passive pair reward fail too.
- There is only one mutual-positive participant pair, and every other pair
  has a strictly negative endpoint. Thus no perfect matching has all four
  participant premiums nonnegative. All four favorite-pair joining gains
  on02|13 are negative, excluding every above-singleton favorite choice.
  For a template with common favorite singleton a, common crossing -b and
  common scheduled premium, the singleton matrix forces02|13 and equal
  recipient normalizations; its participant premiums (2,1,-1,-1) cannot
  become one common value. Positive cross premium Z0(03)=1 defeats every
  all-cross nonpositive test; positive pair02 defeats every all-favorite
  nonpositive test. These are separate complete raw tests, not a claim about
  arbitrary periods or independently chosen phase rewards.
- Reciprocal singleton signs are symmetric, excluding every cyclic test
  requiring Gamma_ij<0<Gamma_ji. Every principal triple block has determinant6
  and negative inverse diagonal entries, so no nonnegative-inverse triple
  extension is available. Every reciprocal joining pair has a negative
  entry, so no triple has all six joining gains positive.
- A broader three-owner joint-return selector requires, in its labeled roles,
  Gamma03>0, Gamma23<0, Z2(23)>0 and J0+J1 b=0 with0<b<1, where
  J0=e a3+d v, J1=e(t3-a3)-(omega+e)v,
  e=Gamma32,d=-Gamma30,w=Z3(02),v=Z3(23),a3=Z3(03),t3=Z3(023),
  and omega=w+d-e. The only positive crossing participant is actual0 on03.
  Hence roles2,3 are actual0,3, and the singleton signs force roles0,1 to
  actual1,2. In this unique assignment J0=7 and J1=-201/50, forcing
  b=350/201>1. Positive row scaling multiplies both J0,J1 by the same
  positive factor, so every scale fails before further parameters are chosen.
- Every marked ordered nonpositive-anchor choice is disjoint from02, hence
  lies in {1,3}; either marked row has positive passive reward99/100 on02,
  contradicting its required nonpositive passive reward on complementary
  coalitions. This checks all nonempty marked sets, ordered blocks and
  strictly positive block weights: the first block meeting02 already fails.
  The strict toggle cycle0->01->1->12->2->23->3->03->0 has gains
  (1,1,1,3,1,1,2,1), excluding every ordinal toggle potential.

These statements concern the exact existing raw producers just identified.
They do not assert the absence of every imaginable nonstationary strategy,
an uncomputed local neighborhood, or an equilibrium certificate supplied as
an additional strategic hypothesis.

## 5. Formalization boundary and remaining cases

The new producer combines the one-sure zero-column exclusion and the
orientation gate with independent Low/Charge support tests. The endpoint and degree machinery
is already available: `pairNash_hasFDerivAt_and_negative_det_fullClippedDisplacement`
in `UniformEquilibrium/Quitting/Root/PairFullClippedJacobian.lean`,
`ambientDegree_homotopy` and `ambientDegree_affineRootField_eq_sign_det` in
`MathUE/Topology/AmbientDegreeHomotopyNormalization.lean`,
`ambientDegree_excision` in `MathUE/Topology/AmbientDegreeProperties.lean`, and
`ambientDegree_of_selfMap_eq_one` in
`MathUE/Topology/AmbientDegreeSelfMapNormalization.lean`.
The exact charge bound is
`QuittingTrapChargeCoefficients.threshold_lt_singletonSourceCharge` in
`UniformEquilibrium/Quitting/Classification/BoxedQuittingNashChargeOdds.lean`.
No new Lean build or formalization is asserted.

For strict same-sign mutual-positive pairs, a counterexample with
nonnegative own singletons must now contain a triple or full support failing
ALL THREE tests: Low, Charge, and positive-Quit orientation. Opposed positive
pairs and the explicitly uncovered weak orientation boundaries remain
additional cases. Failure of the tests is only a necessary obstruction to
this theorem; it does not produce a counterexample or close arbitrary Fin4.
