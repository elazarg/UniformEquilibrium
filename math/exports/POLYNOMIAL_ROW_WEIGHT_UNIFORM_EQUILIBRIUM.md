# Positive polynomial row weights enlarge ordered-pair equilibrium production

Ordinary mathematics; no new Lean theorem is claimed. Fin4 remains open.
This packet gives a finite raw reward-class producer containing the previous
one-pair and restricted two-pair odds-order classes, including their weak
and singular boundaries. A complete one-parameter family separates it from
ALL constant-row odds-order choices, the full sure-first punishment
mechanism, and every positively row-scaled response quotient. An explicit
strict perturbation gives a full sixty-dimensional open enlargement.

## 1. Raw data and conclusion

Players are I=Z/4Z. A native table Z has zero live, literal-Never, empty,
and own-singleton rewards. Put Gamma_ij=Z_i({j}) for i!=j, Gamma_ii=0.
Assume strictly positive favorites Gamma_i,i+2 and strictly negative other
off-diagonal entries. All other absorbing rewards are arbitrary real
numbers subject to the finite tests below. Set J_ja=Z_j({j,a}).

Actual absorbing rewards are r_i(C)=lambda_i Z_i(C)+s_i for nonempty C,
where lambda_i>0 and s_i are arbitrary real numbers. Live and Never remain
zero. For every owner a with s_a<0 require at least one of

    min_(0<=t<=1) max_(j!=a) [t J_ja-Gamma_ja] > 0;       (1a)
    J_ja>=Gamma_ja for some nonfavorite j!=a.             (1b)

One may also impose these guards on owners with s_a>=0, but this is
unnecessary. The minimum in (1a) is computed at 0,1 and the at most three
intersections of the three affine lines in [0,1]. Thus this is a finite
raw test, not an equilibrium existence premise.

Choose positive odds weights rho_j. Choose FOUR multiaffine polynomials
m_i(u0,u1,u2,u3), each with all sixteen vertex values STRICTLY positive.
Equivalently write

    m_i(u)=SUM_(a in {0,1}^4) mu_i,a PRODUCT_j
                   u_j^a_j (1-u_j)^(1-a_j), mu_i,a>0.    (2)

All sixty-four coefficients are finite chosen real parameters. In
particular, m_i is bounded above and bounded away from zero on the cube.
Constant choices m_i=c_i>0 recover every previous constant row weight.

Choose ONE favorite pair with an orientation, or BOTH favorite pairs with
one orientation each. Require the 80 or 280 finite Bernstein inequalities
in Section 2. No matrix determinant condition is required in the theorem.

**Theorem.** Every actual reward table satisfying these raw tests has one
fixed uniform-equilibrium payoff against every unilateral behavioral
replacement. If det Gamma!=0 and every negative-own owner uses the strict
alternative (1a), the proof produces an exact stationary terminal Nash
profile, which witnesses that same fixed uniform payoff at every accuracy.
If every column uses (1a), at least two hazards are positive. At weak or
singular boundaries the assertion is terminal approximate Nash at all
positive errors and one fixed UE payoff; exact stationary attainment is
not asserted there.

The native absorbing SUM-debt infimum is zero throughout the class. The
construction excludes every positive absorbing-debt source on this class,
regardless of its payoff support. It assumes no root, continuation, orbit,
strategic certificate, favorable selector, or invariant region.

## 2. The finite polynomial tests

For q in [0,1]^4 let B be the independent random opposing quitter set and
write

    H_i=PRODUCT_(j!=i)(1-q_j),
    P_i=E Z_i(B), Q_i=E Z_i(B union{i}),
    F_i=(1-H_i)Q_i-P_i.                                  (3)

For u in the cube put

    D_j=1+(rho_j-1)u_j>0,
    psi_j(u_j)=rho_j u_j/D_j,
    G_i(u)=m_i(u) D_-i(u)^2 F_i(psi(u)),
    D_-i=PRODUCT_(j!=i)D_j.                              (4)

To compute G without rational functions, for opposing B set
w_B=PRODUCT_(j in B)u_j PRODUCT_(j outside B,j!=i)(1-u_j),
rho_B=PRODUCT_(j in B)rho_j and define

    P_hat_i=SUM_B rho_B w_B Z_i(B),
    Q_hat_i=SUM_B rho_B w_B Z_i(B union{i}),
    h_i=PRODUCT_(j!=i)(1-u_j).

Then

    G_i=m_i [(D_-i-h_i)Q_hat_i-D_-i P_hat_i].             (5)

This is a polynomial linear in the sixty native rewards at fixed rho,m.
It need not be independent of its own coordinate. That independence is
not used in the projection proof: strict positivity of its multiplier is
what preserves every coordinate's cube sign, zero, and boundary condition.

For one pair relabel its preferred owner 0 and partner 2; set
K={u in [0,1]^4:u0>=u2}. For two pairs relabel preferred owners 0,1 and
partners 2,3; set K={u:u0>=u2,u1>=u3} intersected with the cube.
On a selected tied wall substitute u_i=u_k=t and denote the other two
coordinates by x,y. The polynomial L_ik=(G_i-G_k)|wall has degree at
most (4,3,3) in (t,x,y): the original field has degree at most two per
opposing coordinate, and identifying two coordinates in m adds at most
two to the t degree and one to each crossing degree.

For ONE pair require all 5*4*4=80 Bernstein coefficients of L_ik at
degree (4,3,3) to be nonnegative.
For TWO pairs let x be the other preferred owner and y its partner,
substitute x=s+(1-s)z,y=s, and require all 5*7*4=140 coefficients at
degree (4,6,3) in (t,s,z) to be nonnegative for EACH selected pair.
The latter parametrization is onto 0<=y<=x<=1. These tests imply

    G_i>=G_k on the selected tied wall intersected with K. (6)

For a polynomial sum_gamma A_gamma v^gamma with coordinate degree bound n,
the coefficient at alpha is explicitly

    beta_alpha=SUM_(gamma<=alpha) A_gamma PRODUCT_l
                    binom(alpha_l,gamma_l)/binom(n_l,gamma_l). (7)

The constant coefficient is automatically zero. All choices are finite
raw parameters; no quantified continuum oracle is part of the criterion.
The theorem includes the old 27/90 tests: constant m and degree elevation
preserve nonnegative Bernstein coefficients.

At fixed odds rho, FINDING the weights is itself a finite linear-program
problem. Formula (5) and the coefficient formula (7) are linear in the
sixty-four unknown vertex values mu. All wall inequalities are homogeneous
in mu. A solution with every mu>0 can be multiplied by the reciprocal of
its smallest entry, so feasibility is equivalent to the closed LP

    mu_i,a>=1 for all 64 entries;
    all selected 80 or 280 wall coefficients >=0.         (7a)

Conversely every feasible point in (7a) supplies strictly positive weights
and hence all the required polynomials. There are four oriented one-pair
choices and four oriented two-pair choices. Thus at any fixed odds choice,
eight explicit LPs decide the weighted-wall part of the raw criterion.
For rational Z and rho these LPs have rational coefficients, and every
nonempty feasible polyhedron has a rational point, so rational weights can
be produced. The column tests are separate finite scalar calculations.
This is a raw-data adapter; no equilibrium is among the LP unknowns.

## 3. Nonzero stationary root from projection

Assume det Gamma!=0 and strict guards on negative-own owners for now.
At the origin

    G(0)=0, DG(0)=-A,
    A=diag(m_i(0)) Gamma diag(rho).                       (8)

Derivatives of m and D do not contribute because F(0)=0. Thus A has the
strict matching signs and nonzero determinant. It is R0: if w>=0,
Aw>=0 and w_i(Aw)_i=0, every support of size at least two lies in the
kernel of its principal submatrix. Two-owner principal determinants are
negative. Every three-owner determinant is the sum of two positive cycle
products, since each triangle has one favorite edge and two crossing
edges. The full determinant is nonzero. Singleton support instead gives
an outside negative crossing coordinate of Aw. Hence w=0.

For w in the nonnegative ordered cone and a selected preferred i with
partner k, lower w_i to w_k to obtain wbar. Differentiating (6) along
h wbar at h=0 yields (A wbar)_i-(A wbar)_k<=0. Since A_ii=0 and
A_ki>0,

    (Aw)_i-(Aw)_k
      =(A wbar)_i-(A wbar)_k-A_ki(w_i-w_k)<=0.            (9)

Let v equal one on selected preferred owners and zero elsewhere. For
eta>0, projection onto compact convex K and Brouwer produce a fixed point
of u -> Pi_K(u+G(u)+eta v). Its variational inequality is

    <G(u)+eta v,p-u><=0 for every p in K.                 (10)

This implies ordinary CUBE complementarity for G+eta v. Away from ties,
individual coordinate variations give the signs. At an interior tied pair,
increasing the preferred coordinate and decreasing its partner would give
G_i+eta<=0<=G_k, contradicting (6). At a tied zero pair, increasing the
preferred coordinate gives its nonpositive sign, and (6) makes the partner
strictly negative. At a tied one pair, decreasing the partner gives its
nonnegative sign, and (6) makes the preferred coordinate strictly positive.
These arguments treat all other cube coordinates, including sure owners.

No sequence of such fixed points can collapse to zero as eta tends to
zero. Otherwise divide by r=max(||u||_infinity,eta), pass to a subsequence,
and obtain

    w in the ordered nonnegative cone,
    Aw>=tau v, w_i[(Aw)_i-tau v_i]=0,
    max(||w||_infinity,tau)=1, tau>=0.                    (11)

The quadratic remainder in (8) divided by r tends to zero. If tau=0,
R0 is contradicted. If tau>0, choose any selected pair (i,k). If w_k>0,
then w_i>=w_k>0 and the active equations give (Aw)_i-(Aw)_k=tau,
contradicting (9). Thus w_k=0, and row i has only negative crossing
coefficients and zero diagonal, forcing (Aw)_i<=0<tau. This is again
impossible. Compactness now gives a NONZERO limit satisfying cube
complementarity for G.

Every m_i D_-i^2 is strictly positive on the compact cube, and psi
preserves zero, one, and the open interval. Thus q=psi(u) has EXACTLY
the required cube signs for F: F_i<=0 at q_i=0, F_i=0 in the interior,
and F_i>=0 at q_i=1. There is no transformed game or transformed strategy.
A sole active owner a with q_a=t>0 would give every inactive j

    F_j=t[t J_ja-Gamma_ja].                              (12)

Condition (1a) excludes that possibility whenever s_a<0. If it occurs
on an unguarded owner then s_a>=0, and Section 4 supplies its actual
boundary rather than discarding that root.

## 4. Full behavioral and uniform consumer

If at least two hazards are positive, H_i<1 for every i. Set

    d_i=1-(1-q_i)H_i,
    U_i=[q_i Q_i+(1-q_i)P_i]/d_i.

Direct algebra gives Q_i-(P_i+H_i U_i)=F_i/d_i. Thus the cube signs say
prescribed actions maximize the two Bellman values. Under ANY unilateral
complete behavioral replacement, opponents alone absorb geometrically;
iteration leaves a remainder bounded by a constant times H_i^n. This
vanishes uniformly over the replacement, proving terminal Nash.

For a reward bound R, expected n-stage average payoff differs from expected
terminal payoff by at most 2R/[n(1-H_i)], uniformly over those replacements.
The same bound holds under prescribed play. This proves the same-profile
fixed uniform target. As every replacement absorbs, replacing Z_i by
lambda_i Z_i+s_i transforms every terminal response payoff affinely and
preserves all best responses, even for negative s_i.

If only owner a has positive hazard t, all other owners face geometrically
absorbing opponents and the same argument applies to them. Owner a faces
only Never opponents: every finite Quit date gives its actual singleton
reward s_a, and Never gives zero. Since s_a>=0, its prescribed geometric
clock is an exact best response. Its finite-horizon payoff approaches s_a;
any replacement's finite-horizon payoff is at most s_a. Its uniform regret
therefore tends to zero. This proves the SAME stationary profile's exact
terminal Nash and fixed uniform-payoff conclusion at this boundary too.
In native coordinates that owner's singleton value is zero, so the
native profile is absorbing exact Nash in either case.

Before absorption the public history is just all-Continue. Each player uses
independent private Bernoulli randomization. A complete behavioral deviation
can change its entire first-Quit law, including its separate Never atom.
The preceding bounds cover all these laws, unbounded stopping, and every
finite deadline; no public randomization or correlated device is used.

## 5. Weak and singular closure with the SAME polynomial weights

A positivity lemma supplies an auxiliary native table W at the selected
rho,m and orientations. Its participant rewards are zero; its passive
rewards are additive, W_i(C)=SUM_(j in C)Lambda_ij if i is not in C.
Require Lambda favorites positive and crossings negative. Then
F_i^W=-SUM_(j!=i)Lambda_ij q_j.

On a selected wall (i,k), write the other owners j,l and D_out=D_j D_l.
Choose Lambda_ik=1, Lambda_ki=C, and Lambda_ij=Lambda_il=-B,
Lambda_kj=Lambda_kl=-1. The corresponding wall polynomial is

    t D_out^2 [C rho_i m_k D_i-rho_k m_i D_k]
    + SUM_(a in {j,l}) rho_a u_a D_a D_b^2
                      [B m_i D_k^2-m_k D_i^2],           (13)

where b is the other crossing owner. All weights are restricted to the
wall. Restricted m_i and m_k have strictly positive Bernstein coefficients
at degree (2,1,1). Indeed identifying two variables multiplies positive
Bernstein basis factors; every resulting coefficient is a positive convex
combination of the original sixteen values. Each D has positive endpoint
values, so its Bernstein coefficients and those of its powers are positive.
Products and degree elevations preserve strict coefficient positivity.

Choose C so every coefficient in the first bracket is positive at degree
(3,1,1); choose B so every coefficient in the second is positive at degree
(4,1,1). Explicitly, take 1 plus the largest of the finitely many ratios
of the negative coefficient to the corresponding strictly positive
coefficient. This is a finite raw construction. The first summand in (13)
has strictly positive coefficients whenever alpha_t>=1, and each crossing
summand has them whenever its crossing index is positive, all at degree
(4,3,3). Consequently EVERY nonconstant wall coefficient is strictly
positive. The two pairs specify disjoint rows, so the construction can be
made for both, including an arbitrary orientation of an unused pair.

For completeness the restricted two-pair substitution preserves this
strictness. Substitution x=s+(1-s)z,y=s carries each nonnegative Bernstein
basis polynomial to a polynomial with nonnegative Bernstein coefficients:
use x=s+(1-s)z and 1-x=(1-s)(1-z), expand positive powers, and multiply
by y=s and 1-y=1-s. Its degree is at most (4,6,3). A polynomial with
all nonconstant coefficients positive at degree (4,3,3) coefficientwise
dominates epsilon(t+x+y) for some epsilon>0. After substitution, the latter
is epsilon[t+2s+(1-s)z], whose coefficients are positive at EVERY
nonconstant index at degree (4,6,3). Thus all required restricted
nonconstant wall coefficients are strictly positive as well.

We may ensure det Lambda!=0. Let S be the favorite permutation matrix,
which is invertible. The strict coefficient inequalities survive adding
small positive delta S to Lambda: all changes are explicit linear changes
of finitely many coefficients. Choose a positive delta_max below their
finite margin divided by twice one plus the largest absolute change
coefficient. Five distinct numbers in (0,delta_max) cannot all
be roots of det(Lambda+delta S), a degree-four polynomial with nonzero
leading coefficient det S. Select one with nonzero determinant. The
singleton signs remain correct. This supplies the promised W completely.

For epsilon>0 put Z^epsilon=Z+epsilon W. Formula (5) is linear in Z,
so every required wall inequality persists, becoming strict off the
constant. Participant pairs J stay unchanged, while negative crossing
singletons decrease. Hence every weak alternative (1b) becomes a strict
column cover. Strict covers persist for sufficiently small epsilon by
continuity of the finite minimum. No cover is needed on owners with s_a>=0.
The polynomial det(Gamma+epsilon Lambda) has nonzero leading coefficient,
so all but finitely many epsilon give a nonsingular singleton matrix.
Choose such epsilon tending to zero and apply Sections 3–4.

For the corresponding actual games use the same lambda,s. Their rewards
converge uniformly to r. For any prescribed or deviating behavioral profile,
the terminal payoff changes by at most the largest reward perturbation,
because the unchanged terminal probability law has total mass at most one.
Thus the produced profiles are terminal approximate Nash for r with errors
tending to zero. The exact all-errors/fixed-target equivalence then gives
one fixed UE payoff. This does not assume the approximating targets agree.

## 6. Exact complete family outside EVERY constant-row odds test

Fix 0<k<1/10. For masks 0,...,15 (the binary mask encodes the quitting
coalition) define rows 0 and 2 by

    Z0 = [0,0,-1,k,25,37,25+26k,37+38k,
          -10,-26,-10-9k,-26-25k,15,11,15+16k,11+12k],
    Z2 = [0,25,-1,25,0,37,0,37,-10,15,-10,15,-26,11,-26,11]. (14)

For rows 1 and 3 use additive passive and participant rules:

    Gamma=[[0,-1,25,-10],[-1,0,-1,1],
           [25,-1,0,-10],[-1,5,-1,0]],
    B_1=(-19/20,0,-19/20,2), B_3=(1/2,-2,1/2,0),
    Z_i(C)=SUM_(j in C,j!=i)[Gamma_ij+1_(i in C) B_ij].  (15)

Equations (14)–(15) specify all sixty absorbing rewards. The actual
separating game is r=Z+1, with zero live and Never rewards. All own levels
are positive. Even so, all four columns satisfy the strict cover (1a),
with respective minima 49/75,1,49/75,4/29. The first and third minima occur
at t=52/75 and the fourth at t=11/29; column1 has the constant receiver
line 1. The singleton matrix has det Gamma=575 and strictly positive
inverse

    [[51/575,50/23,74/575,1/23],
     [1/23,20/23,1/23,5/23],
     [74/575,50/23,51/575,1/23],
     [5/23,123/23,5/23,2/23]].                           (16)

At rho=1 choose m0=m1=m3=1, m2=1+k u1. Direct substitution yields

    F0=(1+k q1) F2 whenever q0=q2.                      (17)

Thus either orientation of pair02 has an identically zero weighted wall
polynomial. All 80 tests hold exactly. This family belongs to the new
class for EVERY k in the stated interval; k=1/20 is a rational control.

We now exclude every old constant-row choice, including arbitrary positive
odds weights, row weights, orientations, relabelings, and one-/two-pair
selections. The singleton signs uniquely fix the favorite pairing.

First, pair13 cannot be selected in EITHER orientation, even with the
other pair restricted. If owner1 is preferred, at q1=q3=0,q0=q2=1,
F1=-19/10<0<F3=1. If owner3 is preferred, at q1=q3=1,q0=q2=0,
F3=-2<0<F1=2. These tied endpoint points belong to every ordered domain
on the other pair and are unchanged by all odds transformations. No
positive row multiplier can reverse those opposite signs.

It remains to exclude one-pair02. Suppose owner0 is preferred, and write
r=c0/c2, R=rho0/rho2. At u0=u2=0, q3=0 and q1 tending to zero,
F2=q1 and F0=q1(1+k q1). The wall inequality therefore forces r>=1.
Along the favorite axis near zero it forces c0 rho2<=c2 rho0, so R>=r.
With q1=q3=0 the exact favorite-axis polynomials are

    F0=q2(37q2-25), F2=q0(37q0-25).                    (18)

If R>1, choose the tied transformed coordinate so q2=25/37. Then
q0>q2, F0=0<F2, contradicting the preferred0 wall inequality independently
of every positive multiplier. Thus R<=1, forcing R=r=1.
Equal favorite odds and equal row weights cancel their denominator factors
on the wall. But at q0=q2=1/2,q1=1/4,q3=0,

    F2=-13/16, F0-F2=-13k/64<0,                         (19)

contradicting preferred0 order.

If owner2 is preferred, the same tangent and favorite-axis argument with
indices reversed gives rho2/rho0=c2/c0=1. At q0=q2=0,q1=1/2,q3=0,
F2=1/2 and F0=(1+k/2)/2>F2, contradicting preferred2 order.
Consequently ALL previous odds-order tests fail, even before their column
guards are considered. This is not failure only at the displayed weights.

## 7. Complete sure-first punishment exclusion

Write v for the true actual punishment vector and m_i=v_i-1. Literal
Never guarantees the minimum of zero and all actual passive rewards, so
(14) gives

    m0>=-10-9k, m2>=-10.                                (20)

No attained minimizing profile or common punishment strategy is assumed.
For any first root q with a sure quitter, the actual Quit-minus-Continue
comparison at this vector is

    h_i=g_i-H_i m_i, g_i=Q_i-P_i.                        (21)

If another owner is sure, H_i=0 and h_i=g_i. Every root Nash point must
have h_i<=0 at zero, h_i=0 in the interior, and h_i>=0 at one.
Writing x=q1,y=q3,h=1+kx,D=12-x(1-y), exact identities give

    g2=12q0-16y+x(1-q0)(1-y),
    g0=h [12q2-16y+x(1-q2)(1-y)]+kx H0.               (22)

Suppose q0=1 but q2<1. Then h2=g2<=0. From (20)–(22),

    h0-h h2 <= (1-q2)[-h D+(kx+10+9k)(1-x)(1-y)]<0.   (23)

Indeed D>=11, h>=1, and kx+10+9k<11 for k<1/10. This contradicts
h0>=0. Therefore sure0 forces sure2. Conversely, if q2=1 but q0<1,
then h0=g0 and

    h2-h0/h <= (1-q0)[-D+10(1-x)(1-y)]<0,              (24)

contradicting h2>=0>=h0. Thus sure2 forces sure0.

When q0=q2=1, the other comparisons are h1=2q3-19/10 and h3=1-2q1.
Their cube signs force both coordinates interior: if q1=0 then h3>0
forces q3=1 and h1>0 is impossible; if q1=1 then h3<0 forces q3=0
and h1<0 is impossible. Their unique solution is q1=1/2,q3=19/20.
There h2=-16/5 and h0=-(16/5)(1+k/2), contradicting sure-owner signs.

If q1=1, then h3=(q0+q2)/2-2<=-1, forcing q3=0. Now h2=1+11q0>0
and h0=(1+k)(1+11q2)>0 force q0=q2=1, but h1=-19/10<0.
If q3=1, then h2=12q0-16<0 and h0=(1+kq1)(12q2-16)<0 force
q0=q2=0; then h1=2>0 forces q1=1, but h3=-2<0.
These cases exhaust the entire sure boundary, all mixed opponent supports,
and multiple sure quitters.

Every owner's full continuation best-response cap is at least its true
punishment value. Non-sure owners never reach a continuation when another
owner quits surely. Raising the continuation above punishment only makes
Continue more attractive to a sole sure owner. Thus the above failure
excludes ALL first roots with a sure quitter and ALL full behavioral tails.
Compactness and continuity of the punishment-root regret give a uniform
positive gap on the sure boundary, excluding the complete all-errors
instant-punishment mechanism. This does not exclude arbitrary periodic or
nonstationary equilibria; the new theorem produces actual equilibria.

## 8. Complete response-quotient census and other named comparisons

A positively row-scaled response quotient requires proportionality of the
merged F rows on the block-constant hazard cube. A nonzero two-coefficient
minor excludes every pair of positive constant row scales. The following
census uses the displayed block order; tuples indicate monomial exponents.

| Partition | Rows | Monomials | Minor |
| --- | --- | --- | --- |
| 01\|2\|3 | 0,1 | 001,010 | -15 |
| 1\|02\|3 | 0,2 | 001,101 | -100k |
| 1\|2\|03 | 0,3 | 001,010 | 35 |
| 0\|12\|3 | 1,2 | 001,010 | -11 |
| 012\|3 | 0,1 | 01,10 | -4 |
| 12\|03 | 1,2 | 01,10 | 15 |
| 0\|2\|13 | 1,3 | 001,010 | 4 |
| 02\|13 | 0,2 | 01,02 | -121k |
| 2\|013 | 0,1 | 01,10 | 11 |
| 0\|1\|23 | 2,3 | 001,010 | -51 |
| 01\|23 | 0,1 | 01,10 | -15 |
| 1\|023 | 0,2 | 01,11 | -225k |
| 0\|123 | 1,2 | 01,10 | -11 |
| 0123 | 0,1 | 1,2 | 2(35k+17)/5 |

All minors are nonzero for the entire interval. The discrete partition
retains Gamma, whose R0 degree is +1 by its positive inverse and positive
determinant, so it fails the negative-degree selector. One can check this
without a formula: at offset -1 every complementary solution satisfies
x=Gamma^(-1)(1+w)>0, so w=0 and the unique Jacobian has positive determinant.
This excludes every partition in that named producer, not every conceivable
reduction with state-dependent multipliers.

The matching inverse-source producers based on A=Gamma-J fail immediately:
A02=A20=-12, so their positive-favorite premise is false, invariant under
positive row scaling and the sign-determined relabeling. The complete full
and three-core nonnegative-inverse raw selections also fail: the full determinant is positive, while each proper triple contains
an owner whose favorite was deleted and whose remaining row is negative.
That triple cannot send a nonnegative vector to all ones. Supportwise
balanced premium fails on pair02, whose two participant premiums are 37.
The conditional face-gap range criterion fails in row0: its own singleton
bounds Quit-without below by 0, the grand coalition bounds Quit-with below
by 11+12k<13, while the passive favorite singleton forces Continue-upper
at least25, for every blocker.

Every two-sided crossed lower-face selection fails. If an owner's selected
partner is adjacent, leave only its favorite at hazard1/4: the residual is
(1/4)[J_i,f/4-Gamma_i,f]<0 in every row. For pair02, outside owner3 sure
gives F0=-16. For pair13, outside owner0 sure gives F1=-19/20. These
choices cover every unordered pair, including weak lower-face guards.
Each of the three pair partitions fails a scheduled joining increment:
use g1 against sole0=-19/20 for 01|23, g3 against sole1=-2 for 02|13,
and g0 against sole3=-16 for 03|12. There is no pair with BOTH joining
increments negative. Positive participant-premium/nonnegative scheduled
increment pair classes fail on these same choices. The mixed-premium positive-passive pair class could only select pair13,
but its outside passive anchors are Z0({1,3})=-10-9k and Z2({1,3})=-10,
both negative. The literal equal-crossing symmetric paired or rotating classes fail because rows0 and2 have unequal
negative crossings -1 and -10, invariant under positive row scaling.

These comparisons are for the named finite raw selectors, not the union
of all conceivable prior UE existence theorems or eventual size-threshold
families. The literal calibration has a weak wall identity; Section 9 moves it into
the strict interior and proves a full open reward neighborhood. Supplied
stationary or cycle verifiers can of course consume the strategy produced here.

## 9. A full sixty-dimensional open enlargement

The separation from every old odds test is stable under arbitrary small
reward perturbations, even though that old parameter space is unbounded.
Here is the required parameter trapping argument; simple continuity at a
fixed choice of odds would not suffice.

Fix any k in (0,1/10), and let Z' approach the literal table (14)–(15).
Write all entries in the following inequalities for Z'. Nearby, the
crossings stay negative, the favorites stay positive, and

    a0=Gamma02/J02 in (0,1), a2=Gamma20/J20 in (0,1).

If the old one-pair test with preferred0 holds for some positive c,rho,
put r=c0/c2 and R=rho0/rho2. Its crossing and favorite tangent inequalities
and its favorite-axis zero force

    r >= Gamma21/Gamma01,
    R >= r Gamma02/Gamma20,
    R <= odds(a2)/odds(a0), odds(a)=a/(1-a).             (25)

The third inequality follows by choosing the tied transformed coordinate
so q2=a0. There F0=0, so F2=q0(J20 q0-Gamma20)<=0 requires q0<=a2.
The tied odds relation is odds(q0)=R odds(q2), giving (25). All three
bounds converge to one as Z' tends to the calibration. Together they
force BOTH r and R into a compact rectangle shrinking to (1,1),
independently of absolute odds and the two crossing odds.

To see that these are all relevant parameters, let t=q2. On a transformed
tied wall one has q0=psi_R(t)=Rt/[1+(R-1)t] and
D0/D2=1+(R-1)t. The entire old wall inequality is therefore

    r F0(t,x,y) >= [1+(R-1)t]^2 F2(psi_R(t),x,y).        (26)

Here F0 is viewed as a polynomial of (q2,q1,q3), and F2 of (q0,q1,q3).
All other denominator factors cancel. At the calibration and r=R=1,
the left side minus the right side at (t,x,y)=(1/2,1/4,0) is
-13k/64. Continuity and the shrinking rectangle exclude preferred0
throughout some full neighborhood of the native table. More formally,
any sequence of nearby tables with old certificates would have r,R->1,
and (26) at that fixed witness would contradict this strict negative limit.

For preferred2 the swapped inequalities trap c2/c0 and rho2/rho0 near
one. The fixed witness t=q0=0,x=1/2,y=0 then has preferred2 minus partner
value -k/4<0. Pair13 is excluded robustly in either orientation by its
strict opposite-sign endpoints from Section 6, even on restricted
second-pair domains. Thus EVERY old one-/two-pair odds test remains
impossible on a full neighborhood, with all parameter choices covered.

The sure-first exclusion is also open for actual rewards. If two reward
tables are within delta in sup norm, every fixed behavioral payoff changes
by at most delta. Supremum over responses and infimum over opponents
preserve that bound, so each true punishment value is 1-Lipschitz in the
reward table. The finite punishment-root regret is continuous jointly in
the table, its punishment vector and its root. Its strictly positive
minimum on the compact sure-root boundary from Section 7 therefore stays
positive on a neighborhood. This preserves the exclusion of every sure
root with every full behavioral tail, including the all-errors mechanism.
Each of the fourteen quotient minors is nonzero at the calibration, so
all fourteen failures persist. Positive inverse entries and determinant
persist as well, retaining the discrete partition's positive degree.
The other comparisons in Section 8 have strict finite separating signs,
which likewise persist. For diagonal symmetrization, the directed triangle
013 products are respectively 1 and 50; their inequality also persists
and excludes every positive diagonal row scaling.

We can move INSIDE the new wall class with an explicit direction. Let
W have zero participant rewards and additive passive rewards with matrix

    Lambda=[[0,-2,1,-2],[-2,0,-2,1],
            [2,-1,0,-1],[-1,2,-1,0]], det Lambda=-21.  (27)

Keep rho=1, m0=m1=m3=1 and m2=1+k u1. On pair02 its weighted wall is

    t(1+2kx)+(x+y)(1-kx).                               (28)

At degree (4,3,3), every nonconstant Bernstein coefficient of (28) is
at least 1/4. Indeed it coefficientwise dominates
 t+(1-k)(x+y): the difference is a sum of nonnegative Bernstein products
2ktx+kx(1-x)+ky(1-x). The latter linear polynomial's coefficient at a
nonzero index is at least min(1/4,(1-k)/3)=1/4.

Consequently Z^(k,epsilon)=Z^k+epsilon W has all 79 nonconstant
pair02 coefficients at least epsilon/4 for every epsilon>0. Its constant
coefficient is identically zero, as it is for EVERY native table.
For all sufficiently small epsilon>0, this explicit perturbed table is
still in the open exclusion neighborhoods just proved. The singleton
signs, nonsingularity and strict column covers also persist. At each such
center, strict wall coefficients, singleton signs, determinant and column
margins persist on a full open neighborhood in the 56-dimensional space
of native tables with fixed zero own singletons.

Finally the linear correspondence

    actual table r <-> (Z,s),
    s_i=r_i({i}), Z_i(C)=r_i(C)-s_i for nonempty C        (29)

is an isomorphism from all sixty absorbing coordinates onto 56 native
coordinates and four own levels. Allow s to vary near (1,1,1,1), keeping
every own level positive and remaining in the actual sure-exclusion
neighborhood. The resulting set is a nonempty FULL sixty-dimensional
open set of actual games. Every member satisfies the new raw producer,
and every member defeats all old constant-row odds tests, every sure-first
punishment root/tail, every scaled response partition, and the finite
strict comparisons above. No quantitative radius is asserted: the raw
membership tests remain explicit finite LPs, and (27) gives an explicit
direction entering their strict interior.

This open-family conclusion uses the same theorem and is not a separate
counted class from the polynomial-weight enlargement.

## 10. Exact source correspondence and handoff

The stationary consumer inspected in source is
`terminalNash_and_sameProfileUniform_of_stationaryBoundary`
(`UniformEquilibrium/Quitting/Stationary/ResponseInvariantQuotientSameProfile.lean`).
Sections 3–4 supply its actual root, Bellman identities and boundary. The
all-errors endpoint is
`quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors`
(`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`).
It has the complete behavioral quantifiers and fixed-before-accuracy target
used in Section 5. The sure-root source definition is
`HasQuittingPunishmentVectorNashRootWithSureQuitter`
(`UniformEquilibrium/Quitting/Classification/InstantPunishmentSureQuitterCharacterization.lean`).
The quotient source is `QuittingResponseInvariantOnUnitCube`
(`UniformEquilibrium/Quitting/Stationary/ResponseInvariantQuotient.lean`).
The calibration's discrete matrix degree agrees with
`r0Degree_eq_sign_det_of_nonnegative_inverse`
(`MathUE/LinearProgramming/NonnegativeInverseDegree.lean`).

The known stationary no-go remains:
`periodTwo_no_absorbing_stationary_exactTerminalNash`
(`UniformEquilibrium/Quitting/Examples/BlockPair/FourPlayerPairedSingletonPeriodTwoStationary.lean`)
excludes absorbing stationary equilibrium for the Solan–Vieille table.
The new raw criterion is not universal and makes no claim to cover that
counterexample to stationary sufficiency. No Lean file is changed or built.

A formalization can retain multiaffine m as sixteen positive vertex values
per owner, define the 80/280 raw coefficient tests, prove cube-sign
preservation and projection noncollapse, and use (13) for the weak/singular
perturbation. The row multipliers are proof tools; they do not alter actual
reward tables, observations, randomization, or opponents' response sets.

## 11. Reproduction

The standalone exact checker below reconstructs all sixty rewards, (16)–(24),
column margins, all old-odds obstruction identities, and all fourteen
response-partition minors symbolically. The topology, unrestricted behavioral
consumer, global sure-boundary case split, and singular approximation are
mathematical proofs above; finite arithmetic is not substituted for them.
Run with Python 3 and SymPy.

```python
"""Exact calibration for polynomial row-weighted one-pair projection.
Python 3 + SymPy. No file input or output. Parameter 0 < k < 1/10.
"""
import itertools
import sympy as s

I = tuple(range(4))
q = s.symbols('q0:4')
k = s.symbols('k', positive=True)
GAMMA = s.Matrix([[0,-1,25,-10],[-1,0,-1,1],
                  [25,-1,0,-10],[-1,5,-1,0]])
B = s.Matrix([[0,1,12,-16],[-s.Rational(19,20),0,-s.Rational(19,20),2],
              [12,1,0,-16],[s.Rational(1,2),-2,s.Rational(1,2),0]])

def table():
    z = {(i,m): sum(GAMMA[i,j]+(B[i,j] if m>>i&1 else 0)
                   for j in I if j!=i and m>>j&1)
         for i in I for m in range(16)}
    r0 = [0,0,-1,k,25,37,25+26*k,37+38*k,
          -10,-26,-10-9*k,-26-25*k,15,11,15+16*k,11+12*k]
    r2 = [0,25,-1,25,0,37,0,37,-10,15,-10,15,-26,11,-26,11]
    for m in range(16): z[0,m]=s.sympify(r0[m]); z[2,m]=s.sympify(r2[m])
    return z

def expectation(z,i,quit):
    return s.expand(sum(z[i,m|1<<i if quit else m]*s.prod(
        q[j] if m>>j&1 else 1-q[j] for j in I if j!=i)
        for m in range(16) if not m>>i&1))

def partitions(items):
    if not items:
        yield ()
        return
    a,*rest=items
    for p in partitions(rest):
        yield ((a,),)+p
        for j,b in enumerate(p): yield p[:j]+((a,)+b,)+p[j+1:]

def main():
    z=table()
    H=[s.prod(1-q[j] for j in I if j!=i) for i in I]
    P=[expectation(z,i,False) for i in I]
    Q=[expectation(z,i,True) for i in I]
    F=[s.expand((1-H[i])*Q[i]-P[i]) for i in I]
    g=[s.expand(Q[i]-P[i]) for i in I]
    h=1+k*q[1]
    assert all(z[i,1<<i]==0 for i in I)
    assert all(z[i,1<<j]==GAMMA[i,j] for i in I for j in I)
    assert GAMMA.det()==575 and all(v>0 for v in GAMMA.inv())
    assert s.expand((F[0]-h*F[2]).subs(q[2],q[0]))==0
    assert s.expand(g[2]-(12*q[0]-16*q[3]+q[1]*(1-q[0])*(1-q[3])))==0
    assert s.expand(g[0]-h*g[2].subs(q[0],q[2])-k*q[1]*H[0])==0
    # Every row0 passive coefficient >= -10-9k, row2 >= -10.
    for i,bound in ((0,-10-9*k),(2,s.Integer(-10))):
        for m in range(16):
            if m>>i&1: continue
            d=s.expand(z[i,m]-bound)
            assert d.subs(k,0)>=0 and d.subs(k,s.Rational(1,10))>=0
    # Column covers: direct all-t lower envelopes at rational k-control.
    margins=[]
    for a in I:
        lines=[(z[j,(1<<j)|(1<<a)].subs(k,s.Rational(1,20)), -GAMMA[j,a])
               for j in I if j!=a]
        points={s.S.Zero,s.S.One}
        for (m,b),(n,c) in itertools.combinations(lines,2):
            if m!=n and 0<=(c-b)/(m-n)<=1: points.add((c-b)/(m-n))
        margins.append(min((max(m*t+b for m,b in lines),t) for t in points))
    assert margins==[(s.Rational(49,75),s.Rational(52,75)),(1,0),
                     (s.Rational(49,75),s.Rational(52,75)),(s.Rational(4,29),s.Rational(11,29))]
    # For all k>0, row2 gives column1 line exactly 1, and other columns do not depend on k.
    assert z[2,6]==0 and GAMMA[2,1]==-1
    assert z[0,9]-GAMMA[0,3] == z[2,12]-GAMMA[2,3] == -16
    # Constant-weight/odds obstruction identities (see mathematical proof).
    x=s.symbols('x')
    assert s.expand(F[2].subs({q[0]:0,q[1]:x,q[3]:0})-x)==0
    assert s.expand(F[0].subs({q[2]:0,q[1]:x,q[3]:0})-x*(1+k*x))==0
    assert s.expand(F[2].subs({q[1]:0,q[3]:0})-q[0]*(37*q[0]-25))==0
    assert s.expand(F[0].subs({q[1]:0,q[3]:0})-q[2]*(37*q[2]-25))==0
    bad={q[0]:s.Rational(1,2),q[2]:s.Rational(1,2),q[1]:s.Rational(1,4),q[3]:0}
    assert F[2].subs(bad)==-s.Rational(13,16)
    assert s.expand((F[0]-F[2]).subs(bad))==-13*k/64
    assert F[1].subs({q[0]:1,q[2]:1,q[3]:0})==-s.Rational(19,10)
    assert F[3].subs({q[0]:1,q[2]:1,q[1]:0})==1
    assert F[1].subs({q[0]:0,q[2]:0,q[3]:1})==2
    assert F[3].subs({q[0]:0,q[2]:0,q[1]:1})==-2
    # Sure-boundary force identities.
    assert s.expand(g[0].subs({q[1]:1,q[3]:0})-(1+k)*(1+11*q[2]))==0
    assert s.expand(g[2].subs(q[1],1)-(1+11*q[0]-q[3]*(16+1-q[0])))==0
    assert s.expand(g[0].subs(q[3],1)-h*(12*q[2]-16))==0
    assert s.expand(g[2].subs(q[3],1)-(12*q[0]-16))==0
    assert s.expand(g[1].subs({q[0]:1,q[2]:1})-(2*q[3]-s.Rational(19,10)))==0
    assert s.expand(g[3].subs({q[0]:1,q[2]:1})-(1-2*q[1]))==0
    sure={q[0]:1,q[2]:1,q[1]:s.Rational(1,2),q[3]:s.Rational(19,20)}
    assert g[2].subs(sure)==-s.Rational(16,5)
    assert s.expand(g[0].subs(sure)+(1+k/2)*s.Rational(16,5))==0
    # Every nondiscrete response quotient has a nonzero coefficient minor.
    census=[]
    for part in partitions(list(I)):
        if len(part)==4: continue
        ts=s.symbols('t:'+str(len(part)))
        sub={q[i]:ts[j] for j,b in enumerate(part) for i in b}
        polys=[s.Poly(ff.subs(sub),*ts) for ff in F]
        found=None
        for block in part:
            for i,j in itertools.combinations(block,2):
                monoms=sorted(set(polys[i].monoms())|set(polys[j].monoms()),key=lambda z:(sum(z),z))
                for a,b in itertools.combinations(monoms,2):
                    minor=s.factor(polys[i].coeff_monomial(a)*polys[j].coeff_monomial(b)-
                                   polys[i].coeff_monomial(b)*polys[j].coeff_monomial(a))
                    if minor != 0:
                        # Certify no zeros in the open k interval.
                        poly=s.Poly(minor,k)
                        assert poly.degree()<=1
                        left,right=minor.subs(k,0),minor.subs(k,s.Rational(1,10))
                        if left*right>=0 and (left!=0 or right!=0):
                            found=(i,j,a,b,minor)
                            break
                if found: break
            if found: break
        assert found is not None
        census.append((part,found))
    assert len(census)==14
    # Explicit strict auxiliary direction and full-dimensional opening.
    L=s.Matrix([[0,-2,1,-2],[-2,0,-2,1],[2,-1,0,-1],[-1,2,-1,0]])
    assert L.det()==-21
    t,x,y=s.symbols('t x y')
    fw=-L*s.Matrix(q)
    wall=s.expand((fw[0]-(1+k*q[1])*fw[2]).subs({q[0]:t,q[2]:t,q[1]:x,q[3]:y}))
    assert s.expand(wall-(t*(1+2*k*x)+(x+y)*(1-k*x)))==0
    poly=s.Poly(wall,t,x,y)
    for alpha in itertools.product(range(5),range(4),range(4)):
        beta=s.expand(sum(coef*s.prod(s.binomial(alpha[j],power[j])/s.binomial((4,3,3)[j],power[j])
             for j in range(3)) for power,coef in poly.terms() if all(power[j]<=alpha[j] for j in range(3))))
        if alpha==(0,0,0): assert beta==0
        else:
            assert beta.subs(k,0)>=s.Rational(1,4)
            assert beta.subs(k,s.Rational(1,10))>=s.Rational(1,4)
    assert GAMMA[0,2]-z[0,5]==GAMMA[2,0]-z[2,5]==-12
    assert GAMMA[0,1]*GAMMA[1,3]*GAMMA[3,0]==1
    assert GAMMA[1,0]*GAMMA[3,1]*GAMMA[0,3]==50
    assert z[0,5]==z[2,5]==37
    assert z[0,1]==0 and z[0,15]==11+12*k
    assert z[0,10]==-10-9*k and z[2,10]==-10
    assert all(F[i].subs({q[j]:s.Rational(1,4) if j==(i+2)%4 else 0 for j in I})<0 for i in I)
    print('PASS: explicit det(-21) auxiliary direction; all 79 wall margins >= 1/4')
    print('PASS: literal table, det575, positive inverse, polynomial wall identity')
    print('PASS: strict column covers, all-weight odds obstruction identities, sure-boundary identities')
    print('Column margins:',margins)
    for row in census: print(row)
    print('PASS: all 14 scaled quotient partitions; symbolic 0 < k < 1/10')

if __name__=='__main__': main()
```
