# Alternating pairs from positive inverse cones and asymmetric losses

This gives two complete raw four-player existence theorems in ordinary
mathematics, with an exact sixty-reward calibration and a full reward-space
neighborhood. One theorem permits arbitrary singleton matrices with strictly
positive inverse; the other permits a complementary asymmetric scalar family.
No strategic root or continuation is an input. No new Lean verification or
full Fin4 closure is claimed.

## 1. Actual model and the common conclusion

There are four players I={0,1,2,3}. At each live date each chooses Continue
or Quit using independent private randomization and observed public history.
The first nonempty quitter coalition C absorbs at the finite vector r(C).
Live dates, including the selecting date, and perpetual Continue pay zero.
A deviation may replace one player's entire behavioral strategy.

Choose arbitrary real own levels s_i and positive recipient scales lambda_i,
and define comparison entries on NONEMPTY coalitions only by

    Z_i(C)=(r_i(C)-s_i)/lambda_i.

Require Z_i({i})=0, so s_i is the actual own singleton reward. This notation
does not translate live or Never payoffs. Write Gamma_ij=Z_i({j}), so Gamma
has zero diagonal and receiver rows, quitting-owner columns.

Each of the two raw classes below has an exact proper period-two terminal
Nash profile against every unilateral complete behavioral replacement.
Every opponent-deleted family absorbs geometrically. One fixed initial
terminal vector is a uniform-equilibrium payoff; the same profile works at
every accuracy and every sufficiently long finite horizon. The signed own
levels are unrestricted. No strategic root, hazard, continuation, source
minimum or cycle certificate is supplied as an input. Every player relabeling
is allowed. Section4 proves the complete semantic conclusion for both routes.

## 2. General positive-inverse raw producer

Assume Gamma is invertible and B=Gamma^-1 is strictly positive entrywise.
No matching sign pattern, favorite relation or inverse of a joint-adjusted
matrix is assumed. Choose a partition into two pairs, and write m(i) for
player i's partner and {j,k}=I minus {i,m(i)} for the opposite pair.
Define raw comparisons

    p_i=Z_i({i,m(i)}), c_i=p_i-Gamma_i,m(i),
    P_i=Z_i({j,k}).

Require p_i>=0 and c_i>0. From the singleton inverse alone define

    R_ab=max_l B_al/B_bl,
    eta_i=c_i(1/R_j,m(i)+1/R_k,m(i)),
    kappa_i=c_i/(R_j,m(i)+R_k,m(i)).                   (C1)

All these constants are finite and strictly positive. Require

    P_i<=eta_i,
    Z_i({i,j}), Z_i({i,k}), Z_i({i,j,k})<=kappa_i      (C2)

for every i. These are four passive-pair bounds, eight nonscheduled
participant-pair bounds and four outsider-joining-triple bounds. They have
no lower bounds. The other twenty-four nonsingleton coordinates are arbitrary
finite numbers: eight passive entries on nonscheduled pairs, twelve other
triple entries and four grand-coalition entries.

**Theorem.** Every original table satisfying (C1)–(C2) and the preceding
inverse and premium hypotheses has the common conclusion in Section1.
The schedule alternates the two chosen pairs. All four hazards are produced
from the raw table; no supplied positive nonlinear root is assumed.

### 2.1. The inverse cone and radial production

For every column l of B let b_l=B_.l/(SUM_a B_al), and let C_B be the convex
hull of these four normalized columns. It is a nonempty compact convex
subset of the strictly positive unit simplex. Every v in C_B satisfies

    v_a<=R_ab v_b for all a,b.                         (C3)

Indeed B_al<=R_ab B_bl for every column, and the inequality survives any
nonnegative combination and normalization. Define on x>0

    T_i(x)=c_i x_m(i)(x_j+x_k+x_j x_k)
           +p_i x_m(i)^2/(1+x_m(i))-P_i x_j x_k.      (C4)

For v in C_B and t>0, put

    A_i(v)=c_i v_m(i)(v_j+v_k)-P_i v_j v_k,
    C_i(v)=c_i v_m(i) v_j v_k.

By (C2) and (C3),

    A_i(v)/(v_j v_k)
      =c_i(v_m(i)/v_k+v_m(i)/v_j)-P_i>=0,
    C_i(v)>0.

The exact radial identity is

    T_i(tv)/t=t A_i(v)+t^2 C_i(v)
               +p_i t v_m(i)^2/(1+t v_m(i)).          (C5)

Thus every coordinate T_i(tv)/t is strictly positive and strictly increasing
in t, tends to zero at t=0, and tends to positive infinity as t increases
without bound. These conclusions include p_i=0 and equality in P_i<=eta_i.
Since B is strictly positive, the same statements hold for

    h_v(t)=SUM_i (B T(tv))_i/t.

There is a unique t(v)>0 with h_v(t(v))=1. An explicit common compact
bracket follows from the positive column sums bsum_l=SUM_a B_al. Put

    delta=min_(a,l) B_al/bsum_l,
    H=delta^3 SUM_i bsum_i c_i,
    M=SUM_i bsum_i[3c_i+max(-P_i,0)+p_i],
    t_low=min(1,1/(2M)), t_high=max(1,sqrt(2/H)).

Here delta,H,M are strictly positive. On C_B all coordinates lie in
[delta,1], so h_v(t)>=H t^2; for 0<t<=1, h_v(t)<=M t.
Thus h_v(t_low)<=1/2, h_v(t_high)>=2 and every t(v) lies strictly
inside this common bracket. The scalar t(v) is continuous: if v_n tends
to v, every convergent subsequence of t(v_n) has a limit in the bracket;
continuity of h makes that limit a root for v, and uniqueness makes it
t(v). Compactness then proves convergence of the full sequence. No
nonsingular strategic Jacobian or selected solution branch is needed.

Set

    Phi(v)=B T(t(v)v)/t(v).

The sum of its coordinates is one. It lies in C_B, because T(t(v)v)>0
and a normalized positive B-image is a convex combination of the normalized
columns b_l, with weights proportional to T_l(t(v)v) SUM_a B_al.
Therefore Phi is a continuous self-map of C_B. Brouwer's theorem gives a
fixed point v. Choosing one such point once and setting x=t(v)v gives

    x=B T(x), equivalently Gamma x=T(x),              (C6)

with all four coordinates strictly positive and finite. This produces the
root from arbitrary data in the stated raw class. It also gives the cone
bounds x_a<=R_ab x_b needed for the inactive decisions.

### 2.2. All phase policies and action endpoints

Set q_i=x_i/(1+x_i). In each phase the two owners in its scheduled pair
independently Quit with these hazards; the opposite pair Continues. Repeat
the two phases after every all-Continue outcome. For owner i, define native
annotations at its own active phase and its inactive phase by

    V_i^active=p_i q_m(i), V_i^inactive=c_i x_m(i).    (C7)

At its active phase the Quit endpoint is p_i q_m(i). The Continue endpoint is

    Gamma_i,m(i) q_m(i)+(1-q_m(i))c_i x_m(i)
      =(Gamma_i,m(i)+c_i)q_m(i)=p_i q_m(i).

At its inactive phase put D_i=(1+x_j)(1+x_k). Its Continue endpoint is

    [Gamma_ij x_j+Gamma_ik x_k+P_i x_j x_k
                        +p_i x_m(i)/(1+x_m(i))]/D_i.

It equals c_i x_m(i): substituting Gamma_i,m(i)=p_i-c_i
shows this equality is exactly coordinate i of (C6). Thus every policy
recursion and all four active mixing equalities hold.

The inactive owner's Quit endpoint, including simultaneous joining of both
scheduled opponents, is bounded by

    Q_i<=(kappa_i/D_i)(x_j+x_k+x_j x_k)
         <kappa_i(x_j+x_k)
         <=kappa_i(R_j,m(i)+R_k,m(i))x_m(i)
         =c_i x_m(i).                                  (C8)

The strict middle inequality holds because x_j,x_k>0 and

    (x_j+x_k)D_i-(x_j+x_k+x_j x_k)
      =x_j^2+x_k^2+x_j x_k+x_j^2 x_k+x_j x_k^2>0.

It persists even when every joining cap in (C2) is attained. Every inactive
owner strictly prefers Continue and every active owner mixes between
maximizing endpoints. The actual annotations are s_i+lambda_i V_i^phase.
At each root the coalition masses and all-Continue mass sum to one, so
these recursions and inequalities transfer to the original rewards by
positive scaling and the same own offset. Section4 identifies them as
actual values and proves the full deviation and uniform-horizon claims.

The raw criterion is invariant under every positive recipient scaling.
Multiplying row i of all native comparisons by lambda_i changes B to
B diag(1/lambda), so each column ratio B_al/B_bl and every R_ab stays
unchanged. It multiplies p_i,c_i,P_i,eta_i,kappa_i and row i's joining
comparisons by lambda_i. Thus all inequalities transform together.
Signed own offsets are addressed by the actual absorption proof in Section4.

## 3. Complementary asymmetric scalar producer

Let f=(01)(23) be the favorite matching. The directed strong crossing cycle is 0->2->1->3->0. Choose

    a>c+d, c>0, d>0, K>=0, L>=0,
    0<=p<=min(c,d)(c+d)/a.                              (1)

The singleton comparisons, in receiver rows and quitting-owner columns, are

    Gamma=[[0,a,-c,-d], [a,0,-d,-c],
           [-d,-c,0,a], [-c,-d,a,0]].                    (2)

Let A={0,3} and B={1,2}. Their four participant comparisons are all p:

    Z_0(A)=Z_3(A)=Z_1(B)=Z_2(B)=p.

Their four passive comparisons are

    Z_1(A)=Z_0(B)=-K, Z_2(A)=Z_3(B)=-L.                (3)

The remaining eight participant-pair comparisons satisfy Z_i({i,j})<=p.
The four outsider joining triples satisfy

    Z_1(013), Z_2(023), Z_0(012), Z_3(123)<=0.          (4)

All other twenty-four nonsingleton coordinates are arbitrary finite numbers:
eight passive entries on nonscheduled pairs, twelve other triple entries,
and the four grand-coalition entries. The eight pair caps and four triple
caps have no lower bounds. Every relabeling is allowed.

**Theorem.** Every original table (1)–(4) has an exact proper period-two
terminal Nash profile against every unilateral complete behavioral
replacement. It uses the crossing pair03 at one phase and12 at the other.
Every opponent-deleted family absorbs geometrically. One fixed initial
terminal vector is a uniform-equilibrium payoff; the same profile works at
every accuracy and every sufficiently long finite horizon. The signed own
levels are unrestricted. No strategic root, hazard, continuation, source
minimum or cycle certificate is supplied as an input.

The class includes independent arbitrarily negative scheduled passive
rewards and unequal crossing singleton losses. The existence theorem does
not require inverse matrices. The calibration below lies strictly in the
positive-J matching exceptional branch with one inverse cycle below one.

The scalar route has genuinely additional premium scope. For example,
take a=3,c=d=1,p=2/3,K=L=0, every participant-pair comparison equal to
2/3, and the required joining triples zero. This meets (1)–(4), including
the allowed upper premium endpoint. Its singleton inverse is

    [[2,7,3,3],[7,2,3,3],[3,3,2,7],[3,3,7,2]]/15.

For either crossing schedule, Section2 gives every kappa_i=2/7<2/3,
so the actual joining pairs violate that criterion. For the favorite
schedule, c_i=2/3-3<0. Thus this raw table fails all three schedule choices
of Section2 while the scalar theorem supplies its equilibrium. No claim
that the two criteria are identical or that one subsumes the other is needed.

### 3.1. Producing the two positive odds

Put sigma=c+d. For positive odds x,y write D=(1+x)(1+y) and define

    E0=(p+d)y D-p y/(1+y)-a x+c y+Kxy,
    E3=(p+c)x D-p x/(1+x)+d x-a y+Lxy.                 (5)

We produce a joint zero, rather than assume one. Put

    N(x)=(p+c)x(1+x)+d x-p x/(1+x),
    B(x)=a-(p+c)x(1+x)-Lx.

There is a unique x_bar>0 with B(x_bar)=0, because B(0)=a>0, B is strictly
decreasing on the nonnegative axis, and it tends to minus infinity.
For 0<x<x_bar, N(x)>0: indeed

    N(x)-sigma x=x^2[c(1+x)+p(x+2)]/(1+x)>0.

Hence Y(x)=N(x)/B(x)>0 is continuous there and satisfies E3(x,Y(x))=0.
It tends to zero as x decreases to zero and to positive infinity as x
increases to x_bar. Moreover Y(x)/x tends to sigma/a. Therefore

    lim_(x->0+) E0(x,Y(x))/x=sigma^2/a-a<0.             (6)

At x->x_bar, the positive quadratic term (p+d)(1+x)Y(x)^2 dominates;
the term -pY/(1+Y) is bounded, -ax is bounded, and the other unbounded
terms are nonnegative. Thus E0(x,Y(x)) tends to positive infinity.
The intermediate value theorem supplies x in (0,x_bar) with
E0(x,Y(x))=0. Set y=Y(x). Fix any such root once from the raw table.
No uniqueness or branch regularity is needed for the global theorem.

The equations give useful strict ratio bounds. Rearranging them yields

    ax-sigma y=(p+d)y(D-1)+p y^2/(1+y)+Kxy>0,
    ay-sigma x=(p+c)x(D-1)+p x^2/(1+x)+Lxy>0.          (7)

All signs hold also at p=0, because c,d,x,y>0. Thus

    sigma/a < x/y < a/sigma.                           (8)

### 3.2. Every phase policy and all sixteen action endpoints

Set alpha=x/(1+x), beta=y/(1+y). At phase A, owners0 and3 independently
Quit with probabilities alpha,beta. At phase B, owners1 and2 independently
use alpha,beta. Everyone else Continues. Repeat A,B after every all-Continue
outcome. The candidate native phase values are

    V_A=(p beta, (p+d)y, (p+c)x, p alpha),
    V_B=((p+d)y, p beta, p alpha, (p+c)x).              (9)

At phase A, active owner0 has Quit endpoint p beta and Continue endpoint

    -d beta+(1-beta)(p+d)y=p beta.

Active owner3 similarly has both endpoints p alpha, since its singleton
loss from owner0 is c. Phase B has the corresponding exact equalities for
owners1 and2. These four equalities are independent of the two root
equations and retain the actual pair-collision rewards.

At phase B, inactive owner0 has Continue endpoint

    [a x-c y-Kxy+p beta]/D=(p+d)y,

by E0=0. At phase A, inactive owner1 has the same expression. Likewise,
phase A owner2 and phase B owner3 have Continue endpoint

    [-d x+a y-Lxy+p alpha]/D=(p+c)x

by E3=0. Thus every policy recursion is exact.

For ANY inactive owner, its two potentially quitting opponents belong to
the other scheduled pair. The two singleton-join outcomes are bounded by p
using the eight remaining participant-pair caps, and the simultaneous-join
outcome is bounded by zero using (4). Its forced-Quit endpoint is at most

    p[alpha(1-beta)+(1-alpha)beta]=p(x+y)/D.             (10)

If p=0, each inactive Continue value in (9) is strictly positive and (10)
is nonpositive. If p>0, D>1 and (7) imply

    (p+d)y-p(x+y)/D > d y-px
                         > (d-p a/sigma)y >=0,
    (p+c)x-p(x+y)/D > c x-py
                         > (c-p a/sigma)x >=0.         (11)

The final inequalities use (1). Therefore every inactive owner strictly
prefers Continue, including at the allowed equality in the premium bound.
Active owners mix between maximizing endpoints. This checks all sixteen
phase/player/action endpoints, including deviations that join both active
owners simultaneously.

The actual phase annotations are s_i+lambda_i V_phase,i. At a root all
coalition masses together with the all-Continue mass sum to one, so the
original-game recursions and endpoint inequalities follow by the stated
positive scaling and offset. The following tail argument identifies these
annotations as actual values and validates the signed offsets globally.

## 4. Actual infinite laws, complete caps, and one fixed target

This argument applies to both raw producers. Write q_i in (0,1) for each
owner's hazard in its single active phase. The scalar producer specializes
to q_0=q_1=alpha and q_2=q_3=beta. All coins are private and independent.
Joint survival through a period is

    rho=PRODUCT_i(1-q_i)<1.

Policy recursion iterated through n periods has a bounded continuation
remainder multiplied by rho^n. It tends to zero. Consequently the phase
annotations (C7) or (9), with actual offsets and scales, are the actual
terminal prescribed values.

After deleting player i, the opponents' period survival is

    rho_i=PRODUCT_(j!=i)(1-q_j)<1.

Let rho_*=max_i rho_i; rho_*<1. This absorption bound is independent
of the deleted player's replacement strategy. Against the fixed opponents,
any complete behavioral replacement has a private first-Quit law on the
natural dates plus literal Never, because the only surviving public history
is repeated all Continue. For a finite pure deadline, iterate the Continue
inequality up to that date and apply its Quit bound. For Never, iterate
forever; the bounded remainder tends to zero at rate rho_*^n. Every such
pure response is bounded by the proposed actual phase value. Arbitrary
private mixtures preserve the bound. This proves exact terminal Nash against
all complete behavioral deviations, not just phase-stationary deviations.

Every prescribed outcome and every unilateral response absorbs surely,
so each recipient receives the same own offset s_i on all such outcomes.
No affine invariance at positive Never is being assumed.

Let R bound the absolute original absorbing rewards. The first opponent
quit occurs by the end of a geometric number of two-date periods, uniformly
over every unilateral replacement. Its expected selecting date is at most
2/(1-rho_*). With the selecting live date paying zero, the difference
between terminal expected payoff and the N-stage average is at most

    2R/[N(1-rho_*)].                                   (12)

The same bound holds for prescribed play. Thus every N-stage deviation
gain is at most 4R/[N(1-rho_*)], and prescribed averages tend to the actual
initial phase vector s+lambda V_initial. This vector is fixed before accuracy. The same
profile therefore witnesses one uniform-equilibrium payoff.

The inspected existing semantic consumers are
`isZeroAsymptoticNash_quittingCyclicBehaviorProfile_of_certificate` and
`isUniformEquilibriumPayoff_quittingCyclicTerminalValue_of_certificate`
(`UniformEquilibrium/Quitting/Cycles/PeriodicCompiler.lean`). Their exact
inputs are policy recursions, phase root Nash, and opponent-cycle contraction;
the ordinary proof above supplies each. `IsεQuittingRootNash`
(`UniformEquilibrium/Quitting/Root/FirstBranch.lean`) was also inspected.
No new Lean declaration or build is claimed.

## 5. Literal sixty-reward exceptional calibration

Take a=3,c=21/10,d=3/20,p=1/100,K=1,L=0, own levels all1, and scales all1.
The complete actual table is

| Quitters | Actual reward vector |
| --- | --- |
| 0 | (1,4,17/20,-11/10) |
| 1 | (4,1,-11/10,17/20) |
| 2 | (-11/10,17/20,1,4) |
| 3 | (17/20,-11/10,4,1) |
| 01 | (101/100,101/100,1,1) |
| 02 | (101/100,1,101/100,0) |
| 03 | (101/100,0,1,101/100) |
| 12 | (0,101/100,101/100,1) |
| 13 | (1,101/100,0,101/100) |
| 23 | (1,1,101/100,101/100) |
| 012 | (1,0,0,0) |
| 013 | (0,1,0,0) |
| 023 | (0,0,0,1) |
| 123 | (0,0,1,0) |
| 0123 | (-1,-1,-1,-1) |

Every off-diagonal participant comparison J_ij is 1/100. Both Gamma and
A=Gamma-J have strictly positive inverses and the strict matching sign
pattern. Their two inverse crossing-cycle products are

    471132205633522740670561/1124945068785777318242881 <1,
    3804057762915868823769121/1124945068785777318242881 >1.

Thus the example lies strictly inside the exceptional cycle branch.

For exact isolation,

    Y(x)=-x(211x^2+437x+225)/[(x+1)(211x^2+211x-300)].

Define

    P(x)=276519931x^7+6585082120x^6+25766206569x^5
       +29732741521x^4-7763742750x^3-29419306875x^2
       -7836750000x+3543750000.

Exact substitution gives

    E0(x,Y(x))=-x P(x)/
      [100(x+1)(15x^2+314x+300)(211x^2+211x-300)^2].

Sturm counts give exactly one simple root x in

    (2391257815/10^10,2391257817/10^10).

The denominator has no zero there and Y is positive. This yields proper
hazards approximately alpha=0.19297942 and beta=0.21725771. The approximations
are descriptive; the algebraic isolation and the global proof supply the
exact equilibrium. Its actual initial payoff is approximately

    (1.00217258,1.04440957,1.50455540,1.00192979).

The checker also evaluates all local endpoints using this literal table,
including its four possibly smaller outsider triple entries. Arbitrary
higher rewards have not been substituted for the fixed calibration.

## 6. A full sixty-coordinate open family and a regular branch

The calibration satisfies every raw condition of Section2 strictly, giving
a direct open-family theorem. Its schedule is m=(03)(12), and exact
substitution into (C1) gives

    p=(1/100,1/100,1/100,1/100),
    c=(4/25,4/25,211/100,211/100), P=(-1,-1,0,0),
    kappa_0=kappa_1=212957/4345425>1/100,
    kappa_2=kappa_3=13010471/26300400>1/100,
    eta_0=eta_1=623/3100>0,
    eta_2=eta_3=149177/74400>0.

All four relevant joining triples are nonpositive. The inverse B is
strictly positive, every scheduled premium and c_i is strictly positive,
and the four passive and twelve joining caps have strict slack.
Matrix inversion is continuous where the determinant is nonzero. Finite
maxima, sums and quotients of positive inverse entries are continuous.
Centering at each table's actual own singleton and using scales one,
all these strict hypotheses persist on a neighborhood in the ENTIRE
sixty-dimensional original reward space. Section2 therefore produces
exact terminal Nash and Section4 gives one fixed uniform target for every
table in this neighborhood. This proof requires no selected hazard branch.
Appendix C checks all displayed raw constants exactly.

An independent local continuation selects the particular algebraic root in
Section5. The explicit calibration has strictly inactive gaps and four proper hazards.
Its active equations are nonsingular even when the four hazards vary
independently; the symmetric two-variable derivative alone would not suffice.
Use odds x0,x1,y2,y3 for owners0,1,2,3 at their designated phase. Put
D_A=(1+x0)(1+y3), D_B=(1+x1)(1+y2). The four centered equations at the
calibration's parameter family are

    F0=(p+d)y3 D_B-p y3/(1+y3)-a x1+c y2+K x1y2,
    F1=(p+d)y2 D_A-p y2/(1+y2)-a x0+c y3+K x0y3,
    F2=(p+c)x1 D_A-p x1/(1+x1)+d x0-a y3+L x0y3,
    F3=(p+c)x0 D_B-p x0/(1+x0)+d x1-a y2+L x1y2.       (13)

At x0=x1=x and y2=y3=Y(x), the checker takes the determinant of the
Jacobian in all four variables. After substitution it is a rational function
of x whose numerator has degree22. Exact Sturm counts show that neither
its numerator nor denominator vanishes in the isolating interval above.
Its sign is negative there. Thus the full four-variable Jacobian is
nonsingular; its approximate determinant is -53.88799.

For arbitrary nearby original tables, center each recipient at its own
singleton. At an active pair its native value is its pair comparison times
the other hazard. Active indifference determines its next passive value
by division by the other owner's Continue probability. Substituting these
values into the four passive policy recursions gives a smooth four-equation
system in the four odds and all sixty raw reward coordinates. At the center
this system is (13), up to harmless positive row denominators. Hence its
hazard derivative is invertible. The implicit function theorem produces
proper positive hazards for every table in a sufficiently small open
neighborhood in the ENTIRE sixty-dimensional original reward space.
The strict inactive caps and opponent contraction persist there. Section4
then gives exact terminal Nash and one uniform target for every nearby table.
This second neighborhood also carries a smooth selected hazard branch.
No explicit neighborhood radius or universal openness of UE existence is
asserted. The general raw criterion and this particular nonsingular system
give two independent local existence arguments at the calibration.

## 7. Complete preceding-class comparisons

This section concerns the literal sixty-reward calibration of Section5 and
specified complete producer classes. It proves a genuine increment beyond
stationary, sure-first and the named paired-phase criteria, not just failure
of a particular numerical root search. All fields below are native fields
of that same actual table, with own level one retained in the semantic
comparison. Appendix B gives the full self-contained rational audit.

### 7.1. Exact stationary complementarity

For independent stationary hazards q in [0,1]^4, write

    H_i=PRODUCT_(j!=i)(1-q_j),
    P_i=E Z_i(B), Q_i=E Z_i(B union{i}),
    F_i=(1-H_i)Q_i-P_i,

where B is the opposing random quitter coalition. Each F_i is independent
of q_i and has degree at most two in each other coordinate.

**Proposition.** The only cube-complementary point of F is q=0:

    q_i F_i(q)>=0, (1-q_i)F_i(q)<=0 for every i
      implies q=0.                                      (1)

Consequently the actual table has NO stationary terminal Nash profile
against all behavioral deviations. For q!=0 the total absorption probability
d=1-PRODUCT(1-q_i) is positive, and the stationary payoff/endpoint identities
make (1) necessary for exact Nash. At q=0 actual payoff is zero, while any
owner can quit immediately for one. This last literal-Never comparison is
kept separate; native AllNever is still Nash.

No numerical solver is used as proof of (1). Sections 7.2–7.3 give an analytic
origin exclusion and an exhaustive exact integer cube certificate.

### 7.2. The whole origin neighborhood

Write F(q)=-Gamma q+R(q). There are no constant terms in R and no linear
terms. Exact expansion gives

    K=max_i SUM_(monomials of total degree>=2)
                 |coefficient of F_i| = 451/20.

Therefore ||R(q)||_infinity<=K ||q||_infinity^2 on the cube. Every
principal submatrix Gamma_SS for |S|>=2 is invertible. The maximum infinity
operator norm of their inverses is

    L=max_(|S|>=2) ||Gamma_SS inverse||_infinity = 20/3.

Both equalities are independently recomputed with rational arithmetic by
the checker. Put delta=1/256; then LK delta=451/768<1.

Suppose 0<||q||_infinity<=delta and (1) holds. If the positive support S
has at least two owners, every active coordinate is strictly between zero
and one, so F_S=0. Thus Gamma_SS q_S=R_S, giving

    ||q||_infinity <= LK ||q||_infinity^2,

contradicting LK delta<1. If only owner a has positive hazard t, an adjacent
inactive owner j has F_j=t[(1/100)t-Gamma_ja]>0 because Gamma_ja<0.
That contradicts (1). This excludes EVERY nonempty support in the closed
origin box; it does not require full support or a generic root.

### 7.3. The entire stationary cube

The standalone checker is Appendix B.
It reconstructs Z and F from the literal sixty rewards. For each F_i it
computes all coefficients in the tensor Bernstein basis of degree (2,2,2,2),
using exact rational arithmetic. Independence from q_i is simply degree
elevation in that coordinate. Every polynomial lies between the minimum
and maximum of these coefficients throughout the cube.

Starting from the full closed cube, the checker repeatedly bisects one
coordinate at its midpoint. The two closed children cover their parent.
For a coordinate's degree-two coefficient slice (a0,a1,a2), the exact
children, at FOUR TIMES the previous positive denominator, are

    left: (4a0,2(a0+a1),a0+2a1+a2),
    right:(a0+2a1+a2,2(a1+a2),4a2).                    (2)

All subsequent arithmetic is on integers. A leaf [lo,hi] is discharged
by one of exactly three rules:

* max hi_i<=1/256, covered by Section 7.2;
* lo_i>0 and EVERY coefficient of F_i is strictly negative;
* hi_i<1 and EVERY coefficient of F_i is strictly positive.

The latter two rules contradict (1) at every point of the whole closed leaf,
including all other players' zero/sure boundaries. Both children are always
retained, so termination with every leaf discharged proves full coverage.
The exact run has 1309 nodes, 655 leaves and maximum depth 40. Every leaf
contains a dyadic box, its complete split path, and either the analytic
origin rule or an explicit nonzero integer coefficient bound with its
positive denominator.

The checker reads NO external data; it independently regenerates the entire
tree and every integer bound. The optional argument `--write-certificate`
followed by a chosen filename saves every dyadic leaf and its rational sign
bound for separate inspection.

Without the option it performs the complete proof calculation without
writing a file. The output node counts are assertions, not stopping budgets.
A depth limit raises an error; it never treats an unresolved box as proved.
NumPy arrays use Python integer objects, not machine integers or floats.

### 7.4. A positive gap over all stationary profiles

The exact obstruction strengthens to a uniform positive terminal
exploitability gap over the stationary strategy class. This remains much
weaker than a gap over all behavioral profiles.

Suppose stationary profiles q^n had terminal Nash errors tending to zero.
No q^n=0 can occur eventually because its immediate-Quit gain is one.
If a subsequence converges to q!=0, prescribed stationary payoffs and the
two one-step response payoffs are continuous there. Their limiting
inequalities give (1), contradicting Sections 7.2–7.3.

It remains to exclude q^n->0. Put h_n=SUM_i q_i^n>0 and pass to a
subsequence with w_i=q_i^n/h_n converging in the simplex. The prescribed
NATIVE payoff tends to (Gamma w)_i: the absorption denominator is
h_n+O(h_n^2), while the native payoff numerator is
(Gamma q^n)_i+O(h_n^2). Prescribed actual payoff is one plus this value.
Immediate Quit has actual payoff 1+O(h_n), so approximate Nash forces
Gamma w>=0. A singleton w is impossible because it gives a negative
crossing coordinate of Gamma w.

Hence w has at least two positive coordinates. Whenever w_i>0, at least
one opponent has positive limiting normalized hazard. Literal Never by i
therefore has limiting native payoff (Gamma w)_i/(1-w_i), and limiting
actual payoff one plus that quantity: the opponents absorb almost surely
at each sufficiently large n. Approximate Nash implies

    (Gamma w)_i >= (Gamma w)_i/(1-w_i).

Combined with Gamma w>=0 and w_i>0 this forces (Gamma w)_i=0. Thus
w>=0, Gamma w>=0 and w_i(Gamma w)_i=0, with SUM w_i=1.
This contradicts R0. Indeed every support of size at least two has the
nonsingular principal matrix already checked in Section 7.2, and singleton
support was excluded by a crossing sign. No exchange of limits with a
supremum is used: only immediate Quit, literal Never and one-step
responses are tested.

This compactness contradiction proves existence of a fixed positive gap
against every stationary prescribed profile. It supplies no explicit gap
constant and makes no assertion about nonstationary prescribed profiles.

### 7.5. Every sure-first root and every continuation

Every actual participant reward is at least -1. An owner who quits
immediately therefore guarantees at least -1 against every opponents'
profile. Consequently the TRUE actual punishment value v_i satisfies
v_i>=-1, so its centered continuation m_i=v_i-1 satisfies m_i>=-2.
This is a valid lower bound from one complete strategy; an exact punishment
formula or a jointly attained punishment vector is unnecessary.

At a root q followed by that punishment vector, the exact native comparison
is

    h_i(q)=g_i(q)-H_i(q)m_i, g_i=Q_i-P_i.                (3)

If a different owner quits surely then H_i=0, so this comparison is
independent of every continuation value. For a sole sure owner, lowering
its m_i only makes Quit more attractive. Thus ANY sure-first Nash root at
the true punishment vector would also be a Nash root at the optimistic
vector m=(-2,-2,-2,-2).

The checker substitutes q_a=1 separately for every owner a and constructs
the four exact polynomial fields g_i+2H_i. It applies the same integer
Bernstein subdivision to each full three-dimensional face. No origin
exception is allowed. The four exhaustive trees have respectively
35,41,29,39 nodes, and EVERY leaf violates a required cube sign. They
include all zero/interior/sure combinations of the other three owners.
Hence there is no sure-root Nash point even at the optimistic vector,
and therefore none at the true punishment vector.

For ANY full behavioral continuation, the owner's best-response cap is
at least its true punishment value. On a sure-first root all nonsure
owners have H=0. Raising a sole sure owner's continuation cap makes
Continue more attractive. The same exclusion therefore covers EVERY
sure-first root and EVERY behavioral tail. Compactness of the sure-root
boundary and continuity of the optimistic-vector regret give a strictly
positive gap, so the full all-errors instant-punishment mechanism fails,
not merely one selected punishment profile.

### 7.6. All fifteen scaled response partitions

All fifteen partitions are audited, allowing arbitrary positive CONSTANT
row scales. Twelve partitions have the following nonzero coefficient
minors on their block-constant hazard cubes (the displayed block order
specifies the tuple coordinates):

| Partition | Rows | Monomials | Minor |
| --- | --- | --- | --- |
| 01\|2\|3 | 0,1 | 001,010 | -351/80 |
| 1\|02\|3 | 0,2 | 001,010 | 2529/400 |
| 1\|2\|03 | 0,3 | 001,010 | -243/50 |
| 0\|12\|3 | 1,2 | 001,010 | 243/50 |
| 012\|3 | 0,1 | 01,10 | 117/80 |
| 12\|03 | 1,2 | 01,10 | -117/80 |
| 0\|2\|13 | 1,3 | 001,010 | -2529/400 |
| 02\|13 | 0,2 | 01,10 | 117/80 |
| 2\|013 | 0,1 | 01,10 | 117/80 |
| 0\|1\|23 | 2,3 | 001,010 | 117/20 |
| 1\|023 | 0,2 | 01,10 | -153/40 |
| 0\|123 | 1,2 | 01,10 | -189/80 |

There are THREE actual response-invariant choices, so claiming fourteen
nontrivial minor failures would be false. They are the discrete partition,
the favorite pairing 01|23, and the indiscrete partition. Their literal
quotient singleton matrices are respectively

    Gamma,
    [[3,-9/4],[-9/4,3]],
    [3/4].

Each has positive inverse, positive determinant and R0 degree +1. For the
two-by-two matrix the determinant is 63/16. R0 for Gamma was proved in
Section 7.4; the two-dimensional matrix has positive principal minors, and
the scalar matrix is positive, so these are R0 as well. Every pair of merged rows is
literally equal with a nonzero response polynomial; compatible positive
scales must therefore coincide within each merged block. Remaining
positive quotient-row scales preserve inverse positivity and determinant
sign. Thus every partition choice fails the NEGATIVE-degree quotient
producer, including all compatible positive row scales.

This is not a statement that the game has no quotient. It has two
nontrivial exact quotients; neither supplies the required degree exit.

### 7.7. Complete nonstationary raw-class comparisons

The following exclusions concern the entire stated choice sets of the named
producers. They do not claim exclusion of every conceivable periodic strategy
or of unspecified maximal implicit-function neighborhoods.

Every row has a unique positive favorite and two unequal negative singleton
comparisons, -21/10 and -3/20. Positive recipient scaling and player relabeling
preserve this property. Hence every role choice and positive recipient scale
fails the equal-crossing singleton hypothesis of the global asymmetric
friendly-pair producer, negative-passive friendly-pair producer, opposite-sign
matching phases, below-singleton joint phases, and both ordered and unordered
rotating mixed-premium pair producers. The same observation defeats raw
families with the literal symmetric (3,-1,-1) singleton pattern.

All twelve native participant-pair entries are 1/100. Thus every role choice
fails any raw criterion requiring a nonpositive participant-pair entry.
This includes the two-pair join-cap producer, every matching-anchor producer
requiring a participant row bounded by its own level, the mixed-premium
positive-passive pair producer, and the prescribed negative-participant
bounds of the four-joint-phase rectangle. This is invariant under positive
recipient scaling. It is a raw-hypothesis exclusion, not a claim that every
possible strategy using these supports fails.

The flexible-singleton NONMATCHING_POSITIVE_PASSIVE_PAIR and
BOUNDED_INVERSE_CORNERS classes require a separate all-scale comparison.
Both define, from their raw matrix bounds,

    ell_i=c_i lower rmin/(8 upper),
    rmin<=1/(32 upper Q), Q>=3 cmax, 0<lower<=upper.

Consequently

    ell_i<=lower/(768 upper^2)<=1/(768 upper).          (14)

Their inverse estimate includes the original singleton matrix (the zero
corner). After arbitrary positive recipient scaling lambda it therefore
gives

    upper >= (Gamma_scaled^-1)_ii=(Gamma^-1)_ii/lambda_i.

Every nonscheduled participant-pair cap would require lambda_i p<=ell_i.
Combining with (14) yields the scale-invariant necessary condition

    p (Gamma^-1)_ii <=1/768.                            (15)

At the calibration every diagonal inverse entry is3152/11949, whereas

    p (Gamma^-1)_ii=788/298725>1/768.

Thus both entire classes fail for every role assignment and every positive
recipient scaling, independently of their other determinant or corner tests.
The check does not freeze an unbounded scale search at arbitrary constants.

### 7.8. What the strict separation proves

The calibration has a positive terminal exploitability gap over all
stationary profiles and a positive gap on the complete sure-first boundary,
yet the proper period-two profile of Sections3–4 has zero terminal debt.
The stationary result rules out every member of the preceding polynomial-row-
weight class, every odds choice, every polynomial weight choice and every
one-/two-pair orientation: on a nonsingular, strictly joining-covered table
that producer would give a nonzero exact stationary root. It also rules out
its stationary-approximation boundary as an architecture, by Section7.4.
The response-quotient census includes all fifteen partitions and compatible
constant row scales, including the two actual nontrivial invariant quotients.
The comparisons in Section7.7 exhaust the choices of the named nonstationary
raw classes. These are the specified complete class separations; no absence
of all possible old schedules or all unquantified neighborhoods is claimed.

The separation is robust. The finitely many non-origin Bernstein leaves
have strict coefficient signs on fixed boxes; principal determinants stay
nonzero and the analytic bound LK/256<1 persists. The singleton crossing
signs and participant entries remain strict. Positive own rewards exclude
AllNever. Thus the stationary obstruction, including its small-hazard limit
argument, persists on a full original reward-table neighborhood.

The sure-face certificates likewise have finitely many strict signs. Under
an eta perturbation of the original table, immediate Quit guarantees at
least -1-eta and own levels lie within eta of one, so the optimistic native
continuation may be lowered to -2-2eta. All finite strict face signs persist
for sufficiently small eta; no continuity of a selected punishment strategy
is assumed. The twelve quotient minors remain nonzero. For each remaining
partition, representative singleton row sums retain positive determinant
and positive inverse. If scaled response invariance remains valid, its
quotient differs by positive row scaling and still has degree+1; otherwise
that partition is excluded already. The degree census therefore persists.

The unequal crossing entries and positive participant pairs also persist.
For the inverse-cap tests, replace p by the minimum native participant-pair
entry in each row. The strict reverse of (15) then persists by continuity
of those minima and of the inverse diagonal entries. Intersecting these neighborhoods with the
full sixty-coordinate existence neighborhood from Section6 gives a nonempty
open set of original tables with the new exact-periodic conclusion and all
these named old-class exclusions. This does not assert that the exact raw
equalities (2)–(3) themselves describe an open set.

## 8. Source correspondence and standalone verification

The proof uses ordinary algebra, Brouwer's fixed-point theorem, the
intermediate value theorem, the implicit function theorem and the explicit finite rational certificates.
The complete all-behavior and fixed-target consumer is proved in Section4.
For exact source correspondence, the inspected declarations are
`IsεQuittingRootNash` (`UniformEquilibrium/Quitting/Root/FirstBranch.lean`),
`isZeroAsymptoticNash_quittingCyclicBehaviorProfile_of_certificate` and
`isUniformEquilibriumPayoff_quittingCyclicTerminalValue_of_certificate`
(`UniformEquilibrium/Quitting/Cycles/PeriodicCompiler.lean`),
`stationaryQuittingGain_complementarity_iff_endpoints`
(`UniformEquilibrium/Quitting/Stationary/Gain.lean`),
`HasQuittingPunishmentVectorNashRootWithSureQuitter`
(`UniformEquilibrium/Quitting/Classification/InstantPunishmentSureQuitterCharacterization.lean`),
`QuittingResponseInvariantOnUnitCube`
(`UniformEquilibrium/Quitting/Stationary/ResponseInvariantQuotient.lean`), and
`r0Degree_eq_sign_det_of_nonnegative_inverse`
(`MathUE/LinearProgramming/NonnegativeInverseDegree.lean`).
No new formalization of the present producer or calibration is claimed.

Copy each appendix's Python block into a separate file and run it with
Python3. Appendices A and C require SymPy; Appendix B requires SymPy and
NumPy, using Python integer objects for all Bernstein arithmetic. None of
the checkers reads external data. Appendix A verifies all exact local endpoint identities,
the algebraic isolation and full four-hazard Jacobian, matrix branch, and
scaling-invariant cap separation. Appendix B reconstructs every stationary
and sure-face leaf and every response-quotient choice from the literal table.
Appendix C checks all sixteen generic inverse-cone endpoints, the radial
derivative, and every strict raw calibration guard. The cone existence
argument is the ordinary Brouwer proof in Section2, not a numerical search.
A failed finite proof check raises an assertion; an unresolved Bernstein
box raises an error rather than being accepted at a stopping budget.
Floating searches and numerical payoff displays are not proof inputs.

## Appendix A. Scalar existence, center and full-Jacobian checker

```python
"""Exact asymmetric crossing-pair producer checks; no floating solver is trusted."""

import sympy as s

R = s.Rational
x, y = s.symbols('x y')
a, c, d, p, K, L = s.symbols('a c d p K L', positive=True)
D = (1+x)*(1+y)
alpha, beta = x/(1+x), y/(1+y)
E0 = (p+d)*y*D-p*y/(1+y)-a*x+c*y+K*x*y
E3 = (p+c)*x*D-p*x/(1+x)+d*x-a*y+L*x*y
N = (p+c)*x*(1+x)+d*x-p*x/(1+x)
B = a-(p+c)*x*(1+x)-L*x
Y = N/B
assert s.factor(E3.subs(y, Y)) == 0
assert s.factor(N/x-(c+d)) == x*(c*x+c+p*x+2*p)/(x+1)
assert s.simplify(s.diff(E0.subs(y, Y), x).subs(x, 0)-(c+d)**2/a+a) == 0
# The root equations give the strict ratio bounds.
assert s.simplify(a*x-(c+d)*y-E0*(-1) - (
    (p+d)*y*(D-1)+p*y*y/(1+y)+K*x*y)) == 0
assert s.simplify(a*y-(c+d)*x-E3*(-1) - (
    (p+c)*x*(D-1)+p*x*x/(1+x)+L*x*y)) == 0

# A saturated completion checks every actual local endpoint. Unused rewards
# cannot enter any of these endpoints and may therefore be arbitrary.
I = range(4)
favorite = (1, 0, 3, 2)
strong = (2, 3, 1, 0)
weak = (3, 2, 0, 1)
Z = {(i, C): s.S.Zero for i in I for C in range(16)}
for i in I:
    Z[i, 1 << favorite[i]] = a
    Z[i, 1 << strong[i]] = -c
    Z[i, 1 << weak[i]] = -d
    for j in I:
        if i != j:
            Z[i, (1 << i) | (1 << j)] = p
Z[1, 9] = Z[0, 6] = -K
Z[2, 9] = Z[3, 6] = -L
qA = [alpha, 0, 0, beta]
qB = [0, alpha, beta, 0]
VA = [p*beta, (p+d)*y, (p+c)*x, p*alpha]
VB = [(p+d)*y, p*beta, p*alpha, (p+c)*x]

def endpoints(table, q, continuation, i):
    opp = [j for j in I if j != i]
    quit_value = cont_value = s.S.Zero
    for mask in range(16):
        if mask >> i & 1:
            continue
        weight = s.prod(q[j] if mask >> j & 1 else 1-q[j] for j in opp)
        quit_value += weight*table[i, mask | (1 << i)]
        cont_value += weight*(table[i, mask] if mask else continuation[i])
    return s.factor(quit_value), s.factor(cont_value)

for q, here, nxt, active, residuals in [
        (qA, VA, VB, (0, 3), {1: E0, 2: E3}),
        (qB, VB, VA, (1, 2), {0: E0, 3: E3})]:
    for i in I:
        Q, C = endpoints(Z, q, nxt, i)
        if i in active:
            assert s.factor(Q-here[i]) == 0
            assert s.factor(C-here[i]) == 0
        else:
            assert s.factor(Q-p*(x+y)/D) == 0
            assert s.factor(C-here[i]+residuals[i]/D) == 0

# Literal modified Solan--Vieille center, all sixty rewards retained.
BASE = [
    (0, 0, 0, 0), (1, 4, 0, 0), (4, 1, 0, 0), (1, 1, 1, 1),
    (0, 0, 1, 4), (1, 1, 1, 0), (0, 1, 1, 1), (1, 0, 0, 0),
    (0, 0, 4, 1), (1, 0, 1, 1), (1, 1, 0, 1), (0, 1, 0, 0),
    (1, 1, 1, 1), (0, 0, 0, 1), (0, 0, 1, 0), (-1, -1, -1, -1)]
center = {a: 3, c: R(21, 10), d: R(3, 20), p: R(1, 100), K: 1, L: 0}
Z0 = {(i, C): s.Integer(BASE[C][i]-1) for i in I for C in range(1, 16)}
for i in I:
    Z0[i, 0] = 0
    Z0[i, 1 << i] = 0
    Z0[i, 1 << favorite[i]] = 3
    Z0[i, 1 << strong[i]] = -R(21, 10)
    Z0[i, 1 << weak[i]] = -R(3, 20)
    for j in I:
        if i != j:
            Z0[i, (1 << i) | (1 << j)] = R(1, 100)
assert Z0[1, 9] == Z0[0, 6] == -1
assert Z0[2, 9] == Z0[3, 6] == 0
assert all(Z0[i, C] <= 0 for i, C in [(1, 11), (2, 13), (0, 7), (3, 14)])
Gamma = s.Matrix([[Z0[i, 1 << j] if i != j else 0 for j in I] for i in I])
J = s.Matrix([[Z0[i, (1 << i) | (1 << j)] if i != j else 0 for j in I] for i in I])
A = Gamma-J
assert all(v > 0 for v in Gamma.inv()) and all(v > 0 for v in A.inv())
cycle = (0, 2, 1, 3)
B0 = A.inv()
products = [s.prod(B0[j, i]/B0[i, i] for i, j in zip(order, order[1:]+order[:1]))
            for order in (cycle, tuple(reversed(cycle)))]
assert min(products) < 1 < max(products)
assert R(1, 100) < R(3, 20)*R(9, 4)/3

Y0 = s.factor(Y.subs(center))
assert Y0 == -x*(211*x*x+437*x+225)/((x+1)*(211*x*x+211*x-300))
P = s.Poly(276519931*x**7+6585082120*x**6+25766206569*x**5
           +29732741521*x**4-7763742750*x**3-29419306875*x**2
           -7836750000*x+3543750000, x)
residual = s.factor(E0.subs(center).subs(y, Y0))
assert s.factor(residual + x*P.as_expr()/(
    100*(x+1)*(15*x*x+314*x+300)*(211*x*x+211*x-300)**2)) == 0
lo, hi = R(2391257815, 10**10), R(2391257817, 10**10)
assert P.count_roots(lo, hi) == 1
assert P.eval(lo) > 0 > P.eval(hi)
assert s.Poly(P.diff(), x).count_roots(lo, hi) == 0
assert s.Poly(211*x*x+211*x-300, x).count_roots(lo, hi) == 0
assert Y0.subs(x, lo) > 0 and Y0.subs(x, hi) > 0

# The literal center's smaller triple rewards improve every inactive cap.
for q, here, nxt, active, residuals in [
        (qA, VA, VB, (0, 3), {1: E0, 2: E3}),
        (qB, VB, VA, (1, 2), {0: E0, 3: E3})]:
    q0 = [s.sympify(v).subs(center) for v in q]
    h0 = [s.sympify(v).subs(center) for v in here]
    n0 = [s.sympify(v).subs(center) for v in nxt]
    for i in I:
        Q, C = endpoints(Z0, q0, n0, i)
        if i in active:
            assert s.factor(Q-h0[i]) == s.factor(C-h0[i]) == 0
        else:
            assert s.factor(C-h0[i]+residuals[i].subs(center)/D) == 0
            assert s.factor(R(1, 100)*(x+y)/D-Q) in (0, x*y/D)

# Four independent hazards, not merely the symmetric two-variable slice.
x0, x1, y2, y3 = s.symbols('x0 x1 y2 y3')
DA, DB = (1+x0)*(1+y3), (1+x1)*(1+y2)
F = s.Matrix([
    (p+d)*y3*DB-p*y3/(1+y3)-a*x1+c*y2+K*x1*y2,
    (p+d)*y2*DA-p*y2/(1+y2)-a*x0+c*y3+K*x0*y3,
    (p+c)*x1*DA-p*x1/(1+x1)+d*x0-a*y3+L*x0*y3,
    (p+c)*x0*DB-p*x0/(1+x0)+d*x1-a*y2+L*x1*y2])
jac = F.jacobian([x0, x1, y2, y3]).subs(center).subs({x0: x, x1: x, y2: y, y3: y})
determinant = s.factor(jac.det())
det_num, det_den = s.fraction(s.factor(determinant.subs(y, Y0)))
assert s.Poly(det_num, x).count_roots(lo, hi) == 0
assert s.Poly(det_den, x).count_roots(lo, hi) == 0
assert determinant.subs({x: (lo+hi)/2, y: Y0.subs(x, (lo+hi)/2)}) < 0

# Complete role exclusions for the equal-crossing singleton classes.
# Each row has a unique positive favorite and two different negative entries;
# positive recipient scales and player permutations preserve this inequality.
for i in I:
    negative = [Gamma[i, j] for j in I if j != i and Gamma[i, j] < 0]
    assert len(negative) == 2 and negative[0] != negative[1]

assert all(Gamma.inv()[i, i]/100 > R(1, 768) for i in I)


# The scalar premium endpoint is outside every inverse-cone schedule choice.
Gsym = s.Matrix([[0,3,-1,-1],[3,0,-1,-1],[-1,-1,0,3],[-1,-1,3,0]])
Bsym = Gsym.inv()
assert Bsym == s.Matrix([[2,7,3,3],[7,2,3,3],[3,3,2,7],[3,3,7,2]])/15
for mate in ((1,0,3,2), (2,3,0,1), (3,2,1,0)):
    for i in I:
        ci = R(2,3)-Gsym[i,mate[i]]
        if mate == (1,0,3,2):
            assert ci < 0
        else:
            j,k = [h for h in I if h not in (i,mate[i])]
            ratio_sum = sum(max(Bsym[h,l]/Bsym[mate[i],l] for l in I) for h in (j,k))
            assert ci/ratio_sum == R(2,7) < R(2,3)

print('PASS: symbolic root production identities and all sixteen local endpoints')
print('PASS: full60 center and strict exceptional inverse-cycle products', products)
print('PASS: unique simple algebraic root in', (lo, hi))
print('PASS: nonzero four-hazard Jacobian for the full60 open continuation')
print('PASS: all-role equal-crossing singleton exclusions')
```

## Appendix B. Complete architecture and quotient checker

```python
"""Exact complete stationary and sure-first exclusion in the strict cycle branch.

Python 3, SymPy, NumPy. All proof arithmetic is rational or integer.
No input data are read. Optional --write-certificate PATH saves every dyadic
leaf with its exact integer sign bound, source denominator, and box.
This is an architecture obstruction, not a quitting-game UE counterexample.
"""
import argparse
import itertools
import json
from fractions import Fraction
import numpy as np
import sympy as s

I=tuple(range(4))
Q=Fraction
q=s.symbols('q0:4')
FAVORITE=(1,0,3,2)
STRONG=(2,3,1,0)
WEAK=(3,2,0,1)
BASE=[(0,0,0,0),(1,4,0,0),(4,1,0,0),(1,1,1,1),
      (0,0,1,4),(1,1,1,0),(0,1,1,1),(1,0,0,0),
      (0,0,4,1),(1,0,1,1),(1,1,0,1),(0,1,0,0),
      (1,1,1,1),(0,0,0,1),(0,0,1,0),(-1,-1,-1,-1)]

def table():
    z={(i,m):s.Integer(BASE[m][i]-1) if m else s.S.Zero
       for i in I for m in range(16)}
    for i in I:
        z[i,1<<i]=s.S.Zero
        z[i,1<<FAVORITE[i]]=s.Integer(3)
        z[i,1<<STRONG[i]]=-s.Rational(21,10)
        z[i,1<<WEAK[i]]=-s.Rational(3,20)
        for j in I:
            if j!=i:z[i,(1<<i)|(1<<j)]=s.Rational(1,100)
    return z

def fields(z):
    H=[];P=[];QQ=[]
    for i in I:
        pp=qq=0
        for mask in range(16):
            if mask>>i&1:continue
            w=s.prod(q[j] if mask>>j&1 else 1-q[j] for j in I if j!=i)
            pp+=z[i,mask]*w
            qq+=z[i,mask|1<<i]*w
        H.append(s.prod(1-q[j] for j in I if j!=i))
        P.append(s.expand(pp));QQ.append(s.expand(qq))
    F=[s.Poly(s.expand((1-H[i])*QQ[i]-P[i]),*q)for i in I]
    g=[s.expand(QQ[i]-P[i])for i in I]
    return H,F,g

def coefficients(polys):
    raw=[]
    for i in I:
        for alpha in itertools.product(range(3),repeat=4):
            value=sum(v*s.prod(s.binomial(alpha[j],mon[j])/s.binomial(2,mon[j])
                        for j in I) for mon,v in polys[i].terms()
                        if all(mon[j]<=alpha[j] for j in I))
            raw.append(s.sympify(value))
    denominator=int(s.ilcm(*(s.denom(v)for v in raw)))
    arr=np.array([int(v*denominator)for v in raw],dtype=object).reshape(4,3,3,3,3)
    return denominator,arr

def split_coefficients(b,axis):
    # Both child arrays represent their exact polynomials at FOUR TIMES
    # the parent's positive common denominator. Thus all sign tests below
    # use integers only; no interval rounding or tolerance is involved.
    v=np.moveaxis(b,axis+1,-1)
    a0,a1,a2=v[...,0],v[...,1],v[...,2]
    middle=a0+2*a1+a2
    left=np.stack((4*a0,2*(a0+a1),middle),axis=-1)
    right=np.stack((middle,2*(a1+a2),4*a2),axis=-1)
    return np.moveaxis(left,-1,axis+1),np.moveaxis(right,-1,axis+1)

def certify(polys,lo,hi,origin_delta=None):
    denominator,b=coefficients(polys)
    stack=[(list(lo),list(hi),b,0,'')]
    leaves=[];nodes=0;maxdepth=0
    while stack:
        lo,hi,b,depth,path=stack.pop()
        nodes+=1;maxdepth=max(maxdepth,depth)
        record={'path':path,'lo':list(map(str,lo)),'hi':list(map(str,hi))}
        if origin_delta is not None and max(hi)<=origin_delta:
            record['kind']='origin';leaves.append(record);continue
        witness=None
        for i in I:
            row=b[i].flatten()
            if lo[i]>0 and max(row)<0:
                witness=(i,'negative',int(max(row)));break
            if hi[i]<1 and min(row)>0:
                witness=(i,'positive',int(min(row)));break
        if witness is not None:
            i,sign,bound=witness
            record.update(kind='field',owner=i,sign=sign,numerator=str(bound),
                          denominator=str(denominator*4**depth))
            leaves.append(record);continue
        assert depth<64, 'Unexcluded box: certificate construction failed'
        widths=[hi[i]-lo[i]for i in I]
        maximum=max(widths)
        choices=[i for i in I if widths[i]==maximum]
        axis=choices[depth%len(choices)]
        left,right=split_coefficients(b,axis)
        middle=(lo[axis]+hi[axis])/2
        lower=lo.copy();lower[axis]=middle
        upper=hi.copy();upper[axis]=middle
        # Every split retains BOTH closed children, whose union is the
        # parent. Starting with the whole cube or face proves coverage.
        stack.append((lower,hi,right,depth+1,path+str(axis)+'1'))
        stack.append((lo,upper,left,depth+1,path+str(axis)+'0'))
    assert nodes==2*len(leaves)-1
    return {'nodes':nodes,'depth':maxdepth,'source_denominator':denominator,'leaves':leaves}

def partitions(items):
    if not items:
        yield ()
        return
    first,*rest=items
    for part in partitions(rest):
        yield ((first,),)+part
        for j,block in enumerate(part):
            yield part[:j]+((first,)+block,)+part[j+1:]

def main():
    z=table();H,F,g=fields(z)
    Gamma=s.Matrix([[z[i,1<<j]if i!=j else 0 for j in I]for i in I])
    J=s.Matrix([[z[i,(1<<i)|(1<<j)]if i!=j else 0 for j in I]for i in I])
    A=Gamma-J;B=A.inv()
    assert all(z[i,1<<i]==0 for i in I)
    assert all(J[i,j]==s.Rational(1,100) for i in I for j in I if i!=j)
    for M in (Gamma,A):
        assert M.det()>0 and all(v>0 for v in M.inv())
        for i in I:
            assert M[i,FAVORITE[i]]>0
            assert M[i,STRONG[i]]<0 and M[i,WEAK[i]]<0
    cp=s.prod(B[STRONG[i],i]/B[i,i]for i in I)
    cm=s.prod(B[WEAK[i],i]/B[i,i]for i in I)
    assert cp==s.Rational(471132205633522740670561,1124945068785777318242881)
    assert cm==s.Rational(3804057762915868823769121,1124945068785777318242881)
    assert cp<1<cm
    # Uniform analytic exclusion of every nonempty support near the origin.
    assert all(s.expand(F[i].as_expr()+sum(Gamma[i,j]*q[j]for j in I)).subs(
        {q[j]:0 for j in I})==0 for i in I)
    assert all(F[i].coeff_monomial(q[j])==-Gamma[i,j]for i in I for j in I)
    K=max(sum(abs(v)for mon,v in f.terms()if sum(mon)>=2)for f in F)
    L=s.S.Zero
    for n in range(2,5):
        for support in itertools.combinations(I,n):
            principal=Gamma.extract(support,support)
            assert principal.det()!=0
            inverse=principal.inv()
            L=max(L,max(sum(abs(v)for v in inverse.row(i))for i in range(n)))
    assert K==s.Rational(451,20) and L==s.Rational(20,3)
    delta=Q(1,256)
    assert K*L*s.Rational(delta.numerator,delta.denominator)==s.Rational(451,768)<1
    stationary=certify(F,[Q(0)]*4,[Q(1)]*4,delta)
    assert stationary['nodes']==1309 and len(stationary['leaves'])==655
    assert stationary['depth']==40
    # Immediate Quit guarantees actual payoff >=-1. Hence true punishment
    # v_i>=-1 and native continuation m_i=v_i-1>=-2.
    assert all(z[i,m]+1>=-1 for i in I for m in range(1,16)if m>>i&1)
    sure=[]
    for owner in I:
        # Every nonsure player's H vanishes on this face. For the sure
        # owner, m=-2 maximizes its incentive to Quit over all m>=-2.
        hh=[s.Poly(s.expand((g[i]+2*H[i]).subs(q[owner],1)),*q)for i in I]
        lo=[Q(0)]*4;lo[owner]=Q(1)
        result=certify(hh,lo,[Q(1)]*4)
        sure.append(result)
    assert [x['nodes']for x in sure]==[35,41,29,39]
    # Complete 15-partition census, allowing positive constant row scales.
    quotient_records=[];invariant=[]
    expected=[-s.Rational(351,80),s.Rational(2529,400),-s.Rational(243,50),
              s.Rational(243,50),s.Rational(117,80),-s.Rational(117,80),
              -s.Rational(2529,400),s.Rational(117,80),s.Rational(117,80),
              s.Rational(117,20),-s.Rational(153,40),-s.Rational(189,80)]
    for part in partitions(list(I)):
        ts=s.symbols('t:'+str(len(part)))
        sub={q[i]:ts[j]for j,block in enumerate(part)for i in block}
        polys=[s.Poly(ff.as_expr().subs(sub),*ts)for ff in F]
        witness=None
        for block in part:
            for i,j in itertools.combinations(block,2):
                monoms=sorted(set(polys[i].monoms())|set(polys[j].monoms()),key=lambda a:(sum(a),a))
                for a,b in itertools.combinations(monoms,2):
                    minor=polys[i].coeff_monomial(a)*polys[j].coeff_monomial(b)-polys[i].coeff_monomial(b)*polys[j].coeff_monomial(a)
                    if minor:
                        witness=(i,j,a,b,minor);break
                if witness:break
            if witness:break
        if witness:
            assert witness[-1]==expected[len(quotient_records)]
            quotient_records.append({'partition':part,'rows':witness[:2],
                'monomials':witness[2:4],'minor':str(witness[-1])})
        else:
            assert all(polys[i]==polys[j]for block in part for i,j in itertools.combinations(block,2))
            M=s.Matrix([[sum(z[block[0],1<<j]for j in other if j!=block[0])
                         for other in part]for block in part])
            assert M.det()>0 and all(v>0 for v in M.inv())
            invariant.append({'partition':part,'matrix':[[str(v)for v in M.row(i)]for i in range(len(part))],
                              'determinant':str(M.det())})
    assert len(quotient_records)==12 and len(invariant)==3
    assert [r['partition']for r in invariant]==[((0,),(1,),(2,),(3,)),((0,1),(2,3)),((0,1,2,3),)]
    print('PASS: all15 quotient choices;12 nonzero minors and3 positive-inverse positive-degree matrices')
    print('PASS: strict exceptional positive-J matrix branch; Cplus<1<Cminus')
    print('PASS: origin K=451/20, L=20/3, delta=1/256; LKdelta=451/768<1')
    print('PASS: all stationary supports and cube boundaries;1309 exact nodes,655 leaves')
    print('PASS: all sure-first faces at optimistic punishment m=-2;', [x['nodes']for x in sure])
    payload={'native_table':[[str(z[i,m])for m in range(16)]for i in I],
             'K':str(K),'L':str(L),'delta':str(delta),
             'Cplus':str(cp),'Cminus':str(cm),'stationary':stationary,'sure':sure,
             'quotient_minors':quotient_records,'quotient_invariant':invariant}
    parser=argparse.ArgumentParser()
    parser.add_argument('--write-certificate')
    args=parser.parse_args()
    if args.write_certificate:
        with open(args.write_certificate,'w')as out:json.dump(payload,out,indent=2);out.write('\n')
        print('Wrote complete integer leaf certificates:',args.write_certificate)

if __name__=='__main__':main()
```

## Appendix C. General inverse-cone endpoints and strict raw guards

```python
"""Exact algebra and raw calibration for the positive-inverse cone producer.

Python 3 + SymPy. No numerical solver and no external input data are used.
The general existence argument is Brouwer plus a monotone scalar crossing;
this checker audits its symbolic endpoint identities and exact finite data.
"""
import sympy as s

I = range(4)
mate = (3, 2, 1, 0)
x = s.symbols('x0:4', positive=True)
p = s.symbols('p0:4', nonnegative=True)
c = s.symbols('c0:4', positive=True)
P = s.symbols('P0:4', real=True)
kappa = s.symbols('kappa0:4', positive=True)
Gamma = s.Matrix(4, 4, lambda i, j: 0 if i == j else
                 p[i]-c[i] if j == mate[i] else s.Symbol(f'g{i}{j}'))
Z = {(i, mask): s.Symbol(f'z{i}_{mask}') for i in I for mask in range(16)}
v = [p[i]*x[mate[i]]/(1+x[mate[i]]) for i in I]
w = [c[i]*x[mate[i]] for i in I]
T = []
for i in I:
    j, k = [a for a in I if a not in (i, mate[i])]
    Z[i, 0] = 0
    for a in I:
        Z[i, 1 << a] = Gamma[i, a]
    Z[i, (1 << i) | (1 << mate[i])] = p[i]
    Z[i, (1 << j) | (1 << k)] = P[i]
    for mask in ((1 << i) | (1 << j), (1 << i) | (1 << k),
                 (1 << i) | (1 << j) | (1 << k)):
        Z[i, mask] = kappa[i]
    T.append(c[i]*x[mate[i]]*(x[j]+x[k]+x[j]*x[k])
             +p[i]*x[mate[i]]**2/(1+x[mate[i]])-P[i]*x[j]*x[k])

def endpoints(hazards, continuation, i):
    quit_value = cont_value = 0
    for mask in range(16):
        if mask >> i & 1:
            continue
        prob = s.prod(hazards[j] if mask >> j & 1 else 1-hazards[j]
                      for j in I if j != i)
        quit_value += prob*Z[i, mask | (1 << i)]
        cont_value += prob*(Z[i, mask] if mask else continuation[i])
    return quit_value, cont_value

for active in ((0, 3), (1, 2)):
    q = [x[i]/(1+x[i]) if i in active else s.S.Zero for i in I]
    here = [v[i] if i in active else w[i] for i in I]
    nxt = [w[i] if i in active else v[i] for i in I]
    for i in I:
        Q, C = endpoints(q, nxt, i)
        if i in active:
            assert s.factor(Q-here[i]) == 0
            assert s.factor(C-here[i]) == 0
        else:
            j, k = active
            D = (1+x[j])*(1+x[k])
            assert s.factor(Q-kappa[i]*(x[j]+x[k]+x[j]*x[k])/D) == 0
            assert s.factor(D*(C-here[i])-(Gamma*s.Matrix(x))[i]+T[i]) == 0

a, b, t, vm, pp, aa, cc = s.symbols('a b t vm pp aa cc', positive=True)
assert s.expand((a+b)*(1+a)*(1+b)-(a+b+a*b)
                -(a*a+a*b+b*b+a*b*(a+b))) == 0
radial = t*aa+t*t*cc+pp*t*vm*vm/(1+t*vm)
assert s.factor(s.diff(radial, t)-(aa+2*t*cc+pp*vm*vm/(1+t*vm)**2)) == 0

# The literal 60-coordinate calibration, with original own levels all one.
base = [(0, 0, 0, 0), (1, 4, 0, 0), (4, 1, 0, 0), (1, 1, 1, 1),
        (0, 0, 1, 4), (1, 1, 1, 0), (0, 1, 1, 1), (1, 0, 0, 0),
        (0, 0, 4, 1), (1, 0, 1, 1), (1, 1, 0, 1), (0, 1, 0, 0),
        (1, 1, 1, 1), (0, 0, 0, 1), (0, 0, 1, 0), (-1, -1, -1, -1)]
z = {(i, mask): s.Integer(base[mask][i]-1) for i in I for mask in range(1, 16)}
favorite, strong, weak = (1, 0, 3, 2), (2, 3, 1, 0), (3, 2, 0, 1)
for i in I:
    z[i, 1 << i] = 0
    z[i, 1 << favorite[i]] = 3
    z[i, 1 << strong[i]] = -s.Rational(21, 10)
    z[i, 1 << weak[i]] = -s.Rational(3, 20)
    for j in I:
        if i != j:
            z[i, (1 << i) | (1 << j)] = s.Rational(1, 100)
G = s.Matrix(4, 4, lambda i, j: z[i, 1 << j])
B = s.Matrix([[3152, 5952, 4324, 2504], [5952, 3152, 2504, 4324],
              [2504, 4324, 3152, 5952], [4324, 2504, 5952, 3152]])/11949
assert G*B == s.eye(4) and all(entry > 0 for entry in B)
R = lambda a, b: max(B[a, l]/B[b, l] for l in I)
caps, passives = [], []
for i in I:
    j, k = [a for a in I if a not in (i, mate[i])]
    pi = z[i, (1 << i) | (1 << mate[i])]
    ci = pi-G[i, mate[i]]
    eta = ci*(1/R(j, mate[i])+1/R(k, mate[i]))
    kap = ci/(R(j, mate[i])+R(k, mate[i]))
    assert pi > 0 and ci > 0
    assert z[i, (1 << j) | (1 << k)] < eta
    for mask in ((1 << i) | (1 << j), (1 << i) | (1 << k),
                 (1 << i) | (1 << j) | (1 << k)):
        assert z[i, mask] < kap
    caps.append(kap)
    passives.append(eta)
    assert pi*B[i, i] > s.Rational(1, 768)
assert caps == [s.Rational(212957, 4345425)]*2+[s.Rational(13010471, 26300400)]*2
assert passives == [s.Rational(623, 3100)]*2+[s.Rational(149177, 74400)]*2

# Recipient scaling multiplies Gamma rows and cancels in every column ratio.
lam = s.symbols('lambda0:4', positive=True)
scaled_B = B*s.diag(*(1/a for a in lam))
for a in I:
    for b in I:
        for l in I:
            assert s.factor(scaled_B[a, l]/scaled_B[b, l]-B[a, l]/B[b, l]) == 0

print('PASS: all 16 generic endpoints, radial derivative, positive triple caps,')
print('      literal full60 strict calibration, inverse and all-scale cap identities')
```
