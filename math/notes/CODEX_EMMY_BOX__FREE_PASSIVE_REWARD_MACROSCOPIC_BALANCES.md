# A free passive reward and four macroscopic stationary balances

Status: COMPLETE ORDINARY PROOF DRAFT, not independently reviewed and not
Lean checked. This is an actual raw-table producer with a genuinely free
unbounded coordinate. It does not claim a universal normal form for arbitrary
quitting games. Relevant whole-source admission is pending; an exact
stationary construction alone does not establish new reward-class coverage.

The question is whether two sufficiently negative passive pair rewards
permit a third passive pair reward to be completely arbitrary NONNEGATIVE,
without requiring it to be bounded or to have a prescribed asymptotic rate.
The proof below answers this for an explicit open region of the other raw
coordinates. Both negative magnitudes vary independently. Four exact scales
are required; uniformity at one fixed ratio does not answer the question.

## 1. Raw data and theorem

There are four players0,1,2,3. A nonempty quitter set S absorbs at finite
reward r(S). Continue dates and perpetual Never pay0. Each player uses its
own private randomization, independent of the others. A unilateral deviation
replaces its ENTIRE behavioral strategy, including every finite deadline,
Never and all independent mixtures of these clocks. All conclusions concern
expected terminal payoffs and the usual uniform finite-horizon averages.

The singleton center is

    r(0)=(10,9,8,13),    r(1)=(12,10,17,7),
    r(2)=(4,14,10,17),   r(3)=(7,14,4,10).

The nonsingleton center, with THREE coordinates omitted for now, is

    r(01)=(-1,40,1,*),     r(12)=(1,-1,40,1),
    r(23)=(1,1,-1,40),    r(03)=(40,1,1,-1),
    r(02)=(-1,*,-1,1),    r(13)=(1,-1,*,-1).

Every triple pays-1 to its members and1 to its absent player. The grand row
is(-10,-11,-12,-13). There are57 specified bounded center coordinates. The
three omitted coordinates are PASSIVE and have actual values

    r1(02)=-M1+e1,
    r2(13)=-M2+e2,
    r3(01)= A+e3.                                      (1)

**Theorem draft.** There exists eta>0 such that for EVERY finite R>=0 there
is N_R with the following property. For ALL independent magnitudes
M1,M2>N_R, EVERY A>=0, EVERY |e1|,|e2|,|e3|<=R, and EVERY completion whose
other57 coordinates are within eta of their specified centers, the actual
game has an all-interior stationary terminal Nash equilibrium against ALL
complete behavioral replacements. Its SAME stationary profile delivers its
actual fixed terminal payoff as a uniform-equilibrium payoff over all
sufficiently long finite horizons.

There is NO upper bound on A, NO requirement that A/M2 or A/(M1*M2)
converge, and NO bound on the ratio M1/M2. The equilibrium profile can depend
on the table. Its payoff target is fixed before accuracy and horizon are
chosen. The horizon threshold need not be uniform over these different games.
No root, continuation vector, degree, inverse sign or strategic witness is
supplied as a hypothesis.

## 2. Literal stationary residual and complete consumer

For independent stationary hazards q in(0,1)^4, let B be the opponent quitter
set at one live date and put

    alpha_i=product_(j!=i)(1-q_j),
    Q_i=E[r_i(B union{i})],
    W_i=E[r_i(B)*1_(B nonempty)],
    H_i=(1-alpha_i)*Q_i-W_i.                            (2)

Each selected entry in(1) appears ONLY in the passive stopping term-W_i.
Their respective exact large contributions are

    H1: +M1*q0*q2*(1-q3),
    H2: +M2*q1*q3*(1-q0),
    H3: -A*q0*q1*(1-q2).                               (3)

Each chart below cancels these coefficients against the rare probabilities
before taking a limit. This is not an approximation of the full cap by a
one-stage best reply.

At an actual zero H=0 with all hazards interior, set

    V_i=Q_i=W_i/(1-alpha_i).

The actual value satisfies the absorbing stationary recursion and equals V.
Every finite deadline h earns

    W_i*(1-alpha_i^h)/(1-alpha_i)+alpha_i^h*Q_i=V_i.

Never also earns V_i, since opponents absorb geometrically. A complete
private behavioral replacement on the unique live public history is a
mixture of such deadlines and Never, and therefore cannot improve V_i.
Thus H=0 is FULL terminal Nash, not only stationary Nash.

For a fixed actual table let C bound its terminal reward magnitudes. Under
EVERY replacement of player i, absorption occurs no later than the fixed
opponents' geometric first-quit time, of mean1/(1-alpha_i). Terminal and
n-date average payoffs differ by at most2C/[n*(1-alpha_i)], uniformly in the
entire replacement class. This proves SAME-profile uniform equilibrium with
target V. Arbitrary signs of the finite rewards or V cause no exception.

The inspected actual consumers are
`isZeroAsymptoticNash_stationary_of_fixedPoint_endpointNash_contracts` and
`isUniformEquilibriumPayoff_of_stationaryEndpointCertificate_contracts` in
`UniformEquilibrium/Quitting/Stationary/EndpointCompiler.lean`.
No new raw producer has been implemented in Lean here.

## 3. First chart: A is comparable to or smaller than M2

Put t1=1/M1, t2=1/M2 and a=A/M2. Use

    q=(x,t2*y,c,1-t1*z).                               (4)

After cancellation of(3), H is polynomial in t1,t2,x,y,c,z,a. At the exact
bounded center its limit as(t1,t2) tends to(0,0) is

    F0=33-35*c,
    F1=x*c*(z-10)-2-13*(1-x)*(1-c),
    F2=-5+3*x+y*(1-x),
    F3=(1-(1-x)*(1-c))*(10+30*c-x*(11+30*c))
            -(13*x+17*c-29*x*c)-a*x*y*(1-c).            (5)

The first three equations give

    c=33/35,    y=(5-3*x)/(1-x),
    z=(304*x+96)/(33*x).

For0<x<1 these y,z are positive. The last equation becomes

    a=a(x)=(1-x)*(4917-5025*x-550*x^2)
                         /[14*x*(5-3*x)].              (6)

Let x_star be the unique root in(0,1) of4917-5025*x-550*x^2. On(0,x_star)
both this quadratic and(1-x)/[x*(5-3*x)] are positive and strictly
decreasing, the latter with derivative

    -[3*(x-1)^2+2]/[x^2*(5-3*x)^2]<0.

Hence a(x) is strictly decreasing from infinity to0, with strictly negative
derivative, including its derivative at x_star. Every a>=0 supplies a
unique positive limiting root, taking x(0)=x_star. In unknown order(c,z,y,x)
the first three pivots are-35,xc,1-x. The fourth reduced pivot is

    x*y*(1-c)*a'(x)<0.

Thus for EACH finite L the compact interval a in[0,L] gives uniformly
nonsingular limiting roots. Polynomial IFT supplies actual interior zeros
for t1,t2 sufficiently small, uniformly in that interval and in a small
bounded-coordinate neighborhood. Both negative magnitudes are independent;
only t1 and t2 must be small.

## 4. Second chart: the overlap between the two large scales

For A>0 put

    mu=M2/A,       nu=A/(M1*M2),       t2=1/M2.

Thus mu*nu=1/M1. Use

    q=(mu*X,t2*y,c,1-nu*z).                            (7)

The exact three pole terms(3) are

    X*c*z,    y*(1-nu*z)*(1-mu*X),    -X*y*(1-c).

No negative power remains. At(mu,nu,t2)=(0,0,0), the four limiting equations
are

    33-35*c=0,
    c*X*z+13*c-15=0,
    y-5=0,
    c*(30*c-7)-X*y*(1-c)=0.                            (8)

They have the exact positive root

    c=33/35,    y=5,    X=4917/70,    z=2240/54087.    (9)

Order the equations as0,2,3,1 and unknowns as c,y,X,z. Successive pivots are
-35,1,-y*(1-c),X*c, all nonzero. Polynomial IFT gives an actual interior
zero whenever mu,nu,t2 are sufficiently small and POSITIVE. The actual
relation mu*nu=1/M1 is respected; it is not a constraint needed to invent
independent clock correlation. In particular this chart covers the whole
overlap M2 much smaller than A much smaller than M1*M2, once fixed small
parameter bounds are chosen. It supplies a new scale, rather than claiming
that the first chart is uniform as a tends to infinity.

## 5. Third chart: A is comparable to M1*M2

Put kappa=A/(M1*M2)>0 and use

    q=(t1*X,t2*y,c,d).                                 (10)

For finite kappa, exact pole cancellation leaves a polynomial in t1,t2.
Let alpha=(1-c)*(1-d), and define

    G(c,d)=(1-alpha)*(10-11*c+30*d*(1-c))
                         -4*c-7*d+10*c*d,
    J(c,d)=(1-alpha)*(11*alpha-1)-14*c-14*d+27*c*d,
    T(c)=c*(30*c-7).

The four limiting equations are

    G(c,d)=0,
    J(c,d)+X*c*(1-d)=0,
    d*(6-11*d+y)=0,
    T(c)-kappa*X*y*(1-c)=0.                            (11)

### 5.1 Exact whole-interval barriers

Let d0=6/11. For every d in[d0,1], the quadratic in c has endpoint signs

    G(0,d)=3*d*(10*d+1)>0,
    G(1,d)=3*d-5<0.

It therefore has exactly one simple root c(d) in(0,1), with G_c<0. This
root is smooth in d, including both endpoints. The exact interior test

    G(7/30,d)=(15870*d^2+5759*d+721)/900>0

shows c(d)>7/30, hence T(c(d))>0.

Also J(c,d)<0 for EVERY c in[0,1] and d in[d0,1], not only at a selected
root. Indeed alpha<=1-d<=5/11. The function f(u)=(1-u)*(11u-1) is increasing
on[0,5/11], whereas14*c+14*d-27*c*d>=14-13*d. Consequently

    J(c,d)<=d*(10-11*d)-(14-13*d)
             =-11*d^2+23*d-14<=-2,

the last polynomial being increasing through this d interval. Set

    X(d)=-J(c(d),d)/[c(d)*(1-d)]>0,
    y(d)=11*d-6>0,             d in(d0,1).             (12)

The first three equations in(11) are now solved. As d decreases to d0,
y tends to0 and X has a finite positive limit. As d increases to1,
X tends to infinity, y tends to5, and c tends to33/35.

### 5.2 Scalar IVT with a produced partial Jacobian

The last equation is

    kappa=K(d)=T(c(d))/[X(d)*y(d)*(1-c(d))].            (13)

This is positive and continuous on(d0,1), tends to infinity at d0, and
tends to0 at1. Thus every kappa>0 has a limiting solution. A nonzero full
Jacobian of that chosen solution is NOT assumed or needed.

For a compact interval kappa in[l,L],0<l<L, choose d_minus close enough to
d0 that the last residual in(11) is POSITIVE for all such kappa. Choose
d_plus close enough to1 that it is NEGATIVE for all such kappa. Keep
d0<d_minus<d_plus<1. On this compact d interval, the partial Jacobian of
the first three equations in unknowns(c,X,y) has pivots

    G_c(c(d),d)<0,    c(d)*(1-d)>0,    d>0.

Compact-parameter partial IFT gives continuous actual solutions c,X,y for
small t1,t2 and small bounded-coordinate changes, uniformly in d and
kappa. The remaining scalar residual retains its two strict endpoint
signs. IVT therefore supplies an ACTUAL zero. All four hazards in(10)
are interior. This construction covers every compact positive kappa range
without assuming a selected angular root, global uniqueness or a supplied
strategic continuation.

## 6. Fourth chart: A can be arbitrarily larger than M1*M2

Put k=M1*M2/A and use

    q=(t1*X,t2*k*Y,c,d).                               (14)

After cancellation the pole terms are

    X*c*(1-d),    k*Y*d*(1-t1*X),    -X*Y*(1-c).

At(t1,t2,k)=(0,0,0), the limit is

    G(c,d)=0,
    J(c,d)+X*c*(1-d)=0,
    d*(6-11*d)=0,
    T(c)-X*Y*(1-c)=0.                                 (15)

Take d=d0=6/11. The unique root c0=c(d0) is equivalently the positive root
of1505*c0^2+180*c0-1278=0, namely

    c0=-18/301+3*sqrt(214610)/1505.

Define

    X0=-J(c0,d0)/[c0*(1-d0)]>0,
    Y0=T(c0)/[X0*(1-c0)]>0.

The strict signs were proved on the WHOLE interval in Section5.1, so no
decimal root is being used. Order equations2,0,1,3 and unknowns d,c,X,Y.
Their pivots are-6,G_c,c0*(1-d0),-X0*(1-c0), all nonzero. Polynomial IFT
therefore supplies actual interior roots for small positive t1,t2,k,
including arbitrarily small k>0. The rare clock1 has hazard t2*k*Y=M1*Y/A;
it is positive for each finite input A. This is not a claim that the
infinite-reward boundary itself is a valid game or that q1 remains bounded
away from0.

## 7. Whole positive half-line and uniform raw-data quantifiers

Choose a fixed delta>0 small enough that the transition chart works for
mu,nu<=delta. Choose a fixed L>1 large enough that the fourth chart works
for k<=1/L. The four charts then cover EVERY A>=0:

1. If A/M2<=1/delta, use the first chart on that compact a interval.
2. Otherwise mu<delta. If A/(M1*M2)<=delta, use the transition chart.
3. If delta<=A/(M1*M2)<=L, use the third chart on that compact interval.
4. If A/(M1*M2)>=L, use the fourth chart.

At overlap boundaries use smaller parameter bounds than those from IFT,
so non-strict case splits cause no issue. There is no gap between regimes,
and no limit-order hypothesis on the actual free coordinate A.

All limiting roots in the first, second and fourth charts have produced
nonsingular Jacobians. The third has produced uniform partial inverses and
two strict scalar signs. Small changes in all57 bounded coordinates preserve
these facts; taking the minimum of the four permitted radii gives ONE eta.
In the first and third charts the remaining ratio parameter ranges over a
fixed compact set. In the second and fourth charts the new small parameters
are bounded by the chosen chart radii. This supplies compact branch controls
in EVERY case, despite the unbounded original A and M1/M2.

The bounded residuals in(1) do not alter any limiting equation. Their exact
terms in H have coefficients

    -e1*q0*q2*(1-q3),
    -e2*q1*q3*(1-q0),
    -e3*q0*q1*(1-q2).

On each fixed chart neighborhood their C1 sizes are bounded by a chart
constant times R/min(M1,M2). In the transition chart use the ACTUAL relation
mu*nu=1/M1 for the first term, and t2=1/M2 for the other two. In the fourth
chart k is bounded, so t2*k is also small. In the first and third charts
all other chart coordinates are uniformly bounded. Thus the chart radii
and eta can be fixed BEFORE R; choosing N_R large makes these residual
perturbations small in all four charts. The same choice makes t1,t2 small
enough for every case and every constructed hazard legal.

This proves the stated order exists eta, for every R exists N_R, for ALL
M1,M2>N_R and ALL A>=0. Choosing a different chart may give a different
equilibrium branch; continuity of a global Nash selection is not asserted
or needed. The consumer in Section2 completes terminal Nash and the fixed
uniform payoff for each actual game.

## 8. Exact boundary tests, class scope, and requested check

At A/M2=2267/49 the first limiting branch has exact data

    x=1/2, c=33/35, y=7, z=496/33,

with full limiting Jacobian determinant2933667/6860 in order(c,z,y,x).
At the transition corner all four limiting equations vanish EXACTLY at(9).
At the critical lower endpoint d0 the quadratic in c is the displayed
1505*c^2+180*c-1278; its positive root gives the fourth chart. At d=1,
the critical branch tends to c=33/35, y=5 and X tends to infinity; this
is precisely why uniformity in the third chart alone would be false.

At the EXACT bounded center there is no root Nash with ANY sure quitter,
for ANY free-player probabilities or continuation vector, provided the
two selected negative coordinates are negative and the third is nonnegative.
First force the sure owner's opposite player to Continue: neither negative
opposite pair can be a possible passive opponent coalition for it. The
positive extra passive reward only strengthens Continue. Then both negative
pairs are impossible. All nonsuccessors strictly Continue, the successor
surely Joins for40 rather than a singleton<=17, and the owner withdraws
from-1 to a singleton>=4. This is a whole-selection test, not pure-profile
enumeration. With bounded e it applies once M1,M2 are large and A+e3>=0;
the actual equilibrium theorem itself does not require that last sign when
e3 is negative and bounded.

The construction is an unbounded raw-region theorem, not a theorem that every
canonical positive-minimum source can be changed into this region. No such
adapter is proved. The raw source comparisons for the earlier balanced
three-pole center are being independently checked separately. This note
does not infer novelty from failure of one stationary template, and does
not claim that unknown pointwise thick thresholds or neighborhoods have
been exhaustively excluded.

Concrete requested independent check: falsify the exact pole cancellations
in the FOUR charts, the whole-interval G/J/T signs, the partial-IFT/IVT
critical regime, the regime cover for arbitrary independent M1,M2 and
unbounded A, and especially the order exists eta before R with the actual
transition relation mu*nu=1/M1. Reuse the complete deadline/Never consumer
only after checking all produced hazards stay interior. No export is
requested before soundness and relevant whole-source admission are resolved.
