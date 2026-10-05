# A repeated solo exit pays a positive outsider collision cap

## Game, raw reward criterion, and conclusion

There are four players, independent Continue/Quit choices at every
nonabsorbed date, publicly observed past actions, and no external
correlation. First nonempty quitting coalition S pays r(S) forever;
perpetual continuation pays zero. All unspecified entries below are
arbitrary finite real numbers. The desired conclusion is one fixed
uniform-equilibrium payoff for the original table against complete
behavioral deviations.

Coalition strings abbreviate sets: 01 means {0,1}, and r_i(S)
denotes player i's coordinate of r(S). Live-stage rewards are zero.

Let a,b,c,h1,h2,h3,eta be strictly positive, with abc>1, and let
u<=1, v<1, R real. Prescribe the five complete vectors

    r(0)  = (1,-h1,-h2,-h3),
    r(1)  = (u,0,b,-1),
    r(2)  = (v,-1,0,c),
    r(3)  = (R,a,-1,0),
    r(01) = (1,eta,-h2,-h3).

Thus s=(1,0,0,0). Impose only the following six outsider bounds:

    r2(02), r2(12), r2(012) <= 0,
    r3(03) <= lambda,  r3(13), r3(013) <= 0,

where lambda>=0. Suppose there exists a real theta such that

    0 < theta < eta/h1,       lambda <= h3*theta.       (B1)

Equivalently, the potentially positive cap may be any lambda with
0<=lambda<h3*eta/h1. No assumption is made on pair-23 participant
premiums, on the pivot's participant reward at 03, or on any omitted
higher-coalition entries. Condition (B1) keeps the effective premium
defined below strictly positive; its zero boundary is not part of this
statement.

**Theorem.** Every such raw table, for every real R, has a uniform-
equilibrium payoff. The middle parameter interval has the explicit
four-phase producer below; the complementary intervals follow from
original-singleton-matrix criteria, without changing any reward.

Explicitly, a uniform-equilibrium payoff is one vector such that for
every positive accuracy some behavioral profile delivers that vector
within the accuracy and bounds every unilateral behavioral deviation
by that player's target plus the accuracy at every sufficiently large
finite horizon. The profile and horizon threshold may depend on the
accuracy; the target may not.

## A scalar selector with zero pivot pair premium

Put D=abc-1, L=ac+a+1, Y=D/(b*L), and

    A = [[0,-1,a],[b,0,-1],[-1,c,0]],
    nu = A^(-1)*(h1,h2,h3),
    eta_eff = (eta-h1*theta)/(1+theta) > 0,
    Rlow = 1+((1-u)*nu1+(1-v)*nu2)/nu3,
    Rtop = 1+ac*(1-u)+a*(1-v).

All components of nu are positive since

    A^(-1) = [[c,ac,1],[1,a,ab],[bc,1,b]]/D.

Also 0<Y<c/(c+1), since
bc*L-D*(c+1)=bc+c+1>0.

Moreover Rtop>Rlow, because

    nu3*(Rtop-Rlow)
      = (1-u)*(c*h1+h3)+(1-v)*h1 > 0.

For each y in (0,Y), define K as the unique root in

    0 < K < min(b*y/h2, (c-(c+1)*y)/h3)

of the equation

    z = (h3*K+y)/(c*(1-y)),
    w = (b*y-h2*K)/(1+b*y+(1-h2)*K),
    0 = h1*K+z-a*w*(1-z)
        +eta_eff*K*(1-(1-z)*(1-w)/(1+K)).             (B2)

Here K,y,z,w depend on y. To verify existence, uniqueness, and
continuity directly, set C=c*(1-y), E=c-(c+1)*y,
d0=1+b*y, d1=1-h2. Multiplying the last equation by
C*(d0+d1*K) gives the quadratic alpha*K^2+beta*K+gamma, where

    alpha = h1*C*d1+h3*d1-a*h2*h3
              +eta_eff*(C*d1+h3),
    beta  = h1*C*d0+h3*(d0+a*b*y)+y
              +h2*(a*E-y)+eta_eff*y*(C*b+1),
    gamma = y*(b*L*y-D).

The denominators are positive throughout the closed cap interval:
d0+d1*K>=1+K and C>0. Also beta>0 because
a*E-y=ac-L*y>=1/b on [0,Y]. The polynomial is negative at K=0
for interior y, and positive at the cap: there either w=0 or z=1,
making the right side of (B2) strictly positive. A quadratic with
positive linear coefficient has exactly one crossing from negative to
positive on this interval. Its selected root is

    K = -2*gamma/(beta+sqrt(beta^2-4*alpha*gamma)),

valid also at alpha=0. This root is continuous and tends to zero
at both endpoints. At zero, beta(0)=c*h1+h3+ac*h2=D*nu1
and gamma(y)/y tends to -D. The root formula and the child row
identities therefore give
K/y->1/nu1, z/y->nu2/nu1, w/y->nu3/nu1.

Define the pivot selector

    P(y) = 1 + [ (1-u)*y/(1-y)+(1-v)*z ]/[(1-z)*w].  (B3)

It is continuous on (0,Y), tends to Rlow at zero, and tends to
Rtop at Y. At the upper endpoint K=0 and (B2) says
z=a*w*(1-z); combined with z=y/(c*(1-y)), these give the stated
upper limit directly. Thus for every R in (Rlow,Rtop), the
intermediate value theorem supplies y with P(y)=R. No monotonicity
or unique y is claimed or needed.

The selector proof includes the zero pivot pair premium directly. It
uses u<=1 for a weak pivot floor; no strictly positive pivot premium
is presumed.

## Four exact phase values

Set

    k=K/(1+theta),  x=k/(1+k),  rho=theta*x/(1+theta*x).

Use four successive stages, repeating after nonabsorption:

    A: joint hazards x for player0 and y for player1;
    B: solo player2 with hazard z;
    C: solo player3 with hazard w;
    D: solo player0 with hazard rho.

The phases B,C,D will subsequently be diffused. Write d for the
value before D and t for the value before A. They are

    d = (1, eta_eff*K/(1+K), w/(1-w), 0),
    t = (1, eta*x,
         h2*theta*x+(1+theta*x)*w/(1-w),
         h3*theta*x).

The intervening vectors are

    V_C = ( (1-w)+R*w, (1-w)*d1+a*w, 0, 0 ),
    V_B = ( v*z+(1-z)*V_C0, (1-z)*V_C1-z, 0, c*z ).

These are exact Bellman values for every coordinate. At phase D,
d=(1-rho)*t+rho*r(0). The identity for d1 uses
eta_eff=(eta-h1*theta)/(1+theta). The identity for d2 follows from
the definition of t2; d3=0 is the purpose of the bridge.

At A, the player-0 Quit and Continue endpoints both equal 1 by (B3).
Player1's Quit endpoint is eta*x. Its Continue endpoint agrees because

    V_B1=K*(h1+eta_eff)=k*(h1+eta).

For player2, the literal passive average is

    -h2*x+(1-x)*b*y = t2.

For player3 it is

    -h3*x+(1-x)*[-y+(1-y)*c*z] = h3*theta*x = t3.

The latter equality uses K=(1+theta)*k. Thus player3's value is
positive at the undiffused joint stage but zero immediately before
the solo-0 bridge, which is exactly the value needed after phase C.

At B the solo owner2 has both endpoints zero; at C owner3 has both
endpoints zero; at D owner0 has both endpoints one. Every player at
every phase has a value at least its singleton. For the pivot this
uses V_B0=(1-u*y)/(1-y)>=1 and R>Rlow>1; the other floors follow
from the displayed positive quantities. All pure-Continue endpoints
equal the current phase value, not only its prescribed mixed average.

At the undiffused phase A the only outsider tests are players2 and3.
The three player2 caps give Q2<=0<=t2. The player3 caps give

    Q3 <= lambda*x*(1-y) <= h3*theta*x = t3.           (B4)

This is the genuine new accounting step: r3(03) can be strictly
positive even when both other player3 caps are zero. It is paid by a
continuation value, not by a cancellation with a negative collision
reward. All active endpoints and all four full-response tests at A
have now been checked.

## Diffusion, a fixed target, and complete behavioral deviations

Replace each solo stage of rate q in {z,w,rho} by n stages of rate
q_n=1-(1-q)^(1/n). Keep A unchanged. The product survival over each
block remains 1-q, so t is the same exact prescribed payoff for all n.
Within a solo block of owner j, values are convex interpolants between
its two endpoint vectors; the j coordinate is identically s_j.
Thus all singleton floors, prescribed-policy equalities, and pure-
Continue equalities hold at every refined row.

Let

    Cjoin=max(0, r_i({i,j})-s_i : j in {0,2,3}, i!=j),
    e_n=Cjoin*max(z_n,w_n,rho_n).

Then e_n tends to zero. At any refined row the forced-Quit endpoint
of a nonowner is at most s_i+Cjoin*q_n, hence at most V_i+e_n.
The owner is exact. Together with (B4), EVERY row's Quit endpoint is
at most its value plus e_n, and every Continue endpoint is exactly its
value. Adding the same e_n to each continuation value therefore gives
a supersolution for both unilateral actions. The error is charged once
at eventual quitting, not once per date or period.

The displayed periodic Bellman solution is the actual terminal value:
prescribed survival contracts each period, so iteration of the bounded
equations leaves zero tail remainder. In particular its phase values
are bounded in magnitude by any bound M on terminal rewards.

This proves unrestricted behavioral safety directly: after any history
that has not absorbed, the public date identifies the current row and
the opponents still use their prescribed independent coins. Their
probability of all continuing over one full period is a fixed rho_i<1
for every deviating player i, since each of the other three players
has positive total hazard. Hence absorption under any complete
behavioral deviation is almost sure, uniformly in the deviator's
stopping rule; bounded supersolution remainders vanish. Its terminal
payoff is at most t_i+e_n. The prescribed profile delivers exactly t.

For a direct finite-horizon bound, put m_n=1+3n and
Ctime=max_i m_n/(1-rho_i). Pre-sample the opponents' independent
coins. Under any deviation actual absorption occurs no later than
the first prescribed opponent quit, whose expected date is at most
Ctime (with the harmless usual date-index adjustment). With M bounding
all terminal payoffs, terminal versus N-stage-average expected payoff
differs by at most 2*M*Ctime/N, uniformly over the deviator. Thus

    regret_N <= e_n+4*M*Ctime/N,
    |prescribed average_N-t| <= 2*M*Ctime/N.

Choose n for the requested accuracy, then one horizon threshold for
all larger N. The target t is fixed before that choice. This is also
exactly the quit-error/Continue-equality hypothesis of
`QuittingInfinitePathQuitErrorCertificate` and
`isUniformEquilibriumPayoff_of_arbitrarily_small_infinitePath_quitError`
in `UniformEquilibrium/Quitting/Paths/InfinitePathSupersolution.lean`.
The direct argument shows why no bounded-controller or finite-number-
of-periods restriction on the deviator is being used.

## Original-table exits for all other real R

The only data used by these exits are the four prescribed singleton
vectors, so the bridge parameters and arbitrary unused entries do not
alter them. With row index the payoff receiver, the centered matrix is

    Gamma = [[0,u-1,v-1,R-1],
             [-h1,0,-1,a],[-h2,b,0,-1],[-h3,-1,c,0]].

For t>0, every solution of the child complementarity problem
Az>=t*h, z>=0, z_i(Az-t*h)_i=0 has every coordinate positive:
if one is zero, the next row of A is nonpositive, contradicting its
strictly positive required right side. Hence z=t*nu uniquely. At
t=0 a zero coordinate similarly forces all to be zero; an all-positive
solution would satisfy Az=0 and is impossible. The child is therefore
R0, meaning its homogeneous complementarity problem has only zero.

Let b0=(u-1,v-1,R-1). Its product with nu is
b0*nu=nu3*(R-Rlow). A nonzero full homogeneous solution would
have a positive pivot h, child h*nu, and zero pivot residual, forcing
R=Rlow. Thus Gamma is R0 for R different from Rlow. At equality,
(1,nu) is a nonzero homogeneous solution, and the Fin4 no-UE R0
criterion gives uniform-payoff existence.

For R<Rlow put delta=nu3*(Rlow-R)>0 and choose q0>delta.
At offset (q0,-h1,-h2,-h3), a pivot variable h forces child
(1+h)*nu and pivot residual q0-delta*(1+h). The only two
complementarity roots have h=0 and h=q0/delta-1. The former
has positive inactive residual q0-delta and active determinant D.
The latter has all coordinates positive and determinant
det(Gamma)=D*(b0*nu)=-D*delta. The nonsingular degree-sum
criterion therefore gives degree +1-1=0, whereas no UE would require
degree one. This proves existence for R<Rlow.

For R>=Rtop the child A has nonnegative inverse, and its passive
pivot weights are

    [bc*(R-T1), R-T2, b*(R-T3)]/D,
    T1=1+[c*(1-u)+(1-v)]/(bc),
    T2=Rtop,
    T3=1+[(1-u)+ab*(1-v)]/b.

Here T2>=T3>T1 because u<=1 and v<1. The weights are nonnegative,
including equality R=Rtop. The existing original-table semantic inputs
for these exits are
`exists_uniformEquilibriumPayoff_of_r0Degree_ne_one` in
`UniformEquilibrium/Quitting/Classification/LCP/SingletonDegreeCriterion.lean`,
`finFour_singleton_r0Degree_eq_one_of_no_uniformPayoff` in
`UniformEquilibrium/Diagnostics/Quitting/FinFourSingletonDegreeCriterion.lean`,
and `exists_uniformEquilibriumPayoff_of_raw_nonnegativeInverse_triple` in
`UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/RawPassiveRowInverseCriterion.lean`.
The degree calculation uses `exists_finset_r0Degree_eq_sum_sign_det`
in `MathUE/LinearProgramming/R0DegreeSum.lean`. None of these inputs
adds a condition on the unspecified nonsingleton entries.

The Lean handoff is the raw finite-table predicate above followed by
one all-real-R uniform-payoff theorem. On the open middle interval,
the scalar selector produces positive rates x,y,z,w,rho, the fixed
four phase vectors, and their exact policy/Continue and joint-row Quit
bounds. Solo refinement then supplies profiles with the same target,
vanishing common Quit error, and geometric opponent tails, consumed
by the named infinite-path theorem or the direct horizon proof. The
two closed outer branches use the original-table matrix criteria just
listed. No additional selector or strategic realization is assumed.

## Exact full-core fixture

Take a=b=c=2, h1=h2=h3=1, u=v=0, eta=31/11,
lambda=theta=1/2, R=347/92. Then eta_eff=17/11 and

    K=1/10, y=1/4, z=7/30, w=4/15,
    x=1/16, rho=1/33.

The four value vectors are exactly

    t   = (1,31/176,13/32,1/32),
    V_B = (4/3,14/55,0,7/15),
    V_C = (40/23,7/11,0,0),
    d   = (1,17/121,4/11,0).

The complete fifteen-row table is:

| S | r(S) |
|---|---|
| 0 | (1,-1,-1,-1) |
| 1 | (0,0,2,-1) |
| 2 | (0,-1,0,2) |
| 3 | (347/92,2,-1,0) |
| 01 | (1,31/11,-1,-1) |
| 02 | (1,-1,0,-1) |
| 03 | (2,-1,-1,1/2) |
| 12 | (0,0,0,1) |
| 13 | (347/92,0,1,0) |
| 23 | (347/92,1,1/2,1/2) |
| 012 | (1,0,0,-1) |
| 013 | (1,0,-1,0) |
| 023 | (1,-1,0,0) |
| 123 | (347/92,0,0,0) |
| 0123 | (1,0,0,0) |

All sixteen policy identities and all sixteen pure-Continue identities
hold exactly. At A the endpoint pairs are
(1,1), (31/176,31/176), (13/32,0), (1/32,3/128), so
outsider3 is strictly safe. In the unrefined profile,
player2 has a positive Quit gain 2/15 at C and player3 has gain 1/66
at D. Thus diffusion is genuinely required for this completion; those
gains are not being discarded.

Call a nonempty support a premium trap if every member has a strictly
positive participant premium on some coalition contained in that support.
The greatest premium core is the union of all such traps. Here the
complete positive-premium trap list is 03,013,23,023,0123. The
greatest premium core is all four players. The only common member of
all traps is 3, and player3 strictly prefers joining 0:
r3(03)=1/2>r3(0)=-1. Consequently neither the core-at-most-two class
nor a criterion requiring one common weak trap leaver admits this table.
For the coalitions in the table's order, respective strictly improving
players are 1,0,0,2,2,1,0,0,1,3,3,0,0,1,0. These are immediate
joins or withdrawals from nonsingleton coalitions, so no pure quitting
coalition is an equilibrium. A construction requiring r3(03)<=0
fails that cap; selecting pair03 instead also fails the pivot comparison
r0(03)>=r0(3).

## Bounded source separation for the full-core fixture

A criterion requiring two of a pivot's passive singleton rewards to
be at least its own singleton cannot hold here. For pivot0 only
r0(3)=347/92 exceeds one, while r0(1)=r0(2)=0. Each other
player likewise has only one nonnegative centered off-diagonal singleton
entry. Thus no relabeling meets that necessary two-high-singleton
condition. This is a comparison with that precise raw hypothesis,
not with all possible phase laws.

Its centered singleton matrix is

    Gamma=[[0,-1,-1,255/92],
           [-1,0,-1,2],[-1,2,0,-1],[-1,-1,2,0]].

The 123 child has positive inverse A^(-1) and uniquely solves
Az>=t*1, z>=0, z_i(Az-t*1)_i=0 by z=t*1 for t>0;
its homogeneous problem has only zero. Therefore the full matrix is
R0: a positive homogeneous pivot h would force child h*1 and
pivot residual (71/92)*h>0. At offset (1,-1,-1,-1), the unique
root is (0,1,1,1), its inactive residual is 163/92, and the active
determinant is 7. Its degree is +1. The only nonnegative-inverse
triple is 123, whose passive row is

    (186/161,-297/644,25/322).

The other triples have negative inverse entries: -2 for 012,
-255/439 for 013, and -92/301 for 023. The full inverse has
entry -744/497 in row0,column1. No pair has two positive
off-diagonal entries. Principal02 is R0 but non-Q, by its matrix
[[0,-1],[-1,0]] and the infeasible offset (-1,-1).

For response invariance, singleton block-row sums must agree within
each target block. The following thirteen witnesses eliminate every
nondiscrete partition except 0|123:

| Partition | Rows in one target block | Source block | Unequal sums |
|---|---|---|---|
| 01 / 2 / 3 | 0,1 | 3 | 255/92,2 |
| 1 / 02 / 3 | 0,2 | 1 | -1,2 |
| 1 / 2 / 03 | 0,3 | 2 | -1,2 |
| 0 / 12 / 3 | 1,2 | 12 | -1,2 |
| 012 / 3 | 0,2 | 012 | -2,1 |
| 12 / 03 | 1,2 | 12 | -1,2 |
| 0 / 2 / 13 | 1,3 | 2 | -1,2 |
| 02 / 13 | 0,2 | 13 | 163/92,1 |
| 2 / 013 | 0,3 | 2 | -1,2 |
| 0 / 1 / 23 | 2,3 | 1 | 2,-1 |
| 01 / 23 | 0,1 | 23 | 163/92,1 |
| 1 / 023 | 0,2 | 1 | -1,2 |
| 0123 | 0,1 | 0123 | 71/92,0 |

The remaining partition fails at
the actual root (t,0,0,0), where the three child response residuals
are t+(31/11)*t^2, t, and t+t^2/2. These are unequal for t>0.
Thus the full response-quotient hypothesis also fails. The first-order
necessary condition is
`quittingSingletonBlockRowSum_eq_of_responseInvariant` in
`UniformEquilibrium/Quitting/Stationary/ResponseInvariantQuotient.lean`.

There are exact zero-regret/positive-outside-gain witnesses for thirteen
of the fourteen proper children. For singletons use their sure exit.
For children01,02,012, let every child member quit surely. For
03,13,013 use sure3; for12 use sure1; for23 use sure2.
Every chosen child profile is exact terminal Nash, and a missing
nonpivot currently receiving -1 can join for at least zero. A participant
avoiding a lone sure exit faces opponents at Never and can subsequently
receive at most its singleton, so these are complete behavioral checks.

For child023, use one date with hazards

    (q0,q2,q3)=(3/5,1,92/347),

then Never. The endpoint pairs for its players are exactly

    (1,1), (-245/347,92/1735), (1/5,1/5).

The profile absorbs surely. Player2's only possible post-deviation
survival leaves opponents at Never and has maximal continuation zero,
already included in the displayed Continue value. Hence these are
full behavioral comparisons. Omitted player1 has Continue payoff
-1367/1735 and Quit payoff zero.

An unrefined child123 cycle of hazards1/2 is not exact: at its
player3 phase, player2 can profitably join. Instead, take the child
cycle of aggregate hazards 1/2 in order1,2,3,
and refine EACH solo phase into n equal microhazards

    alpha_n=1-2^(-1/n).

The three child phase vectors remain (0,1,0),(0,0,1),(1,0,0).
All their refined values are nonnegative, pure-Continue is exact, and
the only positive pair surpluses are the two 1/2 values at23. The
standard single-error supersolution therefore bounds every child's
full terminal regret by alpha_n/2. Prescribed joint Never has mass
zero. The quiet pivot's payoff is fixed at R/7=347/644, since
refinement does not change any aggregate singleton-exit probability.
Immediate Quit at the first microstage of player1 pays exactly one:
r0(0)=r0(01)=1. Its gain is thus the fixed 297/644 for EVERY n.

This limiting witness is sufficient to exclude universal debt bounds.
Indeed, any finite nonnegative weight vector would bound that fixed
outside gain by at most (sum weights)*alpha_n/2, plus a zero
joint-Never term, which tends to zero. The exact source criterion is
`withdrawalFutureJoin_quietLift_outsideDebt_le_add_neverExcess` in
`UniformEquilibrium/Quitting/Classification/QuietExtension/WithdrawalFutureJoinDebt.lean`.
Its quantifier is over EVERY child profile and its debt weights and
Never coefficient are fixed by the reward certificate. Consequently,
for each of the fourteen proper children there is an omitted player
for whom no bound of the following form holds for every child profile:
that omitted player's terminal
gain is at most a fixed nonnegative weighted sum of the children's
terminal deviation gains, plus a fixed nonnegative multiple of their
joint-Never probability. An exact child equilibrium is convenient but
not necessary for this contradiction. This excludes such universal
quiet-debt bounds, not every possible selected-child construction.

The result is ordinary mathematical evidence with explicit existing
semantic inputs. No Lean implementation of this new raw criterion is
claimed. It treats the displayed four-player class, not arbitrary
quitting games or every possible periodic architecture.
