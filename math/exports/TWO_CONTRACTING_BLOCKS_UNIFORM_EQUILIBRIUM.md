# Two contracting blocks produce uniform equilibria

The Fin4 conjecture remains open. The results below exclude explicit classes
of original four-player reward tables. The constructive branches give actual
finite periodic approximate equilibria with one fixed payoff target; known
same-table matrix exits handle complementary parameter cases. They include an explicit
quantitative reward box, a complete signed singleton chamber with computable
small-premium thresholds, a complementary pair-contraction regime, and a uniform rectangle of
independent positive premium scales with every ratio allowed.
The proofs are ordinary mathematics, not new Lean-checked declarations.
No equilibrium, continuation, invariant set or strategic selector is an input.

The quantitative theorem is retained because its explicit constants exceed
the conservative thresholds of the general signed-chamber construction.
The calibration also proves exact failures of the named earlier raw criteria.
The rectangle theorem keeps its stated additive passive rewards and
homogeneous rows1,2,3; its row0 participant rewards vary independently
under upper bounds. All rewards below are finite. Equation labels distinguish
the constructions.

## Quantitative fixed-matrix theorem and exact calibration

### Explicit quantitative theorem

There are four players I={0,1,2,3}. At each live date each independently
chooses Continue or Quit. The first nonempty quitting coalition A absorbs
at the finite reward vector r(A); live and AllNever rewards are zero.
Before absorption the only public history is repeated Continue by everyone;
there is no public correlation device. Every unilateral behavioral replacement
is allowed. On this unique live path, a behavioral stopping rule is equivalent
to a private law on finite dates and Never. Such laws are independent across
players, and arbitrary private mixtures are allowed. Set

    ell_i=r_i({i}), Z_i(A)=r_i(A)-ell_i for nonempty A.

The own levels ell_i are arbitrary real numbers. Assume the literal native
singleton matrix is

    Gamma = [ 0  3 -1  3;
              2  0  1 -3;
              2 -2  0 -1;
             -1 -2  1  0 ].                            (Q1)

Require the following SEVEN passive nonsingleton entries only:

    Z0(12)=2, Z0(13)=6, Z0(23)=2, Z0(123)=5,
    Z1(23)=-2, Z2(13)=-3, Z3(12)=-1.                  (Q2)

Together with (Q1), these mean that passive endpoints against a root on
123 are Gamma*q. All other passive nonsingleton entries are arbitrary.

Choose finite raw parameters

    0<b<=1/4, 0<=eta<=min(1/2000,b/250).                 (Q3)

The participant conditions are exactly:

| Row | Native entries | Allowed values |
| --- | --- | --- |
| 0 | Z0(02) | alpha<=3 |
| 0 | Z0(01), Z0(03), Z0(012), Z0(013), Z0(023) | each <=3 |
| 0 | Z0(0123) | <=10 |
| 1 | Z1(12), Z1(13), Z1(123) | independently in [0,eta] |
| 1 | Z1(01) | <=2 |
| 2 | Z2(12), Z2(23), Z2(123) | independently in [b,1/4] |
| 2 | Z2(02) | <=2 |
| 3 | Z3(13), Z3(23), Z3(123) | independently in [0,eta] |
| 3 | Z3(03) | <=1/4 |

Every unlisted nonsingleton entry is arbitrary finite data, including the
three grand rewards Z1(0123), Z2(0123), Z3(0123). One-sided bounds above
have no implicit lower bound. No continuation, profile, equilibrium,
root selector or other strategic object is supplied.

**Theorem.** Every such original table has a uniform-equilibrium payoff.
The proof produces periodic approximate terminal Nash profiles with one
fixed limiting payoff. It does not assert exact finite-period Nash.

Here a uniform-equilibrium payoff v means that for every positive error
there are one behavioral profile and a finite horizon threshold such that,
above that threshold, its expected average payoff is within that error of v
and every unilateral behavioral improvement is at most that error. The same
v must work before the error, profile and threshold are chosen.

### Strategic inputs and definitions

Only the finite reward tests above are inputs. The scalar return below
produces its root from raw data by the intermediate value theorem. The two
backward operations then produce every finite block and their limit
annotations; the final strategies execute finite truncations only. Thus no
strategic witness remains assumed, including at a recursive step.

For native rewards, a full cap is the supremum of a player's terminal payoff
over all unilateral complete stopping-law replacements; debt is cap minus
prescribed payoff. A product root is Nash against a displayed continuation
when each positive Quit probability uses a maximal Quit endpoint and each
positive Continue probability uses a maximal Continue endpoint. The proof
checks both endpoints, retaining arbitrary future responses at the two
finite approximation seams.

Write

    a12=Z1(12), d1=Z1(13), f1=Z1(123),
    d3=Z3(13), a32=Z3(23), f3=Z3(123),
    b1=Z2(12), b3=Z2(23), b13=Z2(123),
    Q2(y,w)=b1*y*(1-w)+b3*w*(1-y)+b13*y*w.

For D=y+w-yw, the raw bounds imply

    bD<=Q2(y,w)<=D/4.                                  (Q4)

### The contracting triple block

At continuation (p,v1,t,v3), suppose

    2/3<=p<=1, 0<=t<=1/10,
    0<=v1,v3<=(4eta/b)t.                               (Q5)

For z in [0,t], put

    y(z)=[v3(1-z)+(1-a32)z]
       /[2+v3(1-z)+d3(1-z)+(f3-a32)z],
    w(z)=[v1(1-z)+(1-a12)z]
       /[3+v1(1-z)+d1(1-z)+(f1-a12)z],
    D=y+w-yw, H=(1-y)(1-w),
    F(z)=[Q2(y,w)+2y+w]/H.                             (Q6)

All denominators are positive. If t=0, set y=z=w=0. If t>0, there is
exactly one z in [t/2,t] with F(z)=t, continuously depending on the data.

Here are quantitative proofs. Since 4eta/b<=2/125, vi<=2t/125<=1/625.
A fraction in (Q6) with denominator base c=2 or3 has derivative numerator

    (1-a)(c+d)-vi(c+f-1)>0,

where a,d,f in [0,eta]. Thus y,w are strictly increasing. With odds
Y=y/(1-y), W=w/(1-w), the exact identity

    F=(b1+2)Y+(b3+1)W+(b13+3)YW                         (Q7)

makes F strictly increasing. At z=t/2 the numerator of y or w is at
most129t/250, and its denominator is at least c-1/40000. Hence

    y<=13t/50, w<=7t/40, H>=1913/2000,
    Q2+2y+w<=(9/4)y+(5/4)w<=643t/800.

So F(t/2)<=3215t/3826<t. Throughout z in [t/2,t],

    49z/100<=y<=13z/25,
    33z/100<=w<=7z/20.                                 (Q8)

For the lower bounds use numerator>=(1-eta)z and denominator<=c+eta+vi.
For the upper bounds use vi<=4z/125 and denominator>=c-eta*z.
At z=t this gives F(t)>=2y+w>=131t/100>t. Strict monotonicity proves
existence and uniqueness. It also proves continuity away from t=0;
(Q8) proves continuity at t=0.

Use the product root q=(0,y,z,w). Its active Quit endpoints are

    Q1=a12*z*(1-w)+d1*w*(1-z)+f1*z*w,
    Q2=Q2(y,w),
    Q3=d3*y*(1-z)+a32*z*(1-y)+f3*y*z.

Equations (Q6) say precisely that owners1,2,3 are indifferent against
the displayed continuation. Its output annotation is

    p'=3y-z+3w+c*p, v1'=Q1, t'=Q2, v3'=Q3,
    c=(1-y)(1-z)(1-w).                                 (Q9)

This preserves (Q5) and satisfies t'<=t/5. Indeed (Q4) and
2y+w>=D imply t>=(Q2+D)>=5Q2. Also D>=y>=z/3 and y,w<=D, so

    Q1<=eta(z+w)<=4eta D<=(4eta/b)t',
    Q3<=eta(y+z)<=4eta D<=(4eta/b)t'.                   (Q10)

For z>0, (Q8), inclusion-exclusion and z<=1/10 give

    73z/50<=3y-z+3w<=161z/100,
    4287z/2500<=1-c<=187z/100.

Thus R=(3y-z+3w)/(1-c) satisfies

    146/187<=R<=4025/4287, 3/4<R<1.                    (Q11)

The first coordinate p' is a convex combination of p and R, preserving
[2/3,1]. Player0's Quit value, including the grand-coalition possibility,
is at most

    3(1-c)+10yzw <=(561/100)z+(91/50)z^3
                  <=28141/50000<2/3.                  (Q12)

Its Continue value p'>=2/3 is larger. Therefore every constructed root
is exact Nash. The idle root at t=0 is also Nash.

Iterating (Q9) converges uniformly on (Q5) to (S,0,0,0). Indeed t_n<=5^(-n)t
and |p_(n+1)-p_n|<=187t_n/100. The continuous limit S lies in [2/3,1].
It is continuous jointly in all raw parameters on the domain b>0. If the
initial p<=146/187, then S>=p. No behavior is performed after infinitely
many dates; these limit annotations will only be used to join finite blocks.

### A scalar return from the raw intervals

For W in [1/5,1/4], define

    Y=W(3+2d1-3b3)
       /[10+2d3+3b1+W(2+2d1-2d3-3b1+3b13-3b3)],
    u=(3+d1)W/(1-W), v=(2+d3)Y/(1-Y),
    a=(u-v)/3, r=(u+2v)/(3-u+v),
    p=3(Y+W), t=Q2(Y,W),
    P=(p,d1*W,t,d3*Y), K=r/(1-r).                      (Q13)

The following bounds hold throughout this interval:

    1/25<=Y<=3/40,
    3/4<=u<=1001/1000, 1/12<=v<=1/6,
    1/6<a<1/3, 0<r<2/3,
    2/3<p<1, 0<t<1/10.                                (Q14)

To verify the Y bounds, its denominator is positive; Y increases with W,d1
and decreases with d3,b1,b3,b13. For the b3 and d1 derivatives, the relevant
positive factor is denominator minus W*(3+2d1-3b3), which equals

    10+2d3+3b1+W*(-1-2d3-3b1+3b13)>0.

The global lower bound from these monotonicities is1125/27502>1/25,
and the upper bound is3001/42001<3/40. At W=1/5 the sharper upper bound
is3001/52001<3/50. The u,v bounds now follow directly. They give the a
bounds and 5u+4v<6, which is equivalent to r<2/3. Finally
p in [18/25,39/40] and t<=13/160 prove the remaining bounds. Equation
(Q4) shows that P belongs to (Q5): d1*W,d3*Y<=eta D<=(4eta/b)t.

Let S(P) be its continuous triple-block limit. There exists W in the
specified interval such that

    S(P)=K.                                            (Q15)

At W=1/5, p<39/50<146/187, so S(P)>=p. To prove p>K uniformly,
use K=(u+2v)/(3-2u-v), whose denominator is positive by r<1.
After multiplication by 1-Y, the sign of p-K is the sign of

    F_L=3(Y+1/5)*[(3-2u)(1-Y)-(2+d3)Y]
           -u(1-Y)-2(2+d3)Y.

This expression decreases with u and d3. Here u<=751/1000 and
d3<=1/1000, so it is bounded below by the concave quadratic

    -10497Y^2/1000-2141Y/2500+739/5000.

Its values at the endpoints Y=1/25 and Y=3/50 are respectively
15117/156250 and146567/2500000, both positive. Concavity proves F_L>0
throughout that interval. Thus S(P)>K at W=1/5.
At W=1/4, u>=1 and v>0, so K>1>=S(P): the inequality K>1 is exactly
u+v>1. The intermediate value theorem proves (Q15). Fix one solution
and its a,r,Y,W,p,t; these data are fixed before accuracy.

### The other exact Nash operations

At L=(0,r,0,r), use a solo0 root with hazard a. Its output is

    V=(0,u,2a,v).

Player0 is indifferent. Player1's Quit value is at most2a, while its
Continue value u=2a+(1-a)r is larger. Player2's Quit value is at most2a,
its Continue value. Player3's Quit value is at most a/4<1/12<=v.
Thus this is an exact Nash root.

At continuation V, use q=(0,Y,0,W). The definitions of u,v give active
owner1 and owner3 indifference, with output values d1*W and d3*Y.
The formula for Y is exactly

    2a(1-Y)(1-W)-2Y-W=Q2(Y,W),

so inactive owner2 is tied. Owner0's Continue value3(Y+W) is at least
its Quit value3(Y+W-YW), by the raw upper bounds. This root is Nash and
its output is P. The triple block gives finite backward chains P_N tending
to Q=(S(P),0,0,0).

From Q, a second backward block uses only owner2. At continuation
(B,h,0,h), put alpha_plus=max(alpha,0) and choose
k=B/(1+alpha_plus+B), where alpha=Z0(02). Its output is

    (alpha_plus*k,k+(1-k)h,0,k+(1-k)h).

Player0's Continue value alpha_plus*k is at least its Quit value alpha*k.
Player2 is indifferent at zero, and players1,3 Continue:
their Quit values are at most eta*k<=k+(1-k)h. Its exact iterates are

    B_M=S rho^M/[1+S(1-rho^M)],
    h_M=(S-B_M)/(1+S), rho=alpha_plus/(1+alpha_plus)<=3/4.

They converge to L because S=r/(1-r). Their first backwards solo2 hazard
is S/(1+alpha_plus+S)>=1/7; the solo0 hazard a is greater than1/6.

### Finite strategies and unrestricted deviations

For finite M,N>=1 repeat the physical word

    solo0, solo2_(M-1),...,solo2_0,
    triple_(N-1),...,triple_0, pair13.

Each root is exact Nash against its displayed annotation. There are only
two value seams: the solo0 root expects L rather than the finite solo2
output Q_M, and solo2_0 expects Q rather than the finite triple output P_N.
Their total error is

    E=||Q_M-L||_infty+||P_N-Q||_infty ->0.

Every player's opponents absorb in each word with probability at least1/7:
use the designated solo2 root for player0 and solo0 for every other player.
Bellman telescoping of the prescribed equalities gives payoff error at most
7E. Telescoping the Quit/Continue upper inequalities gives full response
cap at most the displayed value plus7E. Thus every unrestricted unilateral
debt is at most14E. This includes all finite deadlines, Never and arbitrary
mixtures; the bound depends on two seams, not on the growing word length.

The reward-query inventory is complete. At solo0, only singleton0 and
singletons joined to0 are seen; at solo2, only singleton2 and singletons
joined to2; at pair13, only subcoalitions of13 and one added owner; at
triple123, only its subcoalitions and one added owner. The raw conditions
list every queried nonsingleton entry. An unlisted coordinate Z_i(A) is seen neither
in prescribed payoff nor in player i's own payoff after i replaces its
strategy. Its arbitrary finite magnitude therefore introduces no omitted
response inequality.

Every opponent family absorbs geometrically even after deleting a player.
Consequently every unilateral replacement absorbs surely. Original terminal
payoffs and caps are ell_i plus their native values, even when ell_i is
negative. The fixed target is ell+V. Choose finite M,N for each accuracy.
For that fixed word, absorption time has a finite expectation uniformly over
unilateral deviations; hence sufficiently long finite-horizon average payoffs
converge uniformly to the terminal values. This proves the uniform-equilibrium
contract with the same fixed target ell+V.

### Quantitative strategy lengths and a failed guard

The estimates above give

    E<= (3/4)^M+(187/800)(1/5)^N.

Thus M=N=L gives terminal regret at most(6909/400)(3/4)^L with period2L+2.
This is a sufficient period bound, not a lower bound for all equilibria.
The target remains fixed while L changes.

A queried upper bound cannot simply be omitted. In the calibration below,
change every proper participant reward of player0 to4. At the proposed
pair13 root, owner0's Quit-minus-Continue gap is
4(Y+W-YW)-3(Y+W)=Y+W-4YW>=W>0, because W<=1/4. This invalidates
that root. The modified game nevertheless has exact stationary Nash
q=(1,1/2,(1+h)/(3+h),1): owners1,2 are indifferent, and owners0,3
strictly prefer Quit. This control tests the particular root construction.

### Exact calibration outside stationary and sure-quitter producers

For a complete rational calibration take ell_i=1, keep Gamma from(Q1),
and set EVERY passive native reward to the sum of its singleton rewards.
Every proper nonsingleton participant reward is e=1/100 in rows0,2 and
h=1/25000 in rows1,3. Set the native grand row to(10,-2,-e,-1).
These rules specify all sixty entries and satisfy the raw tests with b=e,
eta=h and alpha=e. The following
stronger calculation covers0<e<=1/100 and0<=h<=1/2000: no stationary
terminal Nash exists, and no exact Nash root with a sure quitter exists
at any original continuation whose player2 coordinate is at least-2.
Every actual continuation, full response cap and punishment value satisfies
that lower bound, because every original reward in row2 is at least-2.

Write q=(x,y,z,w), H_i=product_(j!=i)(1-q_j), D_i=1-H_i, and
J_i=D_i product_(j!=i)q_j (these J_i are polynomial abbreviations, not
response caps). The native forced-Quit endpoints are

    Q0=eD0+(10-e)yzw, Q1=hD1-(2+h)xzw,
    Q2=eD2-2exyw,    Q3=hD3-(1+h)xyz.                    (Q11)

Passive endpoints are P=Gamma q. Set g_i=Q_i-P_i. If owner i is
sure, every other owner compares exactly Q_j and P_j, independent of
the tail. The sure owner's actual gap is g_i-H_i v_i, where v_i is
the original continuation minus1; the only needed tail bound is v2>=-3.

**All sure faces.** If x=1, then

    g3=1+2y-z(1+y)+h(1-yz)>=y+h(1-y).

Its sole possible zero boundary h=y=0,z=1 is rejected by g2=e-2+w<0.
Thus w=1. The remaining free conditions give y=1/2 and
z=(1+h)/(3+h), but owner0's gap e-9/2+(6-e/2)z<0.
If y=1, the successive strict gains g2>=e,g3>0,g0=5 force all
four sure, where owner1's gap is-2. Thus x,y<1 in the remaining cases.
If z=w=1, the only free solution is

    x=(2+h)/(4+h), y=(2-e)/(7-e),
    g3=(3eh+4e-5h^2-26h+2)/[(e-7)(h+4)]<0.

The endpoints x=0 or y=1 reduce to the already rejected sure1 case;
x=1 was also rejected. These signs cover all multiple-sure roots.

For z=1 alone, w=0 forces y=0 and then x=1, impossible. Thus0<w<1,
and g3=0 gives y=(1-h-x)/(2-(1+h)x). If y=0, the sole free candidate
is x=1-h,w=(1+e)/3. Even with the best admissible tail, owner2's gain is

    g2+3H2=(4e-5)/3+h(4-5e/3+e^2/3)
             <=(4e-5)/3+h(4-e)<0.

If y>0, then g1=0 gives w=(2x+1-h)/(3-(2+h)x) and0<=x<51/100.
Multiplying g0 by both positive denominators yields

    N2=4ex^2-8ex+5e-18x^2+9x+1
       +h(3ex^2-4ex+2e+6x^2-18x-5)
       +h^2(ex^2-e+x^2-6x+10)>0.

Indeed its h=0 part is at least4541/5000, and the absolute perturbation
is less than16h. Thus g0>0 forces x=1, contradicting this face.

For w=1 alone, z=0 forces x=0 and then z=1, impossible. Hence0<z<1;
g2=0 gives y=(2x-1-e)/(2(1-ex)) and x>1/2. The case y=0 has
g0=e+z-3<0. Otherwise g1=0 gives z=(3+h-2x)/(1+(2+h)x).
The numerator of g0 after multiplication by the positive denominators is

    N3=-52x^2+64x-27
       +e(20x^2+22x-22)+e^2(-4x^2-4x+3)
       +h(-2e^2x^2+e^2+6ex^2+ex-9e-6x^2+17x-8).

On1/2<=x<=1, N3<=-95/13+20e+32h<0, contradicting x>0.
This exhausts every sure-owner face and every admissible punishment tail.

**Proper stationary faces.** Against positive opponent activity, the
stationary endpoint sign is F_i=D_i Q_i-P_i. A proper positive hazard
requires F_i=0; a zero hazard requires F_i<=0. AllContinue fails because
original own singletons are1. Put E=D2^2-2J2,
E1=h(D1^2-J1), E3=h(D3^2-J3), both E1,E3>=0. Then

    F0=eD0^2+(10-e)J0-3y+z-3w,
    F1=-2J1+E1-2x-z+3w,
    F2=eE-2x+2y+w,
    F3=-J3+E3+x+2y-z.                                  (Q12)

If x=0, F2>0 forces a sure2 unless y=w=0; then F0>0. If z=0,
F3>0 forces a sure3. If w=0, F1<0 forces y=0, and then F0>0.
Thus x,z,w>0. If y=0, the active equalities imply

    z>=(3-e)w/(1+e), x<=(1+e)w/(2-e),
    z<=(1+h)x/(1-h),

which are incompatible already for e<=1/4,h<=1/10. Every remaining
stationary candidate is therefore fully mixed.

Put a=y/x,b=z/x. Equations (Q12) give
w<=2x-2(1-e)y and(3+h)w>=(2-h)x+(1-h)z, hence a<3/4.
The row3 equation gives b<3, and w/x<=2. Consequently

    D0^2/x<6, E1/x<6h, |E|/x<6.

Let A=4-6a-b,C=6-3a-b,k=(10-e)/2. The first two equations give

    xA=2J1-E1+3eE, xC=(10-e)J0+eD0^2+3eE.

Since x>y, D1>D0 and J0<aJ1. Therefore

    C-kaA < ka E1/x+e[D0^2+3(1-ka)E]/x
           <=(45/2)h+60e.                             (Q13)

But C-5aA=30a^2-23a+6+(5a-1)b. For a>=1/5 this is at least191/120
by completing the square. For a<1/5, the formula for A gives
b<=4-6a+6h+18e, and substitution gives the same lower bound.
Since |A|<=5,

    C-kaA>=191/120-(5/2)e>=47/30,

contradicting (Q13). This proves stationary absence for the calibration.

The sure-owner comparison audits the full selection in
`HasQuittingPunishmentVectorNashRootWithSureQuitter` in
`UniformEquilibrium/Quitting/Classification/InstantPunishmentSureQuitterCharacterization.lean`.
It does not infer punishment failure merely from stationary failure.
No positive unrestricted exploitability gap is claimed: the producer above
constructs approximate equilibria for this same literal table.

### Further exact raw-criterion comparisons

At the calibration, only player0 has globally nonnegative participant
premiums: the other native grand rewards are negative. The pair13 is a
positive-premium trap disjoint from{0}; all four players form a premium
trap. Thus EVERY protected-player selection fails the support-specific
strict or weak leaver criterion, and criteria requiring a greatest premium
core of size at most two do not apply. This uses the definitions
`HasProtectedParticipantPremiums`, `HasSupportSpecificQuittingLeavers`, and
`quittingMaximalProtectedPlayers` in
`UniformEquilibrium/Quitting/Classification/SupportSpecificQuittingPremiumLeavers.lean`.

The grand-row sign matters to the comparison. With h=0 and native grand2=+e,
the similar family is already covered by protected player2 when e<2: its
only possible premium trap is02 and leaving pays2>e. The implemented
consumer is `exists_uniformEquilibriumPayoff_of_supportSpecific_strictLeave`
in `UniformEquilibrium/Quitting/Classification/Existence/SupportSpecificQuittingPremiumLeaversUniformPayoff.lean`.
That older coverage is not counted as a new existence conclusion here.

No nonzero nonnegative vector k can have k dot Z(A)>=0 for every proper
nonempty coalition at the calibration. Coalitions013,01,{2},03 give

    k2<=e*k0+h(k1+k3), 3k3<=e*k0+h*k1,
    k0<=k1+k3, k1<=e*k0+k2+h*k3.

Hence(1-h-2h^2/3)k1<=e(2+2h/3)k0, which gives k1<=3e*k0 and
k3<=e*k0/2. Therefore k0<=7e*k0/2<k0 unless all weights vanish.
This rejects every positive proper-coalition ledger, regardless of further
calendar or orientation selections.

The support-filtered ledger tests also fail for every choice of weights.
Their required joining sums

    J_k(A)=sum_(i notin A) k_i[Z_i(A union{i})-Z_i(A)]<=0

at A=123,013,012 respectively force k0=k2=k3=0, because the three
missing-owner joining gaps are5,1-e,1. The required nonnegative weighted
payoff at singleton3 then reads-3k1>=0. This exhausts the nonnegative
weight selection in those tests, not merely a chosen candidate weight.

A further complete selection check excludes universal child-debt lifts.
For EVERY proper nonempty child S there are actual child profiles with
vanishing child debts but a quiet outsider's debt bounded away from zero.
For a singleton child use its sole owner geometrically with hazard1/2;
every column of Gamma has a negative outsider, whose Quit-now value is
nonnegative. For pairs and two triples the following exact child Nash
profiles suffice (j means sole geometric owner j;13 means both sure):

| Child | Child profile | Violating outsider |
| --- | --- | --- |
| 01,02,012 | 0 | 3 |
| 03 | 3 | 1 |
| 12,23 | 2 | 0 |
| 13,013 | 13 | 2 |

Each quiet child member in a sole-owner row receives at least1 natively,
above its small joining value. With sure13, child owner0 receives6 rather
than joining for e, while outsider2 gains3+e.
For child123 use one root
q1=(1-h)/2,q2=1,q3=(1-h)/3, then Never. Owners1,3 are indifferent;
owner2 prefers Quit to every delay. Outsider0's joining gain is

    [1+5e+(2e-5)h+(10-e)h^2]/6>0.

For the remaining child023, repeat solo owners3,0,2 with cumulative hazards
5/12,5/14,5/9. In coordinate order0,2,3, its respective native value rows
are(5/4,0,0),(0,5/7,0),(0,0,5/9). Subdivide each solo phase, preserving
its cumulative survival, until every hazard is at most delta. All intermediate
values remain nonnegative and equal the Continue branch, including at an
active owner's zero coordinate. Every forced-Quit value is at most
max(e,h)*delta. Adding that constant to the value rows therefore gives a
full cap supersolution, so every child debt is at most max(e,h)*delta.
Positive opponent absorption per cycle removes the infinite remainder.
The terminal singleton probabilities remain(1/4,1/4,1/2), giving quiet
outsider1 native payoff-3/4. Prepend an empty date: child debts retain their
bound, while outsider1 can Quit there for native zero. Its gap is at least3/4.

This exhausts every proper child. Therefore no choice of a child or finite
weights can give a universal bound of outsider debt by child debts for this
calibration. It specifically defeats the all-child-profile consumer
`quittingLiftDeletedProfile_outsideDebt_le_of_withdrawalFutureJoin` in
`UniformEquilibrium/Quitting/Classification/QuietExtension/WithdrawalFutureJoinFixedTarget.lean`
and its raw `WithdrawalFutureJoinRewardCertificate` in
`UniformEquilibrium/Quitting/Classification/QuietExtension/WithdrawalFutureJoinRaw.lean`.
It does not exclude a producer selecting some specially favorable child
profile by a different method.

These comparisons do not claim an exhaustive census of every abstract UE
certificate. They give literal raw obstructions to the named broad classes,
including the full stationary and sure-owner/punishment selections above.


## Computable thresholds over a complete signed singleton chamber

### Raw signed chamber and theorem

After positive scaling of payoff rows1 and3, let the native singleton matrix be

    G=[0, g1,-g2, g3;
       k, 0,  1, -c;
       A,-h1, 0,-h3;
      -l, -d, 1,  0],                                (G1)

where g2,g3,k,A,h3,l,c,d are strictly positive, while g1 and h1 are
arbitrary real numbers, including zero. The native convention, information structure and unrestricted deviations
are those of the quantitative theorem above.

Fix EVERY native reward except these nine participant coordinates:

    a12=Z1(12), d1=Z1(13), f1=Z1(123),
    d3=Z3(13), a32=Z3(23), f3=Z3(123),
    b1=Z2(12), b3=Z2(23), b13=Z2(123).                (G2)

All higher passive rewards are arbitrary finite numbers. Write
K0=Z0(13), K2=Z2(13). Impose only the three joining comparisons

    Z0(01)<=g1, Z0(03)<=g3, Z0(013)<=K0,               (G3)

and the two solo0 comparisons

    Z1(01)<=k, Z2(02)<=A.                              (G4)

For K2<=0, the raw construction below produces numbers
B>0, kappa>0, Lambda>0, depending only on the fixed background data,
with the following theorem. Also require Z3(03)<=Lambda. For ANY

    0<b<=B,
    b<=b1,b3,b13<=B,
    |a12|,|d1|,|f1|,|d3|,|a32|,|f3|<=eta<=kappa*b.     (G5)

the original game has a uniform-equilibrium payoff. No other background
participant reward is restricted. In particular Z0(02), all four grand
rewards and every unqueried coordinate may be any finite real numbers.

The construction is genuinely uniform over the independent intervals (G5).
B does not depend on the nine coordinates (G2). For rational or algebraic
background data the finite semialgebraic searches defining its constants
can be performed by real quantifier elimination. For arbitrary real data
the same least-integer definitions are mathematically well defined.

There are two immediate exits. If K2>0, then d1>=-c, d3>=-d and b13<=K2
give a pure pair13 equilibrium under (G3), because its participants prefer
their pair premiums to their passive singleton alternatives. For example take
B=min(1,K2), kappa=min(1,c,d)/2 and Lambda=1+max(0,Z3(03)); then the
interval conditions (G5) imply these pure-pair comparisons automatically.
The other six entries in (G2) are unrestricted in the pure-pair argument itself. If the inverse-column condition used below fails, the existing
same-table source gives UE directly.
Thus K2<=0 is the only new construction branch.

### The matrix source and exact base return

Put

    C=c*h1+d*h3, N=A*c-(k+l)*h3, D=A*d+(k+l)*h1.

Exact cofactor expansion gives

    adj(G)e0=(C,N,d*N+l*C,D),
    det G=g1*N+g3*D-g2*(d*N+l*C).                      (G6)

In this chamber a hypothetical no-UE table has det G>0 and C,N,D>0.
The shared singleton-matrix source proved below gives this implication
from the literal table, without any joint-reward hypotheses. Its inputs are
the named actual-game Q/R0/degree and positive-inverse child declarations;
no new Lean verification is claimed.
If det G<=0 or any of C,N,D is nonpositive, the source's contrapositive
already gives original UE;
in that branch set B=kappa=Lambda=1 to define the advertised constants.
Assume henceforth det G>0 and C,N,D>0. Then (G6) gives G^-1 e0>>0.

Use a positive scalar x as the odds of player3's macroscopic hazard.
At the zero values of the nine coordinates (G2), set

    X0(x)=N*x/[D-(k+l)*K2*x],
    W=x/(1+x), Y0=X0/(1+X0),
    u0=c*x, v0=d*X0,
    a0=(u0-v0)/(k+l),
    r0=(l*u0+k*v0)/(k+l-u0+v0),
    p0=g1*Y0*(1-W)+g3*W*(1-Y0)+K0*Y0*W,
    F0=p0-g2*r0/(1-r0).                               (G7)

All quantities are rational functions of raw background data and x.
The denominator of X0 is positive for every x>=0. Moreover

    A*a0=h1*X0+h3*x-K2*X0*x.

Indeed a0'= [c-d*N*D/(D-(k+l)*K2*x)^2]/(k+l)>=C/D>0.
Thus a0>0 for x>0 and a0 eventually exceeds1. Before its first value1,
r0 is positive and tends to infinity at that endpoint. Consequently it
first reaches1 at a finite earlier point. Both hazards Y0,W remain proper
at every finite x. Initially p0>0 because g1*N+g3*D=det(G)+g2*(d*N+l*C)>0.
Direct differentiation gives

    F0'(0)=det G/D>0.                                  (G8)

Stop at the first r0=1 or the first POSITIVE zero of p0 after its initial
positive interval (if such a zero exists). Immediately before that stop, F0 is
negative: in the first case its second term diverges; in the second case
its first term tends to zero while its second is strictly positive. If
both happen together the negative conclusion remains. Therefore there
exist rational 0<xL<xR such that, throughout J=[xL,xR],

    0<a0,r0,Y0,W<1, p0>0,
    F0(xL)>0, F0(xR)<0.                               (G9)

This also proves a finite raw procedure for producing them: enumerate
rational pairs, retaining the first for which (G9) holds, with its interval
conditions checked as strict polynomial inequalities after clearing the
positive denominators. The preceding argument guarantees termination.
No strategic object is assumed in this search.

On J define the positive raw minima and maxima

    amin=min a0, amax=max a0, rmin=min r0, rmax=max r0,
    pmin=min p0, pmax=max p0, vmin=min v0,
    mF=min(F0(xL),-F0(xR)),
    Lambda=(1/2)*min(v0/a0)>0.                          (G10)

These are extrema of specified rational functions on one compact interval.

### A finite raw threshold for the macroscopic roots

For temporary parameters d1,d3,b1,b3,b13 near zero define

    Nx=A*(c+d1)-(k+l)*(h3+b3),
    Dx=A*(d+d3)+(k+l)*(h1+b1),
    X=Nx*x/[Dx+(k+l)*(b13-K2)*x],
    Y=X/(1+X), W=x/(1+x),
    u=(c+d1)*x, v=(d+d3)*X,
    a=(u-v)/(k+l), r=(l*u+k*v)/(k+l-u+v),
    p=g1*Y*(1-W)+g3*W*(1-Y)+K0*Y*W,
    F=p-g2*r/(1-r).                                   (G11)

Let Bmac be the first dyadic number 2^(-n), n>=0, at most
min(1,c/2,d/2,D/(2A),N/[2(A+k+l)]) for which the following finite semialgebraic
tests hold for every x in J, d1,d3 in [-Bmac,Bmac], and b1,b3,b13 in [0,Bmac]:

    0<Y<1,
    amin/2<=a<=(1+amax)/2,
    rmin/2<=r<=(1+rmax)/2,
    pmin/2<=p<=pmax+1/2,
    v-Lambda*a>=vmin/4,
    F(xL)>=mF/2, F(xR)<=-mF/2.                         (G12)

All denominators are required positive in these tests. Such n exists by
uniform continuity on J: at zero parameters all inequalities have positive
slack. The coefficient Nx remains positive by the imposed upper bound.
The interval and parameter-box tests are finite quantified polynomial
formulas; no unknown continuation or equilibrium occurs in them.

### A finite Taylor box for the complete signed chamber

The extra signs allowed in (G1) mean h1 may be negative. The positive
inverse-column source nevertheless supplies

    H0=h1/d+h3/c=C/(c*d)>0.

No componentwise positivity of h1 is used below. Put

    Lh=abs(h1)/d+h3/c, Ld=1/d+1/c,
    K=2*max(c,d)+1,
    xi0=min(1/100,H0/(100*Lh)),
    kappa=min(1,xi0/(4*H0*K)),
    delta1=Z1(23)-(1-c), delta3=Z3(12)-(1-d).            (G13)

Here Lh>0 because h3>0. A finite raw Taylor box will control all
nonadditive passive terms, however large they are.

For variables z,xi1,xi3 and the nine participant parameters (G2), set

    dy=d+z*xi3*(1-z)+d3*(1-z)+(f3-a32-delta3)*z,
    dw=c+z*xi1*(1-z)+d1*(1-z)+(f1-a12-delta1)*z,
    Ry=[xi3*(1-z)+(1-a32)]/dy,
    Rw=[xi1*(1-z)+(1-a12)]/dw,
    Yhat=Ry/(1-z*Ry), What=Rw/(1-z*Rw),
    Lcore=(b1+h1)*Yhat+(b3+h3)*What+(b13-K2)*z*Yhat*What.

These are rational expressions with no division by z. Also define

    Dy=[(1-a32)*(d+d3)-z*xi3*(d+f3-delta3-1)]/dy^2,
    Dw=[(1-a12)*(c+d1)-z*xi1*(c+f1-delta1-1)]/dw^2,
    Ydot=Dy/(1-z*Ry)^2, Wdot=Dw/(1-z*Rw)^2,
    Dcore=(b1+h1)*Ydot+(b3+h3)*Wdot
             +(b13-K2)*(Ydot*z*What+z*Yhat*Wdot).       (G14)

Let lambda be the first dyadic number 2^(-n)<=1/4 for which all the
following tests hold throughout the FINITE parameter box

    0<=z<=lambda, abs(xi1),abs(xi3)<=xi0,
    abs(a12),abs(d1),abs(f1),abs(d3),abs(a32),abs(f3)<=lambda,
    0<=b1,b3,b13<=lambda:

    all displayed denominators are positive,
    1/(2d)<=Ry<=2/d, 1/(2c)<=Rw<=2/c,
    z*Ry<=1/4, z*Rw<=1/4,
    H0/2<=Lcore<=2H0, Dcore>=H0/2.                     (G15)

These are finite semialgebraic conditions on raw background data. This
search TERMINATES, rather than assuming such a box. At z=0 and all nine
participant parameters zero, uniformly for the compact xi box,

    Ry=(1+xi3)/d, Rw=(1+xi1)/c,
    Lcore=H0+h1*xi3/d+h3*xi1/c,
    Dcore=H0.

Thus Ry,Rw have strict slack in (G15), and
.99H0<=Lcore<=1.01H0. The other inequalities also have strict slack.
Uniform continuity on the compact xi box gives the claimed sufficiently
small positive lambda. Clearing the positive denominators converts every
test to a polynomial condition; no unknown root or strategy is tested.

Consider a tail (p,v1,t,v3) with

    0<=t<=H0*lambda/4,
    abs(v1),abs(v3)<=(K*eta/b)*t, eta<=kappa*b.          (G16)

For t>0, and z in [t/(4H0),4t/H0], substitute xi_i=vi/z into (G14)
and set y=z*Ry,w=z*Rw. This substitution is inside the box because
abs(vi/z)<=xi0. With the participant entries satisfying b_i<=B,
eta<=kappa*b, require

    B<=Bcore=min(1,lambda/(1+kappa),H0*lambda/4,H0/(40*Ld)).
                                                               (G17)

Then all nine entries belong to the box. The native core Continue/Quit
equalities are exact equalities precisely when

    Fcore(z)= [Q2+h1*y*(1-w)+h3*w*(1-y)-K2*y*w]
                       /[(1-y)*(1-w)] = t,
    Q2=b1*y*(1-w)+b3*w*(1-y)+b13*y*w.                 (G18)

The rational expression Fcore/z is Lcore. Its derivative when v1,v3 are
HELD FIXED, evaluated at vi=z*xi_i, is exactly Dcore. This distinction
is the reason for the explicit formulas Dy,Dw in (G14).

At the bracket's lower endpoint, (G15) gives Fcore<=t/2; at its upper
endpoint it gives Fcore>=2t. Moreover Dcore>=H0/2>0 throughout the
bracket. Hence there is a unique root there, continuously depending on
the data. If t=0, the cone forces vi=0 and the chosen root is idle.
The bounds below make continuity at t=0 explicit. Every nonidle root
is proper, since z<=lambda<=1/4 and y,w<=1/4.

The root q=(0,y,z,w) makes owners1,2,3 indifferent. Its active outputs
are the literal participant averages Q1,Q2,Q3. Put Dq=y+w-yw. From
(G15), (G17), (G18) and the raw reward bounds,

    z/(2d)<=y<=2z/d, z/(2c)<=w<=2z/c,
    0<=t'=Q2<=B*(y+w)<=2B*Ld*z<=t/5,
    abs(Q1),abs(Q3)<=K*eta*Dq<=(K*eta/b)*t'.            (G19)

For the last inequality, use Q2>=b*Dq, abs(Q1)<=eta(z+w),
abs(Q3)<=eta(y+z), and z<=2*max(c,d)*Dq. Thus the signed cone is
invariant. Neither the core's partial payoff signs nor the passive
player's singleton drift is assumed nonnegative.

Let Mpass=max{|Z0(S)|:empty!=S subset123},
Mquit=max(0,max{Z0(S):0 in S}), and define

    Lbox=pmax+1, Lhaz=1+2/d+2/c,
    Cstep=(Mpass+Lbox)*Lhaz,
    Delta=min(pmin/4,1/4,mF/4),
    B=min(Bmac,Bcore,
          H0*Delta/(5*Cstep),
          pmin*H0/[32*(1+Mquit)*Lhaz]).                (G20)

All constants are positive and depend only on background data, excluding
(G2). At any step with abs(p)<=Lbox, the passive player's change is bounded
by Cstep*z<=4*Cstep*t/H0. Summing (G19) bounds the total change by
5*Cstep*t_initial/H0<=Delta. Starting from a macro p in (G12), induction
therefore keeps p in [pmin/4,pmax+3/4], inside the bounding box. Its Quit
endpoint is at most Mquit*Lhaz*z<=pmin/8, while its Continue value is at
least pmin/4. Hence every triple root is fully Nash.

The triple iterates converge uniformly to (S,0,0,0), with

    abs(S-p_initial)<=Delta.                           (G21)

Uniform geometric convergence and the continuous scalar root give continuity
of S. This includes arbitrary signed higher passive rewards and arbitrarily
large finite participant rewards for player0. It uses actual finite root
words and their limiting annotations, never execution after an infinite block.

### Scalar crossing and actual finite strategies

For each x in J, the macroscopic annotation

    P=(p,d1*W,Q2(Y,W),d3*Y)

belongs to the contraction cone: Q2>=b*(Y+W-YW), while |d1*W|,|d3*Y|
are at most eta*(Y+W-YW). Equations (G12), (G20) and (G21) imply that
S(P)-g2*r/(1-r) has opposite strict signs at xL and xR. The intermediate
value theorem produces x with S=g2*r/(1-r). Fix its macroscopic data.

At L=(0,r,0,r), the solo0 root of hazard a has output
V=(0,u,A*a,v). Player0 is indifferent. Conditions (G4) make owners1,2
Continue; the computed inequality v>=Lambda*a and the raw bound on
Z3(03) make owner3 Continue. At continuation V, the pair13 root with
hazards Y,W is Nash: its owner1/3 equations are u=(c+d1)W/(1-W),
v=(d+d3)Y/(1-Y); equation (G11) is exactly owner2's indifference.
The termwise comparisons (G3) make owner0 Continue. Its output is P.

The triple block tends to Q=(S,0,0,0). To return from Q to L, put
alpha_plus=max(Z0(02),0). At continuation(B,h,0,h), use a solo2 root

    k2=B/(g2+alpha_plus+B).

Its output is(alpha_plus*k2,k2+(1-k2)h,0,k2+(1-k2)h). Owner0's Continue
value alpha_plus*k2 is at least its Quit value Z0(02)*k2; owner2 is
indifferent, and owners1,3 Continue because their joining premiums are
at most eta<=1. With rho=alpha_plus/(g2+alpha_plus)<1, its iterates are

    B_M=S*rho^M/[1+(S/g2)*(1-rho^M)],
    h_M=(S-B_M)/(g2+S).

They tend to L since r=S/(g2+S). Thus both infinite backward chains are
used only through their finite truncations and their limiting annotations.

Repeat the finite word solo0, reversed solo2 block, reversed triple block,
pair13. Its only errors are two annotation seams, tending to zero. Every
player's opponents absorb each word with probability at least

    eta_abs=min(a,S/(g2+alpha_plus+S))>0.

Full Bellman telescoping therefore gives payoff error at most E/eta_abs
and every unilateral terminal debt at most2E/eta_abs, where E is the sum
of the two seam norms. This bound does not grow with word length and
covers finite deadlines, Never and arbitrary complete laws.

All unilateral replacements absorb surely, so adding each own level ell_i
to the native rewards shifts both payoff and cap by ell_i. The fixed target
is ell+V. Choose finite block lengths for each accuracy. Geometric opponent
absorption gives uniform convergence of long-horizon payoffs over deviations,
proving the original uniform-equilibrium contract.


## Arbitrary positive pair premiums and a complementary contraction

Use the same literal native matrix as the signed-chamber theorem:

    G=[0,g1,-g2,g3; k,0,1,-c; A,-h1,0,-h3; -l,-d,1,0].

The parameters g2,g3,k,A,h3,l,c,d are positive; h1 is arbitrary signed.
For the construction branch assume g1>=0. Put

    Cs=c*h1+d*h3, N=A*c-(k+l)*h3, D=A*d+(k+l)*h1.

The shared same-table source says that failure of any of detG,Cs,N,D>0
already gives original UE, independently of the higher rewards. We therefore
need only the branch where all four are positive. No strategic input is
being assumed in this reduction.

### Raw family

Own levels ell are arbitrary signed finite numbers. Put

    K0=Z0(13)>=0, K2=Z2(13) arbitrary finite,
    P1=Z1(13)>=0, P3=Z3(13)>=0,
    Dpair=c*d+c*P3+d*P1,
    apsi=h3/c, bpsi=h1/d,
    Cpsi=(apsi*P1+bpsi*P3-K2)/Dpair,
    Czero=(K0+(g3/c)*P1+(g1/d)*P3)/Dpair,
    Cplus=max(Cpsi,0),
    Lambda=d*N/[Cs+c*c*d*D*Cplus/Cs]>0.              (P1)

Only the following additional queried participant bounds are needed:

    Z0(01)<=g1, Z0(03)<=g3, Z0(013)<=K0;
    Z1(01)<=k, Z2(02)<=A, Z3(03)<=Lambda;
    Z1(12)<=1, Z3(23)<=1;
    Z2(12)<=bpsi*P3, Z2(23)<=apsi*P1,
    Z2(123)<=apsi*P1+bpsi*P3+Cpsi*P1*P3.                  (P2)

The entry Z0(02) is arbitrary, as are every other nonsingleton entry not
listed, including every grand reward and every other passive nonsingleton
coordinate. Every one-sided bound has no implicit lower bound. The two pair
premiums P1,P3 have no upper bound.

Claim: this complete raw family has an original UE payoff. If the matrix
source exits before (P1), no additional reward restriction is needed; for
formal raw packaging one may define Lambda=1 on that already solved branch.

### Immediate pair exit

If Cpsi<=0, use q1=q3=1 and q0=q2=0. The pair participants prefer P1,P3>=0
to their negative passive singletons -c,-d. Owner0 prefers K0 to Z0(013).
Writing B=apsi*P1+bpsi*P3, the last cap gives

    Z2(123)<=B+Cpsi*P1*P3=K2+Cpsi*(Dpair+P1*P3)<=K2.

Thus owner2 also Continues. Two sure opponents price all unilateral
responses immediately. This is exact terminal Nash and UE. This exit in
fact does not need g1>=0 or K0>=0; those signs are used only below.

Assume henceforth Cpsi>0. No sign restriction on bpsi is needed.
For a pair-premium-independent sufficient cap one may replace Lambda by

    d*N/[Cs+M*c*D/Cs], M=max(h1,h3,-K2,0),

because Cpsi<=M/(c*d). The sharper raw value (P1) is used below.

### Exact pair operation and its limit

For a tail(s,u,t,v) with u,v>=0 set

    w=u/(c+P1+u), y=v/(d+P3+v), H=(1-y)(1-w),
    u'=P1*w, v'=P3*y,
    Psi(u,v)=apsi*u+bpsi*v+Cpsi*u*v,
    Phi(u,v)=(g3/c)*u+(g1/d)*v+Czero*u*v.             (P4)

When t=Psi(u,v), the product root(0,y,0,w) has output

    s'=P0+H*s, u', t'=Psi(u',v'), v',
    P0=g1*y*(1-w)+g3*w*(1-y)+K0*y*w.                 (P5)

The exact identities proving this are

    (1-w)u=c*w+u', (1-y)v=d*y+v',
    H*u*v-u'*v'=Dpair*y*w,
    P2+H*Psi(u,v)=Psi(u',v'),
    [s'+Phi(u',v')]=H*[s+Phi(u,v)],                  (P6)
    P2=-h1*y*(1-w)-h3*w*(1-y)+K2*y*w.

The first two rows of (P6) verify owners1,3 indifference. The spectator2
Continue-minus-Quit difference is bilinear in y,w. At the four vertices
its values are0, bpsi*P3-Z2(12), apsi*P1-Z2(23), and
apsi*P1+bpsi*P3+Cpsi*P1*P3-Z2(123), all nonnegative by (P2).
This remains valid when bpsi or the displayed t values are negative.
Owner0 Continues: its Quit endpoint is at most P0 by the termwise caps,
and P0>=0. Starting from s=0, induction gives s_n>=0, hence s_n'=P0+H*s_n
is at least its Quit endpoint. Every root is therefore exact Nash.

The scalar iterations are explicit:

    u_n=u*r1^n/[1+(u/c)(1-r1^n)], r1=P1/(c+P1)<1,
    v_n=v*r3^n/[1+(v/d)(1-r3^n)], r3=P3/(d+P3)<1,
    product_(j<n)H_j=(c+u_n)(d+v_n)/[(c+u)(d+v)].

The zero-premium cases vanish after one step. All coordinates remain
bounded; t_n=Psi(u_n,v_n) may be signed but tends to zero. Starting at
s=0, the limit is Q=(S,0,0,0), where

    S(u,v)=c*d*Phi(u,v)/[(c+u)(d+v)]>0                (P7)

for u,v>0. This is an explicit rational limit, not a supplied continuation.

### Global scalar return

For u>0 define

    v=d*N*u/[c*D+c*d*(k+l)*Cpsi*u],
    a=(u-v)/(k+l), r=(l*u+k*v)/(k+l-u+v).             (P8)

These formulas give A*a=Psi(u,v) exactly. Since

    R0=d*N/(c*D)<1,
    1-R0=(k+l)*Cs/(c*D)>0,

we have v>0, v/u<=R0<1 and v'<=R0. Therefore a increases strictly
from zero and eventually exceeds1. Before its first value1, r is positive,
strictly increasing and tends to infinity. It first reaches1 at a finite
point ustar with a<1.

On 0<u<ustar set

    F(u)=S(u,v)-g2*r/(1-r).

The cofactor identity
 detG=g1*N+g3*D-g2*(d*N+l*Cs)
gives exactly

    F'(0)=detG/(c*D)>0.                              (P9)

Near ustar, S remains finite whereas the second term tends to infinity.
Thus F is negative there and positive sufficiently near zero. The
intermediate value theorem produces u in(0,ustar) with F(u)=0. Fix it,
v,a,r and S once and for all. They are produced from the raw finite data.
In particular0<a,r<1 and S=g2*r/(1-r).

The raw Lambda bound in (P1) checks the remaining solo0 response uniformly.
Indeed a>=u*Cs/(c*D), so a<1 gives u<c*D/Cs. Directly from (P8),

    v/a=d*N/[Cs+c*d*Cpsi*u]
        >=d*N/[Cs+c*c*d*D*Cpsi/Cs]=Lambda.                  (P10)

At L=(0,r,0,r), a solo0 root of hazard a has output

    V=(0,u,A*a,v).

Owner0 is indifferent. Owners1,2 Continue by their caps k,A; owner3
Continues by (P10). Thus this root is exact Nash. Since A*a=Psi(u,v),
the pair operation applies directly to V and converges to Q.

### Solo2 operation and actual finite strategies

Put alpha=Z0(02), alpha_plus=max(alpha,0). At a tail(B,h,0,h), choose
solo2 hazard z=B/(g2+alpha_plus+B). Its output is

    (alpha_plus*z,z+(1-z)h,0,z+(1-z)h).

Owner0's Continue is at least its actual Quit value alpha*z; owner2 is
indifferent at zero; owners1,3 Continue by their caps1. Starting from Q,

    B_m=S*rho^m/[1+(S/g2)(1-rho^m)],
    h_m=(S-B_m)/(g2+S), rho=alpha_plus/(g2+alpha_plus)<1.

The limit is L. The first backwards solo2 hazard is
z0=S/(g2+alpha_plus+S)>0.

Repeat the finite physical word
 solo0, solo2_(M-1),...,solo2_0, pair_(N-1),...,pair_0.
There are two value seams only: L versus the finite solo2 output, and Q
versus the finite pair output. Their total norm E tends to zero. Every
player sees its opponents absorb in each word with probability at least
min(a,z0)>0. The exact Bellman equalities and upper response inequalities
therefore give prescribed error at most E/min(a,z0) and full regret at most
2E/min(a,z0), by geometric telescoping over periods. This prices every
finite deadline, Never and arbitrary behavioral mixtures.

The finite support types0,2,13 query exactly the entries listed. An unlisted
row-i entry is absent from i's prescribed payoff and i's own replacement
payoffs. Every unilateral replacement absorbs surely, so centering by signed
ell is exact. The fixed target is ell+V. For each accuracy choose finite
M,N; finite expected opponent absorption then supplies the uniform-horizon
conclusion. No strategy is performed after an infinite calendar.

### Additional fixed-matrix quantitative corollary

At the deadlock Gamma, take c=3,d=2,k=A=h1=2,l=h3=g2=1,g1=g3=3,
K0=6,K2=-3. The previous formulas become
 Cpsi=(9+P1+3*P3)/(3*(6+2*P1+3*P3)), Czero=(12+2*P1+3*P3)/(2*(6+2*P1+3*P3)).
For ALL P1,P3>=0, kappa=3Cpsi lies in[1/2,3/2] and Czero in[1/2,1].
Taking u in[1/2,1], v=u/(5+kappa*u), the return difference has the exact
uniform endpoint bounds

    F(1/2)>=15/28-29/80=97/560>0,
    F(1)<=1-17/11=-6/11<0.

Moreover v/a>=6/11. Thus in this literal fixed-matrix corollary the
solo3 joining cap may be relaxed to Z3(03)<=1/2, independently of P1,P3.
This is a stronger numerical range than the conservative general Lambda.
It introduces no further strategy input or proof architecture.

### Calibration separating the mechanisms

Use the same complete calibration table defined above, now with

    e=1/100000, h=3/100000.

Then P1=P3=h and the three spectator2 caps (P2) hold: e<=h,
e=h/3, and e<=h/3+h+Cpsi*h^2. Every other pair-theorem bound holds,
including Z3(03)=h<1/2. This table therefore has UE by the pair mechanism.
Its h/e=3 violates the quantitative triple condition (Q3) and the general
triple condition (G5), whose constructed kappa is at most1. The earlier
stationary, sure-owner/punishment-tail, protected-player, ledger and every
proper-child obstruction proofs apply to this same table: they were proved
uniformly for 0<e<=1/100 and 0<h<=1/2000.

The general signed-chamber branch also meets those exact obstructions.
On the reference singleton and additive-passive background, choose

    0<e<=min(1/100,B/2),
    0<h<=min(1/2000,kappa*e/2,Lambda/2),

and use the complete calibration table again. This is not circular:
Bmac, Bcore, kappa, Lambda and Mpass depend only on the fixed singleton
and passive entries, while the native grand0 reward10 fixes Mquit=10
throughout this range. Thus B does not depend on e or h here. Conditions
(G3)--(G5) hold, and the same complete earlier obstructions apply.

## A uniform rectangle of independent positive premium scales

There is a constant delta>0 with the following property. Let

    0<beta<delta, 0<eta<delta.

Use the native singleton matrix

    Gamma=[0,3,-1,3; 2,0,1,-3; 2,-2,0,-1; -1,-2,1,0].

Every passive native reward is additive in its singleton entries. Every
proper nonsingleton participant reward in rows1,2,3 is respectively
eta,beta,eta. The SIX proper nonsingleton participant rewards in row0 are
independent arbitrary finite numbers at most1, with no lower bounds. The
native grand reward of player0 is any finite number at most10; the other
three grand coordinates are arbitrary finite data. For arbitrary signed
own levels ell_i, original nonempty-coalition rewards are
r_i(S)=ell_i+Z_i(S), while original live and AllNever rewards remain zero.
Native Z is absorbing-reward bookkeeping, not a shift to live or Never.

**Theorem.** Every such original game has a uniform-equilibrium payoff,
against every independent complete behavioral replacement. The same delta
works for all the allowed row0 participant entries, grand coordinates and
own levels. There is no restriction on the ratio eta/beta. One fixed
payoff target is chosen before the approximation accuracy. The proof is
ordinary mathematics, not a new Lean-checked declaration.

Write lambda=eta/beta. We construct equilibria in overlapping ratio regimes,
then prove the uniform bounds needed to cover all positive ratios with one
rectangle. Every graph, continuation and scalar return is produced from the
displayed native rewards. All owner0 forced-Quit estimates use only its
proper-reward upper bound1 and grand-reward upper bound10; its prescribed
absorbing rewards are own-singleton or passive rewards. Only the solo2
operation uses a participant entry as a control parameter: write
alpha=Z0(02) and alpha_plus=max(alpha,0)<=1.

### Exact roots and their small-scale map

For q=(y,z,w), the hazards of owners1,2,3 with owner0 inactive, define

    Cbeta(q)_1=[eta(z+w-zw)-z+3w]/[(1-z)(1-w)],
    Cbeta(q)_2=[beta(y+w-yw)+2y+w]/[(1-y)(1-w)],
    Cbeta(q)_3=[eta(y+z-yz)-z+2y]/[(1-y)(1-z)],
    B_lambda(q)=(lambda(z+w-zw),y+w-yw,lambda(y+z-yz)).

The root q makes owners1,2,3 indifferent against Cbeta(q), and its active
output is beta*B_lambda(q). These exact rational formulas give a common
analytic local inverse of Cbeta near zero for small beta>=0, and hence

    Fbeta(q)=Cbeta^(-1)(beta*B_lambda(q)).

At beta=0 its value is zero; Fbeta/beta extends analytically there. Put

    A=[0,-1,3;2,0,1;2,-1,0], det A=-8,
    M=A^-1 DB_lambda(0)
     =[(lambda+3)/8,0,(3-lambda)/8;
       3(1-lambda)/4,-lambda,(3-lambda)/4;
       (1-lambda)/4,0,(lambda+1)/4].

Since DCbeta(0)=A+beta*DB_lambda(0),

    DFbeta(0)=beta*M*(I+beta*M)^(-1),
    Fbeta(q)=beta[Mq+O(beta||q||+||q||^2)].

All error bounds are uniform on a fixed small neighborhood for each fixed
lambda. Let A_lambda denote the y,w block of M, and put

    f(y,w)=3(1-lambda)y/4+(3-lambda)w/4.

Thus the leading normal update is z'=-lambda*z+f(y,w).

### A common macroscopic return curve

For a macroscopic triple root use the exact positive-beta formulas

    y_beta(w,z)=w[2eta-3beta(1-z)+z+3]
             /[2eta+3beta(1-w)(1-z)+2w-8z+10],
    u=Cbeta(y,z,w)_1, v=Cbeta(y,z,w)_3,
    a=(u-v)/3, r=(u+2v)/(3-u+v), p=3y-z+3w.

They give Cbeta(y,z,w)_2=2a exactly. At beta=0 the return equation
p=r/(1-r) has a unique increasing curve w=w0(z) on 0<=z<=7/40,
with 1/5<w<13/50 and positive u,v,a,r, all a,r<1. Clearing positive denominators reduces the return to P(w,z)=0, where

    P=6w^3z^2-12w^3z-30w^3
      -23w^2z^3+115w^2z^2-145w^2z-7w^2
      +8wz^4-141wz^3+863wz^2-1803wz+1205w
      +40z^4-250z^3+354z^2+70z-250.

On [1/5,13/50] times[0,7/40], the respective Bernstein coefficient bounds are

    7148926941/8000000 <= coefficients(P_w) <= 5993/5,
    -25549557/62500 <= coefficients(P_z) <= -2706231/20000.

These exact arithmetic certificates follow by rescaling the rectangle to
[0,1]^2: for power coefficients a_pq of a bidegree(n,m) polynomial, its
(i,j) Bernstein coefficient is
sum_(p<=i,q<=j) a_pq binom(i,p)/binom(n,p) binom(j,q)/binom(m,q).
Since Bernstein basis weights are nonnegative and sum to one, P_w>890
and P_z<-135 throughout the rectangle. The endpoint values are

    P(1/5,0)=-238/25,
    P(13/50,7/40)=5767817187/800000000>0,
    P(2519/10000,7/40)=-1601728151217/50000000000000<0,
    P(63/250,7/40)=5741313567/100000000000>0.

Hence the asserted increasing return curve exists and
2519/10000<w0(7/40)<63/250. Its v is positive: v=0 is equivalent to
w=b(z)=(5z-4z^2)/3, and

    P(b(z),z)=-(z-2)(z-1)(z+3)^2(4z-5)
                    *(32z^3-148z^2+167z-25)/9.

The last cubic increases on[0,7/40] and equals -17/125 at its right
endpoint, so the return curve cannot cross v=0. It starts with v>0.
The elementary rectangle bounds give u>v and 2u+v<3, hence 0<a,r<1.
The nonvanishing return derivative follows from P_w>890 and positive
cleared denominators. No strategic root is assumed.


The macro root is fully Nash against V=(0,u,2a,v) for small beta.
Owners1,2,3 are indifferent by construction. Owner0's Continue value is p,
while its forced-Quit value is at most (y+z+w)+10yzw. On the compact
macro rectangle, y is between1/20 and1/10, w between1/5 and13/50 and
z<=7/40, so p-(y+z+w)-10yzw=2y+2w-2z-10yzw>1/10.
At L=(0,r,0,r), the solo0 root of hazard a has output V. Owners1,2
Continue when eta,beta<=2, and owner3 Continues when eta*a<=v. The latter
holds for small beta because v/a has a positive compact lower bound.

A uniformly contracting physical small-root chain starting with norm O(beta)
always gives an actual fully Nash wash. Indeed its passive coordinate obeys

    p_next=3y-z+3w+(1-y)(1-z)(1-w)p.

If |p|<=Lbox, its change is at most(3+Lbox)||q||_1. Geometric hazard decay
makes the total change O(beta), so a first-exit bootstrap keeps p in a fixed
positive compact interval. Owner0's Quit endpoint is at most
||q||_1+10||q||_1^3, below that Continue value for small beta. Every root is
therefore fully Nash, and the limit is(S,0,0,0), with S=p_initial+O(beta).
Uniform convergence gives continuity. If the root maps and initial data are
C1 with derivative decay O(beta)^n, the same summable estimates give C1
convergence and the O(beta) bound in C1. These are actual backward roots,
used later only through finite truncations.

### A uniform strict cone on 0<=lambda<=27/50

Let A_lambda be the y,w block of M. Both its entries and both coefficients
of f are positive, since lambda<1. Direct multiplication gives

    f(A_lambda(y,w)) >= m_lambda f(y,w),
    m_lambda=(5-lambda)/8.                           (L6)

Indeed the two coefficient ratios are (lambda+15)/24 and
(5-lambda)/8, and the second is the smaller. Choose the SAME c=9/5
throughout0<=lambda<=27/50. Then

    c*m_lambda-1>=7/2000, 1-lambda*c>=7/250.

On the closed cone

    K_c={y,w>=0, 0<=z<=c f(y,w)}                     (L7)

the image under M obeys

    (1-lambda*c)f(y,w)<=Z'<=f(y,w)
                            <c f(A_lambda(y,w)).    (L8)

Both Y' and W' are strictly positive for every nonzero cone vector.
The inequalities have uniform strict linear margins on the compact slice
K_c intersect {||q||_1=1}. The exact analytic estimate for Fbeta above gives uniform constants radius>0, L<infinity
and beta_1>0 such that, for 0<beta<beta_1,

    q in K_c, ||q||_1<=radius
        implies Fbeta(q) in K_c,
                ||Fbeta(q)||_1<=L beta ||q||_1.     (L9)

Take beta_1 smaller so L beta<=1/2 and radius<1/4. Every nonzero image
lies in the strict interior, so all roots in the resulting infinite
backward iteration have proper positive hazards. Their total hazard norm
is at most twice the initial norm. This proves robustness of the cone
for the actual root map, with no limiting strategy yet executed.

Restrict the common macro family to z=0. Its return curve has a unique
w_* in(1/5,1/4), with y=3w/(10+2w) at beta=0. At positive beta,

    y_beta=w(3+2eta-3beta)/[10+2eta+3beta+(2-3beta)w].

The macro pair root outputs P=(p_beta,beta B_{lambda,beta}), where
p_beta=3(y_beta+w) and

    B_{lambda,beta}=(lambda*w,y_beta+w-y_beta*w,lambda*y_beta).

Its first small triple root is q_0=Cbeta^{-1}(beta B_{lambda,beta}). Hence
q_0/beta tends uniformly to (Y,Z,W)=A^{-1}B_{lambda,0} at beta=0.
These three coordinates are strictly positive for w in[1/5,1/4]. For
Z, note that Z=[3(y+w-yw)-lambda*w-3lambda*y]/4; it is already positive
at lambda=1, where it equals w(2-3y)/4. Positivity of Y,W follows from

    8Y=3(y+w-yw)-lambda(w-y),
    4W=(y+w-yw)+lambda(w-y), 0<y<w.

The initial vector lies uniformly strictly inside the SAME cone. Exact
algebra gives

    (9/5)f(Y,W)-Z=w*N(lambda,w)/[320(w+5)],
    N=18lambda^2*w+63lambda^2+233lambda*w-338lambda-15w+195.

On0<=lambda<=27/50 and1/5<=w<=1/4, N decreases in lambda; its minimum
is at(lambda,w)=(27/50,1/5), where N=675807/12500>0. Thus the actual
q_0 lies in the cone with a uniform linear margin, and ||q_0||_1<=C beta.
Use the fixed macro interval J=[1/5,1/4], whose return endpoint signs are
opposite and strict. All cone, macro-entry, passive and endpoint estimates
are now uniform over this entire closed ratio band, including lambda0;
no division by lambda is used.

The cone contracts the actual hazards by at most1/2, and the common
passive argument therefore produces a continuous axis limit S_beta(w),
uniformly p_0(w)+O(beta). Since the exact K_beta(w)=r/(1-r) converges
uniformly to K_0, the strict opposite endpoint signs on J give a root
S_beta(w)=K_beta(w). Fix that root before accuracy is chosen. All macro,
solo0 and small-root response inequalities have been checked above.

### Ratios 27/50 through 1: a produced invariant graph

Let s=(y,w), L(s)=[8(1-lambda)y+3(3-lambda)w]/(11lambda+7),
and n=z-L(s). The plane n=0 is invariant under M; its transverse eigenvalue
is -lambda. In these coordinates write

    Fbeta(s,n)=(f_beta(s,n),-nu_beta*n+R_beta(s,n)),
    nu_beta=lambda*beta/(1-lambda*beta)>0.

The tangent derivative is beta*A_lambda*(I+beta*A_lambda)^(-1), where
A_lambda is the y,w block of M. There is no first-order coupling to n.
R_beta and all its first derivatives vanish at the origin, and R_beta/beta
has uniformly bounded derivatives through order3 on a fixed neighborhood.
The same is true of (f_beta-Df_beta(0)s)/beta.

For this fixed lambda, choose a small ball D_rho in the s-plane. Consider
the closed class H of C^{1,1} functions h on D_rho with

    h(0)=Dh(0)=0, Lip(Dh)<=K.

Use the weighted C1 metric

    ||h-g||_* = max(sup |h-g|/|s|^2, sup |Dh-Dg|/|s|).

This class is complete: weighted convergence gives C1 convergence, and
the uniform Lipschitz bound on the derivative passes to the limit. Its
members satisfy |h(s)|<=K|s|^2/2 and |Dh(s)|<=K|s|.
Define the graph transform

    (Th)(s)=[R_beta(s,h(s))-h(f_beta(s,h(s)))]/nu_beta.  (H3)

For rho and beta small enough, f_beta(s,h(s)) remains in D_rho.
No inverse tangent map is used. All constants below come from finite
bounds on the displayed analytic maps, with lambda fixed.

For an absolute bound C_lambda enlarged as needed, the chain rule and
R_beta=O(beta |(s,n)|^2), D_n f_beta=O(beta |(s,n)|) give

    Lip(D Th)<=C_lambda/lambda
                   + C_lambda*K*(rho+beta)/lambda,
    ||Th-Tg||_*<= C_lambda*(rho+beta)/lambda * ||h-g||_*,
                                                               (H4)

provided K*rho<=1. To see the second estimate explicitly, the R difference
has weighted C1 size O(beta*rho)||h-g||_*. In the composition difference,
(h-g) evaluated at f has size O(beta^2)||h-g||_*; the shift from f_h to
f_g contributes the same order using Lip(Dg)<=K and
|f_h-f_g|<=C_lambda*beta*|s|*|h-g|. Division by
nu_beta>=lambda*beta yields (H4). The derivative-Lipschitz estimate is the
same chain rule using bounded second derivatives of the analytic maps and
Lip(Dh)<=K; no third derivative of the unknown h is assumed.

Choose K>4C_lambda/lambda, then rho>0 small enough, then beta>0 small
enough, so (H4) makes T preserve H and contract by at most1/2. Banach's
theorem produces a unique h_beta in H with

    h_beta(f_beta(s,h_beta(s)))
       =-nu_beta*h_beta(s)+R_beta(s,h_beta(s)).          (H5)

Thus z=L(s)+h_beta(s) is an actual invariant graph for the exact root map.
The graph is produced from the raw reward formulas. It is not assumed as
an input. Uniform contraction also gives continuous dependence on beta;
only boundedness of K and the estimates h=O(|s|^2), Dh=O(|s|) are needed
as beta tends to zero.

#### Physicality, including the Jordan endpoint

For lambda<1 the coefficients of L are strictly positive. A_lambda is
entrywise positive. Its exact beta transform has positive entries for all
small beta: its off-diagonal entries are those of beta*A_lambda divided by
det(I+beta*A_lambda), and its diagonal entries have positive first-order
terms. Shrinking rho, the graph lies in z>0 when y,w>=0 and y+w>0,
and f_beta maps that positive quadrant strictly into itself. All hazards
are O(rho), and ||Fbeta(q)||<=C_lambda*beta||q|| on the graph. Hence the
physical graph produces an infinite contracting triple chain.

At lambda=1, L(y,w)=w/3 and the tangent block is the Jordan matrix
[1/2,1/4;0,1/2]. There is nevertheless an exact invariant boundary:
q=(y,0,0) has Cbeta(q)=(0,(2+beta)y/(1-y),(2+beta)y/(1-y)), and

    Fbeta(y,0,0)=(beta*y/(2+beta+beta*y),0,0).           (H6)

The closed subclass h(y,0)=0 is preserved by (H3), so its unique fixed point
has this property. The derivative bound then gives

    |h_beta(y,w)|<=K(|y|+|w|)|w|.

After shrinking rho, z=w(1/3+O(y+w))>=w/6. The exact boundary (H6)
also gives w'=w*J_beta(y,w), where J_beta is continuous and
J_beta(0,0)=beta/(2+beta)>0. Its variation is O(beta*rho), so w'>0
for w>0. The y component is positive by its two positive tangent
coefficients and the same small-neighborhood estimate. Thus the endpoint
lambda=1 also has a produced physical invariant graph and contraction.

#### Uniformity through the endpoint from below

All constants in this paragraph are independent of lambda in the closed
interval and beta sufficiently small.

The rational root maps and their derivatives through order3 are jointly
analytic on one common neighborhood, since DCbeta(0) tends to the same
invertible matrix A uniformly in lambda. The normal-coordinate change
z=L_lambda(y,w)+n is smooth in lambda, and lambda>=27/50. Therefore the
C^{1,1} graph ball, its radius rho, derivative bound K and graph-transform
contraction factor1/2 can all be chosen uniformly. More explicitly, for any
h in that ball the same weighted-C1 chain-rule estimates give

    ||T_lambda h-T_1 h||_* <= C(1-lambda).

The divisions by nu=lambda*beta/(1-lambda*beta) do not cause a loss:
each nonlinear numerator and its parameter variation has a factor beta
and a quadratic zero in s. Banach parameter stability consequently gives

    ||h_beta,lambda-h_beta,1||_* <= 2C(1-lambda).       (U1)

Put kappa=1-lambda. At lambda1 the exact solo1 boundary gives
h_beta,1(y,0)=0. For y,w>=0 with y+w<=rho, (U1) and the derivative bound yield

    |h_beta,lambda(y,w)|
       <= C kappa(y+w)^2+K(y+w)w
       <= C' rho(kappa*y+w).

The coefficients of L_lambda satisfy

    L_y=8kappa/(11lambda+7)>=4kappa/9,
    L_w=3(3-lambda)/(11lambda+7)>=1/3.

Thus, after choosing one smaller rho, the physical height is uniformly
nonnegative, and is at least(kappa*y+w)/6. The allowed zero boundary is
lambda1,w0, where the exact solo1 identity applies.

For the tangential w component, write on the graph

    w'=[B_beta,lambda(y,w)]_w+E_beta,lambda(y,w),
    B_beta,lambda=beta*A_lambda*(I+beta*A_lambda)^(-1).

The remainder is quadratic. At lambda1 it vanishes identically on w0,
and the same parameter estimate and Hadamard factorization give

    |E_beta,lambda(y,w)|<=C'' beta*rho(kappa*y+w).      (U2)

One can obtain (U2) directly by comparing E_lambda with E_1: their difference
is O(beta*kappa*|s|^2), while E_1=O(beta*|s|*w). The graph's parameter
Lipschitz bound (U1) is sufficient; no derivative in lambda of h is assumed.
The exact matrix formula gives, for small beta,

    (B_beta,lambda)21>=beta*kappa/8,
    (B_beta,lambda)22>=beta/8.

Shrinking rho once more, w'>=beta(kappa*y+w)/16. The y row has two
uniformly positive coefficients of order beta; its quadratic remainder
is bounded by C beta*rho(y+w), so y'>0 for y+w>0. Hence the same graph
neighborhood is physical and invariant throughout the entire closed band,
including its degenerating positive-cone boundary at lambda1.

Uniform root contraction, passive bootstrap and C1 axis-limit convergence
now follow with common constants. The macro return curve and its v>0,
solo0 and owner0 margins are fixed compact data. The two shooting endpoint
signs have a uniform margin on lambda in[27/50,1], as witnessed by the
same exact Bernstein bounds and compactness. Thus the off-graph C1 extension,
return-curve continuation and final IVT all work for one beta_left>0 on
this whole closed band. This closes the uniformity issue at lambda1 from
below; pointwise physicality alone would not imply this conclusion.

Against any passive coordinate p in a fixed positive compact interval,
these small triple roots are fully Nash for small beta. Player0's forced
Quit endpoint is O(||q||), whereas its Continue value stays bounded away
from zero. Its successive changes are O(||q||); geometric contraction
makes their sum finite. The chain tends to (S,0,0,0), with S=p+O(||q_1||).
The limit is C1 in p and in the initial tangent coordinates: derivatives
of the iterates are bounded by (C_lambda*beta)^n, and the derivatives of
the summable passive increments obey the same bound. Uniformly for the
macroscopic inputs below, S=p+O(beta) in C1.

Let q1=Cbeta^(-1)(beta B_lambda(y_beta,z,w)). Write q1=(s1,n1) in the
plane/normal coordinates. Extend the passive limit off the invariant graph
by replacing n1 with h_beta(s1), retaining p. Denote that extension S_aux.
It is C1 and S_aux=p+O(beta) in C1. Thus the strict return derivative
produces a unique nearby curve w=w_beta(z) solving S_aux=r/(1-r).

On that return curve define

    D_beta(z)=[n1-h_beta(s1)]/beta.

It converges uniformly to

    D0(z)=Z-[8(1-lambda)Y+3(3-lambda)W]/(11lambda+7),
    (Y,Z,W)=A^-1 B_lambda(y0,z,w0).

At z=0 its exact expression is

    -3lambda*w*(lambda*w+9lambda+3w-19)
                         /[(11lambda+7)(w+5)]>0.

For general z the exact shooting expression is

    D0=lambda[lambda*Ap(w,z)+Bp(w,z)]
                   /[(11lambda+7)(-w+4z-5)],
    Ap=-3w^2z+3w^2+8wz^2-24wz+27w-44z^2+55z,
    Bp=3w^2z+9w^2+10wz^2+18wz-57w-28z^2+35z.

At z=7/40 and 2519/10000<=w<=63/250, Bernstein coefficients give
Ap>=56958332739/4000000000>0 and
(27/50)Ap+Bp>=4377331/62500000>0. The denominator is negative.
Thus D0<0 for every 27/50<=lambda<=1. Therefore D_beta has an exact zero
for all sufficiently small beta>0. At that zero q1 lies on the produced
physical graph, so the auxiliary limit is the actual triple-block limit.
All data a,r,u,v,S are fixed before approximation accuracy is chosen.


### Ratios above 1: a finite prefix and the exact pair contraction

The pair wash has critical surface and axis limit

    C(u,t,v)=t-Psi(u,v),
    Psi(u,v)=u/3+v+(9+4eta)uv/[3(6+5eta)],
    S(p,u,v)=6[p+u+3v/2+(12+5eta)uv/(2(6+5eta))]/[(3+u)(2+v)].

Its hazards are y=v/(2+eta+v), w=u/(3+eta+u). Let P denote the pair-root map. The exact identities are C(Px)=H C(x), H=(1-y)(1-w)>0, and S(Px)=S(x) on C=0. The owner2 Continue-minus-Quit gap on C=0 is

    g=(eta-beta)y+(eta/3-beta)w+(c eta^2+beta)yw,
    c=(9+4eta)/[3(6+5eta)].

The continuation caps satisfy u'=eta w and v'=eta y.

Write Sigma={C=0}. Owners1,3 are indifferent. Owner0 Continues since its pair passive
value is3(y+w), its Quit value is at most (y+w-yw), and its tail
coordinate is nonnegative. Owner2 Continues exactly when g>=0 on C=0.
The pair iteration is the exact rational contraction: u and v
contract to zero and its passive limit is the displayed rational S.

Let w_*=w0(0), y_*=3w_*/(10+2w_*), and define

    lambda_c=3(13-w_*)/(19+2w_*) in(1,2).

First consider1<lambda<lambda_c. The following finite leading prefix
will be continued to the exact positive-beta game.

Write A_lambda for the y,w block. Its characteristic polynomial is

    8x^2-(3lambda+5)x+2lambda.

For 1<lambda<2, its discriminant (lambda-1)(9lambda-25) is negative.

There is a particularly useful exact identity:

    f(A_lambda(y,w))-f(y,w)/2
      = -(lambda-1)[(lambda+3)y+(3-lambda)w]/32 < 0.

While f>0 and y,w>0, both coordinates after A_lambda remain positive. Indeed y'>0 and f>0 gives w>3(lambda-1)y/(3-lambda), which implies w'>0. The ratio r=w/y strictly decreases:

    r'-r = [2(1-lambda)+(lambda-1)r-(3-lambda)r^2]
             /[(lambda+3)+(3-lambda)r] < 0.

The numerator has negative discriminant in the stated lambda interval. Thus r cannot remain forever above the positive threshold 3(lambda-1)/(3-lambda); otherwise its decreasing limit would be a fixed point. Consequently the first index m with f(A_lambda^m(y,w))<=0 is finite. On any compact positive initial-ratio interval, m is uniformly bounded.

Put f_j=f(A_lambda^j(y,w)). Define

    Z_lambda(y,w)=sum_{j=0}^{m-1} (-1)^j f_j/lambda^(j+1),

where the empty sum is zero if f_0<=0. Starting from z_m=0 and solving backwards,

    z_j=(f_j-z_{j+1})/lambda,

gives z_j>0 for every j<m. The base case is z_{m-1}=f_{m-1}/lambda>0. For j<=m-2, use 0<=z_{j+1}<=f_{j+1}/lambda<f_j/(2lambda), and descend. Therefore the physical triple prefix hits z_m=0, and its next would-be z is f_m<=0. This final sign is exactly the leading pair-wash owner2 guard sign, with the sign reversed.

Z_lambda is continuous and piecewise linear homogeneous. At a phase boundary f_m=0, the m and m+1 sums agree because their extra term is zero. The phase boundary is simple in the ratio because A_lambda is invertible and f_m is a nonzero linear form. At such a boundary f_{m+1}<0 strictly, so no three phases meet.

This is a constructive first-boundary lemma; it does not infer a boundary hit merely from extinction of nested viability sets.

Restrict the common macro curve to0<=z<=1/8. Its right endpoint obeys
w0(1/8)<6/25 because P(6/25,1/8)=484659/1600000>0. The normalized
first triple output is

    B_lambda=(lambda(z+w-zw), y+w-yw, lambda(y+z-yz)).

Let (Y,Z,W)=A^(-1)B_lambda. We shoot the scalar

    D(z)=Z-Z_lambda(Y,W)

along the return curve. Y,W are strictly positive throughout the rectangle for 1<=lambda<=2. In fact w>y, and

    8Y=3(y+w-yw)-lambda(w-y)(1-z)>0,
    4W=(y+w-yw)+lambda(w-y)(1-z)>0.

At z=0, write w_*=w(0), y_*=3w_*/(10+2w_*), and

    lambda_c=3(13-w_*)/(19+2w_*) ~ 1.97653.

Then Z>0 precisely for lambda<lambda_c. Moreover

    Z-f(Y,W)/lambda
      = -w_*[18lambda^2 w_*+159lambda^2+41lambda w_*
              -434lambda-15w_*+195]/[64lambda(w_*+5)] > 0

for 1<=lambda<=2: the bracket is convex in lambda, with endpoint values 44w_*-80<0 and 139w_*-37<0. If f(Y,W)>0, Z_lambda<=f(Y,W)/lambda; if f<=0, Z_lambda=0. Hence D(0)>0 whenever 1<lambda<lambda_c.

At z=1/8, Z decreases with lambda and at lambda=1 is

    Z=-(328w^2-1235w+288)/[256(2w+9)]<0.

The numerator is decreasing on [1/5,6/25] and is positive at 6/25 (equivalently Z=-1093/252800 there). Hence D(1/8)<0 for all lambda>=1.

The intermediate value theorem now proves a legal LEADING finite triple prefix followed by pair wash for every 1<lambda<lambda_c. No eigendirection is assumed. The phase m may grow without bound as lambda decreases to 1, but is finite for each fixed lambda>1.


#### Exact contact and orientation

For the exact contact calculation use the same C,Psi,c and let T be the
continuation-to-output triple map. For any triple root set

    u0=(3+eta)*w/(1-w), v0=(2+eta)*y/(1-y),
    A=(1-eta-3*w)/(1-w), B=(1-eta-2*y)/(1-y),
    k=z/(1-z), H=(1-y)*(1-w).

Its input coordinates are u=u0-k*A, v=v0-k*B. Define

    L=A/3+B+c*(A*v0+B*u0),
    R=(1-w)/3+(1-y)+c*eta*((1-w)*y+(1-y)*w),
    J=-H*L/(1-z)+H*c*z*A*B/(1-z)^2
      -eta*R-c*eta^2*H*z.

Then direct expansion of the quadratic Psi gives the EXACT identity

    C(Tx)=H*C(x)+z*J.                                  (F2)

In particular J is smooth and J(0,0,0,eta)=-4/3 for every eta. Thus J<0
in a common small neighborhood for eta in a compact small interval.
The identity follows without a large polynomial calculation: compare
Psi(u0,v0)-Psi(u0-k*A,v0-k*B)=k*L-c*k^2*A*B,
and compare the triple output (u',v') with the pair output (eta*w,eta*y).

At z=0, the triple scalar root equation is precisely

    C(x)+g/H_pair=0,                                   (F3)

where g is evaluated at the pair hazards of the same input (u,v), and
H_pair>0. Write the row2 indifference equation as t=F(z); its derivative
F_z is positive near zero, and t-F(0)=C(x)+g/H_pair. Consequently the
signed triple hazard is zero on Sigma exactly where g=0; there T=P
and T maps the contact set back into Sigma.

#### The orientation of adjacent finite phases

Fix a compact interval of ratios lambda>1 and put eta=lambda*beta.
For E(x)=C(Tx), the derivative in t at the zero input is exactly

    E_t(0)=
    [6*beta*eta^2+9*beta*eta-15*beta+13*eta^2+35*eta]
    /[3*(eta-1)*(2*beta*eta+5*beta+3*eta+8)].            (F4)

It is negative whenever 0<beta<=eta<1. More usefully,
E_t/beta extends smoothly to beta=0 and has value
(15-35*lambda)/24<0 there. This extension is uniform in a neighborhood of
zero: after eta=lambda*beta, every active output of T is divisible by
beta, and therefore E/beta itself is a smooth rational function.
Hence E_t<0 for all sufficiently small beta and all sufficiently small
input states, uniformly on the compact ratio interval.

At a regular contact x*, assume C(x*)=g(x*)=0 and dg is nonzero in the
(u,v) plane. Take local coordinates (C,g,rho), where rho completes that
plane coordinate. Equation (F3) gives Z_C>0 and Z_g>0 for the signed hazard
z=Z(C,g,rho). From (F2), at the contact,

    E_g=J*Z_g<0, and E_C<0.

The implicit function theorem makes E=0 a graph C=chi(g,rho), with
chi(0,rho*)=0 and chi_g=-E_g/E_C<0 at the contact. On this graph (F2)
gives z=-H*C/J. Thus, after shrinking the neighborhood, the admissible
new sheet has g<=0, C>=0 and z>=0. The immediate pair sheet is C=0,g>=0.
They agree at g=0 and their union is one continuous local graph over
(g,rho). For a parameter-uniform version use g/beta and E/beta: both
extend smoothly, dg/beta has a nonzero limit in the (u,v) plane, and the
displayed derivative signs persist without an artificial coordinate singularity. This is the required gluing, not an inference from a numerical
intersection. Any earlier strict positive-hazard or Nash inequalities
remain strict on a sufficiently small neighborhood.


#### Continuing the finite sheets to positive scale

Fix 1<lambda<lambda_c and a compact positive (Y,W) neighborhood containing the macro curve. The leading first-forcing-crossing phase count is uniformly finite, say <=M. Use one exact chart throughout. Use the common hazard-to-continuation map Cbeta(q), and let T be the exact continuation-to-output triple map. Normalize actual next-root hazards as Q=q/beta=(Y,Z,W), so the actual input caps are Cbeta(beta Q). For every fixed phase m<=M the exact terminal condition is C(T^m(Cbeta(beta Q)))=0; divide it by beta^(m+1), not beta^m. This normalized equation is analytic in beta and Q. At beta=0 its derivative with respect to the initial Z is a fixed positive normalization factor times (-lambda)^m, hence nonzero. It therefore defines an analytic local graph for sufficiently small beta.

On an open phase interval, all preceding hazards and the terminal pair guard are strict, so physicality persists. At a phase interface, only two adjacent phases meet: the last prefix root has hazard2 zero, and the terminal pair guard zero. The exact identities T=P on this boundary, C(Px)=H C(x), and S(Px)=S(x) imply exact coincidence of their boundary curves and accumulated axis-limit values.

The exact contact calculation above supplies the opposite-side orientation.

The finite patching can be made explicit. The projective map r=w/y -> r' is increasing (det A_lambda=lambda/4>0), while r'<r until the forcing threshold. Thus the phase cells are ordered intervals in the initial ratio; adjacent cells meet on a single simple f_m=0 ray, and nonadjacent cells have disjoint interiors. On a compact positive (Y,W) domain there are finitely many such rays. The analytic graph from each cell extends across a small neighborhood of its boundary. Away from these neighborhoods all inequalities are strict and persist. At each boundary the exact local gluing lemma selects opposite sides of the two adjoining graphs, and the projected boundary is a small perturbation of its simple leading ray. Taking the neighborhoods disjoint prevents incompatible identifications. This produces one continuous piecewise analytic graph Z=Z_beta(Y,W), uniformly close to Z_lambda. Its phase labels are finite, its roots are physical, and its terminal first pair guard is nonnegative. The attached S is continuous because adjacent phase values agree exactly by pair invariance.

For the macro return, take coordinates (z,s) with w=w_0(z)+s and |s|<=epsilon, where w_0 is the common exact limiting return curve. Choose epsilon so small that the leading shooting residual is still positive on z=0 and negative on z=1/8, uniformly in s. The limiting return residual p-r/(1-r) has opposite nonzero signs on s=+epsilon and s=-epsilon by the strict w derivative. Define S off the exact shooting graph by vertical projection in normalized actual next-root hazard coordinates: replace Q_Z by Z_beta(Q_Y,Q_W), reconstruct continuation caps as Cbeta(beta Q_projected), and keep passive coordinate p unchanged. The actual first child Q is obtained as Cbeta^{-1}(beta B_lambda)/beta; thus graph definition and projection use the same chart. This extension is continuous and differs uniformly from p by O(beta), since the phase count is bounded and every later root is small. Define the shooting residual using the same exact next-root coordinates. Both face sign pairs persist for sufficiently small beta. Poincare-Miranda supplies a simultaneous zero of the two continuous residuals. At that zero the vertical projection is the identity, so the resulting return is an actual legal macro. This does not assume scalar shooting transversality or a differentiable return curve across phase corners.

The next estimates supply every later pair guard.


#### Later pair guards and the critical ratio

For lambda in (1,3), divide the exact guard by beta and then by w>0:

    g/(beta w)=(lambda-1)R-(1-lambda/3)+(1+c lambda^2 beta)y,
    R=y/w.

After one pair step,

    R'/R=(3+eta+eta w)/(2+eta+eta y).

In the small-cap terminal region, eta=lambda beta and y,w=O(beta), so this factor is uniformly >6/5 for beta sufficiently small. Both y and w contract by O(beta). A nonnegative initial guard implies

    R >= [(1-lambda/3)-(1+c lambda^2 beta)y]/(lambda-1).

For fixed lambda<3, choose beta small enough that the final term is at most (1-lambda/3)/12. Then R is at least 11/12 of the critical ratio, so the next ratio is at least 11/10 of the critical ratio; the next guard is strictly positive even after discarding its positive quadratic term. Thereafter R increases and all later guards remain positive. For lambda>=3 every guard coefficient is already nonnegative.

For the direct pair branch lambda>=lambda_c, the initial macro pair tail is not small; it needs a separate first-step check. At beta=0, its hazard ratio is y_*/w_*=3/[2(5+w_*)], and after one pair step the limiting ratio is 9/[4(5+w_*)]. At lambda=lambda_c this strictly exceeds the linear guard threshold:

    9/[4(5+w_*)] - 3(2+w_*)/[5(4-w_*)]
      =3(20-43w_*-4w_*^2)/[20(5+w_*)(4-w_*)] > 0.

Here w_*<1/4. The critical ratio decreases with lambda. Thus once the macro first guard is nonnegative, the next small-tail guard has a uniform strict margin near lambda_c and the preceding argument handles all later steps. For lambda>lambda_c choose specifically the local macro direct-pair return branch issuing from w_*: the critical pair equation eliminates y smoothly, and P_w(w_*,0)>0 makes its return equation an implicit-function branch for small beta. On this selected branch the macro first guard is strictly positive to first order. For lambda>=3 all coefficients are nonnegative.

At lambda=lambda_c, the direct-pair and first-triple branches meet at macroscopic z=0. The same gluing lemma applies there: at beta=0, keeping the tail u,v fixed, y_z=(1-y)(1-2y)/2 and w_z=(1-w)(1-3w)/3. The derivative of C(T)/beta with respect to z equals the derivative of (y+w-yw)-lambda(z+w-zw)/3-lambda(y+z-yz). On 0<=y<=1/12,0<=w<=1/4 this is at most 5/6-7lambda/6<=-1/3. Since t_z>0, the triple transverse derivative is negative. Exact invariance then patches the direct-pair sheet to the physical first-triple sheet just as for the small-tail phases.

For the macro return orientation at this join, define the leading next hazard

    Z(w,z)=[3(y+w-yw)-lambda(z+w-zw)-3lambda(y+z-yz)]/4.

At z=0, Z=(w+3y)[lambda_c(w)-lambda]/4 and lambda_c'(w)=-135/(19+2w)^2<0. Thus Z_w<0 at (w_*,0,lambda_c). Also

    Z_z=[3(1-w-lambda)y_z-lambda(4-w-3y)]/4<0,

because y_z>0 and lambda>=1. The first-triple critical branch Z=0 consequently has z'(w)=-Z_w/Z_z<0; its physical side is w<w_*. The direct-pair first guard is g/beta=-4Z(w,0)/3, so its physical side is w>w_*. Along the triple branch the derivative of the return polynomial is P_w+P_z z'(w)>0, while along the pair branch it is P_w>0. Therefore the actual return residual p-K decreases through the joined limiting curve on both sides. Choose w_* plus/minus a small fixed epsilon: the return signs are opposite and strict. The exact local sheet gluing and continuity preserve a connected physical curve with these signs for small beta, and an ordinary IVT gives the lambda_c return. This checks the return orientation, not merely the sheet incidence.


### A uniform hybrid contraction on 1<=lambda<=11/10

The next construction has one positive beta threshold for the entire closed
ratio band. It allows infinitely many active triple roots as well as a stop
onto the exact pair contraction, so no bound on the stopping index is needed.
In this subsection h_beta is defined as the critical pair height. The table
and original-game semantics remain those of the rectangle theorem.

#### Exact local maps and the axis identity

Write q=(y,z,w) for triple123 hazards. Its input core continuation is
R(q)=(u,t,v), where

    u=[eta*(z+w-zw)-z+3w]/[(1-z)(1-w)],
    t=[beta*(y+w-yw)+2y+w]/[(1-y)(1-w)],
    v=[eta*(y+z-yz)-z+2y]/[(1-y)(1-z)].

The output is Q(q)=(eta*(z+w-zw),beta*(y+w-yw),eta*(y+z-yz)).
The derivative of R at beta=0,q=0 is invertible. Thus F(q)=R^-1(Q(q))
is analytic on one common neighborhood for the entire lambda interval.
F/beta extends analytically to beta=0. Its leading derivative is

    F_base/beta=A_lambda*(y,w)+O((beta+|q|)|q|),
    F_z/beta=-lambda*z+f_lambda(y,w)+O((beta+|q|)|q|),

where

    A_lambda=[[ (lambda+3)/8,(3-lambda)/8],
       [ (1-lambda)/4,(lambda+1)/4]],
    f=3*(1-lambda)*y/4+(3-lambda)*w/4.

Let Psi(u,v)=u/3+v+c*u*v, c=(9+4eta)/(3(6+5eta)), and
C(u,t,v)=t-Psi(u,v). The exact pair contraction has critical surface C=0.
Solve C(R(y,h,w))=0 for h=h_beta(y,w). This is analytic; at beta=0,
h is identically zero, not merely zero to first order. Consequently

    f_beta(y,w)=-h_beta(y,w)/beta

extends analytically and f_beta=f_lambda+O((beta+|(y,w)|)|(y,w)|).
At lambda=1, the solo1 axis is EXACTLY invariant:

    h_beta(y,0)=0,
    F(y,0,0)=(beta*y/(2+beta+beta*y),0,0).

This identity is the reason estimates below are uniform as lambda tends to1.
Put x=(y,w), kappa=lambda-1, and use ||x||=y+2w.

Define the critical-height residual

    K_beta(x,z)=[F_z(x,z)-h_beta(F_base(x,z))]/beta.      (O1)

It extends analytically, with leading derivative -lambda in z and Df in x.
There is an EXACT positive factor a_beta(x), tending uniformly to1 near
beta=x=0, such that

    K_beta(x,0)=a_beta(x)*f_beta(x).                    (O2)

Indeed at z=0 the root is the pair root, so C(Q)=H*C(R). Write
C(R(x,z))=(z-h_beta(x))*J_beta(x,z), J_beta>0. Dividing this identity
at the input and output gives (O2), with a=H*J_input/J_output.
This exact proportionality removes the tilted-obstacle error.

#### Uniform local bounds on a physical wedge

Use the convex wedge

    D_lambda,rho={x>=0: kappa*y/4<=w<=2y, ||x||<=rho}.

All stopping continuations on this wedge are physical. If f_beta<=0,
h_beta>=0 and h_beta=O(beta*kappa*y)<=O(beta*w); hence R(x,h_beta)
has positive u,v for beta sufficiently small, except for the allowed solo1
axis at lambda=1,w=0. If f_beta>0 and 0<=z<=1.3f_beta, then
z<.66w<=1.32y, so R(x,z) also has nonnegative u,v.

There are uniform positive rho,beta0, with beta0<=1/100, such that the
following hold on the active part f_beta(x)>0, 0<=z<=1.3f_beta(x):

    .99<=a_beta<=1.01, |Df_beta|_*<=.26,
    -lambda-.01<=K_z<=-lambda+.01, |K_x|_*<=.26,
    ||D_x(F_base/beta)||<=.66,
    ||D_z(F_base/beta)||<=.01,
    F_base belongs to D_lambda,rho,
    ||F_base||<=.67*beta*||x||,
    f_beta(F_base)/beta<=.6*f_beta(x).                 (O3)

Here derivative norms use ||x||=y+2w and its dual. The last two assertions
are only needed on the displayed active sector.

For completeness, these are terminating local Taylor bounds, not extra
hypotheses. The weighted operator norm of A_lambda is at most103/160<.644,
and |Df|_*<=1/4. At lambda=1,w=z=0, every error in the w component and
in the scalar dissipation vanishes identically for all y,beta. Hadamard
factorization and uniform continuity therefore bound the corresponding
errors, with an arbitrarily small coefficient epsilon, by

    epsilon*(w+kappa*y+z).                             (O4)

Likewise |f_beta-f|<=epsilon*(w+kappa*y). Ordinary y-component derivative
errors have arbitrarily small coefficient times y+w+z. These facts follow
from the displayed analytic maps, their derivatives at zero, and the exact
axis identity; no strategic object is used to choose the neighborhood.

The strict dissipation needed in (O3) follows from the exact linear identity

    f(A_lambda x)=f(x)/2
       -kappa*((lambda+3)*y+(3-lambda)*w)/32.           (O5)

For f_beta>0, the error bound gives kappa*y<=.7w and
w<=2.2*f_beta+1.7*kappa*y, after shrinking epsilon. With z<=1.3f_beta,
(O4) is bounded by epsilon*(3.5f_beta+2.7kappa*y).
The negative term in (O5) is at least kappa*y/8. Choosing epsilon sufficiently
small gives the last inequality in (O3). Similarly
(A_lambda x)_w=(lambda*w+f(x))/3, so the active base remains positive.
The wedge margins are explicit:

    (A_lambda x)_w-(kappa/4)*(A_lambda x)_y
      =[-kappa*(12+kappa)*y+(16+6kappa+kappa^2)*w]/32
      >=.2375w,
    2*(A_lambda x)_y-(A_lambda x)_w>=.95y.

The first bound uses kappa*y<=.7w. The errors in its lower-face test carry
w+kappa*y, so these strict margins persist after shrinking the common
neighborhood. Thus the physical wedge is preserved. The remaining derivative inequalities
in (O3) have strict slack at zero and follow by uniform continuity.

#### A contracting obstacle operator

Let GraphSpace_lambda be the complete metric space of functions G on D_lambda,rho
with G(0)=0, weighted Lipschitz constant at most1, and

    0<=G(x)<=1.2*max(f_beta(x),0).

Use distance ||G1-G2||_*=sup_(x!=0)|G1(x)-G2(x)|/||x||.
Zero belongs to this space. Define U G=0 where f_beta<=0. Where f_beta>0,
solve uniquely for z in [0,1.3f_beta] the equation

    K_beta(x,z)=G(F_base(x,z))/beta,                   (O6)

and set (U G)(x)=z+beta*f_beta(x).

Existence, uniqueness and physicality are quantitative. At z=0 the left
side minus the right is at least (.99-1.2*.6)f_beta=.27f_beta.
At z=1.3f_beta it is negative. Every z difference quotient is at most-.99+.01=-.98, since G is only
Lipschitz; no differentiability of G is asserted. Its slope magnitude is
at most1.12, so the root lies between .24f_beta and (1.01/.99)f_beta. Thus U G is positive,
is at most1.2f_beta, and its actual triple hazard z is strictly positive.
The Lipschitz bound follows from implicit difference-quotient estimates

    Lip(z)<= (.26+.66)/.98<.94,
    Lip(U G)<=Lip(z)+beta*.26<1.

The zero extension across f_beta=0 is Lipschitz because these bounds persist
on each active component and U G tends to0 at the boundary. This proves
U maps GraphSpace_lambda to itself. If G1,G2 have roots z1,z2, the same strict
slope and the base-size bound give

    ||U G1-U G2||_* <=(.67/.98)||G1-G2||_*<.7||G1-G2||_*.

Banach contraction therefore produces one fixed graph G_beta,lambda.
Its physical triple hazard is H=G-beta*f_beta=G+h_beta on the active part.
On the stopped part G=0, the tail lies on C=0 and the pair guard is
nonnegative because h_beta>=0. More explicitly, at fixed u,v the local
virtual owner2 indifference tail t(z) is strictly increasing, with derivative
tending uniformly to4/3 at the zero-parameter origin; its z=0 excess t(0)-Psi is the negative pair guard divided
by positive opponent survival. Thus the sign of the virtual root h is
exactly the sign of the pair guard. Equation (O6) says that every active root's
output lies on the same graph. The map is a producer from raw beta,lambda.

Continuity in beta,lambda follows directly from the Picard iterates starting
at zero, whose convergence is uniform with factor .7. To compare varying
wedges use radial coordinate ||x|| and ratio w/y in[kappa/4,2]. The maps,
roots and zero extensions are jointly continuous in these coordinates.
Restricting to any smaller RADIUS rho_prime<=rho, with the same angular
wedge, gives the same fixed graph by uniqueness: active F strictly shrinks
the radius. The homogeneous comparison graph Z_lambda is the fixed point
of the leading operator, defined by

    U0 Z=0 when f_lambda<=0,
    U0 Z=(f_lambda-Z(A_lambda x))/lambda when f_lambda>0.

The active formula is nonnegative on its invariant graph class. No value
Z(A_lambda x) is evaluated on the stopped sector, where A_lambda x may leave the
wedge. The weighted contraction is uniform. At lambda=1 its fixed graph
is w/3; at lambda>1 it is the finite-prefix graph.

Here is a precise tangent comparison, rather than an assertion that arbitrary
nonhomogeneous operators converge under rescaling. On radius rho_prime,
insert the homogeneous fixed graph as a candidate, clipped if necessary to

    Z_tilde=min(Z_lambda,1.2*max(f_beta,0)).

It belongs to GraphSpace_lambda: Z_lambda has Lipschitz constant at most
(1/4)/(1-103/160)<1, and clipping preserves the larger Lipschitz bound.
Since 0<=Z_lambda<=max(f_lambda,0), clipping changes it in weighted norm
by O(beta+rho_prime). Homogeneity of Z_lambda and the displayed analytic
map expansions show that its clipped candidate has U_beta residual
O(beta+rho_prime). Where the signs of f_lambda and f_beta differ, both
candidate graph heights are themselves O((beta+rho_prime)||x||); elsewhere
the implicit slope bound applies directly. Uniform contraction now gives

    ||G_beta,lambda-Z_lambda||_* = O(beta+rho_prime).

Choose rho_prime=C*beta for a fixed compact set of X. Then
G_beta,lambda(beta*X)/beta=Z_lambda(X)+O(beta)||X|| uniformly in lambda.
Equivalently, finite rescaled Picard iterates converge to their homogeneous
counterparts, and the uniform .7 weighted contraction controls the remainder.

#### Every stopped pair continuation is legal, uniformly near lambda=1

At a stopped physical tail, let y,w now denote its actual pair hazards.
Write

    A0=eta-beta, B0=beta-eta/3, L0=beta+c*eta^2,
    g=A0*y-B0*w+L0*y*w>=0.

Shrink the common neighborhood so y<=1/16 and L0<=2beta. Since
B0>=19beta/30, g>=0 implies w<=2*(lambda-1)*y. In the exact pair-guard
recurrence

    g_next/y_next =
    [A0*(1+eta*(w-y))-L0*w*(2+eta*y)
      +(g/y)*(2+eta+eta*y)]/(3+eta+eta*w),

the numerator is at least A0*(1-9y-4y^2)>0 when lambda>1.
Both pair hazards decrease, so all later guards remain nonnegative.
At the zero state the root is idle and no division by y is used.
When lambda=1, the first guard forces w=0; every later pair root is solo1
and its owner2 guard is exactly zero. Thus the endpoint is included.

The stopped pair operation is used through its exact rational axis limit.
It need not remain inside the graph-transform wedge. Only active triple
outputs need that invariant wedge, and (O3) proves it.

#### The scalar return and actual finite profiles

Use the exact macroscopic first triple root and solo0 seam from the common macro construction. Their zero-beta return curve w=w0(z),
0<=z<=1/8, lies strictly between1/5 and1/4. The cleared return polynomial
has strictly positive w derivative, so the actual residual p-r/(1-r) has a
simple zero with opposite strict signs on the two sides. After the macro root, the next virtual triple hazards
are beta*(Y,Z,W)+O(beta^2); their base ratios lie inside the physical wedge.
Indeed on the macro rectangle write D=y+w-yw and E=(w-y)(1-z)>0. Then
W/Y=2*(D+lambda*E)/(3D-lambda*E), and y/w>=2/7 implies
lambda*E<D uniformly. Thus 2/3<W/Y<2 with strict uniform margins;
the lower wedge bound is only kappa/4<=1/40.
The actual virtual-hazard graph is H=G+h_beta=G-beta*f_beta. The exact
shooting residual is

    [q1_z-h_beta(q1_base)-G_beta,lambda(q1_base)]/beta.

For off-graph evaluation, project q1 to (q1_base,H(q1_base)). Its limiting
shooting residual is Z-Z_lambda(Y,W).

For the entire compact lambda interval[1,11/10], the earlier exact endpoint
calculations give uniformly positive residual at z=0 and uniformly negative
residual at z=1/8. At lambda=1 this also follows from Z_lambda=W/3.
Choose a thin fixed tube w=w0(z)+nu around the return curve. Its two nu
boundaries have opposite strict return signs; its two z boundaries have
opposite strict shooting signs. Both signs persist for small beta.
For evaluation off the shooting graph, project the small core tail onto
that graph. This is an auxiliary continuous map, and equals the actual tail
where the shooting residual is zero.

The resulting axis limit S is continuous. A precise truncation is useful:
initialize the truncated value with the rational pair-axis formula

    B(p,u,t,v)=6*[p+u+3v/2+(12+5eta)*u*v/(2(6+5eta))]
                       /[(3+u)(2+v)],

extended to every small tail by ignoring t. At stopped states use B; at
active states prepend one exact triple root and recursively evaluate the
previous truncation. At an active/stopped boundary h=G=z=0, that root is
exactly the pair root and its next state is stopped. Pair invariance gives
B(next)=B(current), so these finite truncations join EXACTLY continuously.
Active core hazards contract by O(beta), as do stopped pair hazards. The
uniform error after n active roots is O((C*beta)^n). Thus the continuous
truncations converge uniformly to the actual axis limit S. Truncating with
p alone would not supply this exact finite-stage continuity.
The Poincare-Miranda theorem on the (nu,z) rectangle supplies an exact
simultaneous return and shooting zero. All data are fixed before accuracy.

The macro root has strict owner0 slack for the row0 upper bounds. Later small roots have
passive0 value bounded away from zero, so their O(beta) Quit endpoints are
strictly lower after shrinking beta0. The solo0 and solo2 guards are the
previous explicit ones; their macroscopic hazards stay uniformly positive.
The hybrid backward chain and the solo2 backward chain are used only through
finite truncations. Their two seam errors tend to zero, while every player's
opponents absorb each finite period with a uniform positive probability.
The existing geometric full-cap argument gives vanishing unrestricted
terminal debt and a fixed limiting target, hence original UE.


### One scale threshold for all positive ratios

The preceding arguments provide uniform positive beta thresholds on closed
bands. This step records the uniformity, rather than inferring it from
separate pointwise conclusions.

The fixed cone c=9/5 directly supplies one beta_cone>0 on[0,27/50].
Its two invariant-cone margins and its macro-entry numerator have the
explicit positive lower bounds displayed above. This also contains the
small-ratio region lambda<=1/250 already covered by (Q3).

The parameter-Lipschitz graph argument explicitly supplies one beta_left>0
on[27/50,1], including the degenerating physical boundary at1. The obstacle
operator supplies one beta_obstacle>0 on[1,11/10], including its changing
stopping index and its endpoint1.

On the compact band[21/20,3], use the finite-sheet and direct-pair branches.
The first-forcing phase count is uniformly finite on compact ratio intervals
away from1. Each interior sheet and contact has a parameter-uniform analytic
chart; the exact lambda_c two-arm return remains transverse with strict
endpoint signs on a neighborhood of lambda_c. Direct-pair returns away from
that contact have strict first-guard and return margins. The later-guard
bounds are uniform on these compact neighborhoods. A finite subcover thus
gives one beta_middle>0 for the entire band, including lambda_c.

Finally, if lambda>=3, then eta>=3beta and the fixed-matrix pair corollary
applies directly whenever eta<=1/2. Its spectator caps hold because
beta<=eta, beta<=eta/3, and beta<=4eta/3+Cpsi*eta^2. Its remaining caps
are eta<=1, eta<=2, beta<=2 and Z3(03)=eta<=1/2. No upper bound on
lambda is used in this branch.

Choose delta smaller than1/2000 and than the four positive thresholds
beta_cone,beta_left,beta_obstacle,beta_middle. For every0<beta,eta<delta,
the ratio eta/beta falls into at least one of these covering regimes.
This proves a single uniform small-premium rectangle. All positivity and
derivative margins come from the displayed raw formulas, finite analytic
estimates, contracting operators and a finite compact cover.

### Actual finite strategies and one fixed original payoff target

In each branch the selected macroscopic data are fixed before accuracy.
The backward wash from V=(0,u,2a,v) tends to Q=(S,0,0,0), and the
selected return satisfies S=r/(1-r). In the cone and graph branches it
uses a macro root followed by an infinite contracting triple chain. In the
finite-prefix branch it uses finitely many triple roots followed by the
exact pair chain; the direct-pair case has no triple prefix. In the uniform
hybrid branch it follows the produced active/stopped graph, continuing
with triple roots or switching to the exact pair chain as specified there.

At L=(0,r,0,r), the solo0 root of hazard a outputs V. Its endpoint guards
were checked in the macro construction; the direct-pair branch retains
those strict solo0 guards from its nearby limiting macro. From Q use the
solo2 backward operation, at continuation(B,h,0,h), with hazard
k=B/(1+alpha_plus+B). Its output is

    (alpha_plus*k,k+(1-k)h,0,k+(1-k)h).

Owner0's Continue value alpha_plus*k is at least its actual Quit value
alpha*k. Owner2 is indifferent; owners1,3 Continue because eta<=1.
Writing rho=alpha_plus/(1+alpha_plus)<=1/2, its exact iterates are

    B_m=S rho^m/[1+S(1-rho^m)], h_m=(S-B_m)/(1+S),

so they tend to L. The first backwards solo2 hazard is S/(1+alpha_plus+S)>0.

Repeat the finite physical word consisting of solo0, the reversed finite
solo2 block, and the reversed finite wash from V toward Q. A finite triple
prefix is included intact; only the infinite contraction portions are
truncated. There are exactly two value seams, with total norm E tending
to zero. Every player's opponents absorb per word with probability at least

    delta_abs=min(a,S/(1+alpha_plus+S))>0.

Bellman telescoping gives prescribed payoff error at most E/delta_abs and
full behavioral regret at most2E/delta_abs. The bound counts seams, not
word length, and covers finite deadlines, Never and every complete private
behavioral law. Every unilateral replacement absorbs surely. Thus arbitrary
signed own levels shift payoff and full cap by ell_i exactly, without a
shift to original live or AllNever rewards. The fixed target is ell+V.
For each accuracy choose finite truncations; their geometric opponent
absorption then gives the uniform finite-horizon conclusion.

The scale thresholds are independent of all freely lowered row0 rewards:
only their upper bounds enter the response inequalities, and the solo2
control uses alpha_plus in[0,1]. The other three grand rewards and ell
are absent from all native root and own-replacement reward queries. The
finite-horizon threshold may depend on the magnitudes of the original finite
rewards; the uniform rectangle constant delta does not. This proves the
original-game theorem with every stated quantifier.

### Calibration outside the preceding displayed producer ranges

At lambda=1, choose any0<beta<delta, set all proper row0 participant
rewards equal to beta, set ell_i=1, and use the complete earlier calibration with e=h=beta and native
grand row(10,-2,-beta,-1). This table satisfies the new theorem. It fails
(Q3), since h/e=1>1/250; it fails(G5), whose reference-background kappa
is3/11200; and it fails the pair bound(P2), since
Z2(23)=beta>h/3. The earlier exact stationary, sure-owner/punishment-tail,
protected-player, ledger and every-proper-child obstructions all apply,
being uniform for0<e<=1/100 and0<h<=1/2000.

The new step excludes the entire stated open rectangle of positive premium
pairs, including every intermediate ratio. It does not close arbitrary
higher rewards, arbitrary singleton matrices, or the full Fin4 conjecture. A formalization can define the raw
homogeneous row1/2/3 table predicate with the independent row0 upper bounds,
and prove existence of delta>0 such that every0<beta,eta<delta gives an
original uniform payoff. Its new lemmas are the analytic root map, strict
cone, produced
C^{1,1} graph with physical boundary, finite phase/contact continuation,
the two simultaneous macroscopic equations, uniform parameter bounds,
the stopped/active obstacle contraction, and the finite-cover argument.
The common full-cap finite-calendar consumer above supplies the final semantic endpoint.

## Shared singleton-matrix source


This proves the matrix implication used by the signed-chamber theorem and
the pair-contraction theorem. No joint reward hypothesis is used. A Fin4
no-UE table supplies standard Q, R0 and LCP degree1 for its literal G,
and excludes every positive-inverse principal triple whose exterior inverse
row is nonnegative. The code interfaces are
`standardQMatrixSide_of_not_exists_uniformEquilibriumPayoff`
(`UniformEquilibrium/Quitting/Classification/LCP/CounterexampleNecessary.lean`),
`PassiveRowInverseCriterion.exists_uniformEquilibriumPayoff_of_raw_nonnegativeInverse_triple`
(`UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/RawPassiveRowInverseCriterion.lean`),
`normalCore_eq_univ_of_fourPlayer_not_exists_uniformEquilibriumPayoff`
(`UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/AmbientCarrierElimination.lean`),
`singleton_r0Degree_eq_one_of_no_uniformPayoff`
(`UniformEquilibrium/Quitting/Classification/LCP/SingletonDegreeCriterion.lean`),
and `exists_finset_r0Degree_eq_sum_sign_det`
(`MathUE/LinearProgramming/R0DegreeSum.lean`).

At offset -y with y>>0, a complementary root with active support S solves
G_SS*x_S=y_S, x_S>>0, and G_out,S*x_S>=y_out. Hold y1,y2,y3 in a fixed
compact positive box and send y0 to infinity. Proper supports containing0
are excluded as follows. A singleton cannot reach a positive active target;
pairs02 and03 have opposite reciprocal signs. Pair01 has outside row3 equal to -l*x0-d*x1<0, so it is impossible
regardless of the sign of g1. On triple012, row1 k*x0+x2=y1 bounds x0,x2.
Its outside row3 inequality -l*x0-d*x1+x2>=y3 then bounds x1 as well.
The active row0 cannot reach the unbounded target y0, regardless of the
signs of g1,h1. Triple013 has its active row3 equal
to -l*x0-d*x1<0 and is impossible.

For the remaining triple023, let

    T=[0,-g2,g3; A,0,-h3; -l,1,0],
    Delta_T=A*g3-g2*h3*l,
    adj T=[h3,g3,g2*h3; h3*l,g3*l,A*g3; A,g2*l,A*g2].

The adjugate is strictly positive. If Delta_T<0 the inverse is strictly
negative; if Delta_T=0 a positive left null vector rules out a strictly
positive target. If Delta_T>0, its exterior adjugate row1 is

    E=(-N, (k+l)*g3-c*g2*l, A*g3-A*c*g2+g2*h3*k).

If N<=0, then

    E2>=(k+l)*Delta_T/A>0, E3>=Delta_T>0,

so E>=0 and the excluded positive-inverse child produces original UE.
Consequently in the remaining Delta_T>0 branch N>0, and the coefficient
of y0 in the exterior value is -N/Delta_T<0. Its row1 inequality therefore
fails for large y0, uniformly over the bounded other target coordinates.

Supports omitting0 are also uniformly excluded. Otherwise a sequence of
such roots with y0 tending to infinity has unbounded sum norm. Pass to a
fixed-support subsequence, normalize by that norm and take a limit v.
It has v>=0, sum v=1, v0=0, Gv>=0, and v_i*(Gv)_i=0 for every i.
The active equalities at indices other than0 tend to zero after division;
the outside inequalities give the remaining nonnegative coordinates.
This contradicts R0. No nonsingularity of an unused principal matrix is needed.

Thus every complementary root at all sufficiently large y0 has full support.
Standard Q supplies such a root for every target in an open set, forcing G
to be invertible. The full-support root is unique and nonsingular; the degree
sum therefore gives sign(det G)=degree(G)=1. Dividing G^-1*y>>0 by y0 and
letting y0 grow gives v=G^-1*e0>=0. Its coordinate v0 is strictly
positive: otherwise Gv=e0 would be a nonzero homogeneous complementary
solution, contradicting R0. Hence C>0 by (G6). The same formula gives N>=0.

If N=0, then D=(k+l)*C/c and
Delta_T=h3*det(G)/C>0. Its exterior row E is nonnegative by the preceding
inequalities, giving the excluded child again. Hence N>0. The identity c*D-d*N=(k+l)*C now gives D>0. All four
coordinates in (G6) are strictly positive and det G>0, completing the source.

## Source correspondence and remaining task


The exact root identities and unrestricted response semantics were checked
against `quittingContinuationBestResponseValue_rootThenContinuation_eq_max`
in `UniformEquilibrium/Quitting/Root/TerminalDebtPrefix.lean` and
`IsQuittingBlockCertificate` in
`UniformEquilibrium/Quitting/Cycles/BlockPeriodicProfile.lean`.
The exact finite-block consumer there is not used to disguise an approximate
block as an exact certificate.

The existing endpoint is
`quittingGame_isUniformEquilibriumPayoff_of_terminalNash_tendsto` in
`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`:
our actual profiles have vanishing unrestricted terminal regret and converge
to the fixed target ell+V. No strategy-compactness or realization assertion
is needed. The finite raw tests, scalar root production, contraction bounds,
and two-seam estimates are new ordinary mathematics, not claimed as Lean
implementations of these declarations.

A Lean handoff can define raw predicates for the quantitative table box,
the signed-chamber threshold bounds, the pair-contraction bounds, and the
uniform small-premium rectangle. Each
intended theorem has the shape: the corresponding raw predicate on reward
implies existence of a target satisfying
`(quittingGame reward).IsUniformEquilibriumPayoff none target`.
Predicate fields contain only reward equalities, inequalities and the defined
raw scalar constants, with no continuation, equilibrium or strategic witness.
The new proof lemmas are the matrix source reduction, termination of the raw
finite searches, unique scalar root and invariant-cone estimates, continuous
limit and scalar return, exact pair identities, and the two-seam full-cap bound.
The existing terminal-Nash convergence consumer above supplies the semantic
endpoint after constructing the actual finite periodic profiles. These are
proposed formalization targets, not claims of checked implementations.

The remaining global task is to produce comparable blocks from arbitrary
surviving Fin4 data, or to find an unrestricted positive-gap table. Neither
is proved here.
