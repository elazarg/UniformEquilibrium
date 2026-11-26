# Shared-anchor rectangle degree for uniform equilibrium

This ordinary mathematical reward-table theorem counts one pair, both adjacent
triples and full support together. Multiple roots and either local index sign
are permitted. Cooperative comparisons on two outer edges control the total
index. The exact table below escapes the earlier independently assigned
pair--triple, individual orientation, charge, ledger and stationary producers.
No new Lean verification or full Fin4 solution is asserted.

## 1. Exact raw class

There are four players0,1,2,3, independent private Continue/Quit behavior,
finite absorbing rewards r_i(S) at the first nonempty quitter coalition, and
zero live and Never rewards. One player may replace its whole behavior law.
Put s_i=r_i({i})>=0, Z_i(S)=r_i(S)-s_i. For nonnegative odds z define

    Phi_i(z)=sum_(empty!=T subset I-i) z_T[r_i(T+i)-r_i(T)],
    R_i(z)=sum_(T subset I-i)z_T Z_i(T+i),
    z_T=product_(j in T)z_j.

Write d_ij=r_i({i,j})-r_i({j}) for a directed pair joining gap.

R_i is the positive denominator times the forced-Quit premium Q_i-s_i.
Name the odds(x,y,z,t) in player order(0,1,2,3). Require:

1. Pair02 is the only mutually positive participant pair:
   Z_0(02),Z_2(02)>0, and every other pair has a nonpositive participant
   premium at some owner. Its two joining gaps d02,d20 are strictly negative.
2. Supports013 and123 are product-low: every product root on that exact
   support has an active Q_i<=s_i. This is equivalent to absence of positive
   odds making every active R_i positive; sure boundaries follow by inward
   continuity of strict positive premiums.
3. The one-sure polynomial test below holds on012,023,I.
4. The capture, axis and rectangle tests below hold for some positive constants
   L1,L3,kappa0,kappa2 and nonnegative lambda1,lambda3.

For the one-sure test, fix a support S among012,023,I and h in S. Take any
product hazard vector with support S, q_h=1 and0<q_i<1 for i in S-h.
Let Q_i be its forced-Quit reward and P_i its forced-Continue absorbing
reward. If every active Q_i>s_i, require at least one of:

    some i in S-h has Q_i!=P_i;
    some k outside S has Q_k>P_k.                     (B)

All these quantities are explicit finite product polynomials. Every owner
other than h faces a sure opponent, so there is no continuation term in
these comparisons. Thus (B) is a finite raw reward test, not an assumed
statement about a strategic Nash root. Simpler uniform negative conditional
gap signs may be used to verify it.

Write the two anchor maps exactly as

    Phi0=F0(y,t)+P0(y,t)z,
    F0=d01*y+d03*t+B0(013)*yt,
    P0=d02+B0(012)*y+B0(023)*t+C0*yt;

    Phi2=F2(y,t)+P2(y,t)x,
    F2=d21*y+d23*t+B2(123)*yt,
    P2=d20+B2(012)*y+B2(023)*t+C2*yt,

where B_i(S)=r_i(S)-r_i(S-i) and C_i=r_i(I)-r_i(I-i).
Require every nonconstant coefficient of P0,P2 to be nonpositive. Their
negative constants then make both denominators strictly negative everywhere
on the nonnegative free quadrant.

The capture implications are: for EVERY x,z>0,y,t>=0 with y+t>0,

    R0,R2>0, (y>0 implies R1>0), (t>0 implies R3>0)
      IMPLY y<L1, t<L3, Phi0<0, Phi2<0,
        and additionally
        y>0 implies Phi2<−kappa2,
        t>0 implies Phi0<−kappa0.                     (C)

Thus full support forces both deep bounds, while each triple forces only
one. Two triples at the same source will supply both bounds together.
These implications do not require a Nash equation or a supplied annotation.

The two axis tests are literal raw conditions, independent of any Nash root.
For a point(x,y,z,0) with x,y,z>0 and R0,R1,R2>0 put a=Phi0,c=Phi2.
For every0<u<y, require that the anchors(1) at(u,0) are positive and all
three premiums R0,R1,R2 there remain positive. Impose the symmetric condition
on every high point(x,0,z,t), at every0<u<t along(0,u). This is BACKWARD
HEREDITY at fixed anchor levels. The negative denominators make these
finite rational, equivalently polynomial, inequalities. Capture(C) already
gives a,c<0 and therefore a positive proper pair anchor at the lower endpoint.

For a polynomial K define the two cleared fiber derivative operators

    D_y K=P0P2 partial_y K
           -P0 partial_x K partial_y Phi2
           -P2 partial_z K partial_y Phi0,
    D_t K=P0P2 partial_t K
           -P0 partial_x K partial_t Phi2
           -P2 partial_z K partial_t Phi0.

Require, on the respective high-premium axis domains,

    t=0, x,y,z>0, R0,R1,R2>0
                     IMPLY D_y(Phi3-lambda1 Phi1)>=0;
    y=0, x,z,t>0, R0,R2,R3>0
                     IMPLY D_t(Phi1-lambda3 Phi3)>=0.  (H)

The constants lambda1,lambda3 are nonnegative. These are reward-polynomial
tests; twelve-coefficient signs after a proved anchor threshold are one
optional way to certify them. Neither strict monotonicity nor a particular
certificate-search method is assumed.

On the closed rectangle R=[0,L1]x[0,L3], require

    F0+kappa0>0, F2+kappa2>0.                          (A)

Consequently, for EVERY a<=−kappa0,c<=−kappa2, the explicit anchors

    X(y,t)=(c-F2(y,t))/P2(y,t),
    Z(y,t)=(a-F0(y,t))/P0(y,t)                         (1)

are strictly positive and finite throughout R. Define the cleared polynomials

    Cf=P0 P2 partial_t Phi1
       -P0 partial_x Phi1 partial_t Phi2
       -P2 partial_z Phi1 partial_t Phi0,
    Cg=P0 P2 partial_y Phi3
       -P0 partial_x Phi3 partial_y Phi2
       -P2 partial_z Phi3 partial_y Phi0.

The edge tests are

    y=L1, 0<=t<=L3, x,z>0, Phi0<=−kappa0, Phi2<=−kappa2
                                      IMPLY Cf>=0;
    t=L3, 0<=y<=L1, x,z>0, Phi0<=−kappa0, Phi2<=−kappa2
                                      IMPLY Cg>=0.    (E)

These are finite polynomial implications on reward data and real variables.
Positive coefficient certificates, interval positivity certificates, or
quantifier elimination can verify them. The theorem does not assume a
numerical continuation scan or completeness of any chosen certificate search.
Full-rectangle cross signs are sufficient but unnecessary.

**Theorem.** Every table satisfying these raw tests has one uniform-equilibrium
payoff target, fixed before accuracy, against all complete unilateral
behavioral deviations. Its native table has absorbing full-debt infimum zero;
every nonnegative recipient-row raise of that native table also has UE.
The result is a sufficient class, not an arbitrary Fin4 theorem.

## 2. Cooperative rectangle index lemma

Let u=f-b,v=g-d be C1 near[0,A]x[0,B]. Suppose u_t>=0 on the right edge
and v_y>=0 on the top edge. Suppose the lower complementarity displacement

    V=(y-max(0,y+u),t-max(0,t+v))

has no zero on the top/right edges. Use the given C1 extension of u,v at
negative coordinates. Its degree on(-epsilon,A)x(-epsilon,B)
is nonnegative. At regular roots this means

    -1_(origin root)
    +sum_(bottom roots) sign f_y
    +sum_(left roots) sign g_t
    -sum_(interior roots) sign det D(f,g) <=0.          (2)

Here lower-axis roots retain the other coordinate's full quiet inequality.

Proof first under strict genericity on all four edges and corners. Clip the
map(y,t)+(u,v) into the CLOSED rectangle. Its total fixed-point index is+1.
The index I off the top/right faces is the negative of the left side of(2).
Put a=u(A,B),b=v(A,B), nonzero. Right-edge fixed points are accepted where
u(A,t)>0; this is a terminal interval by monotonicity. Include its lower
corner if u(A,0)>0,v(A,0)<0. The signed scalar crossing count gives

    U_right<=1_(a>0,b<0).

Indeed if a<0 there are no accepted points. If a>0 and the interval starts
at zero, its index sum is1_(b<0). If it starts at s>0, no boundary common
zero gives v(A,s)!=0 and the sum is(sign v(A,s)-sign b)/2. The same argument
on top gives U_top<=1_(b>0,a<0). The upper-corner index is1_(a>0,b>0).
These three indicators are mutually exclusive, hence total upper index<=1.
Thus I=1-U_upper>=0, proving(2). No own-axis derivative sign or interior
determinant sign has been used.

Remove artificial genericity by small CONSTANT shifts of u,v. They preserve
cross monotonicity and, by compactness, absence of upper/right displacement
zeros. Avoid the finitely many corner values, one-dimensional boundary
critical values, edge common-zero images and two-dimensional critical values.
The shifted map has the preceding regularity. Degree is unchanged along the
small-shift homotopy; on the extended left/bottom boundary one displacement
coordinate is strictly negative. This proves the assertion without any
unproduced artificial-boundary regularity assumption.

## 3. Full game, source production and global degree

At an annotation v the exact endpoint gap is

    Q_i-C_i=H_i(s_i-v_i+Phi_i),
    H_i=product_(j!=i)(1-q_j),

when all hazards are proper. A root is bad if every successor exceeds its
own singleton. At a used proper action its Quit premium is then positive.

Split off any full Nash root with at least two sure quitters: every deviator
still faces a sure opponent, so this single first-date root is an actual
absorbing all-behavior equilibrium, independent of its annotation. Otherwise
no such root exists. Low handles013 and123 including their boundaries.
Bad pair roots must be02; a one-sure02 root would force the other owner's
nonzero joining gap to vanish. Test(B) excludes every remaining one-sure
bad root. Thus under an all-bad contradiction every root is proper on
one of02,012,023,I. Singleton roots cannot be bad.

Choose a generic annotation below at least one own singleton. One dense set
avoids critical values of all active-support polynomial maps, including full
support, and all
inactive-tie images. Critical values are null: on compact cubes a polynomial's
bounded second derivative puts the image near a critical point in a rotated
box with one side O(h^2) and the others O(h); summing O(h^-m) cubes gives
volume O(h). An inactive tie is a polynomial image from three source variables
to four annotation coordinates, also null by Lipschitz cube covers. Finite
supports and countable exhaustion give density. Thus proper Nash roots are
regular with strict quiet inequalities. Under the all-bad hypothesis the
closed compact root set is finite.

Suppose all roots are bad. AllContinue is not Nash at the strict source
deficit. If no higher support occurs, only the at-most-one proper02 root
remains, of index-1, contradicting total cube degree+1.

There are two cases. If a full-support root occurs, (C) gives both native
offsets a=v0-s0<−kappa0 and c=v2-s2<−kappa2. If both triple families occur,
012 supplies the bound on c and023 supplies the bound on a for this SAME
source. In either situation every higher bad root lies strictly inside the
upper edges of R. The pair is at its lower corner. Condition(A) supplies
positive literal anchors(1) on the ENTIRE rectangle. Put
f=Phi1(X,y,Z,t),g=Phi3(X,y,Z,t),b=v1-s1,d=v3-s3.

Every zero of the reduced lower complementarity equations is a full Nash
root: anchors are indifferent, and both free owners satisfy their complete
active or quiet comparisons. An upper/right zero would therefore be a Nash
root violating strict capture(C), hence a good low successor, contrary to
the all-bad hypothesis. No root is discarded because of a low premium.
Conversely every bad root belongs to this same rectangle and anchor chart.

Implicit differentiation gives P0P2 f_t=Cf and P0P2 g_y=Cg. As P0P2>0,
test(E) supplies exactly the cooperative edge inequalities in Section2.
The transverse anchor derivative has determinant- P0P2<0. The full ambient
indices are therefore pair-1, triple sign f_y or sign g_t, and full support
-sign det D(f,g). Quiet coordinates retain their identity derivative block.
Their total is nonpositive by(2), contradicting the full clipped Nash-map
degree+1.

It remains that exactly one triple family occurs and no full-support root
occurs. Suppose it is012; the other case is symmetric. Capture gives a,c<0.
Fix these anchor levels. Backward heredity makes the positive-R0,R1,R2 part
of the rational fiber(X(y,0),y,Z(y,0),0) one initial interval. Write
f(y)=Phi1 and psi(y)=Phi3 on that fiber. Test(H) gives nondecreasing
h=psi-lambda1 f because P0P2>0. At a triple root f=b, the strict quiet
condition is h<d-lambda1 b, retaining an initial interval of admissible roots.
At its proper pair anchor y=0, the quiet1 condition is b>=f(0).

If b>=f(0), any triple root y* gives

    psi(0)-lambda1 f(0)<=h(y*)<d-lambda1 b.

Nonnegativity of lambda1 therefore gives psi(0)<d, so the pair is full Nash.
Equality b=f(0) would give an inactive tie, excluded at the generic source.
Hence the pair occurs precisely when b>f(0). The Schur complement gives
triple index sign f'(y). Cut the admissible interval after its last regular
root; scalar crossings sum to1_(f(cut)>b)-1_(f(0)>b). Adding the pair's
-1 when present gives1_(f(cut)>b)-1<=0. The cut is interior, so no limiting
upper endpoint has been assumed. This counts every root in the remaining
one-triple/pair case. It too contradicts cube degree+1. A good successor
must exist in every case; the pair index has never been spent twice.

The full cube degree is+1 because the clipped endpoint map takes values in
the cube; its homotopy to the constant half-vector has no fixed point on
the boundary of(-1,2)^4. This is a full four-player calculation, not an
induced-face Nash argument.

## 4. Uniform endpoint and native absorption

Define K=sum_(S nonempty,i)|r_i(S)|, the canonical `quittingRewardBound`
from `UniformEquilibrium/Quitting/RewardBound.lean`. Choose B=K+1; it is
strictly above every reward magnitude and below K+2. The argument applies to every
generic boxed source below an own singleton. Compactness and closed Nash
inequalities extend the good-successor conclusion to every such boxed source.
The limiting root cannot be AllContinue at a strict deficit. The existing
`exists_uniformEquilibriumPayoff_of_selectedSingletonSublevelReturn_of_reward_bound`
in `UniformEquilibrium/Quitting/Classification/Existence/SelectedSingletonSublevelReturnUniformPayoff.lean`
supplies the original all-behavior UE with one fixed target.

All raw conditions are unchanged by a nonnegative recipient-row raise of
the native table: participant premiums and joining polynomials stay fixed,
and(B) uses only comparisons facing a sure opponent. Apply the theorem
with strictly positive own raises c_i. For an actual profile, write U_i for
payoff, B_i for the full deviation supremum, D=sum(B_i-U_i), and nu for
original joint Never. Native own-zero rewards make finite deadlines converge
to Never, so

    B_i^(Z+c)=B_i^Z+c_i,
    D_(Z+c)=D_Z+nu sum_i c_i.

The exact declaration
`quittingTerminalDebtSumInf_pos_iff_not_exists_uniformEquilibriumPayoff` in
`UniformEquilibrium/Quitting/Terminal/TerminalDebtSumInf.lean`
produces profiles with both D_Z and nu tending to zero. Move the smallest marginal Never mass, at mostnu^(1/4),
to a finite date. Four prescribed payoffs and three full caps change by at
most twice the reward bound times that mass; the changed owner's cap is
unchanged. Hence the absorbing debt is at mostD_Z+14 max(1,max|Z|)nu^(1/4),
proving A_Z=0. Every nonnegative row raise preserves debt on these absorbing
profiles. The fixed-target consumer is
`quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors` in
`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`.
Before absorption the only live public history is repeated all Continue.
Every complete behavioral replacement is a mixture of pure deadlines and
Never; these full-cap comparisons cover all of them. No strategic witness
is left assumed.



## 5. Complete separating table and actual cap geometry

All own singleton rewards are one; live play and perpetual Continue pay zero.
This is the COMPLETE original table, in recipient order0,1,2,3. Write
Z_i(S)=r_i(S)-1 on nonempty coalitions.

| S | r(S) |
| --- | --- |
| 0 | (1,0,4,0) |
| 1 | (0,1,0,4) |
| 2 | (4,0,1,0) |
| 3 | (0,4,0,1) |
| 01 | (-1,1,1,1/10) |
| 02 | (2,3/2,2,3/2) |
| 03 | (11/10,1/10,1,-3) |
| 12 | (1,-3,1,1/10) |
| 13 | (-9,0,-9,0) |
| 23 | (1,1/10,-1,1) |
| 012 | (-9,2,-9,-20) |
| 013 | (-9,0,-9,0) |
| 023 | (-9,-20,-9,2) |
| 123 | (-9,0,-9,0) |
| 0123 | (-10,0,-10,0) |

### Finite verification of the raw hypotheses

In odds(x,y,z,t), let D=2+10(y+t)+yt. Directly from the complete table,

    Phi0=-y+11t/10-Dz, Phi2=y-t-Dx,
    Phi1=x-3z+xz/2-4t-t(x+z)/10+20xzt,
    Phi3=-3x+z+xz/2-4y-y(x+z)/10+20xyz,
    R0=z-2y+t/10-10yz-10yt-10zt-11yzt,
    R1=xz-4z-t-xt-zt-xzt,
    R2=x-2t-10xy-10xt-10yt-11xyt,
    R3=xz-4x-y-xy-yz-xyz.

Pair02 is the sole mutual-positive pair, with joining gaps(-2,-2).
Supports013 and123 are Low using owner3, whose participant premiums on
each are nonpositive. For(B), a sure anchor gives the other anchor a
strictly negative conditional gap with numerator-D. A sure owner1 gives
proper owner0 numerator-1-10z-zt<0; a sure owner3 gives proper owner2
numerator-1-10x-xy<0. Thus no one-sure bad root is possible.

Take L1=L3=1/10, kappa0=kappa2=8, lambda1=lambda3=0. Positive R2 gives
y+t<1/10. If y>0 and R1>0 then x>4, forcing Phi2<-8; if t>0 and R3>0
then z>4, forcing Phi0<-8. On the left axis Phi0<0 directly, while on
the right Phi2<0 directly. This proves the entire split capture test(C).
The two anchor denominators are-D with negative coefficients. On the
square, F0+8 and F2+8 are at least79/10, proving(A).

For backward heredity on012, at fixed native source levels a,c<0 the anchors
are x=(-c+y)/(2+10y), z=(-a-y)/(2+10y). They decrease until a supplied
high point, since c<-8. The divided premiums

    R0/z=1-10y-2y/z, R1/z=x-4, R2/x=1-10y

all decrease, so positivity persists backwards to zero. On023 the anchors
are x=(-c-t)/(2+10t), z=(-a+11t/10)/(2+10t), again decreasing because
a<-8. Here R2/x=1-10t-2t/x and R3/x=z-4 decrease, while
R0/z=1-10t+t/(10z)>0 whenever t<1/10. This proves both hereditary tests.

Write C=Cf/D,G=Cg/D. These are polynomials. On t=0, substitute x=4+u into
G. It is affine in y; its coefficients in(uz,u,z,1) at y=0,1/10 are

    (30,293/10,1103/10,526/5),
    (10,273/10,323/10,466/5).

On y=0, substitute z=4+v into C. Its coefficients in(xv,x,v,1) at
t=0,1/10 are

    (30,2207/20,293/10,1049/10),
    (10,651/20,273/10,92899/1000).

All coefficients are positive. Affine interpolation proves both(H) tests
on the whole required intervals.

At deep source levels a,c<=-8 the anchors on the square are at least
790/401>19/10. Substitute x=19/10+u,z=19/10+v into C,G. Each is bilinear
in y,t. The following tuples are the coefficients in(uv,u,v,1):

| (y,t) | C | G |
| --- | --- | --- |
| (0,0) | (30,947/20,863/10,26667/200) | (30,863/10,473/10,6677/50) |
| (0,1/10) | (10,231/20,463/10,28757/500) | (499/10,12431/100,8491/100,201379/1000) |
| (1/10,0) | (499/10,2124/25,12431/100,100587/500) | (10,463/10,113/10,2867/50) |
| (1/10,1/10) | (297/10,2439/50,8393/100,124591/1000) | (297/10,8393/100,4853/100,124417/1000) |

Every entry is positive. Bilinear interpolation proves the cooperative
signs on the entire square, hence both outer-edge tests(E). All raw
hypotheses are supplied; the theorem gives original UE and native A_Z=0.

### Full-support obstruction to the earlier raw tests

For positive odds z define the premium and joining numerators

    R_i=sum_(T subset I-i)z_T Z_i(T+i),
    Phi_i=sum_(empty!=T subset I-i)z_T[Z_i(T+i)-Z_i(T)].

At odds(x,y,z,t)=(41/10,1/1000,41/10,1/1000), direct calculation gives

    R=(40160449/10^7,38399/100000,40159449/10^7,38399/100000)>0,
    Phi=(-82819041/10^7,26819/50000,-82820041/10^7,26819/50000),
    det D Phi=799791091999281517359/2500000000000000>0.

At annotation v=1+Phi, all four proper hazards are indifferent and their
outputs exceed their own singletons. This is an isolated full four-player
Nash root of ambient index+1. The native passive-payoff box is

    [-10,3] x [-21,3] x [-10,3] x [-21,3],

and Phi lies strictly inside it. Thus the obstruction cannot be dismissed
by imposing these actual-response coordinate bounds. Membership in this box
does NOT assert that v is an actual prescribed payoff U. Every native
reward vector and Never satisfy4w1+4w3-w0-w2<=14, whereas Phi gives
104274741/5000000>14; the original v violates the corresponding bound20.
This excludes prescribed-payoff realization only. A vector of full behavioral
caps B need not lie in that convex hull, so this calculation does not exclude
B=v. Section6 proves this distinct cap realization exactly.

This same point defeats full-support Low and individual negative Orientation.
After ANY positive recipient scaling lambda, its R entries and determinant
retain their strict signs. Full-support Charge also fails for every scale:
its required nonpositive pair coefficient is instead

    P_I(02)=lambda1 Z1(012)+lambda3 Z3(023)=lambda1+lambda3>0.

Consequently every earlier independent support assignment leaving full
support to Low, Charge or individual negative Orientation fails, including
those permitting distinct pair--triple repairs on proper supports. No
choice of pair roles, charge constants, support labels or positive row
scales repairs this full-support obstruction. The only mutually positive
participant pair is02, with joining gaps(-2,-2).

### No stationary profile, including every boundary support

A stationary profile uses one fixed independent hazard vector at every date.
All Never fails because a lone immediate Quit earns one. A sole active owner
is defeated by its successor on0->1->2->3->0: the successor's native Never
payoff is-1, its participant premium is nonnegative, and its joining gain is
respectively(1,1,1,11/10).

There is no Nash root with a sure quitter, even at an arbitrary continuation.
If owner0 is sure, owner2's four conditional joining gaps are
(-2,-10,-10,-1), so owner2 Continues. Owner3 then faces gaps(-3,-1/10),
so Continues; owner1 has gap1 and Quits surely. Owner0 now has gap-1 and
strictly prefers withdrawal. Sure2 is symmetric, with owners0,1,3 in place
of2,3,1. These contradictions do not depend on a continuation payoff.

It remains to consider sure owners among1,3 with both anchors0,2 proper.
If1 alone is sure, write z,t for the proper odds of2,3. Owner0's conditional
gap has the sign of-1-10z-zt<0, forcing0 quiet. Owner3 then has gap of
sign-4-z/10<0, forcing3 quiet. Owner2 must Quit surely, returning to the
excluded anchor case. The case of3 alone sure is symmetric: force2 quiet,
then1 quiet, then0 sure. If BOTH1,3 are sure, the anchor gaps are exactly
-q2 and-q0. Therefore the anchors cannot both be active. If q0=0, owner3's
gap is-4(1-q2)-q2/10<0. If q0>0, then q2=0 and owner1's gap is
-4(1-q0)-q0/10<0. Both contradict a sure action.

These same cascades exclude every persistent-base/free-set/induced-root
selection, including arbitrary punishment tails: a singleton sure base
triggers the cascade, and a larger sure base already faces the two-sure
contradiction. This is stronger than excluding stationary repetition of
one selected induced row.

A proper stationary pair ij must satisfy q_j Z_i(ij)=Gamma_ij, where
Gamma_ij=Z_i({j}). Pairs01,12,23 have a zero participant entry against a
nonzero singleton. Pairs03,13 require a negative hazard ratio; pair02
requires ratio3. Thus every pair support fails.

For a proper triple use odds. Let D_i be the product of1+odds of the
other two active owners, R_i its native participant numerator and P_i its
native passive numerator. Stationary indifference requires

    E_i=(D_i-1)R_i-D_i P_i=0.                         (W1)

On012 in order(0,1,2), and023 in order(2,3,0), write the odds(x,y,z).
In both cases the first owner's residual is

    E0=y(1-y)-3z-10y²z²-11y²z-12yz²-3yz-2z².

Hence E0=0 forces0<y<1 and0<z<y(1-y)/3<=1/12. The middle owner's
residual, identical on both triples, is

    E1=[(z²+3z+2)x²+(2-5z-5z²)x+2z-6z²]/2>0.

Every coefficient is positive on that interval; the linear coefficient is
at least223/288. Thus neither triple is stationary.

On013 use odds(x,y,z) in order(0,1,3). The first owner's residual is

    10E0=-10y²(z+1)+y(11z²+101z+10)+11z²+10z.

For0<y<=1 this is at least y(11z²+91z)+11z²+10z>0, so stationarity
forces y>1. On123 in order(2,3,1), the first owner's residual is

    E0=-y²(z+1)+y(z²+10z+1)+z²+z.

For0<y<=1 it is at least y(z²+9z)+z²+z>0, again forcing y>1.
The last owner's residual is identical in both orders:

    10E2=-x²y²-31x²y-30x²-41xy²-61xy+10x-40y²-30y.

It is strictly negative for x>0,y>1, since61xy dominates its only positive
term10x. This excludes the remaining two proper triples.

For full proper support define E_i by(W1), now using all three opponents.
The following20-term multiplier certificate excludes their common zero:

    W0=2+t+zt+2y+8x+8xt+3xy+10x²,
    W1=3+8y+y²,
    W2=2+2t+8z+10z²+y+9yz+2xy,
    W3=2+8t.

The polynomial -10 sum_i W_i E_i has140 nonzero monomial coefficients,
ALL strictly positive, with sum71027 and maximum2697. It is therefore
strictly positive whenever all odds are positive, contrary to E_i=0.
This is an explicit finite algebraic certificate. The following standalone
standard-library calculation verifies every coefficient from the literal
table; it performs no root search or floating-point step.

```python
"""Independent standard-library certificate: no proper full stationary root."""
from fractions import Fraction as F

Z = {
    1: [0,-1,3,-1], 2: [-1,0,-1,3], 4: [3,-1,0,-1], 8: [-1,3,-1,0],
    3: [-2,0,0,F(-9,10)], 5: [1,F(1,2),1,F(1,2)],
    9: [F(1,10),F(-9,10),0,-4], 6: [0,-4,0,F(-9,10)],
    10: [-10,-1,-10,-1], 12: [0,F(-9,10),-2,0],
    7: [-10,1,-10,-21], 11: [-10,-1,-10,-1],
    13: [-10,-21,-10,1], 14: [-10,-1,-10,-1], 15: [-11,-1,-11,-1],
}
zero = (0,0,0,0)
weights = [
    {zero:2, (0,0,0,1):1, (0,0,1,1):1, (0,1,0,0):2,
     (1,0,0,0):8, (1,0,0,1):8, (1,1,0,0):3, (2,0,0,0):10},
    {zero:3, (0,1,0,0):8, (0,2,0,0):1},
    {zero:2, (0,0,0,1):2, (0,0,1,0):8, (0,0,2,0):10,
     (0,1,0,0):1, (0,1,1,0):9, (1,1,0,0):2},
    {zero:2, (0,0,0,1):8},
]

def add(p, q, scale=1):
    result = p.copy()
    for a, c in q.items():
        result[a] = result.get(a, F(0)) + scale*c
    return {a:c for a,c in result.items() if c}

def mul(p, q):
    result = {}
    for a, c in p.items():
        for b, d in q.items():
            e = tuple(a[j]+b[j] for j in range(4))
            result[e] = result.get(e, F(0)) + c*d
    return {a:c for a,c in result.items() if c}

certificate = {}
for i in range(4):
    D, R, P = {}, {}, {}
    for mask in range(16):
        if mask & (1<<i):
            continue
        a = tuple((mask>>j)&1 for j in range(4))
        D[a] = F(1)
        R[a] = F(Z[mask | (1<<i)][i])
        P[a] = F(Z[mask][i]) if mask else F(0)
    E = add(mul(add(D, {zero:F(1)}, -1), R), mul(D, P), -1)
    certificate = add(certificate, mul(weights[i], E), -10)

assert len(certificate) == 140
assert all(c > 0 for c in certificate.values())
assert max(certificate.values()) == 2697
assert sum(certificate.values()) == 71027
print("PASS: 140 positive coefficients; sum =", sum(certificate.values()))
```

Stationary approximation is excluded as well. The singleton matrix is

    Gamma=[0,-1,3,-1; -1,0,-1,3; 3,-1,0,-1; -1,3,-1,0],
    Gamma^-1=[2,3,7,3;3,2,3,7;7,3,2,3;3,7,3,2]/15>0.

It is R0: a nonzero x>=0 with Gamma x>=0 and x_i(Gamma x)_i=0 cannot
have singleton support, since its column has a negative exterior entry;
any support of size at least two is impossible because its principal block
is invertible. Pair determinants are-1 or-9, triple determinants6, and the
full determinant45.

If stationary total debt tended to zero, a nonzero limiting hazard would
satisfy the stationary comparisons already excluded. If hazards tend to
zero, normalize by their sum to p>=0,sum p=1. Singleton absorption makes
the limiting prescribed payoff1+Gamma p. Immediate Quit gives Gamma p>=0.
When p_i<1, Never against the opponents gives
1+(Gamma p)_i/(1-p_i), hence p_i(Gamma p)_i<=0; if p_i=1 that product
is zero directly. This contradicts R0. Thus the original table has a
strictly positive debt gap over ALL stationary profiles, also excluding
reward closure of stationary producers. Their weight, scale, odds and
coordinate choices cannot evade a complete stationary-support obstruction.

### Complete weighted, marked, core and matrix admissions

The four crossing-pair native reward vectors sum to
(-19/10,-29/5,-2,-29/5). Thus no nonzero w>=0 can have w dot Z(S)>=0 on
every proper coalition. This defeats EVERY whole-payoff ledger weight,
finite nonempty family of weights and positive matrix coordinate change,
independently of marks, physical floors or orientation choices. For a
support-filtered ledger, w Gamma>=0 and Gamma^-1>0 force w>0, so every
proper support is tested and the same contradiction applies. For an
inserted-premium floor, the sum of its singleton1,2,3 inequalities is
-(9/10)w0-5w1-2w2-w3>=0, impossible for nonzero w>=0. Positive recipient
scalings are absorbed into the weights in all these arguments.

For ordered marked blocks with positive weights, any marked owner in02
makes the first marked block meeting02 have a strictly positive participant
sum. Otherwise the nonempty marked set lies in{1,3}; a marked1 fails on012,
and a marked3 fails on023. This exhausts all marked sets, ordered partitions
and positive block weights. The same strict witnesses make the greatest
premium core all four owners, excluding every literal pair-core or
triple-core admission. Each owner also has a negative participant reward,
excluding every globally protected owner. No owner has all participant
rewards nonpositive; all roles of the passive-bound, exact opposed-path
and quiet-face triple producers therefore fail.

Every principal triple inverse has negative diagonal entries, two-1/6 and
one-3/2; no triple admits a nonnegative-inverse extension. Reciprocal
singleton signs are equal, excluding every role choice requiring opposite
reciprocal signs. The full determinant is positive. Its R0 degree is one:
at strictly positive LCP target1, only the full support is feasible, with
solution(1,1,1,1) and determinant45. Singleton supports cannot reach target1;
negative pairs give negative solutions; favorite pairs have negative
exterior residuals; each triple solution is negative, with entries
(-1/2,-5/2,-1/2) in favorite-pair order. These singleton matrix exits do
not already decide this table.

### Complete pair, phase, return and child-role tests

For the three pair partitions, the joining signs are

    01|23: (-,+),(-,+); 02|13: (-,-),(-,-); 03|12: (+,-),(-,+).

No partition has four nonnegative joining gaps, regardless of inverse,
cone, corner or proof-weight choices. A signed-column condition
Gamma^-1 diag(sigma)>0 forces all signs positive and gives the same failure.
No perfect matching has four positive participant premiums:02 is the sole
positive pair. Thus positive-participant repeated-pair compression admissions
fail for every matching. All four favorite joining gaps are negative,
excluding every above-singleton favorite schedule. Common-favorite-premium
templates require equal row normalizations from the singleton data, but
(1,1,-1,-1) cannot be one common premium. Positive Z0(03)=1/10 defeats
every all-cross-nonpositive template; each crossing pair also has a
nonnegative participant endpoint, defeating all-cross-strictly-below-
singleton templates. Positive favorite pair02 defeats every all-favorite-
nonpositive template. No triple has six positive joining gaps, so every
positive-joining triple/singleton collision-box role and good-subset choice
fails before its remaining tests.

The broader three-owner joint-return selector requires, in roles0,1,2,3,
Gamma03>0,Gamma23<0,Z2(23)>0. The sole positive crossing participant
forces the UNIQUE assignment(roles0,1,2,3)=(actual1,actual2,actual0,actual3).
Its necessary linear/ratio tests use

    e=Gamma32=-1, d=-Gamma30=-3, w=Z3(02)=-9/10,
    v=Z3(23)=-4, a3=Z3(03)=-1, t3=Z3(023)=-1,
    omega=w+d-e=-29/10,
    J0=e*a3+d*v=13, J1=e*(t3-a3)-(omega+e)*v=-78/5.

The first root b=-J0/J1=5/6 is admissible. But its NEXT hazard is
x=e*b/(d-omega*b)=10/7>1. Positive recipient scales leave these ratios
unchanged, so every role, scale and later-root choice fails this selector.

The more general signed solo/triple quadratic producer has a different
entrance and must be checked separately. Its solo/shared owner r and second-
phase owners j,k require positive u,v solving

    [Z_r(rk),Z_r(rj);Gamma_rk,Gamma_rj][u,v]^T
                                  =[-Z_r(rjk),-Z_r(jk)]^T.

Swapping j,k only swaps u,v. These12 rows exhaust all24 ordered roles:

| r;j,k | u,v |
| --- | --- |
| 0;1,2 | -2,-6 |
| 0;1,3 | -100/21,-110/21 |
| 0;2,3 | 300/13,100/13 |
| 1;0,2 | 1/4,1/4 |
| 1;0,3 | -1,-39/10 |
| 1;2,3 | 1/5,-3/10 |
| 2;0,1 | 30,10 |
| 2;0,3 | -6,-2 |
| 2;1,3 | -5,-5 |
| 3;0,1 | 1/5,-3/10 |
| 3;0,2 | 1/4,1/4 |
| 3;1,2 | -39/10,-1 |

Only four rows survive. Their next necessary equation for the shared
owner's second-phase hazard b, up to a nonzero scalar, is

    r=0: 820022b²-2046081b+391876=0;
    r=1: b(3b-4)=0;
    r=2: 7088b²-19809b+3844=0;
    r=3: b(3b-4)=0.

There is no b in(0,1) for r=1,3. The other quadratics are strictly decreasing
on[0,1], positive at1/5 and negative at1. Their unique admissible candidates
therefore have b>1/5, at which the produced solo hazards

    s0=(400b²+38021b-1131)/(100(b-1)(4b+365)),
    s2=(20b²-359b+9)/(10(b-1)(2b-35))

are strictly negative. Hence all roles fail before any later endpoint guard.
Positive row scaling preserves the first solve, multiplies the quadratic
by a positive product and cancels in the solo-hazard ratio, so no scale
repairs the failure.

For every proper nonempty child choose a retained owner whose cyclic
successor is omitted. Sole-owner stopping is exact absorbing child Nash:
every other retained owner has a negative joining gap. The omitted
successor has the positive gain stated above. Child debt and Never are
both zero, so every universal quiet-lift bound by nonnegative weighted
child debt plus child Never fails, for every child, weight and calendar
choice. This does not exclude an adapter supplied with a specially chosen
safe child strategy. Finally the toggle cycle
0->01->1->12->2->23->3->03->0 has positive gains
(1,1,1,3,1,1,11/10,3), excluding any global ordinal toggle potential.

These comparisons exhaust the exact raw selections described, not every
possible nonstationary strategy architecture or a maximal continuation of
an unspecified earlier neighborhood. The positive-index point lies inside
the genuine passive coordinate bounds but outside the prescribed-payoff
hull. Full behavioral cap realization is proved next; no conjecture
counterexample is inferred.


## 6. Exact actual deviation-cap realization

Let eta be the native annotation Phi displayed above, a=eta0,c=eta2,
b=eta1=eta3. At date1 use independent hazards(r0,s,r2,s); on survival,
everyone Quits at date2. Against every unilateral replacement opponents
force absorption by date2. The full terminal deviation-cap recurrence is

    B_i=max(Q_i,P_i+H_i Btail_i), Btail=(-10,-1,-10,-1).

Here Q_i is date1 forced Quit, P_i its passive nonempty-opponent average,
and H_i opponent survival. The tail caps are exactly the maximum of the
grand and passive opponent-triple rewards. Thus this recurrence includes
both actions at both dates, every behavioral mixture, and Never.

Define

    A(s)=-10+18s-18s², B(s)=(1-s)(13-11s),
    r0(s)=(c-A(s))/B(s), r2(s)=(a-A(s))/B(s).

The two anchor Continue caps are A+B r2=a and A+B r0=c. Both free
Continue caps equal

    F(s)=-1+4s-(39/10)s(r0+r2)+(15-177s)r0r2/10.

Substitution gives F(s)-b=N(s)/[10^15(s-1)²(11s-13)²], where

    N(s)=-6795200000000000000s^5+14571698020000000000s^4
         -8884538545700000000s^3-28041440000000s²
         +1315472020837479463s-255220697431989785.

Put l=89775/100000,h=89776/100000. Exact substitution yields

    N(l)=30951616474981033/64000>0,
    N(h)=-13912459125091315893/97656250<0.

The numerators defining r0,r2 increase on[l,h], while B is positive and
decreasing. The endpoint pairs are

    (r0(l),r0(h))=(5254962/25560455,27429257/133109664),
    (r2(l),r2(h))=(5262962/25560455,82412771/399328992).

All lie strictly between205/1000 and207/1000. The forced-Quit offers are

    Q0=-(19/10)s-(81/10)s²+r2[1-(201/10)s+(181/10)s²],
    Q2=-2s-8s²+r0(1-20s+18s²),
    Q1=(1-s)r2(5r0-4)-s, Q3=(1-s)r0(5r2-4)-s.

On that box the anchor expressions decrease in both variables. Each free
expression increases in its first anchor, decreases in the other, and
decreases in s. Exact corner bounds therefore give

    Q0<=-279604595899/32000000000<a-2/5,
    Q2<=-13991906111/1600000000<c-2/5,
    Q1,Q3<=-153584017/160000000<b-7/5.

The intermediate value theorem gives s* in(l,h) with F(s*)=b. Every
Continue cap then strictly beats its Quit offer. Consequently the literal
absorbing two-date profile has native FULL behavioral cap vector B=eta
exactly. For the original table all caps increase by one, because opponents
force absorption by date2 against every replacement.

This is a cap realization, with prescribed payoff U different from eta
by the separating reward-hull inequality. It is not a full-Nash or least-Never
continuation. This precise distinction is part of the boundary example.

## 7. Formalization boundary and remaining cases

The new producer combines both triple faces and full support through one
rectangle. Its inputs are only the reward-polynomial tests(B),(C),(H),(A),(E).
No strategic witness or index budget is supplied. Every rectangle root is
counted; no sign on an individual full-support determinant, axis uniqueness,
or own-axis monotonicity is needed. The exact example has a positive-index
full root at an actual deviation-cap vector, while every stationary profile
and the earlier raw admissions specified above are excluded.

The named selected-return and terminal consumers provide one fixed uniform
target. Relevant degree primitives are `ambientDegree_homotopy` and
`ambientDegree_affineRootField_eq_sign_det` in
`MathUE/Topology/AmbientDegreeHomotopyNormalization.lean`,
`ambientDegree_excision` in `MathUE/Topology/AmbientDegreeProperties.lean`, and
`ambientDegree_of_selfMap_eq_one` in
`MathUE/Topology/AmbientDegreeSelfMapNormalization.lean`.
The new formalization obligations are the planar edge-count lemma, the raw
capture and axis producer, and the full-game adapter. No new Lean check is
asserted.

Opposite-sign joining pairs, multiple positive-pair configurations, failed
capture or edge tests, and the unrestricted global minimum remain open.
The result does not settle arbitrary Fin4 or identify the displayed cap
profile with a zero-debt source.
