# Pair–triple index cancellation for uniform equilibrium

Ordinary mathematics, not a new Lean verification. This gives a finite raw
reward criterion allowing positive-index Nash roots: a related pair root or
another triple root cancels their index. The remaining support tests then
produce a return and a uniform equilibrium. The complete example below
escapes the earlier individual-negative-index criterion, even on the literal
passive-payoff domain and above every coordinate punishment floor. Fin4
remains open.

## 1. Raw theorem

There are four players, finite absorbing rewards r_i(S) on nonempty quitting
coalitions, and zero live and Never rewards. Players use independent private
behavior; one deviator may replace its entire behavior law. Put

    s_i=r_i({i})>=0, Z_i(S)=r_i(S)-s_i, M=max_(i,S)|r_i(S)|,
    J_ij=Z_i(ij), d_ij=r_i(ij)-r_i(j).

Every mutually positive participant pair, meaning J_ij,J_ji>0, must satisfy

    d_ij*d_ji>0.                                        (P)

For each support A of size3 or4 select one of Low, Charge, Orientation, or,
only when |A|=3, the Pair–Triple test below. Each pair may be assigned to
AT MOST ONE Pair–Triple support.

**Low.** Every independent root with exact support A has some active forced
Quit payoff Q_i<=s_i. This is a reward-only product inequality. For a triple it can be checked by nonzero weights w>=0 with
w_i J_ij+w_j J_ji<=0 on each pair and sum_(i in A)w_i Z_i(A)<=0.
Indeed sum_i w_i q_i(Q_i-s_i) equals the coalition average of the weighted
participant premiums. These inequalities make it nonpositive, whereas all
active Quit premiums positive would make it strictly positive.

**Charge.** For nonempty proper T subset A set

    P_A(T)=sum_(i in A\T)Z_i(T+i),
    L_A(T)=sum_(i in A\T)[r_i(T+i)-r_i(T)].

Writing m=|A|, there exist D,tau,G,Lstar>0 such that

    |T|=1: P_A(T)<=-D, L_A(T)<=-G;
    2<=|T|<=m-2: P_A(T)<=0, L_A(T)<=0;
    |T|=m-1: P_A(T)<=tau, L_A(T)<=-Lstar;
    C_A=m(D/tau)^(1/(m-2))*(G+Lstar D/tau)>sum_(i in A)s_i+mM.

**Orientation.** Define the odds polynomials

    Phi_i^A(z)=sum_(empty!=T subset A-i)z_T[r_i(T+i)-r_i(T)],
    R_i^A(z)=sum_(T subset A-i)z_T Z_i(T+i).

For every z>0 with every R_i^A(z)>0 require

    (-1)^|A| det D Phi^A(z)<0.

No supplied root, continuation or index is part of any input.

**Pair–Triple.** Choose ordered roles(i,j,k) in A, with remaining player l.
Use odds(x,y,z) for(i,j,k), and assign the pair{i,k} to this support. Put

    T_h=Z_h(A), B_h=r_h(A)-r_h(A-h),
    alpha=d_ij, beta=d_ik, gamma=d_ki, eta=d_kj.

Require the participant signs

    J_ik>0, J_ki>0,
    J_ij<=0, J_kj<=0, J_ji<=0, J_jk<0, T_j>0;          (F1)

and the joining signs and threshold

    alpha<0, beta<0, gamma<0, eta>=0,
    B_i<=0, B_k<0,
    K=-J_jk/T_j >= eta/(-B_k).                          (F2)

Write p=beta+B_i y, q=gamma+B_k y. The quiet-player polynomial is

    Psi_l(x,y,z)=sum_(empty!=T subset A)z_T
                                      [r_l(T+l)-r_l(T)].

For some scalar lambda>=0 set h=Psi_l-lambda*Phi_j^A and form

    H=pq partial_y h
       -p(eta+B_k x)partial_x h
       -q(alpha+B_i z)partial_z h.                     (F3)

Substitute x=K+u. Require ALL monomial coefficients of the resulting
polynomial in(u,y,z) to be nonnegative. Zero coefficients and the identically
zero polynomial are permitted. There are at most12 coefficients: degree is
at most1 in u and z, and at most2 in y. Each coefficient is affine in lambda,
so the certificate is a finite one-variable linear feasibility problem.
All its other entries are raw reward values and the positive quotient K.
Clearing positive powers of T_j yields literal polynomial comparisons.

**Conclusion.** The original game has one uniform-equilibrium payoff target,
fixed before accuracy, against every complete unilateral behavioral deviation.
The native table Z also has absorbing full-debt infimum A_Z=0; consequently
every nonnegative recipient-row raise of Z has a uniform-equilibrium payoff.

No weak reward-perturbation closure is silently used in(P): changing an
external quiet-row singleton can alter(F3), even when its pair is not inside
the associated triple. Strict(P) avoids that issue.

## 2. All boundaries and the generic source set

For q in the cube let H_i=prod_(j!=i)(1-q_j), Q_i be forced Quit, P_i the
nonempty-opponent passive average, and C_i=P_i+H_i v_i. A full Nash root
uses only maximizing actions between Q_i,C_i; its successor is
w_i=q_i Q_i+(1-q_i)C_i. Here P_i sums the product opponent probabilities
times r_i(T) over nonempty T, and Q_i sums the same probabilities times
r_i(T+i), also including the empty opponent set.
Call it bad if every w_i>s_i.

If some full Nash root has at least two sure owners, all unilateral
comparisons ignore v, and the immediate absorbing profile is already an
all-behavior equilibrium. Otherwise every sure root has exactly one sure
owner. Low excludes a bad root directly. Charge excludes bad roots on a
common box |v_i|<=B with M<B<M+2, chosen so each strict charge threshold
exceeds sum_A s_i+mB. At a bad charged root the whole-cube identity is

    0=c sum_A(s_i-v_i)
        +sum_(empty!=T proper subset A)p_q(T)L_A(T),
    c=product_i(1-q_i).

One sure owner makes the right side negative: a coalition missing a nonsure
active owner has positive probability and strictly negative penultimate L.
For a proper root set U=sum_A z_i and E=sum_i product_(j in A-i)z_j.
Summed positive Quit premiums give DU<tau E; the symmetric-mean inequality
E<=U^(m-1)/m^(m-2) gives U>m(D/tau)^(1/(m-2)). Dividing the identity by c
then forces sum_A(s_i-v_i)>C_A, contradicting the box. This is the exact
bound `QuittingTrapChargeCoefficients.threshold_lt_singletonSourceCharge` in
`UniformEquilibrium/Quitting/Classification/BoxedQuittingNashChargeOdds.lean`.

A bad pair must have both participant premiums positive. Under(P), exactly
one sure owner is impossible because the other owner's indifference would
make its nonzero joining gap vanish. A bad Orientation support has no
exactly-one-sure root: every other active owner's indifference makes the
sure owner's column in D Phi zero. Moving its artificial odds to large
finite values keeps every Quit premium positive, contradicting strict
Orientation. Strict positivity of all active Quit premiums persists at
large finite artificial odds by continuity.

A Pair–Triple support has no exactly-one-sure root either. If i is sure,
proper owner k has conditional gap gamma+B_k y<0, up to a positive factor.
If k is sure, owner i has beta+B_i y<0. If j is sure, owner i has
alpha+B_i z<0. Each contradicts its proper mixing. Thus EVERY bad root left
by these hypotheses is proper on its active support.

There is one dense annotation set avoiding all active-map critical values
and every inactive tie, on every proper support. For critical values, cover
a bounded critical set of a polynomial map R^m->R^m by O(t^-m) small cubes.
Taylor expansion at a critical point in each cube encloses its image in a
rotated box with m-1 sides O(t) and one side O(t^2), so total outer volume
is O(t). Exhaustion proves nullity. Products with free outside coordinates
remain null. An inactive tie is the image of a polynomial map from three
variables to four annotation coordinates, also null by elementary cube covers.
There are finitely many support and outsider choices.

At such generic annotations every PROPER Nash root has strict quiet
inequalities and nonzero active determinant. Hence it is isolated. Under
the all-bad contradiction every root is proper by the preceding boundary
arguments. The full clipped Nash
map is F_v(q)=clip(q+Q-C), and its local ambient index is

    sign[(-1)^m det D Phi^A].                            (1)

Indeed its quiet rows are locally constant zero, while the active endpoint
derivative is diag(H_i)D Phi^A diag((1+z_i)^2), with positive factors.
The full fixed-point set is compact; if all roots are bad, it is finite.
The total ambient degree of this cube self-map is+1: on (-1,2)^4 its
straight homotopy to the constant half-vector has no boundary fixed point,
since every image lies in [0,1]^4.

## 3. The anchored positive-Quit fiber is an initial interval

Fix one Pair–Triple support. Subtract own rewards from the source and denote
its active coordinates by(a,b,c) and its quiet coordinate by d. The active
map has

    Phi_i=alpha*y+(beta+B_i*y)z,
    Phi_k=(gamma+B_k*y)x+eta*y.

At a positive-Quit point, dividing R_j by xz gives

    J_ji/z+J_jk/x+T_j>0,

so x>K and eta+B_k x<0. Hence Phi_i=a<0 and Phi_k=c<0. Holding a,c fixed,

    x(y)=(c-eta*y)/(gamma+B_k*y),
    z(y)=(a-alpha*y)/(beta+B_i*y).                       (2)

The denominators are strictly negative. At y=0, x0=c/gamma>0 and
z0=a/beta>0. Until z reaches zero at the finite value y=a/alpha>0,
x,z remain positive. Their derivatives are

    x'=-(eta+B_k x)/(gamma+B_k y),
    z'=-(alpha+B_i z)/(beta+B_i y).

Both are strictly negative on the whole positive portion of a fiber that
contains one positive-Quit point: the numerator controlling x' is constant
up to a nonzero denominator, so its sign persists backwards.

Now divide R_i,R_k,R_j by yz,xy,xz, respectively:

    J_ij/z+J_ik/y+T_i,
    J_ki/y+J_kj/x+T_k,
    J_ji/z+J_jk/x+T_j.                                  (3)

Every expression strictly decreases along increasing y by(F1). Therefore
the common positive-Quit part is exactly one initial interval0<y<L_R.
The i and k expressions tend to+infinity at y=0; the j expression is
positive there whenever the fiber contains a positive point. Thus no lower
endpoint or disconnected component has been suppressed.

## 4. Tilting the quiet offer and counting the pair face

Let f(y)=Phi_j(x(y),y,z(y)). Multiplying the derivative along(2) by pq>0
shows that(F3) is exactly

    h'(y)>=0,  h(y)=Psi_l(x(y),y,z(y))-lambda*f(y).       (4)

The coefficient test applies because positive R_j forces u=x-K>0.
At a triple Nash root f=b, its strict quiet condition is equivalent to

    h(y)<d-lambda*b.                                    (5)

By(4), this restricts admissible roots to one INITIAL interval inside
0<y<L_R. Nondecreasing h suffices; strict monotonicity is unnecessary.

The Schur-complement calculation for the two anchored equations gives

    det D Phi^A = -pq f'(y).

Thus the full ambient triple index equals sign f'(y), including positive
indices. At the pair face y=0, its index is-1 because beta*gamma>0.
Its j quiet condition is b>=f(0), and its l quiet condition is Psi_l(0)<=d.

Assume some admissible triple root exists. If b>=f(0), (4)-(5) imply

    Psi_l(0)-lambda*f(0)<=h(y)<d-lambda*b,

hence Psi_l(0)<d because lambda>=0. The pair is therefore a full Nash root.
Equality b=f(0) would be an inactive tie, so genericity excludes it. Thus the
pair occurs precisely when b>f(0). If it is not bad, the desired low return
is already obtained; in the contradiction argument below it is bad.

The finitely many admissible regular roots lie in an initial interval.
Choose a finite interior cut beyond the last one, avoiding f=b. The signed
crossing count through this cut is

    1_{f(cut)>b}-1_{f(0)>b}.

All roots before that cut obey positive-Quit and the strict quiet guard,
so this counts exactly the bundle's triple roots. Adding its pair root,
when present, gives

    bundle total index =1_{f(cut)>b}-1<=0.              (6)

If there is no admissible triple root, the bundle contains at most its one
negative-index pair root, and the same nonpositive conclusion holds.
This interior-cut proof avoids any unproved behavior at a limiting endpoint.

## 5. Global degree and the actual-game consumer

At a generic boxed source below some own reward, All Continue is not Nash,
and a singleton cannot be bad. Suppose every full Nash root is bad.
All boundaries and other supports were handled in Section2. Partition the
remaining roots by their assigned pair–triple bundles and their other
supports. Distinct assigned pairs ensure no pair index is counted twice.
Each bundle contributes at most zero by(6); each unassigned bad pair or
Orientation support contributes only negative indices. Thus total index
is nonpositive, contradicting the full cube degree+1.

Some full Nash root therefore returns a successor coordinate at or below its
own reward. Approximate arbitrary boxed below-own sources by generic ones;
compactness and closed Nash inequalities preserve this selected-return
property. The limit cannot be All Continue at a strict below-own deficit.
The existing exact consumer
`exists_uniformEquilibriumPayoff_of_selectedSingletonSublevelReturn_of_reward_bound`
in `UniformEquilibrium/Quitting/Classification/Existence/SelectedSingletonSublevelReturnUniformPayoff.lean`
then gives the stated uniform payoff, including its fixed-target quantifier.

A sufficiently small positive recipient-row raise of r preserves every
participant premium, every joining difference, and every fiber coefficient;
strict charge margins survive. Its native table is still Z and its own
rewards c_i are all positive. For an actual profile let U_i be its terminal
payoff, B_i the supremum over all complete unilateral replacements, and
D=sum_i(B_i-U_i). Absorbing means that the original joint Never mass is zero.
The declaration
`quittingTerminalDebtSumInf_pos_iff_not_exists_uniformEquilibriumPayoff` in
`UniformEquilibrium/Quitting/Terminal/TerminalDebtSumInf.lean`
gives profiles with D_{Z+c}->0, and the exact accounting is

    D_{Z+c}=D_Z+nu*sum_i c_i,

where nu is the product of the original marginal Never masses. To verify
this identity, native own-zero rewards make finite-deadline payoffs converge
to literal Never. Under a positive row raise c_i, each finite deadline gains
c_i, and Never gains at most c_i; hence the full cap gains exactly c_i,
while the prescribed payoff gains c_i(1-nu). Hence D_Z->0 and nu->0. Moving the smallest marginal
Never atom, at mostnu^(1/4), to a finite date changes total native debt by at
most14 max(1,max|Z|)nu^(1/4). This gives absorbing native approximants with
debt tending to zero, so A_Z=0. Nonnegative row raises preserve debt on these
absorbing approximants. The fixed-target consumer is
`quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors` in
`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`.
Before absorption the only live public history is repeated all Continue;
a complete behavioral deviation is a mixture of pure deadlines and Never.
Thus the full-cap comparisons include every unilateral replacement.


## 6. Exact finite classification and a separating game

There are only24 ordered choices of triple roles in Fin4. For each one,
(F1)--(F2) are literal reward comparisons and(F3) is the intersection of
at most12 closed half-lines for lambda, together with lambda>=0. Distinct
pair assignments form a finite matching condition. Thus the new input is
a finite raw reward test, with no numerical continuation scan or supplied
equilibrium. The determinant at an individual root need not be negative.

Here is the complete ORIGINAL table, with own rewards one.

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
| 012 | -1 | 2 | -1 | 10 |
| 013 | -1 | 5/4 | -8 | -1 |
| 023 | -1 | 10 | -1 | -1 |
| 123 | 10 | -1 | -1 | 2 |
| 0123 | -1 | -1 | -19 | 101/100 |

The only mutual-positive pair is02, with joining gaps(-1,-2). Supports013
and123 pass Low using weights(e1+e3)/2, while023 passes using e3: every
weighted participant coefficient on its respective support is nonpositive.
The premium core is all four players: pair02 witnesses owners0,2, triple013
witnesses owner1, and triple123 witnesses owner3. Each witness is strict.

Assign triple012 to pair02 in roles(i,j,k)=(0,1,2). Its data are

    (J01,J02,J10,J12,J20,J21)=(-2,2,0,-4,1,0),
    (T0,T1,T2)=(-2,1,-2),
    (alpha,beta,gamma,eta)=(-1,-1,-2,1),
    (B0,B1,B2)=(-249/100,1/100,-349/100), K=4.

All(F1)--(F2) hold. In odds(x,y,z),

    Phi=(-y-z-(249/100)yz,
          x-3z+(1/100)xz,
         -2x+y-(349/100)xy),
    Psi3=-x-4y+z-(249/100)xy-(299/100)xz
                                -(249/100)yz-(899/100)xyz.

Use lambda=1 in(F3), and substitute x=4+u. The complete coefficient table
for H is positive; columns give the coefficients of1,u,z,uz at each power
of y:

| Power of y | 1 | u | z | uz |
| --- | --- | --- | --- | --- |
| 0 | 14 | 8 | 91/50 | 743/100 |
| 1 | 8339/100 | 3343/100 | 1486519/10000 | 260703/5000 |
| 2 | 9323/100 | 313751/10000 | 18131931/62500 | 78123999/1000000 |

Full support passes Charge with D=1,G=2,tau=1/100,Lstar=899/100.
Its singleton P are(-1,-3,-2,-2), singleton L are(-2,-4,-3,-3), all
middle P are nonpositive and all middle L are negative. Penultimate P
are1/100,-20,-2,-2, while penultimate L are-899/100,-11,-11,-11.
Here M=19 and the charge threshold is36040>4+4M=80. Thus the raw theorem
applies and gives original UE and native A_Z=0.

### Why individual negative orientation and coordinate floors do not suffice

At the proper012 odds

    (x,y,z)=(41/10,1/100,9/10),

the native source and successor are exactly

    v=(-93241/100000,14369/10000,-833309/100000,8),
    w=(1762/1919,3/323,4018/5151,70667/97869)>0.

The active Quit numerators are(881/500,9/100,2009/500)>0; all active
endpoint gaps vanish. The quiet gap is-22729331/9786900<0, and

    det D Phi012=-28758877531/5000000000<0.

Its full ambient index is therefore+1. Individual negative orientation on
this positive-Quit support is false. Low also fails, and Charge is impossible
because P_012({0})=1>0. Under every positive recipient scaling the latter
coefficient becomes lambda2>0, the Quit numerators keep their signs, and
the determinant is multiplied by a positive product. Relabeling conjugates
the Jacobian and does not change its determinant sign. Thus every assignment,
role and positive scale in the Low/Charge/individual-Orientation criterion
fails at012. No claim is made about arbitrary near-table closures with
unbounded changing scale ratios.

The literal native passive box is

    [-1,9] x [-1,9] x [-9,3] x [-1,9],

and v lies strictly inside it. Its lower endpoints are also the exact
coordinate punishment values. Never guarantees each passive minimum, and
pure opponent coalitions attain it: owner0 against{1} chooses between-2
and-1; owner1 against{2} between-4 and-1; owner2 against{0,1,3} between-20
and-9; owner3 against{0} between-2 and-1. The source is strictly above every
one of these minima. Thus neither passive-coordinate bounds nor exact
individual punishment floors remove this positive-index root. This does
not assert that the whole source vector is one jointly realized Nash payoff.

### Stationary profiles and all stationary limits are excluded

If j is sure, its opposite owner j+2 has the following four joining
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

On every proper triple the passive rewards to its active owners are
nonnegative. Thus Q_i=P_i/(1-H_i)>=P_i there. On013 put
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
    Q1=1-4c+5ac,          P1=(199/100)ac.

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

Every proper J(S) is strictly negative. Therefore every monomial of
F=sum_S z_S H(S)-(D-1)sum_(S proper)z_S J(S) having a repeated variable
has a nonnegative coefficient. Its squarefree coefficients are

| Degree | Coalitions, in the listed order | Coefficients of F |
| --- | --- | --- |
| 1 | 0,1,2,3 | 1,1,1,1 |
| 2 | 01,02,03,12,13,23 | 299/50,499/50,249/50,349/50,349/50,299/50 |
| 3 | 012,013,023,123 | 1447/50,547/50,2269/100,1647/50 |
| 4 | 0123 | 5863/100 |

These values follow from H(T)-sum_(empty!=S proper subset T)J(S).
They are all positive, so F>0 on positive odds, contradicting (16).
This coefficient certificate includes the negative passive reward on013
and the negative grand reward; no blanket passive nonnegativity is assumed.

The singleton comparison matrix is

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
  participant premiums. The Low/Charge/individual-Orientation criterion fails on012 as proved
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

## 7. Formalization boundary and remaining cases

The new raw producer is the pair–triple alternative(F1)--(F3), its initial
positive-Quit fibers, and their signed crossing count. Strict orientation
of every individual bad root is unnecessary. The distinct-anchor condition
is essential to this proof: two triples sharing one anchor may not each
subtract its pair index. No such shared-anchor extension is asserted.

The existing selected-return and terminal-debt consumers named above supply
the unrestricted behavioral and fixed uniform-target conclusions. No strategic
witness remains assumed. The exact derivative and degree tools include
`pairNash_hasFDerivAt_and_negative_det_fullClippedDisplacement` in
`UniformEquilibrium/Quitting/Root/PairFullClippedJacobian.lean`,
`ambientDegree_homotopy` and `ambientDegree_affineRootField_eq_sign_det` in
`MathUE/Topology/AmbientDegreeHomotopyNormalization.lean`,
`ambientDegree_excision` in `MathUE/Topology/AmbientDegreeProperties.lean`, and
`ambientDegree_of_selfMap_eq_one` in
`MathUE/Topology/AmbientDegreeSelfMapNormalization.lean`.
The current result is ordinary mathematics; no new Lean build is asserted.

For nonnegative own rewards and strict same-sign mutual-positive pairs, a
counterexample must now fail EVERY distinct-anchor assignment combining
Low, Charge, Orientation and Pair–Triple. This is a stronger condition than
requiring one larger support with a nonnegative individual ambient index.
Opposed positive pairs, uncovered zero products, unsuccessful assignments and
general shared-anchor configurations remain unresolved. The criterion does
not claim to characterize all games with UE or settle arbitrary Fin4.

