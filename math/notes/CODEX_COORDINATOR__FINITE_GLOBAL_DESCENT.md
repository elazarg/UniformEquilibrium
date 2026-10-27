# Finite-calendar global descents for the M14 benchmark

Ordinary mathematics, with complete actual-profile comparisons. For the
selected source penalty r=m/2, an actual minimum has at least two occupied
dates; if it has exactly two, its first support must be all four players.
Its last support must also be all four players. The full/full two-date
case and every longer finite calendar remain open at this fixed penalty.

The two arguments below share the same actual rational tail. The first
works for every r>0; the second excludes first02 for every r>0 and first012
for the selected r=m/2. The absorbing-face bound used in the latter is a
specialization of the existing inverse-axis source construction.

Exact reproduction uses the [one-date Bernstein certificate](../experiments/CODEX_NO_CHILD__ONE_DATE_DESCENT_CHECK.py)
and [consolidated two-date interval certificate](../experiments/CODEX_NO_CHILD__TWO_DATE_DESCENT_CHECK.py).
Fresh whole reviews cover [the one-date argument](../feedback/ONE_DATE_GLOBAL_DESCENT__BY_FRESH_REVIEW.md)
and [both two-date arguments](../feedback/TWO_DATE_GLOBAL_DESCENT__BY_FRESH_REVIEW.md).

## One occupied date

Ordinary mathematics. This lemma supplies an actual global competitor, not a
fixed-observer-cap descendant replacement. It concerns the native M14 table
in `math/notes/CODEX_COORDINATOR__NO_CHILD_FIN4_BENCHMARK.md`.

Let Gamma be its singleton matrix and J its participant-pair matrix:

    Gamma=[0,-1,-1,2;-1,0,1,1;1,2,0,-1;1,-1,1,0],
    J=[0,-5,13,-5;13,0,-5,-5;-5,-5,0,13;-5,13,-5,0].

All larger participant rewards are -5 and every passive nonsingleton reward
is zero. The pivot is2 and observers are O={0,1,3}.

### 1. An actual observer-exact rational tail

There is epsilon>0 and an actual tail T_s, 0<=s<=epsilon, with all prescribed
hazards positive when s>0, positive marginal Never masses, zero observer
debts, and pivot Never a full best response. Its cap vector v(s), pivot debt
e(s), and joint Never mass satisfy

    v(s)=k s+O(s^2),       k=(21,52,92,49)/205,
    e(s)=O(s^2),          nu(T_s)=1-s+O(s^2).          (1)

The actual tail at s=0 is literal Never. Every cap is strictly positive for
s>0 sufficiently small. All four players are ALL-END.

Here is a direct construction. Put

    lambda=2/3, zeta=1/3, h=(52,49,46,58)/615.

Exact matrix multiplication gives

    (Gamma-zeta J)h=(3/205)e2,
    Gamma h/zeta=k,        sum_i h_i/zeta=1,
    (Jh)_O=k_O,            (Jh)_2=83/205.             (2)

For a hazard q write H_i=product_(j!=i)(1-q_j), and let Q_i,P_i be the
native Quit and passive Continue offers. Solve the observer contact equations

    Q_i(q)=P_i(q)+H_i(q)Q_i(q_next), i in O,
    (q_next)_2=lambda q2.                            (3)

The derivative of Q_O with respect to q_O at zero is J_OO, whose determinant
is -970. The implicit function theorem gives

    (q_next)_O=A q_O+b q2+R(q2,q_O),
    A=I-J_OO^-1 Gamma_OO,
    b=J_OO^-1(zeta J_O2-Gamma_O2), R=O(|q|^2).

The characteristic polynomial of I-A, up to a positive factor, is
970u^3+493u^2+52u+1. Its coefficients are positive and493*52>970, so its
roots have negative real parts. Hence the eigenvalues of A have real parts
greater than one and some vector norm satisfies ||A^-1||=kappa<1.
By(2), lambda h_O=A h_O+b h2.

On twice continuously differentiable u with u(0)=u'(0)=0, solve

    u(s)=A^-1[u(lambda s)-R(h2 s,h_O s+u(s))].         (4)

Use the maximum of the weighted norms |u(s)|/s^2, |u'(s)|/s and |u''(s)|.
The linear composition has norm at most kappa lambda^2<1; on a fixed bounded
ball the nonlinear difference is O(epsilon). A sufficiently large fixed
ball and then sufficiently small epsilon give a strict invariant contraction.
Thus q(s)=(h_O s+u(s),h2 s), with coordinates placed in their original order,
is an exact C2 curve, q(s)=h s+O(s^2). All its components lie in(0,1) for
small positive s. Prescribe q(lambda^n s) at date n.

The hazard sum is finite, so all marginal Never probabilities are positive.
Equation(3), iterated with Q_i(q(lambda^n s)) tending to zero, proves that
every observer's finite deadline and Never payoff equals Q_i(q(s)). Every
behavioral replacement is a mixture of these deadlines and Never. Hence
observer caps and prescribed payoffs coincide exactly, not approximately.

For the pivot, singleton passive outcomes give its Never payoff
W2(s)=(Gamma h)_2 s/zeta+O(s^2); the sum of double-event probabilities is
O(s^2). Therefore

    W2(s)-Q2(q(s))=9s/205+O(s^2)>0.                  (5)

The same uniform expansion applies at every conditional date lambda^n s.
Comparing a finite deadline with Never multiplies(5) by prior opponent
survival, so Never strictly dominates every finite deadline. Thus W2 is the
full cap. The pivot's debt satisfies the exact recurrence

    e(s)=q2(s)[W2(s)-Q2(q(s))]+c(s)e(lambda s),
    c(s)=product_i(1-q_i(s)).

The nonnegative forcing is O(s^2); summing the geometric bound proves
e(s)=O(s^2). Finally, the product of all survival factors is
1-s sum_i h_i/zeta+O(s^2)=1-s+O(s^2). This proves(1) with an actual tail.
No absorbing-gap or global-minimum hypothesis enters this construction.

### 2. Exact root attachment preserving the pivot gap

For positive root odds x put

    C_i(x)=(J-Gamma)_i x
       -5[sum_(j<k;j,k!=i)x_j x_k+prod_(j!=i)x_j],
    nu0(x)=product_i(1+x_i)^-1.

Consider a one-date profile followed by Never, with all four hazards positive,
zero observer debt and pivot Never optimal. Its root odds x satisfy

    C_O(x)=0,       C2(x)=-g,       g>=0.

Suppose DC(x) is invertible. For the ACTUAL tails from Section1, the implicit
function theorem produces positive x(s) close to x, with

    C(x(s))=v(s)-g e2,
    x(s)=x+DC(x)^-1 k s+O(s^2).                     (6)

Prepend this root to T_s. The observers' root contacts hold exactly and
hence their entire prescribed laws remain optimal. The pivot's Continue
cap exceeds its Quit offer by H2 g, so Continue remains a full maximizer,
including the tie g=0. Thus this is an actual feasible profile on the same
zero-observer-debt carrier. Its full cap is ALL-END. Nothing is replaced
inside a pre-existing inherited head.

Writing z(s)=x2(s), the exact pivot debt and objective are

    d2(s)=nu0(x(s))[z(s)g+e(s)],
    J_r(s)=nu0(x(s))[z(s)g+e(s)+r nu(T_s)].           (7)

In particular for every r>0, with n_i=1/(1+x_i),

    J_r'(0)/nu0(x)
      =g(e2^T-z n^T)DC(x)^-1 k
         -r[1+n^T DC(x)^-1 k].                      (8)

The tail debt contributes no first-order term. Consequently the two strict
finite inequalities

    (e2^T-z n^T)DC(x)^-1 k<0,
    1+n^T DC(x)^-1 k>0                              (9)

rule out this one-date profile as a global J_r minimum for EVERY r>0.
At g=0 only the second strict inequality is needed. The r=m/2 source choice
is included, without any numerical assumption about m.

### 3. Complete class coverage and exact sign certificate

Every nonempty one-date M14 profile with positive caps, zero observer debts,
ALL-END, and positive Never masses has all four hazards positive. Indeed
an active observer must have its premium predecessor active; the resulting
cycle-prefix candidates are02,012,0123 and the pivot singleton2.
Support2 has negative observer0 Never payoff. Support02 cannot satisfy
observer0 contact, which demands14x2=0. On012, observer0 Never numerator is -x1-x2<0. Thus0123 remains.
Equivalently one may apply the complete last-root classification in the
canonical benchmark, which leaves only012 and0123 before cap positivity.

That classification proves that every such full-support root lies on the
single curve C_O=0 with

    alpha<=z=x2<rho0,        3/25<alpha<rho0<4/25.

Here alpha is the pivot-contact endpoint and rho0 is the first zero of the
observer0 cap. The exact resultant proof and rational endpoint signs are
in the canonical benchmark's complete M14 sign partition; this internal
proof uses that existing theorem and its exact checker, not numerical
branch selection. The following additional bounds are proved here:

    x0 in[3/25,9/50],  x1 in[11/100,19/100],
    x2 in[3/25,4/25],  x3 in[13/100,17/100].          (10)

Set z=x2,y=x3,l=5(1+z),h=14-5z,c=6+5z,k=6z,
d=h^2-lk,e=20l,a=c^2-lk,b=20k. The observer contacts give

    x0=(k+cy)/(h-ly), x1=(ay+b)/(d-ey),
    F_z(y)=(4+5z)x1+(7+5z)y+l x1 y-14z=0.

On its legal interval0<y<d/e, F_z is strictly increasing. Clear d-ey and
substitute z=3/25+t/25,0<=t<=1. At y=13/100 its cubic Bernstein coefficients
are

    -2846868/390625, -149862809/6250000,
    -365472493/9375000, -20430076/390625;

at y=17/100 they are

    22085767/390625, 768161213/18750000,
    254116267/9375000, 5841744/390625.

The denominators are positive throughout this rectangle. These opposite
strict signs and monotonicity place y between the two rational endpoints.
The map phi(y)=(k+cy)/(h-ly) increases in both z and y where its denominator
is positive, as does phi composed with itself. Its corner bounds are

    263/2112<=x0<=1058/6107,
    81411/670700<=x1<=81607/465475.

They imply(10).

Write D=DC(x), P=product_i(1+x_i), b=(21,52,92,49), u=adj(D)b and
S=sum_i[P/(1+x_i)]u_i. Define the polynomials

    A=205P detD+S,        B=-[P u2-zS].

The inverse expressions in(9) satisfy exactly

    1+n^T D^-1k=A/(205P detD),
    (e2^T-z n^T)D^-1k=-B/(205P detD).

On the full rational box(10), all tensor Bernstein coefficients of each of
these three polynomials are strictly positive. Their coordinate degrees,
coefficient counts, and exact minimum coefficients are

| Polynomial | Degrees | Count | Smallest coefficient |
| --- | --- | --- | --- |
| detD | (2,2,2,2) |81|695509964106293/62500000000|
| A | (3,3,3,3) |256|8503628877474398758391/4882812500000000|
| B | (3,3,4,3) |320|46778584435393895821/195312500000000|

This is a finite rational certificate. To reproduce it, substitute
x_i=lo_i+(hi_i-lo_i)t_i and write the resulting power coefficients as c_m.
For coordinate degree d_i, the Bernstein coefficient indexed by j is

    sum_(m<=j) c_m product_i binom(j_i,m_i)/binom(d_i,m_i).

All data are the displayed matrix D (the derivative of C), the three
polynomials, and box(10). The compact exact checker implements this formula
and fails if any sign is nonpositive. Hence D is invertible and both
inequalities(9) hold throughout the complete admissible positive-cap branch.
Equation(8) is strictly negative for every r>0 and every g>=0.

### 4. Global-minimum consequence and precise limit

Therefore NO positive-cap one-date ALL-END exact-observer profile at M14
is a global minimum of d2+r nu, for any r>0. The theorem includes the pivot
tie endpoint g=0 and the previously retained positive finite control z=1/8.
That control is now proved not globally minimizing.

For the selected source with0<mu<r<m, every actual minimum has positive
caps by the already established solo-observer prefix descent. Literal
Never has value r>mu. If a proposed minimum has exactly one occupied date,
initial empty dates may be removed: all existing caps are positive, so
extra pure Quit0 options of value zero cannot raise a cap. The theorem
then rules out that minimum. Every surviving finite actual minimum must
therefore have at least TWO occupied dates; its six first/last support
pairs remain subject to the existing endpoint restrictions.

This changes the ENTIRE actual profile by adding an actual infinite tail.
It does not keep the old observer cap values fixed. It cannot be applied
to the final root of a longer profile without pricing the preceding head.
Longer finite profiles, inherited mixed-cap endpoints and arbitrary Fin4
remain open. This is ordinary mathematical evidence, not a Lean proof.

## Two occupied dates

This is an actual-global-minimum exclusion for the canonical M14 native
benchmark, with pivot2 and observers0,1,3. It does not exclude every two-date
profile, all finite minima, or arbitrary Fin4. The proposed source profile
is ALL-END, has zero observer debts, positive marginal Never masses and
strictly positive full caps. These are the established incoming actual
subcritical-minimum properties. The first02 exclusion holds for every r>0. The first012 exclusion uses the
canonical source choice r=m/2 and the exact upper bound m<=11/156 proved
below on the augmented absorbing face.

**Claim.** For r=m/2, such a global minimum cannot have exactly two occupied
dates with first support02 or012. Combined with the established first/last
support classifications, every remaining two-date minimum starts0123 and
ends012 or0123. The improving profiles keep every original empty date; the
precise treatment of those quiet Quit0 options appears below.

### 1. Exact reduction to one last-root parameter

Use the benchmark's proved complete last-root classification. A last012
root has B0<0. At a first02 root, put zF=q2/(1-q2) and aF=q0/(1-q0).
Observer0 contact is exactly

    B0_tail=14 zF>0.                                      (1)

Thus last012 is impossible. The last root must be the full observer-contact
branch. Write its odds x=(x0,x1,z,y), with

    ell=5(1+z), h=14-5z, C=6+5z, K=6z,
    d=h^2-ell K, e=20ell, a=C^2-ell K, b=20K,
    A2=ell(5z^2+70z+104),
    A1=(4+5z)a+ell b+(7+5z)d+14ze,
    A0=z(70z^2+2980z-2264),
    y=-2A0/[A1+sqrt(A1^2+4A2 A0)],
    x0=(K+C y)/(h-ell y), x1=(a y+b)/(d-e y).         (2)

The all-positive-cap admissible last branch is exactly [alpha,rho0), where
3/25<alpha<121/1000 and rho0 is the unique root on(0,1) of

    C0(z)=125z^6+3875z^5+625z^4-510200z^3
                                  +936360z^2+7107160z-1094208.

C0 is strictly increasing on[0,1], and

    C0(19/125)=180752763882631/30517578125>0.

Hence every actual last root here lies within3/25<z<19/125. Its four
caps B_i are positive. These statements are exactly the established
last-root branch, with the last upper bracket sharpened by one evaluation.

Let Gamma,J be the displayed benchmark matrices, L=J-Gamma, and put

    C_i(x)=L_i x-5[sum_(j<k;j,k!=i)x_j x_k+prod_(j!=i)x_j],
    H_i=prod_(j!=i)(1+x_j)^-1, nu0=prod_j(1+x_j)^-1,
    B_i=H_i Gamma_i x, g=-C2(x)>=0, d0=nu0 z g.       (3)

These are the last root's actual Never caps, pivot debt and joint Never
mass. Native passive nonsingletons vanish in this benchmark.

### 2. Selecting the first observer1 contact

Keep the last root fixed. Equation(1) fixes zF=B0/14. Observer1 is quiet
at the first root. Its contact boundary is

    aF=(B1+6zF)/(14-5zF).                            (4)

Let a=q0=aF/(1+aF), q=q2=zF/(1+zF). Every first q0 between0 and the value
in(4) satisfies all observer comparisons. Observer0 remains indifferent.
Observer1's Quit-minus-Continue comparison increases strictly with q0;
observers3 and the pivot have nonpositive Quit offers and positive Continue
caps. At(4), observer1's common value is positive: since B1>0 and
0<zF<=2/14, its numerator has the sign of

    B1(13-5zF)+8zF-5zF^2>0.

In particular the contact is proper and positive; no sure boundary or
negative observer cap is encountered. The bound B0<=2 follows immediately
from its native singleton/passive rewards.

For fixed q and tail, the complete objective is affine in q0:

    J=(1-a)[q B2+(1-q)(d0+r nu0)]+6qa.              (5)

If its slope is nonzero, a strict interior observer1 comparison is not a
minimum. If its slope is zero, increasing a to the contact(4) preserves the
objective and all feasibility. Thus any alleged global first02 minimum can
be replaced by a global first02 minimum satisfying(4), without changing its
last root or number of occupied dates. At this contact, decreasing a is
feasible. Its one-sided optimality therefore implies

    r>=R(z),
    R=[6q-q B2-(1-q)d0]/[(1-q)nu0].                 (6)

This is genuine global-feasible variation, not an assumption that the last
root minimizes any objective. R may have either sign.

### 3. An actual tail attachment and exact observer repair

There is an actual independent tail T_s, for small s>=0, with zero observer
debts, pivot Never a full maximizer, and

    v(s)=k s+O(s^2),  k=(21,52,92,49)/205,
    e(s)=d2(T_s)=O(s^2), nu(T_s)=1-s+O(s^2).          (7)

All four caps are positive for small s>0. This is the rational tail already
constructed in the one-date descent proof: its hazards are
q((2/3)^n s), q(s)=h s+O(s^2), h=(52,49,46,58)/615. The observer contact
map has expanding linear block I-J_OO^-1 Gamma_OO; its complementary cubic
is970u^3+493u^2+52u+1, with left-half-plane roots. The weighted C2 graph
contraction produces the exact curve. The identities
(Gamma-J/3)h=(3/205)e2 and Gamma h/(1/3)=k give pivot Never surplus
9s/205+O(s^2), so every finite deadline is dominated and e(s)=O(s^2).
The hazard sum gives the last expansion in(7). Thus (7) is an actual tail,
not a freely prescribed continuation vector.

Hold the last root's pivot gap g fixed and solve

    C(x(s))=v(s)-g e2.

The derivative matrix D=DC(x) is invertible on the relevant branch. The
exact certificate below verifies invertibility as well; the one-date
whole-box determinant certificate supplies it independently. IFT gives
x(s)=x+u s+O(s^2), u=D^-1 k, with every hazard positive and proper.
Observers remain exactly optimal, and the pivot's Continue cap exceeds
Quit by H2 g. Hence the new last root followed by T_s is ALL-END and
observer exact, including g=0. Its output caps are

    B_i(s)=Q_i(x(s)) for i in O,
    B2(s)=Q2(x(s))+H2(x(s))g.

At the first root set zF(s)=B0(s)/14 and apply(4) with B1(s). These exact
identities preserve observer0 and observer1 contacts. Observer3 and the
pivot retain their strict inequalities. The entire modified profile is an
actual feasible competitor, with positive Never masses; no head cap is
silently held fixed or ignored.

### 4. The complete objective derivative and exact sign certificate

Primes below denote this actual attachment derivative at s=0. Let
n_i=1/(1+x_i), and put

    B_i'=DQ_i(x)u for i in O,
    B2'=DQ2(x)u-g H2 sum_(i!=2)n_i u_i,
    d0'=nu0 g[u2-z n.u], nu0'=-nu0[1+n.u],
    zF'=B0'/14,
    aF'=[B1'+(6+5aF)zF']/(14-5zF),
    q'=zF'/(1+zF)^2, a'=aF'/(1+aF)^2.

Here nu0' denotes the derivative of last-root survival TIMES the appended
tail survival. The tail debt in(7) has zero first derivative. Differentiating
(5) gives the exact whole-profile derivative A+r B, where

    A=-a'[q B2+(1-q)d0]
        +(1-a)[q'(B2-d0)+q B2'+(1-q)d0']
        +6(q'a+qa'),
    B=-a'(1-q)nu0+(1-a)[-q'nu0+(1-q)nu0'].           (8)

The standalone standard-library checker
`math/experiments/CODEX_NO_CHILD__TWO_DATE_DESCENT_CHECK.py`
SHA256 `15b3c37cf98549e24ec885c00470098dae0035c489d7e90653269c99912f9039`
substitutes(2)--(8) and proves the following exact inequalities:

    3/25<=z<=13/100:   B<0 and A+R B<0;
    129/1000<=z<=19/125: B<0 and A<0.               (9)

The two intervals overlap and cover the whole possible last-root branch.
On the first, (6) gives A+rB<=A+RB<0. On the second, r>0 gives A+rB<0.
Consequently the actual competitor strictly lowers the global objective.
This contradicts minimality and excludes every two-date first02 minimum.

The calculation uses outward-rounded dyadic interval arithmetic with scale
2^80, exclusively integer operations. Rational inputs are rounded outward;
products/divisions use all endpoint extrema, and square roots use integer
square roots rounded outward. Gaussian elimination uses only interval
pivots separated from zero. A box is accepted only when both required upper
bounds are strictly negative; otherwise it is bisected, with a fail-closed
depth/node limit. Its complete final coverage is:

    low interval:73 nodes,37 leaves,maximum depth6;
    high interval:51 nodes,26 leaves,maximum depth6.

The respective worst accepted upper bounds for the nontrivial expressions
are -85607191051274714727/1208925819614629174706176 and
-9151389421230657341/302231454903657293676544. No floating-point arithmetic,
rootfinder, sampled sign claim, or unverified leaf is used.

### 5. The exact source penalty bound

Here C is the zero-observer-debt subset of the full augmented semantic
closure of actual profiles, and

    m=min{d2(Y):Y in C, nu(Y)=0}.

It is not an infimum over actual absorbing profiles already having exact
observer optimality. This distinction matters in the following bound.
Put w=(4,5,1,3), so Gamma w=11e2, Jw=(-27,32,-6,40), and sum w=13.
For fixed t>0 and integer N, run N identical independent roots with odds
tw/N, followed by Never. Every observer passive offer is exactly zero,
because passive nonsingletons vanish and Gamma_O w=0. Its Never payoff is
zero; every Quit offer and full cap are O(1/N), and its prescribed payoff
is O(1/N), since each root contributes q_i Q_i=O(1/N^2). Thus observer debts
tend to zero, without claiming that these finite approximants are exact
observer equilibria.

The pivot Quit offer is strictly negative (its linear odds coefficient is
-6t/N and all higher terms are negative), while its passive offer is
11t H2/N>0. Never is therefore its full maximizer. Exact finite geometric
sums give, in the augmented limit N->infinity,

    N_i=exp(-w_i t), nu=exp(-13t),
    B_i=e_i=U_i=0 for i!=2,
    B2=e2=(11/12)(1-exp(-12t)),
    U2=(11/13)(1-exp(-13t)).

Closedness puts this point in C. Letting t tend to infinity and taking a
compact limit produces a point of C with nu=0 and d2=11/156. Consequently

    m<=11/156,             0<r=m/2<=11/312.           (10)

No infinitely delayed continuation is executed and no approximate observer
profile is silently treated as exact before taking its semantic limit.

### 6. Excluding every two-date first012 source minimum

At first012, observer0 has P0<0: its singleton1 and2 rewards are -1 and
its passive12 reward is0. Positive current cap and contact give
B0_tail=(Q0-P0)/H0>0. Thus last012 is again impossible, and the last root
is the same positive-cap full branch from Section1.

Write Z for its parameter in(2), v_i=B_i for its caps, c=v2 and
k=d0+r nu0. Let b=x1>0 be the first root's observer1 odds. The exact
observer0 and observer1 contacts force

    zF=(v0+4b)/(14-5b),
    aF=(v1+6zF)/(14-5zF).                           (11)

The pivot's positive cap and negative Quit offer make its Continue response
strict. The only remaining quiet comparison is observer3:

    C3(b)=14b-6aF-6zF
           -5(aF b+aF zF+b zF+aF b zF)<=v3.        (12)

The full objective along this actual observer-contact family is exactly

    J(b)=[k+zF(c+6aF+7b+5aF b)]
                         /[(1+aF)(1+b)(1+zF)].     (13)

This identity includes the complete pivot cap and debt; it is not a fixed-cap
surrogate objective.

The exact checker proves v0<1/50 and v1<1/10 for every
3/25<=Z<=19/125. These bounds depend only on Z, independently of b.
Contact(11) and v0>0 imply b<14/5. Positive current Q0 gives

    5b^2-(18+5v0)b+13v0>0.

Its left side is strictly below5b^2-18b+13/50. The latter convex quadratic
has negative endpoint values -71/8000 and -547/50 on[3/200,14/5], so is
negative throughout that interval. Therefore every source root satisfies

                         0<b<3/200.                (14)

For completeness, let primes in this paragraph mean derivative in b:

    zF'=(4+5zF)/(14-5b),
    aF'=(6+5aF)zF'/(14-5zF),
    ell=aF'/(1+aF)+1/(1+b)+zF'/(1+zF)>0.

Writing numerator W=k+zF(c+6aF+7b+5aF b) and denominator V for(13),
J'(b) has the sign of W'-W ell. This expression decreases with r, since
its r coefficient is -nu0 ell<0. It is enough to check r=11/312.
The SAME consolidated exact dyadic checker verifies, on the entire box

    3/25<=Z<=19/125,        0<=b<=3/200,

that W'-W ell>0 at r=11/312, V>0, ell>0, and C3'(b)>0. It also verifies
the two tail-cap bounds used in(14). Its exhaustive traversal uses479 nodes,
240 leaves and maximum total bisection depth11. The worst accepted lower
bound for W'-W ell is

    216680338218802348193/302231454903657293676544>0.

Thus J'(b)>0 throughout the actual source domain for every r in(10).
Decreasing the positive b slightly preserves both active observer contacts
exactly. Because C3'>0, it preserves the quiet3 inequality even at equality.
All active hazards stay positive and proper, and the strict pivot Continue
comparison persists. The last root and its tail remain unchanged. This is
an actual feasible whole-profile variation and strictly decreases J_r,
contradicting global minimality. Every two-date first012 source minimum is
therefore excluded.

### 7. Scope and empty dates

If the original two occupied dates have empty dates between them, the
conditional caps during that gap are the positive last-root caps. After
attachment they remain positive, so every inserted native Quit0 option
stays strictly below Never. Initial empty dates likewise see the positive
whole-profile caps. After the original last occupied date, the new tail
can begin immediately; it replaces the old all-Never continuation rather
than leaving any empty dates inside the new tail. All earlier empty dates
can therefore be retained literally. This is not the invalid general
claim that arbitrary zero-cap empty dates can be deleted or reinserted.

Among the previously listed six first/last support pairs, only two remain
for a two-occupied-date actual source minimum with r=m/2:
first0123/last012 and first0123/last0123. Neither is asserted feasible or
eliminated here. The first02 exclusion itself requires only r>0; the
first012 derivative argument explicitly uses(10).

The proof does not condition a minimum into a minimum, use an inherited
fixed-cap objective as J_r, or assert arbitrary finite-clock closure.
It gives complete additional finite subclass exclusions with actual
full-behavior consumers. The two-root result and the one-date result share
the same rational-tail construction; they should be retained together,
without duplicate producer records.

## Excluding a full first root followed by a triple last root

Assume the same actual M14 source as in the combined two-date proof, with
canonical r=m/2<=11/312 and minimum value mu<r. If its first occupied date
has full support and its last has support012, write first odds(a,b,t,y).
Because the whole observer caps are positive and active observer contacts
hold, the first immediate-Quit payoffs Q0,Q3 are positive. The exact native
formulas therefore give

    (1+b)(1+y)<(5+18t)/[5(1+t)]<18/5,
    (1+a)(1+t)<(5+18b)/[5(1+b)]<18/5.

Consequently the first joint-survival factor exceeds25/324.

Write Z for the last pivot odds. The complete last012 classification gives
Z>=z_*>74/100>1/2, last odds

    (6Z/(14-5Z),14Z/(4+5Z),Z,0),

and last pivot debt

    d_tail=Z^2(1516+110Z)/[(14+Z)(4+19Z)(1+Z)]>1/2.

For the inequality, twice its numerator minus its positive denominator is

    201Z^3+2743Z^2-326Z-56.

For Z>=1/2, this is bounded below by
201Z^3+(2091/2)Z-56>0. All-END makes the first pivot gap nonnegative, so

    mu>=nu_first d_tail>25/648>11/312>=r,

contradicting mu<r. This eliminates the complete first0123/last012 class.
Combined with the pair/triple-first exclusions, any two-occupied-date actual
source minimum must have full support at BOTH dates. No claim about that
remaining full/full class is made here. Empty dates need not be deleted:
this argument uses only the two root recursions, and literal empty roots
have joint survival1 and zero pivot contribution under ALL-END.
