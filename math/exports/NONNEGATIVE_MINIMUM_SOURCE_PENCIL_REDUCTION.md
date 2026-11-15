# Negative-dual reduction and actual repair at proper nonnegative sources

## Exact statement

Let I have four owners. A native quitting table has own-singleton, live and
literal Never rewards zero; all other coalition rewards are arbitrary finite
reals bounded in absolute value by M>=1. Laws on natural stopping dates and
a separate Never point are independent. Every unilateral entire law is allowed.
For actual laws retain prescribed payoffs U, full behavioral caps B, Never
offers e and ORIGINAL marginal Never probabilities N. Let C be their compact
Euclidean closure, E={X in C:U=B}, and nu=product N_i. Suppose

    m=min{nu(X):X in E, min_i U_i(X)<=0}>0.

The positive absorbing gap supplies m>0 as proved below, but the theorem
itself only needs the displayed positive minimum.

**Theorem.** Let X attain this SAME restricted minimum, with u=U(X)>=0,
and let T={i:u_i=0} be nonempty and proper. Put G=Gamma_T, where
Gamma_ij=Z_i({j}) and Gamma_ii=0. Then

    x>=0 and Gx>=0 imply x=0.                         (N)

Equivalently there is y>0 with y^T G<0 in every column. Consequently
|T| is two or three. For |T|=2 both reciprocal singleton rewards are strictly
negative, and both joining increments J_ij-Gamma_ij are strictly positive.
For |T|=3 every joining-increment column has a positive entry. Here
J_ij=Z_i({i,j}) off the zero diagonal and L=J-Gamma.

For |T|=3, additionally suppose every off-diagonal entry of L_T is nonzero
and det L_T!=0. Then EVERY matrix

    M(t)=G-t J_T, 0<=t<=1,

has its own y_t>0 with y_t^T M(t)<0 columnwise. In particular the entire
pencil is R0 of homogeneous complementarity degree ZERO, with definitions
and proof below. For |T|=2 the same pencil conclusion needs no genericity.
Finally, a genuine all-positive incoming Nash chain cannot converge to X
only at an infinite cut: any landing at X is finite, and its last row has
a quantitative positive activity floor, stated below.

The raw negative-dual/degree-zero conditions also produce a local repair
from nearby POSITIVE E points to eligible E points, with explicit original
Never gain. For the uniform statements assume A_Z>0,0<m<1 and
L_ij!=0 for every i!=j, det L_SS!=0 for every three-element S. Then the
positive sublevel

    P_m={Y in E:nu(Y)<=m, U(Y)>>0}

is compact. If nonempty it has a UNIFORM positive payoff buffer through
level m itself. From any GIVEN Y0 in P_m a genuine finite augmented-carrier
Nash head crosses m or reaches eligibility at m after the explicit bounded
number of retained macroscopic cuts below. This does not assert that a
positive starting point exists or identify this carrier head with any
stronger literal full-law source atlas.

Thus the entire semipositive singleton-block branch is excluded for a proper
nonnegative selected source. This proper-zero theorem alone leaves
all-zero m-sources, negative m-sources and positive global-alpha sources.
The later uniform argument separately excludes all-zero E at nu<=m when
A_Z>0 and m<1. Throughout, m retains its restricted eligibility condition;
alpha=min_E nu is a different minimum.

## Conjecture-facing change and strategic inputs

This removes the ENTIRE branch in which a proper nonnegative selected
minimum-Never source has a nonzero x>=0 with Gamma_T x>=0, for arbitrary
finite higher-coalition rewards. The remaining three-zero source must have
a negative singleton dual; under the stated joining genericity every matrix
of its pencil has such a dual and degree zero. A positive incoming head
must reach such a selected proper zero face at a finite macroscopic row.
The actual local repair and uniform positive buffer close the previous
s-up-to-m degeneration on the m<1 branch. Finite-amplitude jumps above m
and the m=1 endpoint still need a global consumer.

The incoming source is the compact minimum for the ORIGINAL eligibility
condition min U<=0. The comparison words below are produced from the raw
finite table in an exhaustive contradiction argument. Every comparison
retains a zero or a negative endpoint coordinate, so it is eligible for
THAT SAME minimum. No favorable root, source realizer, clock, tail minimum,
continuous root selector or continuation openness is supplied as input.
The word constructions are existing mechanisms; the new content is their
complete restricted-minimum consumer and the resulting source reduction.

The unrestricted minimum alpha=min_E nu is generally smaller than m.
The degree here is zero; no uniqueness of AllContinue, degree-one or
standard-Q conclusion at the restricted source is assumed or inferred.
The theorem does not solve the remaining finite-amplitude positive-root
return, the m=1/AllNever endpoint, the negative-source branch or Fin4.

## Probability mode and source production

There is one live public history before absorption. Independent behavioral
randomization is therefore represented by independent first-Quit laws on
natural dates plus a distinct Never point. Every whole-law deviation is
a mixture or limit of pure deadlines and Never, so B is their full supremum.
There is no public randomizer, correlation device or memory bound.
The tuple closure retains U,B,e and the ORIGINAL N separately; finite mass
escaping every fixed date is not relabeled Never. Its coordinates are
bounded and finite-dimensional. AllNever gives a nonempty E and eligibility
set; compactness gives the stated minimum.

To connect its positive-minimum hypothesis to the native counterexample
reduction, define D=sum_i(B_i-U_i) and

    A_Z=inf{D(P):P actual,nu(P)=0}.

Move one smallest original Never mass eta to a finite date. The profile
now absorbs surely. Its mover's response cap is unchanged because that cap
depends only on opponents. Four prescribed payoffs and the other three
caps change by at most2M eta each, uniformly in complete responses. Thus

    A_Z<=D+14M nu^(1/4),

also on C by limits. Consequently A_Z>0 gives positive nu on E and m>0.
The theorem is an ordinary mathematical restriction on the actual selected
sources of any such table. It does not assume that their laws attain C.
Every E point has nu>=beta=(A_Z/(14M))^4>0 when A_Z>0.

The native A_Z changes by at most8 times the entrywise reward perturbation:
each prescribed payoff and full cap changes by at most that perturbation,
so each debt changes by at most twice it. The joining genericity conditions
above avoid finitely many proper polynomial zero sets, so their domain is
open dense in native table space. A positive-gap table can therefore be
perturbed to satisfy them while keeping its gap positive, then selecting
sources afresh. This does not preserve a previously chosen source or erase
zero SOURCE coordinates at a fixed table.

## Actual finite-prefix comparison rule

For a proper product row q, Q_i is the forced-Quit offer, P_i the passive
absorbing contribution, H_i=product_(j!=i)(1-q_j), h=product_j(1-q_j).
The exact maps, also on C, are

    U'_i=q_i Q_i+(1-q_i)P_i+h U_i,
    B'_i=max(Q_i,P_i+H_i B_i),
    e'_i=P_i+H_i e_i, N'_i=(1-q_i)N_i.              (1)

For d_i=B_i-U_i the exact nonnegative decomposition is

    d'_i=q_i(B'_i-Q_i)+(1-q_i)(B'_i-P_i-H_iB_i)+h d_i.

This also charges reached prescribed Quit mass in approximate profiles;
it does not replace a complete cap by a selected deadline comparison.

Their U and B maps are nonexpansive in the respective tail coordinate,
uniformly through a word. They preserve C by prefixing actual approximants.
At positive nu, the inequality B_i-U_i>=N_i(B_i-e_i)>=0 gives U=B=e on E.

Write b=min_(p notin T)u_p>0. Restrict all prefix activity to T and keep its
total sum of conditional hazards at most b/(16M). Every positive outsider
then remains exactly quiet: its passive Continue value changes from u_p by
at most 2M times total activity, while its current Quit offer has magnitude
at most M times current activity. Its zero debt is therefore retained.

It suffices to build finite words with observer debts tending to zero,
survival in a fixed interval [c0,c1] contained in (0,1), and an endpoint
payoff tending to zero in at least one coordinate of T. Apply each finite
word to actual approximants of X and take a compact subsequence. Formula(1)
then produces an ELIGIBLE E point with original Never c m<m. A finite word
may be estimated from a virtual observer starting payoff/cap converging to
zero: nonexpansiveness transfers the estimates to the actual tail X.
No source law need attain X, and no tail is played after an infinite word.

## Three finite-word contradictions

The following complete finite-word constructions check their endpoint
signs for the restricted minimum above. The first two use arbitrarily
small product rows; the third uses subdivided finite solo macrosteps.

**A. Nonnegative columns.** If column j of G is nonnegative, use N solo-j
dates of absolute mass f/N, for small fixed f>0, then X. The conditional
hazards have sum at most f/(1-f), which is chosen within the outsider bound.
Mover j stays at payoff/cap zero. An observer i in T has payoff f G_ij>=0.
An internal deadline exceeds it by at most M f/N (joining changes only the
current atom), and continuing into X gives that payoff. Thus debts vanish;
survival is exactly 1-f. This excludes every nonnegative column. For |T|=1
it already excludes the source, and for |T|=2 it forces both off-diagonals
strictly negative.

**B. Homogeneous complementary directions.** Suppose v>=0 is nonzero,
Gv>=0, and v_i(Gv)_i=0. Normalize sum v_i=1. Repeat q_T=epsilon v for
K=floor(tau/epsilon) dates, where 0<tau<=b/(16M) is fixed. Its survival
c^K tends to exp(-tau). Uniformly in the finite table,

    P_i=epsilon(Gv)_i+O(epsilon^2), Q_i=O(epsilon).

For active i, (Gv)_i=0, so prescribed payoff and full debt are O(K epsilon^2
+epsilon), tending to zero. For inactive i, its payoff is
P_i sum_(s<K)c^s. A deadline can gain at most O(epsilon+K epsilon^2):
if P_i>=0 its earlier passive partial sum is no larger than the whole sum;
if P_i<0 then |P_i|=O(epsilon^2). Through-tail responses give the displayed
payoff. Thus all debts vanish. At least one active coordinate has limiting
payoff zero, so the comparison rule applies. Hence G is R0, including all
degenerate homogeneous directions.

**C. An expanding signed cycle.** Suppose |T|=3, with indices modulo3,

    G_i,i+1=-A_i<0, G_i,i-1=B_i>0,
    rho=(B0 B1 B2)/(A0 A1 A2)>1.

Starting from virtual observer payoff/cap x e_i, a solo-(i+1) macrohazard
q=x/(A_i+x) gives payoff zero at i and at the mover, and moves the positive
axis to i-1 with amplitude B_(i-1)x/(A_i+x). Three such macrosteps return
to the original axis with

    F(x)=rho x/(1+C x),
    C=(A1 A2+A1 B2+B1 B2)/(A0 A1 A2)>0             (axis0).

Choose 1<r<rho and small fixed a with C a<=rho-r. Set x_0=a and
x_(n-1)=x_n/(rho-C x_n), n<=0. Then x_-m<=a r^-m. All intermediate
amplitudes and hazards are bounded by constants times their input, so
the words from x_-m to a have total macroactivity O(a) and contain a fixed
nonzero final macrohazard q_*.

Subdivide a macrohazard q into ell microhazards eta_l=q/(ell-l q),
0<=l<ell. Their survival is 1-q, their sum is at most q/(1-q), and their
maximum can be arbitrarily small. Throughout a macrostep, the observer
payoffs are nonnegative, the moving owner's payoff is zero, and the
coordinate being extinguished ends at zero. If all eta_l<=delta, (1) gives

    d'_mover=d_mover,
    d'_i=max(eta_l J_i,mover-U'_i,(1-eta_l)d_i)
          <=max(M delta,d_i), i!=mover.

Thus virtual observer debts stay at most M delta regardless of word length.
Choose a so total microactivity obeys the outsider bound, and let delta->0
as m->infinity. Applying the words to X changes each final payoff and cap
by at most x_-m. The E limit has core payoff a e_0, hence TWO zeros, while
survival is at least 1-total activity and at most 1-q_*<1. This is eligible
for the ORIGINAL m, and is impossible. This argument needs no signs of J
or higher rewards; these enter only the vanishing microhazard bound.

## Exhaustive zero-diagonal matrix argument

Cases |T|<=2 were handled by A. For |T|=3, A gives a strictly negative entry
in every column. Suppose x>=0, x!=0, Gx>=0. Support one would give a
nonnegative column. If support is {i,j}, then G_ij,G_ji>=0; the required
negative entries in columns i,j must both be in the third row k, giving
(Gx)_k<0. Therefore x>0.

A row cannot have two strictly negative off-diagonals, since x>0 and
Gx>=0. There are at least three strictly negative entries, one per column,
and at most three, one per row. Hence there is exactly one negative entry
in every row AND every column. Each row then needs a strictly positive
other off-diagonal entry to have nonnegative product with x. Thus there
is exactly one strictly positive and one strictly negative entry per row
and column. Relabel into the cycle in C. Multiplying Gx>=0 gives product B>=product A.
Equality forces all three row products to be zero, contradicting B above.
Strict inequality is exactly the expanding cycle excluded by C. This proves
(N) without discarding any zero entry or equality case.

For the dual, the compact convex set {Gx:x>=0,sum x=1} is disjoint from
the closed nonnegative orthant. Strict separation gives y>=0 with
max_j(y^T G)_j<0. Perturb y by a sufficiently small positive multiple of
the all-ones vector to obtain y>0 with the same strict inequalities.
Conversely this dual immediately implies(N).

Finally, if a column of L=J-Gamma on T were nonpositive, a small exact
solo row at its mover would have zero mover payoff, all zero observers
preferring Continue, and positive outsiders strictly quiet. It would
directly contradict m. Hence each L column has a positive entry, giving
the two reciprocal strict joining inequalities when |T|=2.

## The entire three-zero pencil has degree zero

Assume |T|=3 and, ONLY for this corollary, every off-diagonal L_ij is
nonzero and det L!=0. Put M(t)=G-tJ, 0<=t<=1. A matrix A is R0 when
x>=0, Ax>=0, x_i(Ax)_i=0 force x=0. Its homogeneous complementarity
degree is the local Brouwer degree at zero of f_A(x)=min(x,Ax), with
the minimum coordinatewise. Then EVERY M(t) is R0 and has degree ZERO.
In fact every M(t) has its own strict negative left certificate.
This is a necessary RAW condition for the actual restricted source above;
the unrestricted-alpha degree-one argument is not being invoked.

First, for 0<t<1 no column of M(t) can be nonnegative. If column j were
nonnegative, fix small f>0 and set

    R_n=f(1-t)^n, S_n=1-f+R_n, r_n=R_n/S_n, q_n=t r_n.

Only mover j acts at chronological date n. The virtual observer suffix
payoff/cap is G_ij r_n for i!=j, and zero for j. The identities
1-q_n=S_(n+1)/S_n and q_n+(1-q_n)r_(n+1)=r_n make Continue equal that
suffix value; Quit is t J_ij r_n, no larger. Every row is exactly Nash
on the virtual observer diagonal, which may have negative coordinates.
The sum of hazards is at most f/(1-f), and survival tends to 1-f. Truncate
and replace the vanishing virtual terminal observer diagonal by X. The
comparison rule gives E with mover payoff zero and Never (1-f)m<m.

If M(t) has a nonzero homogeneous complementary vector with support two,
the reciprocal entries on that pair must both vanish. The third-row
nonnegative product forces at least one remaining column entry nonnegative,
hence a nonnegative column, already excluded. Support one is precisely
such a column. Full support gives v>0 and (G-tJ)v=0. Since the theorem
provides y>0 with y^T G<0, we have y^T Jv=(y^T Gv)/t<0. Thus some
coordinate of Jv is strictly negative.

Here the existing expanding-mode construction applies on the zero core:
L^-1J v=rho v, rho=1/(1-t)>1. For completeness its exact orbit has

    z_i(q)=(Q_i(q)-P_i(q))/H_i(q), s_i(q)=Q_i(q),
    F=z^-1 composed with s, F(q)=L^-1J q+O(|q|^2),
    F(q_n)=q_(n+1),
    q_n=a rho^n v+O(a^2 sigma^n), n<=0, rho<sigma<rho^2.

The inverse function theorem defines F with a quadratic remainder R
satisfying |R(q)|<=C|q|^2 and
|R(q)-R(r)|<=C' max(|q|,|r|)|q-r| near zero. The positive backward orbit
does not require eigenvalue simplicity. Choose rho<sigma<rho^2 avoiding
every eigenvalue modulus of A=L^-1J. Split into invariant spaces E_s,E_f
below and above sigma, using equivalent norms with
||A_s||<=alpha_s<sigma<alpha_f and ||A_f^-1||<=1/alpha_f.
For forcing f_n,n<0, define on n<=0

    (Kf)^s_n=sum_(k=-infinity)^(n-1) A_s^(n-1-k)f^s_k,
    (Kf)^f_n=-sum_(k=n)^(-1) A_f^(n-1-k)f^f_k.

Empty blocks are omitted. In the norm ||w||_sigma=sup sigma^-n|w_n|,
K has norm at most1/(sigma-alpha_s)+1/(alpha_f-sigma), and direct
cancellation gives (Kf)_(n+1)-A(Kf)_n=f_n. The adapted norms exist from
the convergent norm sum c^-k|A^k x| when the spectral radius is below c,
applied also to the inverse on E_f.

Set z_n=a rho^n v. On ||w||_sigma<=B a^2, the map w->K(R(z+w)) has
norm O(a^2) and Lipschitz constant O(a), since
rho^(2n)<=sigma^n<=rho^n for n<=0. Choose B larger than twice the fixed
quadratic bound, then small a. Banach contraction gives the stated orbit.
The error is at most B a^2 sigma^n; positivity follows uniformly from
sigma^n<=rho^n and v>0. Its total activity is O(a), and all hazards are
proper when a is small enough.

The physical finite words are q_0,q_-1,...,q_-m, with virtual terminal
observer diagonal z(q_-m). The identity z(q_(n+1))=s(q_n) makes all
observer rows exactly indifferent. Initial mismatch tends to zero, total
activity is O(a), survival is bounded away from both0 and1, and final
observer payoff is Q(q_0)=a Jv+O(a^2). Its strictly negative coordinate
makes the limiting actual E comparison eligible for m. This contradiction
excludes full support. Hence M(t) is R0 for every 0<t<1.

The endpoint G is R0 by B. At M(1)=-L, a singleton homogeneous support
would give a nonpositive L column, already excluded by exact solo. A pair
support would force two reciprocal L entries zero, and full support would
force det L=0. Our stated genericity therefore makes -L R0 as well.

For any R0 A, homogeneity and compactness give |f_A(x)|>=c_A|x|, c_A>0.
Along the compact R0 pencil this bound is uniform, so Brouwer homotopy
invariance makes its degree constant. At G, the offset problem
min(x,Gx-one)=0 has NO solution: it would require x>=0 and Gx>=one,
contradicting y^T G<0. The maps min(x,Gx-u one), 0<=u<=1, differ from
f_G by at most |one| and have no zero on a sufficiently large sphere.
The last map has no zero anywhere, so degree_R0(G)=0 as claimed.

Finally each M(t) has a negative entry in every column, also at t=0,1.
If it had a nonzero x>=0 with M(t)x>=0, the zero-diagonal count above
would force a strict signed cycle. Equality of its two products contradicts
R0. Strict positive-product dominance gives det M(t)>0 and M(t)^-1>0;
at offset -one the unique complementary solution is M(t)^-1 one>0,
with local index +1, contradicting degree zero. Thus the same strict
separation argument gives a positive negative-left certificate for EACH
matrix of the pencil. No common certificate independent of t is claimed.

For |T|=2, both G off-diagonals are negative and both L off-diagonals
are positive. Thus M(t)=(1-t)G-tL has negative off-diagonals throughout.
The vector(1,1) is already a strict negative left certificate. The same
offset argument proves degree zero, without extra genericity.

## An actual local positive-to-zero repair

There are four players, independent complete stopping laws on Nat and a
distinct Never label, native own-singleton/live/AllNever rewards0, and
|Z_i(S)|<=M with M>=1. Every unilateral whole-law replacement is allowed.
C is the compact closure of actual(U,B,e,N), with full behavioral caps B
and ORIGINAL Never N. Set E={B=U}, nu=product N_i. On E with nu>0, U=B=e.

Fix a proper nonempty set T, write Gamma_ij=Z_i({j}), J_ij=Z_i({i,j})
and L=J-Gamma, all with diagonal0. Assume

    y>0, y^T Gamma_T<=-c one^T, c>0;
    A=-L_T is R0 and has complementarity degree0.             (H)

Here R0 means f_A(q)=min(q,Aq) has no zero except0 on ALL real q, with
coordinatewise min. Degree0 means its Brouwer degree on a ball around0.
Put Y=sum_T y_i, y_*=min_T y_i and choose any b>0. Define

    a=min_{||q||_1=1} ||f_A(q)||_infinity>0,
    r=min(1/4,a/(16M),b/(16M),c/(4MY)),
    epsilon=min(y_* a r/16,bc/(32M),c/16)>0.                 (C)

The a-minimum is over the FULL real sphere, including negative q.

**Theorem.** Let V in E have original nu(V)>0, payoff v>>0, and

    v_p>b/2 for p notin T, z0=y·v_T<epsilon.

There exists Z in E with min_i U_i(Z)<=0 and

    0<nu(Z)<nu(V),
    nu(Z)<=(1-eta/(12M))nu(V), eta=min_(i in T)v_i>0.        (G)

All roots, finite words and limiting tuples used to produce Z are built
below. No supplied continuation, calendar bound, regular root, common
pencil weight, or source realizer is required.

### A produced nonzero small root at every positive core input

Restrict root activity to T. For i in T let Q_i(q),P_i(q),H_i(q) be its
forced Quit, passive nonempty-opponent offer, and opponent survival. These
are the ordinary product polynomials; extend them polynomially to real q
only for degree. For positive input w_T with V0=||w_T||_infinity define

    g_w(q)=min(q,P(q)+H(q)w_T-Q(q)),
    B_r={q in R^T:||q||_1<r}.

For q>=0, ell=sum q_i<=r, direct singleton/nonsingleton expansion gives

    |P_i-(Gamma_T q)_i|<=2M ell^2,
    |Q_i-(J_T q)_i|<=2M ell^2,
    |H_iw_i-w_i|<=ell V0.

Hence the second argument of g_w differs from Aq by at most
V0+4M ell^2+ell V0 in sup norm. Assume V0<=ar/8. A zero of ANY homotopy

    min(q,(1-t)Aq+t[P(q)+H(q)w_T-Q(q)]), 0<=t<=1,

necessarily has q>=0: a negative coordinate would make that min negative.
At a boundary zero ell=r, coercivity gives ar<=V0+4Mr^2+rV0,
but the right side is at most(1/8+1/4+1/32)ar<ar, contradiction.
Thus degree(g_w,B_r,0)=degree(f_A,B_r,0)=0. At q=0 all w_i>0, so g_w(q)=q
in a neighborhood of0, with isolated local index+1. Excision forces some
OTHER zero in B_r. It is a nonzero proper Nash root on T.

Every root in B_r also obeys

    a ell<=V0+4M ell^2+ell V0<=V0+(9a/32)ell,
    ell<=32V0/(23a)<2V0/a.                               (S)

For a full input whose outside payoffs exceed b/4, this is a FULL Nash
root: r<=b/(16M) makes an outsider's Continue offer at least b/4-2Mell
>=b/8, above its Quit offer at most Mell<=b/16. All outsiders stay quiet.

### Iteration stays local and produces an actual eligible endpoint

Start V^0=V. At a positive V^n choose the nonzero small root just produced
at w=U(V^n), and PREFIX it to V^n to obtain V^(n+1). Continuous full-cap
prefix identities put V^(n+1) in E, retaining original N multiplicatively.
If its payoff has a nonpositive coordinate, stop. Otherwise repeat.

Write ell_n=sum q_i^n, h_n=product(1-q_i^n), z_n=y·U_T(V^n).
The expected one-stage payoff F_i=q_iQ_i+(1-q_i)P_i satisfies

    |F_i(q)-(Gamma q)_i|<=2M ell^2.

Indeed singleton probability corrections cost at most M ell^2 and the
probability of at least two Quit actions is at most ell^2/2. Thus, whenever
both the old and new core payoffs are positive, (H),r<=c/(4MY) give

    z_(n+1)=y·F_T(q^n)+h_n z_n<=z_n-(c/2)ell_n.           (D)

This preserves V0<=z0/y_*<ar/16, so the next small root exists. Over every
initial run with positive outputs, sum ell_n<=2z0/c<1/8. Each prefix changes
any payoff by at most2Mell_n; hence outsiders remain above
b/2-4Mz0/c>3b/8>b/4. Both localization conditions are therefore preserved
inductively, without assuming the desired return or transferring a minimum.

If iteration is infinite, the total activity is summable by(D). Payoffs
are Cauchy by the same2M bound. Original N converges multiplicatively;
the joint new survival is at least1-sum ell_n>7/8. Every intermediate tuple
is in E, so the compact actual closure supplies an E limit Z with positive
original nu. If all limiting core coordinates stayed positive, some eta0>0
would bound every late core input below. At an active coordinate,

    w_i=Q_i-P_i+(1-H_i)w_i<=3Mell_n,

using |w_i|<=M. Thus every nonzero root would have ell_n>=eta0/(3M),
contradicting summability. The limit has a zero core coordinate and is
eligible. In the finite stopping case the new tuple itself is eligible.

This iteration is in CONSTRUCTION order: its physical finite words are
q^n,...,q^0 over actual approximants to V. Their compact limit is legitimate
in C; no infinite reverse word or continuation after omega is executed.

### Exact original-Never gain and selected-source consequence

The FIRST root has an active coordinate with w_i>=eta. The preceding bound
gives ell_0>=eta/(3M), so max_i q_i^0>=eta/(12M) and
h_0<=1-eta/(12M). Every later prefix only decreases original nu. In the
infinite case the limit retains that first factor; in the finite case
there are finitely many proper factors. This proves all of(G), including
strict decrease and positivity of the new original Never product.

Now let X be a proper nonnegative ORIGINAL restricted minimum m, with
T={i:U_i(X)=0}, b=min_(p notin T)U_p(X)>0. Whenever its raw data satisfy(H),
every sufficiently nearby positive E point V obeys

    nu(V)>=m/(1-min_T U_i(V)/(12M))>m.                     (M)

Indeed the constructed endpoint is eligible for the SAME global m. The
proper-zero theorem supplies(H) for two zeros, and for three zeros under
its stated joining genericity. This is a local quantitative exclusion of
actual low-Never positive points; it does not assert that an inherited
payoff-fibre minimum satisfies(H), or exclude finite-amplitude jumps.

## Uniform buffer through m and a finite actual crossing

Define A_Z=inf{D(P):P actual,nu(P)=0}, D=sum_i(B_i-U_i), and assume A_Z>0,
0<m<1, with m the same restricted minimum. Assume L_ij!=0 for every i!=j
and det L_SS!=0 for every three-element S, so the proper-zero classification
used in(M) supplies(H) at EVERY proper nonnegative m-minimizer. No alpha-source or
positive initial point is assumed to exist in this compactness statement.
If the set below is nonempty, it is compact and has a uniform buffer:

    P_m={Y in E:nu(Y)<=m,U(Y)>>0},
    kappa=min_(Y in P_m) min_i U_i(Y)>0.                    (K)

First, moving the smallest original Never atom to one finite date produces
an absorbing profile. Its own cap is unchanged; four prescribed payoffs and
three other full caps change by at most2M times that mass. Thus
A_Z<=D+14M nu^(1/4), also on C; in particular all E points have positive nu.

There is no E point with all payoffs0 and0<nu<=m. To see this, take finite
actual approximants, obtained by moving sufficiently late finite mass to
the SAME owners' Never labels. Complete response values change uniformly
by at most2M times the total moved mass, so all(U,B,e,N) still converge.
Pad each finite block with an unused last date and concatenate two private
independent copies, the second used after the owner's first Never draw.
The padded date represents the old Never response as a finite query. Exact
complete-law formulas are

    U_i'=(1+nu)U_i, B_i'=max(B_i,e_i+H_i B_i),
    e_i'=(1+H_i)e_i, N_i'=N_i^2, H_i=product_(j!=i)N_j.

At a zero-payoff E limit, positive original nu gives B=e=0; hence the
two-copy E limit has original nu'=nu^2<nu. If such a point had nu<=m,
eligibility would give nu>=m, and its two-copy competitor would contradict
m. This is the only zero-payoff renewal conclusion needed here; no copy
is executed after an infinite natural calendar.

Now let Y_n in P_m converge in compact C to Y. Its payoff is nonnegative,
it lies in E and nu(Y)<=m. If it loses strict positivity, it is eligible,
so nu(Y)=m. It cannot have all payoffs0 by the preceding two-copy argument
and m<1. Its zero set is proper, and(M) excludes nearby positive E points
with nu<=m, contradicting Y_n. Thus P_m is closed and(K) follows. Negative
m-minimizers cannot be limits of positive payoffs and cause no extra case.

Here is a complete actual incoming-row producer using that SAME kappa.
For any Y in P_m put delta=kappa/(16M)<=1/16. Take actual approximants P_n
with D_n->0 and initial prescribed payoffs>=3kappa/4. Their original Never
coordinates are positive for large n, so all conditional hazards are proper.
Stop at the first date whose row activity ell>=delta or whose PRIOR
cumulative activity reaches delta. Before that stop every row has ell<delta
and prior activity<delta. Conditional prescribed payoffs change by at most
2M times cumulative activity, so they stay>=5kappa/8; Quit offers are at
most Mell<=kappa/16. Therefore Continue is the full-cap branch and the
exact nonnegative root-debt identity charges at least(kappa/2)ell per row.
Joint prior reach is at least1-2delta, giving

    cumulative prior activity<=2D_n/[kappa(1-2delta)].      (I)

A cumulative-activity stop would have prior activity in[delta,2delta),
contradicting(I) for large n. If no stop existed, the same debt bound would
hold for the entire infinite profile, forcing its total activity to0 with
D_n; then |U_i(P_n)|<=M times total activity would contradict3kappa/4.
Hence there is a first macroscopic row and its preceding activity tends0.

Delete that preceding segment and retain the conditional tuple at the
macroscopic row. Its U,e change by at most2M times the deleted activity;
its N changes by at most that activity. Before the stop every cap is on
Continue, so its B also changes by at most2M times that activity. Thus the
tuple converges to the SAME Y, including ORIGINAL N. Extract the row q
and its actual conditional tail Z. Then ell(q)>=delta and
1-q_i>=N_i(Y)>0. In particular h(q)>=nu(Y)>0. Nonnegative debt recursion
therefore puts Z in E, and continuity gives Y=prefix_q Z with

    nu(Z)=nu(Y)/h(q)>=nu(Y)/(1-delta/4).                    (X)

The cut dates may escape; only their preceding activity was collapsed.
No escaping finite mass was added to Never, and Z inherits no minimum.

Starting from ANY given positive Y0 in E with nu0<=m, use this producer
while its tail remains positive and has nu<=m. Set gamma=-log(1-delta/4)>0.
After at most

    1+floor(log(m/nu0)/gamma)                              (N)

retained cuts, the genuine finite Nash head reaches either an eligible
point with nu=m or a point with nu>m. Indeed (X) increases nu by at least
exp(gamma) per cut; an eligible point with nu<m is impossible. Original
source(U,B,e,N) is preserved through the whole extracted head. The bound
counts macroscopic retained cuts, not empty physical dates.

Since every E point has nu0>=beta=(A_Z/(14M))^4, this count is uniformly
bounded over ALL starting Y0 in P_m by replacing nu0 with beta in(N).

This removes the s-up-to-m buffer degeneration on the m<1 generic branch.
It does not consume a finite-amplitude jump to nu>m, identify its tail as
minimum, or settle m=1. At m=1 an all-zero limit can be literal AllNever,
so the same compactness argument cannot remove that endpoint.

### The positive sublevel has finite Nash-prefix height

Every Nash prefix of a point in P_m remains in P_m. A sure prefix would
give E with nu=0, contradicting A_Z>0. Any nonzero proper prefix has
nu'<nu<=m, so a nonpositive output would contradict the definition of m.
An AllContinue prefix leaves the tuple unchanged.

Write kappa for(K). At a positive input in P_m, a root with activity
ell<kappa/(4M) makes every Continue offer at least kappa-2Mell>kappa/2,
above its Quit offer<=Mell<kappa/4. Thus any NONZERO Nash prefix has
ell>=kappa/(4M), and survival at most theta=1-kappa/(16M)<1.
Along any sequence of such prefixes nu decreases by at least this factor,
while nu>=beta. Its length is therefore at most

    floor(log(m/beta)/[-log(theta)]).

Consequently every maximal nonzero-prefix chain terminates at a point whose only
Nash root is AllContinue. This is a finite-height statement about the
positive semantic sublevel, not a finite-calendar representation theorem
for its points or a joint-return consumer.

### Complete actual positive-input boundary test

Set d=1/8192. For nonempty S contained in012, define rows0,1,2 by this table;
set Z3(S)=1. For EVERY coalition containing3, set ALL FOUR rewards0.

| S | Z0 | Z1 | Z2 |
|---|---:|---:|---:|
|0|0|-1|1|
|1|-1|0|1|
|2|1|1|0|
|01|1|1|2|
|02|-1|4d|1|
|12|4d|-1|1|
|012|4d|4d|2|

The actual one-date row(1/2,1/2,1/2,0), then AllNever, has Q=P=d,d,1 for
owners0,1,2, and owner3 has Q3=0,P3=7/8. These are its FULL caps, including
Never and every later deadline. Thus V in E has U=(d,d,1,7/8),
N=(1/2,1/2,1/2,1),nu=1/8. On T=01, Gamma off-diagonal=-1,J=1,L=2;
y=(1,1),c=1, and A has off-diagonal-2. It is R0; min(q,Aq-one)=0 has no
solution, so the bounded-offset homotopy gives degree0. Its full-sphere coercivity is
a=1/2 (a negative largest coordinate gives at least1/2, a positive largest
coordinate gives at least1 in the other component; equality at(-1/2,-1/2)).
With M=2,b=7/8, (C) gives r=1/64,epsilon=1/2048 and z0=2d<epsilon.

At a current core payoff(x,x), prefix(q,q,0,0), q=x/(2+x). Active Quit and
Continue offers are both q. For owner2 they are2q and2q+(1-q)^2 U2;
for3 they are0 and2q-q^2+(1-q)^2 U3. Both outsiders stay strictly quiet.
Hence x_n=d/[2^n(1+d)-d], and the per-owner head survival telescopes to
product_(j<n)(1-q_j)=2^n x_n/d ->1/(1+d). The finite FULL Nash words
therefore converge in C to an eligible E point with original
nu=1/[8(1+d)^2]<1/8, verifying the repair and its stated gain. Pure01 is
already absorbing full Nash with payoff(1,1,2,1); this is only an actual
scope/boundary test, not a positive-gap example or additional UE coverage.


## A finite landing is necessary

Choose c>0 with y^T G<=-c one^T. Put Y=sum_T y_i, b=min_(p notin T)u_p>0, and

    delta=min(1/4,b/(4M),c/(4MY))>0.

**Corollary.** Suppose successive genuine incoming zero-debt roots from an
all-positive E point stay all-positive before landing at X, either at a
finite cut or as their conditional tuples converge to X. The asymptotic
alternative is impossible. In the finite alternative the LAST root has
sum_i q_i>=delta and joint survival at most1-delta/4. No bound on empty
AllContinue dates is asserted. This does not construct a different return.

**Proof.** For a product root q set ell=sum q_i, h=product(1-q_i), Q_i its
forced-Quit offer, P_i its passive nonempty-opponent offer, H_i=product_(j!=i)
(1-q_j), and F_i=q_iQ_i+(1-q_i)P_i. Uniformly over all higher rewards,

    |Q_i(q)|<=M ell, |F_i(q)-(Gamma q)_i|<=2M ell^2.             (1)

For the second bound, replacing singleton probabilities by q_j costs at
most M ell^2; nonsingleton probability is at most ell^2/2. Own singleton0
proves the first. Exact prefix/debt identities give

    u^t=F(q^t)+h_t u^(t+1), q_i^t>0 => Q_i(q^t)=u_i^t.

In the asymptotic case full tuple convergence to X with nu(X)=m>0
lets us first reindex at a sufficiently late positive-Never point.
Original Never conditions as N_i^t=(1-q_i^t)N_i^(t+1). Thus positive
nu_0 at the initial point gives product_(t<L)h_t>=nu_0 for EVERY L and
sum_t ell_t<=-log(nu_0)<infinity. In particular ell_t->0; no escaped
finite activity is being relabeled Never. In a hypothetical infinite
landing at X, every positive outsider eventually has u_p^t>b/2>M ell_t,
so its hazard is exactly0 by(1). All late q are supported on T. Positivity
of u_T^(t+1), the strict dual and(1) then imply

    y·(u_T^t-u_T^(t+1))
      =y·F_T(q^t)-(1-h_t)y·u_T^(t+1)
      <=-c ell_t+2MY ell_t^2<=-(c/2)ell_t.

Hence y·u_T^t is eventually nondecreasing and strictly positive, impossible
when u_T^t->u_T=0. A terminal run of zero roots cannot change that fact.
For the finite last-root floor, more generally take ANY Nash root at X
with positive output and ell<delta. Each outsider has Continue offer
P_p+H_pu_p>=b-2M ell>b/2 and Quit offer<=M ell<b/4, so is quiet. The
weighted output on T is y·F_T<=-c ell+2MY ell^2<0 if ell>0; ell=0 leaves
zeros. Both contradict positive output. Thus ell>=delta, and max q_i>=
ell/4 gives h<=1-delta/4. All tuples and roots above are genuine conditional
limits of actual approximants; the reindexed asymptotic chain has positive
original Never, ensuring proper conditioning there.


## Strict extension beyond the solo criterion and bounded overlap

Take core T=012, G=[0,-1,2;2,0,-1;-1,2,0], and J=G+one off diagonal.
Every G column has a negative entry and every L column is positive, so NO
exact or diffuse solo covers this zero set. Nevertheless rho=8 and the
theorem excludes it as a selected m-source, for all finite higher rewards.

There is also an actual positive-Never boundary fixture with these pair data.
For core recipient i, give own singleton0, off-own singleton G_ij, own pair
J_ij, opponent pair -1, and core triple -3. Core rewards ignore membership
of owner3; if the core coalition is empty use0. Owner3 gets1 on nonempty
core coalitions excluding3, and0 on coalitions containing3. The one-date
profile q=(1/2,1/2,1/2,0), then AllNever, has Q_i=P_i=0 for i in T;
owner3 strictly prefers Continue. Thus it is actual E with
U=(0,0,0,7/8), N=(1/2,1/2,1/2,1), nu=1/8. The theorem proves that it
cannot attain m. This fixture has an absorbing pure pair equilibrium and
therefore A_Z=0; it is a scope/separation check, not counterexample evidence.

The fixture separates the new selected-source consumer from the exact and
diffuse solo column tests: neither test can start on its zero set. It is
not a new UE existence class. The finite-word and expanding-clock producers
are not credited as new architectures. No row raises, selected favorable
strategy, punishment-tail admission failure or unverified all-game claim is
being used to establish this source exclusion.

## Exact boundary: pointwise pencil duals need not have a common weight

The pencil condition does not imply a single y valid for every t. Indeed
consider

    M(t)=[0,-1,2-17t/10;
          3/10+17t/10,0,-1;
          -1,3/10,0], 0<=t<=1.

The negative cycle product is1. The positive product is at most
(3/10)(23/20)^2=1587/4000<1. Thus every matrix has a strict negative left
certificate and degree zero by the signed-cycle calculation above.
A common positive y would require y2>2y1, y0>(3/10)y2, and y1>2y0
from columns0,1,2 at their respective worst endpoints, giving
y1>(6/5)y1. This is impossible. This is an algebraic boundary test,
not an actual minimum-source or positive-gap counterexample.

## Complete exact boundary check

The following standard-library program verifies every offer of the ACTUAL
one-date fixture, its original Never coordinates, its absorbing pure pair,
the exact expanding-axis calculation and rational product gap, and the
actual local-repair fixture with all full caps, constants and original-N
gain. It has no data-file input or numerical root decisions;
the preceding proofs supply the full interval and source quantifiers.

```python
from fractions import Fraction as F
from itertools import combinations
G=[[0,-1,2],[2,0,-1],[-1,2,0]]
J=[[0 if i==j else G[i][j]+1 for j in range(3)]for i in range(3)]
def reward(i,S):
    core=set(S)&{0,1,2}
    if i==3:return F(bool(core)and 3 not in S)
    if not core:return F(0)
    if len(core)==1:return F(G[i][next(iter(core))])
    if len(core)==2:
        if i in core:return F(J[i][next(iter(core-{i}))])
        return F(-1)
    return F(-3)
def offers(i,q):
    others=[j for j in range(4)if j!=i];Q=F(0);P=F(0)
    for n in range(4):
        for sub in combinations(others,n):
            S=set(sub);mass=F(1)
            for j in others:mass*=q[j]if j in S else 1-q[j]
            Q+=mass*reward(i,S|{i})
            if S:P+=mass*reward(i,S)
    return Q,P
q=[F(1,2)]*3+[F(0)];U=[]
for i in range(4):
    Q,P=offers(i,q);u=q[i]*Q+(1-q[i])*P
    assert max(Q,P)==u
    U.append(u)
assert U==[0,0,0,F(7,8)]
nu=F(1)
for x in q:nu*=1-x
assert nu==F(1,8)
S={0,1}
for i in range(4):
    deviation=S-{i}if i in S else S|{i}
    assert reward(i,S)>=reward(i,deviation)
print('PASS: actual zero-debt fixture, original Never1/8, absorbing pure pair.')
# Neither column solo test can start on the three-zero block.
assert all(any(G[i][j]<0 for i in range(3))for j in range(3))
assert all(any(J[i][j]-G[i][j]>0 for i in range(3))for j in range(3))
x=F(1,100);w=[x,F(0),F(0)]
for mover,extinguished in [(1,0),(0,2),(2,1)]:
    hazard=w[extinguished]/(1+w[extinguished])
    w=[(1-hazard)*w[i]+hazard*G[i][mover]for i in range(3)]
    assert all(v>=0 for v in w)and w[mover]==0 and w[extinguished]==0
assert w==[8*x/(1+7*x),0,0]
assert w[0]>x
# A surviving raw pencil with one common negative left certificate.
H=[[0,-2,1],[1,0,-2],[-2,1,0]]
for j in range(3):assert sum(H[i][j]for i in range(3))==-1
# Its J has all off-diagonal entries2, so column sums are -1-4t.
# The pointwise/common-left separation example has strict product gap.
assert F(3,10)*F(23,20)**2==F(1587,4000)<1
for t in (F(0),F(1,2),F(1)):
    product=F(3,10)*(F(2)-F(17,10)*t)*(F(3,10)+F(17,10)*t)
    assert product==F(3,10)*(F(23,20)**2-F(17,10)**2*(t-F(1,2))**2)<1
print('PASS: expanding-axis identity, surviving pencil, strict product gap.')
# Complete actual positive-input fixture for the raw repair.
d=F(1,8192)
local={1:(0,-1,1),2:(-1,0,1),4:(1,1,0),3:(1,1,2),
       5:(-1,4*d,1),6:(4*d,-1,1),7:(4*d,4*d,2)}
def reward(i,S):
    if 3 in S:return F(0)
    if i==3:return F(1)
    return F(local[sum(1<<j for j in S)][i])
values=[];q=[F(1,2)]*3+[F(0)]
for i in range(4):
    Q,P=offers(i,q);u=q[i]*Q+(1-q[i])*P
    assert max(Q,P)==u
    values.append(u)
assert values==[d,d,F(1),F(7,8)]
M=F(2);b=F(7,8);coercivity=F(1,2);c=F(1);Y=F(2)
r=min(F(1,4),coercivity/(16*M),b/(16*M),c/(4*M*Y))
epsilon=min(coercivity*r/16,b*c/(32*M),c/16)
assert r==F(1,64)and epsilon==F(1,2048)and 2*d<epsilon
head=F(1);x=d
for n in range(1,13):
    hazard=x/(2+x);q=[hazard,hazard,F(0),F(0)];updated=[]
    for i in range(4):
        Q,P=offers(i,q);H=F(1)
        for j in range(4):
            if j!=i:H*=1-q[j]
        C=P+H*values[i]
        assert Q==C if q[i]>0 else Q<=C
        updated.append(q[i]*Q+(1-q[i])*C)
    values=updated;x=hazard;head*=1-hazard
    assert x==d/(2**n*(1+d)-d)and values[0]==values[1]==x
    assert head==2**n*x/d
assert F(1,8)/(1+d)**2<F(1,8)
assert 1/(1+d)**2<=1-d/(12*M)
for i in range(4):
    S={0,1};deviation=S-{i}if i in S else S|{i}
    assert reward(i,S)>=reward(i,deviation)
print('PASS: actual local repair, all full caps, constants, original-N gain.')
```

## Finite raw test and Lean handoff

For a triple, the whole-pencil dual condition has a finite exact test.
Split[0,1] at the at most six roots of its off-diagonal linear entries.
Every column must have a negative entry on each cell and at each endpoint.
If a sign cell is a strict signed cycle, its positive cycle product minus
its negative cycle product, a cubic in t, must be strictly negative there.
All other column-negative sign patterns automatically admit a strict
negative left certificate by the exhaustive zero-diagonal argument above.
At an entry-zero breakpoint the same count rules out semipositivity once
column negativity is checked. Identically zero entries are retained.
Thus this tests the necessary raw condition without sampling t; it does
not produce a source or prove UE for matrices passing the test.

Suggested formal theorem shapes use the actual tuple carrier, the original
minimum over min U<=0 and its proper zero set. Separate the three finite-word
constructions and their ZERO/NEGATIVE endpoint eligibility, the zero-diagonal
three-by-three classification, convex separation, the expanding-mode orbit,
the R0 degree-zero pencil, small-root degree excision, actual iterative
repair, two-copy renewal, uniform positive sublevel and cofinal finite
crossing, and the finite-landing estimate. No field should
assume the comparison word, negative endpoint or desired strict dual.
The existing prefix identities are
`quittingContinuationBestResponseValue_rootThenContinuation_eq_max`,
`quittingTerminalDeviationDebt_nonneg`, and
`quittingTerminalDeviationDebt_rootThenContinuation_eq`
(`UniformEquilibrium/Quitting/Root/TerminalDebtPrefix.lean`), and
`quittingTerminalPayoff_rootThenContinuation_eq`
(`UniformEquilibrium/ProofView/Concepts/Stochastic/Models/Quitting/RootContinuation.lean`).
They concern the full behavioral cap and literal prescribed payoff.
Generic degree interfaces already include
`ambientDegree_lcpMinMap_zero_eq_r0Degree`
(`MathUE/LinearProgramming/R0AmbientDegree.lean`),
`exists_radius_above_ambientDegree_lcpMinMap_eq_r0Degree`
(`MathUE/LinearProgramming/R0AmbientOffsetDegree.lean`), and
`r0Degree_eq_sign_det_of_nonnegative_inverse`
(`MathUE/LinearProgramming/NonnegativeInverseDegree.lean`). Reuse these
for the ambient/local degree translation and the positive-inverse case.
The principal selected-zero-set pencil above has degree zero. The FULL
original singleton degree-one interface is
`finFour_singleton_r0Degree_eq_one_of_no_uniformPayoff`
(`UniformEquilibrium/Diagnostics/Quitting/FinFourSingletonDegreeCriterion.lean`),
with recipient-row invariance given by `quittingSingletonMatrix_sub_payoff`
(`UniformEquilibrium/Quitting/Classification/LCP/QuittingRewardAdapter.lean`).
It applies to an original no-UE table and its anchored full singleton
matrix. The present proof does not identify that original table with the
native own-zero table, whose AllNever annotation is always Nash.

The new source statements and degree arguments above are ordinary mathematics;
no new Lean checking is claimed.

The strict-dual landing proof applies to the ORIGINAL selected m source.
An inherited exact-payoff-fibre minimum does not satisfy that hypothesis
merely because it has the same zero set. Local finite-prefix debt floors
and geometric clock tests already provide related landing criteria; this
corollary uses no joining genericity and no test on J once the strict
Gamma dual is supplied. It does not construct a compatible joint return.

## Remaining gap

Finite-amplitude roots with strictly positive output remain allowed at the
restricted source. The macroscopic landing bound and the tautological return
q*X to X do not lower original m, restore a changed positive pivot amplitude,
or supply a renewable joint head/tail variation. The finite crossing is
in the augmented actual carrier retaining(U,B,e,N), not a claim that the
stronger literal chronology fields of a different source atlas are produced.
The m=1/AllNever endpoint and negative-source consumer remain open;
all-zero sources below1 are excluded in the A_Z>0 argument above. No
whole Fin4 branch or the uniform-equilibrium conjecture is claimed closed.
