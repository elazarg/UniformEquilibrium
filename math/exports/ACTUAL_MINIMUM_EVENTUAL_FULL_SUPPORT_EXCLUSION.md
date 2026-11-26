# An open reward region excludes eventual full support in actual minima

## Exact statement

There are four players I={0,1,2,3}. A native quitting table gives finite
real rewards Z_i(S) for every nonempty coalition S, with Z_i({i})=0 and
AllNever payoff0. Each player independently chooses a complete law on
the natural dates and Never. Let U_i be expected terminal payoff, B_i the
supremum over all unilateral replacement laws, e_i the pure Never response,
N_i the ORIGINAL marginal Never mass, d_i=B_i-U_i, and nu=product_i N_i.
ALL-END means B=e. An observer is any player other than a fixed pivot p.

Write Gamma_ij=Z_i({j}), J_ij=Z_i({i,j}) for i!=j, with both diagonals0.
These are24 independent coordinates. Fix a hollow invertible real matrix
Gamma_*, a pivot p with v_*=Gamma_*^-1 e_p>0 coordinatewise, and

    D=diag(D_0,D_1,D_2,D_3), 0<D_i<1/2,
    D_i!=D_j for i!=j, J_*=Gamma_* D.                 (1)

There is delta>0 with the following property. Let every entry of Gamma,J
differ from Gamma_*,J_* by less than delta. All remaining32 native reward
coordinates, namely passive pair rewards and rewards on coalitions of
size3 or4, may be arbitrary fixed finite numbers. For each such complete
table Z there is epsilon(Z)>0 such that, for 0<=r<epsilon(Z), no actual
independent complete-law profile P can satisfy all of these conditions:

- every N_i(P)>0;
- P is ALL-END and every observer has zero debt;
- P minimizes J_r=d_p+r nu over all actual observer-optimal profiles,
  or over a larger feasible carrier containing all of them;
- P has infinitely many nonempty dates, and every sufficiently late
  nonempty date has all four players in its support.

Equivalently, such an actual minimum with infinitely many nonempty dates
must omit at least one player at infinitely many of those dates.
The conclusion permits finite-support laws. It imposes no assumption on
finite pivot cap contacts and no Never-mass equality. It does not assert
that the minimum is attained by an actual law for every table.

Thus the theorem applies on an open neighborhood in all24 singleton and
participant-pair coordinates around EVERY structured pair(1), with the
other32 coordinates unrestricted. Delta may depend on Gamma_*,D,p;
epsilon and local state neighborhoods may depend on the full table.
For any finite collection of eligible pivots one may intersect their
neighborhoods and take the minimum of their positive penalty bounds.

## Conjecture-facing change and strategic inputs

The selected actual-minimum case of the counterexample reduction has positive
original Never, ALL-END, zero observer debts, and minimizes d_p+r nu for
0<r<m, where m>0 is its absorbing observer-constrained minimum. On the
reward region above, choose r<min(m,epsilon(Z)) before source selection. This result eliminates
its entire eventual-full-support case, including exact mass saturation and
arbitrary earlier pivot cap contacts.

The actual minimum remains an input. Actual attainment and the production
of an eventual-full-support source from an arbitrary table are not proved.
If the source has infinitely many proper-support dates, finitely many active
dates, or is nonrealized, it remains outside this exclusion. Those are
explicit residual cases. The theorem is a necessary support restriction
on actual minima, not a new UE reward-table existence theorem.

All comparison profiles and multipliers used below are constructed from
finite parts of the input law. No observer repair, improving controller,
infinite-dimensional multiplier theorem, or center-manifold theorem is
assumed. The final obstruction is an elementary asymptotic integration
argument, with its proof included.

## Complete deviation semantics and root recursions

Before absorption there is one public live history at each date. Sampling
a unilateral player's private randomization in advance identifies its
behavior with a mixture of deterministic deadlines and Never. The supremum
of these pure responses is therefore exactly B. No public lottery,
correlated recommendation, or continuation after an infinite calendar is used.

For a product root q, set H_i=product_(j!=i)(1-q_j), c=product_i(1-q_i).
Let Q_i(q) be the expected reward when i quits at that root, and let P_i(q)
be the contribution of nonempty opponent quitting coalitions when i continues.
Explicitly, if

    pi_i(S;q)=product_(j in S)q_j product_(j notin S,j!=i)(1-q_j),

then Q_i=sum_(S subset I\{i}) pi_i(S;q) Z_i(S union{i}) and
P_i=sum_(nonempty S subset I\{i}) pi_i(S;q) Z_i(S). With literal tail
coordinates, the exact prefix formulas are

    e'_i=P_i+H_i e_i,
    U'_i=q_i Q_i+(1-q_i)P_i+c U_i,
    B'_i=max(Q_i,P_i+H_i B_i), N'_i=(1-q_i)N_i.          (2)

Positive original Never makes every finite head survival positive. ALL-END
therefore passes to every actual conditional tail: a better conditional
response could be used after that cut to improve whole Never. Observer
optimality also passes to those tails, since a better tail law would improve
the original prescribed payoff by positive joint head survival. At a date
where an observer has positive hazard, its Quit offer equals its END cap.

Every actual positive-Never law has conditional remaining finite masses
tending to0. Consequently its late hazards, conditional prescribed payoffs,
Never offers and debts tend to0; conditional joint Never tends to1.
Moreover sum_t q_i(t)<infinity, since product_t(1-q_i(t))=N_i>0.

## Empty dates and late pivot strictness

Deleting all dates with q=0 preserves U,e,N and all retained deadline values.
Every deadline in the compressed calendar corresponds to an old deadline.
Its cap is therefore at most the old cap, and Never still attains the old
cap because the profile is ALL-END. Hence B is preserved too. This gives
an actual observer-optimal profile with the same objective and minimizing
status. If there are infinitely many nonempty dates, their ordered sequence
is again indexed by the natural numbers. We may therefore work with an
eventually full-support actual law without loss for the stated conclusion.

At a late conditional cut put f_i=Pr(T_i is finite in that conditional law),
and F=max_i f_i. The current hazards satisfy 0<=q_i<=f_i. Independence and
bounded rewards give the uniform expansions

    e=Gamma f+O(F^2), Q=Jq+O(F^2).                     (3)

For the first expansion, except on the event that at least two opponents
have finite times, exactly one opponent j quits and contributes Gamma_ij.
The exceptional probability is at most sum_(j<k) f_j f_k. Replacing the
probability of each lone opponent by f_j introduces the same order of
error. The root expansion follows by separating events with at least two
current opponent quitters. These estimates are uniform over all complete
timing laws at the fixed table.

At(1), ||Gamma_*^-1 J_*||_infinity=max_i D_i<1/2. This strict inequality
with upper bound1 persists on an open24-coordinate neighborhood. If all four current Quit offers
were tied with END, (3) would give

    F<=kappa F+C F^2, kappa=||Gamma^-1 J||_infinity<1.

For sufficiently small nonzero F this is impossible. At a full-support date
all observer contacts already hold and F>0. Thus every sufficiently late
pivot comparison is STRICT: Q_p<e_p. Earlier contacts are unrestricted.

## Finite charts and exact multiplier gluing

Keep a window's complete continuation literally fixed. Compute e_i,k and
u_k=U_p,k backwards by(2), and let nu_k be conditional joint Never.
Put G_i,k=Q_i(q_k)-e_i,k. On a four-date window impose the12 observer
contacts G_i,k=0 and fix all four entrance Never offers e_i,0.

At zero hazards and zero tail payoffs, for a signed hazard variation a_k
write f_k=sum_(t>=k)a_t. With both endpoint variations zero, the homogeneous
constraints are

    Gamma f_k-J a_k=g_k e_p, f_0=f_L=0,
    f_(k+1)=A f_k+b g_k,
    A=I-J^-1 Gamma, b=J^-1 e_p.                       (4)

Thus their kernel is isomorphic to the kernel of
R_L=[A^(L-1)b,...,b]. At(1), A=I-D^-1 is diagonal with distinct entries
and b=D^-1 v_* has no zero entries. The determinant of R_4 is a nonzero
Vandermonde determinant times the product of the four entries of b.
This gives an invertible16-by16 four-date constraint Jacobian. For five
dates, rank R_5=4 gives19 independent constraints on20 variables. Both
ranks persist nearby.

For every sufficiently late five-date window, the finite inverse function
theorem supplies a smooth one-dimensional exact fiber. Its original hazards
are strictly between0 and1 and its pivot gaps are strict. A small two-sided
neighborhood of the fiber preserves these conditions. Backward induction
in(2) preserves ALL-END and observer optimality. All entrance caps and
observer entrance prescribed payoffs are fixed, so splicing the window
back preserves every earlier full cap and observer optimality. Earlier
tied pivot deadlines cause no difficulty because the pivot entrance cap
is fixed too. These are actual finite modifications with positive Never.

Up to a constant and a positive joint head-survival factor, the whole
objective on this fiber is F=-u_0+r nu_0. Minimality gives a unique
multiplier representation

    dF+sum_i Y_i de_i,0+sum_(k,i!=p) mu_i,k dG_i,k=0.   (5)

Existence is finite-dimensional constrained stationarity; uniqueness follows
from the independent constraint gradients. The four-date square map gives
a unique representation of ANY gradient of F in the same manner.

Freeze the fifth date in(5). Its first four dates give precisely their
unique four-date multiplier tuple. Freeze the first date instead. Then
F_0=constant+c F_1 and e_i,0=P_i+H_i e_i,1, while
G_i,0=Q_i-e_i,0. After dividing by c, uniqueness of the last four-date tuple
gives

    Y_i(k+1)=(Y_i(k)-Z_i(k))/(1-q_i(k)), Z_p(k)=0,       (6)

where Z_i(k) is the first-date observer-contact multiplier. This glues all
late windows into one exact adjoint sequence. No infinite-dimensional
multiplier existence is invoked.

The four-date gradients and inverse Jacobians depend continuously on the
finite window and its fixed tail values. At zero data their unique values
are Y=e_p+r w and all contact multipliers0, where w^T=1^T Gamma^-1.
Indeed dF=-(Gamma_p+r 1^T)sum_k a_k and de_0=Gamma sum_k a_k.
Consequently the actual glued sequence satisfies

    (e,d_p,nu,Y)->(0,0,1,e_p+r w), Z->0.               (7)

## Analytic adjoint map

Use the ten-dimensional state x=(e_0,e_1,e_2,e_3,d,nu,Y_0,Y_1,Y_2,Y_3),
where d is pivot debt and u=e_p-d. The seven controls are q in R^4 and
Z_i for observers, with Z_p=0. Set

    e_i^+=(e_i-P_i(q))/H_i(q),
    u^+=(e_p-d-q_p Q_p(q)-(1-q_p)P_p(q))/c(q),
    nu^+=nu/c(q), d^+=e_p^+-u^+.

For formal future values define E_i(q,e^+)=P_i(q)+H_i(q)e_i^+ and
U(q,u^+)=q_p Q_p(q)+(1-q_p)P_p(q)+c(q)u^+.
Take partial q derivatives holding these future values fixed, and only
then substitute the preceding formulas. The seven control equations are

    Q_i(q)=e_i                              (i!=p),
    sum_i Y_i partial_j E_i-partial_j U+r nu^+ partial_j c
      +sum_(i!=p) Z_i partial_j(Q_i-E_i)=0    (j in I).  (8)

The next state uses e^+,d^+,nu^+ and Y_i^+=(Y_i-Z_i)/(1-q_i).
An invertible control Jacobian at(7) defines an analytic local map T.
Equations(5)--(6), restricted to the first root, show that the actual
stationarity sequence is an orbit of this map. The exact finite tests below
verify invertibility. In applying the inverse theorem, signed controls are
permitted near0; the actual orbit retains its original positive hazards.

## Exact symplectic identity and fixed manifold

Put z=-u+r nu=d+r nu-e_p. Differentiate the literal recursions. The
q-stationarity in(8) and the differential observer contacts cancel all q
terms, giving

    dz+Y dot de=c(dz^+ +Y^+ dot de^+).                (9)

For clarity, before cancellation the coefficient of dq is
-U_q+r nu^+ c_q+Y E_q. Equation(8) replaces it by
-Z(Q_q-E_q). Differentiating Q_i-E_i=0 gives
(Q_q-E_q)dq=H de^+ on observer rows. This changes Y H de^+ to
(Y-Z)H de^+=c Y^+ de^+, establishing(9) with its stated sign.

Since nu=c nu^+, the one-form alpha=(dz+Y dot de)/nu is preserved by T.
In coordinates (z,e;1/nu,Y/nu), its exterior derivative is the canonical
nondegenerate symplectic form. Thus T is locally invertible and its
derivative at every fixed point is symplectic.

Taking q=Z=0, e_i=0 for observers, gives a smooth three-dimensional
manifold of fixed points. Its parameters are (e_p,d,nu). The four remaining
equations determine Y through a linear system whose matrix at e_p=0 is
Gamma^T, so it is invertible nearby. Explicitly, with h the pivot coordinate
vector and t the scalar e_p,

    [Gamma^T-t(1-h)h^T]Y=Gamma^T h+(r nu-t+d)1.        (10)

The finite certificate gives geometric unit multiplicity3 and algebraic
unit multiplicity4 at the base point, with six other eigenvalues separated
from1. The three fixed tangent vectors persist. A symplectic matrix has
even algebraic multiplicity at eigenvalue1: generalized eigenspaces with
eigenvalues whose product is not1 are symplectically orthogonal, so its
generalized unit eigenspace inherits a nondegenerate alternating form and
has even dimension. Hence the unit multiplicity remains exactly4 along
the nearby fixed manifold.

After quotienting its three fixed directions, the normal derivative has
one simple eigenvalue IDENTICALLY1 and six other simple real eigenvalues.
Their negative signs, separation in absolute value, and separation from
unit modulus persist near the exact example. Exact persistence of the
unit normal eigenvalue is essential to the following dynamical argument.

## General first jet and openness

At r=0, write h=e_p for the pivot coordinate vector. The base state has
Y=h. Linearize(8), writing a=delta q, zeta=delta Z with zeta_p=0,
and eta=delta Y. The observer rows are J_i a-delta e_i=0. The four
stationarity rows are exactly

    Gamma^T eta+(J-Gamma)^T zeta-1 delta d+h delta e_p
      -h(J_p a)+a_p(Gamma_p-J_p)^T=0.                (11)

Every passive-pair coefficient cancels. Indeed

    E_p-U=q_p(P_p-Q_p)+H_p e_p^+-c u^+.

Taking the q derivative with successors fixed and then substituting the
successor formulas shows that its relevant second jet uses only the
linear terms Gamma_p q and J_p q. Higher passive terms cancel, and
higher forced-Quit terms enter with the additional factor q_p. The other
terms are Gamma^T eta and (J-Gamma)^T zeta. The successor first jet is

    delta e^+=delta e-Gamma a, delta d^+=delta d,
    delta nu^+=delta nu+1^T a,
    eta^+=eta-zeta+h a_p.                            (12)

Thus the complete control and state first jets at r=0 depend only on
Gamma,J, with no restriction on the other32 finite rewards.

At a structured pair(1), use invertible state coordinates

    x=Gamma^-1 delta e, z=Gamma^T eta-1 delta d,
    v=Gamma^-1 h, B=-D(I-D)^-1=diag(beta_i).

Observer contacts say D a-x=g v for one scalar g. Equations(11)--(12)
then give

    x^+=B^-1 x-D^-1 v g,
    z^+=B z+h g/(1-D_p),
    a_p=v^T(z^+-z).                                 (13)

For the last identity, multiply eta^+-eta=-zeta+h a_p by h^T and use
zeta_p=0; equivalently v^T Gamma^T=h^T. Solving gives

    g=-[(1-D_p)x_p+D_p(1-D_p) sum_i v_i z_i/(1-D_i)]
                                      /[v_p(1-2D_p)].          (14)

All denominators are nonzero. This uniquely determines g, then a, then
zeta; consequently the seven-control Jacobian is invertible.

Order the variables as (z_observers; x_p,z_p; x_observers; delta d; delta nu).
The linear state map is block triangular. Its observer z block has
entries beta_i=-D_i/(1-D_i), its observer x block has entries beta_i^-1,
and its pivot two-by-two diagonal block is

    (1/(1-2D_p))*[2(1-D_p), v_p; -1/v_p, -2D_p].     (15)

The last block has trace2, determinant1, and is not the identity. Both
delta d and delta nu have diagonal entry1. Thus the exact characteristic
polynomial for every structured pair is

    (lambda-1)^4 product_(i!=p)
                       (lambda-beta_i)(lambda-beta_i^-1).     (16)

The six nonunit eigenvalues are simple and negative, with distinct
absolute values, three below1 and three above1 in modulus. A fixed vector
in(12) has a=0 and zeta=0. Contacts then force x=t v and stationarity
forces z=-t h; delta d and delta nu are free. The unit eigenspace therefore
has dimension3, as required for the fixed-manifold argument above.

Four consecutive zero hazard observations characterize exactly these fixed
vectors. To see this, suppose a_n=0 for n=0,1,2,3 along the linear map.
Then x is constant and x=-g v, so g is constant at those dates. For some
vector c the z recurrence is

    z_i(n)=beta_i^n c_i  (i!=p),
    z_p(n)=g+beta_p^n c_p.

The four equations a_p(n)=v^T(z_(n+1)-z_n)=0 give

    sum_i v_i(beta_i-1) beta_i^n c_i=0, n=0,1,2,3.

Distinct beta_i and nonzero v_i make this Vandermonde system invertible.
Hence c=0, z=g h, and x=-g v: precisely the fixed tangent, with the two
other free coordinates. The four-block observation stack has rank7 and
kernel equal to that tangent. This proves every finite test throughout(1),
not only at one numerical example.

Nonzero minors and these spectral separations persist on an open
neighborhood of Gamma_*,J_* at r=0. The preceding cancellation makes that
neighborhood independent of the other32 rewards. For each complete table,
continuity then gives epsilon(Z)>0 on which the tests persist for small r.
There is no claim of a common penalty bound over unbounded passive-pair
rewards. The persistent normal unit eigenvalue follows from(9)--(10) and
symplectic parity; it cannot drift merely because r or the fixed point moves.
All actual conditional tails eventually enter the required state neighborhood.

## Exact rational boundary certificate

One explicit base pair in(1) is

    Gamma_*=[0,3,-1,-1; 3,0,-1,-1; -1,-1,0,3; -1,-1,3,0],
    D=diag(1/5,1/4,1/3,2/5), J_*=Gamma_* D.           (17)

It has Gamma_*^-1=(1/15)[2,7,3,3;7,2,3,3;3,3,2,7;3,3,7,2],
det Gamma_*=45, det J_*=3/10, and w=(1,1,1,1). Every pivot is eligible.
Set passive pair rewards to (1-J_*ij-J_*ji)/2 and higher rewards to0
only for the exact calculation below. For every pivot det R_4=7/5 and
the16-by16 contact/entrance determinant is5103/10000. At r=0 the control
determinants for pivots0,1,2,3 respectively are

    81/50, 144/125, 81/125, 9/25.

The supplied program directly reconstructs the root polynomials and verifies
these identities, (16), the unit kernel and the observation rank. For pivot0
the stable eigenvalues are -1/3,-1/2,-2/3, with reciprocals -3,-2,-3/2.
In state order (e0,e1,e2,e3,d,nu,Y0,Y1,Y2,Y3), rows(0,1,2,3,4,8,12) and
columns(0,1,2,3,4,6,8) of the four-block observation stack have
determinant28/177147. These rational checks supplement the general algebra.

## Summable observations exclude the actual orbit

The following lemma is proved in the next section. A smooth map with a
smooth fixed manifold, simple real normal eigenvalues consisting of one
persistent unit eigenvalue and negative stable/unstable eigenvalues of
distinct absolute values, and a full-rank finite observation stack, has no
nonconstant convergent orbit with nonnegative summable observations.

Apply it to the map T, its three-dimensional fixed manifold, and the
four-vector q. The glued actual state converges by(7). Its hazards are
nonnegative and summable because all original Never masses are positive.
The raw certificate and symplectic identity supply the lemma's remaining
hypotheses. Hence the orbit is eventually the zero-tail fixed point and
its hazards eventually vanish. This contradicts eventual full support.
The preceding compression and strictness arguments prove the exact statement.

## Standalone dynamical statement

Let T be a C^3 local map of a finite-dimensional real space fixing0.
Suppose a C^3 manifold F of fixed points passes through0, and use local
coordinates (a,b) in R^d times R^m with F={b=0}. Thus

    T(a,0)=(a,0),
    a_next=a+H(a)b+O(|b|^2),
    b_next=L(a)b+O(|b|^2).                           (1)

Assume that near a=0 the real matrix L(a) has m simple, nonzero real
eigenvalues, with distinct absolute values. One is identically1. Every
other eigenvalue is negative and has absolute value different from1.
Order their absolute values once and for all; the order and all gaps
persist on a smaller neighborhood.

Let q be a C^2 map to R^s with q(a,0)=0. Assume its derivative normal to F,
C=D_b q(0,0), is nonzero on every eigenvector of L(0). Equivalently, the
finite observation stack

    C, C L(0), ..., C L(0)^(m-1)                     (2)

has column rank m. For the equivalence, apply a Vandermonde matrix to the
distinct eigenvalues and use the nonzero vector observation on each
one-dimensional eigenspace.

Then any orbit x_n=T^n(x_0) tending to0 with q(x_n) coordinatewise
nonnegative and sum_n sum_j q_j(x_n)<infinity is eventually the fixed
point0. In particular no such orbit has a positive observed coordinate
at every sufficiently late date.

The assumptions concern the derivative on the normal quotient to the
fixed manifold, not a diagonalization of the full derivative. The full
derivative may have a Jordan block joining the normal unit eigenvector
to a tangent fixed direction.

## Summable observations control distance from the fixed manifold

For a fixed finite number of iterates all maps are defined on a sufficiently
small neighborhood. Consider

    G(x)=(q(x),q(Tx),...,q(T^(m-1)x)).

It vanishes identically on F. Since D_a q(a,0)=0, the normal derivative
of this stack at0 is exactly (2). Choose m scalar components of G giving
a nonsingular normal derivative. Denote that submap by G_0. Uniformly
near0, G_0(a,b)=K b+o(|b|), where K=D_b G_0(0,0) is invertible: subtract
G_0(a,0)=0 and integrate its b derivative along the segment. Consequently

    |b| <= C_0 sum_(j=0)^(m-1) |q(T^j(a,b))|.          (3)

Along the assumed orbit, nonnegativity makes the observation norm
summable. Equation(3) implies sum_n |b_n|<infinity. Equation(1) also gives
sum_n |a_(n+1)-a_n|<infinity.

## Reduction to a summably perturbed diagonal recurrence

Simple separated real eigenvalues permit a C^1 real eigenbasis P(a) on
a small neighborhood, with

    P(a)^(-1)L(a)P(a)=D(a)=diag(d_1(a),...,d_m(a)).

Its matrices and first derivatives are bounded. Taylor's theorem writes
the nonlinear remainder in (1) as E_n b_n with |E_n|<=C|b_n|, using an
integrated derivative along the b segment. Put y_n=P(a_n)^(-1)b_n.
Then

    y_(n+1)=(D_n+R_n)y_n,
    D_n=D(a_n), sum_n |R_n|<infinity.                (4)

Indeed the basis change P(a_(n+1))^(-1)P(a_n)-I is O(|a_(n+1)-a_n|),
and the nonlinear term is O(|b_n|). These are summable by(3). Each diagonal
entry tends to its nonzero value at0; one entry is identically1, the
others remain negative and uniformly separated in absolute value.

## Elementary asymptotic integration lemma

For completeness, any recurrence(4) with the stated uniform absolute-value
separation and summable R has a basis of solutions

    y_n^(i)=phi_i(n)[e_i+o(1)],
    phi_i(n)=product_(k=N)^(n-1) d_i(a_k).            (5)

Here N may be increased. To prove this, substitute y_n=phi_i(n)(e_i+z_n).
Writing B_n=D_n/d_i(a_n), E_n=R_n/d_i(a_n), one obtains

    z_(n+1)=B_n z_n+E_n(e_i+z_n).                   (6)

The sequence E is summable, and B is diagonal. Its i-th diagonal entry
is1; entries of smaller absolute order have absolute value <=rho<1,
and those of larger order have inverse absolute value <=rho<1.

Define a linear solution operator for w_(n+1)=B_n w_n+f_n coordinatewise.
For coordinates of smaller order use the forward sum from N with w_N=0.
For coordinates of larger order use the backward sum from infinity, with
the inverse products of the corresponding B entries. For coordinate i
use w_n=-sum_(k=n)^infinity f_i,k. Each operator maps summable f to a
sequence tending to0, and its supremum norm is bounded by C sum|f_k|,
with C uniform in N. The backward kernel includes the inverse factor at
its first step; all these factors are uniformly bounded.

Apply that operator to f_n=E_n(e_i+z_n). On the Banach space of sequences
z_n tending to0, its Lipschitz constant is at most C sum_(n>=N)|E_n|.
Taking N sufficiently large makes it a contraction. This constructs the
solution z_n->0 of(6). It also makes every z_N arbitrarily small. The
m resulting initial vectors e_i+z_N^(i) are therefore independent,
so (5) is a basis of all solutions. This proof requires no center-manifold
theorem or unproved asymptotic linearization assertion.

## Excluding every nonzero orbit

Expand the actual y solution in the basis(5). If it is nonzero, let i be
the largest absolute-order mode with nonzero coefficient. The uniform
ratio gaps make every smaller phi_j/phi_i tend to0 exponentially. Hence

    y_n=c phi_i(n)[e_i+o(1)], c!=0.                 (7)

A mode with limiting modulus greater than1 grows; the unit mode has
phi_i(n)=1. Since y_n->0, neither can be this leading mode. Thus it is
a stable mode, and every factor d_i(a_k) is negative. The sign of
phi_i(n) alternates with n.

Since q(a,0)=0, q(a,b)=D_b q(a,0)b+O(|b|^2). Equations(7) and a_n->0
give

    q(x_n)=c phi_i(n)[C P(0)e_i+o(1)].              (8)

The vector C P(0)e_i is nonzero by observability. Some observed coordinate
therefore alternates sign for all sufficiently large n, contradicting
nonnegativity. Thus y, hence b, is zero on the considered tail. That tail
lies in F and is fixed; because it tends to0, it is the fixed point0.

## Boundary tests and comparison with existing restrictions

The support geometry excluded for minima is realizable by actual laws on
EVERY structured pair(1). Fix 0<rho<1 and set

    a=[I-(1-rho)D]^-1 v>0, E=Gamma a/(1-rho).

Then Gamma sum_(k=0)^3 rho^k a=(1-rho^4)E and

    J(rho^k a)-rho^k E=-rho^k e_p/(1-rho).

Prescribe entrance offers tE and terminal offers rho^4 tE for a four-date
block. The four-date inverse theorem already proved gives an exact smooth
block q_k(t)=t rho^k a+O(t^2) satisfying all12 observer contacts and
all four entrance equations. For small t>0 every hazard is positive and
the pivot's four gaps are strict by the displayed first-order formula.
No actual continuation is assumed at this construction stage.

Concatenate these blocks at amplitudes t_0 rho^(4n), n>=0, with t_0>0
sufficiently small. Hazards are proper and summable, hence every original
Never mass is positive. Assigned boundary offers match exactly and tend
to zero. Telescoping the exact Never recursion identifies them with the
actual infinite law's Never responses: the remaining bounded reward error
vanishes with the conditional probability of a future finite stop.
The strict pivot inequalities and observer contacts give B=e at every
cut against all finite deadlines and Never. Every observer law is a mixture
of these tied responses, so its debt is zero. This produces genuine actual
full-support profiles, not minima. The theorem proves they cannot be the
selected global minimum for the stated small penalties. No positive absorbing
gap or minimizing property is claimed for this boundary construction.

Exact persistence of the unit normal eigenvalue cannot be replaced by a
test only at the limiting point. Consider

    T(a,b)=(a-b, b(1-2a+b)), F={b=0}, q(a,b)=b.

Starting from b_0=a_0^2 with 0<a_0<1 gives a_(n+1)=a_n-a_n^2,
b_(n+1)=a_(n+1)^2, and sum b_n=a_0. This is a nonzero convergent orbit
with positive summable observation. Its normal eigenvalue is1-2a, which
equals1 at the limit but not along the fixed manifold. The exact
symplectic identity prevents this obstruction in the present theorem.

Nonnegative observations and full observation rank also have genuine roles.
A scalar negative contraction has summable alternating nonzero observations;
an unobserved stable direction can decay while every observed coordinate
vanishes. These do not satisfy the lemma's respective hypotheses.

The new exclusion does not rest on a negative quadratic-energy direction.
Throughout the structured locus(1), put v=Gamma_*^-1 e_p. An earlier sufficient fixed-cap curvature
test requires a symmetric W with Wv=e_p and

    Q(W)=[W Gamma^-1 J+J^T Gamma^-T W-W]/2>0.

For EVERY such W on that locus,

    v^T Q(W)v=(D_pp-1/2)v_p<0.

At the rational example(17), the four values are -1/25,-1/30,-1/45,-1/75. This contradicts the entire
existential positive-energy test, not only one attempted W. In general
the same directional value is (Gamma^-1 Jv)_p-v_p/2, so failure persists
on an open neighborhood. The new exclusion can therefore be taken on a
region where that older sufficient curvature certificate is impossible.

The mass-saturation alternative alone allowed a contact-free actual minimum
with N_p=1/(1+r sum v). The present proof rules out eventual full support
on its stated raw region without using that equality or excluding earlier
contacts. This is a strict additional restriction on the actual source
case. The raw examples are not claimed to lie outside every UE existence
theorem, and no positive-gap example is exhibited.

Sparse infinitely active calendars and finite active calendars remain
outside the conclusion. The proof uses exact observer contacts at every
late date; it cannot apply them to an inactive observer merely by adding
an arbitrarily small hazard. Empty-date deletion removes only dates where
all hazards are zero, using the exact ALL-END cap comparison proved above.
No density percentage or bound on the remaining support changes is claimed.

## Source correspondence and downstream use

The complete-law payoff and unrestricted response cap are
`quittingStoppingLawExpectedPayoff` and
`quittingStoppingLawReplacementPayoffCap` in
[StoppingLawOperationalDistance.lean](../../UniformEquilibrium/Quitting/Paths/StoppingLawOperationalDistance.lean).
The declarations
`quittingStoppingLawExpectedPayoff_behaviorStoppingLaws_eq_terminalPayoff`
and
`quittingStoppingLawCap_behaviorStoppingLaws_eq_continuationBestResponseValue`
identify them with arbitrary behavioral payoff and cap. Conversely,
`quittingTerminalPayoff_stoppingLawProfile_eq_expectedPayoff` and
`quittingStoppingLawCap_eq_continuationBestResponseValue_stoppingLawProfile`
give these identities for independent conditional-hazard implementations.
The proof therefore tests every unilateral behavioral deviation.

The exact root identities are
`quittingTerminalSemanticPair_rootThenContinuation` in
[TerminalSemanticPair.lean](../../UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean)
and `quittingContinuationBestResponseValue_rootThenContinuation_eq_max` in
[TerminalDebtPrefix.lean](../../UniformEquilibrium/Quitting/Root/TerminalDebtPrefix.lean).
They give the payoff and full-cap meanings of(2). The new steps are finite
multiplier gluing, the preserved form, and the actual-tail asymptotic exclusion.

The declaration
`not_exists_uniformEquilibriumPayoff_iff_hasPositiveMinimumTerminalSemanticDebt`
in [PositiveMinimumSemanticDebt.lean](../../UniformEquilibrium/Quitting/Terminal/PositiveMinimumSemanticDebt.lean)
concerns total debt on a compact semantic carrier. It supplies neither an
actual observer-constrained J_r minimum nor the eventual-support condition
of this theorem. Those inputs remain explicit. A compact point cannot be
substituted for the actual law in the summability and conditional-tail steps.

The downstream use is a case exclusion. At a table in this open region,
first choose 0<r<min(m,epsilon(Z)), then perform source selection afresh.
If the selected source is actual and has infinitely many nonempty dates,
its support must be a proper subset at infinitely many of those dates.
Otherwise the preceding proof constructs a contradiction entirely within
that source's allowed comparison class. Every finite comparison, inverse
chart and multiplier is produced. No additional successful strategy witness
is assumed. A nonrealized source arm is not affected.

## Lean handoff and scope

Use existing stopping-law and literal-prefix semantics. Formalize the
finite contact/entrance maps and their rank conditions first. Prove the
four/five-window multiplier uniqueness and restriction identities before
introducing an infinite adjoint sequence. The sequence is a consequence of
those finite results, not a structure field assuming stationarity.

The analytic map requires a finite inverse function theorem. Its preserved
one-form and nondegenerate exterior derivative give the finite symplectic
parity argument. The dynamical lemma needs only normal coordinates, smooth
simple real eigenspaces, elementary summable sequence estimates, and the
explicit contraction proof above; no center-manifold machinery is required.
Keep the finite rational certificate separate from the actual-game adapter.

This is ordinary mathematics awaiting formalization. No new Lean build,
source-realization theorem, raw UE existence class, or solution of Fin4 is
asserted. Conditional actual-source coverage is the complete claimed result.

## Complete exact finite calculation

The following Python program uses SymPy exact integers and rational numbers.
It reconstructs the root polynomials at(17), with the displayed test rewards,
and checks every pivot at r=0. No numerical eigenvalue approximation, stored
matrix payload, or external conference input is used. Save the block as a
Python file and run it in an environment with SymPy installed.


```python
"""Exact all-pivot finite certificate at penalty r=0 (SymPy only).

Only singleton and pair rewards enter the zero-tail first jet of the KKT
map. Higher rewards enter root payoff terms of degree >=3, or second
Quit derivatives multiplied by the zero base contact multipliers. Setting
those higher rewards to zero therefore does not restrict this certificate.
"""
from itertools import combinations
import sympy as s

G = s.Matrix([[0, 3, -1, -1], [3, 0, -1, -1],
              [-1, -1, 0, 3], [-1, -1, 3, 0]])
D = s.diag(s.Rational(1, 5), s.Rational(1, 4),
           s.Rational(1, 3), s.Rational(2, 5))
J = G * D
assert G.det() == 45 and J.det() == s.Rational(3, 10)
assert G.inv().T * s.ones(4, 1) == s.ones(4, 1)
assert max(sum(abs(a) for a in D.row(i)) for i in range(4)) < 1

q, e, Y = [s.symbols(f'{name}0:4') for name in ('q', 'e', 'Y')]
d, nu = s.symbols('d nu')
eplus = s.symbols('ep0:4')
uplus = s.symbols('up')
reward = {}
for i in range(4):
    for size in range(1, 5):
        for coal in combinations(range(4), size):
            if size == 1:
                value = G[i, coal[0]]
            elif size == 2:
                a, b = coal
                value = (J[i, b if i == a else a] if i in coal
                         else (1 - J[a, b] - J[b, a]) / 2)
            else:
                value = s.Integer(0)
            reward[i, coal] = value
for a, b in combinations(range(4), 2):
    assert sum(reward[i, (a, b)] for i in range(4)) == 1

H, P, Q = [], [], []
for i in range(4):
    others = [j for j in range(4) if j != i]
    H.append(s.prod(1 - q[j] for j in others))
    passive = quit = s.Integer(0)
    for size in range(4):
        for coal in combinations(others, size):
            probability = s.prod(q[j] if j in coal else 1 - q[j] for j in others)
            if coal:
                passive += probability * reward[i, coal]
            quit += probability * reward[i, tuple(sorted((*coal, i))) ]
    P.append(s.expand(passive))
    Q.append(s.expand(quit))
c = s.prod(1 - rate for rate in q)
E = [P[i] + H[i] * eplus[i] for i in range(4)]
lam = s.symbols('lambda')
control_determinants = [s.Rational(81, 50), s.Rational(144, 125),
                        s.Rational(81, 125), s.Rational(9, 25)]

for pivot in range(4):
    observers = [i for i in range(4) if i != pivot]
    v = G.inv()[:, pivot]
    assert all(entry > 0 for entry in v)
    Acontrol = s.eye(4) - J.inv() * G
    bcontrol = J.inv()[:, pivot]
    R = s.Matrix.hstack(*[Acontrol**k * bcontrol for k in range(4)])
    assert R.det() == s.Rational(7, 5)
    columns = [(k, j) for k in range(4) for j in range(4)]
    rows = [[G[i, j] for k, j in columns] for i in range(4)]
    rows += [[(J[i, j] if t == k else 0) - (G[i, j] if t >= k else 0)
              for t, j in columns] for k in range(4) for i in observers]
    assert s.Matrix(rows).det() == s.Rational(5103, 10000)

    zs = s.symbols('z0:3')
    Z = [s.Integer(0)] * 4
    for i, z in zip(observers, zs):
        Z[i] = z
    U = q[pivot] * Q[pivot] + (1 - q[pivot]) * P[pivot] + c * uplus
    future = {eplus[i]: (e[i] - P[i]) / H[i] for i in range(4)}
    future[uplus] = (e[pivot] - d - q[pivot] * Q[pivot]
                     - (1 - q[pivot]) * P[pivot]) / c
    stationarity = []
    for j in range(4):
        equation = sum(Y[i] * s.diff(E[i], q[j]) for i in range(4))
        equation -= s.diff(U, q[j])  # r=0; no r*nuplus*partial(c) term.
        equation += sum(Z[i] * s.diff(Q[i] - E[i], q[j]) for i in observers)
        stationarity.append(equation.subs(future))
    equations = s.Matrix([Q[i] - e[i] for i in observers] + stationarity)
    state = list(e) + [d, nu] + list(Y)
    control = list(q) + list(zs)
    base = dict.fromkeys(list(e) + [d] + control, s.Integer(0))
    base.update({nu: 1, **{Y[i]: int(i == pivot) for i in range(4)}})
    assert equations.subs(base) == s.zeros(7, 1)
    M = equations.jacobian(control).subs(base)
    assert M.det() == control_determinants[pivot]
    policy = -M.inv() * equations.jacobian(state).subs(base)
    next_state = s.Matrix([future[eplus[i]] for i in range(4)] +
                          [future[eplus[pivot]] - future[uplus], nu / c] +
                          [(Y[i] - Z[i]) / (1 - q[i]) for i in range(4)])
    A = (next_state.jacobian(state).subs(base)
         + next_state.jacobian(control).subs(base) * policy)
    expected = (lam - 1)**4
    for i in observers:
        beta = -D[i, i] / (1 - D[i, i])
        expected *= (lam - beta) * (lam - 1 / beta)
    assert s.expand(A.charpoly(lam).as_expr() - expected) == 0
    fixed = s.Matrix.hstack(*(A - s.eye(10)).nullspace())
    assert fixed.shape == (10, 3)
    C = policy[:4, :]
    O = s.Matrix.vstack(*[C * A**k for k in range(4)])
    assert O.rank() == 7 and O * fixed == s.zeros(16, 3)
    if pivot == 0:
        assert O.extract([0, 1, 2, 3, 4, 8, 12], [0, 1, 2, 3, 4, 6, 8]).det() == s.Rational(28, 177147)
    for i in observers:
        beta = -D[i, i] / (1 - D[i, i])
        mode = (A - beta * s.eye(10)).nullspace()[0]
        observed = C * mode
        assert observed[pivot] != 0
        observed /= observed[pivot]
        predicted = (s.eye(4) - (1 - beta) * D).inv() * v
        predicted /= predicted[pivot]
        assert observed == predicted and all(a > 0 for a in observed)
    print(f'pivot {pivot}: all exact checks passed; control determinant {M.det()}')
```
