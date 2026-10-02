# Guarded row-swap degree escape in quitting games

## Result and status

This note proves a raw-reward sufficient criterion inside the four-player
R0, degree-+1 singleton-matrix class. It does not require equality of any
stationary-response rows. Strict inverse positivity gives an exact stationary
terminal Nash equilibrium, with every opponent-deleted clock contracting,
for arbitrary signed singleton levels. A weak-inverse boundary gives a
uniform-equilibrium payoff by literal reward approximation.

The mechanism is to interchange two residual coordinates in a clipped
fixed-point map. Finite reward inequalities prove that every nonzero fixed
point of the altered map still satisfies all individual incentives in the
ORIGINAL game. The matrix used to calculate its local degree is consequently
a ROW-permuted singleton matrix, not a quotient or a new quitting game.

This is ordinary mathematics, not a Lean-checked theorem. The accompanying
`CHECK_GUARDED_ROW_SWAP.py` checks the rational fixture, matrix identities,
strict reward guards, exact full caps, and exclusion certificates using exact
arithmetic. It does not check the general topological argument.

## 1. Model and exact stationary quantities

Let I be finite with n >= 3. Every nonempty coalition S has reward r(S) in
R^I. The live state and Never have payoff zero. All randomization is private
and independent. A complete behavior strategy is equivalently a private law
on N union {Never}; a deviation replaces that entire law.

Write s_i = r_i({i}) and Gamma_ij = r_i({j}) - s_i. Rows are recipients and
columns are quitters. Thus Gamma_ii = 0.

For stationary hazards q in [0,1]^I define

    alpha_i(q) = product_{j != i}(1-q_j),
    pi_i(T;q) = product_{j in T}q_j product_{j not in T, j != i}(1-q_j),
    Q_i(q) = sum_{T subset I\{i}} pi_i(T;q) r_i(T union {i}),
    H_i(q) = sum_{nonempty T subset I\{i}} pi_i(T;q) r_i(T),
    Delta_i(q) = (1-alpha_i(q))Q_i(q) - H_i(q).

Delta_i is a polynomial independent of q_i. Its ambient expansion at zero is

    Delta(q) = -Gamma q + O(||q||^2).                    (1)

Indeed Q_i = s_i + O(||q||), 1-alpha_i = sum_{j != i}q_j + O(||q||^2),
and H_i = sum_{j != i}q_j r_i({j}) + O(||q||^2).

Put C(q) = product_i(1-q_i), a(q) = 1-C(q), and
R_i(q) = q_i Q_i(q) + (1-q_i)H_i(q). For q != 0 the actual terminal payoff
of repeating q is

    v_i(q) = R_i(q)/a(q).                              (2)

The positive denominator follows from q != 0. Direct algebra gives

    a(q)[Q_i(q)-H_i(q)-alpha_i(q)v_i(q)] = Delta_i(q).   (3)

Thus stationary one-stage Nash against the actual payoff v is precisely

    q_i=0       => Delta_i(q)<=0,
    0<q_i<1     => Delta_i(q)=0,
    q_i=1       => Delta_i(q)>=0.                       (4)

These are not yet complete behavioral conditions for a negative sole
quitter. The producer below excludes every sole-quitter output.

## 2. Endpoint guards and a general degree theorem

Choose distinct players a,b, and let J = I\{a,b}, which is nonempty. Write
z = q_J. Because Delta_a is independent of q_a, its remaining variables are
q_b and z; likewise Delta_b has variables q_a and z.

Assume Gamma_ab>0 and Gamma_ba>0, and the following endpoint guards:

    Delta_a(q_b=0,z)>0 and Delta_b(q_a=0,z)>0
        for every nonzero z in [0,1]^J;                  (G0)

    Delta_a(q_b=1,z)<0 and Delta_b(q_a=1,z)<0
        for every z in [0,1]^J.                         (G1)

Let P exchange rows a and b and fix all other rows, and put A = P Gamma.
For a real square matrix A, let

    f_{A,c}(x) = min(x, A x+c)

coordinatewise on the whole ambient space. Its zeros are LCP(A,c). A is R0
when f_{A,0} has no nonzero zero. For R0 A, kappa(A) is its integer LCP
degree, using this min-map convention.

**Theorem 1.** Under the positive reciprocal comparisons and (G0)-(G1), if
A is R0 and kappa(A) != +1, the original game has an exact stationary
terminal Nash equilibrium. The produced hazards satisfy

    0<q_a<1,  0<q_b<1,  q_J != 0.                       (5)

In particular at least three players have positive hazards. Every
opponent-deleted clock contracts, and this same profile delivers one fixed
uniform-equilibrium payoff for arbitrary signed rewards.

The entire set of nonzero fixed points of the modified map below has total
degree 1-kappa(A). This is not an assertion about the number of equilibria
or about the index of an equilibrium under the usual, unswapped map.

### 2.1 Why the row swap is strategically sound

Extend Delta polynomially to R^I and define

    T(q) = clip_[0,1]^I(q + P Delta(q)),
    Z(q) = q - T(q).                                    (6)

Every fixed point belongs to the strategy cube. The a-coordinate uses
Delta_b, and the b-coordinate uses Delta_a. This map is a mathematical
construction, not a relabeling of utilities or permission for joint deviations.

Suppose q is fixed and z != 0. If q_a=0, (G0) makes the a-coordinate of T
strictly positive. If q_a=1, (G1) makes it strictly less than one. Hence
0<q_a<1, and the same argument gives 0<q_b<1. The fixed-point equations
therefore force BOTH Delta_a(q)=0 and Delta_b(q)=0. Every other coordinate
uses its own residual and satisfies (4). All original players' conditions
are consequently satisfied.

There is no nonzero fixed point with z=0. For example, putting u=q_a,

    Delta_b(u,0)
      = u[(1-u)(s_b-r_b({a}))
                  + u(r_b({a,b})-r_b({a}))].            (7)

The two bracket endpoints are strictly negative: the first by Gamma_ba>0,
the second by (G1) at z=0. Thus Delta_b(u,0)<0 for every u>0, incompatible
with a fixed positive a-coordinate of T. Hence q_a=0, and similarly q_b=0.
This proves that every nonzero fixed point satisfies (5) and all of (4).

### 2.2 Global degree and the all-Continue index

On Omega=(-1,2)^I the image of T lies in [0,1]^I, strictly inside Omega.
Homotoping T to the constant cube center introduces no boundary fixed point.
Therefore

    deg(Z,Omega,0)=+1.                                  (8)

This expanded domain retains fixed points on all strategy faces.

Near zero, the upper clip is inactive, although the lower clip is not. By (1),

    Z(q)=min(q,-P Delta(q))
        =min(q,Aq+O(||q||^2)).                           (9)

R0 and positive homogeneity give

    c_A = min_{||x||_infinity=1} ||min(x,Ax)||_infinity >0,
    ||min(x,Ax)||_infinity >= c_A ||x||_infinity.

Coordinatewise minimum is 1-Lipschitz in its second argument. Thus the
O(||q||^2) perturbation in (9) is smaller than this nonzero linear boundary
margin on a sufficiently small cube. The straight homotopy is boundary-zero
free. Zero is isolated and its local degree under Z is kappa(A).

Excision and additivity now give degree 1-kappa(A) on the complement of a
small closed cube about zero inside Omega. This is nonzero, so a nonzero
fixed point exists. Section 2.1 proves its original-game incentive conditions.
No nonzero root was supplied or selected in advance.

The classical ingredients are homotopy invariance, normalization, excision,
additivity, nonzero-degree existence, and the min-map convention. See Gowda,
*Applications of Degree Theory to Linear Complementarity Problems*,
Mathematics of Operations Research 18(4), 1993, 868-879, Section 2,
DOI 10.1287/moor.18.4.868. The guarded game-specific map and its semantic
justification are proved here, not attributed to that paper.

## 3. Thirty-two strict raw inequalities and positive determinant

There is an elementary finite reward test for the guards. For i=a,b, let j
be its partner. Require

    min_{B subset J} r_i({i} union B)
        > max_{nonempty B subset J} r_i(B),              (L)

    r_i({i,j} union B) < r_i({j} union B)
        for every B subset J.                          (U)

These compare only literal nonempty-coalition rewards. They do not translate
the game, change Never, or invoke a strategic cap. In Fin4, (L) is twelve
strict linear comparisons per owner and (U) is four, for thirty-two total.

When the partner is absent, let ell_i be the left minimum in (L) and h_i
the right maximum. Then

    Q_i>=ell_i,   H_i<=(1-alpha_i)h_i,
    Delta_i >= (1-alpha_i)(ell_i-h_i)>0

as soon as z != 0. When the partner is sure, alpha_i=0 and Delta_i is an
average of the strictly negative differences in (U). This proves (G0)-(G1).

**Theorem 2, strict-inverse raw class.** Suppose

    det Gamma>0,           Gamma^{-1}>0 entrywise,       (10)

and (L)-(U) hold for some pair. Then the game has the exact stationary and
uniform conclusions of Theorem 1, with at least three positive hazards.
Every table in this class has full Gamma R0 and kappa(Gamma)=+1.

To prove the reciprocal comparisons, (L) with B empty on its left gives
Gamma_i,k<0 for every k in J. If Gamma_i,j<=0 as well, the whole i-th row
of Gamma would be nonpositive. It could not have scalar product one with
the nonnegative i-th column of Gamma^{-1}. Thus Gamma_ab,Gamma_ba>0.

For A=P Gamma, its inverse is Gamma^{-1}P>0 and det A=-det Gamma<0.
Any homogeneous complementary pair x>=0,w=Ax>=0 with x!=0 would have
w!=0 and x=A^{-1}w>0. Complementarity would force w=0, a contradiction.
Therefore A is R0.

For completeness, strict inverse positivity computes its degree exactly.
Every solution of LCP(A,-1) satisfies

    x=A^{-1}(1+w)>0,

so w=0 and x=A^{-1}1 is the unique solution. Near that point the min-map
selects Ax-1 in every coordinate. Its local index is sign(det A)=-1.
For R0 matrices this degree is independent of the right-hand side: solutions
for bounded right-hand sides are uniformly bounded, since an unbounded
sequence normalized by its norm would give a nonzero homogeneous solution.
Homotopy in the right-hand side therefore gives

    kappa(A)=-1.                                       (11)

The same argument applied to Gamma gives kappa(Gamma)=+1. Theorem 1 applies,
and the nonzero fixed-point set of (6) has total degree +2.

This is not application of an old quitting theorem to A as a new singleton
matrix. A generally has nonzero diagonal and is not the singleton matrix of
a smaller or transformed quitting game. Its role is solely the local
linearization of the original game's guarded map.

## 4. Full behavioral caps, fixed target, and finite laws

Let q be the produced root and v its value (2). At least three coordinates
of q are positive, so alpha_i<1 for every player. Equation (4), together
with the stationary recursion, gives

    Q_i<=v_i,             H_i+alpha_i v_i<=v_i.          (12)

Against these stationary opponents, a pure quit at date t has payoff

    H_i(1-alpha_i^t)/(1-alpha_i) + alpha_i^t Q_i,

and Never has payoff H_i/(1-alpha_i). Every complete behavioral response
is a mixture of these pure-clock laws. Hence its full response cap is

    B_i=max(Q_i,H_i/(1-alpha_i))<=v_i.

Prescribed play attains v_i, proving B_i=v_i. Negative singleton rewards
cause no unpriced Never branch, because opponents absorb almost surely.

Fix M>0 bounding all absolute terminal rewards. The first opponent quit
L_i is geometric, with E[L_i+1]=1/(1-alpha_i). Under any unilateral response
the actual absorption date is at most L_i. Since absorption at date t has
H-stage weight max(H-t-1,0)/H,

    |average payoff - terminal payoff|
        <= M/[H(1-alpha_i)]                             (13)

uniformly over every complete i-response. Prescribed averages converge to v,
and horizon-H regret is at most 2M/[H(1-alpha_i)]. The same q works for all
accuracies after increasing H. The target is chosen once, before accuracy.

There is also a finite-law implementation. Keep N>=1 stationary rows and
independently move all later private clock mass to Never. Write p^N for the
result, C=product_i(1-q_i), and rho=max_i alpha_i<1. Renewal gives

    U_i(p^N)=(1-C^N)v_i.

Under any i-response, the original and censored outcomes differ only if all
of i's opponents survive N rows, of probability alpha_i^N. Coupling and
bounded rewards give

    B_i(p^N)<=v_i+2M alpha_i^N,
    E(p^N)<=3M rho^N,
    ||U(p^N)-v||_infinity<=M rho^N.                     (14)

This includes all after-support dates and Never, not merely deviations on
the retained menu. For a fixed selected root, the required number of rows
is O(log(1/epsilon)); rho=0 needs only one row.

For finite p^N and arbitrary singleton signs, the complete finite-horizon
bounds are

    horizon-H regret <= 3M rho^N + 2M(N+1)/H,
    delivery error   <= M rho^N + M(N+1)/H.             (15)

For a late response with s_i>=0, truncating the average cannot increase
its solo contribution above its terminal value. With s_i<0, compare that
late response instead with Never; it deletes the nonpositive solo
contribution without changing earlier opponent absorption. This gives the
one-sided complete-cap comparison in (15). Choosing N first, then H,
produces literal finite independent laws delivering the same target.

For rational rewards the stationary root conditions, including (5), form a
nonempty finite semialgebraic system. In Fin4 there are only nine choices
for the two outside coordinates' zero/mixed/one statuses; the two guarded
coordinates are mixed. Real-algebraic elimination can select an algebraic
root. This is an in-principle finite procedure, not a practical complexity
bound. No actual root oracle is assumed in the theorem.

## 5. Weak inverse boundary

**Corollary.** For n>=3, Theorem 2's uniform-payoff conclusion remains valid
with Gamma^{-1}>=0, keeping det Gamma>0 and the strict raw guards. This
corollary does not assert exact stationary attainment at the boundary.

Here is the approximation lemma needed. Let B=Gamma^{-1}>=0 and K=J_n-I_n.
For small e>0,

    Gamma_e=Gamma-eK,
    Gamma_e^{-1}=B+eBKB+e^2 BKBKB+... .                 (16)

The Neumann series converges when e||BK||<1; every coefficient is nonnegative.
If B_ij and (BKB)_ij both vanish, the nonempty supports of row i and column
j of B must be the same singleton {k}, since

    (BKB)_ij=sum_{u!=v}B_iu B_vj.

There is a positive entry B_uv with u,v!=k. Otherwise the n-1>=2 rows
outside k would all be supported only in column k, contradicting invertibility.
Consequently B_ik K_ku B_uv K_vk B_kj>0, so the second-order term is positive.
Thus Gamma_e^{-1}>0. The diagonal is unchanged and det Gamma_e remains positive.

Implement this by decreasing each off-own-singleton reward r_i({j}), i!=j,
by e, leaving all own singletons and nonsingletons unchanged. The literal
tables converge to r. The finitely many strict guards persist. Apply
Theorem 2 afresh to each nearby table, obtaining actual exact terminal Nash
profiles p_e. Uniform reward distance e changes every fixed prescribed or
deviated payoff by at most e, hence

    E_r(p_e)<=2e.

Thus the original game has arbitrarily small complete terminal regret.
Select a convergent subsequence of its bounded prescribed payoff vectors,
with limit v. Each selected p_e still has contracting opponent clocks in
the original game, because transitions and laws were not changed. For a
requested accuracy, choose one sufficiently late p_e with small original
regret and payoff distance to v, then apply (13), with the ORIGINAL reward
bound, to choose one horizon threshold for every larger horizon. This gives
a fixed original UE payoff directly, and also fits the existing terminal
all-errors consumer. No limiting strategy or cap-continuity assertion is made.

The matrix approximation in (16) is the same elementary inverse-positivity
lemma proved in the supplied inverse-positive and three-player-row-extension
notes. Its use here is on the new guarded positive-determinant class.

## 6. A full rational table beyond the compared entrances

Use the following table. Coalition strings denote sets; recipients are columns.

| S | r_0 | r_1 | r_2 | r_3 |
|---|---:|---:|---:|---:|
| 0 | 1 | 4 | 0 | 0 |
| 1 | 4 | 1 | 0 | 0 |
| 2 | 0 | 0 | 1 | 4 |
| 3 | 0 | 0 | 4 | 1 |
| 01 | -3 | -3 | 4 | 2 |
| 02 | 1 | 4 | 4 | -1 |
| 03 | 3 | -1 | 2 | -1 |
| 12 | -3 | 3 | -3 | 3 |
| 13 | -2 | 3 | -2 | 1 |
| 23 | 0 | -2 | 1 | 1 |
| 012 | -4 | 3 | -3 | -2 |
| 013 | -3 | -3 | -4 | -1 |
| 023 | 2 | -3 | 1 | 0 |
| 123 | 0 | 3 | 1 | 1 |
| 0123 | -1 | -5 | -4 | 0 |

Here

    Gamma = [ 0  3 -1 -1; 3  0 -1 -1;
             -1 -1  0  3; -1 -1  3  0 ],

    Gamma^{-1}=(1/15)[2 7 3 3; 7 2 3 3; 3 3 2 7; 3 3 7 2].

The full determinant is +45, while swapping rows 0 and 1 gives determinant
-45 and a strictly positive inverse. Both absent-partner margins are 1.
The present-partner margins, ordered by B=empty,2,3,23, are

    owner 0: (7,1,1,1),       owner 1: (7,1,2,2).

All guards hold strictly.

A rational root is

    q=(5/7,2/3,1,1),
    Delta(q)=(0,0,1/21,11/21),
    U(q)=B(q)=(0,-19/7,-29/21,2/7).                     (17)

The two sure quitters screen all complete responses, so the same date-zero
product root followed by Never also realizes (17). This particular fixture
has a directly checkable root; the general theorem does not assume one.

### 6.1 No nontrivial response-invariant partition

At the all-half hazard vector,

    Delta(1/2,1/2,1/2,1/2)
       =(-5/16,-1/32,-23/32,-17/32).                   (18)

These four values are pairwise distinct. This point belongs to the
block-constant hazard subspace of EVERY partition. Any nonsingleton block
would require equality of two of the values in (18). Therefore the discrete
partition is the only response-invariant partition. Its degree is +1.
This directly separates the fixture from the supplied quotient-degree test.

### 6.2 All four child-domination LPs fail

For an omitted player k, write the relaxed fourteen-row test as V lambda>=b,
lambda>=0, using only future rows F_A and join rows J_A of the supplied
capped-clock compiler. Since all child singletons equal one, this is the
variant allowed to omit the Never inequality.

The following positive row combinations y give strict Farkas certificates.
Vectors list the surviving players in increasing order.

| Omitted k | Nonzero coefficients of y | V^T y | b.y |
|---|---|---|---:|
| 0 | 2 F_2 + 3 J_12 + 4 F_3 + 9 F_123 | (-12,-12,-12) | 12 |
| 1 | J_2 + F_03 | (-1,-1,-1) | 5 |
| 2 | 86 J_0 + 19 J_1 + 22 J_01 | (-133,-602,-133) | 133 |
| 3 | 5 J_1 + 7 F_02 + 2 F_012 | (-25,-25,-28) | 25 |

Any feasible nonnegative lambda would imply
0 < b.y <= lambda.(V^T y) <= 0. Thus all four relaxed LPs, and hence the
versions retaining Never, are infeasible. These are exact integer checks.

The fixture also has no pure coalition equilibrium. Every principal triple
has a negative inverse entry. Reciprocal singleton comparisons always have
the same nonzero sign, so there is no singleton escort edge and hence no
balanced singleton cycle under the supplied escort necessity. Finally,
uniform stationary hazards tending to zero have payoff tending to
(5/4,5/4,5/4,5/4)>s. Therefore the supplied payoff-exclusion criteria fail.
These are comparisons with named sufficient tests, not a claim of exclusion
from every possible existing stationary or collision-dependent producer.

## 7. A certified full-dimensional neighborhood

Let r* be the fixture and suppose ||r-r*||_infinity<1/1000, with Never
unchanged. Every such table satisfies Theorem 2, has full degree +1, has no
nontrivial response-invariant partition, and fails all four child LPs.

Indeed ||Gamma-Gamma*||_infinity<=6 delta in maximum row-sum norm, while
||(Gamma*)^{-1}||_infinity=1. The inverse perturbation bound is

    ||Gamma^{-1}-(Gamma*)^{-1}||_infinity
        <= 6 delta/(1-6 delta) < 2/15.

Since every old inverse entry is at least 2/15, the new inverse is strictly
positive. The Neumann bound preserves invertibility along the whole segment,
so the determinant remains positive. Each raw guard difference changes by
at most 2 delta, less than its margin one.

At the all-half root each residual changes by at most 7 delta/4. The smallest
old pairwise separation is 3/16, and 7 delta/2<3/16, retaining all four
inequalities in (18).

A child LP row coefficient or right-hand side changes by at most 2 delta.
The four certificate coefficient sums are 18,2,127,14. Their resulting
errors are at most 36 delta,4 delta,254 delta,28 delta, strictly smaller
than every required sign margin in the table. All four infeasibilities
therefore persist. Also each singleton row sum remains positive; small
uniform stationary hazards still defeat payoff exclusion.

This is an open subset of the full sixty-coordinate reward space, not a
row-equality locus. On the exact paired singleton cylinder the raw guard
region likewise has nonempty interior in all forty-four nonsingleton
coordinates. The region is constrained by strict inequalities; it does NOT
include arbitrary nonsingleton completions.

## 8. A new necessary condition on counterexamples

The supplied Fin4 degree theorem says that no UE forces full Gamma to be
R0 with kappa(Gamma)=+1, hence standard Q. Suppose a hypothetical
counterexample has a pair satisfying the strict raw guards (L)-(U).
Standard Q implies each of its two rows has a positive entry: solve the
LCP at -1 to obtain Gamma x>=1. Since (L) makes every external entry of
those rows negative, their reciprocal pair entries must be positive.

In fact A=P Gamma is then R0. To see this, let x=(u,z)>=0 and w=Ax>=0
be homogeneous complementary. If z=0, the paired rows are
w_a=Gamma_ba u_a and w_b=Gamma_ab u_b, so complementarity forces u=0.
If z!=0, the strict negativity of Gamma_aJ and Gamma_bJ forces both
u_a,u_b>0. Thus w_a=w_b=0. Swapping these zero slack coordinates changes
nothing, so Gamma x=w and x is a homogeneous complementary vector for
Gamma. Its R0 property again gives x=0, a contradiction.

Theorem 1 now yields the additional necessary condition

    kappa(P_ab Gamma)=+1
    for EVERY pair passing (L)-(U).                    (19)

Consequently the matrix residual is not exhausted by full matrices and
response-invariant quotients. Strategically guarded row permutations add
another necessary degree-one family, without any exact reward symmetry.
For the positive-determinant strictly inverse-positive cylinder, its swapped
degree is -1, so EVERY such guarded pair is consumed.

## 9. Boundary warning and formalization interface

Swapping rows without guards is invalid. For a complete table whose only
nonzero entry is r_0({0,1})=2, at q=(0,1,0,0) the residual vector is
(2,0,0,0). The row-swapped map (6) fixes q, but original player 0 can join
and gain two. The guards, not determinant arithmetic alone, exclude precisely
such false fixed points.

The new proof obligations for Lean are the polynomial residual expansion,
the guarded fixed-point transfer including z=0, and the altered-map degree
argument. The existing stationary endpoint compiler can consume the produced
root, actual value, and all-player contraction:

    isZeroAsymptoticNash_stationary_of_fixedPoint_endpointNash_contracts
    isUniformEquilibriumPayoff_of_stationaryEndpointCertificate_contracts

in `UniformEquilibrium/Quitting/Stationary/EndpointCompiler.lean`. Their
statements were inspected at source snapshot
`5aac30ad2553dadd5895dc79fbc4f1f5680d7570`; no compilation or axiom audit was
performed in this work. The general theorem above is not represented as an
existing checked declaration.

The relevant supplied mathematical dependencies and comparisons are the
integer LCP degree note, stationary-response quotient note, inverse-positive
approximation note, capped-clock child-domination note, and the
three-player row-extension note's escort comparison. The complete-cap and
finite-horizon proofs needed for the new class are included here.

The theorem does not resolve all Fin4 tables. Failure of its raw guards does
not imply failure of UE, nor does it automatically produce another guarded
pair or a chronological packet. It supplies a proved raw-table producer and
an additional counterexample restriction inside the degree-one branch,
with no claimed exhaustive dispatch or general stochastic-game reduction.
