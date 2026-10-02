# Stationary-response quotient degree escape for quitting games

## Conjecture-facing change

The stationary endpoint compiler converts a suitable stationary root into
complete behavioral equilibrium, but does not produce that root from an
arbitrary reward table. The result here supplies a raw-table producer:
equality of individual stationary-response polynomials on a block-constant
hazard subspace, together with a quotient LCP degree different from +1,
forces an absorbing stationary Nash–Bellman root of the original game.
The signed four-player consequence has no supplied-strategy or punishment
hypothesis.

The quotient criterion strictly improves on testing the full singleton
matrix's degree: the explicit class below has full degree +1 and quotient
degree −1. It allows thirty-three independent nonsingleton payoff
coordinates and four arbitrary signed own-singleton levels. An exact
example additionally has a full sixty-dimensional neighborhood of games
with an exact stationary equilibrium.

The quotient producer, paired class, and example are ordinary mathematics
to be formalized. Existing checked behavioral and uniform-payoff consumers
are identified by exact declarations in Section 9. Classical integer degree
is used with the published conventions stated in Section 3.

## 1. Exact statements, definitions, and semantics

Let I be a finite nonempty player set. For every nonempty S ⊆ I, specify a
finite real reward vector r(S) in R^I. At each date t = 0,1,..., each player
chooses Continue or Quit. The first nonempty simultaneous quitting coalition
S ends live play, with terminal reward r(S). All live-stage rewards and
the terminal reward of infinite all-Continue (Never) are zero. In the
absorbing evaluation, r(S) is paid at every stage after the quitting date.

Players observe the action history. Before absorption the only possible
history is all-Continue. A behavioral strategy therefore specifies one
conditional Quit probability h_i(t) at each live date. Randomization is
private and independent across players, and a unilateral replacement may
use any behavioral strategy, with no bound on memory or stopping time.

Equivalently, independently sample each player's first-Quit time T_i in
N ∪ {Never}, with

    Pr(T_i=t) = h_i(t) product_(u<t)(1-h_i(u)),
    Pr(T_i=Never) = lim_n product_(u<n)(1-h_i(u)).

Conversely, every such law is implemented by its conditional hazards,
assigned arbitrarily when the survival event has probability zero. This
equivalence also holds after one player's complete behavioral replacement.
The first finite minimum determines the terminal coalition. No public
randomization or correlated opponent plan is introduced.

Write U_i(σ) for terminal payoff and

    B_i(σ) = sup_τ U_i(τ,σ_-i),
    d_i(σ) = B_i(σ) − U_i(σ),
    E(σ) = max_i d_i(σ),

where τ ranges over every behavioral strategy of player i. The finite
reward table is bounded, so these quantities are finite and d_i ≥ 0.

For a horizon H, absorption at date t has evaluation weight
max(H-t-1,0)/H; Never has weight zero. For patience d in (0,1), normalized
discounted evaluation has weight d^(t+1). Let U^H and U^d be the corresponding
payoffs. A uniform-equilibrium payoff v means that for each ε > 0 there
exist one behavioral profile σ and H₀ such that, for all H ≥ H₀,

    |U_i^H(σ) − v_i| ≤ ε,
    U_i^H(τ,σ_-i) ≤ U_i^H(σ) + ε     for every i and every τ.

The same-profile stationary conclusions below mean that one fixed
stationary σ serves at every accuracy after increasing H₀; the proof also
gives the corresponding bounds for sufficiently patient discounted
evaluations.

Write

    s_i = r_i({i}),       Gamma_ij = r_i({j}) - s_i.

For stationary product hazards q, let the opponents' quitting-set law be the
ordinary independent product law, and define

    alpha_i(q) = product_{j!=i}(1-q_j),
    p_i(T;q) = product_(j in T) q_j
               product_(j in I \ (T union {i})) (1-q_j),
    Q_i(q) = sum_(T subset I\{i}) p_i(T;q) r_i(T union {i}),
    H_i(q) = sum_(nonempty T subset I\{i}) p_i(T;q) r_i(T),
    Delta_i(q) = (1-alpha_i(q)) Q_i(q) - H_i(q).                 (1)

These are polynomials in the original hazards; Delta_i does not depend on
q_i. No empty terminal reward or continuation payoff is inserted into (1).

Partition I into nonempty blocks O_1,...,O_k. Let E:R^k -> R^I repeat each
coordinate on its block. The raw partition condition is

    Delta_i(E x) = Delta_j(E x)   whenever i,j lie in one block,
                                 for every x in [0,1]^k.       (RI)

This is a finite raw-table test: expand the two polynomials and equate
coefficients. Each coefficient is linear in the terminal rewards. It is not
an assumption about the existence of an equilibrium or a favorable root.
Polynomial identity makes (RI) equivalent to the same identity on R^k.

The first derivative of Delta at zero is -Gamma. Consequently (RI) makes

    A_ab = sum_{j in O_b} Gamma_{i_a,j},     i_a in O_a,          (2)

independent of the representative. The embedding satisfies Gamma E=E A.
These are sums, not averages; A_aa need not vanish. A is not being treated
as the singleton matrix of a smaller quitting game.

For a real k-by-k matrix A and b in R^k, LCP(A,b) is the system

    x >= 0,       w = A x+b >= 0,       x_a w_a = 0 for every a.

The map f_b(x)=min(x,A x+b), coordinatewise on the whole ambient space,
has exactly these zeros. A is R0 if LCP(A,0) has only zero as a solution.
For R0 A, define kappa(A) as the integer Brouwer degree
deg(f_0,(-1,1)^k,0). Section 3 proves the radius and right-hand-side
independence used below. In LCP(A,-1), the symbol 1 denotes the all-ones
vector.

For a continuation vector v and a product row q, define the one-stage
successor payoff

    F_r(v,q)_i = q_i Q_i(q) + (1-q_i)H_i(q) + C(q)v_i,
    C(q) = product_j(1-q_j).

Against that continuation, player i's Quit endpoint is Q_i(q), and its
Continue endpoint is H_i(q)+alpha_i(q)v_i. Exact one-stage Nash means that
the prescribed mixture attains the larger of these two endpoints.

### Theorem A: raw finite-dimensional root producer

Suppose (RI) holds, A is R0, and kappa(A)!=+1. Then there are block-constant
hazards q=E x in [0,1]^I, with positive joint absorption, and a vector v such
that

    v = F_r(v,q),        q is exact one-stage Nash against v.   (3)

The vector v is the actual terminal payoff of repeating q. More precisely,
the nonzero fixed points of the stationary-response map constructed below
have total degree 1-kappa(A). Thus the paired example below has total
absorbing-root degree +2 in the three-dimensional hazard subspace.

The theorem holds for arbitrary signed rewards and arbitrary finite player
counts. Its conclusion is a stationary Nash–Bellman root, not yet a guarantee
against a negative sole quitter's Never response.

### Theorem B: complete strategic consequences

Under Theorem A's hypotheses:

* If every player in a singleton block has s_i>=0, repeating the produced q
  is exact terminal Nash against every behavioral replacement, and the same
  profile is uniform at v.
* If every singleton-block player is punishment-normal, the game has an
  ordinary uniform-equilibrium payoff. Here punishment-normal means
  mu_i<=s_i, with mu_i the infimum over independent opponent plans of the
  supremum payoff over all complete i-responses. A negative sole owner may
  require punishment-completed approximants.
* For four players, UE follows for arbitrary signed rewards, without
  normality as an input. The existing same-table no-UE reduction supplies
  normality under the contrary assumption.

If every block has at least two players, the first conclusion therefore
holds with arbitrary signed rewards and any finite player count.

### Optional raw strengthening of the exact-stationary conclusion

For every singleton-block owner i with s_i<0, suppose the following
one-variable system has no solution:

    0<h<=1,
    r_j({i}) >= (1-h)s_j + h r_j({i,j})     for every j!=i.     (SG)

This is a finite set of linear inequalities in h, with coefficients from
the literal reward table. Under Theorem A and this sole-owner exclusion
condition, every nonzero fixed point of the quotient map is an exact
behavioral terminal Nash equilibrium and the same profile is uniform at
its payoff. Nonnegative singleton-block rewards make the condition vacuous
and recover Theorem B's first bullet. Section 5 proves the strengthening.

### Counterexample-facing form and inverse test

Every hypothetical Fin4 counterexample satisfies, for every partition
obeying the raw identity (RI),

    A is R0,                      kappa(A)=+1.                 (4)

In particular this applies to every player-orbit partition of every subgroup
of the full reward-table automorphism group. A reward-table automorphism
is a permutation p of I satisfying r_(p i)(p S)=r_i(S) for all i,S.
The discrete partition gives A=Gamma. A useful direct Fin4 corollary is

    (RI),       det A<0,       A^{-1}>=0   ==>   UE(r).         (5)

Zero inverse entries are allowed: first obtain R0 under no UE, then compute
the degree. Strict inverse positivity already implies R0 directly.

### Strategic inputs and the response-quotient adapter

The **response-invariant partition adapter** takes the literal reward table
and a nonempty-block partition. It forms the finite polynomial identities
(RI), the row-sum matrix A, and the specified R0 and degree tests. These are
conditions on finite reward data, not assumed equilibria or continuation
values. For Fin4, the inverse test (5) is a direct matrix sufficient
condition without an input R0 witness.

The degree argument produces q and its actual terminal payoff v. The
independent stationary behavioral profile is obtained by repeating q.
Section 5 produces every additional punishment-completed profile needed
for a normal negative sole owner, using an approximate infimum minimizer
from the definition of normality. For signed Fin4, the same-table
no-UE theorem in Section 9 supplies normality under contradiction. No
strategic witness remains as an extra input to the signed Fin4 conclusion.

For arbitrary finite cardinality, Theorem B's normality alternative is
the explicitly stated hypothesis mu_i<=s_i on singleton-block players.
It is not produced for arbitrary games. The unconditional sign alternative
and the no-singleton-block alternative require no punishment plan.

## 2. A 33-coordinate paired completion class

Take

    Gamma = [ 0  3 -1 -1
              3  0 -1 -1
             -1 -1  0  3
             -1 -1  3  0 ].                                  (6)

Let p=(0 1). Require only the following equality of the TWO paired players'
centered terminal payoff rows:

    r_1(p S)-s_1 = r_0(S)-s_0       for every nonempty S.        (7)

The singleton instances already follow from (6). All four own-singleton
levels are arbitrary signed reals. Choose freely all eleven nonsingleton
entries for recipient 0, and all twenty-two for recipients 2 and 3. Equation
(7) defines recipient 1's eleven nonsingleton entries. Thus thirty-three
nonsingleton entries are independent, with no bounds or sign restrictions.

**Corollary.** Every table satisfying (6)-(7) has UE. If s_2,s_3>=0, it has
an exact stationary terminal equilibrium with q_0=q_1, uniform at its payoff.
The two paired singletons s_0,s_1 may still be negative or unequal.

To prove the raw identity, put q=(x,x,y,z) and c=s_1-s_0. Relabeling the
opponent sets in the two finite expectations gives

    alpha_1=alpha_0=alpha,
    Q_1=Q_0+c,            H_1=H_0+(1-alpha)c.

Hence Delta_1=Delta_0. There is no required comparison between Delta_2 and
Delta_3 because their blocks are singletons. In particular no restriction
on recipients 2 and 3 is hidden in (7). This algebra does not translate the
game or change Never's payoff.

For the partition {0,1},{2},{3}, the quotient is

    A = [ 3 -1 -1
         -2  0  3
         -2  3  0 ],

    det A=-15,
    A^{-1}=(1/15) [9 3 3
                    6 2 7
                    6 7 2] >0.                               (8)

It is R0 and has degree -1. To see the first assertion, a homogeneous
solution with nonzero slack w>=0 would satisfy x=A^{-1}w>0; complementarity
would then force w=0, a contradiction. Zero slack gives x=0. For the
second assertion, any solution of LCP(A,-1) satisfies
x=A^{-1}(1+w)>=A^{-1}1>0, hence w=0 and x=A^{-1}1=1.
Its index is sign det A=-1 by Section 3.

In contrast,

    det Gamma=45,
    Gamma^{-1}=(1/15) [2 7 3 3
                        7 2 3 3
                        3 3 2 7
                        3 3 7 2] >0.                         (9)

The same argument gives full R0 and kappa(Gamma)=+1. Thus a full-matrix
degree test cannot force a nonzero root for this class, whereas the
quotient test does. Restricting to q_0=q_1
removes one of the two negative within-pair modes; the quotient determinant
has the opposite sign.

Whole-table symmetry under p is one special case of (7), when s_0=s_1 and
the other recipients' rows are also symmetric. But changing only
r_2({0,2}) to any real number preserves the new class and generally destroys
that whole-table symmetry. This exhibits why the residual-map condition is
strictly weaker.

## 3. Classical degree facts used

For R0 A, the map f_0(x)=min(x,A x) has no nonzero zero on the whole R^k.
It is continuous and positively homogeneous. Therefore

    c_A = min_{||x||_infinity=1} ||f_0(x)||_infinity >0,
    ||f_0(x)||_infinity >= c_A ||x||_infinity.                 (10)

Since f_0 has no nonzero zero, excision and positive homogeneity give the
same degree kappa(A) on every centered box of positive radius.

For completeness, LCP solutions are uniformly bounded when b ranges over
a bounded set. Otherwise choose solutions x_n with ||x_n|| tending to
infinity and pass to a subsequence for which x_n/||x_n|| tends to a
unit vector z. Dividing the nonnegative primal and slack coordinates and
their complementarity equations by the corresponding powers of ||x_n||
gives z>=0, Az>=0, and z_a(Az)_a=0. This contradicts R0. The homotopy
b_t=t b therefore has all zeros in one sufficiently large box; homotopy
invariance and excision identify deg(f_b) with kappa(A).

At a strictly complementary solution, let S be the set of positive
coordinates of x. In a neighborhood of the solution, f_b uses the slack
coordinate (Ax+b)_a for a in S and x_a for a outside S. With the same
permutation of rows and columns, its Jacobian has diagonal blocks A_SS
and the identity and zero lower-left block. If A_SS is nonsingular, its
local degree is therefore sign det A_SS.

The proof uses integer-degree normalization, homotopy invariance, stability
under uniform boundary-small perturbations, excision and additivity. A primary
source for these conventions is M. S. Gowda, “Applications of Degree Theory to
Linear Complementarity Problems,” Mathematics of Operations Research 18(4),
1993, 868-879, Section 2, printed pages 869-870
([original article](https://doi.org/10.1287/moor.18.4.868)).
These are classical published topological results, not additional strategic
hypotheses. Mod-2 degree cannot distinguish the values +1 and -1 used here.

## 4. Direct stationary-map proof of Theorem A

### 4.1 Nonzero fixed points are full individual Nash–Bellman roots

Put

    C(q)=product_i(1-q_i),       a(q)=1-C(q),
    R_i(q)=q_i Q_i(q)+(1-q_i)H_i(q).

For q!=0 in the strategy cube, a(q)>0 and the actual terminal payoff of
repeating q is

    v_i(q)=R_i(q)/a(q).

Since C=(1-q_i)alpha_i, direct algebra gives

    a(q)[Q_i-H_i-alpha_i v_i(q)] = Delta_i(q).                 (11)

Thus the stationary endpoint Nash conditions are exactly

    q_i=0       ==> Delta_i<=0,
    0<q_i<1     ==> Delta_i=0,
    q_i=1       ==> Delta_i>=0.                               (12)

Write Dbar_a(x)=Delta_{i_a}(E x), using (RI), and define on the WHOLE R^k

    T(x)=clip_[0,1]^k(x+Dbar(x)),       Z(x)=x-T(x).             (13)

Its fixed points belong to [0,1]^k. Every nonzero one satisfies (12) for
every original player, because the coordinates within each block agree in
both hazard and unilateral residual. It therefore gives exactly (3).

Crucially, no player's test is replaced by a joint deviation of its block.
Equal hazards are implemented by independent coins. Equation (11) and
continuity of the finite expectations are all that is needed; no discounted
values, analytic arc, or affine reward transformation appears in this proof.

### 4.2 The global degree is +1

On Omega=(-1,2)^k the map T takes values in the interior cube [0,1]^k.
Homotope it to the constant cube center. The displacement has no boundary
zero throughout, so

    deg(Z,Omega,0)=+1.                                       (14)

The expanded domain includes lower and upper strategy-boundary fixed points.
Using (0,1)^k instead would incorrectly omit proper-support solutions.

### 4.3 The all-Continue zero has local degree kappa(A)

At q=0, all Delta_i vanish. First-order expansion gives

    1-alpha_i=sum_{j!=i}q_j+O(||q||^2),
    Q_i=s_i+O(||q||),
    H_i=sum_{j!=i}q_j r_i({j})+O(||q||^2),

and therefore

    Delta(q)=-Gamma q+O(||q||^2),
    Dbar(x)=-A x+O(||x||^2).                                 (15)

All collision rewards remain present in the higher terms. These identities
hold in an ambient real neighborhood, not just at nonnegative hazards.

Near zero, x+Dbar(x) is uniformly small, so the upper clip is inactive.
The lower clip is essential. Hence

    Z(x)=min(x,-Dbar(x))=min(x,A x+O(||x||^2)).                 (16)

Coordinatewise minimum is 1-Lipschitz in its second argument. Thus for some
K>=0, ||Z(x)-f_0(x)||<=K||x||^2 near zero. Choose a sufficiently small
radius rho<1/2 with K rho<c_A. On 0<||x||<=rho, (10) then gives Z(x)!=0.
The straight homotopy from f_0 to Z likewise has no zero on the radius-rho
boundary. Therefore

    deg(Z,(-rho,rho)^k,0)=kappa(A).                            (17)

This proves both isolation and the local degree at the artificial
all-Continue zero. No individual nonzero root is assumed isolated.

### 4.4 Degree left over forces an absorbing root

Excision and additivity in (14)-(17) give

    deg(Z,Omega \ [-rho,rho]^k,0)=1-kappa(A).                 (18)

When kappa(A)!=1 this is nonzero, so Z has a zero outside that small cube.
It is a nonzero strategy-cube fixed point. Section 4.1 identifies it with
the desired actual stationary root. This proves Theorem A, including its
nonzero-root total-degree statement.

## 5. Complete behavioral and uniform-payoff proof

Let q,v be the root produced by Theorem A, now in the original game.
For a queried player i use the original Q_i,H_i,alpha_i. Exact root Nash
and the fixed-point equation give

    Q_i<=v_i,             H_i+alpha_i v_i<=v_i.             (19)

If alpha_i<1, the actual complete response cap is

    B_i=max(Q_i,H_i/(1-alpha_i))<=v_i.                     (20)

Indeed a pure quit at date t gives

    H_i(1-alpha_i^t)/(1-alpha_i)+alpha_i^t Q_i,

Never gives H_i/(1-alpha_i), and arbitrary replacement laws average
these responses. Prescribed play attains v_i. This proves d_i=0 without
restricting deviations to stationary strategies.

If at least two original players have positive hazards, every alpha_i<1.
Let L_i be the first opponent-quit date. It is geometric, with
E[L_i+1]=1/(1-alpha_i). Under any complete i-response, the first absorption
date tau is at most L_i. Choose M>0 bounding every |r_i(S)|. Since

    1 - max(H-tau-1,0)/H <= (tau+1)/H,

terminal and finite-average payoffs differ by at most
M/[H(1-alpha_i)], uniformly over all i-responses, including prescribed
play. Exact terminal Nash therefore implies horizon-H regret at most
2M/[H(1-alpha_i)]. Prescribed averages converge to v.

Likewise 1-d^(tau+1)<=(1-d)(tau+1) gives discounted regret at most
2M(1-d)/(1-alpha_i) and prescribed discounted payoffs converging to v.
Finitely many players allow one horizon or patience threshold for all
players. Thus the same stationary profile is uniform at v; no estimate
uniform over all possible roots is asserted.

If some alpha_i=1, positive joint absorption forces i to be the unique
active player. Its fixed-point value is s_i and its complete cap is
max(s_i,0). Such an i must be a singleton block. If s_i>=0, its cap is
already correct. Its deviations have nonnegative sole-quitting rewards,
so delaying their payment cannot improve their average over the terminal
cap; prescribed averages tend to s_i. Outsider clocks still contract.
For a sole owner with hazard h>0 and s_i>=0, every discounted response
is at most s_i. Its prescribed delivery shortfall, and hence its discounted
regret, is at most M(1-d)/h by the same geometric-clock estimate. Outsiders
obey the preceding contracting-clock estimate.
This proves the first assertion of Theorem B.

For the optional strengthening, consider a possible sole-owner profile
q=h e_i, where 0<h<=1. It is block-constant exactly when i is in a
singleton block. Its original residuals are

    Delta_i=0,
    Delta_j=h[(1-h)s_j+h r_j({i,j})-r_j({i})]     for j!=i.

Thus it is a nonzero fixed point precisely when h satisfies the
inequalities in (SG). Infeasibility for every negative singleton-block
owner excludes exactly the bad sole-owner roots. Every other nonzero root
has two positive original hazards or a nonnegative sole owner, so the
preceding complete-cap and same-profile uniform arguments apply. Failure
of the condition only permits such a bad root; it does not assert that
no other exact equilibrium exists.

For the remaining case suppose s_i<0 but mu_i<=s_i. Let M>0 bound
all original rewards. For each epsilon>0 choose one independent opponent
punishment plan with complete i-cap at most s_i+epsilon. Prescribe K rows
of the produced solo-i hazard q_i, then that punishment plan; let i use
Never after K. Put rho=(1-q_i)^K.

Any i-response quitting before K gets s_i. Any response surviving to K
faces the supplied punishment cap. Therefore its full cap is at most
s_i+epsilon. Its prescribed payoff differs from s_i by at most 2M rho.
For an outsider j, compare with infinite solo-i play. Under any j-response
the outcomes differ only if the independent i-clock survives the K rows,
an event of probability rho. Hence its cap is at most v_j+2M rho and
its prescribed payoff is at least v_j-2M rho. Thus

    d_i<=epsilon+2M rho,      d_j<=4M rho (j!=i),
    ||U-v||_infinity<=2M rho.

Taking epsilon=1/n and K=n, for positive integers n, gives terminal
approximate Nash errors tending to zero and terminal payoffs tending to
the one fixed target v. The existing declaration
`quittingGame_isUniformEquilibriumPayoff_of_terminalNash_tendsto`,
whose exact scope is given in Section 9, yields UE at v. No cap attainment
is used in choosing the punishment plan. No assertion that the strategies'
limit is an equilibrium is required.

For signed Fin4, assume no UE. Choose a bound M for the finite reward table.
The same-table theorem
`nonempty_finFourQuantitativeFullSupportHardResidual_of_no_uniformPayoff`
supplies mu_i<=s_i for all four players. Apply Theorem A and the preceding
complete-response construction to contradict no UE. This proves the signed
raw criterion in Theorem B without changing any reward or Never's payoff.

## 6. The counterexample-facing and inverse consequences

Assume no Fin4 UE. The same-table theorem supplies punishment normality
for all players. The existing declaration
`exists_uniformEquilibriumPayoff_of_homogeneous_supported_normal`
excludes a nonzero homogeneous complementary vector of Gamma: normalize
that vector to the unit simplex and use normality on its positive support.
The exact interface is stated in Section 9. If x is such a vector for A, its
block-constant lift E x satisfies

    E x>=0,     Gamma E x=E A x>=0,
    (E x)_i (Gamma E x)_i=0.

Normalize this nonzero vector by its positive coordinate sum. The same-table
punishment normality supplies the consumer's support-normality premise.
Therefore A must be R0. Theorem B then forces kappa(A)=1, proving (4).

For (5), assume no UE and use this R0 conclusion. Any solution of
LCP(A,-1) satisfies

    x=A^{-1}(1+w)>=A^{-1}1>0.

Every row of an invertible nonnegative matrix is nonzero, proving the last
strict inequality. Complementarity forces w=0. Thus the solution is unique,
full-support and has index sign det A=-1. Right-hand-side independence gives
kappa(A)=-1, contradicting (4). Uniqueness at one right-hand side is not
being used to infer R0.

Every full reward-table automorphism group gives a special case of (RI).
For an automorphism p and an orbit-constant q, the bijection T -> pT
preserves each product probability and sends the endpoint reward for i to
that for p i. Hence alpha_(p i)=alpha_i, Q_(p i)=Q_i, and H_(p i)=H_i.
This proves residual equality on each orbit, so every subgroup's orbit
partition is admissible. No test of only the largest group is required.

## 7. A complete rational example and exact stationary realization

This fixture has s=(1,1,1,1), singleton matrix (6), and the required
transposition symmetry. Coalition strings denote sets.

| S | r_0 | r_1 | r_2 | r_3 |
|---|---:|---:|---:|---:|
| 0 | 1 | 4 | 0 | 0 |
| 1 | 4 | 1 | 0 | 0 |
| 01 | 2 | 2 | 3 | 2 |
| 2 | 0 | 0 | 1 | 4 |
| 02 | 1 | 1 | -1 | 1 |
| 12 | 1 | 1 | -1 | 1 |
| 012 | -2 | -2 | 0 | 1 |
| 3 | 0 | 0 | 4 | 1 |
| 03 | 1 | 0 | -1 | 3 |
| 13 | 0 | 1 | -1 | 3 |
| 013 | -2 | -2 | 2 | 1 |
| 23 | 3 | 3 | 4 | -1 |
| 023 | -1 | 2 | 2 | -1 |
| 123 | 2 | -1 | 2 | -1 |
| 0123 | 1 | 1 | 4 | 4 |

### 7.1 Algebraic hazards, not numerical root selection

Let x be the unique zero in (197/1000,1/5) of

    f(x)=3x^3-10x^2+12x-2.

The endpoint signs are opposite and f'>=8 on this interval. Choose y as
the zero in (1/2,3/5) of

    F(x,y)=4x^2 y^2-5x^2 y+x^2-4x y^2+3xy-3x+y.

At y=1/2 the value is 1/2-(5/2)x-(1/2)x^2<0. At y=3/5 it is
3/5-(66/25)x-(14/25)x^2>0. Moreover F_y>0 throughout the rectangle:
using x(1-x)<=4/25 gives the lower bound

    F_y >= -8(4/25)(3/5)-5(1/5)^2+3(197/1000)+1 > 0.

Thus these are well-defined algebraic numbers. Set

    q=(x,x,y,0).

For original stationary endpoint residuals D_i=(1-alpha_i)Q_i-H_i,
exact expansion gives

    D_0=D_1=F(x,y),        D_2=-x f(x),

    D_3=9x^4 y^2-13x^4 y+4x^4-22x^3 y^2+34x^3 y-12x^3
        +15x^2 y^2-18x^2 y+5x^2+4xy+2x-2y^2-3y.

On the rectangle above, discard the negative monomials other than
-2y^2-3y, bound positive monomials at x=1/5,y=3/5, and bound those two
negative terms using y>=1/2. The resulting upper bound is -8269/15625 = -0.529216,
strictly below -1/2. Hence D_3<0, and all four stationary Nash conditions
hold. All opponent clocks contract because three players have positive
hazards.

The exact payoff is

    v_0=v_1=1+x-4xy,
    v_2=(x-1)(3x-1),
    v_3=(4y-6xy+x^2 y+2x^2)/(1-(1-x)^2(1-y)).

For orientation only, x is approximately 0.19713723 and y approximately
0.51628606, giving v approximately (0.79002041,0.79002041,0.32804033,2.25552423).
The proof uses the rational intervals and exact identities, not those decimals.

### 7.2 Full-dimensional persistence of this example

On the three active coordinates, the Jacobian of (D_0,D_1,D_2) at
(x,x,y,0) has determinant

    -2 A_0 B_0 C_0,
    A_0=6x^3-15x^2+12x-1,
    B_0=8x^2 y-5x^2-8xy+3x+1,
    C_0=8xy^2-10xy+2x-4y^2+3y-3.

Throughout the same rectangle,

    A_0 >= -15(1/5)^2+12(197/1000)-1 >0,
    B_0 >0 by the preceding F_y bound,
    C_0 <=8(1/5)(3/5)^2+2/5+9/5-3<0.

The determinant is nonzero. The implicit function theorem and D_3<0 give
an exact stationary equilibrium on a full reward neighborhood, allowing
arbitrary small symmetry-breaking changes of all sixty entries. Its three
active hazards remain interior and all deleted clocks still contract.
No numerical radius for this neighborhood is asserted.

### 7.3 No deterministic terminal equilibrium in the exact table

The fixture has no deterministic behavioral terminal equilibrium. In coalition
order 0,1,01,2,02,12,012,3,03,13,013,23,023,123,0123, toggle the membership
of the following players:

    3,3,0,0,2,2,0,0,2,2,0,3,0,1,0.

The corresponding gains r_i(S symmetric-difference {i})-r_i(S), obtained
directly from the table, are

    3,3,2,1,1,1,3,1,3,3,2,5,4,4,1.

Every changed coalition is nonempty. For a deterministic clock profile
with finite first quitting date t and coalition S, an outside player in
this list can join at t. A listed quitting player can instead use Never;
at least one other member of S still quits at t. Thus possible later
deterministic clocks do not affect the displayed profitable deviation.
If all clocks are Never, any player gains one by quitting immediately.
The mixed equilibrium in Section 7.1 therefore supplies a genuinely
randomized positive boundary example.

### 7.4 The same exact fixture in canonical single-pivot form

Define a second literal table, still with zero Never reward, by

    r^can_i(S)=r_i(S)-b_i,       b=(0,1,1,1),   S nonempty.

Its own-singleton vector is exactly (1,0,0,0). It retains Gamma (6) and
the centered two-recipient condition (7), but it no longer has the full
player-swap symmetry. At every stationary root, the polynomial residuals
are unchanged: Q_i changes by -b_i and H_i by -(1-alpha_i)b_i, which cancel
in Delta_i. Consequently the same algebraic hazards (x,x,y,0) satisfy the
same strict and equal endpoint conditions. All deleted clocks contract,
so this is again exact terminal Nash and uniform for the same profile.
Its fixed payoff is

    v^can=v-(0,1,1,1)
         approximately (0.79002041,-0.20997959,-0.67195967,1.25552423).

This does not assert strategic equivalence of the two games for arbitrary
profiles: their Never payoff remains fixed at zero. It proves the stationary
root and complete-cap assertions anew through the exact residual identities.

All displayed nonempty membership-toggle gains are unchanged by the
recipient shifts. All-Never is still defeated by player 0, whose singleton
reward remains one. The canonical table also has no deterministic terminal
equilibrium. Every shifted terminal coordinate has absolute value at most
four, as the displayed table shows. Dividing this second table by four
gives a literal table in [-1,1], with singleton vector (1/4,0,0,0);
the same strategy is exact terminal Nash and uniform with payoff v^can/4.

## 8. Exact negative and degenerate boundary tests

### 8.1 A negative sole-owner root and a discontinuous Never cap

Take two players with

    r({0})   = (1,-1),
    r({1})   = (1/2,-1/2),
    r({0,1}) = (-1,1).

Never pays zero. The discrete partition is response-invariant and

    Gamma = [0,-1/2;-1/2,0].

This matrix is R0: x>=0 and Gamma x>=0 force both coordinates of x to
vanish. LCP(Gamma,-1) has no solution, since each slack coordinate is
strictly negative for x>=0. Its degree is therefore zero.

At q*=(0,1/4), the actual payoff is v=(1/2,-1/2). For player 0,

    alpha_0=3/4,       Q_0=1/2,       H_0=1/8,

so both endpoints equal v_0. For player 1, all opponents Continue,
Q_1=-1/2 and H_1=0, so both one-stage endpoints equal v_1.
Thus q* is an absorbing Nash–Bellman root, but player 1 gains 1/2 by
using Never. The omitted implication from a root directly to complete
terminal Nash is false even for an R0, degree-zero full matrix.

For q^t=(t,1/4), with 0<t<=1, direct substitution gives the same actual
payoff v. Player 0's complete cap is 1/2. Player 1's Quit endpoint is
-1/2+3t/2 and its Never endpoint is -1, so its cap is -1/2+3t/2.
Consequently E(q^t)=3t/2 tends to zero as t decreases to zero, but
E(q*)=1/2. A vanishing opponent clock can make the terminal cap
discontinuous. Strategy-limit closure is therefore not a valid replacement
for the fixed-payoff terminal-target argument in Section 5.

Player 1 is nevertheless punishment-normal. Immediate Quit guarantees
at least -1/2 against every opponent plan. Constant opponent hazard t>0
has full cap -1/2+3t/2, giving punishment value exactly -1/2 by passage
to the infimum. Normality permits approximation; it does not make this
unmodified negative-sole-owner root an exact equilibrium. Here the
sole-owner system (SG) for i=1 is 1/2>=1-2h, so it is feasible for
h>=1/4 and correctly does not certify exactness of every root.

### 8.2 A singular quotient and nonisolated upper-boundary roots

Take four players, partitioned into {0,1},{2,3}, and define

    Gamma = [ 0   -1  -1/2 -1/2
             -1    0  -1/2 -1/2
             -1/2 -1/2  0   -1
             -1/2 -1/2 -1    0 ],
    r_i(S) = sum_(j in S) Gamma_ij.

The literal singleton matrix of this game is Gamma, since every s_i=0.
For this additive reward table, Q_i=H_i=sum_(j!=i) Gamma_ij q_j,
hence Delta_i=-alpha_i sum_(j!=i) Gamma_ij q_j.
At q=(x,x,y,y), this gives the common block residuals

    Dbar_1=(1-x)(1-y)^2(x+y),
    Dbar_2=(1-x)^2(1-y)(x+y).

Thus (RI) holds and A=[-1,-1;-1,-1]. This singular matrix is R0 because
every nonzero nonnegative vector has strictly negative coordinates under
A. LCP(A,-1) has no solution, so kappa(A)=0.

Every point on x=1 or y=1 is a quotient fixed point. In particular (1,0)
is a proper-support root, and the absorbing root set is not discrete.
The total nonzero-root degree remains +1. This test requires both the
expanded ambient domain and the use of a total set degree instead of
unproved individual root indices. Each block has two players, so these
roots also meet the complete-cap conclusion.

### 8.3 Nonnegative inverse and unique inhomogeneous solution do not imply R0

The matrix A=[0,1;1,0] has determinant -1 and nonnegative inverse.
LCP(A,-1) has the unique positive solution x=(1,1), but LCP(A,0) has
the nonzero solution x=(1,0), with slack (0,1). Thus the inverse test
cannot establish R0 solely from uniqueness at right-hand side -1.
Section 6 instead derives R0 from the full homogeneous-normal consumer
under no Fin4 UE before assigning the quotient its degree.

## 9. Source correspondence and semantic consumers

The following are existing checked repository results, separate from the
ordinary mathematical quotient producer proved above.

- `normalizedSoloMatrix_eq_soloReward_sub` in
  `UniformEquilibrium/Quitting/Classification/PreemptionGateDictionary.lean`
  identifies the normalized singleton entry at recipient i and quitter j
  with r_i({j})-r_i({i}). Thus the matrix here is exactly the matrix used
  by the homogeneous consumer, in the correct orientation.
- `nonempty_finFourQuantitativeFullSupportHardResidual_of_no_uniformPayoff`
  in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/FullSupportProjectiveQBarResidual.lean`
  takes a literal Fin4 reward table, a coordinate bound, and the assumption
  that this same game has no uniform-equilibrium payoff. It returns
  `FinFourQuantitativeFullSupportHardResidual`, whose
  `all_punishmentNormal` field asserts normality for all four players.
  Section 5 supplies the finite bound and uses this field without reward
  normalization or a new table.
- `quittingBestReplyValue` and `quittingPunishmentValue` in
  `UniformEquilibrium/Quitting/Stationary/MinMax.lean` use respectively
  the supremum over complete behavioral replies and the infimum over
  independent behavioral opponent plans. `IsQuittingNormalPlayer` in
  `UniformEquilibrium/Quitting/Classification/AbnormalPlayers.lean`
  is the inequality mu_i<=s_i used here, including when s_i is negative.
  These definitions justify the approximate punishment-plan selection;
  an attained min-max is not assumed.
- `exists_uniformEquilibriumPayoff_of_homogeneous_supported_normal` in
  `UniformEquilibrium/Quitting/Classification/LCP/HomogeneousProductionNormalDispatch.lean`
  takes a simplex vector w with Gamma w>=0, w_i(Gamma w)_i=0,
  and mu_i<=s_i for each positive coordinate. Its conclusion is a
  uniform-equilibrium payoff of the original game. Section 6 supplies
  w=Ex/sum_i(Ex)_i and all of these hypotheses. A possible simplex
  vertex is included in the declaration's scope.
- `IsQuittingStationaryBoundaryAdmissible`,
  `quittingStationaryFullRateUnilateralCap_le_of_fixedPoint_endpointNash`,
  and `isZeroAsymptoticNash_stationary_iff_endpointNash_and_boundary` in
  `UniformEquilibrium/Quitting/Stationary/EndpointCompiler.lean`
  are the exact stationary endpoint-to-full-cap interfaces. The additional
  boundary inequality is max(0,s_i)<=v_i whenever every opponent of i
  continues surely. Section 5 proves exactly this inequality in its
  same-profile cases and treats its failure separately.
- `quittingGame_isUniformEquilibriumPayoff_of_terminalNash_tendsto` in
  `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`
  takes actual terminal approximate Nash profiles with errors tending
  to zero and actual terminal payoffs tending to one specified vector v.
  It concludes that v is a uniform-equilibrium payoff. Section 5's
  punishment-completed profiles supply both convergences; convergence
  of the strategies to an equilibrium is neither a premise nor a claim.

The published topological input is the integer-degree theory specified
in Section 3. The additional finite-dimensional content is the raw
response-invariant partition and its original-player root adapter,
the quotient obstruction, the paired class, and the exact example.
No publication-priority claim is made.

## 10. Actual-data application and Lean handoff

For a literal four-player reward table, the response-invariant partition
adapter computes the polynomials and quotient directly. A partition passing
(RI), R0 and kappa(A)!=1 gives UE by Theorems A and B. Alternatively,
(RI), det A<0 and A^{-1}>=0 suffice by the same-table contradiction and
homogeneous lift. The paired centered-row identities (6)-(7) are an explicit
affine reward criterion ensuring these tests, with no selected stationary
root as an input.

The ordinary mathematics to formalize has the following narrow structure:

1. Define the finite product polynomials Q, H, alpha and Delta. Establish
   their independence from the owner's hazard, origin derivative -Gamma,
   and the nonzero-root identity (11).
2. Define a nonempty-block partition, coordinate-repetition embedding,
   the raw polynomial condition (RI), and the row-sum matrix A.
   Prove Gamma E=EA and the homogeneous complementary lift.
3. Define the whole-space clipped response map, and prove that its
   nonzero fixed points satisfy each original player's endpoint Nash
   condition at the actual stationary terminal payoff.
4. Establish the R0 homogeneous norm bound, the integer LCP degree
   convention, and the local comparison at zero. Combine global degree,
   excision and existence to produce a nonzero fixed point. Neither
   an equilibrium nor a nonzero fixed point is a structure input.
5. Apply the existing endpoint/full-cap and same-table normality
   declarations. Formalize the finite solo-prefix punishment completion
   and its terminal error and fixed-target bounds when required.
   The optional sole-owner exclusion is a separate finite linear
   condition giving the stronger same-profile conclusion.
6. Prove the paired centered-row adapter and matrix identities. For the
   exact table, use the rational root brackets, explicit residuals,
   active Jacobian and strict inactive inequality in Section 7.

The existing behavioral consumers should be reused with their actual
hypotheses, especially the Never boundary condition. The game-specific
quotient and classical degree argument are not asserted to be existing
Lean declarations. No assumed field expressing the desired UE conclusion
is part of the actual-data adapter.

## 11. Scope and nonclaims

The raw class is strictly broader than the full-matrix degree mismatch
test, but is not all finite quitting games or all four-player games.
A general table may have no useful nondiscrete response-invariant
partition. For the discrete partition, E is the identity and the theorem
is exactly its full-matrix instance.

No reward table is averaged to manufacture symmetry. The quotient is not
a smaller-player quitting game. Block members use independent coins and
each retains its own complete deviation test. The paired criterion concerns
only the two specified centered recipient rows; it does not include
arbitrary nonsingleton completions of Gamma.

The paired affine class has thirty-three freely assigned nonsingleton
entries, not an open subset of the full sixty-coordinate reward space.
The separate solved open neighborhood in Section 7.2 follows from the full
active-coordinate Jacobian and strict inactive inequality; it does not
assert persistence of (RI) under arbitrary perturbation.

For arbitrary finite player counts, Theorem A, the sign and normality
alternatives of Theorem B, and the optional sole-owner exclusion remain
valid. Normality is a stated sufficient hypothesis, not proved logically
necessary for arbitrary-cardinality UE under these quotient assumptions.
No unconditional cardinal reduction to four is supplied.

An absorbing stationary Nash–Bellman root with a negative sole owner is
not asserted to be terminal Nash or uniform. Total nonzero-root degree is
not a root count, and no isolated nonzero roots, regular root selection,
discounted invariant quotient, analytic germ, or quantitative neighborhood
radius is assumed. The signed Fin4 consumer concludes existence of an
ordinary uniform-equilibrium payoff, not unconditional exact stationary
equilibrium in every game of the class.
