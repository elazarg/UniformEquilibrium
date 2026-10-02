# Stationary-response quotient degree escape for quitting games

## Status and output

This is a mathematical proof, not a new Lean-checked declaration. It gives a
raw-table existence criterion inside the full-matrix degree-+1 residual.
The concrete paired-matrix consequence allows **33 freely chosen nonsingleton
coordinates** and all four arbitrary signed own-singleton levels.

The proof uses a polynomial stationary-response map directly. No discount
limit, selected analytic germ, individual-root regularity, or presumed
strategy certificate is needed. The all-Continue zero has local degree equal
to an LCP degree; the full map has degree +1. A mismatch forces an absorbing
stationary Nash–Bellman root. Complete behavioral deviations, including a
negative sole owner's Never response, are handled separately.

Whole-table symmetry is sufficient but unnecessary. Only equality of the
relevant unilateral stationary-response residuals on the chosen hazard
subspace is required. In the paired example, the other two players' entire
nonsingleton payoff rows remain unrestricted.

## 1. Definitions and statements

Let I be finite and nonempty. The first nonempty simultaneous quitting
coalition S receives r(S) in R^I; live play and Never pay zero. Randomization
is independent and private. Complete behavioral replacements are allowed.
Write

    s_i = r_i({i}),       Gamma_ij = r_i({j}) - s_i.

For stationary product hazards q, let the opponents' quitting-set law be the
ordinary independent product law, and define

    alpha_i(q) = product_{j!=i}(1-q_j),
    Q_i(q) = expected r_i(T union {i}) over the opponent Quit set T,
    H_i(q) = expected r_i(T) over nonempty opponent Quit sets T,
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

For a real square matrix A put f_b(x)=min(x,A x+b), coordinatewise on the
whole ambient space. Its zeros are exactly LCP(A,b). A is R0 if LCP(A,0)
has only zero as a solution. For R0 A, kappa(A) is its integer Brouwer LCP
degree, using the same convention as the attached integer-degree manuscript.

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

### Counterexample-facing form and inverse test

Every hypothetical Fin4 counterexample satisfies, for every partition
obeying the raw identity (RI),

    A is R0,                      kappa(A)=+1.                 (4)

In particular this applies to every player-orbit partition of every subgroup
of the full reward-table automorphism group. The discrete partition recovers
the prior full-matrix condition. A useful direct Fin4 corollary is

    (RI),       det A<0,       A^{-1}>=0   ==>   UE(r).         (5)

Zero inverse entries are allowed: first obtain R0 under no UE, then compute
the degree. Strict inverse positivity already implies R0 directly.

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

It is R0 and has degree -1. Indeed strict inverse positivity makes any
nonzero homogeneous complementary solution impossible, and LCP(A,-1) has
unique positive solution A^{-1}1=1, of index sign det A=-1.

In contrast,

    det Gamma=45,
    Gamma^{-1}=(1/15) [2 7 3 3
                        7 2 3 3
                        3 3 2 7
                        3 3 7 2] >0.                         (9)

The same argument gives full R0 and kappa(Gamma)=+1. Thus this corollary
operates inside the old full-degree-one residual. Restricting to q_0=q_1
removes one of the two negative within-pair modes; the quotient determinant
has the opposite sign.

Whole-table symmetry under p is one special case of (7), when s_0=s_1 and
the other recipients' rows are also symmetric. But changing only
r_2({0,2}) to any real number preserves the new class and generally destroys
that whole-table symmetry. This exhibits why the residual-map condition is
strictly weaker.

The attached paired one-parameter collision family is not in this class:
its {0,2} and {1,2} entries for recipients 0 and 1 violate (7). Its
simultaneous swap (0 1)(2 3) instead gives quotient [3,-2;-2,3] with degree
+1. Neither arbitrary completions of (6) nor that entire different cylinder
are claimed covered.

## 3. Classical degree facts used

For R0 A, the map f_0(x)=min(x,A x) has no nonzero zero on the whole R^k.
It is continuous and positively homogeneous. Therefore

    c_A = min_{||x||_infinity=1} ||f_0(x)||_infinity >0,
    ||f_0(x)||_infinity >= c_A ||x||_infinity.                 (10)

The integer degree on any sufficiently small neighborhood of zero is
kappa(A). For completeness, the same degree may be computed at any right-hand
side b: LCP solutions are uniformly bounded for b in bounded sets, by
normalizing a proposed unbounded solution sequence to a nonzero homogeneous
solution. The right-hand-side homotopy on a sufficiently large box and
excision give independence of b. At a strictly complementary nonsingular
support S, the local index is sign det A_SS.

The proof uses integer-degree normalization, homotopy invariance, stability
under uniform boundary-small perturbations, excision and additivity. A primary
source for these conventions is M. S. Gowda, “Applications of Degree Theory to
Linear Complementarity Problems,” Mathematics of Operations Research 18(4),
1993, Section 2, printed pages 869-870. Mod-2 degree cannot distinguish the
values +1 and -1 used here.

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
Their first opponent-quit clocks have geometric tails. Against every
complete deviation, terminal and finite-average payoffs differ by a quantity
bounded by a fixed constant divided by the horizon. Thus the same stationary
profile is uniform at v.

If some alpha_i=1, positive joint absorption forces i to be the unique
active player. Its fixed-point value is s_i and its complete cap is
max(s_i,0). Such an i must be a singleton block. If s_i>=0, its cap is
already correct. Its deviations have nonnegative sole-quitting rewards,
so delaying their payment cannot improve their average over the terminal
cap; prescribed averages tend to s_i. Outsider clocks still contract.
This proves the first assertion of Theorem B.

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

Taking K large and epsilon small produces actual terminal approximate Nash
profiles tending to the one fixed target v. The tracked terminal-target
consumer gives ordinary UE. No cap attainment is used in choosing the
punishment plan.

For signed Fin4, assume no UE. The tracked same-table hard-residual theorem
supplies mu_i<=s_i for all four players. Apply Theorem A and the preceding
complete-response construction to contradict no UE. This proves the signed
raw criterion in Theorem B.

## 6. The counterexample-facing and inverse consequences

The full homogeneous-normal consumer already excludes a nonzero homogeneous
complementary vector of Gamma under no Fin4 UE. If x is one for A, its
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

Every full reward-table automorphism group gives a special case of (RI):
its unilateral endpoints and survival products agree along player orbits at
orbit-constant hazards. Thus every subgroup's quotient can be tested. Testing
only the largest symmetry group can lose information: its coarser quotient
may have degree +1 even when a subgroup's quotient has degree -1.

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

### 7.3 Bounded comparisons with the supplied raw gates

The fixture has no pure terminal equilibrium. In coalition order
0,1,01,2,02,12,012,3,03,13,013,23,023,123,0123, profitable membership
moves can be made by players

    3,3,0,0,2,2,0,0,2,2,0,3,0,1,0,

with gains respectively

    3,3,2,1,1,1,3,1,3,3,2,5,4,4,1.

All-Never admits a gain of one. Leaving moves in this list retain a nonempty
coalition, so arbitrary hidden later deterministic clocks do not repair them.

The product-low test fails at pure coalition 01: both active quitters get
2>1. At equal small positive stationary hazards, the prescribed payoff
converges to the singleton average (5/4,...,5/4). Thus all the listed
payoff-exclusion tests fail as well.

Every triple of (6) has a negative entry in its inverse, so the
inverse-nonnegative-child row criterion fails. Reciprocal singleton gaps
have the same strict sign on every pair; the named escort condition has no
edges, ruling out balanced singleton cycles of every length by the
attachment's existing escort necessity. The cross principal on {0,2} is
[0,-1;-1,0], which is neither standard Q nor homogeneously feasible;
therefore the full principal-Q-bar test fails. Full det Gamma=45 also
fails the old negative-determinant inverse criterion.

All four capped-clock quiet-deletion LPs fail even with their Never row
omitted. Here are exact Farkas contradictions for the F and J rows in the
attached compiler:

* Delete 0. Take F rows at {3},{1,3},{2,3} with weights 4/9,1,2/9.
  The combined child coefficient row, in order (1,2,3), is (0,0,-14/9),
  while the combined outside lower bound is 1.
* Delete 1. Apply the transposition to the same certificate.
* Delete 2. The J row at {0,3} has child coefficients (0,-2,0) in
  order (0,1,3), and outside bound 3.
* Delete 3. The J row at {0} has child coefficients (0,-2,-1) in
  order (0,1,2), and outside bound 3.

These separate specific raw hypotheses. They do not say a supplied stationary
witness would fail the existing stationary verifier; (20) is precisely that
verifier's semantic interface. Nor is a worldwide priority claim made.

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

All displayed nonempty membership-toggle gains, F and J deletion-LP rows,
and singleton comparison matrices are unchanged by this operation. The
product-low failure at coalition 01 becomes rewards 2>1 and 1>0 for its two
active owners. Equal small positive stationary hazards still give strictly
positive surplus above every own singleton. Thus the separation checks also
hold in canonical single-pivot form. Dividing every terminal entry of this
second table by four gives a literal table in [-1,1], with singleton vector
(1/4,0,0,0); its same strategy has payoff v^can/4.

## 8. Source correspondence and implementation boundary

The following existing interfaces were read or identified in the supplied
source inventory:

* `nonempty_finFourQuantitativeFullSupportHardResidual_of_no_uniformPayoff`
  (`UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/FullSupportProjectiveQBarResidual.lean`)
  produces the same-table `all_punishmentNormal` field. Its declaration and
  hypotheses were fetched in this turn.
* `exists_uniformEquilibriumPayoff_of_homogeneous_supported_normal`
  (`UniformEquilibrium/Quitting/Classification/LCP/HomogeneousProductionNormalDispatch.lean`)
  consumes the normalized full homogeneous witness in Section 6. Its exact
  support-normality premise was fetched in this turn.
* `quittingStationaryFullRateUnilateralCap_le_of_fixedPoint_endpointNash`,
  `IsQuittingStationaryBoundaryAdmissible`, and
  `isZeroAsymptoticNash_stationary_iff_endpointNash_and_boundary`
  (`UniformEquilibrium/Quitting/Stationary/EndpointCompiler.lean`)
  give the full-cap and sole-owner interfaces of Section 5. This source was
  fetched in this turn.
* `quittingGame_isUniformEquilibriumPayoff_of_terminalNash_tendsto`
  (`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`)
  consumes the signed sole-owner approximants with one fixed target.

The attached integer-degree manuscript supplies the prior full-matrix
criterion and degree conventions. The additional mathematical content is the
raw response-invariant partition and quotient criterion, the 33-coordinate
paired completion class, and the exact example. The direct stationary-map
argument also removes the discounted-localization and curve-selection steps
from this proof.

A narrow Lean implementation would need:

1. the stationary residual Delta and its complete endpoint identity;
2. the raw partition identity, quotient matrix and Gamma E=E A;
3. the clipped stationary map and its full-individual-Nash adapter;
4. R0's quantitative homogeneous bound and local degree at all Continue;
5. global-minus-local integer degree and the existing behavioral consumers;
6. the paired raw adapter and exact rational example.

Integer degree remains a classical mathematical input not formalized here.
The new theorem was not compiled, axiom-audited, committed, or published to a
repository branch in this turn. The accompanying exact Python checker covers
the finite identities and fixtures; it is not a formal proof of the degree or
infinite-game theorems.

## 9. Scope

This closes a raw-table part of the degree-one residual, with a producer
rather than an assumed strategy certificate. It does not prove or refute
arbitrary Fin4 UE. A general table may admit no nondiscrete partition obeying
(RI), in which case the criterion reduces to the old full-matrix test.

No symmetry is manufactured by averaging games. The quotient is not treated
as a smaller-player quitting game, and block members do not share a random
coin. The paired raw condition concerns only the two specified centered
recipient rows, not an arbitrary completion of their singleton matrix.

For arbitrary finite player counts, Theorem A and the stated complete-cap
conditions remain valid. They do not supply a cardinal reduction to four or
an arbitrary-game producer.
