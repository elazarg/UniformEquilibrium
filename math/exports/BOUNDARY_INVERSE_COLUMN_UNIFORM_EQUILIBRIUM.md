# Boundary inverse columns produce stationary uniform equilibria

This is ordinary mathematics, not a Lean-checked theorem. It extends the
strict-column large-reward producer to explicit weak-column boundary faces.
The unrestricted Fin4 conjecture remains open.

## 1. Raw theorem

Let I be finite with at least two players. A nonempty first-quitting coalition
D pays r(D) in R^I. Live dates and perpetual continuation pay zero. Players
use private independent behavioral randomization. Deviations replace any one
player's complete behavioral law, including Never.

Fix all singleton rewards and define

    s_i=r_i({i}), Gamma_ii=0, Gamma_ij=r_i({j})-s_i (j!=i),
    Z_i(D)=r_i(D)-s_i for every nonempty D.

The last expression is only notation for finite-coalition reward differences;
live and Never rewards remain zero throughout the proof.

Assume Gamma is invertible. Choose a recipient a and sigma in {-1,1}, and put

    v=sigma Gamma^{-1} e_a, S={i:v_i>0}, T={i:v_i=0}.

Assume v>=0. If T is nonempty, require the principal inverse block

    M=(Gamma^{-1})_{TT}

to be invertible, and require B=M^{-1} to be strictly semimonotone, meaning
that for every nonzero x>=0, some i satisfies x_i(Bx)_i>0. This is a condition
on the singleton matrix alone, not a supplied strategic witness. One finite
sufficient test is that M be a P-matrix: every nonempty principal minor of M
is strictly positive. No entrywise sign condition is imposed away from the
diagonal. The empty-block convention includes the strict-column case.
Choose a coalition D* containing a with |D*|=d+1>=2 and

    P(v)>0, P(z)=(sum_{j!=a} z_j) product_{j in D*\{a}} z_j.

Choose A>0. For every finite R>=0 there is L0 such that, for every L>L0,
EVERY raw table satisfying the fixed singleton rows and

    r_a(D*)=sigma A L+c, |c|<=R,
    |r_i(D)|<=R at every other nonsingleton coordinate,

has an exact terminal Nash equilibrium against unrestricted behavioral
replacements. The equilibrium is stationary, every hazard is below one, and
at least two hazards are positive. Its actual terminal payoff is a uniform-
equilibrium payoff, with the same profile working at every accuracy.

Writing t=L^{-1/d}, the produced hazards obey

    q=t z, z_S=rho v_S+O(t), z_T>=0, z_T=O(t),
    rho=(A P(v))^{-1/d}.

All constants are uniform over the bounded residual box. Thus omitted-label
hazards are O(t^2), while each positive-column-label hazard has order t.
No continuity or uniqueness of the selected complementary root is claimed.

The theorem also has a scale-thick form: for fixed singleton data, A, a,
sigma,D*, some kappa>0 and L1 allow all residual nonsingleton coordinates,
including c, to range independently within +/-kappa L^{1/d}, for L>L1.
The O(t) error for z refers to bounded residuals at the fixed singleton
table, not to this thicker region.

Both conclusions hold uniformly on some open neighborhood of the original
singleton table: there are delta_0>0, kappa>0 and L1 such that every table
whose singleton entries differ from those of the base by at most delta_0,
whose nonsingleton residuals have absolute value at most kappa L^{1/d}, and
whose selected reward is sigma A L plus its residual, has the same type of
stationary equilibrium whenever L>L1. The perturbed singleton matrix need
not itself have a nonnegative selected inverse column. For bounded residuals
and singleton perturbation size delta, the produced z differs from the base
z* by O(t+delta); the O(t^2) omitted-hazard statement applies only at delta=0.

## 2. Elementary matrix facts

A P-matrix B has the sign-nonreversal property: for every nonzero x there
exists i with x_i(Bx)_i>0. For suppose all products were nonpositive. Let J
be the nonzero support of x and set E_ii=-(Bx)_i/x_i>=0 for i in J. Then
(B_JJ+E)x_J=0. However expansion of det(B_JJ+E) in its diagonal entries is
a sum of principal minors of B_JJ multiplied by products of E entries,
including the strictly positive term det B_JJ. The determinant is positive,
a contradiction.

The inverse of a P-matrix is P: for any principal index set J, the principal
minor of B^{-1} equals det B_{J^c,J^c}/det B, with the empty determinant one.
This identity follows from the Schur-complement determinant identity when
the complementary block is invertible; all such blocks of a P-matrix are.

If T is nonempty, the assumed M is invertible and therefore Gamma_SS is invertible.
Indeed, if Gamma_SS x_S=0, extend x by zero on T. Then Gamma x=(0_S,y_T),
so x_T=M y_T=0; invertibility of M gives y=0 and then x=0. If a were in T,
Gamma_SS v_S=0 would contradict this invertibility. Consequently a belongs
to S. Moreover S has at least three members. A singleton S would make Gamma_SS
zero. If S={a,b}, the equation in row b would give Gamma_ba v_a=0 and hence
Gamma_ba=0, again making Gamma_SS singular. The argument also applies when
T is empty, since Gamma itself is invertible. Thus in Fin4 a nonempty zero
set necessarily consists of one label h, and the matrix hypothesis is exactly
(Gamma^{-1})_hh>0. These facts ensure proper opponents in the final consumer.

## 3. Exact polynomial at the large-reward scale

For stationary opponent hazards q_-i define

    alpha_i=product_{j!=i}(1-q_j),
    Q_i=sum_{B subset I\{i}} Pr_q(B) r_i(B union {i}),
    C_i=sum_{nonempty B subset I\{i}} Pr_q(B) r_i(B),
    H_i(q)=(1-alpha_i)Q_i-C_i.

If at least one opponent is proper, the stationary continuer value is
C_i/(1-alpha_i); therefore H_i<=0 means that Quit is no better than Continue.

Set q=t z and L=t^{-d}. Direct finite polynomial expansion gives

    Phi(t,z,b)=H(tz)/t=sigma A P(z)e_a-Gamma z+t E(t,z,b),  (1)

where b denotes the bounded nonsingleton residuals and E is a polynomial in
all its arguments. In detail, the large selected contribution equals

    sigma A [1-product_{j!=a}(1-tz_j)]
       product_{j in D*\{a}} z_j product_{j notin D*}(1-tz_j),

before division by t. The bracket is divisible by t. Its constant divided
term is sigma A P(z). Bounded nonsingleton terms have degree at least two
in the undivided H, and singleton terms give exactly -t Gamma z at degree
one. This proves the cancellation without a limiting-payoff assumption.

At t=0, z*=rho v satisfies Phi=0 by homogeneity. Put g=grad P(z*). Its
Jacobian is

    J=sigma A e_a g^T-Gamma,
    det J=-d det(-Gamma)!=0,
    J^{-1}=-Gamma^{-1}+(A/d) v g^T Gamma^{-1}.       (2)

Indeed A g^T v=d+1 by Euler's identity and A P(z*)=rho. The determinant
lemma and direct multiplication yield (2).

In particular (J^{-1})_{TT}=-M. It follows that J_SS is invertible: extend
a hypothetical kernel vector by zero on T and apply J^{-1} just as in the
Gamma_SS argument of Section 2.

## 4. Positive-label equations and complementary omitted labels

For bounded b, the parameter implicit-function theorem solves the equations
Phi_S=0 uniquely near z*_S as

    z_S=psi(t,b,x), x=z_T,
    psi(0,b,0)=z*_S.

Uniformity over a compact b-box follows from the common derivative J_SS and
uniform polynomial derivative bounds (equivalently, one quantitative local
contraction). At t=0 the entire field is independent of b. Define

    f(t,b,x)=-Phi_T(t,psi(t,b,x),x).

This is defined on a common neighborhood of x=0 and satisfies

    f(0,b,0)=0,
    D_x f(0,b,0)=-(J_TT-J_TS J_SS^{-1}J_ST)=M^{-1}=:B.   (3)

The block-inverse identity proves the last equality using (J^{-1})_TT=-M.
The primary hypothesis says that B is strictly semimonotone; the finite
P-matrix test implies this by Section 2.

Here is a self-contained local complementarity existence argument. By strict
semimonotonicity and compactness, the number

    eta=min_{x>=0, ||x||_infty=1} max_i x_i(Bx)_i

is strictly positive. Choose a small fixed radius r so that psi stays
strictly positive on S, and, uniformly for all parameters under consideration,

    ||f(t,b,x)-f(t,b,0)-Bx||_infty <= (eta/4)||x||_infty

for 0<=x<=r. Also ||f(t,b,0)||_infty<=C t uniformly. For all sufficiently
small positive t arrange C t<eta r/4.

Apply Brouwer to the continuous map on [0,r]^T

    x -> clamp_{[0,r]}(x-f(t,b,x)).

At a fixed point, if 0<x_i<r then f_i=0, if x_i=0 then f_i>=0, and if x_i=r
then f_i<=0. In all cases x_i f_i<=0. If ||x||_infty=r, choose i with
x_i(Bx)_i>=eta r^2. The error bound gives

    x_i f_i >= eta r^2-r(Ct+eta r/4)>eta r^2/2>0,

a contradiction. Thus no coordinate is at the upper boundary, and the fixed
point satisfies

    x>=0, f>=0, x_i f_i=0.                            (4)

Using the same eta estimate at this solution shows

    (3 eta/4)||x||_infty <= C t,

unless x=0, where the desired O(t) bound is already true. The IFT then gives
psi(t,b,x)=z*_S+O(t). Equations (1),(3),(4) produce q>=0 with q_i<1,

    H_i(q)=0 if q_i>0; H_i(q)<=0 if q_i=0.             (5)

When T is empty, the ordinary full IFT yields (5) directly.

For the scale-thick version, write every residual b_j=e_j/t. The exact field
(1) extends polynomially in (t,z,e), because each bounded nonsingleton
monomial in H/t has degree at least one in t before substituting e/t. For
the selected residual the least exponent is d-1>=0. At (t,e)=(0,0) the root
and derivative are the same. The preceding local IFT and Brouwer argument
apply whenever t and all |e_j| are sufficiently small; now f(t,e,0)=O(t+|e|).
Choose one kappa inside that common parameter neighborhood. Positive-label
hazards remain positive, regardless of which omitted labels activate.

Finally treat every raw singleton perturbation as an additional parameter
delta. The field remains polynomial in (t,z,e,delta), with the same base root
and Jacobian at (0,0,0). The reduced derivative stays close to B and
f(t,e,delta,0)=O(t+|e|+|delta|). The same fixed cube and strict boundary
estimate therefore apply on one common small parameter box. This proves
the open-singleton-neighborhood assertion without presuming positivity of
any perturbed inverse column. It also gives z-z*=O(t+|e|+|delta|); for bounded
residuals, e=t b, giving the stated O(t+delta) estimate.

## 5. Complete behavioral and uniform-payoff consumer

The support S has at least two members, so every player has a proper opponent.
Fix the produced table and profile. Let U_i be its actual terminal value.
First-step evaluation gives

    U_i=[q_i Q_i+(1-q_i)C_i]/[1-(1-q_i)alpha_i].

If q_i>0, (5) gives C_i=(1-alpha_i)Q_i, so U_i=Q_i and the Continue endpoint
C_i+alpha_i U_i equals U_i. If q_i=0, U_i=C_i/(1-alpha_i) and (5) gives
Q_i<=U_i. Hence each pure endpoint against continuation U_i is at most U_i,
and every endpoint prescribed with positive probability equals U_i.

Iterating these one-stage inequalities against any complete behavioral
replacement bounds its truncated expected payoff by U_i, up to a terminal
remainder tending to zero. The remainder vanishes uniformly over replacements:
the opponents' probability of continuing through N dates is alpha_i^N,
independently of the deviator's actions. Thus the profile is exact terminal
Nash against all behavioral deviations, not merely stationary deviations.

If R_table bounds all rewards of this fixed finite table, the absorption time
under every deviation is bounded by the first opponent Quit and has expectation
at most 1/(1-alpha_i). Consequently terminal and finite-average payoffs differ
uniformly by at most 2 R_table/[N(1-alpha_i)] (an endpoint convention can only
improve this safe bound). The same stationary profile and the fixed actual
terminal target U therefore satisfy the uniform-equilibrium contract.

## 6. Explicit Fin4 application

For the fixed comparison matrix

    Gamma=[0,3,-1,3; 2,0,1,-3; 2,-2,0,-1; -1,-2,1,0],
    Gamma^{-1}=(1/25)[8,5,9,3; 3,5,-6,-2;
                              14,15,-3,24; 10,0,5,10],

choose a=1, sigma=+1, D*={1,2}, A=1. Then

    v=(1,1,3,0)/5, S={0,1,2}, T={3}, M=2/5,
    P(v)=12/25, rho=25/12,
    z*=(5/12,5/12,5/4,0), B=M^{-1}=5/2.

Thus for every finite box of ALL other nonsingleton rewards, every sufficiently
large positive reward r_1(12) produces an exact stationary terminal equilibrium
and a same-profile fixed UE target. In the original own-singleton-zero notation
this is a=Z_1(12)->+infinity, with p=Z_2(12) and all other collision rewards
bounded independently. For a fixed bounded completion,

    q_0=5/(12a)+O(a^{-2}), q_1=5/(12a)+O(a^{-2}),
    q_2=5/(4a)+O(a^{-2}), q_3>=0, q_3=O(a^{-2}).

The scalar reduced H-field derivative is -5/2, so if its value at x=0 is
nonpositive, player 3 stays quiet; otherwise a small positive hazard restores
indifference. This covers both possible perturbation signs without assuming
that a full interior root remains nonnegative.

For an explicit matrix in the robust neighborhood, increase Gamma_30 by
epsilon>0 and keep every other entry fixed. Direct inversion gives

    (Gamma_epsilon^{-1} e_1)_3=-2 epsilon/(25+3 epsilon)<0.

The first three coordinates remain positive for sufficiently small epsilon.
The neighborhood theorem still produces stationary UE for all sufficiently
large selected rewards and all the stated bounded or scale-thick completions.
Thus the robustness assertion includes actual mixed-sign selected inverse
columns; it is not an application of the base weak-column premise to them.

## 7. Exact boundary controls

These tests concern the local mechanism, not new coverage witnesses. Use the
Gamma in Section 6, own singleton zero, and set every nonsingleton reward to
zero except r_1(12)=a and the passive entry r_3(02)=b. Put t=1/a. With z* as
in Section 6, the coefficient of t in Phi(t,z*,b) is exactly

    E=(25/24,25/576,0,-25b/48-25/24).

Solving the active equations at z_3=0 gives the first correction

    z_{012}=z*_{012}+t(25/64,25/64,25/192)+O(t^2).

The remaining Phi_3 value is -25b t/48+O(t^2), and its reduced derivative
is -5/2. Therefore b=+1 selects the quiet branch for small t; b=-1 requires
and produces an active fourth hazard q_3=5t^2/24+O(t^3). This explicitly
checks both possible signs of the bounded-completion perturbation.

For an exact finite positive test, take a=200/39 and b=1 in this same table.
The hazard vector q=(1/10,1/10,1/4,0) has actual terminal target
(0,15/13,0,9/157). Its endpoint fields satisfy H_0=H_1=H_2=0 and H_3<0.
More generally q=(x,x,3x/(1+2x),0) gives H_0=H_2=0 and

    H_1=x(x-1)(3ax^2-12ax+10x+5)/(1+2x)^2,
    H_3=-3b x^2(1-x)/(1+2x).

Thus choosing a=5(2x+1)/[3x(4-x)] for 0<x<1 and b>=0 makes it an exact
terminal equilibrium by Section 5. This is a mechanism calibration, not a
separating new-coverage example.

For a negative sign control, replace Gamma by

    Gamma'=Gamma diag(1,1,1,-1).

The nonnegative column v and z* are unchanged, but the principal inverse
entry is now M=-2/5 and the reduced Phi_3 derivative is +5/2. Keep the same
collision completion and choose b=-1. At z_3=0 the reduced field is again
25t/48+O(t^2)>0. It is strictly increasing in z_3 throughout a common small
neighborhood. Thus no z_3>=0 in that neighborhood satisfies the required
Phi_3<=0, and no nearby complementary stationary root exists for small t.
The unrestricted weak-column perturbation argument therefore fails without
a condition controlling this sign. This does not claim that the altered
game has no other equilibrium or no UE.

## 8. Exact four-player coverage family

This is a family of four-player original reward tables, with live and Never
payoffs zero. All own singleton rewards are4. The selected growing entry is
r1(12)=M. The complete table is

| D | r0 | r1 | r2 | r3 |
|---|---:|---:|---:|---:|
| 0 | 4 | 6 | 6 | 3 |
| 1 | 7 | 4 | 2 | 2 |
| 2 | 3 | 5 | 4 | 5 |
| 3 | 7 | 1 | 3 | 4 |
| 01 | -1 | -1 | 4 | 4 |
| 02 | -1 | 4 | 26 | 4 |
| 03 | 27 | 4 | 4 | -1 |
| 12 | 4 | M | -1 | 4 |
| 13 | 4 | -1 | 4 | 22 |
| 23 | 4 | 4 | -1 | -1 |
| 012 | -1 | -1 | -1 | 4 |
| 013 | -1 | -1 | 4 | -1 |
| 023 | -1 | 4 | -1 | -1 |
| 123 | 4 | -1 | -1 | -1 |
| 0123 | -1 | -1 | -1 | -1 |

Thus every nonselected reward is bounded in absolute value by27. The
comparison matrix and inverse are

    Gamma=[0,3,-1,3; 2,0,1,-3; 2,-2,0,-1; -1,-2,1,0],
    Gamma^-1=(1/25)[8,5,9,3;3,5,-6,-2;14,15,-3,24;10,0,5,10].

Column1 is v=(1,1,3,0)/5. Its zero set is{3}; the omitted principal inverse
entry is2/5>0, so the boundary-jackpot theorem applies. For S*=12,
P(v)=12/25, d=1. Therefore as M tends to infinity there is a stationary
full behavioral terminal Nash with

    (q0,q1,q2)=(5/12,5/12,5/4)/M+O(1/M^2), q3=O(1/M^2), q3>=0.

Its actual terminal target tends to(4,21/4,4,4) across this family, though
for each fixed sufficiently large M the theorem supplies its own fixed
uniform-equilibrium target. This is not a common target assertion across
changing games.

### 8.1 Complete sure-owner exclusion

Let successor be the four-cycle0->2->1->3->0. For each i its pair with its
successor pays i=-1 and its successor the singleton payoff at i plus20,
except that at i=2 the successor1 receives M. All other pair participants
and all triple/grand participants receive-1. Every nonparticipant reward,
including singleton rewards, is at least1. Assume M>14.

Suppose a product root has a sure owner i and is Nash against ANY
continuation payoff vector. Every nonsuccessor j of i must Continue:
whenever j joins i, its reward is-1, whereas continuing receives at least1
since i quits surely. Thus only i and successor(i) can quit. The successor
strictly prefers Quit, by20 if i!=2 and by M-5>0 if i=2, so quits surely.
Owner i then receives-1 but can obtain its positive singleton payoff at
successor(i) by Continue. Contradiction. Continuation values do not enter
any comparison once an opponent is sure.

This excludes every sure-root support, every sure-owner continuation
selection, and every persistent-base source requiring such a root, for
ALL M>14.

### 8.2 Every proper child has an unsafe exact equilibrium

For every proper nonempty child C, choose d in C whose successor lies
outside C. Such d exists by the directed cycle. In the child let only d
Quit0 surely and every other child player Never. Each other child player
is a nonsuccessor of d, so obtains a singleton payoff at least1, compared
with joining payoff-1. Later quitting does not improve an already absorbed
outcome. Player d receives its own singleton4, compared with Never0.
Thus this is a full behavioral exact child Nash with zero child debt and
zero joint Never mass. The absent successor gains20 if d!=2 and M-5>0 if d=2 by Quit0.
Hence every proper child fails every raw certificate whose conclusion
bounds outsider gain by child debts plus bounded joint-Never slack. The selected pair is precisely one of these unsafe incoming-cycle entries.

### 8.3 Ordered anchors and weighted upper averages

The positive singleton graph of Gamma is strongly connected. Consequently
any closed marked set required by the ordered-anchor producer is all four
players. Consider its first nonempty block B. If successor(i) belongs to B
but i does not, coalition{i,successor(i)} first meets B only at its
successor, whose native participant reward is strictly positive. The
required nonpositive weighted sum fails. Thus B must be predecessor-closed
under the full cycle, so B=I. If positive weights w worked on this block,
the four pair inequalities would require

    22 w2<=5w0, (M-4) w1<=5w2, 18 w3<=5w1, 23 w0<=5w3.

Multiplying gives22*(M-4)*18*23<=5^4, a contradiction for M>14. This excludes every
block partition, order and choice of positive weights, not merely equal
weights.

For every nonzero nonnegative weight vector w, the sum of supportwise
forced-Quit native upper averages on the four singleton coalitions is

    13w0+(M-14)w1+12w2+8w3>0.

Each recipient has one incoming-cycle joining premium, respectively
23,M-4,22,18, and two other joining premiums-5. Thus no such weight can make
all these four averages nonpositive. Also the only premium trap is the full
set: a strict participant premium for0 requires3, for3 requires1, for1
requires2, and for2 requires0. Therefore the full-trap singleton upper
charge criterion fails too.

### 8.4 Exact singleton degree and full support census

Every singleton column of Gamma has a negative entry. The principal pair
determinants, in order 01,02,03,12,13,23, are

    -6,2,3,2,-6,1.

The principal triple determinants, in order 012,013,023,123, are10,-3,5,8;
the full determinant is25. Hence Gamma is R0: a nonzero homogeneous
complementary vector cannot have support of size at least two because that
principal block is invertible, and cannot have singleton support because
the corresponding column has a negative entry.

At standard-LCP offset (1,1,1,1), an active support C of size at least two
has the sole possible positive vector z_C=-Gamma_CC^{-1}1. The complete
list is

| C | z_C | reason for exclusion |
|---|---|---|
| 01 | (-1/2,-1/3) | negative active coordinate |
| 02 | (-1/2,1) | negative active coordinate |
| 03 | (1,-1/3) | negative active coordinate |
| 12 | (1/2,-1) | negative active coordinate |
| 13 | (1/2,1/3) | omitted row2 residual -1/3 |
| 23 | (-1,1) | negative active coordinate |
| 012 | (-7/10,-1/5,2/5) | negative active coordinate |
| 013 | (-7,4,-13/3) | negative active coordinate |
| 023 | (-1,-2,-1) | negative active coordinate |
| 123 | (3/8,-1/4,1/4) | negative active coordinate |
| 0123 | (-1,0,-2,-1) | negative active coordinate |

A singleton support cannot solve its diagonal-zero active equation at this
positive offset. Thus the empty support is the only standard-LCP root; its
residual is strictly positive and its local index is+1. The standard support
index formula therefore gives actual R0 degree+1. In particular the existing
nonunit-singleton-degree producer does not cover this family. The support
index is the sign of the active principal determinant, with the empty
determinant equal to1; no extra factor depending on support size is used.

### 8.5 Other concrete producer comparisons

The signed single-column jackpot producer with strict column positivity
does not cover the displayed growing direction: recipient1 has the zero
coordinate v3, and its opposite signed column is nonpositive. The only
strictly positive column is column0, but no recipient0 reward grows.
This is an extension of its missing boundary case, not a counterexample to
its theorem. All-column signed-inverse producers fail because column2 has
both positive and negative entries. The passive-pole producers require a
large reward to a nonparticipant; the only growing coordinate here pays
a participant.

For every ordered recipient/partner pair(i,p), choose a player j different
from i,p and predecessor(i). Such j exists among four players. Its pair
joining native payoff for i is-5, while Gamma_ij>=-3. Hence the necessary
zero-partner lower endpoint difference is at most-2. This excludes all
partner choices for the crossed-face guard requiring that lower face.

The unique mutually positive singleton pair is01 and the unique mutually
negative pair is13. They intersect. Thus the signed-four-cycle templates
requiring disjoint such pairs fail under every relabeling. The only principal
triple with nonnegative inverse is023; its outside inverse row is
(-3,6,2)/5. Hence the full nonnegative-child/passive-inverse selector fails.
For the three pair partitions 01|23,02|13,03|12, a mandatory joining
increment Z_i({i,mate})-Gamma_i,mate is respectively -8 at recipient0, -4
at recipient0, and -4 at recipient3. Thus all partitions fail the nonnegative
joining-increment requirement of the two-pair cone producers. The unique
mutually negative pair is13. The only compatible attached-negative-pair
labeling is (3,1,0,2); its required nonnegative participant premium fails at
Z_1(13)=-5. The alternative allowing both attached participant premiums still
requires the positive singleton comparison m=Gamma_21, which here is-2.

These are comparisons with the specified complete source selections, not a
claim about every conceivable sufficient equilibrium theorem.

## 9. Source correspondence, actual-data adapter, and scope

Inspected exact semantic declarations:

- quittingUniformEquilibriumPayoffConjecture in
  UniformEquilibrium/Quitting/Conjecture/Basic.lean;
- exists_finset_r0Degree_eq_sum_sign_det in
  MathUE/LinearProgramming/R0DegreeSum.lean, whose support-index convention
  and actual-root census match Section 8.4;
- isZeroAsymptoticNash_stationary_of_fixedPoint_endpointNash_contracts and
  isUniformEquilibriumPayoff_of_stationaryEndpointCertificate_contracts in
  UniformEquilibrium/Quitting/Stationary/EndpointCompiler.lean.

The strict-column large-reward hypothesis requires every coordinate of the
signed selected inverse column to be positive. A zero coordinate is outside
that hypothesis. Sections 2-4 address it by a raw matrix condition and
complementary activation; the neighborhood extension also permits nearby
mixed-sign selected columns. No interior root or threshold transferred from
nearby strict columns is assumed. The full-positive-inverse and signed-all-
column hypotheses likewise do not directly supply this construction.

The actual-data inputs are singleton rewards, one recipient and containing
coalition, a signed nonnegative inverse column, the displayed finite matrix
condition, the pole magnitude, and bounds on the other original rewards.
Sections 3-4 produce actual hazards from these inputs; no continuation,
strategic root, or target is supplied. Section 5 converts those hazards into
a fixed actual terminal target and bounds every behavioral deviation.

The counterexample restriction is that every sufficiently large table in
this boundary-column region has UE. Section 8 compares a whole explicit ray
with the stated complete producer selections. It does not assert exclusion
from every unspecified implicit-function neighborhood. The theorem does
not imply that every weak column satisfies the matrix condition or that an
arbitrary fixed game can be changed into a large-pole game. In particular
it does not settle the negative-a central wedge or the actual subcritical
global-minimum problem.
