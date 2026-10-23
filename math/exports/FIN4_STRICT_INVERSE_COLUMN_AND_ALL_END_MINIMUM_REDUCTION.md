# Strict inverse columns and all-END original minima in four-player quitting games

## Exact statement and conjecture-facing change

A four-player quitting game assigns a finite real payoff vector r(C) to
each nonempty coalition C. At every live date, players independently choose
Continue or Quit using private behavioral randomization. The first nonempty
quitting coalition absorbs at its payoff, received thereafter. All live
rewards and literal Never rewards are zero. Every unilateral behavioral
replacement is allowed, including arbitrary stopping laws and Never.
A uniform-equilibrium payoff is ONE fixed target before accuracy: for each
positive accuracy there is one profile and one horizon threshold that
deliver that target and cap every unilateral improvement at every larger
finite horizon.

This packet proves three linked conclusions.

1. For the literal singleton comparison matrix
   Gamma_ii=0 and Gamma_ij=r_i({j})-r_i({i}), original no UE implies
   det Gamma>0 and a STRICTLY positive column of Gamma inverse.
   No genericity or supplied matrix witness is assumed.
2. For EVERY fixed own-zero native table Z with a positive absorbing
   full-SUM debt infimum A, its literal Gamma has such a strict column.
   No perturbation of Z is needed.
3. From that same native table one can choose a fixed compact positive
   recipient-weight box K with nonempty interior, and t0>0, such that for
   EVERY theta in K, EVERY 0<t<t0, and EVERY original full-SUM global minimum
   at r_i(C)=theta_i[Z_i(C)+t], all four native END caps are active.
   Every ORIGINAL marginal Never mass is bounded below by one fixed c>0.

The third statement has no small-total-finite-mass, future-owner count,
ROOT support, calendar, tie-pattern, cap-attainment, or clock-representation
hypothesis. The weights are chosen before t and before every minimum.
An END-active native cap equals the native pure-Never response, equivalently
the limit of late finite native responses. In the raised table, this gives
the late FINITE cap; literal Never keeps its original zero reward on the
all-Never event and is not silently identified with that cap.

The complete source from an arbitrary hypothetical signed Fin4 counterexample
is included: implemented single-pivot normalization produces a native table
with A>0, the strict-column theorem applies to THAT table, and the fixed
weight box produces positive original minima with all ENDs active. Therefore
a universal consumer of this all-END source would settle the original
conjecture. Such a consumer is NOT proved here.

The new matrix boundary reduction is stronger than requiring a nonnegative
inverse column. The new minimum reduction supplies all-END activity without
the small-mass or at-most-two-future premises of earlier source reductions.
Its matrix proof intentionally uses degree, singleton-sign and passive-child
UE exits; no excluded table is claimed to lie outside their combined
sufficient coverage. Its new source consequence is the complete production
of the all-END minimum hypothesis from the actual counterexample source.

## Proof organization and strategic inputs

Part I proves strict-column necessity, including a finite-dimensional
separation argument and literal original-reward perturbation. Part II
produces the strict column from every fixed positive native absorbing gap
and proves the full original minimum conclusion by explicit finite-word
competitors. Part III supplies the arbitrary-original-game normalization
adapter, boundary controls and implementation handoff. Part IV contains the
complete nonnegative-column prerequisite proof, its singleton-sign
classification and its exact checker. The other complete checkers are in
Part V.

Section and formula numbers inside each proof part are LOCAL to that part.
In particular, references to Sections 1--9 or Appendix A inside Part IV
refer to its own prerequisite proof, not to the preceding parts.

No strategic object is assumed. Compact minima exist in the original
augmented semantic carrier. Native Never values and ORIGINAL Never masses
are retained explicitly. Every new graft is constructed through actual
finite-prefix realizers and prices the entire unilateral response menu.
The separation direction, inverse column, weight box, finite-word directions
and perturbations are all produced from the stated finite data or from
the already supplied positive-gap source. No public correlation device,
unrestricted invariance under terminal-only payoff shifts, or selected
successful equilibrium continuation is used.

## Part I. Strict inverse-column necessity

### 1. A simultaneous diagonal-preserving tangent lemma

Let G be an invertible real n-by-n matrix, B=G^(-1), and

    J={j: B e_j>=0 entrywise}.

Assume B_jj>0 for every j in J. Define the finite zero set

    Z={(i,j): j in J and B_ij=0}.

There is a real matrix H with H_ii=0 for every i such that

    (B H B)_ij>0 for every (i,j) in Z.                   (1)

No sign condition on G, no assumption that its diagonal vanishes, and no
condition on the other inverse columns is required. If Z is empty, H=0
satisfies the assertion.

#### Proof of the finite alternative used

For a finite collection of linear forms L_a on a finite-dimensional real
vector space E, either some h has every L_a(h)>0, or there are nonnegative
weights w_a, not all zero, with sum_a w_a L_a=0. To see the nontrivial
alternative, let V be the image of E under the map h |->(L_a(h))_a.
If V misses the open positive orthant, finite-dimensional separation of
that linear subspace from the open convex orthant gives a nonzero functional
w. Linearity of V forces w to annihilate V, and testing positive vectors with one
coordinate arbitrarily large forces w_a>=0. The alternatives cannot both
hold. This is the strict form of Gordan's alternative.

Apply this alternative to E={H:diag H=0} and
L_(i,j)(H)=(BHB)_ij for (i,j) in Z. If (1) failed, there would be a nonzero
matrix W>=0 supported on Z such that

    sum_(i,j) W_ij (BHB)_ij
       =trace(B W^T B H)=0 for every H with diag H=0.

Testing the off-diagonal matrix units implies

    B W^T B=D, with D diagonal.                         (2)

For j in J set a=W^T B e_j. The vector a is nonnegative, because
W>=0 and B e_j>=0, and a_k=0 for k outside J, because those columns of W
vanish. Equation(2) gives D e_j=B a.

For k in J with k!=j, the kth coordinate on the left is zero. On the
right every summand is nonnegative, because all columns of B indexed by
J are nonnegative. In particular

    0=(B a)_k>=B_kk a_k.

The strictly positive diagonal entry forces a_k=0. The remaining coordinate
vanishes for a different reason:

    a_j=sum_i W_ij B_ij=0,

because W is supported on zero entries of B. Thus a=0 and D_jj=0 for
every j in J.

Multiply (2) on the right by G to obtain B W^T=D G. Every row j in J
on the right is zero. On the left W^T has nonzero rows only in J, and
all corresponding columns of B are nonnegative. Therefore, for all k,

    0=(B W^T)_jk>=B_jj (W^T)_jk>=0.

Again B_jj>0 forces every row j in J of W^T to vanish. All other rows
already vanished, so W=0, a contradiction. This proves (1).

The argument produces ONE H for ALL zeros in ALL nonnegative columns.
It is not an argument that the interior of a finite union equals the
union of its interiors.

### 2. Two-sided removal of the inverse-column boundary

For the H in Section1, invertibility persists for sufficiently small |t|,
and entrywise differentiation of the inverse gives

    (G+tH)^(-1)=B-t BHB+o(t).                           (3)

There are finitely many entries in Z. If Z is nonempty, let
m=min_((i,j) in Z)(BHB)_ij>0. For all sufficiently small t>0, every such
entry in (G+tH)^(-1) is less than -tm/2. Every originally strictly negative
entry of B remains negative after further decreasing the bound on t.
Similarly, every originally strictly positive entry in a column in J
remains positive in (G-tH)^(-1), and its zero entries become positive.
Consequently:

1. If no column of B is strictly positive, every column of
   (G+tH)^(-1) has a negative entry for all sufficiently small t>0.
   A column in J acquires one from Z; a column outside J already had one.
2. For all sufficiently small t>0, every column in J of
   (G-tH)^(-1) is strictly positive.

If J is empty, the first conclusion already holds near G by continuity.
If a column in J was strictly positive, the first conclusion is not asserted;
the second still holds. The diagonal of G+tH equals that of G exactly, and
any strict determinant sign is preserved for sufficiently small |t|.

For an invertible R0 matrix the positive-pivot hypothesis is automatic.
Indeed, let v=G^(-1)e_j>=0. It is nonzero and Gv=e_j. If v_j=0, then
v>=0, Gv>=0 and v_i(Gv)_i=0 for every i, contradicting R0. Thus v_j>0.
This deduction does not require G to have zero diagonal.

It follows that any invertible R0 matrix with no strictly positive inverse
column is approximable, keeping its diagonal fixed, by invertible matrices
with a negative entry in EVERY inverse column. Neither R0 nor degree is
asserted to persist under this perturbation, and neither persistence is
needed in the application below.

### 3. The original Fin4 consequence

There are four players. Every nonempty first-quitter coalition S has finite
original reward r(S), absorbed thereafter. Live and literal Never pay zero.
The players use independent private randomization. A unilateral replacement
may be any complete behavioral strategy, including arbitrary stopping laws
and Never. Put

    s_i=r_i({i}),  G_ii=0,  G_ij=r_i({j})-s_i for i!=j.

**Theorem.** If this original game has no uniform-equilibrium payoff, then

    det G>0 and some column of G^(-1) is STRICTLY positive. (4)

Equivalently, every actual table with det G<=0 has UE; and every table with
det G>0 for which each inverse column has a nonpositive entry has UE.
The original own singleton levels and all nonsingleton rewards are arbitrary
signed finite data. No root, profile, period, continuation, or certificate
is an input. The UE payoff is one fixed target before accuracy and horizon.

The prerequisite proved completely in Part IV is the following:
original no UE implies det G>0 and at least one NONNEGATIVE inverse column.
Its complete analytic proof, including all singular boundaries, is included;
no assumption about generic matrices replaces the actual-game statement.

The same original no-UE hypothesis also gives R0, by
`finFour_singleton_r0Degree_eq_one_of_no_uniformPayoff` in
`UniformEquilibrium/Diagnostics/Quitting/FinFourSingletonDegreeCriterion.lean`.
The exact terminal characterization
`not_exists_uniformEquilibriumPayoff_iff_exists_terminalExploitabilityGap`
in `UniformEquilibrium/Quitting/Terminal/ExploitabilityGap.lean`
gives a positive terminal exploitability gap g>0 against EVERY behavioral
profile. Reward robustness gives an open neighborhood of original no-UE
tables, as follows directly.

For a fixed profile or fixed complete unilateral replacement, changing each
absorbing reward by at most delta changes its terminal expectation by at
most delta. The first-quitter law has total mass at most one, and the Never
reward stays zero. Every improvement changes by at most2delta. Taking the
supremum over all replacements preserves the bound, even when it is not
attained. Thus every table within delta<g/4 retains a positive exploitability
gap. This is also the exact content of
`abs_quittingTerminalExploitability_sub_le_of_reward_close` in
`UniformEquilibrium/Quitting/Terminal/TerminalExploitabilityRewardRobustness.lean`.

Suppose (4) failed at the original no-UE table. The reduction in Part IV gives
det G>0 and a nonempty set J of nonnegative inverse columns, none strictly
positive. R0 supplies their positive diagonal pivots. Choose the single H
from Section1. For every sufficiently small t>0, the inverse of G+tH has
a negative entry in every column.

Realize this perturbation in the ORIGINAL sixty reward coordinates by

    r(t)_i({j})=r_i({j})+t H_ij for i!=j,

keeping own singleton rewards, all nonsingleton rewards, live rewards and
Never unchanged. Its literal singleton matrix is exactly G+tH. Its reward
supremum distance is t max_(i!=j)|H_ij|. Choose t small enough to stay inside
the positive-gap neighborhood and the matrix neighborhood of Section2.
Then the very same perturbed original game has no UE but has no nonnegative
inverse column, contradicting the reduction in Part IV. This proves (4).

Equivalently, the boundary tables are limits of UE tables, and
`exists_uniformEquilibriumPayoff_of_arbitrarily_close_reward_tables` in
`UniformEquilibrium/Quitting/Terminal/TerminalExploitabilityRewardRobustness.lean`
supplies the fixed-target closure. The neighboring targets need not be
chosen continuously. No translation of live or Never payoffs, equilibrium
selection theorem, or degree-continuity premise is used.

## Part II. Every fixed native positive-gap source has all-END minima

### Strict column at the SAME native table

Let Z have own singleton zero and A>0 as defined below. The elementary
properification inequality proved in local Section 2 gives, for every actual
profile and its original joint Never probability nu,

    A <= D_Z+14M*nu^(1/4).

For R=Z+1 on nonempty coalitions, with live and Never still zero, the exact
full-cap identity gives D_R=D_Z+4nu. Put c=(A/(28M))^4. If D_Z>=A/2,
then D_R>=A/2; otherwise nu>=c and D_R>=4c. Thus the unrestricted original
SUM-debt infimum at R is at least min(A/2,4c)>0. By the exact terminal
debt/UE characterization, R has no uniform-equilibrium payoff.

Its literal singleton matrix is exactly Gamma_ij=Z_i({j}) off the diagonal.
Part I applied to R therefore proves det Gamma>0 and supplies one STRICTLY
positive inverse column. Choose, for example, the least carrying index h.
This choice depends only on the fixed native Z. No approximation, genericity,
changed higher reward, changed native table, or matrix hypothesis is required.

The theorem below is written with this now-PRODUCED column as (1).
Its proof gives explicit constants and a full positive box of weights.

### 1. Exact data, strategic semantics, and statement

There are four owners I={0,1,2,3}. An own-zero native table Z assigns a finite
real reward Z_i(C) to every nonempty quitting coalition C, with Z_i({i})=0.
Every live date and literal Never pays zero. Each owner independently draws
one complete stopping law on the natural dates together with a separate Never
point. The first finite tied coalition absorbs at Z(C). Every unilateral
replacement of a complete law is allowed; this is equivalent to unrestricted
private behavioral deviations along the unique live public history.

For actual laws P write U_i(P) for prescribed reward, B_i(P) for the complete
response supremum, e_i(P) for the pure Never response, and N_i(P) for the
ORIGINAL Never mass. Put

    d_i=B_i-U_i>=0, D_Z=sum_i d_i, nu=product_i N_i,
    M=max(1,max_(i,C)|Z_i(C)|),
    A=inf{D_Z(P): P actual and nu(P)=0}.

Assume A>0. This is the actual absorbing-debt obstruction, not an exhibited
game with positive gap. The native unrestricted infimum is zero because
AllNever is native Nash. Put Gamma_ii=0 and Gamma_ij=Z_i({j}) for i!=j.
Suppose Gamma is invertible and, for some fixed h,

    v=Gamma^(-1)e_h is STRICTLY positive in every coordinate.       (1)

Here e_h denotes the coordinate unit vector only in matrix expressions.
For j!=h put w^j=Gamma^(-1)e_j and choose explicitly

    L_j=max_i |w_i^j|/v_i,
    lambda_j=1/[2(1+L_j)],   lambda=min_(j!=h) lambda_j>0,
    c=(A/(28M))^4,
    epsilon=c*lambda/4.

The weights range over the ONE fixed compact positive box

    K={theta: epsilon/2<=theta_h<=epsilon,
              1<=theta_j<=2 for every j!=h}.                      (2)

Set t0=epsilon*A/32. For theta in K and 0<t<t0 define the FINAL original
reward table

    r_i(C)=theta_i[Z_i(C)+t] for C nonempty, live/Never still zero.  (3)

The original semantic carrier is augmented by ORIGINAL N and native e;
equivalently use the compact native closure

    H=closure{(U^Z(P),B^Z(P),N(P),e^Z(P)): P actual}.

At (3), minimize the true full original SUM debt over H. This is exactly the
unrestricted actual infimum, not a restricted menu or suffix minimum.

**Theorem.** For every theta in K, every 0<t<t0, and EVERY global minimum Y,

    nu(Y)>=c>0,
    B_i^Z(Y)=e_i^Z(Y) for ALL i.                                 (4)

Thus every native END is active, including when its cap is an unattained
finite-deadline supremum. In the raised game every full cap equals the limit
of late finite replies; literal Never remains a distinct, generally lower,
response. The minimum value is strictly positive under A>0. No small-total-
finite-mass hypothesis is present.

All constants use only the fixed native table and its positive A. One may
replace A throughout by any fixed positive lower bound a<=A, with the same
proof and constants c=(a/(28M))^4, t0=epsilon*a/32. The reduction does not
pretend to compute the positive obstruction from an arbitrary reward table.

### 2. Native-to-original identities and the Never bound

A native finite deadline tending to infinity has payoff tending to the pure
Never response: on opponents' finite exits they eventually agree, and on
opponents' joint Never event both pay own zero. Bounded convergence proves
B_i>=e_i. Every finite response at (3) guarantees absorption and adds
theta_i*t. Its late-response limit exceeds raised Never by
theta_i*t*product_(j!=i)N_j. Thus the full caps, including literal Never, obey

    B_i^r=theta_i(B_i^Z+t),
    U_i^r=theta_i[U_i^Z+t(1-nu)],
    D_r=sum_i theta_i d_i^Z+t*Theta*nu,  Theta=sum_i theta_i.       (5)

These continuous identities also hold on H. Its image under (5), retaining
N,e, is the original augmented carrier: actual realizers map both ways and
compactness provides lifts of projected limits. Consequently every minimum
of (5) is an original full-SUM minimum and conversely every such minimum
has a lift in H. No limiting strategy or clock realization is assumed.

For ANY actual P choose an owner k with N_k<=nu^(1/4) and redirect all of its
Never mass to any finite date. The resulting profile absorbs almost surely.
Only its own payoff changes for owner k, by at most 2M N_k; its own cap is
unchanged because the old law is deleted in a response. Each other payoff
and every pure response change by at most 2M N_k under independent coupling.
Taking suprema gives the same bound on each other full cap. Hence

    A<=D_Z(P)+14M*nu(P)^(1/4).                                  (6)

The inequality passes continuously to H. Also 0<A<=8M, since every debt is
at most 2M and actual absorbing profiles exist. In particular 0<c<1 and
0<epsilon<1.

AllNever gives D_r=t*Theta. At any global minimum, nonnegativity of native
debts and (5) imply

    D_Z<=t*Theta/theta_min.

For theta in K, theta_min>=epsilon/2 and Theta<=8. Therefore t<t0 implies
D_Z<A/2. Equation(6) yields nu>=c, and thus N_i>=c for every i. This is a
uniform bound for all weights in the full box and every minimum, independent
of total finite mass and the minimizing point.

The source really is a positive original minimum. At any point of H either
D_Z>=A/2, giving D_r>=theta_min*A/2, or (6) gives nu>=c, giving
D_r>=t*Theta*c. Thus

    inf D_r>=min(theta_min*A/2,t*Theta*c)>0.                       (7)

This uses no strategic equivalence under a terminal-only shift.

### 3. Complete-graft inequality at a global minimum

This section reconstructs the previously established graft inequality with
the exact source coordinates, so its use does not hide a strategic premise.
Fix a native actual old profile P and an independent actual tail Q. If each
owner's old draw is Never, let that owner independently sample its own Q law
after the old finite calendar. For an infinite old calendar first censor
after a finite date to the same owner's Never, retain an empty boundary test,
then append Q on later actual dates. Let the cutoff tend to infinity.
Uniform coupling controls prescribed and every pure-response error by the
removed tail mass times 2M, hence also controls the full cap error.

Put H_i=product_(j!=i)N_j. For each finite prefix the exact native identities
are

    U_i^new=U_i+nu*U_i^Q,
    B_i^new=max(B_i,e_i+H_i B_i^Q),
    N_i^new=N_i N_i^Q,
    e_i^new=e_i+H_i e_i^Q.                                      (8)

Every old prefix response remains available. The empty boundary response
equals old e_i and is below old B_i. Every new finite response and Never has
value old e_i plus H_i times the corresponding Q response. Thus the cap
formula prices the entire menu in both directions. In particular responses
carry the deleted-opponent factor H_i, whereas the prescribed tail gain
carries joint survival nu. They cannot be interchanged.

The identities are continuous in their finite coordinates. Diagonal finite
realizers extend (8) to every old point in H and every tail limit of actual
laws, producing a point in the SAME unrestricted original carrier. A strict
decrease at that point contradicts the original floor; it also implies a
strict decrease at sufficiently late actual approximants.

At a minimum with all N_i>0 define

    kappa_i=(B_i-e_i)/H_i>=0,
    E={i:kappa_i=0}.

For any tail limit Q, minimality of (5) and (8), divided by nu>0, gives

    sum_i theta_i (B_i^Q-kappa_i)^+/N_i
       >=sum_i theta_i U_i^Q+t*Theta*(1-nu_Q).                   (9)

To obtain a direction from raw data choose any fixed nonzero x>=0. For small
rho>0 and integer n let Q_i place mass rho*x_i/n at each of n fresh dates
and mass 1-rho*x_i at Never, with empty dates before and after the word.
All private draws remain independent. As n tends to infinity the probability
of prescribed ties is O(1/n); collision of any forced response with its test
date is also O(1/n), uniformly over all deadlines. The remaining singleton
probabilities and passive reply values are Riemann sums. Their limits are

    U_i(rho)=sum_j Gamma_ij integral_0^1 rho*x_j
                              product_(l!=j)(1-rho*x_l z) dz,
    F_i(y;rho)=integral_0^y sum_(j!=i) rho*x_j
                              product_(l!=i,j)(1-rho*x_l z) Gamma_ij dz,
    B_i(rho)=max_(0<=y<=1)F_i(y;rho),
    N_i(rho)=1-rho*x_i.

The payoff of literal Never is F_i(1;rho), already included in this maximum;
every y is approached by actual finite queries. These formulas cover zero
coordinates of x and moving tester dates, including unbounded deadlines.
Bounded arbitrary higher rewards contribute only the vanishing tie errors.
Uniformly over y,

    U_i(rho)=rho*(Gamma x)_i+O(rho^2),
    B_i(rho)=rho*(Gamma x)_i^++O(rho^2),
    1-nu_Q=rho*sum_j x_j+O(rho^2).

For i outside E, its fixed positive kappa_i makes its clipped term vanish
for sufficiently small rho. No uniform inactive margin across minima is
assumed. Divide (9) by rho and let rho decrease to zero. The result is the
complete necessary inequality

    sum_(i in E) theta_i (Gamma x)_i^+/N_i
       >=sum_i theta_i (Gamma x)_i+t*Theta*sum_j x_j              (10)

for EVERY nonzero x>=0 at the SAME minimum. All caps and Never values were
accounted for before taking this first variation.

### 4. One column and three cone directions force ALL ENDs

Take x=v in (10). Since Gamma v=e_h, inactivity of h makes its left side
zero and its right side theta_h+t*Theta*sum v strictly positive. Thus h is
active. This is the existing single-column consequence, now used as a step.

For j!=h let

    x^j=v+lambda_j w^j.

Because lambda_j L_j<1/2, each coordinate satisfies x_i^j>v_i/2>0. Also

    Gamma x^j=e_h+lambda_j e_j.                                (11)

If j were inactive, only row h could contribute on the left of (10). Hence

    theta_h/N_h >= theta_h+lambda_j theta_j
                           +t*Theta*sum_i x_i^j,
    theta_h*(1-N_h)/N_h >= lambda_j theta_j.                     (12)

But the source bound N_h>=c and the fixed weight box give

    theta_h*(1-N_h)/N_h <= epsilon/c=lambda/4
                                      <lambda_j theta_j,

a contradiction. Every j is therefore active. This proves(4), simultaneously
for every minimum, all theta in K and every 0<t<t0. The direction x^j depends
only on Gamma and h, not on the cap inventory or the minimizing point.

The weight choice does not depend on t or a particular source. The small t
requirement is chosen AFTER the whole positive box. There is no feedback
loop between a vanishing weight, the source Never bound and a selected
minimum: c depends only on Z,A,M and is unchanged as theta ranges over K.

## Part III. Original counterexamples, boundaries, and handoff

### 1. Access from the arbitrary original counterexample obligation

The positive-A source is already obtainable from any hypothetical original
signed Fin4 no-UE table. The exact declaration
`nonempty_finFourSinglePivotNormalization_of_no_uniformPayoff` in
`UniformEquilibrium/Diagnostics/Quitting/FinFourSinglePivotNormalization.lean`
produces a same-skeleton no-UE table R with one own singleton equal to one
and the other three zero. The full terminal debt infimum delta_R is positive
by `quittingTerminalDebtSumInf_pos_iff_not_exists_uniformEquilibriumPayoff`
in `UniformEquilibrium/Quitting/Terminal/TerminalDebtSumInf.lean`.
Subtract one only from the pivot recipient row on nonempty coalitions,
retaining zero live/Never rewards, to obtain own-zero Z. At any absorbing
prescribed profile its prescribed pivot payoff and its complete cap both
shift by one. For the cap, use finite deadlines and the late-deadline limit;
the nonnegative own singleton makes their supremum already dominate Never
in both tables. Thus every absorbing debt is unchanged and A_Z>=delta_R>0.

Part II now applies to this EXACT native Z and produces its strict column,
fixed K, fixed t0 and positive-gap original tables r=theta(Z+t). Every
global SUM minimum at every one of those final tables is all-END. Nothing
here says that the minimizing profiles of the initial user table are
preserved by normalization or weighting. The source reduction produces a
new original table, fixes it, and minimizes its actual unrestricted SUM.

The converse direction of the source reduction is immediate: a strictly
positive full terminal SUM-debt infimum implies original no UE by the
same terminal characterization. Thus the construction loses no hypothetical
counterexample when narrowing the proof obligation to the displayed
weighted all-END source.

### 2. Exact inverse-column boundary controls

A literal Fin4 boundary example is

    G0=[ 0 -1  2  8 ]
       [ 6  0 -6 -6 ]
       [-2  2  0 -1 ]
       [-6  5  1  0 ],  det G0=18,

    B0=[1 -5/18 29/3 -11/3;
        1 -2/9  28/3 -10/3;
        1 -5/9  34/3 -13/3;
        0  1/9  -5/3   2/3].

Only column0 is nonnegative, and its only zero is at row3. Every singleton
column has a negative entry, every principal matrix of size at least two is
invertible, and the exact regular LCP(-ones) census gives degree+1.
Every nonnegative-inverse passive triple test fails. With H=9E_10,

    ((G0+tH)^(-1))_30=-t/(1-5t/2).

Thus positive small t leaves the union of nonnegative inverse-column sets;
negative small t makes the formerly boundary column strictly positive.
This is a control for the boundary argument, not a claim of separation from
every previously accepted UE criterion.

A simultaneous six-column control uses

    T=[0 -1 2; 2 0 -1; -1 2 0], C=T^(-1)>0,
    A=diag(T,T), K=[0 J3; J3 0],

where J3 is the three-by-three all-ones matrix. Every column of A^(-1)
is nonnegative with three zero entries, and every diagonal entry is positive.
For |t|<1/3 the exact inverse blocks of A+tK are

    diagonal: C+[3t^2/(1-9t^2)]J3,
    off-diagonal: -[t/(1-9t^2)]J3.

All eighteen boundary zeros therefore become negative simultaneously for
t>0, while the entire inverse is strictly positive for t<0. The abstract
lemma also applies at G=identity, confirming that a zero base diagonal was
not used in its proof.

The positive diagonal pivots cannot be omitted. For

    G=[0 a; b 0], a,b>0,

its inverse is [0 1/b; 1/a 0]. Every sufficiently small diagonal-preserving
perturbation keeps this form with positive a,b: neither inverse column is
strictly positive, yet both remain nonnegative. The diagonal pivots vanish,
and R0 fails because e0 is a nonzero homogeneous complementary vector.
This is an actual finite-union obstruction when the necessary source
hypothesis is dropped.

### 3. One carrying column is enough for the weight box

The following exact matrix tests the one-column cone construction:

    G=[0 -9 -6 7; -6 0 4 7; 7 8 0 -1; -1 -3 9 0],
    det G=7345,
    G^(-1)=(1/7345)[516 -405 777 524;
                    -391 435 308 -454;
                    -73 100 189 723;
                    484 645 558 36].

Only column h=2 is positive; the other columns are mixed. The three
cone vectors (11) of Part II exist nevertheless. Its use here checks the new cone algebra,
not a claimed positive-A completion or a new UE class outside old coverage.
In particular there is NO exhibited native table with A>0.

### 4. Scope, source correspondence, and implementation handoff

The exact controls above do not exhibit a native positive-A table. The
positive-gap hypotheses are counterfactual source assumptions. Conversely,
the theorem is about every source satisfying them, not about a supplied
finite clock. Smallness of total finite mass was never inferred from
small t. Positive original Never comes from the properification inequality
and the comparison with actual AllNever at the SAME final table.

The nonnegative-column prerequisite does not by itself give strict
positivity; the diagonal-preserving Gordan argument is essential at zero
inverse entries. Its positive diagonal pivots are supplied by R0.
The one-column weight proof does not apply arbitrary signed column
perturbations to a vector with zero coordinates: strict positivity was
proved first for the exact source table.

The full law semantics are the named declarations
quittingTerminalPayoff_stoppingLawProfile_eq_expectedPayoff and
quittingStoppingLawCap_eq_continuationBestResponseValue_stoppingLawProfile in
UniformEquilibrium/Quitting/Paths/StoppingLawOperationalDistance.lean.
The original minimum correspondence is
quittingTerminalDebtSumInf_eq_terminalSemanticDebtSum_of_minimum in
UniformEquilibrium/Quitting/Terminal/TerminalDebtSumInf.lean.
The exact positive-gap characterization, normalization, reward robustness,
degree source and passive-child consumers are named in the respective
proof parts. They are existing tracked declarations; the new source
reductions in this packet are ordinary mathematics to be implemented.

Natural formal targets are: the finite Gordan alternative and simultaneous
zero-diagonal tangent lemma; R0 positivity of the diagonal pivot in a
nonnegative inverse column; strict-column necessity for original Fin4 no UE;
the original augmented full-cap graft; its finite-word first variation;
the source-uniform original Never bound; the fixed positive weight-box
all-END theorem; and their complete original-counterexample adapter.
The actual original reward matrix and full behavioral quantifiers must
be retained at every step. A structure field assuming all-END activity
would not implement the producer proved here.

The remaining obligation is to consume ALL-END minima with arbitrary
original calendars and finite-owner counts. Other finite queries
may tie END, and changing one owner's law can increase observers' complete
caps. This packet proves neither a successful global decrease nor an
equilibrium strategy for that surviving source. It does not resolve
arbitrary Fin4 quitting games.

## Part IV. Complete nonnegative-column prerequisite

### 1. Needed theorem and conventions

For any original four-player quitting table with the full behavioral and
fixed-target semantics stated above, no UE implies

    det G>0 and some column of G^(-1) is entrywise nonnegative.    (N)

Equivalently, UE exists whenever

    det G<=0, or det G>0 and each inverse column has a negative entry. (U)

All own singleton levels and all higher rewards are arbitrary. The following
complete proof establishes this prerequisite, including zero comparisons,
singular principal triples and zero full determinant. Within this part
section and formula references are local. Appendix A below supplies the
entire no-mutually-negative-pair argument used by the proof.

### 2. Generic algebraic lemma

For a real zero-diagonal G use LCP(G,b) in the convention

    x>=0, w=Gx+b>=0, x_i w_i=0.

R0 means that LCP(G,0) has only the zero solution. Its integer degree is that
of the whole-space map x |-> min(x,Gx), with coordinatewise minimum.

Assume every off-diagonal entry of G is nonzero, G is invertible, every
three-principal determinant is nonzero, and every entry of G inverse is
nonzero. Suppose also that G is R0 of integer degree +1, that G has a mutually
negative reciprocal pair, and that

    det G<0 OR every column of G^(-1) has a negative entry. (D)

**Generic lemma.** There are a triple C and its omitted owner o such that

    det G_CC>0,       (G_CC)^(-1)>0,
    G_oC (G_CC)^(-1)>0,                                  (P)

entrywise. Sections3--5 give the complete proof. No positive entry in each
inverse column is required. The det G<0 branch permits full-support roots
because their index is negative.

### 3. Degree forces a triple at every coordinate ray

First G has a negative entry in every column. Otherwise e_j would be a
nonzero homogeneous complementary solution, using G_jj=0, contrary to R0.
Every row has a positive entry: nonzero degree gives an LCP solution at
b=-1, so Gx >= 1 for some x>=0.

Fix h and use

    b(M) = -(M e_h + 1),               M -> +infinity.

Every LCP solution with positive support S must satisfy

    G_SS x_S = M (e_h)_S + 1,
    G_oS x_S >= M (e_h)_o + 1        for o outside S.   (2)

There are finitely many supports. Their possible large-M behavior is as
follows.

* Empty and singleton supports are impossible, since b(M) is strictly
  negative and G has zero diagonal.
* If S omits h, its active solution is constant in M: every principal of
  size at least two is invertible. The outside inequality at h eventually
  fails.
* At full support x=G^(-1)(M e_h+1). If its h-th inverse column has a
  negative coordinate, this support eventually fails. Otherwise every entry
  of that column is strictly positive, by the generic nonzero-entry
  hypothesis, and the full root is eventually strictly positive. Under
  alternative (D), this latter case can occur only when det G<0;
  its local index is then -1.
* Suppose S={h,k}. Positive active coordinates require G_hk,G_kh>0, and
  x_k=(M+1)/G_hk while x_h=1/G_kh. Column k has a negative entry; its row
  cannot be h or k, so an outsider's left side in (2) tends to minus infinity.

Only triples C containing h and possibly a full-support root can therefore
survive for all sufficiently large M. Write T=G_CC and c=G_oC for a triple.
Its active coordinates are

    x_C = M T^(-1)e_h + T^(-1)1.

Every entry of T^(-1)e_h is nonzero: its cofactors are signed products of
two nonzero off-diagonal entries. The exterior leading coefficient
c T^(-1)e_h is also nonzero. Indeed block inversion gives

    (G^(-1))_oh = -[det T / det G] c T^(-1)e_h.       (3)

Thus, for all sufficiently large M, each surviving triple has strictly
positive active coordinates, strictly positive exterior slack, and an
invertible active block. All roots are regular and finite in number.
The local degrees of the triple roots are sign(det T). A surviving full
root is also regular, since its coordinates are strictly positive and G is
invertible, and its index is -1 by the preceding case analysis. The total
sum is +1. Thus the triple-index sum is either +1 or +2, and at least one
triple has positive determinant. We have proved the following property:

    For every h there is a triple C containing h with
    det T>0, T^(-1)e_h>0, c T^(-1)e_h>0.              (AC)

This uses the actual integer degree, not merely existence of some root at
the chosen offsets.

For completeness, the degree facts used here have an elementary R0 proof.
Solutions remain uniformly bounded for b in a compact set: otherwise normalize
an unbounded sequence by its coordinate sum to obtain a nonzero homogeneous
solution. Homotopy in b then preserves degree on a sufficiently large box.
At a strict complementary root its derivative, in active/inactive order, is
[[G_SS,G_S,S-complement],[0,I]], so its local degree is sign(det G_SS).
This proves the offset invariance and local-index convention used here;
the exact tracked degree source is listed in Section9.

### 4. Axis coverage forces a cyclic positive-inverse triple

Only the first two matrix tests in (AC) are needed in this section. Relabel
the mutually negative pair as 01.

The triple chosen for axis2 cannot be 012: its inverse diagonal at2 is
-G_01 G_10 / det G_012 < 0. Similarly axis3 cannot use 013. Thus the
chosen triples for axes2 and3 are among 023 and123.

If both use the same triple, that triple has two strictly positive inverse
columns and positive determinant. The elementary 3 by 3 adjugate formula
then forces cyclic signs and a positive inverse. To spell this out, for

    B = [[0,a,b],[c,0,d],[e,f,0]],
    adj B = [[-df,bf,ad],[de,-be,bc],[cf,ae,-ac]].      (4)

If the last two columns are positive, a,d,e have one sign and b,c,f the
opposite sign. Its first column is then positive as well. Any other choice
of two columns is a relabeling of this calculation.

It remains that different triples were selected. Interchange 0 and1 if
necessary, so axis2 uses 023 and axis3 uses 123. Put

    epsilon=sign(G_32),              delta=sign(G_23).

The positive adjugate columns in (4) force

    sign(G_02)=-epsilon, sign(G_03)=epsilon,
    sign(G_30)=-epsilon;
    sign(G_12)=delta, sign(G_13)=-delta,
    sign(G_21)=-delta.                                  (5)

The signs of G_20 and G_31 are not yet specified.

If delta=-epsilon, one selected triple is already cyclic:

* If epsilon=+1, det G_023>0 forces G_20>0. Its other determinant
  monomial is negative, and the coefficient of G_20 is positive. The
  six signs of 023 now form a directed cycle, so its adjugate is positive.
* If epsilon=-1, det G_123>0 similarly forces G_31>0, making 123 cyclic
  with positive adjugate.

If delta=epsilon, (AC) at axis0 is impossible:

* For epsilon=+1, triple023 has negative inverse diagonal at0, because
  G_23,G_32>0. In triple012, a positive adjugate column at0 would require
  G_20>0; both determinant monomials would then be negative. In triple013,
  the first and third entries of its adjugate column at0 have opposite
  signs, namely sign(G_31) and -sign(G_31).
* For epsilon=-1, positivity of det G_023 and det G_123 forces
  G_20>0 and G_31>0. Triple023 again has negative inverse diagonal at0.
  Triple012 has negative entry G_12 G_20 in its adjugate column at0.
  Triple013 has negative inverse diagonal at0 because G_13,G_31>0.

These exhaust the three triples containing0. Consequently a triple with
positive determinant and positive inverse exists.

### 5. One more axis forces the entire passive row

Relabel this cyclic triple as123 and choose its cyclic orientation so

    T = [[0,-a,b],[c,0,-d],[-e,f,0]],
    a,b,c,d,e,f>0,     Delta=bcf-ade>0,

    adj T = [[df,bf,ad],[de,be,bc],[cf,ae,ac]].        (6)

A mutually negative pair cannot lie inside this triple. Therefore the
outside row0 has a negative entry. It also has a positive entry, as shown
in Section3. Rotate the cyclic labels until

    G_01=-u<0,             G_03=w>0.                 (7)

This rotation is possible for every mixed sign word of length three: there
is an adjacent positive-to-negative transition around the cycle. Write
G_02=v, with either sign. For n=(-u,v,w) adj T, direct subtraction gives

    n_1 = (d/b)n_2 + w Delta/b,
    n_3 = (c/e)n_2 + u Delta/e.                      (8)

Hence positivity of the middle exterior inverse weight implies positivity
of all three weights.

Apply (AC) to axis2. Its triple is one of123,012,023.

* If it is123, the last inequality in (AC) says n_2>0. Equation(8) gives
  all exterior weights positive, proving (P).
* It cannot be012. Its adjugate column at2 has entries
  (G_01 G_12, G_02 G_10, -G_01 G_10). Positivity forces G_10>0 and G_02>0.
  There would then be no mutually negative pair: the three pairs inside123
  have opposite signs; 01 has G_10>0; 02 has G_02>0; 03 has G_03>0.
* If it is023, its adjugate column at2 is
  (G_03 G_32, -G_03 G_30, G_02 G_30). Positivity forces G_30<0 and G_02<0.
  Positive determinant then forces G_20>0, because

      det G_023 = G_02 G_23 G_30 + G_03 G_20 G_32

  has a negative first monomial and a coefficient of G_20 that is positive.
  Thus023 is also a cyclic positive-inverse triple. All pairs except01
  now have opposite signs, so G_10<0. Its exterior row1, in order(0,2,3),
  starts negative and ends positive: (G_10,G_12,G_13). Its middle coordinate
  is again axis2. The same identity(8) and (AC) give all three exterior
  inverse weights positive.

Every possibility proves (P). This completes the generic algebraic proof.

### 6. Generic perturbations of the literal singleton coordinates

Let H=J-I, so H has zero diagonal and every off-diagonal entry equal to one.
Consider the twelve-coordinate line

    G(theta)=(1-theta)G+theta H.

At theta=1 the exact quantities are

    det H=-3,    every three-principal determinant=2,
    adj H has diagonal entries2 and off-diagonal entries-1.

Thus each of the following33 polynomials in theta is nonzero:

* the12 off-diagonal entries;
* the full determinant;
* the four three-principal determinants;
* the16 adjugate entries.

Their product has value -768 at theta=1. Its degree is at most76, so there
are only finitely many forbidden theta. In particular arbitrarily small
positive theta satisfy every generic nonvanishing assumption of Section2.
No inverse exists at a forbidden determinant zero, and no such value is used.
The endpoint H is only a witness that these polynomials are nonzero; it need
not satisfy any of the other hypotheses of the generic lemma.

If det G<0, the same strict inequality holds for sufficiently small theta.
If det G>0 and every inverse column has a negative entry, select one such
entry per column. Continuity of inversion on invertible matrices preserves
all four selected negative signs and det G(theta)>0 for sufficiently small
theta. These observations prove that the open raw alternatives in (U), with
strict negative determinant replacing det<=0, admit arbitrarily close generic
perturbations satisfying (D).

Realize this line in the ORIGINAL table by

    r(theta)_i({j})=s_i+G(theta)_ij,
    r(theta)_i(S)=r_i(S) for |S|>=2.

Own singleton levels are unchanged because the diagonal stays zero. Every
higher reward is unchanged. All live and Never rewards remain zero. With

    D=max_(i!=j)|1-G_ij|,

its uniform distance from r is exactly theta D. The harmless bound
theta max(1,D) may be used even if D=0. There is no strategic transport under
an absorbing offset; these are literal nearby reward tables on the same
quitting transition structure.

### 7. Actual no-UE openness and the open alternatives

For one fixed profile or one fixed unilateral replacement, changing every
absorbing reward by at most delta changes its terminal expectation by at most
delta. The first-quitter law is the same, and its total absorption mass is at
most one. Literal Never has the same zero reward in both tables. It follows
that every deviation gain changes by at most2delta, uniformly over all
behavioral profiles and all complete replacements. No cap needs to be attained.

The terminal characterization of the uniform-payoff problem says that no UE
is equivalent to a fixed positive terminal exploitability gap against every
behavioral profile. Thus if r has such a gap g>0 and ||r'-r||_infinity<g/4,
the very same deviations give r' a gap greater than g/2. Hence r' also has
no UE. This establishes the required openness in the actual60-coordinate
reward space; it does not assume continuity of an equilibrium selector.

Suppose now that r belongs to either open alternative

    det G<0, or det G>0 with a negative entry in every inverse column,

but has no UE. Choose a sufficiently small generic positive theta from
Section6, so r(theta) stays inside that alternative and inside the positive
gap neighborhood. The SAME perturbed original game r(theta) has no UE.
Apply these established necessary facts to that game:

1. Its full literal singleton matrix is R0 of integer degree+1.
2. It has a mutually negative reciprocal pair; otherwise the complete
   proof in AppendixA gives original-game UE.

All hypotheses of Section2 hold for G(theta). Its produced triple (P)
satisfies the literal positive-inverse/passive-row criterion, which gives a
uniform-equilibrium payoff for r(theta), a contradiction. This proves UE
for both open alternatives. The argument does not require R0 or degree to be
continuous under the selected perturbation: each comes afresh from the
actual perturbed no-UE game.

### 8. Every zero determinant is approached from the negative side

Determinant, restricted to the twelve off-diagonal entries, is a nonzero
multi-affine polynomial p. It is affine separately in each coordinate,
because every determinant monomial uses each matrix entry at most once.
It is not identically zero, since p(H)=-3.

Let p(G)=0 and fix ANY delta>0. Take the closed twelve-dimensional cube
whose off-diagonal coordinates are G_ij plus or minus delta; keep the diagonal
zero. By successive averaging in each coordinate, the average of p over
its4096 vertices equals p(G)=0.

These vertex values cannot all vanish. A multi-affine polynomial on a box
with positive side lengths is recovered from its vertex values by successive
linear interpolation in each coordinate. If all values vanished, p would
vanish on the whole box and hence be the zero polynomial, contrary to
p(H)=-3. Therefore some vertex value is strictly negative (and another is
strictly positive). This conclusion holds for every delta>0, without any
rank, cofactor, or genericity hypothesis at G.

Realize that negative-determinant vertex by changing only the original
cross-singleton coordinates, retaining all own and higher rewards as in
Section6. The actual reward distance is delta. Every such neighboring table
has UE by Section7. Existing reward-closure of uniform-payoff existence now
produces one fixed target for r itself. The neighboring targets and profiles
may vary; the closure theorem does not assume their convergence in advance.
Equivalently, the positive-gap argument of Section7 would rule out no UE at
r because every positive-radius neighborhood contains one of these UE tables.

This proves the zero-determinant case and completes the actual-game theorem.
Negating the two excluded alternatives gives exactly (N).

### 9. Source correspondence, verification, and precise remaining scope

The following exact tracked declarations supply the stated mathematical consumers.

* `finFour_singleton_r0Degree_eq_one_of_no_uniformPayoff`, in
  `UniformEquilibrium/Diagnostics/Quitting/FinFourSingletonDegreeCriterion.lean`,
  gives full R0 and canonical integer degree+1 from the same original Fin4
  no-UE hypothesis. Its degree convention agrees with the local index account
  in Section3; the full local-index account is included there.
* `not_exists_uniformEquilibriumPayoff_iff_exists_terminalExploitabilityGap`,
  in `UniformEquilibrium/Quitting/Terminal/ExploitabilityGap.lean`, supplies
  the positive gap with complete behavioral quantifiers.
* `abs_quittingTerminalExploitability_sub_le_of_reward_close` and
  `exists_uniformEquilibriumPayoff_of_arbitrarily_close_reward_tables`, in
  `UniformEquilibrium/Quitting/Terminal/TerminalExploitabilityRewardRobustness.lean`,
  record the2-Lipschitz bound and fixed-target reward closure used above.
  Their underlying profile and deviation spaces are identical across tables.
* `childMatrix`, `outsideRow`, `inverseWeight`,
  `exists_labeledCycle_uniformPayoff_of_raw_strictInverse_triple`, and
  `exists_uniformEquilibriumPayoff_of_raw_nonnegativeInverse_triple`, in
  `UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/RawPassiveRowInverseCriterion.lean`,
  read the actual child principal and outside row in recipient-first,
  singleton-owner-second convention. They consume exactly (P), with no
  supplied strategic object, and allow arbitrary signed own and higher rewards.

The negative-pair necessity used above is proved in full in Appendix A of
this part. Its external mathematical consumers are the exact tracked Lean
declarations named in that argument. The complete exact algebraic checker
appears after its proof; finite tests corroborate the universal analytic
argument and do not replace it.

### AppendixA. Complete proof that absence of a negative reciprocal pair gives UE

This appendix is included to make the source self-contained. All claims below
refer to the original game with signed own and arbitrary higher rewards.
The only external mathematical consumers invoked are exact tracked Lean
declarations named in the text.

#### A.1. The positive-chord Hamiltonian class

Consider arbitrary real four-player quitting rewards r_i(S), with live and
Never payoff zero, private independent randomization, and unrestricted
behavioral deviations. Put s_i=r_i({i}) and Gamma_ij=r_i({j})-s_i for
i different from j, with diagonal zero. Suppose positive scaling of
payoff rows and relabeling puts the singleton matrix in the form

    Gamma = [ 0   a   e  -1 ]
            [-1   0   b   g ]
            [-f  -1   0   c ]
            [ d  -h  -1   0 ],

where a,b,c,d,e,g,h>0 and f<0. Thus the opposite pair 02 is mutually
positive, every other reciprocal pair has opposite signs, and there is
a negative Hamiltonian cycle 0,1,2,3. Own levels and all higher coalition
rewards are unrestricted.

Every such original table has a uniform-equilibrium
payoff. The scope differs from the reciprocal-opposition classification:
the strict product Gamma_02 Gamma_20 is positive here. The proof produces
a legal expanding four-cycle using the same direct singleton consumer,
but its support census and lower endpoint argument are different.

#### A.2. Necessary source and the easy exit

Suppose the original table had no uniform-equilibrium payoff. The exact
same-table full-Q reduction follows from
`standardQMatrixSide_of_not_exists_uniformEquilibriumPayoff` in
`UniformEquilibrium/Quitting/Classification/LCP/CounterexampleNecessary.lean`
and `normalCore_eq_univ_of_fourPlayer_not_exists_uniformEquilibriumPayoff`
in `UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/AmbientCarrierElimination.lean`.
Thus Gamma is standard Q: every offset has a nonnegative complementary
solution. Positive row scaling preserves this assertion and preserves
original-game utility comparisons and UE existence.

Only the triple 013 has a cyclic tournament of reciprocal signs. Its
determinant is Delta1=adg-h. The other triples either contain the positive
pair 02 and have a nonnegative column, or are transitive and have a
nonnegative column. Every proper pair and singleton is also projective Q.
If Delta1>=0, the cyclic triple is standard Q for positive determinant,
or has a positive homogeneous kernel for zero determinant. The full
matrix is standard Q, so every principal is projective Q. The checked
`exists_uniformEquilibriumPayoff_of_projectiveQBar_snell` in
`UniformEquilibrium/Quitting/AbsorptionPath/PunishmentNormalPathStrategicSnell.lean`
then contradicts nonexistence. The cyclic determinant classification is
`standardQ_and_noHomogeneous_iff_orientation_and_det_pos` in
`UniformEquilibrium/Quitting/Classification/LCP/ThreeByThreeZeroDiagonalQ.lean`.

It remains to handle Delta1<0. Define Delta2=cde-f>0.

#### A.3. A large negative offset forces one inverse column

Write LCP offset as -y, with y strictly positive. Fix y0,y2,y3 and let
y1 tend to infinity. Every complementary solution on an active support S
satisfies Gamma_SS x_S=y_S with x_S strictly positive.

Singleton support is impossible. A reciprocal opposite-sign pair cannot
map a nonnegative vector to a strictly positive vector. The only other
pair is 02; it is invertible and its solution is fixed by y0,y2.
For support 023, the determinant is Delta2>0, so its solution is fixed by
y0,y2,y3. Both such supports have a bounded exterior row at owner 1,
and therefore fail for large y1.

Support 013 is a negative-determinant cyclic triple. Its inverse is
strictly negative, so it cannot map a nonnegative vector to y_S>0.
Support 123 has its owner-3 row nonpositive and also cannot do so.
Finally, on support 012 the two equations

    a x1+e x2=y0,
    (-f)x0-x1=y2

bound all three nonnegative variables independently of y1. Consequently
the equation -x0+b x2=y1 fails for sufficiently large y1. This is an
explicit support argument; no nonsingularity of this triple is needed.

Hence every solution for all sufficiently large y1 has full support.
The same conclusion holds on an open set of y by the uniform bounds
when the other three coordinates range in small positive compact
intervals. Standard Q now implies that Gamma maps an open set onto that
open set of y, and so Gamma is invertible. Letting y1 tend to infinity
in its strictly positive full solution gives

    Gamma^(-1)e1 >= 0.

The diagonal cofactor at owner 1 is Delta2>0. The inverse-column sign
therefore forces det Gamma>0. Exact adjugate expansion gives

    adj(Gamma)e1 =
      (1-ac+ceh, Delta2, d+fh-acd, -af+de+efh).

In particular

    d+fh >= acd > 0,
    c(a-eh) <= 1.

These are produced by the same-table Q source, not additional raw guards.

#### A.4. Produce the positive expanding Hamiltonian ray

Start from v=(0,1,r,0). Successive column moves 0,1,2,3 have durations

    t0=1,
    t1=r-f,
    t2=d-h(r-f),
    t3=a(r-f)+e[d-h(r-f)].

Every duration is positive and every intermediate vector is nonnegative
when 0<r<R, where R=f+d/h=(d+fh)/h>0. The endpoint is (0,x',y',0),
with return matrix

    M = [ga  b+ge] [-f      1] = [A B].
        [ca   ce ] [d+hf  -h]   [C D]

Direct expansion gives

    det M=abcd>0,
    det(I-M)=-det Gamma<0,
    C=c[-af+e(d+fh)]>0,
    D=c(a-eh)<=1,
    D+C/R=acd/(d+fh)<=1.

The characteristic polynomial is negative at one and has positive
constant term. It has two distinct positive roots
0<lambda_minus<1<lambda_plus. Put lambda=lambda_plus and

    r=C/(lambda-D).

Since C>0 and lambda>D, r>0. Since lambda>D+C/R, r<R.
The second eigenvector equation is immediate; the characteristic equation
then gives the first. Thus M(1,r)=lambda(1,r), and all four durations are
strictly positive. The lower endpoint does not need a passive-row test:
f<0 makes r>0 already stronger than r>f.

#### A.5. The actual strategic consumer

Let T=sum t_j and alpha=(lambda-1)/T. Starting from native continuation
alpha v, prepend owner j with hazard

    q_j=alpha t_j/(1+alpha sum_(k<j)t_k+alpha t_j),

in construction order 0,1,2,3. The value is the unnormalized column
path divided by one plus accumulated scaled time. It remains nonnegative,
and the moving owner's value is zero. At the end its value is
alpha lambda v/(1+alpha T)=alpha v. The reverse chronological word is
therefore an exact periodic singleton Bellman cycle, with joint survival
1/lambda<1 and positive opponent hazard for every player.

The corresponding supplied-certificate consumer is
`BalancedSingletonCycleCertificate.isUniformEquilibriumPayoff` in
`UniformEquilibrium/Quitting/Cycles/BalancedSingletonCertificate.lean`.
Its singleton arcs, owner equalities, all singleton floors and opponent
divergence have just been produced. Its arbitrary signed-own and
arbitrary-higher-reward scope is essential here.

Equivalently, subdivide every singleton block into sufficiently small
hazards without changing its survival or coarse value. Every intermediate
value remains on its original nonnegative segment. With H the maximum
positive native joining-pair reward and every microhazard at most delta,
the full-cap excess satisfies

    d_i' <= max(H delta,d_i).

For the moving owner it is unchanged. Iterating this exact maximum
recursion caps every finite deadline without an error proportional to
word length. Opponent survival tending to zero adds literal Never and
every behavioral mixture. Original own levels shift every prescribed and
deviating terminal payoff by the same s_i because opponents absorb surely.
The uniform opponent tail bound transfers to finite-horizon payoffs with
one fixed target s+alpha v, independently of delta. This proves the
core conclusion.

#### A.6. The non-Hamiltonian two-triangle chamber

The remaining strongly connected five-edge negative graph is

    0->1, 1->2, 2->0, 0->3, 3->2.

Its missing pair 13 is mutually positive. Positive row scaling puts its
singleton matrix in the form

    Gamma = [ 0   a  -1   g ]
            [-1   0   b   p ]
            [ c  -1   0  -e ]
            [-1   q   d   0 ],

with all eight parameters positive. Its cyclic triples are 012 and 023,
with determinants D1=abc-1 and D2=cdg-e. The other triples have a
nonnegative column and so are projective Q. If D1,D2>=0 the full-Q
source again gives the projective-Q-bar exit.

For the good triple 012, meaning D1>0, multiply its exterior inverse row
by D1. The resulting three entries are

    n=(bcq-b+d, acd+cq-1, -ab+ad+q).

This row fails nonnegativity exactly when n2=a(d-b)+q<0. Indeed if
n2>=0 then n1>=abc-1=D1>0. If d>=b then n0>0 directly; if b>d,
q>=a(b-d) implies n0>=(b-d)D1>0. Thus failure requires b>d.
For the good triple 023, meaning D2>0, the corresponding row is

    m=(be+cdp-de, bg-dg+p, bcg+cp-e).

It fails nonnegativity exactly when its middle entry m2=g(b-d)+p<0
(the labels here are the actual coordinates 0,2,3). If m2>=0 then
m3>=cdg-e=D2>0. If b>=d then m0>0 directly; if d>b then
p>=g(d-b) gives m0>=(d-b)D2>0. Thus this failure requires d>b.
These implications alone already prevent both good triples from failing.

Suppose exactly one determinant is positive and the other is negative.
If its passive row is nonnegative, the raw passive-row inverse consumer
already gives UE. Otherwise fix y0,y1,y3>0 and let y2 tend to infinity
in LCP(Gamma,-y). Here is the entire proper-support census:

* A singleton or an opposite-sign pair cannot map a nonnegative vector
  to a strictly positive vector. Pair 13 can do so internally, but its
  exterior row 2 is (-1,-e), which violates the positive residual target.
* Triple 123 has its row 2 strictly negative off diagonal, so cannot
  support such a solution. Triple 013 is invertible, with determinant
  -ap-gq<0; its solution depends only on the fixed y0,y1,y3, so its
  exterior row cannot dominate y2 for large y2.
* A nonpositive-determinant cyclic triple cannot map a nonnegative
  vector to a strictly positive vector. For a positive-determinant
  cyclic triple, the failed passive row has a negative coefficient
  precisely at the varying coordinate 2, by the preceding formulas.
  Its exterior residual therefore eventually fails.

Thus every solution has full support for all sufficiently large y2,
uniformly on a small open box for the other coordinates. Full standard Q
implies invertibility and Gamma^(-1)e2>=0. But exact expansion gives

    adj(Gamma)e2 =
      (-adp-bgq-pq, -bg+dg-p, -ap-gq, ab-ad-q).

The negative diagonal entry forces det Gamma<0. When triple 012 is good
and fails its passive test, the last adjugate entry is -n2>0. When triple
023 is good and fails, the second entry is -m2>0. Either would give a
negative entry of Gamma^(-1)e2, a contradiction. This closes the mixed
case. Cases with one positive and the other zero were already covered by
D1,D2>=0.

It remains that D1,D2<=0 with at least one strictly negative. The same
large-y2 census excludes every proper support: both cyclic triples now
fail internally. We obtain a unique strictly positive full-support root,
invertibility, and again det Gamma<0 from adj(Gamma)_22=-ap-gq<0.
This is incompatible with the actual no-UE degree source. The same-table
no-homogeneous source gives full R0: a nonzero homogeneous nonnegative
complementary vector could be normalized to a homogeneous simplex vector.
The exact equivalence is `isR0Matrix_iff_not_singletonLCPFeasible` in
`MathUE/LinearProgramming/CopositiveQ.lean`. The full-core transport above
identifies this with the original full singleton matrix.

The inspected theorem `singleton_r0Degree_eq_one_of_no_uniformPayoff` in
`UniformEquilibrium/Quitting/Classification/LCP/SingletonDegreeCriterion.lean`
says that an R0 singleton matrix of an original no-UE game has degree one.
There is no extra positive-own or auxiliary no-UE assumption. On the other
hand, `exists_finset_r0Degree_eq_sum_sign_det` in
`MathUE/LinearProgramming/R0DegreeSum.lean` computes the degree from all
roots at any test offset with strict complementarity and nonsingular
active principals. At the chosen -y there is exactly one root, it has
full positive support, and its active Jacobian is Gamma with negative
determinant. Strict complementarity has no inactive coordinate to check.
The degree is therefore -1, contradicting one. No genericity of other
principals or other offsets is needed. This closes the entire two-triangle
chamber.

#### A.7. Exhaust the no-mutually-negative singleton sign graphs

The full theorem is: if, for each i!=j, at least one of Gamma_ij
and Gamma_ji is nonnegative, then the original four-player game has UE,
with arbitrary own levels and higher rewards.

First assume every off-diagonal coordinate is nonzero. Form the oriented
negative graph with edge j->i exactly when Gamma_ij<0. It has no reciprocal
edges. A missing edge is precisely a mutually positive pair. Under no UE,
every column has a negative entry, so every vertex has outdegree at least
one. There are between four and six edges.

If the graph is not strongly connected, it consists of a strongly connected
three-cycle and one singleton. To justify this, a finite directed graph
with every vertex of positive outdegree has a terminal strongly connected
component containing a directed cycle. With no reciprocal edges, that
component has at least three vertices. As the whole graph is not strong,
it has exactly three; the remaining vertex has an edge into it. No edge
can leave the terminal component. Consequently the exterior row c of the
triple is strictly positive and its exterior column has at least one
negative coordinate. Let B be the cyclic triple. If det B>0, then B^-1>0
and cB^-1>0 gives the passive-row exit. If det B<=0, choose y_out=1 and
all three child targets equal to a large Y. If x_out=0, every residual
requires Bx_child>=Y*1, which is impossible: for det B<0 its negative
inverse, and for det B=0 its positive left kernel, both rule it out.
If x_out>0, complementarity gives c x_child=1, uniformly bounding every
child coordinate. At a child row i where Gamma_i,out<0, the residual
Gamma_i x is bounded above independently of x_out and Y. For large Y it
cannot reach its target. This contradicts standard Q. Thus the graph
must be strongly connected.

With four edges every vertex has outdegree one, and strong connectivity
makes the graph a directed four-cycle. It has no directed triangle; every
proper principal has a nonnegative column. Full Q then gives Q-bar UE.
With six edges the graph is a tournament, handled by the complete strict
reciprocal-opposition proof in AppendixA.8.

With five edges, if there is a directed Hamiltonian cycle, the missing
pair is opposite on that cycle. Rotate it to pair 02. The remaining
opposite chord can be made positive in entry 13 by rotating the cycle
two positions if necessary. Row normalization gives exactly AppendixA.1--A.5:
f<0 and the other seven parameters positive.

If there is no Hamiltonian cycle, choose a directed triangle, which must
exist: a shortest directed cycle has length three or four, and length four
would already be Hamiltonian. The remaining vertex needs both an incoming
and an outgoing edge for strong connectivity. These use the two remaining
edges, and their triangle endpoints are distinct because reciprocal edges
are forbidden. Write these edges u->outside->v. If u->v is an edge of the
triangle, replacing it by this two-step path gives a Hamiltonian cycle.
Otherwise v->u is the triangle edge, and the graph is precisely the two
triangles sharing that edge in AppendixA.6, up to relabeling. This completes
the strict sign census without any computational premise.

For off-diagonal zeros, perturb each literal off-own singleton reward by
arbitrarily little so every reciprocal pair remains free of two negative
entries and both entries become nonzero. For example, replace a zero
opposite a negative entry by a small positive number, a zero opposite a
positive entry by a small positive number, and two zeros by two small
positive numbers. Leave all other coordinates, all own levels and all
higher rewards unchanged. The strict theorem applies to each approximant,
and `exists_uniformEquilibriumPayoff_of_arbitrarily_close_reward_tables`
in `UniformEquilibrium/Quitting/Terminal/TerminalExploitabilityRewardRobustness.lean`
gives UE for the original table with its required fixed-payoff quantifier.

Every remaining Fin4 counterexample must therefore have a mutually
strictly negative singleton pair. Full Fin4 is not closed by this theorem.

#### A.8. Complete strict-tournament argument used by the sign census

For completeness the tournament branch is proved here, with no appeal to
another unformalized packet. The source and exits concern the same original
reward table. Besides standard Q, the no-UE source excludes a nonzero
homogeneous LCP vector, as supplied by
`standardQMatrixSide_of_not_exists_uniformEquilibriumPayoff` in
`UniformEquilibrium/Quitting/Classification/LCP/CounterexampleNecessary.lean`
and the full-core transport in AppendixA.2. A nonnegative column would itself
be homogeneous; its exclusion is also the direct conclusion of
`exists_singletonColumnBlockerCertificate_of_fourPlayer_noUniform` in
`UniformEquilibrium/Quitting/Classification/LCP/FourPlayerSingletonColumnBlockers.lean`.

Only strongly connected tournaments need consideration, because AppendixA.7
handles every nonstrong oriented negative graph. Every strongly connected
four-tournament has a directed Hamiltonian cycle: choose a directed triangle
and the fourth vertex; it has both incoming and outgoing triangle neighbors,
so some triangle edge can be replaced by a path through that vertex. Rotate
the Hamiltonian cycle so both opposite chords in entries 02 and 13 are
positive. The four possible orientations of the two chords are interchanged
transitively by the four rotations. Positive row scaling yields exactly
AppendixA.1's displayed matrix, now with all a,b,c,d,e,f,g,h strictly positive.
Its only cyclic triples are 013 and 023, with determinants

    Delta1=adg-h, Delta2=cde-f.

Every transitive triple has both a nonnegative column and a nonpositive
row. Every opposite-sign pair and every singleton similarly has a
nonnegative column and cannot map a nonnegative vector to a strictly
positive vector. For a cyclic triple, the adjugate is strictly positive.
Positive determinant gives a strictly positive inverse and standard Q;
negative determinant gives a strictly negative inverse, hence forbids a
positive image of a nonnegative vector. At determinant zero there are
strictly positive right and left kernels; the former is homogeneous and
the latter forbids such a positive image.

If both Delta values are nonnegative, all proper principals are projective
Q. Together with full standard Q this supplies the Q-bar exit in AppendixA.2.
If both are nonpositive with at least one negative, every proper support
is impossible at every offset -y, y>>0. Thus standard Q supplies a full
positive solution to Gamma x=y for every positive y. The range contains
an open set, proving invertibility; taking y towards each coordinate vector
then gives Gamma^-1>=0. A negative cyclic determinant is a diagonal
cofactor, so det Gamma<0. The checked theorem
`exists_uniformEquilibriumPayoff_of_nonnegative_singletonInverse` in
`UniformEquilibrium/Quitting/Classification/LCP/NonnegativeInverseCriterion.lean`
consumes precisely this determinant sign and nonnegative inverse and yields
UE, with arbitrary higher rewards.

The only remaining case has one strictly positive and one strictly negative
Delta. Let S be the good cyclic triple, o its missing owner, B=Gamma_SS,
and R=Gamma_oS B^-1. If R>=0, the passive-row inverse exit applies. The exact
consumer is
`PassiveRowInverseCriterion.exists_uniformEquilibriumPayoff_of_raw_nonnegativeInverse_triple`
in
`UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/RawPassiveRowInverseCriterion.lean`.
Otherwise R has a negative coordinate. The good triple is the only proper
principal that can support an LCP at offset -y with y>>0. Fix y_S and let
y_o tend to infinity; its exterior residual R y_S-y_o becomes negative.
Every solution must therefore have full support, uniformly on a small
open box for y_S. Standard Q forces invertibility and

    Gamma^-1 e_o>=0, det Gamma>0,

where the second conclusion follows from the positive diagonal cofactor
Delta_good. Define M=[[A,B0],[C,D]] by the return in AppendixA.4. Its determinant
is abcd>0 and det(I-M)=-det Gamma<0, so its eigenvalues satisfy
0<lambda_minus<1<lambda_plus. The legal interval is now f<r<R0=f+d/h.
The following two exact endpoint arguments place the expanding ray inside it.

When Delta1>0>Delta2, the outside row of triple 013, multiplied by Delta1,
is

    (n0,n1,n3)=(ch-dg-fgh, acd-d-fh, ac-afg-1).

If n0>=0, then c>=dg/h+fg, giving n3>=Delta1/h>0 and
n1>=(d/h+f)Delta1>0. Thus the passive-row failure means n0<0.
The omitted inverse column has adjugate entries

    (B0, 1-d(b+ge), Delta1, a-abd-eh).

Hence B0>=0 and d(b+ge)<=1. In fact B0>0: equality implies
ag=h(b+ge), giving Delta1=h[d(b+ge)-1]<=0, a contradiction.
Put r=(lambda_plus-A)/B0. The eigenvector equations follow from the
characteristic polynomial, and A+B0*f=d(b+ge)<=1 gives r>f. At R0 set
ell=A+B0*R0=adg/h>1. The projective return there equals c/g<R0 by n0<0.
Writing chi(t)=det(tI-M), direct expansion gives

    chi(ell)=B0*ell*(R0-c/g)>0.

Since ell>1>lambda_minus, ell>lambda_plus. Thus r<R0.

When Delta1<0<Delta2, the outside row of triple 023, multiplied by Delta2,
is

    (m0,m2,m3)=(bcd-c+fg, bd+deg-1, bf-ce+efg).

If m3>=0 then m2=(d*m3+Delta2)/f>0. Also m0>0: it is direct when
g>=c/f, and otherwise follows from
m0=(cd/f)m3+Delta2(c/f-g)>0. Passive-row failure therefore means m3<0.
The omitted inverse column has the same adjugate entries as AppendixA.3,
so C>=0, D<=1 and acd/(d+fh)<=1. In fact C>0: C=0 would imply
a=e(d+fh)/f and acd=(cde/f)(d+fh)>d+fh, a contradiction.
Put r=C/(lambda_plus-D)>0. This is an eigenvector ratio. The identity
D+C/R0=acd/(d+fh)<=1 gives r<R0. At the lower endpoint let
ell=D+C/f=cde/f>1. The failed passive coefficient m3<0 gives
ce/(b+ge)>f, equivalently A+B0*f=d(b+ge)<ell. The exact identity

    chi(ell)=(C/f)[ell-(A+B0*f)]>0

therefore implies ell>lambda_plus, hence
r=C/(lambda_plus-D)>C/(ell-D)=f.

In either mixed case all four durations in AppendixA.4 are strictly positive,
all intermediate values are nonnegative, and M(1,r)=lambda_plus(1,r).
The complete singleton consumer of AppendixA.5 produces a fixed original-game
uniform payoff. This finishes the strict-tournament branch and makes
AppendixA.7's full sign classification self-contained.

### Appendix B. Exact verification of the prerequisite

Save this complete block as a file and run it with Python 3 and SymPy.

```python
#!/usr/bin/env python3
"""Exact finite algebra checks; no floating arithmetic or game solver."""
from itertools import product


def det3(t):
    return (t[0][0] * (t[1][1] * t[2][2] - t[1][2] * t[2][1])
            - t[0][1] * (t[1][0] * t[2][2] - t[1][2] * t[2][0])
            + t[0][2] * (t[1][0] * t[2][1] - t[1][1] * t[2][0]))


def adj3(t):
    out = [[0] * 3 for _ in range(3)]
    for i in range(3):
        for j in range(3):
            rr = [k for k in range(3) if k != j]
            cc = [k for k in range(3) if k != i]
            out[i][j] = (-1) ** (i + j) * (
                t[rr[0]][cc[0]] * t[rr[1]][cc[1]]
                - t[rr[0]][cc[1]] * t[rr[1]][cc[0]])
    return out


def mul(a, b):
    return [[sum(a[i][k] * b[k][j] for k in range(len(b)))
             for j in range(len(b[0]))] for i in range(len(a))]


# Formula(4), including its inverse identity, at all strict sign choices.
for a, b, c, d, e, f in product((-1, 1), repeat=6):
    t = [[0, a, b], [c, 0, d], [e, f, 0]]
    adj = [[-d*f, b*f, a*d], [d*e, -b*e, b*c], [c*f, a*e, -a*c]]
    assert adj3(t) == adj
    assert mul(t, adj) == [[det3(t) if i == j else 0
                           for j in range(3)] for i in range(3)]


# Formula(8) is polynomial after multiplication by b or e. Each variable
# degree is at most two, so exact agreement on {1,2,3} in every variable
# proves the polynomial identities by univariate interpolation successively.
for a, b, c, d, e, f, u, v, w in product((1, 2, 3), repeat=9):
    delta = b*c*f - a*d*e
    n1 = -u*d*f + v*d*e + w*c*f
    n2 = -u*b*f + v*b*e + w*a*e
    n3 = -u*a*d + v*b*c + w*a*c
    assert b*n1 == d*n2 + w*delta
    assert e*n3 == c*n2 + u*delta


positions = [(i, j) for i in range(4) for j in range(4) if i != j]
survivors = 0
cyclic_counts = {1: 0, 2: 0}
for signs in product((-1, 1), repeat=12):
    g = [[0] * 4 for _ in range(4)]
    for (i, j), value in zip(positions, signs):
        g[i][j] = value
    if not all(any(g[i][j] < 0 for i in range(4)) for j in range(4)):
        continue
    if not all(any(g[i][j] > 0 for j in range(4)) for i in range(4)):
        continue
    if not any(g[i][j] < 0 and g[j][i] < 0
               for i in range(4) for j in range(i + 1, 4)):
        continue
    eligible = [[] for _ in range(4)]
    cyclic = []
    strong = set()
    for omitted in range(4):
        child = [i for i in range(4) if i != omitted]
        t = [[g[i][j] for j in child] for i in child]
        # Positive determinant is impossible if both nonzero monomials
        # are negative. If either is positive, keep the sign possibility.
        if (t[0][1] * t[1][2] * t[2][0] < 0
                and t[0][2] * t[1][0] * t[2][1] < 0):
            continue
        adj = adj3(t)
        if all(value > 0 for row in adj for value in row):
            cyclic.append(omitted)
            pos = [j for j in child if g[omitted][j] > 0]
            neg = [j for j in child if g[omitted][j] < 0]
            # Equation(8), after a cyclic rotation: an outside row has
            # negative first and positive last entries. The middle axis
            # is the strong test. The sign word determines it uniquely.
            if len(pos) == 3:
                strong.update((h, omitted) for h in child)
            elif len(pos) == 1:
                strong.update((h, omitted) for h in child if g[h][pos[0]] < 0)
            elif len(neg) == 1:
                strong.update((h, omitted) for h in child if g[neg[0]][h] < 0)
        for local, h in enumerate(child):
            if all(adj[i][local] > 0 for i in range(3)):
                eligible[h].append(omitted)
    if not all(eligible):
        continue
    survivors += 1
    assert cyclic
    cyclic_counts[len(cyclic)] += 1
    forcing_axes = [h for h in range(4)
                    if all((h, o) in strong for o in eligible[h])]
    assert len(forcing_axes) == 1

assert survivors == 132
assert cyclic_counts == {1: 120, 2: 12}
print('PASS: adjugate formulas and exact exterior polynomial identities')
print('PASS: all4096 sign patterns;132 survivors; each has one forcing axis')

# Additional original-game perturbation and determinant-closure controls.
from fractions import Fraction as F
from itertools import permutations, combinations


def det(a):
    n = len(a)
    answer = F(0)
    for p in permutations(range(n)):
        sign = (-1) ** sum(p[i] > p[j] for i in range(n) for j in range(i+1, n))
        term = F(sign)
        for i in range(n):
            term *= a[i][p[i]]
        answer += term
    return answer


def principal(a, indices):
    return [[a[i][j] for j in indices] for i in indices]


def adj(a):
    n = len(a)
    return [[(-1) ** (i+j) * det([[a[k][l] for l in range(n) if l != i]
                                  for k in range(n) if k != j])
             for j in range(n)] for i in range(n)]


def inv(a):
    d = det(a)
    assert d
    return [[v/d for v in row] for row in adj(a)]


def guards(a):
    return ([a[i][j] for i, j in positions] + [det(a)]
            + [det(principal(a, c)) for c in combinations(range(4), 3)]
            + [v for row in adj(a) for v in row])


H = [[F(i != j) for j in range(4)] for i in range(4)]
assert det(H) == -3
assert all(det(principal(H, c)) == 2 for c in combinations(range(4), 3))
assert adj(H) == [[F(2 if i == j else -1) for j in range(4)] for i in range(4)]
assert len(guards(H)) == 33
product_at_one = F(1)
for value in guards(H):
    product_at_one *= value
assert product_at_one == -768

# A boundary calibration: triple123 is singular and one full inverse entry
# is zero, but every inverse column contains a strictly negative entry.
G = [[F(v) for v in row] for row in
     [[0,-1,2,-2],[2,0,-2,1],[-1,2,0,1],[-1,2,2,0]]]
assert det(G) == 4
assert det(principal(G, (1,2,3))) == 0
assert inv(G)[0][0] == 0
assert all(any(inv(G)[i][j] < 0 for i in range(4)) for j in range(4))
for k in range(1, 20):
    theta = F(1, 2**k)
    nearby = [[(1-theta)*G[i][j]+theta*H[i][j] for j in range(4)] for i in range(4)]
    if (all(guards(nearby)) and det(nearby) > 0
            and all(any(inv(nearby)[i][j] < 0 for i in range(4)) for j in range(4))):
        break
else:
    raise AssertionError('finite calibration failed to find a generic perturbation')

owns = list(map(F, (-2,0,3,-5)))
table, changed = {}, {}
for mask in range(1, 16):
    coalition = [j for j in range(4) if mask & (1 << j)]
    for i in range(4):
        if len(coalition) == 1:
            j = coalition[0]
            table[i,mask] = owns[i]+G[i][j]
            changed[i,mask] = owns[i]+nearby[i][j]
        else:
            table[i,mask] = changed[i,mask] = owns[i]+(i+1)*(mask-8)
assert len(table) == len(changed) == 60
assert all(table[i,1<<i] == changed[i,1<<i] == owns[i] for i in range(4))
assert all(changed[i,1<<j]-changed[i,1<<i] == nearby[i][j]
           for i in range(4) for j in range(4))
D = max(abs(1-G[i][j]) for i,j in positions)
assert max(abs(table[key]-changed[key]) for key in table) == theta*D

# Full-singular and rank-zero controls for the centered multi-affine cube.
# The analytic proof covers every singular matrix and every radius.
zero = [[F(0) for _ in range(4)] for _ in range(4)]
singular = [[F(v) for v in row] for row in
            [[0,0,1,1],[0,0,1,1],[1,1,0,1],[1,1,1,0]]]
for base in (zero, singular):
    assert det(base) == 0
    delta = F(1,16)
    values = []
    for signs in product((-1,1), repeat=12):
        vertex = [row[:] for row in base]
        for (i,j), sign in zip(positions, signs):
            vertex[i][j] += sign*delta
        values.append(det(vertex))
    assert sum(values) == 0
    assert min(values) < 0 < max(values)
print('PASS: all33 generic-line endpoint guards; product=-768')
print('PASS: zero-principal/zero-inverse calibration and literal60 reward perturbation')
print('PASS: both exact4096-vertex singular determinant cubes have zero mean and both signs')

# Complete inherited analytic sign-classification controls.
"""Exact algebra/sign-graph checks for the no-mutually-negative candidate.

Run with Python and SymPy installed. Universal Q forcing and strategic
semantics are proved in the accompanying mathematical text; finite
enumeration is a falsification aid, not the proof.
"""
from itertools import combinations, permutations, product
from collections import Counter
import sympy as sp

a,b,c,d,e,g,p,q = sp.symbols('a b c d e g p q', positive=True)
G = sp.Matrix([[0,a,-1,g],[-1,0,b,p],[c,-1,0,-e],[-1,q,d,0]])
D1,D2=a*b*c-1,c*d*g-e
assert sp.expand(G.extract([0,1,2],[0,1,2]).det()-D1)==0
assert sp.expand(G.extract([0,2,3],[0,2,3]).det()-D2)==0
assert sp.expand(G.extract([0,1,3],[0,1,3]).det()+a*p+g*q)==0
n=sp.Matrix([[b*c*q-b+d,a*c*d+c*q-1,-a*b+a*d+q]])
m=sp.Matrix([[b*e+c*d*p-d*e,b*g-d*g+p,b*c*g+c*p-e]])
assert G.extract([3],[0,1,2])*G.extract([0,1,2],[0,1,2]).adjugate()==n
assert G.extract([1],[0,2,3])*G.extract([0,2,3],[0,2,3]).adjugate()==m
assert all(sp.expand(x-y)==0 for x,y in zip(G.adjugate()[:,2],
    [-a*d*p-b*g*q-p*q,-b*g+d*g-p,-a*p-g*q,a*b-a*d-q]))
assert sp.expand(n[1]-c*n[2]-D1)==0
assert sp.expand(n[0]-b*c*n[2]-(b-d)*D1)==0
assert sp.expand(m[2]-c*m[1]-D2)==0
assert sp.expand(m[0]-c*d*m[1]-(d-b)*D2)==0

f,h=sp.symbols('f h', real=True)
H=sp.Matrix([[0,a,e,-1],[-1,0,b,g],[-f,-1,0,c],[d,-h,-1,0]])
M=sp.Matrix([[g*a,b+g*e],[c*a,c*e]])*sp.Matrix([[-f,1],[d+h*f,-h]])
assert sp.expand(M.det()-a*b*c*d)==0
assert sp.expand((sp.eye(2)-M).det()+H.det())==0
assert all(sp.expand(x-y)==0 for x,y in zip(H.adjugate()[:,1],
    [1-a*c+c*e*h,c*d*e-f,d+f*h-a*c*d,-a*f+d*e+e*f*h]))
assert sp.factor(M[1,1]+M[1,0]/(f+d/h)-a*c*d/(d+f*h))==0
A,B0,C0,D0=M[0,0],M[0,1],M[1,0],M[1,1]
chi=lambda z:(z-A)*(z-D0)-B0*C0
ell1=a*d*g/h
assert sp.factor(chi(ell1)-B0*ell1*(f+d/h-c/g))==0
ell2=c*d*e/f
assert sp.factor(chi(ell2)-(C0/f)*(ell2-(A+B0*f)))==0

I=range(4)
edges=list(combinations(I,2))
P=[tuple(x) for x in permutations(I)]
canon={
 'four_cycle':sp.Matrix([[0,1,1,-1],[-1,0,1,1],[1,-1,0,1],[1,1,-1,0]]),
 'positive_chord':sp.Matrix([[0,1,1,-1],[-1,0,1,1],[1,-1,0,1],[1,-1,-1,0]]),
 'bowtie':sp.Matrix([[0,1,-1,1],[-1,0,1,1],[1,-1,0,-1],[-1,1,1,0]]),
 'tournament':sp.Matrix([[0,1,1,-1],[-1,0,1,1],[-1,-1,0,1],[1,-1,-1,0]])
}

def reach(T,j):
 seen={j};todo=[j]
 while todo:
  k=todo.pop()
  for i in I:
   if T[i,k]<0 and i not in seen:seen.add(i);todo.append(i)
 return seen

counts=Counter()
for types in product((0,1,2),repeat=6):
 T=sp.zeros(4)
 for (i,j),kind in zip(edges,types):
  T[i,j],T[j,i]=((1,1),(-1,1),(1,-1))[kind]
 if any(all(T[i,j]>=0 for i in I) for j in I):
  counts['nonnegative_column']+=1;continue
 if all(len(reach(T,j))==4 for j in I):
  matches=[name for name,C in canon.items()
           if any(T.extract(order,order)==C for order in P)]
  assert len(matches)==1,(types,matches)
  counts[matches[0]]+=1
 else:
  terminal=[]
  for S in combinations(I,3):
   o=next(i for i in I if i not in S)
   if all(T[o,j]>0 for j in S) and any(T[i,o]<0 for i in S):
    if all(sum(bool(T[i,j]<0) for i in S)==1 for j in S):terminal.append(S)
  assert len(terminal)==1,types
  counts['terminal_triple']+=1
assert sum(counts.values())==729

R=sp.Rational
X=sp.Matrix([[0,R(5,4),R(3,2),-1],[-1,0,R(9,4),R(1,4)],
             [R(1,4),-1,0,R(1,4)],[2,-R(3,2),-1,0]])
assert X.det()==R(27,16)
assert X.extract([0,1,3],[0,1,3]).det()==-R(7,8)
assert all(z>=0 for z in X.inv()[:,1])
roots=[]
for k in (1,2,3,4):
 for S in combinations(I,k):
  B=X.extract(S,S)
  if k==1:continue
  assert B.det()!=0
  z=B.inv()*sp.ones(k,1);x=sp.zeros(4,1)
  for i,v in zip(S,z):x[i]=v
  w=X*x-sp.ones(4,1)
  if all(v>0 for v in z) and all(v>=0 for v in w):roots.append((S,x,w))
assert len(roots)==1
assert roots[0][0]==(0,2,3)
assert roots[0][1]==sp.Matrix([R(13,8),0,R(9,4),R(19,8)])
assert roots[0][2]==sp.Matrix([0,R(97,32),0,0])
print('PASS: symbolic bowtie rows/adjugate and positive-chord return identities')
print('PASS: all729 oriented/missing-edge patterns:',dict(counts))
print('PASS: exact positive-chord R0/degree-one control and forced inverse column')

# Two exact attempted falsifiers for the bowtie forcing/degree argument.
for vals,y,wanted in [
 ((R(1,2),R(1,2),R(1,2),R(1,2),R(33,64),2,R(1,2),2),
  sp.Matrix([1,1,100,1]),-1),
 ((2,2,1,R(1,2),1,1,1,1),sp.Matrix([1,1,100,1]),0)]:
 Y=G.subs(dict(zip((a,b,c,d,e,g,p,q),vals)))
 roots=[]
 for k in (1,2,3,4):
  for S in combinations(I,k):
   B=Y.extract(S,S)
   if k==1:continue
   assert B.det()!=0
   z=B.inv()*y.extract(S,[0]);x=sp.zeros(4,1)
   for i,vv in zip(S,z):x[i]=vv
   w=Y*x-y
   if all(vv>0 for vv in z) and all(vv>=0 for vv in w):
    assert all(w[i]>0 for i in I if i not in S)
    roots.append((S,x,int(sp.sign(B.det()))))
 if wanted==-1:
  assert Y.det()==-R(1,32)
  assert roots==[((0,1,2,3),sp.Matrix([R(20147,2),1612,13701,6448]),-1)]
 else:assert roots==[]
print('PASS: bowtie negative-index and mixed-passive-failure stress tests')
```

## Part V. Complete exact controls for the strict column and all-END cone

### 1. Strict-column tangent and original-reward controls

Save this complete block as a file and run it with Python 3 and SymPy.

```python
"""Exact controls for diagonal-preserving inverse-column boundary removal."""
from itertools import combinations
import sympy as s

q=s.Rational
G=s.Matrix([[0,-1,2,8],[6,0,-6,-6],[-2,2,0,-1],[-6,5,1,0]])
B=s.Matrix([[1,-q(5,18),q(29,3),-q(11,3)],
            [1,-q(2,9),q(28,3),-q(10,3)],
            [1,-q(5,9),q(34,3),-q(13,3)],
            [0,q(1,9),-q(5,3),q(2,3)]])
assert G.det()==18 and G*B==s.eye(4)
J=[j for j in range(4) if all(B[i,j]>=0 for i in range(4))]
assert J==[0] and B[0,0]>0
assert not any(all(B[i,j]>0 for i in range(4)) for j in range(4))
assert all(any(G[i,j]<0 for i in range(4)) for j in range(4))
roots=[]
quiet=[]
for size in (2,3,4):
 for c in combinations(range(4),size):
  C=list(c);O=[i for i in range(4) if i not in C]
  T=G.extract(C,C)
  assert T.det()!=0
  x=T.inv()*s.ones(size,1);w=G.extract(O,C)*x-s.ones(len(O),1)
  if all(v>0 for v in x) and all(v>=0 for v in w):
   assert all(v>0 for v in w)
   roots.append((c,x,w,s.sign(T.det())))
  if size==3 and all(v>=0 for v in T.inv()):
   if all(v>=0 for v in G.extract(O,C)*T.inv()):quiet.append(c)
assert len(roots)==1 and roots[0][3]==1 and quiet==[]
H=s.zeros(4);H[1,0]=9
assert (B*H*B)[3,0]==1
z=s.symbols('z')
Bz=B-(z*9/(1-5*z/2))*(B[:,1]*B[0,:])
assert s.simplify((G+z*H)*Bz-s.eye(4))==s.zeros(4)
assert s.simplify(Bz[3,0]+2*z/(2-5*z))==0
for eps in (q(1,100),q(1,1000),q(1,10000)):
 P=(G+eps*H).inv();N=(G-eps*H).inv()
 assert (G+eps*H).det()>0
 assert all(any(P[i,j]<0 for i in range(4)) for j in range(4))
 assert all(N[i,0]>0 for i in range(4))

# Literal original-game realization, with independent signed own levels.
owns=(-3,0,2,-7)
base={};moved={};eps=q(1,100)
for mask in range(1,16):
 coalition=[j for j in range(4) if mask>>j&1]
 for i in range(4):
  if len(coalition)==1:
   j=coalition[0]
   base[i,mask]=owns[i]+G[i,j]
   moved[i,mask]=owns[i]+G[i,j]+eps*H[i,j]
  else:
   base[i,mask]=moved[i,mask]=owns[i]+(i-2)*(mask-7)
assert len(base)==len(moved)==60
assert all(moved[i,1<<i]==base[i,1<<i]==owns[i] for i in range(4))
assert max(abs(moved[k]-base[k]) for k in base)==9*eps

# All six boundary columns are removed simultaneously, not one at a time.
T=s.Matrix([[0,-1,2],[2,0,-1],[-1,2,0]])
C=T.inv();ones=s.ones(3)
assert T.det()==7 and all(v>0 for v in C)
A=s.diag(T,T);K=s.zeros(6)
K[:3,3:]=ones;K[3:,:3]=ones
assert all(A.inv()[j,j]>0 for j in range(6))
assert all(any(A.inv()[i,j]==0 for i in range(6)) for j in range(6))
den=1-9*z*z
D=C+3*z*z/den*ones;E=-z/den*ones
Az=D.row_join(E).col_join(E.row_join(D))
assert s.simplify((A+z*K)*Az-s.eye(6))==s.zeros(6)
for eps in (q(1,10),q(1,100)):
 assert all(any((A+eps*K).inv()[i,j]<0 for i in range(6)) for j in range(6))
 assert all(v>0 for v in (A-eps*K).inv())

# The abstract lemma does not require zero diagonal in the base matrix.
Id=s.eye(3);Hid=s.ones(3)-Id
assert all((Id+q(1,100)*Hid).inv()[i,j]<0
           for i in range(3) for j in range(3) if i!=j)

# Essential-pivot negative control: R0 fails and the zeros cannot move.
a,b=s.symbols('a b',positive=True)
S=s.Matrix([[0,a],[b,0]])
assert S.inv()==s.Matrix([[0,1/b],[1/a,0]])
assert all(v>=0 for v in (s.Matrix([[0,1],[1,0]])*s.Matrix([1,0])))
print('PASS: exact Fin4 R0/degree-one boundary control and absent quiet triple')
print('PASS: exact two-sided perturbation and literal60-coordinate signed-own adapter')
print('PASS: all six boundary columns removed simultaneously; reverse direction strictly positive')
print('PASS: nonzero-base-diagonal positive control and missing-positive-pivot negative control')
```

### 2. Weight-cone, complete-graft and original-SUM controls

Save this complete block as a file and run it with Python 3 and SymPy.

```python
"""Exact controls for the one-column weighted all-END source reduction.

No positive-A game is asserted. A and M in cone tests are conditional source
parameters. Complete finite-law controls test the actual full-cap identities.
"""
from fractions import Fraction as Q
from itertools import product
import sympy as s

matrices = [
    s.Matrix([[0,-9,-6,7],[-6,0,4,7],[7,8,0,-1],[-1,-3,9,0]]),
    s.Matrix([[0,3,-1,-1],[3,0,-1,-1],[-1,-1,0,3],[-1,-1,3,0]]),
]

def rational(a):
    return Q(int(s.numer(a)), int(s.denom(a)))

for number,G in enumerate(matrices):
    B=G.inv()
    carrying=[h for h in range(4) if all(v>0 for v in B[:,h])]
    assert carrying==([2] if number==0 else [0,1,2,3])
    if number==0:
        assert G.det()==7345
        assert B*7345==s.Matrix([[516,-405,777,524],[-391,435,308,-454],
                                 [-73,100,189,723],[484,645,558,36]])
    for h in carrying:
        v=B[:,h];lam={};direction={}
        assert v[h]>0
        for j in range(4):
            if j==h:continue
            w=B[:,j]
            L=max(abs(w[i])/v[i] for i in range(4))
            lam[j]=1/(2*(1+L))
            direction[j]=v+lam[j]*w
            assert all(direction[j][i]>v[i]/2 for i in range(4))
            target=s.zeros(4,1);target[h]=1;target[j]=lam[j]
            assert G*direction[j]==target
        smallest=min(lam.values())
        # These are arbitrary positive conditional source constants; the
        # tested matrices are not claimed to have a positive-A completion.
        for A,M in [(s.Rational(1,100),s.Integer(10)),
                    (s.Integer(1),s.Integer(10)),
                    (s.Integer(8),s.Integer(1))]:
            assert 0<A<=8*M
            c=(A/(28*M))**4
            eps=c*smallest/4
            t0=eps*A/32
            assert 0<c<1 and 0<eps<1
            for bits in product((0,1),repeat=4):
                theta=[(eps/2 if bits[i]==0 else eps) if i==h else 1+bits[i]
                       for i in range(4)]
                Theta=sum(theta)
                assert t0*Theta/min(theta)<=A/2
                for active in product((0,1),repeat=4):
                    if all(active):continue
                    if not active[h]:
                        x=v
                    else:
                        missing=next(j for j in range(4) if not active[j])
                        x=direction[missing]
                    image=G*x
                    # N_i>=c: this is a valid upper bound on the left side
                    # of the necessary graft inequality for EVERY N.
                    left=sum(theta[i]*max(image[i],0)/c
                             for i in range(4) if active[i])
                    right=sum(theta[i]*image[i] for i in range(4))
                    assert left<right
                    assert right+t0*Theta*sum(x)>right
print('PASS: every deficient END set contradicts the exact cone inequality; full weight boxes.')

# Independent exhaustive finite-law identities: all 60 native coordinates,
# arbitrary signed participant/higher values, empty gaps and literal Never.
G=matrices[0]
native={}
for mask in range(1,16):
    for i in range(4):
        if mask&(mask-1)==0:
            j=mask.bit_length()-1
            native[i,mask]=rational(G[i,j])
        else:
            native[i,mask]=Q(((mask*(i+3)+i)%11)-5,3)
old=[{0:Q(1,7),2:Q(2,7),None:Q(4,7)},
     {0:Q(1,3),2:Q(1,6),None:Q(1,2)},
     {0:Q(1,5),2:Q(1,5),None:Q(3,5)},
     {0:Q(2,9),2:Q(1,3),None:Q(4,9)}]
tail=[{0:Q(1,8),1:Q(1,4),None:Q(5,8)},
      {0:Q(1,6),1:Q(1,3),None:Q(1,2)},
      {0:Q(1,4),1:Q(1,8),None:Q(5,8)},
      {0:Q(1,3),1:Q(1,6),None:Q(1,2)}]
def payoff(table,laws):
    out=[Q(0)]*4
    for draw in product(*(tuple(law) for law in laws)):
        mass=Q(1)
        for i,d in enumerate(draw):mass*=laws[i][d]
        finite=[d for d in draw if d is not None]
        if not finite:continue
        first=min(finite)
        mask=sum(1<<i for i,d in enumerate(draw) if d==first)
        for i in range(4):out[i]+=mass*table[i,mask]
    return out
def state(table,laws):
    last=max(d for law in laws for d in law if d is not None)
    U=payoff(table,laws);caps=[];end=[]
    for i in range(4):
        replies=[]
        for d in tuple(range(last+2))+(None,):
            replacement=list(laws);replacement[i]={d:Q(1)}
            replies.append(payoff(table,replacement)[i])
        caps.append(max(replies));end.append(replies[-1])
    return U,caps,[law.get(None,Q(0)) for law in laws],end
joined=[]
for i in range(4):
    law={d:p for d,p in old[i].items() if d is not None}
    for d,p in tail[i].items():
        key=None if d is None else d+4
        law[key]=old[i][None]*p
    assert sum(law.values())==1
    joined.append(law)
U,B,N,e=state(native,old)
u,b,n,eq=state(native,tail)
Un,Bn,Nn,en=state(native,joined)
nu=Q(1)
for z in N:nu*=z
for i in range(4):
    H=nu/N[i]
    assert Un[i]==U[i]+nu*u[i]
    assert Bn[i]==max(B[i],e[i]+H*b[i])
    assert Nn[i]==N[i]*n[i]
    assert en[i]==e[i]+H*eq[i]
theta=[Q(1,97),Q(2),Q(3,2),Q(1)]
t=Q(1,113)
raised={(i,m):theta[i]*(native[i,m]+t) for i in range(4) for m in range(1,16)}
for laws in (old,tail,joined):
    Un,Bn,Nn,en=state(native,laws)
    Ur,Br,Nr,er=state(raised,laws)
    survival=Q(1)
    for z in Nn:survival*=z
    for i in range(4):
        assert Ur[i]==theta[i]*(Un[i]+t*(1-survival))
        assert Br[i]==theta[i]*(Bn[i]+t)
    assert sum(Br[i]-Ur[i] for i in range(4))==(
        sum(theta[i]*(Bn[i]-Un[i]) for i in range(4))+t*sum(theta)*survival)
print('PASS: entire finite response menus, exact independent graft, actual row raise and full SUM ledger.')

H=s.ones(4)-s.eye(4)
assert H.det()==-3
assert all(H.adjugate()[i,j]!=0 for i in range(4) for j in range(4))
assert all(H.extract([i for i in range(4) if i!=k],
                     [i for i in range(4) if i!=k]).det()==2 for k in range(4))
print('PASS: generic native-slice perturbation endpoint witnesses.')
```
