# Weighted collision dominance produces stationary uniform equilibria

This packet gives a stationary equilibrium producer from explicit raw-data
inequalities and excludes an entire asymptotic region of reward space.
It is ordinary mathematics, not checked in Lean. Fin4 remains open.

## 1. Raw criterion

Let I have n>=2 players. Nonempty first-quitting coalitions D pay r(D), while
live play and literal AllNever pay zero. Strategies use private independent
behavioral randomization and unilateral replacements are unrestricted.
Define kappa_i=r_i({i}), Z_i(D)=r_i(D)-kappa_i on NONEMPTY coalitions only,
and Gamma_ii=0, Gamma_ij=Z_i({j}). Fix this singleton matrix. Choose an
active set S subset I with m=|S|>=2, and put T=I\S. Require Gamma_SS to be
invertible. Choose a nonempty recipient set J subset S and signs sigma_i
in{-1,1}, i in J, for which

    v_i=sigma_i Gamma_SS^(-1)e_i>0 entrywise,
    Gamma_TS v_i>0 entrywise if T is nonempty.        (1)

These are finite singleton-matrix tests. When S=I only the first test is
needed. The full matrix Gamma need not be invertible when S is proper, and
no condition is imposed on unused inverse columns. For a nonsingleton D put

    d_D=|D|-1>=1,
    eps_iD=1 if i belongs to D, and -1 otherwise.

Let P be the finite set of favorable coordinate positions

    P={(i,D):i in J, D subset S, |D|>=2}.

For (i,D) in P put a_iD=eps_iD sigma_i Z_i(D). Define

    G=max_((i,D) in P) [(a_iD)_+]^(1/d_D),
    B=max( { [(-a_iD)_+]^(1/d_D):(i,D) in P }
           union { |Z_i(D)|^(1/d_D):(i,D) outside P, |D|>=2 } ).

Empty maxima are zero. These are explicit finite reward-table quantities.
Positive favorable participant rewards and negative favorable passive
rewards have opposite signs because they enter stationary comparison with
opposite signs.

**Theorem.** There are constants L0<infinity and c>0, depending only on
Gamma,S,J,sigma, such that

    G>=L0,                  B<=c G                  (2)

implies an exact terminal Nash equilibrium supported exactly on S: players
in S use constant hazards strictly between0 and1, and players in T Never.
Its actual payoff is a uniform-equilibrium payoff against unrestricted
behavioral deviations, with the
same profile working at every accuracy. The original kappa_i may be
arbitrary independently, and L0,c are independent of them.

The constants can be chosen uniformly when Gamma ranges over any compact
set of zero-diagonal matrices on which Gamma_SS remains invertible and all
strict inequalities in(1) hold, with S,J,sigma fixed. There is no assumption
about relative sizes of favorable coordinates, their coalition sizes, or a
nondegenerate selected equilibrium root.

In particular, if every unfavorable reward is fixed and at least one
favorable reward tends to infinity in weighted scale, all sufficiently
large members have exact stationary equilibrium. Any number of favorable
coordinates may diverge simultaneously, at arbitrary different rates.

## 2. Exact scale expansion

For stationary hazards q_-i let

    H_i(q)=product_(j!=i)(1-q_j),
    Q_i(q)=sum_(S subset opponents) Pr_q(S) Z_i(S union{i}),
    P_i(q)=sum_(nonempty S subset opponents) Pr_q(S) Z_i(S),
    F_i(q)=(1-H_i(q))Q_i(q)-P_i(q).

The own native singleton is zero. In original rewards the kappa_i terms
cancel exactly in F_i. If opponents are proper, F_i=0 is the equality
between Quit now and the stationary Never value.

Assume G>0, set t=1/G, and write q_j=t z_j for j in S and q_j=0 for j in T.
Thus z has only S coordinates. For (i,D) in P define

    A_iD=t^(d_D)(a_iD)_+,
    E_iD=-eps_iD sigma_i t^(d_D)(-a_iD)_+.

At every other nonsingleton coordinate define E_iD=t^(d_D)Z_i(D).
Then the actual collision reward is exactly

    Z_i(D)=t^(-d_D)(eps_iD sigma_i A_iD+E_iD) if (i,D) in P,
    Z_i(D)=t^(-d_D)E_iD otherwise.

The favorable coefficients satisfy0<=A_iD<=1 and max A_iD=1. If c<=1,
condition B<=cG gives |E_iD|<=(c)^(d_D)<=c.

For each (i,D) in P define a positive homogeneous polynomial on the strict
positive orthant of R^S:

    m_iD(z)=(sum_(j in S\{i})z_j) product_(j in D\{i})z_j if i in D,
    m_iD(z)=product_(j in D)z_j                    if i outside D.

Its degree is |D|, between2 and m. Embed z by zero off S when evaluating F.
The exact finite polynomial expansions are

    F_S(tz)/t=-Gamma_SS z
       +sum_((i,D) in P) sigma_i A_iD m_iD(z)e_i+R_S(t,z,A,E),
    F_T(tz)/t=-Gamma_TS z+R_T(t,z,E).                (3)

The remainders are polynomial and, on every fixed compact z-set,

    ||R_S||_infinity+||R_T||_infinity<=C(t+||E||_infinity)      (4)

uniformly for0<=A_iD<=1 and small t,E.

For completeness, a favorable participant reward contributes

    sigma_i A_iD [(1-H_i(tz))/t]
       product_(j in D\{i})z_j
       product_(j in S\D)(1-tz_j)

to F_i(tz)/t. The quotient (1-H_i(tz))/t is polynomial with constant term
sum_(j in S\{i})z_j. A passive favorable reward has sign -sigma_i and contributes

    sigma_i A_iD product_(j in D)z_j
       product_(j in S\(D union{i}))(1-tz_j).

Their t=0 terms are exactly those in(3). Singleton passive terms give the
specified -Gamma blocks plus O(t). All outside-recipient collision entries
belong to E. A bad participant coordinate involving an inactive recipient
still has a polynomial expansion: its t^(-(|D|-1)) cancels the |D|-1
opponent factors, and the additional1-H_i contributes a factor t before
division by t. If another inactive label belongs to D its contribution is
zero. Passive coordinates have |D| opponent factors before division by t.
Thus no E term has a negative power of t. This proves(3)--(4), including the
inactive rows, for mixed coalition sizes and all relative growth rates.

Multiply the first line of(3) by Gamma_SS^(-1). The exact active equation is

    z=T_A(z)+E_t(z),
    T_A(z)=sum_((i,D) in P) A_iD m_iD(z) v_i,
    E_t(z)=Gamma_SS^(-1)R_S(t,z,A,E).                (5)

The perturbation has the bound in(4), with another constant. All vectors
v_i are strictly positive.

## 3. One compact cone for every favorable coefficient array

Write s_i=sum_j(v_i)_j>0 and w_i=v_i/s_i. Set

    eta=min_(i in J,j in S)(w_i)_j>0.

If T is nonempty, put

    gamma_out=min_(i in J,k in T)(Gamma_TS w_i)_k>0,
    M_out=max_(k in T) sum_(j in S)|Gamma_kj|.

For empty T set gamma_out=1 and M_out=0, and omit all outside constraints.
Use the compact convex angular set

    K={x in R^S: sum_j x_j=1, x_j>=eta/2,
                    Gamma_TS x>=gamma_out/2 when T nonempty}.

It is nonempty because it contains every w_i. For positive z and every
favorable coefficient array A with max A=1, T_A(z)>0 and

    T_A(z)/sum_j(T_A(z))_j belongs to conv{w_i:i in J}.

Thus the normalized image lies strictly within every displayed constraint
of K. Zero coefficients and changes of which coordinate realizes max A
cause no difficulty.

On K all m_iD(x) are positive. Explicit common bounds are
m_-=(eta/2)^m and m_+=1. Let s_-,s_+ be the minimum and maximum of the s_i,
and let N=|P|. For0<rho<=1 and rho>=1, respectively,

    sum T_A(rho x)/rho <= N s_+ m_+ rho,
    sum T_A(rho x)/rho >= s_- m_- rho.

Every degree is at least2, and at least one A_iD equals1. Choose

    rho_-=min(1/2,1/(8N s_+)),
    rho_+=max(2,8/(s_- m_-)),
    gamma0=s_- m_- rho_-^m.

Then uniformly over x in K and A,

    sum T_A(rho_- x)<=rho_-/4,
    sum T_A(rho_+ x)>=4rho_+,                        (6)
    sum T_A(rho x)>=gamma0 for rho in[rho_-,rho_+].

Choose

    delta=min(eta gamma0/8,rho_-/(8m),rho_+/(2m),
              gamma_out gamma0/[8(m+1)max(1,M_out)]).

An entrywise perturbation of T_A of size at most delta preserves positivity,
the strict inner/outer radial inequalities, and normalized image in K.
For coordinates, eta<=1/m gives perturbed normalized values at least3eta/5.
For the outside constraints, writing H=sum T_A>=gamma0, normalized-vector
error is at most2(m+1)delta/H in sup norm, hence its image under Gamma_TS
changes by at most gamma_out/4. These estimates follow directly by bounding
the perturbed denominator below H/2. Thus each outside constraint stays
strictly above gamma_out/2 as well.

There are finite constants C0,CE,D0,DE with

    ||E_t||<=C0 t+CE||E||,
    ||R_T||<=D0 t+DE||E||

on the compact annulus. If T is empty take D0=DE=0. For rational Gamma the
constants are computable by finite rational arithmetic: the errors have
form t R0(t,z,A)+sum E_iD R_iD(t,z); bound them on0<=t<=1,
0<=z_j<=rho_+,0<=A_iD<=1 by sums of absolute polynomial coefficients
times rho_+ to the total z degree. Define tau=rho_- gamma_out/4 and take

    c=min(1,delta/[4max(1,CE)],tau/[4max(1,DE)]),
    t0=min(1,1/(2rho_+),delta/[4max(1,C0)],tau/[4max(1,D0)]).

Then0<t<=t0 and||E||<=c imply||E_t||<=delta/2 and||R_T||<=tau/2.
All constants depend only on the fixed singleton data and S,J,sigma.
No polynomial elimination or unproved numerical root search is needed for
these explicit sufficient constants.

## 4. Radial Brouwer produces the active root and quiet inequalities

Put T=T_A+E_t and S(z)=sum T(z). On the compact convex product
[rho_-,rho_+] times K consider

    (rho,x) -> (clamp_[rho_-,rho_+](2rho-S(rho x)),
                 T(rho x)/S(rho x)).               (7)

The preceding estimates make this a continuous self-map. Brouwer gives a
fixed point. It cannot have rho=rho_-, because S(rho_- x)<rho_- makes the
first output strictly larger than rho_-. It cannot have rho=rho_+, because
S(rho_+ x)>rho_+ makes that output strictly smaller. Thus rho is interior,
and the first fixed-point equation forces S(rho x)=rho. The second then
gives z=rho x=T(z). Equation(5) yields F_S(tz)=0 exactly.
For an inactive recipient k, the angular constraint and the remainder bound
in(3) give

    F_k(tz)/t<=-rho_- gamma_out/2+tau/2<0.

Each active z_j>=rho_- eta/2>0 and z_j<=rho_+, so active q_j=t z_j lies
strictly between0 and1; set the other hazards to0. Since |S|>=2, every player
still has a proper opponent. Taking L0=1/t0
proves the raw root producer in Section1. It does not require a nonzero
Jacobian determinant or isolated roots; degeneracies among simultaneous
large-reward directions are included.

For a compact varying singleton set satisfying(1) with S,J,sigma fixed,
the principal inverses are bounded, the normalized selected columns have a
common positive coordinate bound, and their outside images have a common
strict positive bound when T is nonempty. The displayed formulas and compact
polynomial estimates therefore give common rho_-,rho_+,delta,t0,c. The
angular set K may depend on Gamma; its shared margins are uniform. This proves the asserted uniformity.

## 5. Full behavioral and uniform-horizon consumer

Fix the produced stationary q. Every player has proper opponents. Put

    U_i=P_i/(1-H_i).

The active equalities give Q_i=U_i for i in S; the quiet inequalities give
Q_i<=U_i for i in T. Hence P_i+H_i U_i=U_i always, and every prescribed
positive quitting hazard is indifferent. The actual prescribed terminal
payoff is U by the first-step identity and vanishing survival remainder.
Every forced finite quitting date pays at most U_i, while literal Never
pays exactly U_i. A complete unilateral behavioral replacement is a mixture
of these responses along the unique surviving live history, so cannot
improve. In original units every terminal payoff gains exactly kappa_i,
because absorption occurs almost surely even after a replacement. This is
exact terminal Nash against all behavioral deviations.

For each i, absorption under any replacement is bounded by the geometric
opponents-only clock with success probability1-H_i>0. Thus one finite
expected absorption-time bound holds uniformly over every replacement.
If R bounds original absolute rewards, the difference between terminal
payoff and horizon-T average payoff is at most2R times this bound divided
by T. Consequently the same stationary profile yields a uniform-equilibrium
payoff at the one fixed target kappa+U. Neither the target nor the profile
changes with accuracy.

## 6. What this changes in an asymptotic partition

Fix one of the support/column choices above and a compact singleton set.
For a sequence of tables with G→infinity
and B/G→0, all sufficiently late members have UE. More quantitatively, a
hypothetical counterexample with G>=L0 must satisfy B>cG. Thus favorable
large rewards alone cannot support an escaping counterexample sequence;
one unfavorable coordinate must remain comparable in weighted scale.

Equivalently, normalize each collision reward of coalition size k by
G^(-(k-1)). The coefficient arrays lie in a finite-dimensional compact cube
when B/G is bounded. The closed favorable face (all unfavorable normalized
coordinates zero, at least one favorable coordinate one) has one uniform
UE collar for sufficiently small t=1/G. The proof covers that entire face,
including all relative-size and support-switch boundaries. Its constants
are uniform on compact singleton cells satisfying the selected support tests.

This is not an exhaustive partition. Unfavorable dominant coordinates and
singleton matrices approaching singular or inverse-column boundaries remain.
In particular, normalizing the whole reward table into a compact cube does
not supply a uniform version near those singleton boundaries. The criterion
is a proved raw-data exclusion, not a claim that all remaining chambers admit
a continuation selection.

### 6.1. A finite explicit active-set atlas in Fin4

For four players only the full set and the four three-player subsets can
pass the matrix test. A one-player principal block is zero; a nonsingular
two-player zero-diagonal matrix has zero diagonal in its inverse, so none
of its signed columns is strictly positive. For each remaining S, inspect
every principal inverse column. There is at most one sign making that
column strictly positive; retain it only if its outside image is also
strictly positive. Every nonempty subset J of retained columns gives one
raw weighted-dominance test. This is a finite procedure, with at most
4(2^3-1)+(2^4-1)=43 recipient-subset tests for a fixed singleton matrix;
usually many are absent. It includes both reward signs and strict outside
cones, not just the full-support positive-column case.

The sufficient regions are semialgebraic in the raw rewards. All constants
in Section3 use finite rational operations, absolute values and finite
minima or maxima of singleton-matrix rational functions. The weighted scales
require only finitely many positive integer powers after sign cases are
fixed. More concretely, at rational input choose a favorable coordinate g
of degree d maximizing g^(1/d), by comparing g^(d') with (g')^d. The test
G>=L0 is g>=L0^d; for every bad magnitude b of degree d', the test B<=cG is

    b^d <= c^(d d') g^(d').

These are exact rational comparisons. Singular blocks and failed strict
sign tests are simply discarded. Thus this is an explicit finite raw atlas,
not a requirement to run an unspecified polynomial elimination procedure.
One may disjointify its overlapping successful regions by choosing the
first successful test in any fixed order.

The complement remains an unresolved region. The atlas makes no assertion
that every table, every strict-column singleton cell, or every asymptotic
direction passes one test. Boundary columns with a zero coordinate or zero
outside image are not silently included in the strict tests. The substantive
exclusion is the produced UE region and its uniform projective collar;
the finite enumeration does not itself close the remaining Fin4 cases.

## 7. A complete separating family

The original rewards below have all own-singleton levels4. Fix L>=2.
The two growing coordinates are r0(023)=L^2 and r0(0123)=L^3.

| D | r0 | r1 | r2 | r3 |
|---|---:|---:|---:|---:|
|0|4|6|6|3|
|1|7|4|2|2|
|2|3|5|4|5|
|3|7|1|3|4|
|01|-1|-1|4|4|
|02|-1|4|26|4|
|03|27|4|4|-1|
|12|4|25|-1|4|
|13|4|-1|4|22|
|23|4|4|-1|-1|
|012|-1|-1|-1|4|
|013|-1|-1|4|-1|
|023|L^2|4|-1|-1|
|123|4|-1|-1|-1|
|0123|L^3|-1|-1|-1|

The singleton matrix and inverse are

    Gamma=[0,3,-1,3;2,0,1,-3;2,-2,0,-1;-1,-2,1,0],
    Gamma^(-1)=(1/25)[8,5,9,3;3,5,-6,-2;14,15,-3,24;10,0,5,10].

Choose S=I,J={0} and sigma0=1. Then v0=(8,3,14,10)/25>0 and

    G=max(23,sqrt(L^2-4),(L^3-4)^(1/3)), B=22.

In particular G>=L/2 for L>=2. The raw criterion therefore applies for
L>=max(2,2L0,44/c). It produces full-support stationary UE for the entire
large-L tail, independently of whether one can solve its stationary
polynomials explicitly.

### 7.1. Every sure-owner continuation is excluded

Let successor be the cycle0->2->1->3->0. A pair consisting of an owner i
and its successor pays owner i=-1 and the successor its singleton payoff
at i plus20. Every other pair participant receives-1. Every triple/grand
participant except recipient0 in023 and0123 receives-1. Every
nonparticipant reward, including singleton rewards, is at least1.

At any root with a sure quitter i, a nonsuccessor j other than0 must Continue:
joining gives-1 for every coalition that can occur, while continuing gives
at least1. This argument is independent of all continuation values.
For sure i=1 it first forces player2 off; for sure i=2 it forces player3
off. In either case both growing recipient0 rewards become impossible.
Joining by0 then gives-1 while continuing gives at least1, so0 also stays
off. For sure i=0, players1,3 are off directly; for sure i=3, players1,2
are off directly. Thus in every case only i and successor(i) can quit.

The successor strictly prefers Quit by20, so quits surely. The owner then
gets-1 but obtains its positive singleton payoff at its successor by Continue.
This contradicts its optimality. Hence there is no root with a sure quitter
that is Nash at ANY continuation vector, for any L>=2. This excludes the
complete sure-owner selection and its punishment-tail consumers.

### 7.2. Every proper child has an unsafe exact equilibrium

For every nonempty proper child C, some d in C has its successor outside C.
Let only d quit at date0 surely and let all other child players Never.
Each other child player is a nonsuccessor of d; its singleton payoff is at
least1, while joining pays-1. Neither growing coordinate can occur under a
single child's unilateral deviation, since it would require at least three
quitters. Player d gets4, compared with Never0. These are full behavioral
exact child equilibria with zero joint Never mass and zero child debts.
The absent successor gains exactly20 by joining at date0. Thus no proper
child satisfies a universal outsider-gain bound by child debts plus bounded
joint-Never slack. No choice among proper children repairs this failure.

### 7.3. Complete anchor, weight and trap comparisons

The positive singleton graph of Gamma is strongly connected. Thus any
closed marked set for the ordered nonpositive-anchor criterion is all
players. Its first nonempty block B cannot contain successor(i) without i:
coalition{i,successor(i)} would first meet B only at its successor, whose
native participant reward is positive. Hence B is predecessor-closed under
the cycle and equals all players. Positive block weights would require

    22w2<=5w0, 21w1<=5w2, 18w3<=5w1, 23w0<=5w3.

Their product would give22*21*18*23<=5^4, which is false. This tests every
block order and every positive weighting.

For a nonzero nonnegative recipient weight vector, the sum of the four
supportwise forced-Quit native upper averages at singleton coalitions is

    13w0+11w1+12w2+8w3>0.

Thus no weight makes all four averages nonpositive. Every strict positive
participant premium for0 requires player3, including the two growing
coordinates; for3 it requires1, for1 it requires2, and for2 it requires0.
Consequently the only nonempty premium trap is the full set, and its
singleton upper-charge test fails by the same displayed weight inequality.
The growing rewards do not remove any of these obstructions.

### 7.4. Singleton degree and other complete raw selectors

Every singleton column contains a negative entry. The principal pair
determinants, in order01,02,03,12,13,23, are

    -6,2,3,2,-6,1.

The principal triple determinants, in order012,013,023,123, are10,-3,5,8;
det Gamma=25. Thus Gamma is R0: a complementary nonzero nonnegative vector
with support at least2 would lie in a nonsingular principal kernel, while
singleton support is ruled out by the negative entry in its column.

At standard-LCP offset1, the only possible vector for an active support C
is z_C=-Gamma_CC^(-1)1. The complete nontrivial support census is

| C | z_C | exclusion |
|---|---|---|
|01|(-1/2,-1/3)|negative coordinate|
|02|(-1/2,1)|negative coordinate|
|03|(1,-1/3)|negative coordinate|
|12|(1/2,-1)|negative coordinate|
|13|(1/2,1/3)|omitted row2 residual-1/3|
|23|(-1,1)|negative coordinate|
|012|(-7/10,-1/5,2/5)|negative coordinate|
|013|(-7,4,-13/3)|negative coordinate|
|023|(-1,-2,-1)|negative coordinate|
|123|(3/8,-1/4,1/4)|negative coordinate|
|0123|(-1,0,-2,-1)|negative coordinate|

Singleton supports cannot solve their zero-diagonal active equation. Hence
the empty support is the only root and has index+1, giving actual R0 degree1.
The nonunit-degree producer therefore does not cover this family.

Column2 of Gamma inverse is(9,-6,-3,5)/25, so the wholly positive-inverse
and signed-all-column criteria fail under every relabeling and sign choice.
The only principal triple with nonnegative inverse is023, whose outside
inverse row is(-3,6,2)/5. The complete passive-child inverse selector fails.
The unique mutually positive singleton pair01 intersects the unique
mutually negative pair13, excluding signed-cycle templates requiring them
disjoint. All three pair partitions fail a required nonnegative joining
increment:01|23 gives-8 at recipient0,02|13 gives-4 at recipient0, and
03|12 gives-4 at recipient3. The only compatible attached-negative-pair
labeling is(3,1,0,2), where its required nonnegative premium is Z1(13)=-5.
The alternative allowing both such premiums arbitrary requires Gamma21>=0,
whereas Gamma21=-2.

For every ordered recipient/partner pair(i,p), choose j different from
both i,p and predecessor(i). Then its pair joining native payoff for i is-5
and Gamma_ij>=-3. The necessary zero-partner lower-face difference is at
most-2. This excludes every partner choice for the crossed-face guard.
None of the two growing entries changes these pair comparisons.

A relabeling or positive row scaling preserving the displayed singleton
matrix is trivial: its unique row with two equal positive entries fixes0,
that row's sign fixes2, and the remaining signs fix1,3; its nonzero entries
then force all row scales to1. More directly, EVERY recipient has a positive
native participant pair: Z0(03)=23, Z1(12)=21, Z2(02)=22, Z3(13)=18.
Under any relabeling and positive row scaling, no player therefore satisfies
the seven nonpositive participant caps required of the passive outer player
in the compared nonstationary core families. This also excludes their
version with variable singleton entries; no singleton-rigidity assumption
is needed for that comparison.

### 7.5. Increment over previous large-coordinate producers

The radial argument for a wholly positive inverse already handles different
coalition sizes and one positive participant pole per recipient. This proof
does not present that fixed-point mechanism as new. Its new hypotheses use
only selected signed strict columns, allow passive poles, allow any number
of growing coordinates per recipient, and include all zero-coefficient and
relative-size boundaries through max A=1. The weighted-dominance collar
also allows unfavorable coordinates at a common small fraction of that scale.

Here the inverse is not wholly positive, so the all-recipient positive-
inverse producer does not apply. The single-coordinate signed or boundary-
column producer allows bounded residuals, or residuals of order M^(1/d)
for one selected coalition of size d+1 and pole magnitude M. Choosing the
triple pole M=L^2 leaves grand reward L^3, outside every such fixed O(L)
box. Choosing the grand pole M=L^3 leaves triple reward L^2, also outside
every fixed O(L) box. No other coordinate grows. Thus changing the designated
pole does not supply this comparable multi-coordinate family. No large
passive coordinate is present for the passive-pole producers.

These comparisons concern the specified complete sufficient selectors.
They do not assert absence of stationary equilibria: the new raw criterion
produces those equilibria. The increment is an explicit previously
unproduced raw asymptotic class, not a stronger equilibrium statement on
an already supplied stationary witness.

### 7.6. Proper active sets cover mixed full inverse columns

The same singleton matrix gives another exact scope test. On S={0,2,3},

    Gamma_SS^(-1)=(1/5)[1,3,1;1,3,6;2,1,2],
    Gamma_1S Gamma_SS^(-1)=(-3,6,2)/5.

Thus J={2,3}, sigma2=sigma3=1 satisfies(1), despite both corresponding FULL
inverse columns having mixed signs. The theorem applies to arbitrary
simultaneous favorable rewards in these two recipient rows on coalitions
contained in023, with unfavorable weighted scale bounded as in(2), and
produces a stationary equilibrium with player1 quiet. A full passive-child
criterion requiring the entire outside inverse row nonnegative fails at
its first coordinate. The chosen-column inequalities are sufficient here.

There is also a negative signed example: on S={1,2,3},

    -Gamma_SS^(-1)e2=(3/8,3/4,1/4)>0,
    Gamma_0S(-Gamma_SS^(-1)e2)=9/8>0.

Consequently large negative participant rewards, or large positive passive
rewards, in recipient2 on this active set are included. These tests show
that the proper-support version is not just notation for a strictly
positive column of the full inverse. Neither test asserts exhaustive
coverage of all signs or all coalitions on the reference singleton table.

## 8. Actual-data adapter, sources and limits

The input is the singleton matrix, an active set, selected signed strict
columns of its principal inverse with positive outside images, and G,B. All strategic objects are produced:
the finite coefficient array, compact cone and radial barriers, a fixed
point of the exact active field, strict quiet-player inequalities, and the
stationary private hazards. No
continuation, root, target or response optimizer is assumed.

The semantic declarations matching the output are
`isZeroAsymptoticNash_stationary_of_fixedPoint_endpointNash_contracts` and
`isUniformEquilibriumPayoff_of_stationaryEndpointCertificate_contracts`
(`UniformEquilibrium/Quitting/Stationary/EndpointCompiler.lean`). The general
positive endpoint is
`quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors`
(`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`).
The index convention used above is the support determinant sign in
`exists_finset_r0Degree_eq_sum_sign_det`
(`MathUE/LinearProgramming/R0DegreeSum.lean`).
Section5 supplies its own unrestricted behavioral and horizon proof; these
citations identify existing consumers, not new Lean verification.

The formalization targets are the exact mixed-size participant/passive
expansion, compact cone for selected principal columns and outside guards, radial clipped Brouwer
lemma with uniform coefficient support switches, computable polynomial
error bounds, and the raw weighted-scale adapter. All threshold choices
are independent of the original own-singleton levels. The result rules
out the favorable projective face and one collar; it does not decide the
remaining unfavorable directions, singular singleton limits, either
arbitrary-game global-minimum branch, or Fin4.
