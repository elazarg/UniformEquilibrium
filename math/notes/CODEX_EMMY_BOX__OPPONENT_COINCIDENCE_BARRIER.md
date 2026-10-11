# Opponent-coincidence barriers and a cubic moment obstruction

Status: INTERNAL ordinary mathematics and exact rational computation, not
Lean checked or independently reviewed. No positive invariant barrier,
unrestricted positive gap, uniform equilibrium, or new solved raw class is
claimed. The completed calculation in Section4 excludes EVERY cubic
polynomial potential for one explicit actual table, not merely a selected
cubic ansatz. A separate ten-edge certificate does the same even with
EVERY endpoint nonnegative and in the convex hull of actual terminal
rewards. Neither certificate is a chronological cycle or an independent-law
realization. Section3.3 gives a separate ordinary necessary-mode proof:
on the paired singleton matrix, sufficiently small FULL regret forces a
macroscopic root at uniformly positive original joint reach, even when the
suffix hazards are arbitrary. This is not an exact-Nash compactness theorem.
The actual all-degree/barrier question remains open.

## 1. Exact negative-endpoint question

Let I=Z/4Z, with independent private stopping clocks and unrestricted
complete behavioral replacements. Live and Never pay0. Fix K>=1 and define
the ORIGINAL finite reward table as follows:

    singleton{i}: 1 to i, 4 to i+2, 0 to both other players;
    adjacent pair{i,i+1}: -1 to i, 2 to i+1, 1 to both outsiders;
    opposite pair: 0 to both members, 1 to both outsiders;
    triple: -1 to its three members, K to its outsider;
    grand coalition: K-1 to every player.                 (1)

The main explicit test is K=10, whose reward bound is10. The change from
the earlier negative-grand stress test is substantive: ALL four passive
triple rewards and ALL four grand rewards grow together. It is not a
one-column change that zero upper-average weights can ignore.

Question. Does this actual table admit a closed full payoff/cap barrier
containing the all-Never semantic pair and invariant under EVERY product
root, with a uniform strictly positive maximum full debt? Equivalently,
can one construct a polynomial P on[-12,12]^4 with strictly charged drift
on the ENTIRE robust forward relation, not just one root orbit?

For a root q let a=1-product_i(1-q_i). At continuation v put

    alpha_i=product_(j!=i)(1-q_j),
    Q_i=E[r_i(B union{i})],
    B_i=E[r_i(B)*1_(B nonempty)],
    C_i=B_i+alpha_i*v_i,
    u_i=q_i*Q_i+(1-q_i)*C_i.                             (2)

The full exact relation requires u_i>=Q_i,C_i for every player. A robust
edge additionally permits errors bounded by tau*a, with BOTH endpoints
inside the fixed cube. A negative certificate must obey

    P(v)-P(u)>=a                                        (3)

for every such edge at one tau>0. Exact positive-charge edges are therefore
necessary tests at every tolerance.

Declarations inspected: `IsQuittingFloorFreeRobustEdge` and
`QuittingRobustChargedEdge` in
`UniformEquilibrium/Quitting/Projective/RobustChargedRelation.lean`, and
`quittingGame_not_exists_uniformEquilibriumPayoff_iff_noSureRoot_and_rationalPotential`
in `UniformEquilibrium/Quitting/Projective/PolynomialForwardCertificateCharacterization.lean`.
They retain the whole boxed source/root/target relation. The present note
does not restrict it to actual-payoff annotations or a Nash selection.

## 2. Exact first screens; not an unrestricted gap argument

Each player i can be punished to full cap0 by making successor i+1 Quit0
and all other opponents Never. Quit0 gives-1; every later deadline and
Never gives0. Thus the table is normal with cap infimum<=0<=own singleton1,
and has a positive singleton.

There is NO full exact root with any sure quitter, for ANY continuation.
If i is sure, its opposite i+2 has joining-minus-Continue difference-4
when neither other nonowner quits, -2 when one does, and -1 when both do.
It therefore strictly Continues. The predecessor i-1 then strictly
Continues as well. The successor i+1 joins for2 instead of0. Owner i
receives-1 and would withdraw for0. This covers all free probabilities,
not just pure coalitions.

The singleton comparison matrix is

    Gamma=[0,-1,3,-1; -1,0,-1,3; 3,-1,0,-1; -1,3,-1,0],
    det Gamma=45,
    Gamma^-1=(1/15)*[2,3,7,3;3,2,3,7;7,3,2,3;3,7,3,2].  (4)

It is R0 with degree1. At offset ones the strictly complementary roots
are: the empty root, four adjacent-pair roots with both active entries1,
and four triple roots obtained by rotating(1/2,5/2,1/2,0). Their indices
are respectively+1, four copies of-1 and four copies of+1. All active
principal blocks are invertible; axis R0 solutions fail a negative external
entry. The local index convention is the sign of the principal determinant,
not that sign multiplied by support parity. Every deleted triple inverse
has a negative diagonal entry. These are limited source screens, NOT a
completed census of all existing producers on(1).

The only premium trap is all4: a proper trap would have to be closed under
the directed cycle of participant rewards2. For K>2 the grand forced-Quit
premium is K-2 at every recipient, so every nonzero nonnegative upper-average
weighting fails. For the full trap, the literal boxed coefficients are

    singleton: P=-2, L=-3;
    pair:      P=-4, L=-4;
    triple:    P=K-2, L=-1.

At K=10 they force d<=2,g<=3,ell<=1,tau>=8, hence the boxed charge is at
most4*sqrt(2/8)*(3+2/8)=13/2, below4+4K=44. Thus that boxed sufficient
predicate also fails. These failures are not evidence of no UE.

### Every stationary exact Nash component is excluded

The sure case was excluded above. Zero active players leave Quit gain1.
With one active i, successor i+1 has Never value0 and Quit0 value1+q_i.
With two opposite active players, either Never value is4 and Quit value
is at most1. With two adjacent active players the successor again has
Never value0 and strictly positive Quit value.

For three active players rotate so q=(a,b,c,0). Active endpoint identities
are unchanged by K:

    Q0=1-2b-c+bc, B0=(4-3b)c, 1-alpha0=b+c-bc,
    Q1=1+a-2c-ac, B1=ac,      1-alpha1=a+c-ac.

Stationary indifference for player0 implies Q0>0, b<1/2 and c<1/4,
because (5/2)c<B0=Q0*(1-alpha0)<(1+c)/2. But player1 has
Q1>1/2 while B1/(1-alpha1)<=c<1/4, a contradiction.

For full support put z_i=q_i/(1-q_i)>0, x_i=z_(i-1),y_i=z_(i+2),
w_i=z_(i+1), L_i=x_i+y_i+w_i, T_i=x_i*y_i+x_i*w_i+y_i*w_i,
V_i=x_i*y_i*w_i and A_i=L_i+T_i+V_i. The numerator of Quit is

    P_i=1+2*x_i-w_i-T_i+(K-1)*V_i,

and the numerator of one-date Continue absorption is

    N_i=4*y_i+T_i+K*V_i.

Stationary indifference would force F_i=N_i*(1+A_i)-P_i*A_i=0. However

    sum_i F_i = sum_i z_i + Q(z)
      +sum_i[(K-1)*V_i+3*T_i*(2*y_i+w_i)+2*T_i^2
               +V_i*(-x_i+5*y_i+2*w_i)+3*T_i*V_i+V_i^2],

    Q(z)=2*sum_i z_i^2+(z0-z2)^2+(z1-z3)^2
                                   +7*sum_i z_i*z_(i+1).

Every term is nonnegative after combining2*T_i^2-x_i*V_i: its six
monomial coefficients are2,2,2,3,4,4. Also sum z_i>0. Thus all F_i
cannot vanish for ANY K>=1. This does not imply positive stationary
infimum, an unrestricted gap, or no nonstationary equilibrium.

An early alternative using a cyclic rather than opposite singleton favorite
was discarded immediately: its R0 degree is-1, so the existing singleton
degree theorem already solves every completion. No negative claim is
retained for that discarded table.

## 3. An exact opponent-coincidence ledger

For independent clocks T_i in Nat union{Never}, let p_S be the terminal
coalition probabilities and rho the joint-Never mass. Define

    E_i=sum_t product_(j!=i)Pr(T_j=t),
    G=p_I,
    C_i=E_i-p_(I\{i})-G>=0.                            (5)

Here E_i is the probability that ALL three opponent clocks coincide at a
finite date, even if i has already stopped the actual game. C_i is exactly
the probability that i strictly preempts such a later coincidence. These
counterfactual events matter to the full Never cap.

Under prefixing ANY product root q, with joint survival c0 and deleted
survival alpha_i, direct clock-law multiplication gives

    E_i'=product_(j!=i)q_j+alpha_i*E_i,
    G'=product_j q_j+c0*G,
    p_(I\{i})'=(1-q_i)*product_(j!=i)q_j+c0*p_(I\{i}),
    C_i'=alpha_i*C_i+q_i*alpha_i*(p_(I\{i})+G).           (6)

These are universal-prefix identities, not selected-root identities.
On a terminal coalition containing i, replacing i by Never gains4 for an
opposite pair, gains1 for its outgoing adjacent pair, loses2 for its incoming
adjacent pair, gains2 for a triple, and gains1 for the grand coalition.
On a solo-i event the gain is at least-1, with an extra K on the C_i
subevent. Terminal events not containing i are unchanged. Therefore the
actual unrestricted debts satisfy

    sum_i D_i >= K*sum_i C_i+rho+5*G+7*sum_(|S|=3)p_S
                              +9*sum_(S opposite pair)p_S-1.       (7)

In particular full gap<=epsilon implies sum_i C_i<=(1+4*epsilon)/K.
This is an honest necessary low-debt constraint. It does NOT make the
triple or grand probabilities vanish at fixed K, and does not close an
invariant barrier. Opponent-coincidence coordinates cannot simply be
replaced by actual terminal triple probabilities.

### 3.1. A nonlinear independent-law constraint and its limited force

For distinct i,j let A=I\{i,j}. Actual independent clocks satisfy

    E_i*E_j<=G+C_i+C_j,
    p_(I\i)*p_(I\j)<=G*p_A+C_i+C_j.                  (7a)

These are ordinary exact inequalities, not assertions that the attainable
law set is convex. To prove the first, expand E_i*E_j as a double sum over
dates t,s. The t=s terms are

    sum_t p_i(t)*p_j(t)*(product_(k in A)p_k(t))^2<=G.

For t<s, sum the first triple's factor over t, bounding its two shared
atom factors by1. This contribution is at most
sum_s Pr(T_j<s)*product_(k!=j)p_k(s)=C_j. The s<t terms similarly give C_i.
For the second inequality use
p_(I\i)(t)=Pr(T_i>t)*product_(k!=i)p_k(t). The off-diagonal estimates only
improve; its diagonal summand is exactly G(t)*p_A(t), and summing is at
most G*p_A. All sums are nonnegative, so the proof applies to infinite
laws and positive Never masses by monotone summation.

For example C=0 and G=0 imply that at most ONE counterfactual triple
coincidence E_i is positive. More generally, if C=0 and G>0, every triple
or grand coincidence must occur at one common date t0, with no player's
finite atom strictly before t0. Indeed a positive grand atom at t0
makes ANY later triple coincidence preempted by its excluded player's
positive t0 atom. A triple coincidence earlier than t0 similarly preempts
one of the grand event's deleted triple coincidences. Two different grand
dates are covered by the same argument. This is an exact zero-C boundary
description, not a fixed-K low-regret classification: (7) only gives
C=O(1/K), not C=0 as regret tends0 at the fixed table K=10.

### 3.2. Coincidence/order data alone do not preserve FULL caps

Even the complete joint weak ordering of the four prescribed clocks does
not determine full deviation caps on the integer calendar. In this ACTUAL
table take T1 uniform on{0,1} and let the other three clocks be Never.
Player0 has prescribed payoff0. Its deadline0 payoff is0, deadline1
payoff-1/2, and every later deadline and Never payoff0. Thus its FULL cap
is0. Change ONLY T1 to uniform on{0,2}. Every terminal coalition mass,
prescribed payoff, E_i,C_i,G and the joint clock weak ordering is unchanged.
But deadline1 now gives player0 payoff1/2. Its full cap is1/2.

The same effect occurs near the K=10 low-debt search, not only in this
high-debt calibration. The exact twelve-date profile and independent
integer cap checker in `CODEX_NASH_BOX__DIRECT_EXISTENCE_BEYOND_TEMPORALIZATION.md`
Section24 and `../experiments/CODEX_NASH_BOX__FINITE_CLOCK_JOINT_APPROXIMATION.py`
give maximum full regret63609521374809/10^16. Insert one all-zero date
immediately after date0, shifting every old finite date>=1 up by1 and
leaving Never fixed. The exact same checker gives maximum full regret

    2107022933400569/5000000000000000 > 2/5,

attained by player1's new deadline1. Prescribed payoffs and ALL ordering
and coincidence data remain identical. This computation was rerun in
exact integers/Fractions; it is not a claim about the optimizer's global
minimum. It rules out charging this cap increase solely to a change in
terminal law, coincidence counts, or clock-order probabilities: those
changes are exactly zero.

Conversely, deleting globally empty dates is a sound operation: it preserves
the independent prescribed payoff and cannot INCREASE any full cap. Every
compressed pure deadline lifts to the original date with the same position
against all opponents; Never lifts to Never, and arbitrary mixed replies
are averages. This does not justify inserting dates, coalescing nonempty
dates, or replacing source-specific menus by a common dense calendar.

A contemplated probability-quantile coarsening is not new: the actual
full-cap theorem `hasEscapeAwareQuantileClockCompressionAtBound`
(`UniformEquilibrium/Quitting/Paths/CommonQuantileClockTransport.lean`)
already controls both payoffs and unrestricted caps. The selected finite
source `exists_fin4_finiteClockStoppingLaws_exploitability_le`
(`UniformEquilibrium/Quitting/Paths/QuantitativeFiniteClockSource.lean`)
approximates the UNKNOWN global infimum, not zero. No new producer or
barrier follows by rebuilding that compression.

### 3.3. Macroscopic activity cannot first occur at vanishing joint reach

This is a separate ordinary proof, not independently checked or a positive-gap
barrier. It strengthens the all-small-conditional-hazard exclusion in
`CODEX_TURING_BOX__STATE_INFORMATION_AND_RELAXATION.md` Section25.3 in one
specific way: the first macroscopic root occurs at uniformly positive
ORIGINAL joint reach. It does not transport a cap to a different calendar.

Keep the singleton matrix R=I+4P, where P exchanges opposite mates, but
allow ANY collision rewards of absolute value at most M, M>=4. Let q_i(t)
be an actual independent profile's conditional hazards, J_t its joint
survival before date t, and eta its maximum FULL unrestricted regret. Put

    delta=1/(10000M),       kappa=1/(1000000M).

Claim. If eta<=kappa/2, some finite date t satisfies

    J_t>kappa,             max_i q_i(t)>delta.          (7b)

Thus every full-regret-zero sequence has a macroscopic conditional root
at nonvanishing joint reach. At that date some ORIGINAL unconditional
private atom is larger than kappa*delta. This is a necessary profile-mode
condition, not an equilibrium producer or an unrestricted gap bound.

Proof. Replacing one's private Never branch by a late deadline gives
limiting gain equal to joint Never mass, because own singleton is1 and
all finite opponent tails vanish. Hence J_infinity<=eta. Suppose(7b)
fails. There is a finite first T with J_T<=kappa, since
J_infinity<=eta<kappa. Every date t<T then has all q_i(t)<=delta.
Future hazards AFTER T remain completely arbitrary.

Write v_t for the ACTUAL conditional prescribed tail value, Q_it for
Quit-now value, C_it for Continue-now value. The following estimates use
only legal complete unilateral laws, without replacing the actual suffix:

    v_ti=q_i(t)Q_it+(1-q_i(t))C_it,
    J_t(Q_it-v_ti)<=eta,
    sum_window J_t*q_i(t)*(v_ti-Q_it)_+<=eta.           (7c)

For the last inequality, suppress one's quitting exactly at dates of a
finite window with C_it>Q_it, retain its old hazards elsewhere, and then
revert to its ACTUAL suffix. Finite Bellman telescoping gives gain
sum J'_t*q_i(t)*(C_it-Q_it)_+, where J'_t>=J_t. This implies(7c).

Set h_it=-log(1-q_i(t)), h_t=sum_i h_it, s_t=sum_(u<t)h_u.
On the prefix t<T one has h_t<=5delta and J_t=exp(-s_t). Let T0 be
the first date with s_T0>=1; it exists and T0<=T. Every endpoint up to
T0 has J_t>=1/4. Interpolate the v_t linearly in hazard time s, and put
a_i=h_it/h_t on each positive cell. Ignore zero cells. On[0,1], elementary
logarithm/exponential bounds and the exact payoff recursion give

    v'=v-Ra+e,  a>=0, sum a=1, ||e||_infinity<=50Mdelta,
    v_i>=1-tau, tau=4Mdelta+4eta,
    integral_0^1 (v-1) dot a <=20eta+48Mdelta.         (7d)

Here |Q_it-1|<=4Mdelta; one-date simultaneous stopping mass is at most
(3/2)delta*sum_i q_i(t); and the exact cell endpoint increment satisfies
||v_(t+1)-v_t||_infinity<=4M h_t. These facts plus(7c) give(7d).
They do NOT require small hazards after T.

The missing sum-of-values estimate is obtained by accounting separately
for that arbitrary suffix. Conditional on ANY used endpoint t<=T0,
first collision BEFORE T has probability at most2delta: at each prefix
date collision probability is at most2delta times absorption probability,
so summing against reach telescopes. First absorption AT/AFTER T has
probability at most J_T/J_t<=4kappa. Conditional Never mass is at most
4eta. Every singleton reward sums to5, whereas every coalition reward
sum has absolute value at most4M. Consequently

    |sum_i v_i-5|<=sigma,
    sigma=20eta+12Mdelta+21Mkappa.                    (7e)

This estimate, preserved by interpolation, is the essential finite-prefix
repair. Merely assuming small hazards on the initial hazard-time interval
would not justify it; a far enough reached cutoff is needed.

For completeness the quadratic contradiction is retained. Put g=v-1,
A=I-4P, W=g^T A g, x=g+tau*1>=0. For nonnegative x of mass L,
-(3/2)L^2<=x^T A x<=L^2, and

    W=x^T A x+6tau*sum x-12tau^2.

The stated constants imply tau<=.0008, sigma<=.0033,
sigma+4tau<=.0065, hence everywhere -1.6<=W<=1.1 and ||g||_1<=1.05.
Using AR=-15I and A1=-3*1 gives the exact derivative

    W'=2W-6*sum g+30g dot a+2g^T A e.

Equations(7d),(7e) imply

    W(1)-W(0)<=-3.8+6sigma+600eta+2040Mdelta
               <=-3.5162<-2.7,

contradicting the range of W. This proves(7b).

Conditional use and exact remaining seam. Matching the original prefix
before s, then making any complete replacement, shows that the actual
tail's full regret is at most eta/J_s. Whenever eta/J_s<=kappa/2, the
same conclusion applies to that tail, with relative reach kappa.
For an approximate-equilibrium sequence, condition at the dates in(7b)
and shift those actual tails to0. Their full regrets still tend0, and some
date0 hazard stays above delta. Independence survives this product
conditioning. This does NOT give an actual exact Nash limit: subsequent
calendar intervals and finite mass can escape to infinity. Nor does it
justify deleting a diffuse interval between successive macroscopic roots;
Section3.2 shows why preserving prescribed ordering is not enough.

## 4. Complete cubic exclusion by ten rational exact edges

For the ACTUAL table K=10 there is NO real polynomial P of total degree
at most3 satisfying(3) on the full exact-root relation in[-12,12]^4.
Consequently none can be a full robust potential at any positive tolerance.
This includes nonsymmetric cubics, repeated-coordinate monomials and all
indefinite quadratic terms.

The finite exact certificate is in the owned script
`CODEX_EMMY_BOX__CUBIC_FORWARD_MOMENT_CHECK.py` in this same directory.
Run from the repository root:

    python math/notes/CODEX_EMMY_BOX__CUBIC_FORWARD_MOMENT_CHECK.py

It uses only SymPy rational arithmetic, no numerical solver or floating
sign decision. The ten explicit roots and source values are:

| j | q | v |
| --- | --- | --- |
| 1 | (0,7/10,9/10,0) | (12,-8,17/3,-12) |
| 2 | (7/10,7/10,0,0) | (-4/3,17/3,12,-48/5) |
| 3 | (0,0,0,1/40) | (41/39,261/130,38/39,1) |
| 4 | (1/2,1/10,0,7/10) | (136/27,-11,12,-2/3) |
| 5 | (0,1/2,0,7/10) | (6,-25/3,52/5,-3) |
| 6 | (7/10,7/10,0,0) | (-4/3,17/3,0,0) |
| 7 | (1/1000,0,0,0) | (1,12,12,12) |
| 8 | (1/10,0,0,0) | (1,11/9,17/10,8/9) |
| 9 | (0,0,7/20,0) | (21/130,6/13,1,399/130) |
| 10 | (9/10,0,0,7/10) | (17/3,12,-12,-8) |

For each row the script evaluates Q,B,alpha and u from the literal raw
table, checks active indifference and EVERY quiet player's inequality,
checks both endpoint boxes and positive charge. Thus these are edges of
the FULL exact relation, not active-subgame roots.

Let Phi comprise the nine nonconstant C4 orbit sums of monomials of degree
at most3: sum v_i, sum v_i^2, adjacent products, opposite products,
sum v_i^3, the two oriented adjacent v_i^2*v_j sums, opposite v_i^2*v_j,
and the triple-product sum. These span all C4-invariant cubics modulo
constants. Form the rational9-by10 matrix

    D[:,j]=Phi(v_j)-Phi(u_j).

Its exact rank is9 and its one-dimensional kernel has a vector lambda
with EVERY entry strictly positive. The script prints the exact rational
vector normalized by lambda10=1 and checks D*lambda=0 exactly. The total
weighted positive charge is

    77872576233168050991164281026022599715552505550085470964665074033343823371
    /14344375045173165129962149927920047050365817799481764900337940459932640

which is strictly positive. If a C4-invariant cubic obeyed(3), multiplying
its ten edge inequalities by lambda and summing would give0>0. For an
arbitrary cubic average it over the four label rotations. Table(1), the
cube and the FULL exact relation are rotation invariant, so the averaged
cubic would still obey(3), giving the same contradiction.

This is an exact computer-assisted ordinary certificate, not a Lean proof
or an independently reviewed result. It establishes no higher-degree
exclusion. The balanced feature moments are NOT a chronological cycle:
there is no claim that an endpoint u_j equals another source v_k, or that
these ten unrelated edges can be concatenated into a packet.

### A rejected numerical inference

A numerical attempt to remove the three-active edge produced an invalid
quiet-player root. It clipped a required quiet continuation19 to the box
boundary12 at q=(9/10,0,0,0), giving Quit1.9>Continue1.2. Exact root
checking rejected it. Moving that value to19 made the edge legal on a
larger cube but destroyed the claimed positive moment balance. No
two-active-only cubic exclusion, arbitrary higher-completion exclusion,
or all-degree consequence is claimed from that failed attempt.

### 4.1. Nonnegative endpoints inside the actual reward hull

Shrinking the auxiliary cube does not rescue the cubic mechanism. For the
same K=10 table there is NO cubic charged potential even for the restricted
FULL exact edges with BOTH endpoints in

    Delta={v>=0: sum_i v_i<=99/10}.                     (8)

Delta lies in the convex hull of actual finite rewards and0: if j is the
outsider of a triple, that reward is11*e_j-ones and the grand reward is
9*ones; their weights9/10 and1/10 give(99/10)*e_j. This is a convex-hull
outer constraint only. No convexity of attainable independent payoff laws
is assumed, and no independent realization of these sources is claimed.

Here is complete rational data for the second certificate. Divide each q
entry by1000 and each f entry by10. For each player put x=q_(i-1),
y=q_(i+2),w=q_(i+1) and

    alpha=(1-x)*(1-y)*(1-w),
    Q=12*w*x*y-w*x+w*y-2*w-2*x*y+x-y+1,
    B=4*y-3*x*y-3*y*w+x*w+11*x*y*w,
    h=(Q-B)/alpha.

Set v_i=h if q_i>0; otherwise set l=max(0,h) and
v_i=l+(10-l)*f_i. Entries f_i at active players are unused.

| Row | q numerators | f numerators |
| --- | --- | --- |
| 1 | (0,0,16,10) | (1,0,0,8) |
| 2 | (0,0,156,87) | (2,0,8,5) |
| 3 | (0,100,218,0) | (1,10,4,1) |
| 4 | (0,0,293,85) | (2,0,8,3) |
| 5 | (436,0,0,516) | (10,1,0,6) |
| 6 | (0,426,442,0) | (1,3,4,1) |
| 7 | (0,52,188,18) | (2,6,3,3) |
| 8 | (169,0,175,0) | (3,3,2,2) |
| 9 | (273,0,0,146) | (0,1,1,4) |
| 10 | (175,136,157,133) | (10,8,9,9) |

The same exact script independently enumerates all raw opponent coalitions
and checks EVERY root inequality, both Delta memberships and positive
charge. Its nine-feature difference matrix again has rank9 and a
one-dimensional kernel whose ten coordinates are strictly positive.
The normalized positive weights are computed in exact rational arithmetic;
their approximate sizes are(52620,2518,594,361,76,643,500,2.78,2403,1).
No floating-point decision enters the certificate. Thus the same moment
argument excludes every C4-invariant cubic. Delta and the relation are
rotation invariant, so averaging the polynomial excludes EVERY cubic.
Only the polynomial is averaged, never the players' independent clocks.

For comparison, every FULL exact root target always satisfies
u_i>=Q_i>=-1, even for an arbitrary auxiliary source. Therefore the earlier
negative source coordinates could only be entrances, not an exact cycle
wholly made of those targets. The new certificate shows that eliminating
those entrances, imposing nonnegativity, and imposing linear terminal
reward feasibility STILL do not supply a cubic potential. It does not
exclude higher-degree potentials, actual payoff/cap barriers, or UE.

## 5. Bounded falsification by a previously successful calendar

The numerical diagnostic
`CODEX_EMMY_BOX__K10_RETURN_CONTINUATION.py` tests the old59-root twisted
return against table(1), rather than assuming that a successful negative-grand
calendar fails at K=10. Its adjacent-pair roots do not depend on K. At a
consecutive-triple root with hazards(a,b,c), only the quiet recipient's
actual value changes: its additional stopping payoff is(K-1)*a*b*c, and
its grand Quit endpoint changes by(K+9)*a*b*c relative to the old table.
Both changes are included in the script; all quiet inequalities are checked.

Experiment, not proof. Starting at K=1, continuation with increments.01
keeps the original support word legal until one newcomer hazard crosses0
near K=1.94. Replacing just that root, index20 T3, by its adjacent-pair
face P3 yields a numerically legal return at K=2, with starting value

    (1.0872918830338,2.2401722986377,.7245417553426,.8559738604894).

The changed word remains numerically legal at K=2.12, starting at

    (1.0883323385124,2.2415201012085,.7212227974483,.8569386807795).

The minimum active hazard there is about.001766 and the minimum quiet
gap about.008704, but the smallest singular value of the four-dimensional
return Jacobian is about.0002094. Newton continuation fails at K=2.121.
This is compatible with a fold of the chosen branch, but establishes
neither a fold theorem nor absence of another return. No K=10 equilibrium,
positive gap, or whole-support exclusion follows. The bounded test is
stopped here instead of interpreting one failed word as an actual-law
barrier. The exact cubic result in Section4 is independent of this experiment.

Reproduction from math/: `python notes/CODEX_EMMY_BOX__K10_RETURN_CONTINUATION.py
--step .01 --stop 2.13` (one shell line). At its failed2.13 step the script
also reports the previous2.12 Jacobian singular values and tries the
finer2.121 step, reproducing the diagnostic just quoted. NumPy is required;
these finite-difference/Newton calculations are numerical only.

## 6. Current boundary and next mathematical question

The apparent artificial restriction tested here is that the first permitted
polynomial degree, three, might already describe a global obstruction.
For this explicit actual table it cannot: a finite collection of FULL
exact edges defeats every cubic. This is stronger than a sampled failure of
one ansatz, but weaker than a global obstruction or an existence theorem.

The opponent-coincidence ledger provides additional actual-law information
that a payoff-only cubic does not capture. The concrete next question is
whether(6),(7), together with independent-law constraints, supports a closed
positive-debt invariant set under EVERY product root. The gap is exactly
that(7) alone permits compensating solo/adjacent-pair mass, and the finite
moment circulation in Section4 has no concatenation or independence
purification theorem. Raising the polynomial degree without resolving one
of those structural seams is not yet a new mechanism.
