# A sharp choice of dates on a three-player cycle with a fourth observer

Let r be any finite four-player quitting game, live and Never zero. Set
s_i=r_i({i}), Gamma_ij=r_i({j})-s_i with Gamma_ii=0, and
J_ij=r_i({i,j})-s_i for i≠j. Suppose 0,1,2 form a cyclic triple.
In cyclic order p,j,n, the successive movers are p then j then n. Use
a_j=-Gamma_pj>0, b_j=Gamma_nj>0. Write o=3 for the outsider. Suppose

    lambda=product_j a_j / product_j b_j <1.

Set L_0=1 and L_(j+1)=(a_j/b_(j+1))L_j for each successive phase,
so L_(j+3)=lambda L_j. Repeat all labels modulo three and define

    A_j = [sum_{m>=j} L_m Gamma_o,m]/L_j,
    B_j = [sum_{m> j} L_m Gamma_o,m]/L_j = A_j-Gamma_oj.

These geometric sums are three-term expressions divided by 1-lambda.
In each phase put a=a_j, b=b_j, P=J_pj, N=J_nj, D=J_oj,
A=A_j, B=B_j. Define eta=1 for N<=b, eta=b/N for N>b, and
t_*=max(P,0)/(a+max(P,0)). If, in every phase,

    A<0 implies P<=0 and D eta<=A,
    B<0 implies N<=b and D<=A+(max(P,0)/a) B,                     (T)

then there is one uniform-equilibrium payoff of r against every
unilateral behavioral replacement. The 20 raw entries on coalitions of
size at least three, all passive pair rewards and all off-schedule joining
entries are unrestricted. All own singleton levels are arbitrary. Conditions
(T) are necessary and sufficient for an arbitrarily accurate calendar
obtained by subdividing these particular three cyclic phases independently.
A different calendar is permitted by the broader game.

## Proof

Normalize total exit mass to one by dividing all lengths by sum_m L_m.
On the absorption interval belonging to phase j the sole possible quitter
is j and t denotes the fraction of the phase's mass already used. If the
next date spends Δ in that phase (0<Δ<=1-t), set the hazard equal to
L_j Δ / S, where S is the remaining total mass from this date, in the same
units as L. Any finite subdivision of a cycle repeated each three phases
is an actual periodic independent hazard profile. The limiting conditional
value times S is the sum of all remaining singleton columns weighted by
their remaining masses. In the native coordinates, the active j's value
is zero. The predecessor's, successor's and outsider's respective
unnormalized values divided by L_j are

    a t,        b(1-t),        w(t)=A(1-t)+Bt.

For the core these identities follow from L_(j+1)/L_j=a_j/b_(j+1) via
backward summation, with zero terminal mass. The latter follows immediately
from the definition of the geometric tail. At every date the mover is
indifferent between quitting for zero and continuing. Every quiet player's
forced quit offer times S/L_j is its relevant pair joining reward times Δ.
Consequently the only local requirements are

    P Δ<=a t,    N Δ<=b(1-t),    D Δ<=w(t).                        (1)

When A,B>=0 use arbitrarily fine equal-mass substeps. All cap violations
in these units are at most M times the mesh with M bounding the absolute
joining rewards. When A<0<=B take steps Δ=eta(1-t). The first two inequalities
hold by definition and P<=0, and the third holds since
D eta(1-t)<=A(1-t)<=w(t). For eta=1 this is just one step. Otherwise close
the infinitesimal remaining mass after finitely many steps by one final step,
with cap error O(remaining mass). When A>=0>B, use a final step 1-t_* from
t_*. Conditions (T) give its three comparisons, using w(t_*)/(1-t_*)=
A+max(P,0)B/a. If P<=0 there is nothing else to do. If P>0, before t_*
use Δ=(a/P)t. Its third comparison holds for 0<=t<=t_* by affinity, since
it holds at 0 and t_*; the first is equality, and the second uses N<=b and
Δ<=1-t. Design this geometric mesh backwards from t_* toward zero, add one
initial step tending to zero, and truncate. The error on that first step
is O(mesh) since all three endpoint floors are nonnegative there. If both
A,B<0 then P<=0,N<=b,D<=A suffice for the single whole step.

The conditional error at each date is O(mesh). The ratio L_j/S is uniformly
bounded even at the end of any phase by the positive next-phase length.
Continuing coincides with prescribed value at every date for every player.
Following any finite deadline thus loses at most the positive conditional-cap
error of that single deadline, and follows exact Continue identities until
then. The opponent-survival factor after a cycle is bounded away from one
for every player, independently of subdivision, since at least two other
core owners' phase aggregates are positive (or all three if the deviator is
the outsider). Thus Never also satisfies the bound, as does any mixture of
deadlines. Prescribed and all deviating laws absorb almost surely, restoring
the row offsets. The finite cycle length at each accuracy and the geometric
survival bound give the usual uniform terminal-to-finite-average reduction.
The target is s plus the normalized singleton column sum from the first date,
fixed before accuracy and independent of subdivision.

Conversely, on the first cycle all opponent survival probabilities and S/L_j
are bounded below uniformly in the cuts; S/L_j is also bounded above. Because
the native incumbent always Continues indifferently where it mixes, its gain
from any pure deadline equals the signed date-cap excess times survival to
that date against the opponents. Consequently vanishing regret requires each
inequality (1) up to a uniform o(1) error. If A<0, the first positive step
must have nonvanishing length, D<0, P<=0, length at most eta+o(1), and
D eta<=A in the limit. If B<0 the terminal step must have nonvanishing length
(since forced joining would otherwise cost o(1) at a negative continuation).
Writing its initial point as t, we must have N<=b in the limit and
t>=t_*-o(1). The ratio w(t)/(1-t)=A+B t/(1-t) is decreasing. The final
comparison therefore gives the asserted maximum admissible D. No inference
about optimality outside these cyclic calendars enters the proof.

## Calibration and comparison

Take the matrix

    Gamma=[0,-1,2,-3; 2,0,-1,1; -1,2,0,-3; -3/2,-1/2,7/2,0].

The core lengths are L_(j+1)=L_j/2, hence A=(−1,1,3), B=(1/2,3/2,−1/2).
For a concrete completion use additive passive rewards sum Gamma_ij
over the quitting opponents and joining reward k_i times this sum,
where k=(-1,-1,0,2/3), except set J_21=1/100 and J_20=-1/100. Take all s_i=1.
Then P,N,D in phases 0,1,2 respectively are (-1/100,-2,-1),
(1,1/100,-1/3), (1,-2,7/3). Phase 0 is a single whole date,
phase 1 is arbitrarily fine, and phase 2 meets (T) since 7/3<3-1/2
and t_*=1/2. No fully fine calendar on this core works because A_0<0.
No fully coarse calendar on this core works because P_2>0 and the forced
quit of the zero predecessor then gains 1 in the normalized phase units.
Even any uniformly bounded number of cuts in phase 2 leaves a positive
regret gap: the first positive cut in any finite limiting subdivision faces
P>0 at t=0. The comparison is under every cyclic rotation.

From the opening of phase 0, the probabilities of singleton quitters
0,1,2 are (4/7,2/7,1/7). The original uniform payoff on the marked table
is therefore (1,2,1,1/2). Within this cycle the number of dates required
per period is of order log(1/epsilon). In phase 2 the predecessor comparison
for an epsilon-equilibrium gives Delta<=t+C epsilon with a fixed C by
the survival bound in the necessity proof. Starting at zero, after n
steps the mass used is at most C epsilon(2^n-1). Conversely, in phases
1 and 2 use an initial step of length 2^(-n), then steps Delta=t up to
t=1/2 and a final step of length 1/2. In phase 1 the outsider comparison
holds throughout since D<0 and both endpoints are positive; in phase 2
the decreasing-endpoint construction above applies. The first steps
cost O(2^(-n)) and phase 0 takes one date.

The full determinant is 91/2, and Gamma^-1 has strictly positive
columns 1 and 3. In deletion order 0,1,2,3 the passive triple inverse
rows are (-57,-8,-10)/11, (2/3,-1,-2/3), (-1/9,-10/3,-34/9) and
(3/2,-1/2,1/2). No passive-row consumer applies to any triple.
The mixed graph is the diamond with arcs 1 to 2, 2 to 0 and 3,
and 0 and 3 to 1. The missing 03 pair is mutually negative. Thus no
negative-chord Hamilton cycle exists and the no-mutually-negative
criterion fails. Every pair partition has a strictly negative joining gap
because 03 is the only mutually negative singleton pair and the modified
entries preserve the signs of their joining gaps. Thus the disjoint-pair producer
does not apply. Pair 12 has positive participant premiums (1,1/100) and
opposite joining gaps (2,-199/100). This is the opposed-edge arm of the
coverage map, outside its supportwise Low/Charge/Orientation and paired
assignment admission. The shared-anchor rectangle requires negative joining
gaps on its unique positive edge, also impossible. The table is outside
the common-factor additive class. The native payoff vector at coalition
13 is (-4,-1,-1,-1/3), strictly negative in every row. Hence every
nonnegative normalized ledger fails the proper-coalition sign H_a(13)>=0,
including every weight and marked set in the marked-support orientation
ledger theorem.

The hull and first-action adapters of payoff-domain orientation both
fail at the opposed pair 12. Put c=1/10000 and u=c Gamma_.0. This is
in the native reward hull with u_2=-c<0. It is also in the first-action
outer domain N1: set q_0=1/10 and q_1=q_2=q_3=0. The forced offers are
(0,-1/5,-1/1000,-1/10)<=u, with equality on the active row. The passive
floor vector is m=(-4,-3,-4,-2), giving P_i+m_i H_i equal respectively
to (-4,-5/2,-37/10,-39/20)<=u. At positive odds z_2=c,
z_1=100c/199 on support 12, both forced-Quit numerators are positive
and Phi_12=(2c,-c) is the projection of u. The orientation sign is
det D Phi_12=199/50>0, violating the required weak sign in both domains.

The two-unrestricted-row theorem also misses this table for every role
assignment. Its scheduled comparison (2) requires both free owners h,k
to have nonnegative joining gaps as seen by a. The only possible
(a,b;h,k) are (3,2;0,1), (2,1;0,3), (0,2;1,3). For these choices,
respectively, the following rational hazards violate comparison (1).
The coordinates of x are h,k and of y are h,k followed by the other
scheduled owner. A_e,B_e use that theorem's definitions.

    (a,b;h,k)   e       x             y           A_e        B_e
    (3,2;0,1)   3     (1/4,0)    (0,1/8,1/8)    13/1024   -19/1024
    (2,1;0,3)   1     (0,1/2)    (0,0,1/2)       5/8       -5/8
    (0,2;1,3)   2     (1/2,0)    (0,0,3/4)     993/1600   -1579/3200

There is no stationary equilibrium or genuine sure-quitter head on
the marked table. Here is a common rational exclusion certificate. Write
b=Gamma q and theta=(q_1-q_0)(1-q_3)/100. The passive numerator is
b_i and the forced Quit offer is k_i b_i+1_{i=2}theta. At a nonzero
stationary equilibrium the Never value is b_i/(1-H_i) when the opponents
have positive hazard and H_i is their joint probability of continuing.
Comparison gives b_i>=0 if i is quiet, b_i=0 if proper, and b_i<=0
if sure, with tolerance |theta| on row 2 only. If only i is active then
b_i=0 already. Scale the entire vector by its largest hazard to put
one coordinate at one. The tolerance in the scaled necessary signs is
at most 1/100 since |theta|<=max(q)/100. All Never itself fails since s_i=1.

For a sure-quitter head, every owner facing a sure opponent compares the
same two offers with H_i=0. If 3 alone is sure then
b_0=-q_1+2q_2-3<0 forces 0 also sure. If the sole sure owner is i=0,1
or 2, its punishment tail has native cap at least zero for owners 0,1,
using the fixed absorbing hazard 1/(1-k_i), and at least -1/100 for
owner 2 by quitting immediately. Comparing the sure owner's Quit against
Continue then gives b_i<=0 with a row-2 tolerance of at most 2/100.
These comparisons are valid for the original signed rewards because
all three security strategies absorb.

An exact enumeration uses a word in Q,A,S for a quiet, proper or sure
owner, with at least one S. Set q_Q=0, q_S=1 and allow 0<=q_A<=1.
Write d>=0 for the row-2 tolerance. For each row require
z b_i <= 1_{i=2} d for z=-1 on Q, z=1 on S, and both on A.
Of the 65 words, only the following six systems are feasible for
any d. Their minima are, in order,

    word    QSAQ    QSSQ    ASAQ    SQQS    SQAA   SQAS
    min d      2       2     7/4       4    13/7      4.

These numbers can be checked by the following finite rational recipe.
After substituting q_Q,q_S the unknowns are (q_A,d). Append the box and
d>=0 to the signed inequalities above. For every subset of |A|+1
inequalities with invertible coefficient matrix, solve the corresponding
equalities, discard infeasible vertices and take the smallest last
coordinate. The feasible polyhedron is pointed and d is bounded below,
so this lists every finite minimum. Since 2/100<7/4, all cases fail.

Every nonsingleton principal of Gamma is invertible, and each singleton
column contains a negative entry, hence Gamma is R0. At target y=1 the
only complementary solution is x012=(1,1,1), x3=0. The passive slack is
1/2 and det Gamma012=7>0, so the degree is +1 (enumerate the eleven
nonsingleton principals). The comparison covers the named admissions.
It does not identify the union of all historical raw predicates.

The result is an ordinary mathematical reduction. The all-fine special
case uses the same three-player geometry as
the [three-player cycle inheritance theorem](../formalized/THREE_PLAYER_CYCLE_PASSIVE_ROW_EXTENSION.md).
The new step is solving (1) for subdivisions at negative outsider endpoints.
A formal handoff can first isolate the one-dimensional mesh lemma (T),
then apply the finite-deadline regret estimate to the finite periodic
profiles. The [terminal characterization](GLOBAL_LEAST_NEVER_SOURCE_REDUCTION.md)
also gives the original fixed-target conclusion from vanishing terminal
regret. The comparisons above use the
[two-unrestricted-row criterion](TWO_UNRESTRICTED_RECIPIENTS_UNIFORM_EQUILIBRIUM.md),
the [support orientation criterion](SUPPORTWISE_NEGATIVE_ORIENTATION_UNIFORM_EQUILIBRIUM.md)
and the [marked weight criterion](MARKED_SUPPORT_ORIENTATION_LEDGER_UNIFORM_EQUILIBRIUM.md).
