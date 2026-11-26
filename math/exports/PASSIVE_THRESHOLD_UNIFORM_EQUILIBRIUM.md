# A passive-payoff threshold gives uniform equilibrium beyond participant ledgers

Ordinary mathematics, not Lean checked. The result is a raw four-player UE
class; all strategic data used by its actual-law minimum argument are produced
in the proof. Its complete collision-plane corollary includes the formerly
surviving benchmark.

## 1. Raw criterion and statement

Let I={0,1,2,3}. For every nonempty coalition A let Z_i(A) be a finite real
native reward, with Z_i({i})=0. Native live/Never payoff is0. Put

 Gamma_ij=Z_i({j}),   H=max(0,max_(A nonempty) Z0(A)),
 a=-Z1(13),          c=Z1(123).

Assume all the following finite raw conditions:

    Z0(A)<=0 whenever0 in A;
    Z1(12)<=0, a>0, c>0, Z3(23)<=0;                  (R1)

    c H+a Gamma02<=0;                                (R2)

    Z0(12)<=0, Z0(23)<=0, Z0(123)<=0;
    c Gamma01+a Z0(12)<=0;
    c Gamma03+a Z0(23)<=0;
    c Z0(13)+a Z0(123)<=0.                            (R3)

All unlisted rewards are arbitrary finite. The displayed player labeling may
be found by enumerating24 permutations; no continuation, root, weight or
strategy is supplied as a premise. H,a,c are explicit functions of the raw
reward table. Weak boundaries in(R1)–(R3) are included.

THEOREM. The infimum A_Z of complete total native terminal Nash debt over
prescribed independent profiles that absorb surely is zero. Consequently,
for every nonnegative own-level vector kappa, the original reward table
r_i(A)=kappa_i+Z_i(A), with live/Never0, has one fixed uniform-equilibrium
payoff. Strategies use independent private randomization; every complete
unilateral behavioral replacement is permitted. The selected payoff is fixed
before accuracy. No public correlation or observed-deviation signal is used.

The mechanism differs from a static nonpositive-participant ledger. The
coalition123 may pay all its participants strictly positively. Its Nash
conditions force player2's hazard above a raw threshold, and then player0's
passive payoff prevents a wholly positive root output.

First prove the theorem with strict(R2). Produce the numbers

 theta=a/(a+c),    V=(H-a Gamma02/c)/2.

Then0<theta<1, V>H>=0, and c V+a Gamma02<0. Section6 recovers equality in(R2)
by a single-coordinate reward approximation, with an explicit regret bound.

## 2. Root maps and a produced invariant region

For q in[0,1]^4 let a0=product_i(1-q_i) and
H_i=product_(j!=i)(1-q_j). If B is the independently sampled opponent
quitter set, write

 Q_i=E[Z_i(B union{i})],
 P_i=E[Z_i(B)1_(B nonempty)],
 E_i=sum_(A nonempty)Pr_q(A)Z_i(A).

A payoff/full-cap annotation pair(u,b) transforms under a root prefix to

 u'_i=a0 u_i+E_i,
 b'_i=max(Q_i,P_i+H_i b_i).                         (2.1)

Prescribed payoff uses joint survival a0; a deviator's cap uses opponents-only
survival H_i. At a Nash root against u, starting from b=u gives b'=u'.
The maps are continuous and separately coordinatewise1-Lipschitz in terminal
annotations. Their finite-word compositions have the same bound, independent
of word length. Prefix order is reversed in the physical calendar.

These cap formulas include every behavioral deviation. Before absorption the
only public history is an all-Continue history; each player's strategy induces
a law of its first Quit time in the natural numbers plus Never. Against fixed
opponents, every such response law is a mixture of finite deadlines and Never.
Taking the supremum commutes with the nonnegative multiplier H_i, proving the
second formula. There is no restriction to stationary or on-support deviations.

Produce the region

 D={u:u0<V},       K={u in D:min_i u_i<=0}.

Every actual row0 payoff and cap is at most H. Every arbitrary prefix from D
satisfies u'_0<=max(u0,H)<V and, if b0<V, b'_0<=max(b0,H)<V. Thus a closure
of prefixes from a fixed seed stays below max(seed0,H)<V as well. The strict
upper domain needed by later virtual seeds is preserved by actual formulas.

CLAIM. Every Nash root against u in K has its output in K. Indeed every
nonzero Nash root against ANY u in D has a nonpositive output coordinate.

If q0>0, supported Quit gives u'_0=Q0<=0 by(R1). If q0=0, a single active
owner in{1,2,3} has its own Quit value0. For active set12, Q1=q2 Z1(12)<=0;
for13, Q1=q3 Z1(13)<0; for23, Q3=q2 Z3(23)<=0. This covers every proper
nonempty active subset, including sure hazards and boundary equalities.

For active set123, put y=q1,b=q2,z=q3. If Q1<=0, again we are done.
Otherwise(R1) gives

 0<Q1=b(1-z)Z1(12)+(1-b)z(-a)+bz c
       <=z[(a+c)b-a],

so b>theta. With q0=0 the output row0 is affine in y,z and increasing in
u0. Its four(y,z) corner upper bounds, after replacing u0 by V, are

 (1-b)V+b Gamma02,
 (1-b)Gamma03+b Z0(23),
 (1-b)Gamma01+b Z0(12),
 (1-b)Z0(13)+b Z0(123).                            (2.2)

At b=theta these are nonpositive by cV+aGamma02<0 and(R3). At b=1 they
are nonpositive by Gamma02<0, which follows from strict(R2), and the first
line of(R3). Affineness makes them nonpositive for every b in[theta,1].
Bilinear interpolation then gives u'_0<=0. At q=0 the output is u itself.
This proves the produced invariant, with no assumption on any selected root.

## 3. Local escape from a unique all-Continue root

We prove the exact localized form of the needed invariant-region consumer.
Let Z be any finite native own-zero table for which (i) all actual row0
rewards are at most H, (ii) all finite prefixes preserve D={u0<V} and its
full-cap counterpart, and (iii) root Nash preserves K above. The preceding
section supplies all three properties from the raw table.

Suppose v in D is coordinatewise nonnegative, min_i v_i=0, and AllContinue
is the unique whole-game Nash root against v. Put S={i:v_i=0}.

LOCAL LEMMA. For every d>0 and eta0>0 there exist c>0 and finite words W_n,
supported on S with every hazard at most d, such that their joint survivals
h_n satisfy1-eta0<=h_n<=1-c, their full virtual debts from(v,v) tend to zero,
and their output minimum has limsup<=0. All positive coordinates outside S
remain positive. No root selection or recurrence assumption is made.

We prove this by induction on |S|. Shrink eta0 below1 if needed. Choose M>=1
bounding every reward and v and a fixed small neighborhood of v. Unrolling
any word of survival h from seed z gives

 ||U-v||_infinity<=||z-v||_infinity+2M(1-h).        (3.1)

Take eta0 small enough to preserve all strictly positive outside coordinates.
All seeds are chosen with z0<V. Their finite-prefix closures stay below
max(z0,H)<V, so the localized invariant remains applicable even at limits.

### Nonnegative-kernel case

Let Gamma_SS be the own-zero singleton matrix on S. If it has a nonzero
nonnegative kernel vector x, normalize sum x=1 and repeat q=epsilon x for
floor(T/epsilon) stages, for fixed small T>0. Choose T with
1-eta0<exp(-T)<1. Core singleton drift vanishes. Core finite-absorption
contributions per date are O(epsilon^2), and immediate Quit offers are
O(epsilon); summing through O(1/epsilon) dates gives core payoff and cap
errors O(epsilon). The positive outsiders retain strict Continue preference
by(3.1), since their Quit offers are O(epsilon), and have zero debt. Thus
survival tends to exp(-T), core payoffs tend to0, and the lemma follows.
This also proves the singleton induction base, whose principal matrix is0.

### Signed separation and virtual seeds

Otherwise0 is outside the convex hull of Gamma_SS's columns. Its nearest
point w satisfies

 w Gamma_SS>=||w||^2 1^T>>0.

Consequently, for all sufficiently small hazards supported on S,

 w E_S(q)>=gamma sum_i q_i, gamma>0.              (3.2)

The higher-order remainder is bounded by a constant times max(q)sum(q).
No sign is assumed on w. There are arbitrarily small vectors z_S with
w z_S>0 and min_(i in S)z_i<0: for |S|>=2 the union of negative coordinate
halfspaces meets every nonzero positive linear halfspace. Set z_out=v_out.
Choose these seeds in D.

Unique AllContinue and compactness of the entire Nash root cube imply that
for a sufficiently small neighborhood of v every whole-game Nash root has
all hazards below a chosen delta and is supported on S. The latter also
uses outsiders' strict Continue gaps. Take delta<=d, small enough for(3.2)
and delta<eta0/16. Choose epsilon0 for this neighborhood, then fix

 c0=min(eta0/4,epsilon0/(8M),1/4)

before choosing seeds z with ||z-v||<epsilon0/4.

### A budgeted prefix minimum

Let K_z be the closure of all outputs(U,B,h) from finite words at(z,z),
supported on S, having hazards at most delta and survival h>=1-eta0. Include
the empty word. This is compact. Prefixing a fixed allowed word acts on this
closure whenever the resulting survival has strict slack above1-eta0,
by applying the word to defining approximants first.

Minimize h on the nonempty compact subset

 F_z={B=U, min_i U_i<=0, w U_S>=h w z_S}.

The empty word belongs to F_z. If a minimum Y=(u,u,h) had h>1-c0, (3.1)
would place u in the chosen neighborhood. Every Nash root there is small,
proper and supported on S. Any nonzero root preserves zero virtual debt,
the minimum condition by the invariant, and the original weighted inequality
by(3.2). It retains strict survival-budget slack because

 a0(q)h>(1-4delta)(1-c0)>1-eta0.

It would strictly lower h in the same F_z, a contradiction. Thus AllContinue
is the unique root at u, forcing u>=0. The weighted inequality makes u_S
nonzero. Its zero set T is therefore a nonempty proper subset of S; outsiders
remain positive by(3.1).

Apply the induction hypothesis at u with zero set T. Request hazards at most
delta and a budget eta1 with h(1-eta1)>1-eta0. Its words have survival at most
1-c1 for some c1>0, virtual debt tending to zero, and output minimum with
limsup<=0. Apply them to Y. All their hazards are supported on T subset S,
so(3.2) retains the ORIGINAL weighted inequality

 w U_S(new)>=h_new w u_S>=h_new h w z_S.

A compact endpoint subsequence therefore belongs to the same F_z, with
survival at most h(1-c1)<h, contradiction. No uniformity of c1 in Y is
required: the minimum and its strict improvement are fixed. Hence every
seed's F_z minimum has h<=1-c0.

Approximate those minima by their defining finite words, and let z tend to v.
Apply identical words to(v,v). Coordinatewise nonexpansiveness changes each
payoff and cap by at most||z-v||, independently of word length, so total debt
still tends to zero and the output minimum has limsup<=0. The survival is
unchanged and bounded above by1-c0/2 after discarding finitely many terms.
This proves the local lemma. All nested seeds and prefix closures remain in D;
no global-in-u version of the invariant was silently assumed.

## 4. Actual laws and the global minimum

For actual independent stopping laws let C_actual be the compact closure of their
finite-dimensional data(U,B,N): prescribed terminal values, complete unilateral
response caps, and each ORIGINAL marginal Never mass N_i. Finite prefixes act
continuously by(2.1), including non-Nash words, and multiply product_i N_i
by their joint survival.

Let A_Z be the infimum of total native Nash debt over absorbing prescribed
laws. For an actual law choose an owner with smallest Never mass and move
that mass to one finite date. The new law absorbs surely. Each prescribed
payoff changes by at most2M times the moved mass; every other player's full
cap changes by at most that amount; the chosen owner's cap is unchanged.
For four players this yields

 A_Z<=sum_i(B_i-U_i)+14M(product_i N_i)^(1/4).     (4.1)

The same inequality holds on C_actual by continuity. No realized virtual seed is
required anywhere in this argument.

Consider the compact set

 E={X in C_actual:B=U, min_i U_i<=0}.

It contains AllNever. Assume A_Z>0. By(4.1), product N has a positive minimum
m on E. Let X attain it with payoff v. Actual values/caps in row0 are at most H,
so v is in D.

Any nonzero Nash root against v preserves zero full debt. A root with a sure
quitter gives zero Never product and contradicts(4.1). A proper nonzero root
preserves E by the invariant and strictly lowers its ORIGINAL Never product,
also impossible. Thus AllContinue is the unique whole-game root at v. It
forces v>=0, and membership in E gives min v=0.

Apply the local lemma at v and prefix the identical finite words to X.
Their virtual annotations are exactly the actual semantic annotations,
because X has B=U=v and the prefix maps are continuous on C_actual. A compact endpoint
subsequence has zero debt, nonpositive minimum payoff, and Never product at
most m(1-c)<m. This is a point in the SAME E, contradiction. Therefore A_Z=0.

## 5. Original game and uniform target

For nonnegative kappa, an absorbing prescribed native law has original payoff
U_i^r=U_i^Z+kappa_i. Every unilateral finite absorption receives that same
coordinate shift, while literal Never receives0, so for every complete
replacement its original payoff is at most its native payoff+kappa_i.
Hence original debt is at most native debt. The absorbing profiles whose
native debts tend to zero therefore provide original terminal Nash profiles
at every accuracy. The established terminal-to-uniform selection theorem
selects one payoff before accuracy and supplies the uniform finite-horizon
contract against every complete behavioral replacement. This proves the theorem under the strict inequality in(R2).
The proof includes neither public correlation nor observed deviation signals.

## 6. The weak boundary in the first raw inequality

Suppose(R2) is an equality. Its hypotheses imply Gamma02<=0, since H>=0 and
a,c>0. Decrease only Z0({2}) by epsilon>0. H is unchanged: its definition
includes0, and the changed entry was already nonpositive. No other guard
changes, while(R2) becomes strict. The preceding proof gives original terminal
Nash profiles at every accuracy for each perturbed table, for every fixed
nonnegative kappa.

Changing all terminal rewards by at most epsilon changes every profile payoff
and every unilateral payoff by at most epsilon; taking suprema gives a debt
change of at most2epsilon per player. Given a target error delta, choose
epsilon<delta/4 and a perturbed terminal Nash profile of error<delta/2.
The identical profile has original error<delta. Thus original terminal Nash
profiles exist at every error, and the fixed-target selection theorem gives
UE. For kappa=0 these identical profiles still absorb surely in the unperturbed
game; its total native debt changes by at most8epsilon. Thus their total
debt still tends to zero and A_Z=0 follows. This
proves all weak boundaries claimed in(R1)–(R3).

## 7. Exact unbounded family and the formerly surviving benchmark

For arbitrary real eta,p,t,R,K define every native nonempty-coalition reward by

|A|Z0|Z1|Z2|Z3|
|---|---:|---:|---:|---:|
|0|0|2|2|-1|
|1|3|0|-2|-2|
|2|-1|1/2|0|1|
|3|3|-3|-1|0|
|01|0|-1|-10|-12|
|02|-1/10|5|2+eta|-219/29|
|12|-12|-K|p|-6|
|03|-20|3|-5|1|
|13|2|-100|-1|10|
|23|R|9|3|-100|
|012|-20|6|-100|11|
|013|-20|8|10|-10|
|023|-20|-8|-100|t|
|123|-8|11|2|1|
|0123|-5|-9|-100|21/2|

If K>=0 and R<=-33/100 then(R1)–(R3) hold for every eta,p,t:

 H=3, a=100, c=11,
 cH+aGamma02=-67<0,
 cGamma01+aZ0(12)=-1167,
 cGamma03+aZ0(23)=33+100R<=0,
 cZ0(13)+aZ0(123)=-778.

All participant row0 rewards are nonpositive, Z3(23)=-100, and the remaining
three passive endpoint rewards are -12,R,-8. Thus the theorem produces UE
throughout this unbounded five-parameter region for every nonnegative kappa.
The exact former benchmark is

 eta=12281660/12608823, R=-25,t=987,p=0,K=1000,kappa_i=1.

The strict first guard gives V=133/22, produced directly from the table.
No computation of an equilibrium period or unknown continuation cap is needed.

## 8. The entire two-coordinate collision plane

Use the complete native table in the main theorem, with
eta=12281660/12608823, K>=0, arbitrary p, R=Z0(23), and t=Z3(023).
Let t0=28599/29. The profiles below supply the two regions complementary to
the localized-invariance region R<=-33/100. Every probability and comparison
is produced explicitly. They allow arbitrary original own offsets kappa_i;
only the separate localized-invariance consumer requires kappa_i>=0.

### Every R when t<=t0: an exact five-date profile

Put b=3/10, x=87/947. Repeat the five product hazard vectors

    (0,0,0,1/20), (x,0,b,0), (0,0,0,3/100),
    (0,0,0,525873/29323973), (0,0,0,22221/476821).

All displayed nonzero hazards lie strictly between0 and1. At those dates
assign respectively the native continuation values

    Y=(243/2000,66663/454600,607433/2898580,0),
    X=(-3/100,134853/431870,39598/144929,0),
    U=(27/70,-42984/302309,14281/144929,0),
    B=(207/679,-1577619/29323973,1862887/14058113,0),
    V=(12069/47210,0,104816681/684209809,0),

and return from V to Y. At each solo3 date of hazard q, the literal identity

    current=q(3,-3,-1,0)+(1-q)next

holds. Owner3 has both action offers zero. The quiet owners0,1,2 have Quit
offers -20q,-100q,3q. Their current-minus-Quit margins are exactly

| Current | Owner0 | Owner1 | Owner2 |
|---|---:|---:|---:|
|Y|2243/2000|2339663/454600|86323/1449290|
|U|69/70|863943/302309|123739/14492900|
|B|19457169/29323973|525873/302309|334524762032/4249894082917|
|V|5663169/4768210|2222100/476821|925082854/69105190709|

Every margin is strictly positive. At the joint02 date, with successor U,
owner0's two action offers equal X0=-b/10; owner2's two action offers equal
X2=(2+eta)x. The passive row3 payoff is

    -x+b-(219/29)xb=0,

and its forced Quit offer is

    x(1-b)-100(1-x)b+t xb = xb(t-t0)<=0.

Quiet owner1's Continue payoff is X1. Its Quit payoff is
x(-1+7b)-K(1-x)b. The exact margin is

    43187916/204490445+(258/947)K>0.

The native Bellman identities at the joint date, including row1, are direct
rational equalities with the displayed values. Thus every prescribed action
is optimal against its exact successor annotation at every date. R occurs
in none of these prescribed payoffs or one-player deviation offers; p is
also absent because player1 never quits. This proves the same profile works
for every R, every p and every K>=0 whenever t<=t0.

Each player faces positive opponent absorption in every period: at the joint
date owners0,2 have proper positive hazards, and at the four other dates
owner3 has a proper positive hazard. Hence the opponents-only survival
product is strictly below1 for every player. Iterating the action inequalities
against any complete unilateral behavioral replacement makes the bounded
continuation remainder vanish. The native profile is exact terminal Nash
with payoff Y, and every unilateral replacement absorbs almost surely.
Original rewards kappa_i+Z_i therefore add kappa_i to every terminal
comparison. The geometric absorption bound uniformly controls the difference
between terminal and long finite-horizon averages over all replacements.
The fixed original uniform-equilibrium payoff is kappa+Y.

### R>=-33/100 and t>=t0: an exact two-date punishment profile

Define

    x=2929/(29t+3148), z=9/(10R+209).

The stated region gives 0<x<1/10 and 0<z<1/20. At date1 use hazards
(x,0,1,z). If everyone Continues, at date2 prescribe certain quitting by
players0,1, with players2,3 continuing. Later actions are immaterial.

Players0 and3 face certain absorption by player2 at date1. Their exact
Quit-minus-Continue differences are

    9/10-(R+209/10)z=0,
    -101+(t+3148/29)x=0,

so both proper mixing prescriptions are optimal. Quiet player1 has passive
and Quit offers

    P1=(1+9x+17z-43xz)/2,
    Q1=-K(1-x)(1-z)+6x(1-z)+11(1-x)z-9xz.

Consequently

    P1-Q1=(1-3x-5z+9xz)/2+K(1-x)(1-z)>9/40>0,

using x<1/10, z<1/20 and K>=0.

If player2 deviates by continuing at date1 and reaches date2, it faces sure
quitting by players0,1. Its Continue payoff there is Z2(01)=-10 and its
Quit payoff is Z2(012)=-100. Thus its COMPLETE native continuation cap is
exactly -10. At date1 its Quit and optimal Continue values are therefore

    Q2=(2+eta)x(1-z)+3(1-x)z-100xz,
    C2=2x(1-z)-(1-x)z-5xz-10(1-x)(1-z).

Their difference simplifies to

    Q2-C2=10+(eta-10)x-6z-(eta+89)xz>33/4>0,

because 0<eta<1, x<1/10 and z<1/20. This prices all future deviations of
player2, rather than comparing only the prescribed Continue action.

Every unilateral replacement by a player other than2 faces certain player2
quitting at date1. A deviating player2 faces sure players0,1 by date2.
Therefore every replacement absorbs by date2. The displayed endpoint
comparisons prove exact terminal Nash against all behavioral deviations;
the punishment need not be a Nash profile on the unreached continuation.
The fixed original target is kappa plus the native expected date1 reward.
All terminal comparisons survive arbitrary own offsets kappa, and the
terminal-to-average error is uniformly O(1/T). Hence this is a uniform
equilibrium for the original game.

### Full-plane conclusion

The localized-invariance producer covers R<=-33/100 for every t. The five-date profile
covers every R when t<=t0, and the two-date profile covers R>=-33/100 when t>=t0.
These regions cover every real pair(R,t), including both threshold equalities.
Thus, combined with that producer, the entire two-coordinate surface has UE
for K>=0, arbitrary p, and every nonnegative original own-offset vector.

## 9. Nonredundancy and exact negative controls

### Every global marked-cone choice fails at the benchmark

The benchmark has eta=12281660/12608823,R=-25,t=987,p=0,K=1000. For a
nonempty marked set C, global invariance would require every proper Nash root
against every real u with min_(i in C)u_i<=0 to produce another such point.
The new bounded domain cannot be replaced by that stronger global premise:
it fails for EVERY one of the15 marked sets at this same table.

A safe positive edge j->i means Gamma_ij>0 and Z_i(ij)<=Gamma_ij. If j is
outside C and i is in C, prescribe only j to mix properly, set u_j=u_i=0,
and take all other continuation coordinates sufficiently large and positive.
The owner j is indifferent; i's positive passive payoff dominates its Quit
offer; all other quiet players strictly prefer Continue. Every marked output
is positive, although u_i=0. Thus a globally invariant C must contain every
safe predecessor of each of its members.

The complete safe-edge set at this table is

 0->1, 1->0, 2->1, 2->3, 3->0.

Its only proper nonempty predecessor-closed sets are{2} and{2,3}. For both use

 q=(1/2,0,1/2,1/50),
 u=(261/490,1,eta-13/7,25971/29).

The active owners0,2,3 satisfy Q_i=P_i+H_i u_i exactly. Quiet1's Continue
value is167/80 and its Quit offer is-9769/40. Yet u2=eta-13/7<0 while the
marked outputs are F2=(49eta+1)/100>0 and F3=222>0. This excludes both
remaining proper marked sets.

For C=all4 use

 q=(0,99/100,19/20,9999/10000),
 u=(200000000,-1217901/2,3009897,12436).

Owners1,2,3 are exactly indifferent, and the complete output is

 F=(11693257/5000000,1070891/200000,2009799/1000000,971/2000)>>0.

Quiet0's Quit offer is-1178758369/200000000<F0, so this is a proper whole-game
Nash root although the input u1<0. It lies outside the new bounded domain in
coordinate0; no realizability of its large virtual continuation is asserted.
The first example uses different marked sets and does not contradict the new
full-player invariant. These two exact calculations, together with the safe
edges, exhaust all15 global marked-cone selectors.

Earlier static ordered-participant criteria also fail every selection here.
The positive singleton graph is strongly connected: it includes0->2->3->0
and0->1->0, with giver-to-recipient arrows. Thus a nonempty marked set with
nonpositive rewards from all outside coalitions must be all4. Coalition123
has participant rewards(11,2,1), so its first intersected block has a positive
weighted participant sum for EVERY block order and positive weight choice.
The present root-Nash threshold argument supplies an invariant despite this
strict failure of the static raw conditions.

### The passive23 restriction cannot simply be removed

An exact negative control modifies the full family table to

 eta=500,p=0,t=60000,K=1/2,R=4000, and Gamma02=-500.

Here(R1) holds and(R2) is strict: H=4000,a=100,c=11 gives cH+aGamma02=-6000.
All(R3) conditions concerning12 and123 hold. The two passive23 conditions
fail. The continuation and proper root

 u=(-1,2,499,59796), q=(0,99/100,99/100,1/2)

are an exact whole-game Nash root pair. Each active owner is indifferent;
quiet0's Quit offer is-2490149/200000. The current output is

 F=(150977/20000,1879/400,201/200,891/10000)>>0,

so it leaves the nonpositive-coordinate region. The input is inside the
literal coordinate reward ranges and has u0<V=47000/11. This is a failure of
the invariant after removing its passive23 restrictions, not a no-UE example.
Every displayed equality follows by the finite coalition expectations(2.1).

## 10. Source correspondence and scope

The mathematical consumer proved in Sections3–5 uses finite Nash existence,
full-cap prefix nonexpansiveness, a budgeted local escape, and an actual
zero-debt carrier minimum with its ORIGINAL marginal Never masses. It does
not minimize an artificial tail, assume a finite equilibrium period, or
identify virtual seeds with actual profiles. The compact carrier keeps only
finitely many bounded semantic coordinates; finite-prefix continuity is the
literal recurrence(2.1), not continuity of a payoff map on arbitrary weak
stopping-law limits.

The inspected source interfaces are `exists_isZeroQuittingRootNash` in
`UniformEquilibrium/Quitting/Root/NashExistence.lean`;
`quittingContinuationBestResponseValue_rootThenContinuation_eq_max` in
`UniformEquilibrium/Quitting/Root/TerminalDebtPrefix.lean`;
`quittingFiniteRootWordCap_sub_le_opponentSurvival_mul_posPart` in
`UniformEquilibrium/Quitting/Root/CommonPrefixCapStability.lean`; and
`quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors` in
`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`.
They identify the precise finite Nash, cap, and fixed-target consumers. The
new raw criterion and proof are ordinary mathematics, not a new checked Lean
declaration. The original-own-level conclusion assumes kappa>=0; negative
own levels are not silently included by terminal-only row subtraction.


A Lean handoff can retain four precise theorem shapes: the finite raw predicate
(R1)–(R3) implies absorbing native debt infimum zero; localized proper-Nash
invariance on an open prefix-invariant box implies the same infimum conclusion;
the budgeted unique-AllContinue escape lemma produces finite words with a
fixed positive absorption amount and vanishing full debt; and the infimum
conclusion plus nonnegative own levels yields the established fixed uniform
payoff endpoint. The weak first guard is handled by the single-reward
approximation in Section6. The explicit five-date and two-date corollaries use
literal rational Bellman comparisons and opponents-only absorption. No
unproduced strategy-class completeness hypothesis is part of these statements.

## 11. An exhaustive eleven-support raw test

For any finite native four-player table with own rewards zero, define

 ell_i=min(0,min_A Z_i(A))-1,   u_i=max(0,max_A Z_i(A))+1,
 D=product_i(ell_i,u_i).

The constants are explicit raw data, and ell_i<0<u_i. Use the polynomials
Q_i(q),P_i(q),H_i(q) defined above. For each subset S of size2,3,or4, set
q_j=0 off S and require0<q_i<1 on S. There are exactly11 such supports.
Test the following real-polynomial system:

 Q_i>0,  ell_i H_i<Q_i-P_i<u_i H_i                 for i in S;    (A1)
 P_j+u_j H_j>0,  P_j+u_j H_j>Q_j                 for j outside S; (A2)

and at least one of the four anchor alternatives

 Q_i-P_i<=0                                      for some i in S,
 P_j>0 and Q_j<=P_j                              for some j outside S. (A3)

If all11 systems are infeasible, then A_Z=0 and every original table with
nonnegative own offsets has UE. Expanding(A3) gives at most44 systems in
at most four hazard variables, with polynomial degree at most3. Exact
real-algebraic emptiness is meant; a finite grid search does not suffice.

Proof. Every proper root has H_i>0. For an active owner i, root Nash forces
v_i=(Q_i-P_i)/H_i and output Q_i. Thus(A1) is exactly input membership in D
and positive output. For inactive j, output is P_j+H_j v_j and must be
positive and at least Q_j. Its attainable range as v_j runs through
(ell_j,u_j) is an open interval with upper endpoint P_j+u_j H_j. Feasibility
is exactly(A2). An active input is nonpositive exactly when Q_i-P_i<=0.
An inactive nonpositive input with positive Nash output exists exactly when
P_j>0 and Q_j<=P_j; sufficiency sets v_j=0. Other inactive inputs can be
selected independently near u_j. This proves that(A1)–(A3) are equivalent
to a proper root Nash at some v in D with min v<=0 and all output coordinates
strictly positive. Zero support cannot cross, and one active owner has output
its own zero, so the11 supports are exhaustive, including all zero walls.

Their infeasibility gives nonpositive inertia on D. Every arbitrary prefix
preserves D on payoff and full-cap annotations. For each fixed seed, all
outputs and their closure lie in the smaller closed coordinate box spanned
by that seed,0,and the corresponding reward extrema, strictly inside D.
All actual annotations lie strictly inside D as well. In the local zero-set
induction, positive outside coordinates are left fixed and each zero coordinate
is an interior point of its interval(ell_i,u_i), so the small signed seeds stay
in D. Each fixed-seed prefix closure has the strict interior bound just proved;
this also supplies the same bound for every recursive induction point. These
are exactly the domain properties used in Sections3–4. The localized zero-set
escape and actual least-Never proof therefore give A_Z=0 on this coordinate box. No continuation or selected Nash root is an
input. Conversely, failure of this bounded inertia property supplies a
solution to one of the eleven systems; it does not imply failure of UE.


Consequently, any counterexample with nonnegative original own levels must
admit a solution to at least one of these eleven raw systems. This is an
additional finite necessary condition on its higher-coalition rewards, not an
assumption that an actual equilibrium or selected minimizing source supplies
the root. The threshold family above supplies the new
UE coverage; the finite reformulation is not counted as a second coverage gain.
