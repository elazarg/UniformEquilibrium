# Uniform equilibrium by returning a nonpositive payoff to its minimum

## Statement

There are four players, numbered 0 through 3. Write 02 for the coalition
{0,2}, and likewise for other coalitions. Each player independently chooses
Continue or Quit on the common live history. The first nonempty quitting
coalition absorbs with the indicated real rewards. Live play and never
absorbing give zero. All unilateral behavioral replacements are allowed.

Write the original rewards as r_i(S)=s_i+l_i Z_i(S) on nonempty coalitions,
where the s_i are arbitrary real numbers, l_i>0 and Z_i(i)=0. Define
Gamma_ij=Z_i(j), J_ij=Z_i(ij) for i distinct from j. Assume

    Gamma = [ 0  -2  -5   4 ]
            [-6   0  -4   6 ]
            [ 1   3   0  -5 ]
            [ 1  -1   4   0 ].
    J01=-1, J03=3, J10=-7, J13=-1, J30=2, J31=-2.
    Z_i(S)<=0 for i=1,2 whenever i belongs to S.
    Z1(03)<=0, Z2(03)<=-4.                                  (1)

All further conditions use observed reward entries. Put

    p=-J02, v=-J20, c=J32, j=J12, e=5+J23,
    H_i(T)=Z_i(T)-Z_i(T union {i}) for i outside T.

**Theorem.** Each of the following two sets of conditions implies that r
has a uniform-equilibrium payoff. There is one target vector for which,
at every requested accuracy, one profile delivers that target within the
accuracy and caps all unilateral gains within the accuracy at every
sufficiently long finite horizon. The proof below covers every continuation in each stated reward class.

**Two pairs.** Write d=p-5, h=c-4, M0=max(1,-Z0(013)). Require

    d>0,  h>=2/3,  h<=5d,  0<e<=4,  4+j<=24d,
    H1(02)>=-4d(7+6v),  H3(02)>=-4dv,
    H0(23)>=-h/(1+M0), H1(23)>=-h/M0.                       (2)

**A row containing players 2 and 3.** Write b=-H0(23), n=4-c, g=-H3(02),
k=Z2(023)-Z2(03), and a=5-p. Require

    a>=0, b>=0, a+b>0, e>0, k>0,
    g>=0 if b=0, and g> -b if b>0,
    L=H1(03)>=0, 7a>=4+j, H1(02)>=-a L,
    H1(23)>=-7b, H1(023)>=-b L.                              (3)

Here c may be any real number.

All remaining entries are arbitrary finite numbers subject to the displayed
conditions. In particular (1) fixes six nonsingleton entries. The result
allows changes to the passive and triple rewards used in earlier
fixed-table source constructions. Neither the existence of a special
profile nor any condition on the actual continuation is an input.

## The minimum and a negative starting point

Work first in the native table Z, with zero live and Never payoffs. Before
absorption the only public history is its date. Independent private
randomization therefore amounts to one independent first-Quit time per
player on the natural numbers and a distinct point Never. A randomized
replacement is a mixture of deterministic deadlines, including Never.
Let U_i be expected payoff, B_i the supremum over those deadlines, e_i the
payoff of Never against the other clocks, and N_i the original marginal
probability of Never. Let C be the Euclidean closure of the actual tuples
(U,B,(e_i)_i,N), keeping finite mass escaping to late dates distinct from N_i
throughout. Write E for its closed subset U=B, nu for the product of N_i,
and D for the sum of B_i-U_i. All these sets of tuples are bounded.

Let A_Z be the infimum of D over actual profiles with nu=0. Suppose A_Z>0.
Then nu>0 throughout E. Otherwise take approximants to a point with N_i=0
and move the vanishing remaining Never mass of player i to one finite date.
All prescribed payoffs and every other player's deadline values change by
at most twice the reward bound times that mass, while B_i is unchanged.
The repaired profiles absorb and have D tending to zero.

Over a tail with payoff u in E, a first-stage Nash equilibrium of the finite
game with continuation u produces another point of E. To see this, let q be
the independent first-stage Quit probabilities. For each player i write Q_i
for the expected payoff of joining now, P_i for the expected passive reward
from nonempty opponent coalitions now, and H_i^c for the probability every
opponent continues. The new cap is max(Q_i,P_i+H_i^c B_i), and the new
payoff mixes Q_i and P_i+H_i^c U_i with weights q_i,1-q_i. Prefix actual
approximants and use continuity. The new nu equals nu times the product
of 1-q_i. A sure component is consequently impossible at any such Nash row
under A_Z>0.

Minimize nu over E subject to min_i U_i<=0, and call the minimum m. AllNever
is admissible. We establish 0<m<1 and that every minimizing point has a
negative coordinate. Here are the details of the strict upper bound, which
also account for the possible all-zero minimizing payoff.

Use only players S=(0,1,3) and their two matrices G=Gamma_SS, J=J_SS
with zero diagonal. For a row q on S define Q(q) from immediate Quit,
P(q) from passive rewards, and W_i(q)=(Q_i(q)-P_i(q))/H_i^c(q).
Their differentials at the origin are J, G (for P), and J-G (for W).
The matrix J-G has determinant -8. Near zero the smooth map
T=W^{-1} composed with Q maps a later row into an earlier indifferent row.
Its derivative (J-G)^{-1}J has characteristic polynomial
(t-2)(4t^2+t-11)/4, and eigenvector v0=(39,25,15) for eigenvalue 2.
For small z>0 there exist infinite rows q_t=2^{-t}z v0+O((2^{-t}z)^2)
for t=0,1,..., with W(q_t)=Q(q_{t+1}). Indeed all three eigenvalues
are real, distinct and of modulus at most 2. In their eigenbasis T is
3-Lipschitz near zero, and T(s v0)=2s v0+O(s^2). Start at date L with
2^{-L}z v0 and iterate T towards date zero. If the approximation error
is bounded by K s^2 at scale s, at the next scale it is bounded by
(3K+C)s^2<=K(2s)^2 for K>=C. Small z keeps every iterate in the chosen
neighborhood. A diagonal subsequence as L tends to infinity gives the
stated rows, all strictly positive and proper.

The summable hazards give positive Never and some absorption. For each
core player, stopping and continuing give identical values with the
indicated future annotation. The annotations Q(q_t) tend to zero.
Truncating at date L thus prices every finite deadline and Never in the
infinite clock by the same initial value in the limit, since both the
remaining absorption probability and the terminal annotation tend to zero.
Player 2 stays quiet. Its unconditional passive contribution at each row
conditional on reaching that row is 2^{-t}z (1,3,-5) dot v0 plus a
quadratic error, with leading coefficient 39>0. Its immediate Quit offer
is nonpositive. Continuing at every date is therefore optimal. The initial
payoff of player 1 is negative since (J v0)_1=-288. This is an actual
point of E eligible for m and has nu<1.

At a nonnegative minimizing payoff with a nonempty proper zero set, a
single owner can move. An exact solo move by j is available if every other
zero owner i satisfies Gamma_ij>=J_ij. Prepending a small hazard f at j
keeps j at zero, and every positive owner prefers Continue by continuity.
A diffuse solo move suffices if every other zero owner has Gamma_ij>=0.
Prepend L solo dates of total unconditional mass f, each of mass f/L.
A zero observer receives f Gamma_ij and gains at most O(f/L) at an internal
deadline, since earlier absorption gives Gamma_ij, and joining can affect
only the current atom. Continuing into the old tail attains the prescribed
value. Positive observers retain their buffer for fixed f sufficiently
small, uniformly in L. Prefix approximants and take a compact limit as
L grows. In either case the resulting point of E keeps j at zero and
has Never product (1-f)m. Here is the full list of choices, with a
singleton zero set using its own exact move.

| Zero set | 01 | 02 | 03 | 12 | 13 | 23 | 012 | 013 | 023 | 123 |
|---|---|---|---|---|---|---|---|---|---|---|
| Mover | 0 | 0 | 3 | 1 | 3 | 2 | 0 | 3 | 0 | 1 |
| Move | exact | diffuse | diffuse | diffuse | diffuse | diffuse | exact | exact | diffuse | exact |

For an all-zero minimizing payoff, approximate by finite calendars, moving
late finite mass to Never with vanishing error uniformly over deadlines.
Concatenate two independent copies, using a spare empty date between them.
In the first block an early deadline is priced as before, with the empty
separator allowing a zero singleton on survival. A deadline in the second
block has value e_i of the first block plus its opponent-survival probability
times the second deadline value. Thus in the limit all caps are at most
zero, the prescribed payoffs are zero, and the original Never product is
m^2<m. This excludes the all-zero case as well.

## Returning to the same minimum

Take a minimizing Y with payoff u. AllContinue fails the finite-stage Nash
test over u, since some u_i<0 and the own singleton pays zero. Finite-game
Nash existence supplies a nonempty row over Y. Every such row must give
strictly positive payoffs to all players, since otherwise prefixing would
reduce m at an eligible point. Its support contains neither 1 nor 2 by
their participant signs. A solo mover would receive its zero singleton,
so the support is exactly 03. Its finite positive hazard odds are D0 for
player 0 and A for player 3. Indifference and the two positive passive
payoffs give

    u0=-A, u3=D0,
    u1>6(D0-A),   u2>5A-D0-Z2(03) A D0.                    (4)

Indeed indifference at 0 and 3 reads u0=(3-4)A,
u3=(2-1)D0. The passive payoff numerators are u1-6D0+6A+
Z1(03)A D0 and u2+D0-5A+Z2(03)A D0. Both are positive.
It suffices now to construct one nonempty Nash row over the **same** Y
in which player 2 quits with positive probability. Its player-2 payoff
is then nonpositive and its Never product strictly below m. Y itself is
the minimizing point in this comparison. No later tail is minimized.

For clarity, the Continue-minus-Quit gap for a player i, divided by the
positive probability that every opponent continues now, is

    u_i + sum over nonempty opponent subsets T of
                 H_i(T) times the product of the hazard odds in T.     (5)

Only players assigned positive odds occur in this sum. A mixing player
needs equality and a quiet player needs a nonnegative result.

The identities below also give a necessary condition throughout (1), including
tables outside (2) and (3). At a negative restricted minimizer neither
applicable pair of quiet gaps below can be simultaneously nonnegative
with its indicated finite, nonnegative odds and positive player-2 odds.
This removes individual continuations even when a whole-table sign test
does not apply.

### Two pairs

If u2=-C<=0, (4) gives D0>5A+C+4AD0 and u1>24A+6C, in particular A<1/4.
Assign odds x=C/(1+v) to 0 and y=A/d to 2. Their two equalities in (5)
hold, including x=0. The two quiet gaps, already divided as in (5), are

    u1+x-(4+j)y+H1(02)xy,     D0-x-hy+H3(02)xy.

The first exceeds (24d-4-j)y+(7+6v)x+H1(02)xy.
The second exceeds (5d-h)y+vx+H3(02)xy. Since y<1/(4d),
(2) makes both positive. Player 2 has positive odds throughout.

If u2=C>0, take an actual approximating sequence for Y and pass to
subsequences of the literal date-zero hazards and the continuation tuples.
When a first row is sure, a continuation can be specified arbitrarily
off-path. Positive original Never at Y ensures that the limiting row is
proper. The cap formula gives Q_i<=u_i, with equality for each positive
hazard, since the difference B_i-U_i at the prefixed point is the sum of the
nonnegative weighted action gaps and the propagated tail debt. Thus q2=0.
If q1=0 also, Q0=3q3>=0 contradicts u0=-A. Hence q1>0 and u1<=0.
Furthermore Q0 is a convex combination of 0,-1,3,Z0(013), so A<=M0.
It follows from (4) that 0<D0<A and C>4A(1+D0).

Assign odds x=D0/h at 2 and y=C/e at 3. Both equalities hold, and
y>A(1+D0), x<=3D0/2. The quiet gaps are

    -A+dx+y+H0(23)xy,         u1-(4+j)x+7y+H1(23)xy.

Here y-A>yD0/(1+D0)>=hxy/(1+M0). Also
u1-(4+j)x+7y>6(D0-A)-4x+7y>y, and x<=M0/h.
Conditions (2) make both gaps positive.

### A row containing players 2 and 3

Treat both signs of u2 together. At odds x,y,z for 0,2,3 respectively,
the active equations at 3 and 2 in (5) are solved by

    x(y)=(D0+n y)/(1+g y),
    z(y)=(u2+(1+v)x(y))/(e+k x(y)).

Follow these functions from y=0 to the earliest available endpoint,
taking y=1/b if b>0 and the first zero of D0+n y if n<0. If neither occurs, continue
to infinity. The denominator 1+g y is strictly positive on this interval,
x>=0, and z is continuous and bounded because e,k>0. At y=0, equation
(4) gives z(0)>A, since e<=5, k<=-Z2(03) and v>=0. The quiet gap at 0
is

    F(y)=(1-b y) z(y)-A-a y.

It is positive initially. A first zero of z would make F strictly
negative. At y=1/b, F is also strictly negative. In the unbounded case
b=0 and a>0, so F eventually becomes negative. Therefore either F=0
at some positive y with z>0, or the path reaches x=0 with z>0 and F>=0.
In the latter case player 0 stays quiet. Its indifference is unnecessary,
and the indifferences at players 2 and 3 still hold. At the chosen point

    z>=A+a y+b y z.

In both cases the quiet gap at 1 is
u1+x-(4+j)y+7z+L xz+H1(02)xy+H1(23)yz+H1(023)xyz. Substitution of
the last lower bound into 7z and L xz bounds the gap below by

    u1+7A+(1+L A)x+[7a-4-j]y
        +[H1(02)+a L]xy+[H1(23)+7b]yz+[H1(023)+b L]xyz.

This is strictly positive by (3) and (4). The resulting row has active
player 2, and completes the contradiction to A_Z>0.

## From absorption to the original game

For each error we now have an actual absorbing native profile with
arbitrarily small total debt. To treat arbitrary signed own levels,
first give two players zero Never mass. Write M=max(1,max|Z_i(S)|).
At an absorbing profile choose i with N_i=0 and j with Gamma_ij<=0,
available in every row of (1). At a sufficiently late date T, the old
probability that i survives to T is at most delta, and the sum over all
players of physical finite mass on dates at or beyond T is at most delta.
Keep all hazards before T. Conditional on survival, make i quit at T,
let j use a positive constant hazard at most delta from T onward and
let everyone else continue forever. Both i and j now quit eventually
almost surely.

Prescribed payoffs and every deadline value for players other than i
change by at most 2M delta, by coupling up to T. For i, deadlines before T
are unchanged. Write p0 for the old expected contribution from opponents
who have already quit before T. The old deadline T earns at least p0-M delta.
In the new tail, i's own singleton pays zero, j's singleton gives i at
most zero, and a tie with j has conditional probability at most delta at
any fixed deadline. Hence every new deadline at or after T, including
Never, earns at most p0+M delta. This bounds every increase in debt by
4M delta. With two almost-sure quitters, absorption now occurs under every
unilateral replacement. Adding s_i to every absorbing payoff and scaling
the native row by l_i therefore transforms every such expected payoff
exactly. Original total debt tends to zero.

The checked semantic endpoint is
`quittingGame_exists_uniformEquilibriumPayoff_of_terminalNash_all_errors`
in `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`.
Apply it to the original terminal profiles just obtained. It selects a
single payoff before the accuracy. The implementation's general target is
`quittingUniformEquilibriumPayoffConjecture` in
`UniformEquilibrium/Quitting/Conjecture/Basic.lean`. The two raw sufficient
tests and their restricted-minimum proof here are ordinary mathematics.

## Boundary tests and formalization

The following two tables satisfy (2) and (3), respectively. Set L0=10^11. Each row lists
the four native payoffs in player order. The singleton rows are given
by (1).

| Coalition | Two pairs | Row containing 2 and 3 |
|---|---|---|
| 01 | (-1,-7,4,0) | (-1,-7,4,0) |
| 02 | (-6,0,-1,0) | (-4,0,-1,0) |
| 12 | (0,-1,-1,0) | (0,-3,-1,0) |
| 012 | (-1,-1,-1,0) | (0,-1,-1,0) |
| 03 | (3,0,-4,2) | (3,0,-4,2) |
| 13 | (3,-1,-L0,-2) | (0,-1,0,-2) |
| 013 | (2,-8,-L0,0) | (2,-8,0,0) |
| 23 | (1,-1,-3,5) | (0,0,-3,3) |
| 023 | (0,0,-5,1) | (1,-2,-2,1) |
| 123 | (0,-1/2,-1,-1) | (0,-1,-1,0) |
| 0123 | (-1,-1,-1,-1) | (0,-1,-1,0) |

In the first table p=6,h=d=1,e=2,H3(02)=-1 and H1(23)=-1/2. In the second,
a=b=g=1,e=k=2,L=8 and H1(023)=-1. No pure absorbing profile is a
terminal equilibrium on either table. In increasing order of the binary
coalition mask (player 0 is bit zero), the two lists give players who
strictly gain by toggling membership at the first absorbing date.

    (2)  3,0,1,1,0,2,0,2,0,1,0,1,0,3,0
    (3)  3,0,1,0,2,2,1,2,0,0,1,0,1,1,2.

The resulting coalitions are nonempty in all thirty comparisons, so
these checks also survive every signed offset and positive row scaling.

In fact the first table has no one-stage Nash row with a sure quitter
over *any* continuation, including the punishment vector. Write “sure”
and “quiet” for quitting probabilities one and zero. Each implication
here follows by comparing the two raw rewards for every possible coalition
of the remaining opponents. Once one opponent is sure the continuation
does not enter that comparison.

* If 0 is sure, 1 is quiet, then 3 is sure, then 2 is quiet. Player 0
  gains by withdrawing from 03.
* If 1 is sure, 0 cannot be sure by the preceding case. Player 3 is
  quiet because its joining differences on 1,01,12,012 are negative except
  for equality on 01, and 0 continues with positive probability.
  Then 2 is quiet, 0 joins 1 surely, a contradiction.
* If 2 is sure, 0 is quiet, then 1 is sure, already excluded.
* If 3 is sure, 0 is quiet, then 2 is sure, already excluded.

This tests the entire selection set of the instant-punishment producer
characterized in
`UniformEquilibrium/Quitting/Classification/InstantPunishmentSureQuitterCharacterization.lean`.
It also defeats every quiet-child extension that must work for *all*
absorbing zero-debt profiles of some proper nonempty child. In increasing
order of the fourteen child masks, the following pairs give a child
equilibrium consisting of its listed mask of sure quitters at date zero
and an omitted player who strictly gains by joining it.

    (1,3),(2,0),(1,3),(4,1),(1,3),(2,0),(1,3),
    (8,2),(8,2),(2,0),(8,2),(12,1),(12,1),(2,0).

The second table has the same obstruction, with list

    (1,3),(2,0),(1,3),(4,0),(1,3),(2,0),(1,3),
    (8,2),(8,2),(2,0),(8,2),(4,0),(13,1),(2,0).

On the first table every proper stationary row with support exactly 013
also fails in the full game. Here are bounds uniform over *all* its roots.
Use a,b,c' for its 0,1,3 hazards and t=max(a,b,c'). Write
F_i=(1-H_i^c)Q_i-P_i for stationary Quit advantage times the opponent
absorption probability. At a core interior root all three F_i vanish.
All core rewards have absolute value at most 8. Each partial derivative
of F_i has absolute value at most 40 (Q_i and P_i have derivatives at
most 16). The product term is bounded by 32t^2 and the passive mixed
correction by 24t^2, giving |F_i+(Gamma_SS q)_i|<=56t^2. The infinity
operator norm of Gamma_SS^{-1} is 17/6. Hence t>1/160.

When b=c'=0 one has 2F1+7F3=5a. Comparing each F with its root and
using independence of its own coordinate gives a<=72 max(b,c').
Also F0(0,c')=c'(3c'-4) and F0(b,0)=b(2-b), so b<=40c' and c'<=40b.
Thus b c'>1/[40(72 times 160)^2]. Since both 13 and 013 pay player 2
-L0, P2<=4-L0 b c', while Q2>=-5. Consequently F2>=L0 b c'-9>0.
Player 2 gains by joining. The raw proof above covers this table without
requiring any stationary strategy. The comparison concerns the whole
013 face with these three active players and does not classify full
four-player stationary roots.

A separate exact continuation shows the effect of the pointwise exclusion
even off both solved raw sets. Keep (1) and set Z1(03)=0, Z2(03)=-4.
Use the four assignments below. The other entries can be chosen freely
subject to (1).

    Z(02)=(-6,0,-1,11), Z(23)=(4/5,0,-3,5),
    Z(023)=(14/5,196,-4,9), J12=-1, Z1(012)=-1.

Give each of 0,2,3 hazard 1/2 at date zero and Never thereafter, with 1
always quiet. Over the zero tail all three active equalities in (5) hold.
The resulting actual zero-debt point has payoff
u=(-1/20,24,-2,4), since player 1's immediate Quit offer is nonpositive.
Prefixing the 03 row with odds 4,1/20 yields a genuine positive-payoff
point of E. The old positive-head guards and the last-atom support 023
therefore both occur on actual clocks. Yet the 02 row with odds 1,1/20
has both quiet gaps positive, returns player 2 a nonpositive payoff and
lowers the initial Never product from 1/8 to 5/84. Thus u is excluded at
the original restricted minimum. Here H0(23)=-2 defeats (2) when
Z0(013)=2, and p=6 defeats (3). This comparison needs no claim that the
initial point was a minimizer or that this particular table has positive
absorbing gap.

A limit of the one-stage argument can be checked without solving for
a clock. Take the continuation u=(-1/20,6,-1/4,1) and set Z1(03)=0,
Z2(03)=-4, Z1(013)=-8. For any remaining opponent set containing 2
choose player 1's joining reward strictly below its passive reward and
nonpositive. Require H0(2)=-1/20, H0(23)=1, H3(2)=1, H3(02)=-1.
These finite assignments are compatible with (1). Continuing is strictly
dominant at 1. Regardless of player 2's mixed move, the actual
Continue-minus-Quit gaps at 0 and 3 depend only on the other of those
two players. In odds notation their signs are those of z-1/20 and 1-x,
where x,z denote the odds at 0 and 3. This follows by factoring 1+y out
of (5), with y the odds at 2, and extends to pure endpoints from the
original affine gaps. There is no pure boundary equilibrium of this
two-player game, so its unique response pair has x=1,z=1/20.
Against it, player 2's passive numerator is
-1/4+1-5/20-4/20=3/10>0, and its joining reward is nonpositive.
The unique full row is therefore 03, and every prescribed payoff there
is positive. This shows why the static guard (4) alone cannot cover
every completion of (1). Realization of this particular annotation at
a restricted minimum is a separate condition.

A formalization can isolate the compact prefix identity and the restricted
minimum first, then prove the two return statements directly from (5).
The second return uses the intermediate value theorem on a single real
variable. The signed shift step only needs a nonpositive off-diagonal
singleton in each row. Games outside the two reward classes still require
a separate argument.
