# Exact negative-search screen for the positive-solo deadlock fibre

**Identity:** `CODEX_NEGATIVE_CERTIFICATE`  
**Status:** exact search reduction plus one ordinary-mathematics integer
completion with no stationary terminal Nash profile, now closed positively by
an exact period-three product block; the new block proof awaits independent
review  
**Current consequence:** the displayed stationary-free table is not a
counterexample: it has a fixed uniform-equilibrium payoff realized by the
periodic supports `{0}`, `{2}`, `{1,3}`.  This is an exact ordinary-mathematics
application of the checked unrestricted block consumer, not a whole-fibre
theorem

## Exact question

Let the players be `Fin 4` and fix the normalized singleton matrix

```text
M = [ 0  3 -1  3
      2  0  1 -3
      2 -2  0 -1
     -1 -2  1  0 ].
```

For arbitrary baseline `s`, consider every reward table satisfying

```text
r_i({j}) = s_i + M_(i,j).
```

The 44 nonsingleton coordinates are free.  Can a positive-solo member of this
48-dimensional fibre survive the exact easy-exit screens and support an
all-behavior positive exploitability certificate?

This note isolates the exact finite conditions that any such candidate must
meet.  It does not optimize a bounded controller, horizon, word length, or raw
numerical score.

## Why this is genuinely beyond the fullCore balanced cycle

The checked definition `FullCoreDeadlock.deadlockMatrix` and actual-data class
`IsFullCoreDeadlockCompletion` are in

```text
UniformEquilibrium/Quitting/Classification/LCP/FullCore/
  DeadlockChargedReturn.lean
```

The checked theorem
`ReducedIdealSingletonLasso.debt_pos` is in

```text
UniformEquilibrium/Quitting/Classification/LCP/FullCore/
  DeadlockReducedSingletonLassoBarrier.lean
```

It proves that every finite reduced ideal-singleton lasso for this matrix has
strictly positive debt at every phase.  The ordinary adapter recorded and
independently reviewed in Proposition 16 of
`CODEX_GAUSS__CURL_FREE_TOGGLE_POTENTIAL.md` gives the exact contradiction
from a hypothetical `BalancedSingletonCycleCertificate`:

1. delete zero-hazard phases and compose cyclically adjacent phases with the
   same owner;
2. subtract the own-singleton baseline from every coarse value;
3. use `soloFloor` for nonnegative clearances and `active` for zero owner
   clearance;
4. reverse the cyclic phase word so the Bellman arc has the checked
   `idealSingletonClearance` orientation; and
5. put debt identically zero.  The balanced arc and floor fields make every
   local clipping charge zero, producing a `ReducedIdealSingletonLasso` with
   zero debt, contrary to `debt_pos`.

This argument reads only the normalized singleton matrix.  Therefore every
baseline lift and every nonsingleton completion is outside the balanced
singleton-cycle certificate language.  This is not a nonexistence theorem:
joint quitting blocks can still give a UE.

## The checked joint-block chamber that must be removed

`DeadlockRationalPolyhedralBlock.lean` defines
`IsDeadlockRationalJointBlockCompletion reward s`.  It assumes the deadlock
singleton rows, requires

```text
r({1,3}) = s,
```

and imposes eight explicit linear upper bounds on the relevant collision
coordinates.  The checked theorem

```text
isUniformEquilibriumPayoff_of_isDeadlockRationalJointBlockCompletion
```

gives the fixed target

```text
s + (0, 5/7, 8/21, 1/7)
```

through a three-phase product block with supports `{0}`, `{2}`, and `{1,3}`.
Its semantic consumer is unrestricted: it is not only a one-shot or
bounded-clock witness.  Thus any negative search inside the deadlock fibre
must certify the negation of this raw-data predicate (and of any separately
proved relabelled or alternative joint-block predicate) before treating the
matrix as hard.

The eight checked inequalities, copied by declaration name rather than
silently paraphrased, are:

```text
pair_zero_one_one, pair_zero_two_two, pair_zero_three_three,
pair_zero_two_zero, pair_one_two_one, pair_two_three_three,
joint_cap_zero, joint_cap_two.
```

The first six are pair-coordinate bounds and the last two are rational linear
caps involving pair and triple coordinates.  The slice is unbounded and
allows arbitrary-sign baselines; it is not just the literal zero-multiquitter
table.

## Exact stationary pair lemma

Fix two players `i != j`, prescribe positive stationary hazards only for
`i,j`, and make every other player Continue.  Put

```text
d_i = r_i({i}),       a_i = r_i({j}),
c_i = r_i({i,j}),
```

and define `d_j,a_j,c_j` symmetrically.  Against player `j`'s stationary
hazard `q_j>0`, player `i`'s Never payoff is exactly `a_i`, while Quit-now
pays

```text
(1-q_j)d_i + q_j c_i.
```

Hence player `i` is indifferent exactly when

```text
q_j = (d_i-a_i)/(d_i-c_i).                         (P1)
```

This lies strictly in `(0,1)` exactly in either of the two orientations

```text
c_i < a_i < d_i     or     d_i < a_i < c_i.        (P2)
```

The same formula with `i,j` reversed gives `q_i`.  If (P2) holds for both
players and every spectator's Quit-now value is at most its Never value at
the two displayed hazards, then the stationary profile is an exact terminal
Nash profile against every behavioral deviation.  The unrestricted upgrade
is elementary: against stationary opponents, any pure stopping time receives
the Never payoff until its stopping date and the Quit-now payoff conditional
on reaching that date; randomized history-dependent stopping laws are
mixtures/limits of those choices.  Thus no behavioral deviation beats the
maximum of Quit-now and Never.  The active pair is indifferent by (P1), and
the spectator inequalities select Never.

This is an exact stationary certificate, including boundary policies Never;
it is not a sampled pair-controller test.

## The six deadlock pair chambers at baseline one

Set `s=(1,1,1,1)` and write `c_i^{ij}=r_i({i,j})`.  The cross-singleton
values are fixed by `M`.  Condition (P2) becomes the following six exact
open chambers:

| active pair | condition on its two member coordinates | hazards |
|---|---|---|
| `{0,1}` | `c_0^{01}>4`, `c_1^{01}>3` | `q_1=3/(c_0^{01}-1)`, `q_0=2/(c_1^{01}-1)` |
| `{0,2}` | `c_0^{02}<0`, `c_2^{02}>3` | `q_2=1/(1-c_0^{02})`, `q_0=2/(c_2^{02}-1)` |
| `{0,3}` | `c_0^{03}>4`, `c_3^{03}<0` | `q_3=3/(c_0^{03}-1)`, `q_0=1/(1-c_3^{03})` |
| `{1,2}` | `c_1^{12}>2`, `c_2^{12}<-1` | `q_2=1/(c_1^{12}-1)`, `q_1=2/(1-c_2^{12})` |
| `{1,3}` | `c_1^{13}<-2`, `c_3^{13}<-1` | `q_3=3/(1-c_1^{13})`, `q_1=2/(1-c_3^{13})` |
| `{2,3}` | `c_2^{23}<0`, `c_3^{23}>2` | `q_3=1/(1-c_2^{23})`, `q_2=1/(c_3^{23}-1)` |

Each formula follows directly from (P1); no solver is used.  The two remaining
spectator inequalities are rational polynomial inequalities after these
hazards are substituted and denominators (positive in the displayed chamber)
are cleared.

Consequently, orienting a singleton--pair--singleton two-cycle by placing each
member's pair payoff beyond its cross-singleton payoff automatically creates
an interior stationary pair root.  Such a no-pure-coalition gadget is not a
negative candidate unless a spectator has a certified profitable join at
that exact root.

### Exact regression

The first rational no-pure completion tried in this fibre used

```text
r_2({2,3})=-1,   r_3({2,3})=3.
```

The last row of the table gives exactly `q_2=q_3=1/2`.  With the attempted
spectator rows, both spectators weakly preferred Never, so this was an exact
stationary all-behavior Nash profile.  The completion is rejected.  Retaining
this failed implication prevents a future raw search from rediscovering the
same pair trap.

## An exact all-pure/all-pair survivor, rejected at a larger stationary face

The following integer table is a stronger regression.  Rows are in coalition
mask order and coordinates are players `0,1,2,3`:

```text
{0}       ( 1,  3,  3,  0)
{1}       ( 4,  1, -1, -1)
{0,1}     ( 5, 18,-18, 17)
{2}       ( 0,  2,  1,  2)
{0,2}     (12,  3, 14,  8)
{1,2}     (12,  3,  0,-19)
{0,1,2}   ( 3,  9,  0,  4)
{3}       ( 4, -2,  0,  1)
{0,3}     ( 5, -5, 18,-19)
{1,3}     (-9,  0, -9,  0)
{0,1,3}   (12, 12,  3, 12)
{2,3}     (15,  9,  8,  6)
{0,2,3}   (16,  3, 17,  2)
{1,2,3}   (10,  8,-10,  5)
{0,1,2,3} ( 9, 13, -5, 11).
```

Its singleton differences are exactly `deadlockMatrix`, and all own solos are
one.  It is outside the checked rational joint-block slice already because

```text
r({1,3})=(-9,0,-9,0) != (1,1,1,1)=s.
```

### No pure sure-exit coalition

For every nonempty coalition, the following list gives an improving toggle as

```text
(source mask, toggler, destination mask, exact gain):
```

```text
( 1,1, 3,15)   ( 2,2, 6, 1)   ( 4,3,12, 4)   ( 8,0, 9, 1)
( 3,2, 7,18)   ( 6,3,14,24)   (12,0,13, 1)   ( 9,1,11,17)
( 5,1, 7, 6)   (10,0,11,21)
( 7,0, 6, 9)   (14,1,12, 1)   (13,2, 9, 1)   (11,3, 3, 5)
(15,0,14, 1).
```

When the toggler is outside the source it joins; when inside it leaves.  The
list contains all 15 nonempty masks, so no deterministic sure-exit coalition
is Nash.  The all-Never profile is not Nash because every solo is one.

### All six active-pair supports are excluded exactly

For pair `{i,j}`, the member gap against the other member's positive hazard
is affine:

```text
F_i(q_j)=d_i-a_i+q_j(c_i-d_i).
```

An active member is indifferent when its hazard is interior and has
`F_i>=0` when it Quits surely.  Enumerating the root and sure endpoint of
these two affine functions gives the complete list of member-feasible points.
The following table lists them and one exact profitable spectator gap
`Quit-now - Never`:

| pair | member-feasible hazards `(q_i,q_j)` | escaping spectator and gap |
|---|---|---|
| `{0,1}` | `(2/17,3/4)` | player 2: `12275/3604` |
|           | `(1,1)`     | player 2: `18` |
| `{0,2}` | `(1,1)` | player 1: `6` |
| `{0,3}` | `(1/20,3/4)` | player 1: `14533/4880` |
| `{1,2}` | `(1,1)` | player 3: `24` |
| `{1,3}` | `(1,1)` | player 0: `21` |
| `{2,3}` | `(1,1)` | player 0: `1` |

There are no other active member-feasible points.  For reproducibility, the
six ordered indifference roots `(root q_j for i, root q_i for j)` are

```text
{0,1}: (3/4, 2/17)    {0,2}: (-1/11, 2/13)
{0,3}: (3/4, 1/20)    {1,2}: (1/2, 2)
{1,3}: (3, 2)          {2,3}: (-1/7, 1/5).
```

Roots outside `(0,1)` cannot be an interior hazard.  Mixed/sure combinations
not listed fail the sure member's sign inequality.  A singleton active
support reduces to its sure-quitter vertex because the own solo is one; the
pure-toggle audit above then supplies an outsider deviation.  Hence every
stationary support of cardinality at most two is excluded by exact rational
arithmetic.

### Exact larger-face rejection

Despite those simultaneous screens, the stationary vector

```text
q=(1/11, 1/2, 1, 1)
```

is an exact unrestricted terminal Nash profile.  Players `2,3` Quit surely,
so absorption occurs at date zero even after either player `0` or `1`
deviates.  Exact Quit-now and Never values are

| player | Quit-now | Never | difference |
|---:|---:|---:|---:|
| 0 | `25/2` | `25/2` | `0` |
| 1 | `93/11` | `93/11` | `0` |
| 2 | `-4/11` | `-69/22` | `61/22` |
| 3 | `123/22` | `-79/11` | `281/22` |

Thus mixed players `0,1` are indifferent and sure quitters `2,3` strictly
prefer Quit.  Since at least one opponent Quits surely for every player, any
behavioral stopping replacement is resolved immediately; no late-clock or
Never seam is hidden.  The prescribed payoff is exactly

```text
(25/2, 93/11, -4/11, 123/22).
```

The two active indifference polynomials on the face `q_2=q_3=1` reduce to

```text
1-2q_1=0,   11q_0-1=0,
```

which explains the rational hazards without numerical solving.

This table proves an exact limitation of the reduced search: positive solos,
no pure exit, no balanced singleton cycle, escape from the named rational
joint-block slice, and strict spectator escape on all six pair supports are
still insufficient.  Sure-quitter boundary faces with a remaining mixed pair
must be included in the “triple/full” stationary elimination, even though the
support of positive hazards is all four players.

## Full stationary semialgebraic screen

For a general stationary hazard vector `q in [0,1]^4`, let

```text
A_i(q) = product_{j != i} (1-q_j).
```

Let `Q_i(q_-i)` be player `i`'s one-stage expected payoff after choosing Quit,
and let `R_i(q_-i)` be the unnormalized expected reward from a nonempty
opponent quitting coalition when `i` chooses Continue.  If some opponent has
positive hazard, Never pays

```text
N_i(q_-i) = R_i(q_-i)/(1-A_i(q)).
```

Define the polynomial

```text
P_i(q) = Q_i(q_-i)*(1-A_i(q)) - R_i(q_-i).           (S1)
```

On every face with positive opponent absorption, exact stationary Nash is the
finite complementarity system

```text
q_i = 0       -> P_i <= 0,
0 < q_i < 1   -> P_i = 0,
q_i = 1       -> P_i >= 0.                           (S2)
```

The all-Never corner is handled separately: with positive solos it is not
Nash.  All coefficients in (S1) are rational for a rational reward table.
Thus stationary exclusion is a finite exact semialgebraic obligation over all
`3^4` zero/interior/one faces, including sure-quitter seams; an interior
sigmoid optimizer is not an exclusion.

For the deadlock fibre, the six pair systems above should be substituted and
cleared first.  Candidate generation should then use explicit join-dominance
inequalities to eliminate proper supports where possible, leaving only named
triple/full-support systems for CAD, resultants, Sturm certificates, or exact
Positivstellensatz output.  A floating failure to solve (S2) is not evidence.

## A compact integer completion passing the full stationary screen

The following completion was obtained symbolically, not by optimizing a raw
stationary score.  It keeps the baseline-one deadlock singleton rows.  In mask
order its complete reward table is

```text
{0}       ( 1,  3,  3,  0)
{1}       ( 4,  1, -1, -1)
{0,1}     ( 1,  1,  1, -2)
{2}       ( 0,  2,  1,  2)
{0,2}     ( 1,  4,  1,  1)
{1,2}     ( 3,  1,  1,  0)
{0,1,2}   ( 1,  1,  1, -1)
{3}       ( 4, -2,  0,  1)
{0,3}     ( 1,  0,  2,  1)
{1,3}     ( 7,  1, -2,  1)
{0,1,3}   ( 1,  1,  0,  1)
{2,3}     ( 3, -1,  1,  1)
{0,2,3}   ( 1,  1,  1,  1)
{1,2,3}   ( 6,  1,  1,  1)
{0,1,2,3} (11, -1,  1,  0).
```

This is ordinary exact mathematics, not yet a Lean declaration.  The table is
outside `IsDeadlockRationalJointBlockCompletion`, since already

```text
r({1,3})=(7,1,-2,1) != (1,1,1,1).
```

### Symbolic origin and exact gain formulas

There is a unique baseline completion in which the four stationary gain
numerators are the linear forms `-M q`.  Its nonsingleton rows agree with the
displayed table except that the grand row is `(1,1,1,1)`.  This uniqueness is
the solution of the four independent exact coefficient-matching systems:
for each payoff coordinate, cancel every mixed monomial in (S1).  The displayed
grand row then adds

```text
delta=(10,-2,0,-1).
```

Put

```text
D_i = 1 - product_{j != i}(1-q_j),
B_i = D_i * product_{j != i} q_j.
```

Changing only player `i`'s grand reward by `delta_i` adds exactly
`delta_i B_i` to (S1).  Direct expansion therefore gives

```text
P_0 = -3q_1 + q_2 - 3q_3 + 10B_0,
P_1 = -2q_0 - q_2 + 3q_3 - 2B_1,
P_2 = -2q_0 + 2q_1 + q_3,
P_3 =  q_0 + 2q_1 - q_2 - B_3.                 (S3)
```

This also explains why the construction is stable under the easy screens:
every `B_i` vanishes when at most two hazards are positive, and on a
three-player support it vanishes for each active player.

### Exact audit of supports of size at most three

The all-Never corner is not Nash because every own solo equals one.  On a
singleton support, the active owner prefers its payoff one to nonabsorption;
the following spectator has `P_i>0` and joins:

```text
owner 0 -> spectator 3,   owner 1 -> spectator 2,
owner 2 -> spectator 0,   owner 3 -> spectator 1.
```

On a two-player support, (S3) is `P=-Mq`.  All off-diagonal entries of `M`
are nonzero, so an active member can mix only if an impossible nonzero linear
term vanishes.  Both members can prefer sure Quit only for `{1,3}`; there
`q_1=q_3=1`, but spectator `2` has `P_2=3>0`.  Thus every pair support is
excluded.

For a support of size three, the active-member system is again `P=-Mq`.
Exact substitution in its `2^3` mixed/sure faces gives the complete list of
member-feasible profiles:

| inactive player | member-feasible stationary rates |
|---:|---|
| 0 | `(0,1/2,1,1/3)`, `(0,1,1,1)` |
| 1 | none |
| 2 | none |
| 3 | none |

At the first listed profile, player `0`'s linear term is `-3/2`, while
`B_0=1/6`, so `P_0=1/6>0`.  At the second it is `-5`, while `B_0=1`, so
`P_0=5>0`.  The inactive player therefore joins in both cases.  This is an
exact exhaustion of all proper nonempty supports; it also supplies the pure
sure-exit audit rather than assuming it separately.

### Exact audit of the sixteen full-support faces

Write `M` for a mixed coordinate and `Q` for a sure-Quit coordinate.  The
four faces with exactly three `Q` coordinates have, for the remaining mixed
player `0,1,2,3`, respectively, the constant equation

```text
5=0,  -2=0,  1=0,  1=0.
```

At the all-`Q` vertex the gain vector is `(5,-2,1,1)`, so player `1`
prefers Continue.  The six faces with exactly two mixed coordinates are
exhausted as follows.  A displayed negative sure-player gain rejects the
otherwise interior mixed root.

| mixed players | exact mixed solution or obstruction |
|---|---|
| `{0,1}` | `(q_0,q_1)=(1/2,2/7)`, but `P_3=-1/14` |
| `{0,2}` | `q_0=3/2` |
| `{0,3}` | the mixed equation for player `3` is `1=0` |
| `{1,2}` | `(q_1,q_2)=(1/2,1/3)`, but `P_0=-5/2` |
| `{1,3}` | equations force `q_3=3` and `q_1=0` |
| `{2,3}` | equations force `q_3=0` and `q_2=3/2` |

For the four faces with exactly one sure quitter, the three mixed equations
have two algebraic solutions each.  For sure player `0`, the two triples
`(q_1,q_2,q_3)` are

```text
(2-3sqrt(2)/2, 4/3-sqrt(2)/3, -2+3sqrt(2)),
(2+3sqrt(2)/2, 4/3+sqrt(2)/3, -2-3sqrt(2)).
```

The first has `q_1<0` and `q_3>1`; the second is also outside the cube.  For
sure player `1`, the two triples `(q_0,q_2,q_3)` are

```text
((-9+sqrt(571))/14, (34+sqrt(571))/39, (-23+sqrt(571))/7),
((-9-sqrt(571))/14, (34-sqrt(571))/39, (-23-sqrt(571))/7).
```

The first has `q_0>1` and `q_2>1`, while the second has negative coordinates;
use `23^2<571<24^2`.  For sure player `2`, the two triples
`(q_0,q_1,q_3)` are

```text
(1/4-sqrt(17)/12, (43+3sqrt(17))/106, (19-3sqrt(17))/26),
(1/4+sqrt(17)/12, (43-3sqrt(17))/106, (19+3sqrt(17))/26).
```

The first has `q_0<0`; the second has `q_3>1`, using `4^2<17<5^2`.
For sure player `3`, the two solutions are nonreal:

```text
(q_0,q_1,q_2)=
(8/13 ∓ sqrt(95)i/26, 3/26 ∓ sqrt(95)i/26,
 11/18 ± sqrt(95)i/18).
```

Thus no numerical root isolation is hidden in any boundary face.

It remains to rule out the fully mixed face without a large resultant.
Assume all four hazards lie strictly between zero and one and all four
equations (S3) vanish.  From `P_2=0`, put

```text
x=q_0,   a=q_1/q_0,   b=q_2/q_0,
q_3=2x(1-a).
```

The `P_1=0` and `P_0=0` equations become

```text
A := 4-6a-b = 2B_1/x > 0,
C := 6-3a-b = 10B_0/x > 0.                         (S4)
```

In particular `0<a<2/3` and `b<4-6a`.  Since `q_0>q_1` and the other two
hazards are interior, the opponent-absorption probabilities satisfy
`D_1>D_0`.  Cancelling the common positive factors in `B_0/B_1` gives

```text
C/A = 5a * D_0/D_1 < 5a.
```

Thus

```text
0 < 5aA-C
  = (1-5a)b - (30a^2-23a+6).                       (S5)
```

But

```text
30a^2-23a+6 = 30(a-23/60)^2 + 191/120 > 0.
```

If `a>=1/5`, the right side of (S5) is negative.  If `a<1/5`, its coefficient
of `b` is positive, so `b<4-6a` makes it strictly less than

```text
(1-5a)(4-6a) - (30a^2-23a+6) = -2-3a < 0.
```

Both cases contradict (S5).  Hence the fully mixed face is empty.  Together
with the preceding exact tables, this proves ordinary-mathematically that the
displayed completion has no exact stationary terminal Nash profile.

The implication from a stationary terminal Nash profile to (S2) is the
checked `isεQuittingRootNash_of_isεAsymptoticNash_stationary` followed, under
positive absorption, by
`isQuittingStationaryGainComplementary_iff_endpointNash`.  The calculations
above instantiate its polynomial field; they do not yet constitute a checked
Lean theorem for this new table.

## Positive closure by an exact period-three block

The same literal table has a nonstationary exact product block.  Number the
three phases `0,1,2` and put

```text
q^0 = (a,0,0,0),
q^1 = (0,0,b,0),
q^2 = (0,c,0,d).
```

Thus the positive-hazard supports are `{0}`, `{2}`, and `{1,3}`.  The four
active equations reduce exactly to

```text
F_0 =  3bc + 3bd + b - 3c - 3d,
F_1 = -2acd + 2ac + 2ad - 2a + 2c + d,
F_2 = -abd + ab + 2ad - 2a + bd - b + 3d,
F_3 = -abc + ab - ac + a + bc - b + 2c.          (B1)
```

Here `F_0,F_1` are also the two inactive tied gaps identified below; this is
important because they are not strict inactive inequalities.

### Exact rational isolating parallelotope

Let

```text
x = (2200649139/10^10,
     4455252923/10^10,
      598923293/10^10,
      415887857/(2*10^9)),

A = [ 7/20     -323/1000   137/500    631/1000
      213/250    22/125     309/1000    59/125
       7/100    267/1000    -69/1000    23/100
      253/1000  -19/250     101/250    141/500 ],

r = 1/10^6,
P = { x + A z : |z_j| <= r for j=0,1,2,3 }.
```

The determinant is the nonzero rational

```text
det A = -41914379009/10^12.
```

Straight interval addition gives the following coordinate hull for `P`:

```text
a in [2200633359/10^10, 2200664919/10^10] subset (11/50,23/100),
b in [4455234833/10^10, 4455271013/10^10] subset (11/25,9/20),
c in [ 598916933/10^10,  598929653/10^10] subset ( 1/20,3/50),
d in [415885827/(2*10^9),415889887/(2*10^9)] subset (1/5,21/100).
                                                               (B2)
```

This is an exact existence and uniqueness certificate, not floating-point
root evidence.  Set `G(z)=F(x+Az)` and `T(z)=z-G(z)`.  Direct rational
expansion gives

```text
F(x) = (
  1732473241/(5*10^19),
  7039082593629169961/10^29,
  12514868747864475471/(2*10^29),
 -69568260756753837021/10^30),
```

so `||F(x)||_infinity < 1/10^9`.  Expanding each entry of `DT` as a
polynomial in `z`, and bounding a monomial coefficient `u z^alpha` by
`|u|r^|alpha|`, gives the following four exact row-sum upper bounds:

```text
14618922367/10^13,
170910873577211158347/(5*10^22),
13928416905704981571/(3125*10^18),
191805008621195199843/10^23.                    (B3)
```

Each number in (B3) is strictly below `1/200`.  Hence `T` is a strict
contraction on the rational cube `[-r,r]^4`, and

```text
||T(z)||_infinity
 <= ||T(0)||_infinity + (1/200)||z||_infinity
 < 1/10^9 + 1/(200*10^6) < r.
```

The contraction theorem therefore supplies a unique `z_*` in that cube with
`T(z_*)=z_*`, equivalently `F(x+Az_*)=0`.  Put

```text
(a,b,c,d) = x + A z_*.
```

For an independent sign check, the same coefficient expansion shows that on
the face `z_i=-r`, `G_i<-99/10^8`, and on `z_i=r`,
`G_i>99/10^8`.  The exact lower margins before comparison with `99/10^8`
are

```text
24962771111137/(25*10^18),
99782438672735255019833/10^29,
199877926167001860463113/(2*10^29),
999457586075568031650689/10^30.                  (B4)
```

Thus Poincare--Miranda also proves existence in the same rational
parallelotope.  Banach gives the additional uniqueness there.

### Short exact phase values and all endpoint gaps

At this root define the four displayed rows `U^0,U^1,U^2,U^3` by

```text
U^0 = (1, 1+2a+b-ab, 1+2a, (1-a)(1+b)),
U^1 = (1, 1+b,       1,    1+b),
U^2 = (1+3c+3d, 1,   1,    1),
U^3 = U^0.                                             (B5)
```

The one-step recursion residual is identically zero except at

```text
(phase 1, player 0): F_0,
(phase 2, player 1): (1-c)F_2,
(phase 2, player 2): F_1,
(phase 2, player 3): (1-d)F_3.
```

Consequently (B1) makes every recursion exact.  The Quit-minus-Continue
endpoint gaps computed against the next row in (B5) are

| phase | player 0 | player 1 | player 2 | player 3 |
|---:|---:|---:|---:|---:|
| 0 | `0` | `ab-2a-b` | `-2a` | `ab+a-b` |
| 1 | `F_0` | `-b` | `0` | `-b` |
| 2 | `-3(c+d)` | `F_2` | `F_1` | `F_3` |

The four positive-hazard coordinates have zero gap.  Two inactive
coordinates, player `0` in phase 1 and player `2` in phase 2, are also exact
ties because their gaps are `F_0,F_1`.  Every other inactive gap is uniformly
strict throughout `P`.  Indeed (B2) gives

```text
ab-2a-b < -a-b < -1/2,
-2a < -2/5,
ab+a-b = a(1+b)-b
         < (23/100)(29/20)-11/25 = -213/2000 < -1/10,
-b < -2/5,
-3(c+d) < -3/4.                                  (B6)
```

This separates the six strict inequalities from the two structural ties and
proves the exact endpoint complementarity required by the block certificate.

### Checked consumer and fixed target

Instantiate `IsQuittingBlockCertificate` from
`UniformEquilibrium/Quitting/Cycles/BlockPeriodicProfile.lean` with period
three, hazards (B1), and rows (B5):

* probability bounds are (B2);
* the value recursion and last-row identity are the calculations above;
* every coordinate of (B5) lies in `(0,2)` by (B2), while the canonical
  reward bound is at least the absolute grand-row coordinate `11`;
* the gain field is exactly the endpoint-gap table and (B6);
* phase 0 absorbs with positive probability because `a>0`; and
* after deleting any one player's hazards, at least one opponent still has a
  positive hazard: use `b` for player 0 and `a` for players 1,2,3.

The checked theorem

```text
isUniformEquilibriumPayoff_of_isQuittingBlockCertificate
```

therefore yields a uniform-equilibrium payoff, against unrestricted
behavioral deviations, at the fixed target

```text
v = U^0 = (1, 1+2a+b-ab, 1+2a, (1-a)(1+b)).       (B7)
```

The algebraic root and target are chosen once, before the accuracy and horizon
quantifiers.  This closes the displayed table positively even though the
complete stationary-face audit above rules out every stationary terminal Nash
profile.

The present sign certificate does not by itself give a full-dimensional open
neighborhood of reward tables.  The two inactive equalities `F_0=F_1=0` are
not strict and can split under reward perturbation.  A robust-neighborhood
claim would need either one-sided control of those two gaps at the continued
root or an enlarged-support construction; neither is claimed here.

## Exact candidate class after this table is removed

A rational deadlock-fibre table is worth passing to escape-aware deadline and
late-clock certification only after it has exact evidence for all of:

1. strictly positive own singleton baselines (excluding all-Never);
2. no pure sure-exit coalition, checked on all 15 nonempty coalitions;
3. the matrix-level no-balanced-cycle bridge above;
4. negation of `IsDeadlockRationalJointBlockCompletion` and any other named
   joint-block chamber actually applicable to the table;
5. infeasibility of every stationary face system (S2), including all
   zero/one boundaries;
6. failure of all six pair roots after spectator inequalities are included;
7. exact persistent-base and finite-deadline screens; and
8. only then, an escape-aware all-behavior lower certificate retaining Never,
   mass escaping finite dates, product provenance, and unrestricted unilateral
   deviations.

The displayed completion passes items 1--6 by exact arithmetic but is removed
from the negative search by the exact period-three block above.  The list is
therefore a screen for the next candidate, not an unfinished obligation for
this table.  In particular, stationary nonexistence did not force any
deadline or late-clock analysis here.

## Source audit and nonclaims

Declarations inspected:

* `deadlockMatrix`, `IsFullCoreDeadlockCompletion`, and
  `normalizedSoloMatrix_reward` in `DeadlockChargedReturn.lean`;
* `ReducedIdealSingletonLasso` and
  `ReducedIdealSingletonLasso.debt_pos` in
  `DeadlockReducedSingletonLassoBarrier.lean`;
* `IsDeadlockRationalJointBlockCompletion` and
  `isUniformEquilibriumPayoff_of_isDeadlockRationalJointBlockCompletion` in
  `DeadlockRationalPolyhedralBlock.lean`;
* `BalancedSingletonCycleCertificate` and its unrestricted consumer in
  `BalancedSingletonCertificate.lean`; and
* `IsQuittingBlockCertificate`,
  `isQuittingBlockCertificate_of_root`, and
  `isUniformEquilibriumPayoff_of_isQuittingBlockCertificate` in
  `Cycles/BlockPeriodicProfile.lean`, together with
  `quittingRewardBound` and `abs_reward_le_quittingRewardBound` in
  `Quitting/RewardBound.lean`; and
* `quittingStationaryGain`, `IsQuittingStationaryGainComplementary`, and
  `isQuittingStationaryGainComplementary_iff_endpointNash` in
  `Stationary/Gain.lean`, together with
  `isεQuittingRootNash_of_isεAsymptoticNash_stationary` in
  `Stationary/Root.lean`; and
* `StochasticGame.Game.isεHorizonNash_iff` and
  `IsUniformEquilibriumPayoff` in `GameTheory/Stochastic/Uniform.lean`.

The deadlock rational joint-block chamber and global debt bounds are already
documented in `docs/FRONTIER.md`; they are inputs, not claimed as new results.
The new contribution here is the exact negative-search normalization, the six
closed-form pair chambers, the displayed integer completion with its exact
finite stationary-face exclusion, and its exact period-three unrestricted UE
closure.

Not proved:

* a whole-fibre UE theorem for arbitrary nonsingleton rewards;
* a full-dimensional open reward neighborhood covered by (B1)--(B7);
* a Lean-checked producer for the algebraic root (the consumer is checked, the
  rational contraction calculation is presently ordinary mathematics);
* a positive terminal exploitability gap; or
* the Fin4 conjecture.

## Next exact question

First subject (B1)--(B7) to an independent exact audit.  If it passes, determine
the largest one-sided semialgebraic reward chamber on which the same
parallelotope and endpoint signs persist, or enlarge the two tied inactive
coordinates into the active support to seek a genuinely open chamber.  Only
then return to a new negative candidate that survives both stationary and
short product-block screens.
