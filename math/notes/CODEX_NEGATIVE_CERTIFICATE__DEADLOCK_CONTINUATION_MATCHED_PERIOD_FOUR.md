# Deadlock continuation-matched pair slice: exact period-four exclusion

Identity: CODEX_NEGATIVE_CERTIFICATE

Status: exact ordinary-mathematics 20-dimensional fibre exclusion, recorded
under maintenance pause; not independently reviewed and not proposed for
export.

Current consequence: replacing the closed integer table's \(\{1,3\}\) row by
the structurally continuation-matched row \((0,-2,0,-1)\) kills the old
three-phase support, but opens an exact singleton-support block

\[
 \{0\}\longrightarrow\{2\}\longrightarrow\{1\}
 \longrightarrow\{3\}.
\]

Thus the replacement is a positive falsifier, not a negative survivor.

## Exact theorem

Let the players be \(\operatorname{Fin}4\), let Never pay zero, and fix the
following singleton and pair rows:

    {0}:   (1,  3,  3,  0)      {0,1}: (1,  1, 1,-2)
    {1}:   (4,  1, -1, -1)      {0,2}: (1,  4, 1, 1)
    {2}:   (0,  2,  1,  2)      {0,3}: (1,  0, 2, 1)
    {3}:   (4, -2,  0,  1)      {1,2}: (3,  1, 1, 0)
                                   {1,3}: (0, -2, 0,-1)
                                   {2,3}: (3, -1, 1, 1).

Allow all four triple rows and the grand row to vary arbitrarily.  The
resulting affine fibre has 20 free coordinates.  Every table in this fibre has
one fixed uniform-equilibrium payoff against unrestricted unilateral
behavioral deviations.

## Exact hazards

Put \(s=\sqrt{649}\).  Since \(25^2<649<26^2\), \(25<s<26\).  Define

\[
\begin{aligned}
a&=\frac{5(s-11)}{264},&
b&=\frac{331-7s}{324},\\
c&=\frac{s-23}{28},&
d&=\frac{193-s}{732}.
\end{aligned}
\tag{1}
\]

All four hazards lie strictly in \((0,1)\):

\[
 0<a<\frac{75}{264},\quad
 \frac{149}{324}<b<\frac{156}{324},\quad
 \frac2{28}<c<\frac3{28},\quad
 \frac{167}{732}<d<\frac{168}{732}.
\tag{2}
\]

The number \(d\) satisfies

\[
 366d^2-193d+25=0,
\tag{3}
\]

and the other hazards can equivalently be written

\[
 a=-\frac{5(366d-91)}{132},\qquad
 b=\frac{427d-85}{27},\qquad
 c=-\frac{366d-85}{14}.
\tag{4}
\]

At phases \(0,1,2,3\), respectively, let the unique positive-hazard player be
\(0,2,1,3\), with hazards \(a,b,c,d\).  All other coordinates Continue.

## Periodic value and target

Set

\[
 (o_0,o_1,o_2,o_3)=(0,2,1,3),\qquad
 (h_0,h_1,h_2,h_3)=(a,b,c,d),
\]

\[
 C_k=1-h_k,\qquad B_k=h_k r(\{o_k\}),\qquad
 H=1-C_0C_1C_2C_3>0,
\]

with subscripts read modulo four.  Define

\[
 U^k=
 \frac{B_k+C_kB_{k+1}+C_kC_{k+1}B_{k+2}
 +C_kC_{k+1}C_{k+2}B_{k+3}}{H},
\tag{5}
\]

and \(U^4=U^0\).  Expansion gives

\[
 U^k=B_k+C_kU^{k+1}.
\tag{6}
\]

The fixed target is \(v=U^0\).  It depends only on the fixed singleton rows.

## Active equations

Let \(\Delta_{k,i}\) be Quit value minus Continue value for player \(i\) at
phase \(k\), with tail \(U^{k+1}\).  The four active normalized gaps are

\[
\begin{aligned}
E_0=H\Delta_{0,0}
 &=-3bcd+3bc+3bd+b+3cd-3c-3d,\\
E_1=H\Delta_{1,2}
 &=-2acd+2ac+2ad-2a-cd+2c+d,\\
E_2=H\Delta_{2,1}
 &=-abd+ab+2ad-2a+bd-b+3d,\\
E_3=H\Delta_{3,3}
 &=2abc+ab-2ac+a-2bc-b+2c.
\end{aligned}
\tag{7}
\]

After (4), direct rational expansion gives

\[
\begin{aligned}
E_0&=\frac{(183d-170)(366d^2-193d+25)}{54},\\
E_1&=-\frac{(1830d-1741)(366d^2-193d+25)}{924},\\
E_2&=\frac{(2135d-2081)(366d^2-193d+25)}{3564},\\
E_3&=\frac{61(915d-149)(366d^2-193d+25)}{1782}.
\end{aligned}
\tag{8}
\]

Thus all four used Quit actions are exactly indifferent by (3).

## Complete inactive-gap table

Substitution of (1) into all endpoint differences gives

\[
\begin{array}{c|rrrr}
 &i=0&i=1&i=2&i=3\\ \hline
k=0&
0&
-\frac{103}{48}+\frac{31s}{528}&
\frac{85}{48}-\frac{15s}{176}&
0\\[1mm]
k=1&
0&
-\frac{2347}{972}+\frac{79s}{972}&
0&
\frac{865}{1944}-\frac{55s}{1944}\\[1mm]
k=2&
\frac{151}{42}-\frac{s}{6}&
0&0&0\\[1mm]
k=3&
-\frac{2237}{1464}+\frac{59s}{1464}&
-\frac{2237}{1464}+\frac{59s}{1464}&
\frac{106}{61}-\frac{9s}{122}&
0.
\end{array}
\tag{9}
\]

This table lists \(H\Delta_{k,i}\).  Its additional zeros are structural
inactive ties.  Every nonzero entry is strictly negative.  Indeed, using only
\(25<s<26\), the seven distinct entries are bounded above by

\[
 -\frac{327}{528},\quad
 -\frac{190}{528},\quad
 -\frac{293}{972},\quad
 -\frac{510}{1944},\quad
 -\frac{24}{42},\quad
 -\frac{703}{1464},\quad
 -\frac{13}{122},
\tag{10}
\]

in their order of first appearance in (9).  Since \(H>0\), every unused Quit
action is weakly worse than Continue.

## Unrestricted consumer proof

Equations (2), (6), (8), and (9) give the probability, recursion, and exact
root-Nash fields of the checked structure
IsQuittingBlockCertificate in
UniformEquilibrium/Quitting/Cycles/BlockPeriodicProfile.lean.

The value-box field follows without restricting the free coordinates:
(5) is a convex combination of the four singleton reward rows, because its
nonnegative absorption weights sum to \(H\).  Those singleton coordinates are
bounded by quittingRewardBound; arbitrary triple or grand rewards can only
enlarge that bound.  The block absorbs because every hazard is positive.
The admissibility disjunction holds through its nonnegative-solo branch,
because every own singleton reward equals one.

Therefore the checked theorem
isUniformEquilibriumPayoff_of_isQuittingBlockCertificate yields

\[
 (\operatorname{quittingGame}r)
   \text{.IsUniformEquilibriumPayoff none }U^0.
\]

That theorem quantifies over all unilateral behavioral replacements.  No
stationary-deviation, finite-clock, bounded-controller, or attainment
restriction is introduced.

## Exact status of the literal seed

For the intended literal seed, retain the triple/grand rows

    {0,1,2}: (1,1,1,-1)     {0,1,3}: (1,1,0,1)
    {0,2,3}: (1,1,1, 1)     {1,2,3}: (6,1,1,1)
    {0,1,2,3}: (11,-1,1,0).

Every one of its 15 pure quitting coalitions has an exact strict join-or-leave
escape.  In bit-mask order \(1,\ldots,15\), one may take toggling players

\[
 (3,2,0,0,2,1,0,2,0,0,2,1,0,0,1)
\]

with respective payoff gains

\[
 (1,2,3,1,2,1,2,1,3,1,1,2,2,5,2).
\]

A broad numerical stationary-face audit found no candidate.  That is only a
screen.  The exact period-four certificate already proves that the literal
seed is not a counterexample.

The larger quadratic root \(d=(193+\sqrt{649})/732\) gives
\(a=-5(366d-91)/132<0\), so it is not a probability solution.

Triple and grand rows do not occur in (5), (7), or (9): a prescribed phase has
only one possible quitter, and one unilateral Quit deviation creates at most
a pair.  This proves the full 20-coordinate freedom rather than only the
literal completion.

## Relation to the killed period-three support

The continuation-matched row satisfies

\[
 r_1(\{1,3\})=r_1(\{3\})=-2,\qquad
 r_3(\{1,3\})=r_3(\{1\})=-1.
\]

For the old support word
\(\{0\}\to\{2\}\to\{1,3\}\), the four active polynomials admit an exact ideal
combination equal to

\[
 \frac{d(d-2)(48d^2-21d+25)}{48}.
\]

This is nonzero on \(0<d<1\), since

\[
 48d^2-21d+25
 =48\left(d-\frac7{32}\right)^2+\frac{1453}{64}>0.
\]

Thus that three-phase active system has no interior root.  The positive
closure above is genuinely a different support pattern.

## Sources and reproducibility

Named declarations inspected:

- deadlockMatrix and IsFullCoreDeadlockCompletion in
  UniformEquilibrium/Quitting/Classification/LCP/FullCore/DeadlockChargedReturn.lean;
- ReducedIdealSingletonLasso.debt_pos in
  DeadlockReducedSingletonLassoBarrier.lean;
- IsQuittingBlockCertificate,
  isQuittingBlockCertificate_of_root, and
  isUniformEquilibriumPayoff_of_isQuittingBlockCertificate in
  UniformEquilibrium/Quitting/Cycles/BlockPeriodicProfile.lean; and
- quittingRewardBound and abs_reward_le_quittingRewardBound in
  UniformEquilibrium/Quitting/RewardBound.lean.

The exact polynomial calculation is reproducible from
/tmp/deadlock_continuation_pair_period4_exact.py.  This note is ordinary
mathematics and claims no Lean seal.

## Nonclaims

- This excludes one exact 20-dimensional fibre, not every full-core deadlock
  completion.
- It fixes all singleton and pair coordinates; only triple and grand rows are
  arbitrary.
- It does not promote the numerical stationary screen to a theorem.
- It does not contradict the balanced-singleton-cycle exclusion: the present
  inactive endpoints depend on pair rewards.
- It proves no open neighborhood in pair-row space; five inactive gaps are
  exact ties.
- It supplies no positive all-behavior exploitability gap and does not solve
  the finite-quitting conjecture.

## Next exact test after the maintenance pause

A new deadlock-fibre seed must escape both exact support patterns:

1. the reviewed three-phase joint block
   \(\{0\}\to\{2\}\to\{1,3\}\); and
2. the four-singleton block
   \(\{0\}\to\{2\}\to\{1\}\to\{3\}\).

The latter's active hazards depend only on singleton rows.  Therefore the next
principled search should impose a pair-row inequality that makes at least one
entry of (9) positive, while retaining the pure-coalition and stationary
screens.  Triple or grand perturbations cannot escape this fibre theorem.
No such new region is started here.
