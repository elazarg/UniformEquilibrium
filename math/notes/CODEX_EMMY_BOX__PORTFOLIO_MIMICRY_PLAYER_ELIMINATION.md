# Portfolio mimicry eliminates a strategic quitting player

Author: CODEX_EMMY_BOX.

Status: CLOSED AS A NEW-COVERAGE ROUTE. The portfolio inequalities imply
the exact already-checked `CappedClockParentRewardCertificate`, including
its Never, future, and joining rows; Section 7 records the subtraction.
Consequently Proposition 1 gives NO NEW TABLE CLASS. Its pathwise proof and
the rational fixture are ordinary mathematical records, not independently
reviewed or Lean checked, and not export candidates. The fixture separates
several simpler classes but is explicitly consumed by the existing capped-
clock theorem. Research must change mechanism rather than enlarge this
same donor inequality cone.

## 1. Self-contained question and finite data

Let I be a finite set of players, e a distinguished player, and J=I\{e}.
At each live integer date all players independently choose Quit or Continue.
The first nonempty quitting coalition S gives bounded absorbing reward
r_i(S) to player i. Preabsorption and literal Never pay zero. There is no
public correlation device. Unilateral deviations range over every behavioral
stopping law, including every pure finite date and Never.

For a product profile p of independent stopping laws, let U_i(p) be its
terminal expected payoff, B_i(p) its supremum payoff over ALL unilateral
behavioral deviations, and D_i(p)=B_i(p)-U_i(p). Set E(p)=max_i D_i(p).
An ordinary uniform-equilibrium payoff is the project's fixed-payoff,
uniform finite-horizon notion, not merely a terminal equilibrium.

Choose fixed nonnegative real coefficients a_d for d in J. The following
finite table conditions concern an original four-player table, not a supplied
equilibrium or a state-dependent selector:

    (P)  r_e(S) >= sum_d a_d r_d(S)
         for every nonempty S subset J;

    (Q)  r_e(A union {e}) <= sum_d a_d r_d(A union {d})
         for every A subset J, INCLUDING A=empty.

Every coalition on the right of (Q) is nonempty. Coefficients need not sum
to one. Never has reward zero on both sides. Thus (P) holds automatically
on the added Never outcome as well, without a terminal-payoff shift.

Question: does every uniform-equilibrium payoff of the deleted game on J
lift to some uniform-equilibrium payoff of the original game by prescribing
literal Never for e, even though e's reward row need not equal any other row
and e can sometimes profit by joining?

## 2. Proposition 1: exact full-deviation gain domination

Under (P) and (Q), every product profile p on J, lifted by e=Never, satisfies

    D_e(p,Never) <= sum_d a_d D_d(p),                 (1)

where the right-hand debts are in the deleted game. Every survivor's
terminal payoff and complete deviation cap are unchanged by the lift.
Consequently

    E(p,Never) <= max(1, sum_d a_d) E(p).             (2)

In particular, if |I|<=4, the original game has a uniform-equilibrium payoff.
More generally, deletion preserves existence whenever the smaller game has
a uniform-equilibrium payoff. No attainable-profile convexity is assumed.

### Pathwise proof of the novel inequality

Fix a finite test date t and independently sample all original survivor
clocks T_d. Compare e's deviation Quit at t with, separately for each donor
d, the legal unilateral deviation

    T_d' = min(T_d,t),

leaving all other survivor laws unchanged. This is implementable by keeping
d's original hazards before t and quitting surely at t. It uses neither
another player's clock nor public information. Let tau=min_d T_d, with
tau=infinity if every survivor chooses Never.

If tau<t, all the original and modified profiles already absorb at the
same coalition before t. Every gain being compared is exactly zero.

If tau>=t, let A={d:T_d=t}, possibly empty. The e deviation absorbs at
A union {e}. Donor d's separate deviation absorbs at A union {d}.
If the original survivor profile eventually absorbs, write its original
coalition as S. Then (Q) and (P) give, on this clock sample,

    r_e(A+e)-r_e(S)
       <= sum_d a_d [r_d(A+d)-r_d(S)].               (3)

If the original outcome is Never, all baseline rewards in (3) are zero,
and (Q) gives the same inequality. This includes a positive probability of
joint Never. Equality tau=t causes no difficulty: donors already in A do
not change their clock, and A+d is still the correct coalition.

Take expectations. Although the donor comparisons share a clock sample
for the proof, each expected term is the payoff of one legal unilateral
deviation against the ORIGINAL opponents. It is not the payoff of a joint
change or a correlated candidate profile. Each term is at most D_d(p).
The gain of e's pure date t is therefore at most sum_d a_d D_d(p).
The pure Never test has gain zero and satisfies the same bound.

Finally, along the unique all-Continue live history, any unilateral
behavioral deviation has the same payoff as a probability mixture of pure
date/Never stopping tests. Thus the bound covers ALL behavioral deviations.
Taking the supremum proves (1). Survivor transport gives (2).

### Uniform-payoff conclusion, not only terminal approximate Nash

Let epsilon_k tend to zero. From a uniform-equilibrium payoff of the
deleted game choose actual terminal epsilon_k-Nash profiles with terminal
payoffs tending to that fixed smaller-game target. Lift them with e=Never.
Equation (2) makes their full terminal errors tend to zero. The enlarged
payoff vectors lie in a fixed finite-dimensional reward cube, so a
subsequence converges. The checked terminal-Nash-to-uniform-payoff theorem
then gives ONE fixed uniform-equilibrium payoff of the original game.
Survivor coordinates retain the deleted-game target. No exact formula for
the additional coordinate is claimed unless (P) is equality.

The smaller-game existence input is unconditional when |J|<=3. This is an
actual class producer from finite reward data and finite inequalities.

## 3. A strict rational four-player fixture

Take J={0,1,2}, e=3. Define the core reward R on J by the seven rows below.
This is a Solan-shaped rational table; no sufficiently-small-perturbation
literature theorem is invoked for the particular parameter 1/10.

| S | R_0(S) | R_1(S) | R_2(S) |
| --- | ---: | ---: | ---: |
| 0 | 1 | 3 | 0 |
| 1 | 0 | 1 | 3 |
| 2 | 3 | 0 | 1 |
| 01 | 11/10 | 0 | 1 |
| 02 | 0 | 1 | 11/10 |
| 12 | 1 | 11/10 | 0 |
| 012 | 0 | 0 | 0 |

Set a=(1/10,1/10,4/5), so sum a=1. On every nonempty S subset J put

    r_i(S)=R_i(S)             for i in J,
    r_e(S)=a dot R(S)+1/10.

Thus e's seven passive rewards, in the row order above, are

    1/2, 13/5, 6/5, 101/100, 27/25, 31/100, 1/10.    (4)

For coalitions containing e write S=A union {e}. For core players set

    r_i({e})=0;
    r_i(A+e)=2 if i in A, and 3 if i not in A,
                  whenever A is nonempty.

Prescribe e's own exit rewards by

    r_e(e)=4/5;
    r_e(e0)=r_e(e1)=r_e(e2)=0;
    r_e(e01)=r_e(e12)=0;
    r_e(e02)=21/25;
    r_e(e012)=-1/10.                                (5)

This specifies all 15 nonempty coalitions and all four reward coordinates.
Never remains zero.

The upper bounds sum_d a_d R_d(A+d) in (Q), for
A=empty,0,1,2,01,02,12,012, respectively, are exactly

    1, 49/50, 21/100, 91/100, 11/100, 22/25,
    11/100, 0.                                     (6)

All inequalities (Q) are strict; the least slack is 1/25 at A=02.
All (P) inequalities have slack 1/10. Therefore the same fixed a works
throughout the open sup-norm reward ball of radius 1/100 about this table:
each difference of the two sides changes by at most 2/100, because sum a=1.
Every table in that ball has a uniform-equilibrium payoff by Proposition 1.
This openness concerns the terminal table; the canonical Never reward is
still exactly zero.

### Exact separation from pure-coalition equilibria

No pure date-zero coalition is a terminal equilibrium:

- Empty coalition: a core player can Quit alone for 1>0.
- Singleton core i: the zero-payoff outsider joins and receives 11/10.
- Core pair: its zero-payoff participant leaves and receives 3.
- Core triple: any participant leaves and receives 1.
- Singleton e: any core player joins and improves from 0 to 2.
- e plus one core player: e leaves and receives its positive passive
  singleton payoff from (4), instead of zero.
- e plus at least two core players: a core participant leaves and improves
  from 2 to 3.

For a pure timing profile the earliest finite coalition is deterministic;
the listed deviation at that date or to Never has the same strict gain.
All-Never also fails. Thus this fixture has no PURE timing equilibrium of
any chronology, not just no pure one-shot equilibrium. This is not a
positive exploitability gap over mixed private clocks.

### Exact separation from low-active-Quit participant conditions

All singleton rewards are (1,1,1,4/5). At the independent sure-Quit root
with active support {0,2,e}, the participants' pure-Quit rewards are
(2,2,21/25), strictly above their own singleton rewards. Thus the direct
product-low condition fails. In particular the supportwise participant LP,
its fixed-positive-weight special case, and weak solo-exit preference do
not supply this fixture. This test uses an actual product root including
its sure-Quit boundary, not a correlated coalition lottery.

## 4. Singleton-matrix overlap tests

The actual singleton comparison matrix M_ij=r_i({j})-r_i({i}) is

    M = [  0   -1    2   -1 ]
        [  2    0   -1   -1 ]
        [ -1    2    0   -1 ]
        [ -3/10 9/5  2/5  0 ].                     (7)

### Full recursive normal core

Each core row has a negative entry at another core player; e has the
negative entry M_e0=-3/10. These witnesses remain in the full set at every
normality layer, so the distinct-witness recursive core is all four players.
This is the algebraic alpha-player core, not a computation of minmax values.

### R0 and no homogeneous simplex solution

Let x>=0 and Mx>=0, with x_i(Mx)_i=0. Write t=x_e and z=(x_0,x_1,x_2), and
let C be the upper-left 3x3 block of (7). It has determinant 7 and C*1=1.

If t>0, the top inequalities give Cz>=t*1. Any zero coordinate of z makes
another coordinate of Cz nonpositive, so all three z_i are positive.
Complementarity gives Cz=t*1 and hence z=t*1. The last residual is then
(19/10)t>0, contrary to e's complementarity.

If t=0 and some z_i=0, the cyclic top inequalities force all z_i=0. If
all z_i>0, complementarity gives Cz=0, and invertibility gives z=0 again.
Thus the only homogeneous nonnegative complementary vector is zero: M is
R0 and has no homogeneous simplex solution. The fixture therefore does not
fall in the nonvertex homogeneous-source branch.

### Degree one and standard Q: finite exact inventory

At LCP offset -1, for every support A of size at least two the unique
active-equation solution is x_A=M_AA^-1*1. The table lists its active
coordinates and the off-support residual -1+M_BA*x_A.

| A | det M_AA | x_A | off-support residual |
| --- | ---: | --- | --- |
| 01 | 2 | (1/2,-1) | (-7/2,-59/20) |
| 02 | 2 | (-1,1/2) | (-7/2,-1/2) |
| 0e | -3/10 | (-10/3,-1) | (-20/3,10/3) |
| 12 | 2 | (1/2,-1) | (-7/2,-1/2) |
| 1e | 9/5 | (5/9,-1) | (-5/9,10/9) |
| 2e | 2/5 | (5/2,-1) | (5,-5/2) |
| 012 | 7 | (1,1,1) | (9/10) |
| 01e | -39/10 | (-10/39,20/39,-59/39) | (70/39) |
| 02e | 1 | (-2,1,1) | (-7) |
| 12e | 1 | (1,-2,1) | (-7) |
| 012e | 133/10 | (10/19,10/19,10/19,-9/19) | empty |

Empty/singleton supports cannot solve offset -1 because M has zero
diagonal. Every rejected row has a negative active coordinate. The only
solution has support 012, strictly positive off-support residual 9/10,
and active determinant 7>0. The canonical R0 degree is therefore one by
the finite support degree formula. Nonzero R0 degree gives standard Q.
These uses match actual checked declarations listed below; the arithmetic
inventory is ordinary exact rational mathematics, not a new Lean theorem.

Consequently this fixture is not handled just by non-Q or degree-not-one
singleton criteria. It has a mutually harmful pair {0,e}, so it does not
have completely projective-Q principal structure merely because its full
matrix is Q. No claim is yet made about every other existing proper-face
or quiet-extension consumer.

## 5. Source declarations inspected and exact overlap boundary

Actual files/declarations inspected for this branch:

- `UniformEquilibrium/Quitting/Classification/TwinMerging.lean`:
  `QuittingTwinMergeable`, `QuittingIndistinguishableTwins`,
  `quittingBestReplyValue_le_twin`,
  `isεAsymptoticNash_liftDeletedProfile_of_twinMergeable`, and
  `exists_uniformEquilibriumPayoff_of_twinMergeable`. The existing lift uses
  exactly equal reward rows and token invisibility equalities. Proposition 1
  uses instead two inequalities and a possibly multi-donor comparison; it
  does not assume or conclude twin mergeability.
- `UniformEquilibrium/Quitting/Classification/PlayerDeletionLift.lean`:
  `quittingTerminalPayoff_liftDeletedProfile`,
  `quittingBestReplyValue_liftDeletedProfile`, and
  `hasTerminalExploitabilityGap_deletePlayer_of_ownerJoinAntitone`.
  Survivor payoff/cap transport is already checked. The antitone branch has
  a negative singleton/punishment gate; all four fixture singletons are
  positive, and e has a strictly positive join increment on coalition 02.
- `UniformEquilibrium/Quitting/Cycles/BehaviorPureTimeExtremality.lean`:
  the unique-live-history reduction and pure-time extremality mechanism.
  This is why the proof's pure finite-date/Never tests cover unrestricted
  behavioral deviations, not just a bounded menu.
- `UniformEquilibrium/Quitting/Classification/ThreePlayer/Existence.lean`:
  `quittingGame_exists_uniformEquilibriumPayoff_threePlayer`.
- `UniformEquilibrium/Quitting/Classification/SmallPlayerExistence.lean`:
  `quittingGame_exists_uniformEquilibriumPayoff_of_card_le_three`.
- `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`:
  `exists_terminalNash_terminalPayoff_close_of_isUniformEquilibriumPayoff`
  and `quittingGame_isUniformEquilibriumPayoff_of_terminalNash_tendsto`.
- `UniformEquilibrium/Quitting/Classification/LCP/NormalCore.lean`:
  `normalLayer`, `normalCore`, `normalizedNormalPlayerMatrix`, and the
  distinction between alpha-player recursion and strategic normality.
- `UniformEquilibrium/Quitting/Classification/LCP/MatrixClasses.lean`:
  `StandardLCPSolution`, `IsStandardQMatrix`, and the standard/projective
  convention distinction. No strategic conclusion is imported from a
  matrix definition alone.
- `MathUE/LinearProgramming/FiniteSupportDegree.lean`:
  `r0Degree_eq_sum_admissible_supports`, whose zero diagonal, positive
  anchor, negative column witnesses, nonsingular proper principal tests,
  and strict off-support residual hypotheses are all explicit here.
- `MathUE/LinearProgramming/R0Degree.lean`:
  `isStandardQ_of_r0Degree_ne_zero`.

No literature-derived claim beyond these inspected project declarations is
needed for Proposition 1. The earlier notebook
`CODEX_EMMY_BOX__OBJECTIVES_AND_GLOBAL_SELECTION.md` concerns different
objective/public-root restrictions; none of its no-gos limits this donor
clock operation.

## 6. Current unresolved work

No independent export review is requested: the bounded overlap test in
Section 7 already shows the mechanism is integrated. Further strengthening
would have to change the legal clock operation or exploit a genuinely
selected reduced equilibrium, not just rename these pointwise inequalities.
No universal donor producer is claimed.

The suspected artificial restriction is that eliminating a player must
either make that player's own joining pointwise unprofitable or identify it
with one exact twin. The concrete replacement is cross-player domination of
COMPLETE deviation gains by legal individually sped-up donor clocks.

## 7. Exact overlap: all three capped-clock rows follow

This comparison was suggested independently by CODEX_NASH_BOX through the
coordinator, then checked directly against the actual source declaration
`CappedClockParentRewardCertificate` in
`UniformEquilibrium/Quitting/Classification/QuietExtension/CappedClockPointwiseDomination.lean`.
Reindex e as `none` and every donor d as `some d`, and choose certificate
weights a_d. Write s_i=r_i({i}). The declaration requires precisely:

    N: s_e <= sum_d a_d s_d;
    F: s_e-r_e(A) <= sum_d a_d [s_d-r_d(A)];
    J: r_e(A+e)-r_e(A)
          <= sum_d a_d [r_d(A+d)-r_d(A)]

for nonempty child coalitions A in F and J. Condition (Q) at A=empty is
exactly N. Subtract (P) at A from N to obtain F. Subtract (P) at A from
(Q) at A to obtain J. All signs and coalition indices match literally.
There is no residual Never, normalization, or probability-mode issue.

The checked declaration
`quittingGame_exists_uniformEquilibriumPayoff_of_finFour_cappedClockCertificate`
in `UniformEquilibrium/Quitting/Classification/QuietExtension/CappedClockFinFourExistence.lean`
already composes these raw finite inequalities with the unconditional
three-player theorem and supplies a fixed uniform-equilibrium payoff.
Therefore the strict rational neighborhood in Section 3 is an example of
THAT EXISTING CLASS, not a new coverage result.

The useful lesson is narrow: allowing several donor debts does repair the
exact-twin restriction, but that repair has already been made in the live
source. This failed novelty test does not obstruct different clock
transformations, equilibrium-dependent domination, or other mechanisms.
