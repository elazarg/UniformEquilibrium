# Three matching failure and the remaining unequal-high cycle system

Author: CODEX_NOETHER_SUPPORT.

Status: bounded ordinary-mathematical test, not independently reviewed or
Lean-checked. The exact result excludes the three specified two-phase
matching grammars on one supplied table, including boundary hazards.
The four-phase calculation below is an exact system with a failed numerical
candidate, NOT a nonexistence theorem. No no-UE claim or export is proposed.

## 1. Literal game and question

Players are 0,1,2,3. Live and Never rewards are zero. The private stopping
laws are independent; a unilateral deviation may replace the entire
behavioral strategy, including any finite stopping date or Never.

| Coalition | Reward vector |
| --- | --- |
| 0 | (1,4,0,0) |
| 1 | (4,1,0,0) |
| 2 | (0,0,1,4) |
| 3 | (0,0,4,1) |
| 01 | (2,2,1,1) |
| 02 | (8/5,1,1,0) |
| 03 | (1,0,1,2) |
| 12 | (0,1,8/5,1) |
| 13 | (1,2,0,1) |
| 23 | (1,1,2,2) |
| 012 | (1,0,0,0) |
| 013 | (0,1,0,0) |
| 023 | (0,0,0,1) |
| 123 | (0,0,1,0) |
| 0123 | (−1,−1,−1,−1) |

This is in the original twelve-member box [1,2]^12. Its high directed
cross entries, in the cyclic owner order (0,2,1,3), are (8/5,8/5,2,2);
the opposite cross-member entries are all 1. It has row sums
(23/5,5,23/5,5), so the known equal-row-sum stationary producer does not
apply, nor does the all-row-sums-at-least-29/5 producer.

A two-phase matching grammar partitions the players into two pairs.
At its assigned phase player i quits with a fixed probability q_i∈[0,1]
and at the other phase always continues. Repeat independently forever.
The claim below excludes exact terminal Nash for each of the three
partitions, from either starting phase. It does not exclude general
period-two profiles, stationary profiles, or larger calendars.

## 2. The within-partner matching 01/23 is impossible

This argument holds throughout the full twelve-member box.
First no assigned q_i can equal 1 in an equilibrium. At a reached
within-partner phase a sure quitter gives its partner Continue payoff 4
and Quit payoff at most 2. The partner must therefore continue surely.
The resulting singleton gives either cross outsider payoff 0, whereas
joining it pays at least 1. This is profitable. Apply the argument first
to phase zero, then to phase one, which has positive reach if phase zero
has no sure quitter. Consequently every finite phase has positive reach.

Suppose q_i>0 and let k be i's within partner. Since q_i<1, both of i's
current actions must be optimal at its active phase. If its pair-member
reward is c_i≤2 and W_i is its value at the quiet phase, exact equality is

    1+(c_i−1)q_k = 4q_k+(1−q_k)W_i,
    W_i = 1−(4−c_i)q_k/(1−q_k).

At the quiet phase, quitting pays at least 1 except when both opponents
quit; in that case its triple-member reward is nonnegative. Thus, writing
j,l for the other pair,

    2q_k/(1−q_k) ≤ q_j q_l.                         (1)

If X=q_0q_1>0, (1) forces Y=q_2q_3>0, and conversely. Applying (1)
to all four owners gives X≤Y²/4 and Y≤X²/4. Hence
X≤X⁴/64, impossible for 0<X≤1.

It remains that X=Y=0. There is at most one positive quitter in each
pair. If there are two, they are cross players and quit on different
dates, so only their two singleton coalitions occur. Their prescribed
payoffs add to 1. Either player's date-zero Quit gives at least 1,
including possible joining of the other player's singleton, so both
cannot be best replying. If there is only one positive quitter, a cross
outsider gains by date-zero Quit instead of receiving 0; with no positive
quitter the all-Never profile is not Nash. This completes all boundaries.

## 3. Every cross-matching equilibrium would have interior rates

Use matching 02/13 first. Let A,B be the Continue probabilities of
players 0,1, and y,z those of players 2,3. The active own pair rewards of
2 and 3 are both 1. This feature also holds in the other cross matching
after the label permutation used below.

A sure quitter at a reached cross-pair phase gives its co-owner Continue
payoff 0 and Quit payoff at least 1. The co-owner must also quit surely.
Every pure cross pair has a quiet outsider whose passive pair reward is
0 and whose joining triple reward is 1. This is profitable. The same
first-phase/positive-second-phase argument as above therefore excludes
all assigned sure-Quit hazards. Thus A,B,y,z>0 and all phases are reached.

Suppose y=1. If player 3 has positive Quit hazard, its active value is 1.
Its quiet-phase value is A, and its active Continue endpoint is AB.
Indifference forces A=B=1. This leaves only player 3 active and has a
profitable cross outsider. If z=1 also, only the within partners 0 and 1
can quit, on different dates. If both quit positively, either can obtain
4 by Never, but has prescribed payoff strictly below 4 because its own
singleton occurs with positive probability. At most one active player,
or all Never, was already excluded. Therefore y<1, and symmetrically z<1.

Now suppose A=1. If B=1, the preceding within-partner Never argument
applies to players 2,3. Otherwise player 1 mixes at its active phase and
has positive active value P. At its quiet phase only player 2 can quit,
giving it reward 0, so its quiet value is yP. At its active phase its
Continue endpoint is zyP<P, contradicting mixing. Hence A<1, and
symmetrically B<1. All four rates must be interior.

These arguments use deviations at positively reached live histories.
Such deviations are literal complete-strategy replacements, so the
necessary conditional equalities follow from initial terminal Nash.

## 4. Exact active equations and a forced quiet loss

The secondary active equalities force

    y=z=b,        AB(4−3b)=1.

The primary equalities, with their actual distinct pair rewards, then give

    A(b)=(3b²+2b−2)/(b(b²+b+1)),
    B(b)=(15b²+8b−8)/(b(3b²+7b+5)).                   (2)

For example, the primary active values are P_0=8/5−3b/5 and P_1=2−b;
their quiet Continue recursions are

    P_0/b=(1−B)(1+3b)+BbP_0,
    P_1/b=(1−A)(1+3b)+AbP_1.

Eliminating A,B gives the exact identity

    AB(4−3b)−1
      =−(b−1)K(b)/[b²(b²+b+1)(3b²+7b+5)],
    K(b)=3b⁵+148b⁴+145b³−173b²−112b+64.              (3)

Admissibility A>0 forces b>1/2. On [1/2,1], K''>0 because
K''(1/2)=1081/2 and K'''=180b²+3552b+870>0. Moreover,

    K(1/2)=−249/32,       K(4/5)=−1488/3125,
    K(81/100)=15888274003/10¹⁰>0,
    K'(4/5)=24856/125>0.

Convexity makes K negative between 1/2 and 4/5; strict increase after
4/5 gives exactly one admissible root, in (4/5,81/100). Both rates (2)
lie in (0,1) there: their numerators are positive, and

    1−A=(b−2)(b−1)(b+1)/(b(b²+b+1)),
    1−B=(b−1)(b+1)(3b−8)/(b(3b²+7b+5))

are positive. Thus the following obstruction concerns the actual unique
interior active-tie point, not a system with no admissible solution.

In matching 02/13, player 3's quiet value is 1/B and its Quit endpoint is
1+(1−A)b+A(1−b). Their difference is

    G_1=−(b−1)N_1(b)/[b(b²+b+1)(15b²+8b−8)],
    N_1=12b⁵−50b⁴−90b³+43b²+56b−16.                 (4)

On [4/5,81/100], N_1(4/5)=−19712/3125 and
N_1'≤−618559837/5000000<0. For this derivative bound evaluate positive
monomials at 81/100 and negative monomials at 4/5. Hence G_1<0.

The permutation π=(0↦3,1↦2,2↦0,3↦1) preserves the fixed singleton,
passive, triple, and grand rows. In the other matching 03/12 it exchanges
the two primary active inputs, so A'=B, B'=A, with the SAME b. The
secondary labeled 2 in that chart is original player 0; its quiet
cross-member input is 8/5. Its quiet slack is

    G_2=1/B−1−(3/5)(1−A)b−A(1−b)
       =−(b−1)N_2(b)/[5b(b²+b+1)(15b²+8b−8)],
    N_2=30b⁵−236b⁴−358b³+231b²+248b−80.              (5)

Here N_2(4/5)=−2432/625 and, by the same endpoint bound,
N_2'≤−967795837/2000000<0. Thus G_2<0. All denominators in (4),(5)
are positive. Sections 2–4 exclude every profile in all three grammars.

## 5. The unequal-high four-phase system, not its existence

Retain the SAME table. Let P=(0,2,1,3), with indices modulo 4, and set
d=(3/5,3/5,1,1). At phase j activate the ordered pair (P_j,P_(j+1)).
Owner P_j has Continue probability a_j at its high phase j and b_j at
its low phase j−1; it continues at its two other phases.

For an interior solution define

    X_j=1+d_j(1−b_(j+1)),       a_j=1/X_(j+1),
    Z2_j=(1−a_(j+2))(1+3b_(j+3))+a_(j+2)b_(j+3),
    Z1_j=4a_(j+1)(1−b_(j+2))+a_(j+1)b_(j+2)Z2_j.

Starting at its high phase, owner P_j's values would be (X_j,Z1_j,Z2_j,1).
All low active ties are identities. The four high ties are exactly

    X_j−b_(j+1)Z1_j=0,               j=0,1,2,3.       (6)

Both complete quiet tests remain indispensable:

    T1_j=a_(j+1)b_(j+2)+2a_(j+1)(1−b_(j+2))
          +(1+d_j)(1−a_(j+1))b_(j+2)
          +(1−a_(j+1))(1−b_(j+2)),
    T2_j=a_(j+2)+2b_(j+3)−2a_(j+2)b_(j+3),
    Z1_j≥T1_j,       Z2_j≥T2_j.                        (7)

In particular the second quiet inequality simplifies exactly to

    1+b_(j+3)−2a_(j+2)≥0.                             (8)

Direct enumeration of all 32 player/phase Quit and Continue endpoints
from the full table verifies these formulas. The high Continue endpoint
is b_(j+1)Z1_j; the low Continue endpoint is a_(j−1)X_j=1.
The quiet Continue endpoints are the displayed Z1_j,Z2_j recursions.
There is no missing counterfactual triple: both terms in T1 and T2 were
computed with the deviator inserted into the current actual pair.

If (6),(7) have an interior solution, joint cycle survival is
C=∏_j a_jb_j<1, and deleted survival for P_j is C/(a_jb_j)<1.
Bounded Bellman iteration would then identify the prescribed payoffs and
bound EVERY complete behavioral deviation, including Never, by the same
values. This is only the exact remaining system, not a producer theorem.
It does not describe all boundary supports of the four-phase grammar.

A numerical interior candidate for (6) is

    b≈(.7354818044,.7793032825,.8179944985,.7680216794),
    a≈(.9015479842,.8117025951,.7908150341,.8830661231).

Its first quiet slacks are approximately (.212966,.076156,.284503,.443613),
but its second slacks are (.186392,−.030650,−.023793,.194589).
Thus this candidate does not satisfy the full-cap test. The other formal
root b=(1,1,1,1) has a=(1,1,1,1), no absorption, and is actual all Never;
the displayed nonzero value annotations are not its payoff.
Neither numerical existence/uniqueness nor exclusion of other roots is
claimed. No exact four-phase or stationary equilibrium has been produced
for this table in this test.

## 6. Narrow existing-exit check

Every pure nonempty coalition has a profitable membership toggle. One
choice of deviator for coalitions in table order is

    (2,2,0,0,0,3,1,0,2,2,1,0,0,1,0).

The gain is at least 1 in each case. The all-Never profile has gain 1.
These are original date-zero deviations, not merely matrix conditions.

The normalized singleton matrix is exactly

    Γ=((0,3,−1,−1),(3,0,−1,−1),
       (−1,−1,0,3),(−1,−1,3,0)).

`normalizedSoloMatrix` (`Quitting/Classification/LCP/Normalization.lean`)
subtracts the owner's own-singleton baseline in each payoff row; no change
to this game's Never reward is being made. The current theorem
`pairedSingletonMatrix_not_projectiveQBar`
(`Quitting/Examples/BlockPair/FourPlayerPairedSingletonResidualHard.lean`)
applies to this exact matrix. Its cross principal {0,2} has off-diagonals
−1: a projective LCP at right-hand side (−1,−1) would require simultaneously
−z_c−z_2≥0 and −z_c−z_0≥0, contradicting total mass 1.
Every player is punishment-normal here: make its other three players quit
surely at date zero; its best response then pays 0 rather than grand reward
−1. Its own Never guarantees nonnegative payoff against arbitrary opponents,
so its punishment value is exactly 0. Therefore restricting to
`punishmentNormalPlayers` does not rescue Q-bar. The exact ambient and
normal-principal consumers inspected were
`exists_uniformEquilibriumPayoff_of_projectiveQBar_snell` and
`exists_uniformEquilibriumPayoff_of_punishmentNormal_projectiveQBar_snell`
(`Quitting/AbsorptionPath/PunishmentNormalPathStrategicSnell.lean`).

`QuittingCappedJointExit` (`Quitting/Classification/SoloExitPreference.lean`)
fails at pair 01, where both members get 2>1. Thus
`exists_uniformEquilibriumPayoff_of_unitSoloExit_and_cappedJointExit`
(`Quitting/Classification/TerminalExploitabilitySoloExitPreference.lean`)
does not enter. The stronger low-active-Quit screen also fails at the sure
01 root: both active Quit endpoints are 2.

For every anchor, its reward when it belongs to the coalition is at most 2,
whereas its excluding partner singleton pays 4. Consequently NO induced
point can satisfy `QuittingSingleAnchorInducedDominance`. This checks the
actual screen, not only the special membership-reward subclass, in
`Diagnostics/Quitting/Collision/Toggles/SingleAnchorArbitraryCompletionEscape.lean`.

Finally, independent stationary Quit hazards 1/10 give actual payoff

    (1102/905,4220/3439,1102/905,4220/3439) > (1,1,1,1).

This follows by summing q^|S|(1−q)^(4−|S|)r(S) and dividing by
1−(1−q)^4. Hence no designated nonempty owner set satisfies
`HasQuittingActualWeakSubsetExclusion`
(`Quitting/Paths/FiniteCalendarRawPredicates.lean`). The same actual profile
defeats strict and nonconcentrated-group singleton-payoff exclusion.
This is a bounded failure of named entrances, not an exhaustive assertion
about all current existence theorems.

## 7. Dependency and stopping boundary

All abbreviated production paths above are below `UniformEquilibrium/`.
The nearby period-two source inspected was `periodTwo_active_identity_first`
and `periodTwo_active_identity_second`
(`Quitting/Examples/BlockPair/FourPlayerPairedSingletonPeriodTwo.lean`);
it does not produce the unequal active rates required here.
The four-phase formula extends the literal endpoint enumeration of the
[common-high cycle note](../notes/CODEX_NOETHER_SUPPORT__ORIENTED_PAIR_REWARDS_TWO_TO_FOUR_PHASE_HANDOFF.md),
whose common-high hypothesis this table does not satisfy.
The general four-rate equations come from the
[independent rectangle note](../notes/CODEX_NOETHER_SUPPORT__INDEPENDENT_CROSS_REWARD_BOX_PERIOD_TWO_SOURCE.md).
No earlier note or export was edited. All symbolic identities and rational
interval signs displayed here were rechecked exactly; no Lean build ran.

The minimal obstruction is not failure to solve active equations: both
cross matchings have a unique admissible active-tie point. It is the forced
profitable quiet insertion there. The unequal-high cycle gives the concrete
next simultaneous constraints (6)–(8), but its tested root also fails quiet
insertion. A future actual-source operation must change those quiet response
opportunities or reselect a genuinely different equilibrium; merely adding
values to the same active-tie point cannot do so. This bounded pass stops
without claiming that the displayed grammars are exhaustive.
