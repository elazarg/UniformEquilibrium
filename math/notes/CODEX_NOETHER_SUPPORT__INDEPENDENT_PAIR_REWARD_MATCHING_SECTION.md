# A common periodic selector on an independent pair-reward section

Author: CODEX_NOETHER_SUPPORT.

Status: ordinary mathematical research, not Lean-checked or independently
reviewed. The complete positive result below covers a nine-dimensional
section of the twelve independently variable pair-member rewards. One
choice of rates works for an entire eight-coordinate box at each fixed c.
The unrestricted twelve-parameter box remains open in this investigation.
No export gate is requested for the diagnostic examples in Section 6.

## 1. Exact original-table section

There are four players, zero live and Never payoff, independent private
behavioral randomization, and unrestricted complete behavioral deviations.
For c∈[1,2], choose independently w_i∈[1,2] and u_i∈[1,c], i=0,1,2,3.
Use the following literal nonempty-coalition reward table:

| Coalition | Reward vector |
| --- | --- |
| 0 | (1,4,0,0) |
| 1 | (4,1,0,0) |
| 2 | (0,0,1,4) |
| 3 | (0,0,4,1) |
| 01 | (w_0,w_1,1,1) |
| 02 | (c,1,c,0) |
| 03 | (u_0,0,1,u_3) |
| 12 | (0,u_1,u_2,1) |
| 13 | (1,c,0,c) |
| 23 | (1,1,w_2,w_3) |
| 012 | (1,0,0,0) |
| 013 | (0,1,0,0) |
| 023 | (0,0,0,1) |
| 123 | (0,0,1,0) |
| 0123 | (−1,−1,−1,−1) |

The four active member rewards on 02 and 13 are common c. The other
cross-matching member rewards u_i may differ independently below c.
Crucially the within-partner rewards w_i may exceed c, all the way to 2.
Consequently this is not only a pointwise reward decrease from the old
common-c table. All singleton/passive/triple/grand rows remain unchanged.

Theorem. For every c∈[1,2] there are continuation probabilities
1/4<b<a<9/10 such that the SAME two-phase profile is an exact terminal
equilibrium, at every live suffix, for EVERY allowed pair (w,u). In
phase A only 0,2 quit, with Continue probabilities a,b; in phase B only
1,3 quit, with Continue probabilities a,b. Repeat independently forever.
Its phase-A payoff and full caps, independent of w,u, are

    v=(P,P/b,R,R/a),
    P=c−(c−1)b,            R=c−(c−1)a.                 (1)

This v is one fixed uniform-equilibrium payoff for every table in the
box. Keeping K≥1 complete cycles and independently censoring every later
finite clock to Never gives actual finite product laws with

    U_i^K=(1−C^K)v_i,       B_i^K=v_i,
    C=a²b²,                E^K≤8(9/10)^(4K).             (2)

B_i denotes the supremum over ALL complete behavioral replacements and
E=max_i(B_i−U_i). The rates are selected from c before w,u, K, accuracy,
or finite horizon. No favorable continuation or supplied root is assumed.

The same assertion holds for the other cross matching 03/12 by the
literal table symmetry described in Section 5. These are explicit raw
sections, not a proof that some such section contains every box input.

## 2. Rate production retained from the common-c theorem

The active-pair and prescribed passive rewards do not involve w or u.
Their original-table active ties and payoff recursions are exactly

    P/b=(1−a)(1+3b)+abP,
    R/a=4a(1−b)+abR.                                    (3)

Here is the full existence reduction, credited to the reviewed
[common-c disjunction](../exports/PAIRED_COLLISION_REWARD_EQUILIBRIUM_DISJUNCTION.md).
Set R(a)=c−(c−1)a, and let a₀∈[1/2,2/3) solve 4a₀²=R(a₀).
The function 4a²−R(a) is increasing, with the required opposite endpoint
signs. For a∈[a₀,1] put

    b(a)=(4a²−R(a))/(a²(4−R(a))).                       (4)

Its denominator is positive, b(a₀)=0, and 0<b(a)<1 for a₀<a<1.
The second equation (3) holds identically. Moreover

    b(a)−a=(1−a)g(a)/(a²(4−R(a))),
    g(a)=(c−1)a³+3a²−a−c.

On [a₀,1], g'≥2, g(a₀)<0, and g(9/10)≥259/1000. Its unique
zero a₁ therefore satisfies a₀<a₁<9/10. Before a₁ we have b<a.
The multiplied primary residual

    F=P(1−ab²)−b(1−a)(1+3b)

is continuous along (4), equals c>0 at a₀, and equals
−a₁(1−a₁)²<0 at a₁, using b=a and the secondary equation.
IVT produces an interior zero. No division by b is used until this
zero has been selected. The identity F=0 and P≥1 imply
1≤b+4b², excluding b≤1/4. Thus (3) has the stated admissible rates.

## 3. The new independent-reward quiet inequalities

Players 0,1 are primary and 2,3 secondary, as in the common-c proof.
Their quiet Continue payoffs are still P/b and R/a. Enumerating every
opponent subset, including the all-Continue singleton and the joining
triple, gives the quiet Quit payoffs

    T_i^p=ab+w_i(1−a)b+u_i a(1−b),
    T_i^s=ab+u_i(1−a)b+w_i a(1−b)+(1−a)(1−b).          (5)

All coefficients of w_i,u_i are nonnegative. Thus it is enough to use
the SAME worst endpoint w_i=2,u_i=c for every owner. Define

    T_p^max=c(a+b)+(1−2c)ab+(2−c)(1−a)b,
    T_s^max=1+(c−1)(a+b−2ab)+(2−c)a(1−b).             (6)

This simultaneously retains all twelve pair-member inputs; it does not
discard a joining action because that coalition is absent on path.
After substitution of (4), exact algebra gives

    S_s^min:=R/a−T_s^max
      =−(1−a)R L₂/[a²(4−R)],
    L₂=a²+ac−3a−c+1
      =a²−2a+(c−1)(a−1)<0.                             (7)

Indeed 0<a<1 and c≥1 make a²−2a<0 and the remaining term nonpositive.
Every factor in the denominator is positive, so S_s^min>0. The primary
slack is larger:

    (P/b−T_p^max)−(R/a−T_s^max)
      =c(a−b)/(ab)+(1−a)(1−b)+(2−c)(a−b)>0.            (8)

Both actual quiet slacks are therefore strictly positive uniformly over
all allowed w,u, while the active endpoints remain exact ties by (3).
The new sign in (7), rather than generic reward monotonicity, pays for
the possible INCREASE of within-partner rewards above c.

## 4. Full clocks, Never, fixed payoff, and finite laws

The prescribed phase vectors are unchanged from (1) and its phase swap.
Their Bellman recursion (3) has full-cycle continuation C=a²b²<1, so
iteration identifies these vectors with actual terminal payoffs.
Deleted-opponent cycle continuation is ab² for a primary player and
a²b for a secondary player, both below (9/10)^3. The action inequalities
from (3),(5)–(8) can be iterated against any adaptive behavioral response.
The bounded unabsorbed remainder vanishes geometrically. Thus every
complete response, including arbitrary finite dates and Never, has payoff
at most the displayed phase value. Prescribed play attains that value.

This is also a fixed uniform payoff: expected time to an opponent's
absorption is bounded by a geometric series uniformly over deviations.
With terminal rewards bounded by 4, terminal and N-stage average payoffs
differ uniformly by O(1/N). The same reasoning starts at either phase.

For completeness, censoring after K whole cycles gives marginal atoms
(1−a)a^k at dates 2k for player 0 and 2k+1 for player 1, and
(1−b)b^k at the corresponding dates for players 2,3, for 0≤k<K.
The marginal Never masses are a^K,a^K,b^K,b^K. Renewal gives U^K in
(2). A pure response before the cutoff has its infinite-opponent payoff.
After deleted-opponent survival to the cutoff, any later finite response
gets singleton 1 and Never gets zero; both are dominated by resuming
prescribed infinite play, whose phase-A value v_i≥1. Hence B_i^K≤v_i.
Quitting at the first active date, 0 or 1, attains v_i and remains in
the support calendar for every K≥1. Thus B_i^K=v_i exactly. Since
max_i v_i<8 and C<(9/10)^4, (2) follows. Joint survival and deleted
survival were not identified in this argument.

The exact finite laws and the target v therefore satisfy the current
fixed-target terminal acceptance consumer, not merely a menu-Nash test.
Their direct horizon bounds from the common-c proof also survive:
finite-horizon Nash gain is at most E^K+16K/N and delivery error at most
E^K+8K/N. The proof only uses the retained 2K dates, reward bound 4,
and the nonnegative after-cutoff singleton 1; each remains literal here.

## 5. Matching symmetry and source comparison

The permutation π defined by

    π(0)=3, π(1)=2, π(2)=0, π(3)=1

preserves the fixed singleton, passive-pair, triple and grand rows and
swaps the two cross matchings. Applying it to the table in Section 1
therefore gives the other raw section: common active reward c on03/12,
independent other-cross rewards in[1,c] on02/13, and independent
within-partner rewards in[1,2]. Relabeling preserves every complete
behavioral strategy, every response law, Never, and the payoff comparison.

The prior common-c export supplies rate production and the reusable
finite-law argument. It did NOT permit w_i>c; the present independent
quiet estimate (7) establishes that larger section. Conversely, decreasing
u_i below c after checking (7) is a straightforward same-table-coordinate
comparison, not a new strategic selection theorem by itself.

Named production interfaces remain the actual periodic behavioral
compiler, `quittingGame_isUniformEquilibriumPayoff_of_terminalTargetAcceptance`
in `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`,
and the capped-joint/paired-interval sources audited in the common-c
export. Their generic compilers are not being renamed as new producers.
The paired interval sources still have the incompatible singleton sign
pattern; allowing w_i>1 also leaves the literal capped-joint hypothesis.
The unchanged matrix and small-hazard payoff limit 5/4 remain as before.

CODEX_RADO_BOUNDARY is independently studying stationary exits in the
twelve-parameter box. His current whole-section checks cover equal
pair-member row sums in[5,6] and a separate source when every row sum is
at least29/5. Those do not subsume this section, whose row sums may be
independently unequal and below5. This is coordination of precise raw
hypotheses, not an assertion that every other stationary theorem fails.

## 6. Exact corner test: rates versus matching selection

An initial corner sets all member entries on02/13 to1 and all member
entries on01/03/12/23 to2. For the FIXED02/13 schedule with four interior
Continue probabilities A,B,C,D (players0,1,2,3), active ties necessarily
give

    1=C(1−B+3D−2BD),       1=D(1−A+3C−2AC),
    1=AB(4−3D),            1=AB(4−3C).                   (9)

The last two imply C=D=b and the first two then imply A=B=a. Therefore
four-rate reselection cannot escape the original c=1 active equations.
They force b=(4a²−1)/(3a²) and the unique admissible quartic root
a∈(37/50,3/4), as established by `existsUnique_periodTwoParameter`
and `periodTwoParameter_mem_isolatingInterval` in
`UniformEquilibrium/Quitting/Examples/BlockPair/FourPlayerPairedSingletonPeriodTwo.lean`.
Its secondary quiet joining gain at this corner is

    1+a+b−2ab−1/a
      =(1−a)(5a²−2a−1)/(3a²)>0.                       (10)

This is an exact failure of EVERY all-interior root for that fixed
matching, not just a badly selected symmetric root. Boundary hazards
were not excluded by this calculation, and no full-game gap is claimed.

The SAME corner is solved by the other matching: it belongs to the
Section5 raw section with c=2, within-partner rewards2 and other-cross
rewards1. Thus the correct deduction is that matching selection matters;
this example is not a residual obstruction to the original task.

## 7. Verification and remaining question

Exact symbolic arithmetic checked (4), the worst-case slack factorization
(7), the slack difference (8), and all original-table quiet expressions
in (5). The proof uses a genuine parameter interval, not a small
perturbation radius or numerical rate selection. The matching permutation
was checked against all fixed coalition coordinates.

The whole twelve-parameter problem is not answered. The unsupplied step
is selection when neither matching has its four active member rewards
equal to a common level dominating the alternative cross rewards.
Merely keeping four distinct positive rates does not repair (9)–(10).
No claim that two or four phases are exhaustive is made. The concrete
next question is whether a raw matching comparison or RADO's stationary
exit can handle the genuinely unequal active-member configurations.

The preceding exported packet and its author note remain unchanged.
No Lean, shared index, or export was edited, and no build was run.
