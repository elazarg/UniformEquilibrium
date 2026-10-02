# Four unequal periodic rates from an independent cross-reward box

Author: CODEX_NOETHER_SUPPORT.

Status: proved ordinary mathematics, not independently reviewed or
Lean-checked. The result produces an actual two-phase equilibrium on a
twelve-dimensional raw reward rectangle. It does not solve the entire
[1,2] pair-member box. Constants below are fixed; there is no threshold
optimization task. Existing notes and exports remain unchanged.

## 1. Original data and actual output

Players are0,1,2,3, live and Never payoffs are zero, and private
randomization is independent. A unilateral deviation may replace the
ENTIRE behavioral strategy, with no bound on its stopping dates.

Choose independently

    c_i,u_i∈[1,6/5],       w_i∈[1,2],        i=0,1,2,3.

Use this literal terminal table:

| Coalition | Reward vector |
| --- | --- |
| 0 | (1,4,0,0) |
| 1 | (4,1,0,0) |
| 2 | (0,0,1,4) |
| 3 | (0,0,4,1) |
| 01 | (w_0,w_1,1,1) |
| 02 | (c_0,1,c_2,0) |
| 03 | (u_0,0,1,u_3) |
| 12 | (0,u_1,u_2,1) |
| 13 | (1,c_1,0,c_3) |
| 23 | (1,1,w_2,w_3) |
| 012 | (1,0,0,0) |
| 013 | (0,1,0,0) |
| 023 | (0,0,0,1) |
| 123 | (0,0,1,0) |
| 0123 | (−1,−1,−1,−1) |

Thus ALL EIGHT cross-pair member rewards vary independently in[1,6/5],
and ALL FOUR within-partner member rewards vary independently in[1,2].
No relation among row sums, active members, or opposite pairs is assumed.

Theorem. For every supplied active vector c there are four continuation
probabilities A_0,A_1,B_2,B_3 such that

    7/10<A_i<4/5,           3/5<B_j<13/16,              (1)

and the following SAME profile is an exact terminal equilibrium at every
live suffix for every allowed u,w: phase A has only players0,2 active,
with Continue probabilities A_0,B_2; phase B has only players1,3 active,
with Continue probabilities A_1,B_3. Repeat the two phases independently.
The selected rates need not coincide. They precede u,w and accuracy.

Write

    Q_0=c_0−(c_0−1)B_2,    Q_1=c_1−(c_1−1)B_3,
    Q_2=c_2−(c_2−1)A_0,    Q_3=c_3−(c_3−1)A_1.

The actual phase values and full behavioral caps are

    V_A=(Q_0,Q_1/B_3,Q_2,Q_3/A_1),
    V_B=(Q_0/B_2,Q_1,Q_2/A_0,Q_3).                     (2)

For K≥1, censor each private clock after K whole cycles to Never. If
v=V_A, C=A_0A_1B_2B_3, U is terminal payoff, and B is the supremum
over ALL complete behavioral replacements, these actual finite laws satisfy

    U_i^K=(1−C^K)v_i,       B_i^K=v_i,
    E^K=max_i(B_i^K−U_i^K)≤4(169/400)^K.               (3)

In particular each raw table has one fixed original uniform-equilibrium
payoff v. Neither a root, a continuation vector, nor a favorable choice
among preexisting equilibria is a strategic assumption of this theorem.

## 2. Exact elimination leaves a two-dimensional production problem

Temporarily allow A=A_0 and B=A_1 throughout the closed square
[7/10,4/5]². Put t=AB and

    q_2=c_2−(c_2−1)A,       q_3=c_3−(c_3−1)B,
    z=B_3=(4t−q_2)/(t(4−q_2)),
    y=B_2=(4t−q_3)/(t(4−q_3)).                         (4)

Here t∈[49/100,16/25] and 1≤q_j≤53/50. The denominators are
strictly positive. The map (4) increases in t and decreases in q, giving

    1500/2401≤y,z≤13/16,       hence y,z>3/5.           (5)

These bounds hold throughout the square, before a zero is selected.
The secondary equations become exact identities:

    q_2/A=4B(1−z)+Bzq_2,
    q_3/B=4A(1−y)+Ayq_3.                              (6)

Set p_0=c_0−(c_0−1)y, p_1=c_1−(c_1−1)z. The two remaining
cleared residuals are

    R_0=p_0(1−Byz)−y(1−B)(1+3z),
    R_1=p_1(1−Ayz)−z(1−A)(1+3y).                     (7)

Zero residuals mean precisely

    p_0/y=(1−B)(1+3z)+Bzp_0,
    p_1/z=(1−A)(1+3y)+Ayp_1.                          (8)

The four relations (6),(8) are the original-table quiet Continue
recursions. The values (2) also make every active Quit/Continue pair an
exact tie. No probability in (4) has been divided by before proving (5).

## 3. Uniform face signs for every independent active input

For fixed A,B and interior y,z, the first residual has the following
monotonicities. It increases with c_0 because

    ∂R_0/∂c_0=(1−y)(1−Byz)>0.

Keeping c_0 fixed and recalling p_0=c_0−(c_0−1)y,

    ∂R_0/∂z=−Byp_0−3y(1−B)<0,
    ∂R_0/∂y=−(c_0−1)(1−Byz)−Bzp_0−(1−B)(1+3z)<0.

Since z decreases with c_2 and y decreases with c_3 in (4), R_0
increases with each of c_0,c_2,c_3 on the whole allowed box. Thus the
lower-face minimum uses all three equal1; the upper-face maximum uses
all three equal6/5. The following checks are continuous interval
certificates, not corner extrapolation.

At A=7/10 and c_0=c_2=c_3=1, exact simplification yields

    R_0=L(B)/(441B²),
    L(B)=2156B³−3829B²+2090B−300.                      (9)

At A=4/5 and c_0=c_2=c_3=6/5 it yields

    R_0=H(B)/(11840B²(B+14)²),
    H(B)=877808B⁴+12107604B³−23395277B²
                     +12550140B−1696500.             (10)

To certify their signs put B=7/10+s/10, 0≤s≤1. In the degree-n
Bernstein basis binom(n,k)s^k(1−s)^(n−k), k=0,…,n, their coefficients are

| Polynomial | Bernstein coefficients, in increasing k |
| --- | --- |
| L, degree3 | 13149/500, 11461/500, 8203/375, 3164/125 |
| H, degree4 | −28544643/2500, −103589477/2500, −956519693/15000, −93466321/1250, −44201172/625 |

These identities can be checked by expansion. The basis functions are
nonnegative and sum to1. Hence L>0 and H<0 throughout the interval.
Their denominators in (9),(10) are positive. Monotonicity now proves

    A=7/10 ⇒ R_0>0,          A=4/5 ⇒ R_0<0,             (11)

uniformly over B and all active c. The second residual is obtained by
interchanging A,B, c_0,c_1, c_2,c_3, and y,z. Therefore

    B=7/10 ⇒ R_1>0,          B=4/5 ⇒ R_1<0.             (12)

Apply the two-dimensional Poincaré–Miranda theorem to (R_0,R_1) on
the square. Explicitly, Brouwer applied to coordinatewise clipping of
(A,B)+(R_0,R_1) produces a fixed point. Strict face signs exclude its
boundary; at an interior fixed point both residuals vanish. This produces
the required A,B strictly between7/10 and4/5. Formula (4) then supplies
y,z, with the strict upper bound in (1) because t<16/25.

This use needs only continuity on the square. If using the named global
continuous-field source below, first compose the rational field with
coordinatewise clipping into this square. Its denominators stay positive
everywhere, and the field on the square is unchanged.

## 4. Every inactive Quit response is paid on the original table

At a primary owner's quiet phase let B be the active primary Continue
probability and z the active secondary Continue probability. Literal
Quit payoff is

    T_p=Bz+w_i(1−B)z+u_iB(1−z).

It increases with w_i,u_i, so use w_i=2,u_i=6/5 for the upper bound.
The resulting expression decreases with B on (5), since its B derivative
is (6/5)(1−z)−z<0. It increases with z because
2−(11/5)B>0. Hence throughout the rate square

    T_p≤971/800,
    quiet value ≥1/(13/16)=16/13,
    quiet value−T_p≥177/10400>0.                        (13)

For a secondary owner use the notation (4) for its own active endpoint
q=q_2, current primary rate B, and preceding primary rate A. Its quiet
value is q/A, while its literal Quit endpoint is bounded by

    T_s=1+(u−1)(1−B)z+B(1−z),       u≤6/5.             (14)

This includes the triple payoff1 as well as the all-Continue singleton1.
There is no omitted late or simultaneous response in (14). Set

    k=B−(u−1)(1−B),
    S=q/A−T_s=q/A−1−B+kz,
    z=(4AB−q)/(AB(4−q)).

Here 0<k≤B. Regard q as an independent variable in[1,6/5], keeping
A,B,u fixed. Direct differentiation gives

    ∂S/∂q=1/A−4k(1−AB)/(AB(4−q)²)
           ≥(1−25/49)/A>0.                           (15)

Indeed k≤B, 1−AB≤1 and (4−q)²≥(14/5)². Thus the smallest
slack has q=1; it also has u=6/5 because (14) increases with u.
At these values the slack is

    S_0(A,B)=(9AB²−19AB+9B+1)/(15AB).

Its A derivative is −(9B+1)/(15A²B)<0, and its B derivative is
(9AB²−1)/(15AB²)>0 on the square. Consequently

    S≥S_0(4/5,7/10)=47/2100>0.                        (16)

The same calculation applies to the other secondary owner with A,B
and y,z interchanged. This verifies all four original quiet Quit
inequalities, uniformly over every independently supplied u,w.

## 5. Full behavioral equilibrium and finite-law output

Every active Quit/Continue endpoint equals its displayed value in (2).
Every quiet Continue endpoint equals that value by (6),(8), and every
quiet Quit endpoint is strictly below it by (13),(16). The prescribed
two-cycle survival is C=AB yz<169/400<1. Bounded recursion therefore
identifies (2) with the actual payoff at each live suffix. Each displayed
value is at least1, since every active Q_i≥1.

For any queried owner, the probability that all opponents Continue for
a whole cycle is the product of the OTHER THREE rates. It is strictly
below1. The rowwise Quit/Continue inequalities are consequently a full
Bellman bound: iterate over arbitrarily many cycles, and the bounded
surviving remainder vanishes. This includes all history-dependent
behavioral replacements and literal Never, not just periodic deviations.
Prescribed play attains the bound, so the full cap equals (2).

For the finite laws, renewal gives U_i^K=(1−C^K)v_i. Beyond date2K
every remaining opponent clock is Never; the pure late response values
are singleton1 and Never0, both below the cutoff phase value. Applying
the same finite Bellman bound gives B_i^K≤v_i. Quitting at the FIRST
active date attains v_i: opponents' finite laws before that date match
the infinite profile, and every preceding prescribed Continue equality
and final active Quit equality is exact. Thus B_i^K=v_i, proving (3).

All actual rewards have absolute value at most4. The N-stage prescribed
payoff of the finite law differs from its terminal payoff by at most8K/N.
For a complete deviation, the same bound holds for absorption before2K;
after2K only that deviator may quit, for nonnegative singleton1, so its
late average payoff is bounded above by its terminal payoff. Therefore
every N-stage gain is at most

    4(169/400)^K+16K/N,

and prescribed error from the fixed v is at most
4(169/400)^K+8K/N. Select K and then a common N threshold. This is the
original fixed uniform-equilibrium conclusion, not merely terminal Nash.

## 6. Sources, exact checks, and the unsolved extension

The topological theorem inspected is
`Math.Topology.exists_rectangular_zero_of_strict_face_signs` in
`MathUE/Topology/RectangularPoincareMiranda.lean`; use the negative of
our field for its sign convention. Its imported
`Math.Topology.exists_cube_zero_interior_of_strict_opposite_face_signs`
in `MathUE/Topology/PoincareMirandaCube.lean` proves the usual clipped
Brouwer reduction. This supplies topology, not the reward-specific signs.
No build or Lean implementation of the present producer was run.

The exact original c=1 two-phase source is
`FourPlayerPairedSingletonPeriodTwo.lean`; the reviewed
[common-c packet](../exports/PAIRED_COLLISION_REWARD_EQUILIBRIUM_DISJUNCTION.md)
supplies the preceding scalar selector and complete finite-law accounting.
The present four independent active entries are not a common-c input.
The nearby paired-affine interval sources have a different singleton-sign
entrance, as documented in that packet. The actual target consumer remains
`quittingGame_isUniformEquilibriumPayoff_of_terminalTargetAcceptance`
in `Terminal/TargetTail/TerminalUniformPayoffSelection.lean`.

Symbolic arithmetic checked (4),(6), the exact cleared polynomials
(9),(10), both Bernstein coefficient identities, and (13)–(16).
The face-sign proof ranges over every continuous input and every other
controller coordinate; testing just endpoint tables would not suffice.

This rectangle is not merely reward lowering at a supplied equilibrium:
lowering active c_i independently destroys its old equalities. The
two-dimensional producer regenerates four actual rates from those c_i.
The other eight inputs then enter the proved quiet bounds only.

There are two distinct limitations when expanding toward[1,2]. First,
the fixed production square's upper-face sign fails already when its
three relevant active entries are all5/4: at A=4/5,B=7/10,
R_0=4778003/361827648>0.
This is failure of THAT square certificate, not nonexistence of rates.
Second, quiet inequalities really can fail even at an exact active root:
the earlier [matching note](../notes/CODEX_NOETHER_SUPPORT__INDEPENDENT_PAIR_REWARD_MATCHING_SECTION.md)
Section6 sets active cross entries1 and unused cross/within entries2.
Every all-interior root of that matching then has a profitable secondary
quiet join. The SAME table is repaired by the other matching, as proved
there; this is not a no-UE example.

The [oriented handoff](../notes/CODEX_NOETHER_SUPPORT__ORIENTED_PAIR_REWARDS_TWO_TO_FOUR_PHASE_HANDOFF.md)
handles a separate common-high/low1 cyclic section by switching to four
phases. RADO's [stationary sources](../notes/CODEX_RADO_BOUNDARY__ASYMMETRIC_PAIR_MEMBER_STATIONARY_BOUNDARY.md)
require balanced row sums at least5, or every row sum at least29/5;
here every row sum is at most22/5. Neither their failure nor failure of
our fixed face signs currently implies a raw-input matching or four-phase
entrance. Establishing such a SAME-table alternate selection, rather
than checking another corner, is the remaining conjecture-facing question.
