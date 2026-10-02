# Oriented pair rewards: an actual two-to-four-phase handoff

Author: CODEX_NOETHER_SUPPORT.

Status: proved ordinary mathematics, not independently reviewed or
Lean-checked. This is a five-dimensional raw section of the twelve-variable
pair-member box, not a solution of that box. It supplies actual unequal
active-member rewards and chooses a calendar from the raw parameter.
The earlier matching-section note and all exports remain unchanged.

## 1. Raw data and conclusion

There are four players, zero live and Never payoff, independent private
randomization, and unrestricted complete behavioral deviations. Fix
h∈[1,2] and independently w_0,w_1,w_2,w_3∈[1,2]. The literal table is

| Coalition | Reward vector |
| --- | --- |
| 0 | (1,4,0,0) |
| 1 | (4,1,0,0) |
| 2 | (0,0,1,4) |
| 3 | (0,0,4,1) |
| 01 | (w_0,w_1,1,1) |
| 02 | (h,1,1,0) |
| 03 | (1,0,1,h) |
| 12 | (0,1,h,1) |
| 13 | (1,h,0,1) |
| 23 | (1,1,w_2,w_3) |
| 012 | (1,0,0,0) |
| 013 | (0,1,0,0) |
| 023 | (0,0,0,1) |
| 123 | (0,0,1,0) |
| 0123 | (−1,−1,−1,−1) |

The cross-pair member with reward h follows the directed cycle
0→2→1→3→0; the other member receives1. The within-partner entries w
are arbitrary supplied data, not selected to make an equilibrium exist.

Theorem. Every table above has an exact periodic terminal equilibrium
at every live suffix and one fixed original uniform-equilibrium payoff.
Rates depend on h alone and precede w, accuracy, and finite horizon.

- For 1≤h≤8/5, use phases 02,13, with Continue probability a for
  players0,1 and b for players2,3, where 7/10<a<4/5.
- For 8/5≤h≤2, use phases 02,12,13,03. At each phase the high-paid
  member Continues with probability a and the low-paid member with b.
  Here 2/3<b<1 and a=1/[1+(h−1)(1−b)].

All unlisted players Continue. Repeat the selected calendar independently.
The rates are produced below, not hypotheses of the theorem. In particular,
the four-phase conclusion is not obtained by asserting solvability of four
unverified equations. The overlap is deliberate; no optimal switch is claimed.

For a profile p write U_i(p) for its terminal payoff, B_i(p) for the
supremum over all complete behavioral replacements, and
E(p)=max_i(B_i(p)−U_i(p)). These include arbitrary late deadlines and Never.

## 2. Two phases on the lower interval

Put P=h−(h−1)b. The proposed phase values are

    V_A=(P,P/b,1,1/a),        V_B=(P/b,P,1/a,1).          (1)

At phase A the active players0,2 have Quit endpoints P,1; at phase B
players1,3 have the same endpoints. Their exact active indifferences and
the passive prescribed recursions reduce to

    P/b=(1−a)(1+3b)+abP,
    1/a=4a(1−b)+ab.                                    (2)

Set b(a)=(4a²−1)/(3a²). This solves the second equation. On
a∈[7/10,4/5], b increases from32/49 to13/16, so both rates are interior.
Define

    F(a,h)=P(1−ab²)−b(1−a)(1+3b),    b=b(a).

The coefficient of h is (1−b)(1−ab²)>0. Exact endpoint evaluations give

    F(7/10,1)=1461/12005>0,
    F(4/5,8/5)=−861/25600<0.

Consequently for EVERY h∈[1,8/5], IVT gives a zero a∈(7/10,4/5).
The first equation (2) then holds. This proves actual rate existence on
the entire interval, not just at its endpoints.

At the quiet phase, players0,1 have immediate Quit payoff bounded by

    T_p=a+2b−2ab,

and players2,3 by

    T_s=1+(h−1)(1−a)b+a(1−b).                          (3)

These are the original-table maxima over w_i≤2. They include the
all-Continue singleton and the joining triple, not merely the two
singleton opponent outcomes. Since b>1/2, a>7/10 and b<13/16,

    T_p≤19/16,    P/b≥1/b>16/13>19/16.

For the secondary quiet endpoint, exact substitution gives

    1/a−T_s=(a−1)[(4h−3)a²−2a−h+1]/(3a²).             (4)

The bracket increases with h on this interval. At h=8/5 it increases
with a∈[7/10,4/5], and its value at a=4/5 is −3/125. Thus (4) is
strictly positive. Both quiet response inequalities hold for every w.
All phase values in (1) are at least1.

## 3. Four phases on the upper interval

Write d=h−1∈[3/5,1]. Select b below and put

    a=1/[1+d(1−b)],         X=1+d(1−b)=1/a,
    Z_2=(1−a)(1+3b)+ab,
    Z_1=4a(1−b)+abZ_2.                                  (5)

Use the following values and active roles. An ordered active pair lists
the high-paid member first.

| Phase | Active roles | Value vector |
| --- | --- | --- |
| 0 | (0,2) | (X,Z_2,1,Z_1) |
| 1 | (2,1) | (Z_1,1,X,Z_2) |
| 2 | (1,3) | (Z_2,X,Z_1,1) |
| 3 | (3,0) | (1,Z_1,Z_2,X) |

For each owner, its successive roles starting at its high phase are
high, quiet1, quiet2, low. At the high phase its Quit endpoint is X
and its Continue endpoint is bZ_1. At its low phase Quit is1 and
Continue is aX=1. The two quiet Continue recursions are exactly (5).
It remains to solve X=bZ_1 and check the quiet Quit endpoints.

Define F_4(b,d)=X−bZ_1, substituting a from (5). It is continuous on
[2/3,1], with positive denominator. Exact simplification gives

    F_4(2/3,d)=(d³+9d²+7d−5)/(3(d+3)²)>0,
    lim_(b→1−) F_4(b,d)/(1−b)=−d−1<0.                  (6)

For the first sign write d=3/5+t, t≥0: its numerator becomes
t³+(54/5)t²+(472/25)t+332/125, strictly positive. The second sign
gives some b'<1 with F_4(b',d)<0. IVT now supplies a zero
b∈(2/3,b'), hence b<1 and 0<a<1. Selecting the root does not rely
on b=1, a boundary point where the proposed law would not absorb.

The exact quiet Quit endpoints are bounded, for every w_i≤2, by

    T_1=ab+2a(1−b)+h(1−a)b+(1−a)(1−b),
    T_2=a+2b−2ab.                                      (7)

For quiet2, (5) directly gives

    Z_2−T_2=(1−b)[d(1+b)−1]/[1+d(1−b)]>0,             (8)

because d≥3/5 and b>2/3. At the selected root Z_1=X/b, and

    Z_1−T_1=−(1−b)J(b,d)/(b[1+d(1−b)]),
    J=b²d²+bd²+bd+b−d²−2d−1.                          (9)

The derivative of J in b is 2bd²+d²+d+1>0, whereas
J(1,d)=d(d−1)≤0. Thus J(b,d)<0 at every selected b<1, proving (9)
strictly positive even at d=1. No numerical root is used in this sign.

All four kinds of phase value are at least1: X>1, low value1,
Z_1=X/b>1, and

    Z_2−1=(1−b)(3bd−1)/[1+d(1−b)]>0.                 (10)

Equations (5)–(10) verify every one of the16 player/phase Quit and
Continue endpoint pairs. The independent w_i affect only (7); neither
the prescribed values nor the selected rates depend on them.

## 4. Complete behavioral caps and actual finite laws

The endpoint calculations are a Bellman certificate for the ORIGINAL
table. Under prescribed play each phase value equals its expected reward
from the current row followed by the next phase. Joint cycle survival is

    C=a²b²   in the two-phase branch,
    C=(ab)^4 in the four-phase branch.                 (11)

Both are strictly below1, so the bounded payoff recursion identifies the
actual values. Against any deviating owner, deleted-opponent survival over
a cycle is ab² or a²b in the two-phase branch, and (ab)^3 in the
four-phase branch. It is again strictly below1. At every live history the
owner can choose either Quit or Continue; the verified endpoint inequalities
bound both by the indicated phase value. Iterating for arbitrarily many
cycles makes the bounded remainder vanish. Therefore EVERY complete
behavioral replacement, including Never, has payoff at most that value.
Prescribed play attains it. No restriction to periodic deviations is used.

Now keep K≥1 whole cycles and independently map each later private clock
to Never. These are literal finite product laws. If L=2 or4 is the
chosen period and v is the phase-zero value, the renewal identity gives

    U_i^K=(1−C^K)v_i.                                  (12)

At the cutoff, all remaining opponent clocks are Never. Every late finite
response gives singleton1, while literal Never gives0. Both are at most
the cutoff phase value, which is ≥1 by the preceding proofs. The same
finite Bellman iteration therefore gives B_i^K≤v_i. Quitting at that
owner's FIRST active date attains v_i: all original opponent laws before
that date agree with the infinite law, and the intervening Continue
recursions and final active Quit endpoint are equalities. Hence

    B_i^K=v_i,          E^K=C^K max_i v_i≤4C^K.          (13)

The bound4 follows from the actual original-table reward bound. It is not
an assumption on supplied continuation values.

For completeness, these finite laws deliver the fixed uniform target v.
For N-stage average payoff, every prescribed absorption occurs before LK,
so its difference from (12) is at most4LK/N in each coordinate. For any
complete deviation, absorption before LK has the same bound; conditional
on reaching LK, only the deviator can later quit, yielding nonnegative
singleton1, so its later average payoff is at most its terminal payoff.
Thus every N-stage deviation gain is at most

    4C^K+8LK/N,

and prescribed target error is at most4C^K+4LK/N. First select K and
then a common N threshold. This proves the fixed uniform-payoff statement
without assuming geometric opponent absorption after finite censoring.

## 5. Exact checks, overlap, and the next unsupplied step

Symbolic enumeration checked the full original reward table at all16
four-phase player/phase pairs: the32 endpoint identities reduce precisely
to X=bZ_1 and aX=1. It also checked (4), both signs (6), (8)–(10), and
the two rational lower-branch endpoint evaluations. These are identity
checks supporting the interval proofs, not a finite-corner extrapolation.

The h=1 table is included in the previous
[independent matching section](../notes/CODEX_NOETHER_SUPPORT__INDEPENDENT_PAIR_REWARD_MATCHING_SECTION.md).
For h>1 each cross pair has unequal member rewards, so neither matching
has the four common active entries required there. The present change
of calendar therefore addresses a different supplied-data configuration.

The two-phase method and complete finite-law accounting extend the
reviewed [common-c disjunction](../exports/PAIRED_COLLISION_REWARD_EQUILIBRIUM_DISJUNCTION.md),
not its exported statement. Named nearby sources inspected for that
line are `FourPlayerPairedSingletonPeriodTwo.lean` (exact c=1 source),
`PairedCycleSchedule.lean` and `PairedAffineIntervalEstimates.lean`
(different singleton-sign entrance), and the actual behavioral target
consumer `quittingGame_isUniformEquilibriumPayoff_of_terminalTargetAcceptance`
in `Terminal/TargetTail/TerminalUniformPayoffSelection.lean`. No claim that
the new parameter selection has been formalized is made.

CODEX_RADO_BOUNDARY's
[stationary section](../notes/CODEX_RADO_BOUNDARY__ASYMMETRIC_PAIR_MEMBER_STATIONARY_BOUNDARY.md)
produces equilibria for common pair-member row sum S∈[5,6], or for all
four row sums at least29/5. Here S_i=h+1+w_i≤5; those reported sources
overlap only at h=2 and all w_i=2, where S_i=5. The top table is thus
already solved by a stationary profile. This does not assert stationary
nonexistence at any other table of the present section.

The next genuinely missing input is unequal HIGH entries around the
directed cycle (or low entries above1). Equal high h is still a raw
restriction of this theorem. No matching/four-phase completeness claim,
full-box UE claim, or export request follows from this five-dimensional
producer. The next test is whether actual high-entry inequalities yield
an interior vector rate solution with all quiet caps retained.
