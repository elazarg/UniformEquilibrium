# Matching reselection closes the single-reward path

Author: CODEX_NOETHER_SUPPORT.

Status: proved ordinary mathematics, not independently reviewed or
Lean-checked. The SAME raw path investigated in the first-contact note
has an actual equilibrium for every u∈[1,2], by selecting the other
matching. No connected equilibrium-path assumption or new parameter-box
generalization is made. Existing notes and exports remain unchanged.

## 1. Exact original table and conclusion

Players are0,1,2,3, live and Never payoff are zero, randomization is
independent and private, and every unilateral complete behavioral
replacement is allowed. Fix u∈[1,2] and use

| Coalition | Reward vector |
| --- | --- |
| 0 | (1,4,0,0) |
| 1 | (4,1,0,0) |
| 2 | (0,0,1,4) |
| 3 | (0,0,4,1) |
| 01 | (2,2,1,1) |
| 02 | (1,1,1,0) |
| 03 | (1,0,1,1) |
| 12 | (0,1,u,1) |
| 13 | (1,1,0,1) |
| 23 | (1,1,2,2) |
| 012 | (1,0,0,0) |
| 013 | (0,1,0,0) |
| 023 | (0,0,0,1) |
| 123 | (0,0,1,0) |
| 0123 | (−1,−1,−1,−1) |

This varies only r_2({1,2}) and is exactly the path of
[the first-contact calculation](../notes/CODEX_NOETHER_SUPPORT__FIRST_QUIET_CONTACT_INSERTS_A_LEGAL_PERIODIC_ROLE.md).

Theorem. For every u∈[1,2], there are A,B,b∈(0,1), selected from u,
such that the following original-table profile is an exact terminal
equilibrium at every live suffix:

- Phase A: only players3,0 are active, with Continue probabilities A,b.
- Phase B: only players2,1 are active, with Continue probabilities B,b.

Repeat these rows independently. Put P=u−(u−1)b. The phase-A payoff
and full behavioral caps are

    v=(1,1/B,P/b,1).                                    (1)

The rates precede accuracy and finite horizon. Censoring each private
clock after K≥1 complete cycles to Never gives actual finite laws with

    U_i^K=(1−C^K)v_i,       B_i^K=v_i,
    C=ABb²≤2/5,            E^K≤4(2/5)^K.                (2)

Thus every supplied table has one fixed ORIGINAL uniform-equilibrium
payoff. Neither a branch of the previous matching nor a favorable
continuation vector is an input.

## 2. Relabeling the actual matching

For the calculation, permute the standard labels by

    π(0)=3, π(1)=2, π(2)=0, π(3)=1.

This permutation preserves every fixed singleton, passive pair, triple,
grand, within-member, live and Never coordinate. Standard active pairs
02,13 become the original03,12. The special reward u becomes standard
r_1({1,3})=u. All other active member rewards and ALL unused cross-member
rewards are1; all within-member rewards are2.

Accordingly the four standard continuation probabilities are A,B,b,b,
and the proposed standard phase vectors are

    V_A=(1,P/b,1,1/B),       V_B=(1/b,P,1/A,1).          (3)

The following proof is therefore a literal payoff-coordinate permutation,
not a terminal shift, a change of own singletons, or a strategic-equivalence
claim that ignores Never.

## 3. One scalar root produced from every u

For b∈[7/10,4/5] define

    B=(3b²+b−1)/(b(1+2b)),       A=1/[B(4−3b)].          (4)

The numerator3b²+b−1 is positive. Moreover

    B'(b)=(b²+4b+1)/(b²(1+2b)²)>0,
    39/56≤B≤43/52,
    520/817≤A≤35/39<1.                                 (5)

The bounds for A follow simply by multiplying the endpoint bounds for
B and4−3b. Thus every denominator and every continuation probability
in the argument is legal throughout the entire interval.

Equations (4) make three exact active/recursion identities hold:

    1/b=(1−B)(1+3b)+Bb,
    1/A=B(4−3b),          1/B=A(4−3b).                 (6)

The remaining cleared residual is

    F(b,u)=P(1−Ab²)−b(1−A)(1+3b).                     (7)

Its u coefficient is (1−b)(1−Ab²)>0. Exact rational evaluations give

    F(7/10,1)=2461/24700>0,
    F(4/5,2)=−48/1075<0.                               (8)

Therefore for EVERY supplied u∈[1,2], continuity and (8) give a zero
b∈(7/10,4/5). At this selected zero,

    P/b=(1−A)(1+3b)+AbP,                               (9)

so all four original active ties and prescribed recursions hold. No
uniqueness, monotonicity of the selected zero, or continuation in u is
needed for this actual-data existence theorem.

## 4. All quiet responses on the full selected interval

The two standard primary quiet Quit endpoints are respectively
B+2b−2Bb and A+2b−2Ab. The two secondary ones are
1+B(1−b) and1+A(1−b). These enumerate the all-Continue singleton,
both singleton opponents, and the joining triple. Using (4), their four
slacks have the following exact expressions or lower bounds:

    S_0=1/b−B−2b+2Bb
        =(b−1)(2b²−b−2)/(b(2b+1))>0;

    S_1=P/b−A−2b+2Ab
        ≥−(b−1)H(b)/[b(3b−4)(3b²+b−1)]>0,
    H(b)=18b⁴+4b³−19b²−3b+4;

    S_2=1/A−1−B(1−b)
        =−(b−1)(6b²+b−3)/(b(2b+1))>0;

    S_3=1/B−1−A(1−b)
        =−(b−1)(5b²−4)/[(3b−4)(3b²+b−1)]>0.          (10)

Here S_1 uses P≥1, which holds because the actual input u≥1. For
its sign, H''(b)=216b²+24b−38>0 and H'(7/10)=122/125>0,
so H increases on this interval. Its maximum is
H(4/5)=−712/625<0. The other signs follow directly from
7/10≤b≤4/5: 2b²−b−2<0, 6b²+b−3>0, and5b²−4<0,
with3b−4<0 and3b²+b−1>0. Thus all four quiet inequalities hold
throughout the SAME rate interval used for existence, not only at a
numerically selected zero.

## 5. Complete deviations, finite censoring, and fixed target

Relations (6),(9),(10) prove every active and quiet Quit/Continue
endpoint condition for (3). The actual joint cycle survival is

    C=ABb²=b²/(4−3b)≤2/5<1.

Each deleted-opponent cycle survival is likewise a product of three
strictly interior continuation probabilities, uniformly below1 by (5).
Bounded Bellman iteration therefore identifies the actual phase payoffs
with (3) and bounds EVERY complete behavioral deviation, including Never,
by those same values. Prescribed play attains them.

All phase values are at least1. For whole-cycle censoring, renewal gives
the payoff identity in (2). At the cutoff every remaining opponent clock
is Never; all later finite responses pay singleton1 and Never pays0.
The cutoff value dominates both, so the finite Bellman bound gives
B_i^K≤v_i. Quitting at the first active date attains v_i, since every
earlier response outcome and Continue equality is unchanged. This proves
(2), including the original unlisted late deadlines.

All absolute rewards are at most4 and prescribed finite absorption is
before2K. The direct N-stage bounds are4(2/5)^K+16K/N for every
deviation gain and4(2/5)^K+8K/N for delivery of v. After the cutoff
only the deviator can quit, for nonnegative singleton1. Selecting K and
then a common N threshold proves the original fixed uniform-payoff claim.

## 6. What this closes and what the old branch did not prove

The [four-rate rectangle](../notes/CODEX_NOETHER_SUPPORT__INDEPENDENT_CROSS_REWARD_BOX_PERIOD_TWO_SOURCE.md)
provides the general active equations and full-cap discipline used here.
Its fixed square certificate is not used to assert existence outside its
box: (4)–(8) are a new, complete scalar production argument for this
specific raw path. The baseline c=1 identities agree with the inspected
`periodTwo_active_identity_*` declarations in
`FourPlayerPairedSingletonPeriodTwo.lean`. No Lean proof of the new
scalar path selector is claimed.

Exact arithmetic checked all60 permutation coordinates, the three
eliminated equalities (6), both rational endpoint signs (8), all four
slack factorizations (10), and the stated H derivative/endpoint signs.

As a diagnostic only, numerical continuation of the PREVIOUS five-role
branch suggested that player3's remaining quiet slack vanishes near
t≈0.103948 and u≈1.914771. Adding it to that branch's phase A then
gave a nearby algebraic branch with a negative new hazard for increasing u.
These later-contact observations were NOT converted into an exact
connected-branch or local nonexistence theorem. They are not used above.

The present theorem instead chooses a legal profile on the SAME table
for every u through2. It does not transport the previous profile, impose
connected equilibrium selection, or infer noUE from a failed local chart.
It closes the chosen single-coordinate path, not arbitrary independent
movement of the other eleven pair-member rewards. A remaining global
question is whether a raw-table path can always obtain a comparable
same-table alternate schedule when its currently selected support loses
an inequality. No such exhaustive disjunction is claimed.
