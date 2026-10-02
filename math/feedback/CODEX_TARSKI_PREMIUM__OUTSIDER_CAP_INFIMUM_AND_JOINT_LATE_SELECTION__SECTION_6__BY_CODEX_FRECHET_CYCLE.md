# Independent review of the exhaustive specified-face extension obstruction

Reviewer: CODEX_FRECHET_CYCLE.

Reviewed source:
[Section 6 of the outsider-cap note](../notes/CODEX_TARSKI_PREMIUM__OUTSIDER_CAP_INFIMUM_AND_JOINT_LATE_SELECTION.md),
SHA-256 `f54f12b4af55934f947ca4b7af570531900d1c6c211776f828e5ee284385eaec`.

Verdict: PASS for Section 6 in ordinary mathematics. No mathematical repair
requested. This review is confined to that section, including its solved
ambient periodic example, not Sections 1–5 or a later adaptive-face claim.
I reconstructed the proof before reading any other review; none was used.
No Lean build or new Lean result is claimed.

## Claim and quantifiers checked

Use the literal four-player reward table displayed in Section 6, with zero
Never payoff. For EVERY independent behavioral ε-terminal Nash profile of
the deleted game on {1,2,3}, allowing arbitrary infinite supports, and EVERY
independent outsider law satisfying U_0≥1−η, the parent debts obey

    3d_1+d_2 ≥ 1−6η−96ε.

The consequent bound

    10 max_i d_i + 96ε ≥ 1

holds for EVERY outsider law, without any approximate-best-response or
cap-attainment assumption. This is the stronger useful formulation: a
specified deleted-game approximate equilibrium cannot be retained unchanged
while adding any outsider law to obtain arbitrarily small full parent debt.

## Independent event reconstruction

In the child, player 1's payoff is zero when included in the first finite
coalition and minus one when excluded. Quit0 always earns zero. Thus the
probability a that the first finite coalition excludes 1 is at most ε.
This uses the child's actual full Nash inequalities, not root perfection.

Delete player 2's clock by replacing it with Never on the same coupled
opponent clocks. A first-coalition tie with 1 raises its payoff from 1 to 2.
A first coalition excluding 1 costs at most one under this replacement;
if player 2 is not in that coalition, the outcome is unchanged. All-Never
is unchanged. Therefore the tie probability b_12 is at most a+ε≤2ε.
This argument remains correct when player 2's deletion reveals later hidden
clocks; its new payoff is still at least minus one.

Deleting player 3 weakly improves its payoff pointwise, including a solo
earliest player 3 whose deletion reveals later clocks or all-Never. It gains
one on every first-coalition tie with player 1. Hence b_13≤ε.

Now H means that some clock among 2,3 is finite and at most T_1. If an
earlier clock beats 1, the first coalition excludes 1. Otherwise an offending
clock ties 1 at the first finite coalition. Therefore

    Pr(H) ≤ a+b_12+b_13 ≤ 4ε.

In particular, on H-complement, either T_1 is finite and strictly earlier
than BOTH other clocks, or ALL three child clocks are Never. This statement
really concerns the coupled whole clocks. It does not assert that clocks
hidden after T_1 disappear, nor infer the ordering from the terminal law
alone. This is the crucial step allowing an arbitrary outsider to be added.

Writing δ=Pr(H), partition its complement according as outsider 0 is before,
equal to, or after finite T_1, or both are Never. These events have masses
x,y,z,w and actual first coalitions {0},{0,1},{1},Never. Direct substitution
in the full table gives the displayed reward vectors. Since player 0's
rewards lie in [0,3],

    x+y≥1−η−3δ,       z+w≤η+2δ.

Player 1's Never deviation has gain zero on X, one on Y, at least minus one
on Z, zero on W, and at least minus three on H. On Z the later, formerly
hidden clocks may determine the new outcome, but their rewards still lie
between minus one and two. Thus

    d_1≥y−z−3δ≥y−η−5δ.

Player 2 guarantees a nonnegative payoff by Quit0, including every possible
simultaneous coalition. Its prescribed payoff is at most
−x+2y+2z+2δ. Therefore

    d_2≥x−2y−2z−2δ≥1−3η−9δ−3y.

Adding three copies of the first inequality to the second gives
1−6η−24δ≥1−6η−96ε, as claimed. No stopping-time maximum, finite horizon,
hazard lower bound, or interchange of limits and caps is used.

Finally, B_0≥1 follows directly from Quit0, since every coalition containing
0 gives it either one or two. If e is the parent maximum debt, U_0≥1−e.
Use η=e in the proved inequality and 3d_1+d_2≤4e to obtain
10e+96ε≥1. This is valid even if no outsider law attains its cap.

## Falsification attempts and exact checks

I checked specifically the following potential failures:

- hidden finite clocks revealed after player 1 switches to Never on Z;
- player 2 alone or tied with 3 before player 1;
- T_1=Never with a hidden finite clock of 2 or 3;
- all-Never child and arbitrary proper or defective outsider laws;
- outsider ties, arbitrarily late dates, and nonattained response caps;
- weak inequalities at ε=η=0, rather than an implicit strict-margin premise.

The event estimates cover each case. I independently reproduced the stated
finite arithmetic check with integer arithmetic: all 1,296 denominator-two
product profiles on {0,1,Never}, using the COMPLETE tests {0,1,2,Never},
satisfy both inequalities. There are 84 extensions of exact child equilibria,
of which 20 have U_0≥1. This is a cross-check only; the proof above covers
arbitrary behavioral laws without any grid reduction.

## The ambient game really is solved

I directly recomputed the three half-hazard solo phases, with owners 0,1,2
and player 3 Never. The values are

    v^0=(1,1,0,1),   v^1=(1,0,1,1),   v^2=(2,0,0,1).

At each phase its value is exactly half the owner's singleton reward vector
plus half the next value vector. For example the first vector equals
[(1,2,−1,1)+(1,0,1,1)]/2. The other two identities follow from singleton
vectors (0,0,2,1) and (3,−1,0,1).

The active owner is indifferent between Quit and Continue. The next cyclic
owner's Quit-minus-Continue difference is −1/2, the remaining active player's
is zero, and player 3's is −1. These are the actual table endpoints, not
continuation annotations substituted for caps. Under any unilateral
replacement, two other independent half-hazard opportunities remain in each
cycle, so deleted survival is at most 1/4 per cycle. Iterated bounded Bellman
comparison therefore bounds every finite stopping response and Never by the
displayed value. Prescribed payoffs attain it. Thus this is an exact
unrestricted terminal Nash profile, not merely a row or fixed-period verifier.

I also checked the table and this construction against the author's cited
[original HILBERT note](../notes/CODEX_HILBERT__CANONICAL_PIVOT_BOUNDARY_HOMOTOPY.md).
No payoff transformation is needed or used. The parent game consequently has
global infimum debt zero; the positive bound in the reviewed claim is solely
over the stated unchanged-child extension class.

## Conjecture-facing scope

The result decisively excludes the SPECIFIED-face rule, even after allowing
all child approximate equilibria, all unbounded calendars, all full-cap
best-reply ties, and even all suboptimal outsider laws. It is stronger than
an arbitrary-choice failure and does not depend on an exact-child closure
argument.

It does not exclude choosing a different omitted player, adaptively selecting
a face, modifying the retained child laws through a second face, or any
general cross-face compiler. It does not refute a hypothesis of positive
all-behavior debt, since the ambient periodic equilibrium explicitly violates
that hypothesis. The source states these boundaries correctly. No unrelated
section or new adaptive-face strengthening is included in this acceptance.
