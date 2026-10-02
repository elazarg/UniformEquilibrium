# Exact finite-menu Nash can fail uniformly while approximate selection succeeds

## Status and scope

This note proves an explicit separation for a four-player quitting game with
own-singleton rewards `(1,0,0,0)` and Never payoff zero. It does **not** prove
finite approximate selection for every reward table and is **not** a
counterexample to uniform-equilibrium existence.

For the displayed game:

1. For every finite deadline N >= 1 there is exactly one finite-menu Nash
   product law, and its unrestricted late defect L_0 equals 1/2.
2. For every K >= 1 an explicitly given product law on F_(3K) satisfies
   E_(3K) = L_0 = 8^(-K).
3. The infinite cyclic version is an exact behavioral equilibrium.
4. For the approximate profile with N = 3K, player 1's marginal is at total
   variation distance 1 - 2^(-K) from the marginal of the unique exact
   finite-menu equilibrium.

These are mathematical proofs, not Lean formalizations. The accompanying
standard-library Python script independently checks the displayed payoff and
best-response formulas by exact rational arithmetic for several K. Its
computations do not substitute for the all-N uniqueness proof.

## 1. The reward table

Write predecessor/successor cyclically on {1,2,3}:

- prev(1)=3, prev(2)=1, prev(3)=2;
- next(1)=2, next(2)=3, next(3)=1.

For every nonempty coalition S set

    r_0(S) = 1 if 0 belongs to S, and 2 otherwise.

For i in {1,2,3}, set

    r_i(S) = 0                         if i belongs to S;
             -1                        if i does not belong to S and 0 belongs to S;
             2 1_{prev(i) in S}
               - 1_{next(i) in S}      otherwise.

The full table is:

| S | r(S) |
|---|---|
| {0} | (1,-1,-1,-1) |
| {1} | (2,0,2,-1) |
| {2} | (2,-1,0,2) |
| {3} | (2,2,-1,0) |
| {0,1} | (1,0,-1,-1) |
| {0,2} | (1,-1,0,-1) |
| {0,3} | (1,-1,-1,0) |
| {1,2} | (2,0,0,1) |
| {1,3} | (2,0,1,0) |
| {2,3} | (2,1,0,0) |
| {0,1,2} | (1,0,0,-1) |
| {0,1,3} | (1,0,-1,0) |
| {0,2,3} | (1,-1,0,0) |
| {1,2,3} | (2,0,0,0) |
| {0,1,2,3} | (1,0,0,0) |

All absolute rewards are at most 2.

## 2. A three-player row lemma

Consider the one-row game of players 1,2,3, with player 0 absent and
all-Continue continuation payoff zero. Let x_i be their quit probabilities.
Player i's Quit payoff is zero and its Continue payoff is

    C_i(x) = 2 x_{prev(i)} - x_{next(i)}.

**Lemma.** Its only Nash equilibrium is x=(0,0,0).

**Proof.** Suppose x_m=max_i x_i>0. Then

    C_{next(m)} >= x_m > 0,

so x_{next(m)}=0. Since x_m>0, player m uses Quit, and therefore

    C_m = 2 x_{prev(m)} <= 0.

Thus x_{prev(m)}=0. But then

    C_{prev(m)} = -x_m < 0,

which forces x_{prev(m)}=1, a contradiction. The all-Continue profile is an
equilibrium since all three players are indifferent there. QED.

## 3. No exact finite-menu equilibrium can have a certainly absorbing row

Fix N and an exact finite-menu Nash product law. At any date reached with
positive joint survival, consider its conditional row q. Suppose this is the
first row at which joint survival after the row is zero. Some q_i equals 1.

If some zero-singleton player has q_i=1, player 0 obtains 2 by continuing
at that row and only 1 by quitting. Hence q_0=0.

For each player j in {1,2,3}, two legal deviations are available:

- Quit now, obtaining conditional payoff 0;
- Continue now, then quit at the next date. If this is the last menu date,
  Continue now and choose Never instead.

In the second deviation, conditional on everyone continuing in the current
row, the subsequent payoff is exactly zero. Before the last menu date this
follows because player j's reward is zero in every coalition containing j;
at the last date it follows because everyone subsequently plays Never.

Since absorption is certain under the prescribed current row, its payoff
is exactly the one-row payoff with empty outcome zero. The Nash inequalities
therefore imply that the zero-singleton players play an equilibrium of the
three-player row game in Section 2. That is impossible when one of them has
quit probability 1.

If instead q_0=1, every zero-singleton player obtains -1 by continuing and
0 by quitting, forcing all three to quit with certainty. This reduces to the
contradiction in the previous paragraph.

There is therefore no such row. Every live date through the deadline is
reached with positive probability, and all four Never masses are positive.
At every such date, the conditional suffix is a Nash equilibrium: a strictly
profitable suffix replacement would give a strictly profitable complete-law
replacement, multiplied by the positive probability of reaching that date.

This argument covers all finite-menu Nash equilibria, including those not
assumed subgame perfect. In particular, off-path punishments do not provide
an escape from the following backward argument.

## 4. Exact classification of all finite-menu Nash equilibria

### Last row: continuation zero

Put A=1-product_{i=1}^3(1-q_i). Player 0's action payoffs are

    Quit: 1;             Continue: 2 A.

For i in {1,2,3} they are

    Quit: 0;
    Continue: -q_0 + (1-q_0)(2 q_{prev(i)} - q_{next(i)}).

No q_i can equal 1: a sure zero-singleton quitter forces q_0=0 and then
contradicts Section 2; a sure player-0 quitter forces all the others to quit,
which is itself inconsistent with player 0's best reply.

Nor can q_0=0, because then Section 2 forces all the others to continue,
against which player 0 strictly prefers to quit. Hence 0<q_0<1 and

    A=1/2.

Every q_i for i=1,2,3 is positive. Indeed, q_i=0 would make the Continue
payoff of next(i) strictly negative, forcing q_{next(i)}=1, already excluded.
All three are consequently interior, and their indifference equations are

    2 q_{prev(i)} - q_{next(i)} = q_0/(1-q_0).

This invertible cyclic linear system has the unique solution with all three
coordinates equal. Define

    a = 1 - 2^(-1/3),
    b = a/(1+a).

The unique last-row equilibrium is

    q* = (b,a,a,a),

and its payoff is

    v = (1,0,0,0).

### Earlier row: continuation v

For continuation v, the zero-singleton players have the same action-payoff
formulas as above, whereas player 0's Continue payoff becomes

    2 A + (1-A) = 1+A.

If A>0, player 0 strictly prefers Continue, so q_0=0. Section 2 then forces
A=0, a contradiction. Thus A=0. If q_0>0, every zero-singleton player would
strictly prefer Quit, so q_0=0 as well.

The only equilibrium of the row game with continuation v is therefore
all-Continue, and its payoff remains v.

### Backward conclusion

By Section 3, every conditional suffix is subject to these Nash conditions.
Backward induction gives the unique exact finite-menu Nash product law:
all players continue at dates 0,...,N-2, and play q* at date N-1, with Never
if they continue at the last row. Conversely, these rows form a finite
subgame-perfect equilibrium, so the product law does exist.

For this law,

    D_0 = (1-a)^3 = 1/2,
    W_0 = 2(1-D_0) = 1,
    U_0 = 1.

Therefore, for every N>=1 and every exact finite-menu Nash law p,

    E_N(p)=0,                L_0(p)=1/2.

## 5. Explicit finite approximate selectors

Choose K>=1 and N=3K. Let player 0 play Never with probability 1. For
player i in {1,2,3}, define its independent stopping law by

    p_i(3k+i-1) = 2^(-(k+1))       for k=0,...,K-1,
    p_i(Never) = 2^(-K),

and zero at all other dates.

Equivalently, players 1,2,3 take turns; on its designated date the active
player quits with conditional probability 1/2. After K cycles they all
continue forever. This construction uses independent private randomization
only.

Write J=8^(-K). Direct evaluation gives

    U(p) = (2-2J, 0, 1-J, 0),
    B^N(p) = (2-2J, 0, 1, 0),
    B(p) = (2-J, 0, 1, 0).

Here is a verification of all three identities.

### Prescribed payoffs

One three-date cycle survives with probability 1/8. Its zero-singleton
players' unconditioned payoff contribution is (0,7/8,0). Summing K cycles
gives (0,1-J,0). Player 0 receives 2 on every finite absorption, hence
2(1-J).

### Player 0's cap

Its payoff from quitting at date t is

    2 - Pr(no opponent quits strictly before t).

This is nondecreasing in t. At the last menu date it is 2-2J, which is
also its Never payoff. At every date at or after N it is 2-J. Thus its
menu cap is 2-2J and its unrestricted cap is 2-J.

### The other players' caps

When player i in {1,2,3} quits, its payoff is zero. Its pure-time payoff
is consequently the expected reward from opponents' absorption strictly
before that date.

For players 1 and 3, this cumulative expected reward starts at zero,
drops below zero after the first relevant opponent's date, and returns to
zero after the second relevant opponent's date in each cycle. Its maximum
is zero, including the Never endpoint.

For player 2, at the beginning of opponent cycle k this quantity is
1-4^(-k). After player 1's date it becomes 1, and after player 3's date it
becomes 1-4^(-(k+1)). Its maximum is exactly 1, already attained by quitting
at date 1.

These calculations cover every deterministic date and Never. Any randomized
or unbounded replacement law averages their payoffs and cannot exceed their
supremum. They therefore establish the unrestricted caps, not just local
or menu-restricted deviation bounds.

It follows that

    E_N(p)=J,             L_0(p)=J,             E(p)=J.

Given epsilon>0, choose

    K = max(1, ceil(log_8(1/epsilon))),          N=3K.

The single displayed product law satisfies both requested inequalities for
this reward table.

## 6. Exact infinite equilibrium and failure of exact projection

Letting the three cyclic clocks run forever gives independent stopping laws

    p_0(Never)=1,
    p_i(3k+i-1)=2^(-(k+1)) for every k>=0, i=1,2,3.

The same cap computation gives

    U=B=(2,0,1,0),

so this is an exact behavioral equilibrium. In particular, the table cannot
be a global positive-exploitability-gap counterexample.

For the finite approximate law with N=3K, player 1's finite support is
{0,3,...,3K-3}. For the unique exact finite-menu Nash law, player 1's finite
support is the singleton {3K-1}. Their only common support point is Never,
and their overlap mass there is 2^(-K). Therefore their total variation
distance is exactly

    1 - 2^(-K).

Thus approximate finite-menu equilibria with menu regret 8^(-K) can become
maximally far from the exact equilibrium set as the deadline grows. A
projection onto exact finite-menu equilibria cannot be inserted into a
selection proof without losing the late-defect control in this example.

## 7. A parameter family with any exact-selector gap below one

Keep the cyclic externalities of players 1,2,3 unchanged. Replace player 0's
reward when 0 is absent by any R>1, and replace each nonquitting zero-singleton
player's reward when 0 quits by -h, for any h>0. Player 0 still receives 1
whenever 0 belongs to the quitting coalition. The reward bound is
max(2,R,h).

The same row arguments apply. Set

    a_R = 1 - (1 - 1/R)^(1/3),
    b_R = a_R/(h+a_R).

For every deadline N, the unique exact menu Nash law waits until N-1 and
then uses quit probabilities (b_R,a_R,a_R,a_R). Its payoff is (1,0,0,0),
and its late defect is exactly

    L_0 = 1 - 1/R.

Thus the uniform exact-selector defect can be any prescribed value in
(0,1), not just 1/2.

The finite cyclic laws in Section 5 do not depend on R or h. With J=8^(-K)
their payoff and caps become

    U = (R(1-J), 0, 1-J, 0),
    B^N = (max(R(1-J), R-2(R-1)J), 0, 1, 0),
    B = (R-(R-1)J, 0, 1, 0).

Since R>1, the pivot's menu regret is max(0,2-R)J <= J, while player 2's
menu regret is exactly J. Hence still

    E_(3K) = L_0 = E = 8^(-K).

The infinite cyclic law is an exact behavioral equilibrium with payoff
(R,0,1,0). These parameter claims follow from the analytic proof; the
accompanying computation checks the displayed R=2,h=1 instance only.

## 8. Reproduction

Run:

    python check_example.py

The script uses exact fractions and evaluates every finite pure deviation,
Never, and the additional late deviation. It checks the displayed payoff
and cap vectors for K in {1,2,3,4,6}. The analytic arguments above establish
the results for all K and all N.

## Remaining general task

The universal construction for arbitrary reward entries satisfying only the
single-pivot singleton normalization is still not established here. The
proved separation rules out the universal exact-menu-Nash strengthening;
it neither rules out nor proves the requested approximate selector for all
tables.
