# Direct existence beyond temporalization

Author: CODEX_NASH_BOX.

Status: completed independent ordinary mathematical mechanism tests, not
Lean-checked or exported. Section 6's entire-correspondence limit-order
calculation has a bounded independent PASS by CODEX_TURING_BOX; Sections
2, 4 and 5 remain unreviewed ordinary proofs. No UE proof, positive-gap
game, or new exclusion from the possible-counterexample class is claimed.

Central conclusion: NONE of the no-go results below refutes existential
selection from the FULL private-Never-bonus equilibrium correspondence.
The same auxiliary games have rigorously bad exact selections and good
exact selections. Weak continuity of their compactified clock games fails,
but this does not prohibit the good selections. Section 6 calculates the
two limit orders for the entire correspondence and states the remaining
unproved sufficient theorem. The unrestricted approximate-selection
question is still broader than that auxiliary theorem.

The artificial restriction tested first is exact Nash selection on a common
finite clock menu, even after changing every terminal reward coordinate by a
small amount. The alternative permits approximate menu Nash and changes the
whole product law, without preserving source ancestry or a previous payoff.

## 1. Question and source boundary

Fix four players and real rewards r(S) for every nonempty quitting coalition.
Before termination, the sole public history is unanimous Continue. Independent
behavioral strategies are therefore independent laws on the nonnegative
integer dates together with Never. A unilateral deviation replaces a complete
law, including unbounded laws and Never. Never and preabsorption pay zero.

The desired construction, for every epsilon > 0, is an actual product law p
whose maximum unrestricted terminal deviation gain is at most epsilon. The
law and deadline may change with epsilon. No chronological relationship
between these profiles is required.

Source declarations inspected under their imports:

- `quittingUniformEquilibriumPayoffConjecture`, in
  `UniformEquilibrium/Quitting/Conjecture/Basic.lean`;
- `quittingGame_exists_terminalTargetAcceptance_of_terminalNash_family`,
  `quittingGame_exists_uniformEquilibriumPayoff_of_terminalNash_all_errors`,
  and `quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors`,
  in
  `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`;
- `HasTerminalExploitabilityGap` and
  `not_exists_uniformEquilibriumPayoff_iff_exists_terminalExploitabilityGap`,
  in `UniformEquilibrium/Quitting/Terminal/ExploitabilityGap.lean`.

The positive endpoint selects a fixed payoff from approximate terminal Nash
profiles. It does not require profiles to converge or nest. The negative
endpoint requires a positive gap against every actual behavioral profile.

I also inspected `quittingActualTerminalPayoffSet_eq_finiteCalendarPayoff`
and `isCompact_quittingActualTerminalPayoffSet`, in
`UniformEquilibrium/Quitting/Paths/FiniteCalendarPayoffClosure.lean`. These
preserve prescribed payoffs and do not preserve deviation caps.

The narrow no-go comparison used the existing notebooks
`CODEX_ROOT__PROOF_MECHANISM_DIVERSIFICATION.md`,
`CODEX_HILBERT__CANONICAL_PIVOT_BOUNDARY_HOMOTOPY.md`,
`CODEX_NOETHER_SUPPORT__GLOBAL_NEVER_BONUS_SELECTION_AND_DISCOUNT_STALL.md`,
and `CODEX_ROOT__CANONICAL_EXACT_MENU_OBSTRUCTION_SOURCE.md`.
The last contains the independently reviewed rational example used below.
The new calculation tests an arbitrary nearby terminal reward table, not one
specified boundary credit, discount, or private action bonus.

## 2. Arbitrary small terminal-table perturbations cannot repair exact menus

### Complete statement

Take players 0,1,2,3. The rewards to core players 0,1,2 depend only on the
nonempty core part T of the quitting coalition and are zero if T is empty:

| T | Core reward vector |
| --- | --- |
| {0} | (1,7,7) |
| {1} | (7,0,7) |
| {2} | (7,7,0) |
| {0,1} | (6,8,7) |
| {0,2} | (9,7,5) |
| {1,2} | (7,5,8) |
| {0,1,2} | (7,6,6) |

For player 3, the reward is -1 when 3 quits together with any core player,
1 when 3 is absent and some player in {1,2} quits, and zero otherwise.
Never pays zero. The own-singleton vector is (1,0,0,0), and every reward has
absolute value at most 9.

**Proposition.** Let 0 <= delta <= 1/1000. Let r' be any other complete
terminal reward table with |r'_i(S)-r_i(S)| <= delta for every i,S, still
paying zero at Never. At any N >= 1, every exact mixed Nash law of the
r'-game on the COMMON menu {0,...,N-1,Never} has the following form:

1. All players Continue at every date before N-1.
2. Player 3 chooses Never surely.
3. At N-1, the core Quit probabilities q satisfy
   |q_0-2/7| <= 2 delta, |q_1-4/7| <= 2 delta,
   |q_2-1/7| <= 2 delta.
4. Evaluated in the ORIGINAL r-game, its unrestricted pivot deviation gain
   is at least 18/49 - 6 delta > 1/3.

Every terminal entry may change, including own singletons and coalition
rewards involving the dummy. The perturbation can depend on N. The theorem
quantifies over all exact Nash selectors. It concerns no approximate selector
and no perturbation depending on the privately planned stopping action.

The same proof also permits a separate perturbed table r'_t at each finite
date, provided every entry remains within delta of r. In the proof below,
the 2 delta current-root comparison is applied to that date's table, and
the last-stage payoff floor propagates through earlier all-Continue rows.
Thus date dependence alone does not remove this obstruction. This extension
still concerns realized-terminal rewards, not privately planned actions.

### Root formulas and perturbation estimate

Use cyclic core indices modulo three and put g=(1,0,0). When player 3
Continues, the original Quit-minus-Continue gap against continuation v is

    Delta_i = g_i + q_(i-1) - 2 q_(i+1)
              - v_i (1-q_(i-1))(1-q_(i+1)).                 (2.1)

For arbitrary dummy probability q_3, replace v_i by (1-q_3)v_i in (2.1):
dummy-only termination gives each core coordinate zero. Holding v fixed,
changing r to r' changes each current Quit-minus-Continue gap by at most
2 delta. This follows by applying the uniform reward bound separately to
the two current pure actions; the common continuation term is unchanged.

Write H for the probability that at least one core player quits now and
b for the probability that at least one of players 1,2 quits now. Player
3's original root gap is

    Delta_3 = -H - b - (1-H)v_3.                           (2.2)

### Every reached date has positive unanimous-Continue probability

First no core player quits surely in an exact finite-menu Nash law. If any
core player does, current absorption is certain. Dummy Quit pays -1 in the
original table; dummy Continue pays 0 or 1. For r', Continue is strictly
better by at least 1-2 delta, so q_3=0.

If q_0=1, (2.1) gives Delta_2=q_1-2 <= -1, forcing q_2=0 even after
perturbation. Then Delta_1=1 forces q_1=1, after which Delta_0=-1
contradicts q_0=1. If q_2=1, similarly Delta_1=q_0-2 <= -1 forces
q_1=0; Delta_0=2 forces q_0=1; then Delta_2=-2 is a contradiction.

For q_1=1, every actual core continuation satisfies v_1 >= -delta:
all ORIGINAL core rewards and Never are nonnegative. The Nash inequality
for the surely quitting player 1 and the perturbation estimate yield

    0 <= Delta'_1 <= q_0-2q_2+3 delta,
    q_2 <= (1+3 delta)/2.

Player 0's gap is Delta_0=q_2-1, since player 1 surely quits. Thus
Delta'_0 <= -1/2 + (7/2)delta < 0, forcing q_0=0. Player 2 then has
Delta'_2 >= 1-2 delta > 0, forcing q_2=1, already excluded.

Nor can player 3 quit surely. Its prescribed payoff is at most -H+delta.
The complete Never deviation guarantees at least -delta, because original
rewards to a nonquitting dummy are nonnegative. Exact Nash therefore implies
H <= 2 delta. In particular q_1,q_2 <= 2 delta. Against q_3=1 the pivot's
original immediate gap is 1+q_2-2q_1 >= 1-4 delta, so its perturbed gap is
at least 1-6 delta > 0. This forces q_0=1 and contradicts H <= 2 delta.

Consequently every player Continues with positive probability at the first
date. The joint probability is positive by independence. Conditional tails
are exact Nash laws on the shorter common menu: any profitable complete
tail replacement would have its gain multiplied by the positive joint
prefix reach and remain profitable ex ante. Conditioning independent own
laws on own survival retains independence. Applying the same argument
successively proves that every finite suffix is reached and exact Nash.
No subgame-perfect selection is imposed off path.

### All one-date equilibria remain near the rational root

At the final date the continuation is zero. If q_3>0, (2.2) and exact Nash
give H+b <= 2 delta. Hence q_1,q_2 <= 2 delta, while the pivot has
Delta'_0 >= 1-6 delta > 0. This forces q_0=1, a contradiction. Thus
q_3=0.

The preceding argument gives q_i<1 for each core player. Their Nash
inequalities consequently imply Delta_i <= 2 delta. Successively,

    q_1 >= 1/2-delta,
    q_0 >= 1/4-(3/2)delta,
    q_2 >= 1/8-(7/4)delta.

All three probabilities are positive. They therefore mix, so their exact
perturbed gaps vanish. Write e_i=Delta'_i-Delta_i, with |e_i| <= 2 delta.
Solving the three ORIGINAL linear gaps gives

    q_0 = 2/7 + (2e_0+e_1+4e_2)/7,
    q_1 = 4/7 + (4e_0+2e_1+e_2)/7,
    q_2 = 1/7 + (e_0+4e_1+2e_2)/7.

Each displacement has absolute value at most 2 delta. This argument permits
any number of nearby perturbed equilibria; uniqueness is unnecessary.

At the unperturbed rational root the prescribed payoff is

    V = (31/7, 19/7, 34/7, 31/49).

Couple the three Bernoulli core actions at q and q*. Their total mismatch
probability is at most 6 delta. The reward bound 9 and the table difference
therefore give |V'_i-V_i| <= delta+18(6 delta)=109 delta. In particular

    V'_0,V'_1,V'_2 > 2,             V'_3 > 1/4.            (2.3)

### Entire earlier-root equilibrium set is all-Continue

Fix ANY continuation v satisfying (2.3). At every root, (2.2) is at most
-min(1,v_3) <= -1/4. The perturbed dummy gap is strictly negative, so q_3=0.

All-Continue is a strict root equilibrium: each core gap there is
g_i-v_i <= -1, and the dummy gap is at most -1/4, before errors of at most
2 delta. There are no other root equilibria, as the following exhaustive
support check shows.

- With one positive core hazard, its owner's original gap is g_i-v_i <= -1.
- With support {0,1}, player 0's gap is
  (1-q_1)(1-v_0)-q_1 <= -1.
- With support {0,2}, player 2's gap is
  -2q_0-v_2(1-q_0) <= -2.
- With support {1,2}, player 1 has the analogous bound at most -2.
- If every core hazard is positive, their original gaps satisfy

      sum_i Delta_i
        = 1-sum_i q_i-sum_i v_i(1-q_(i-1))(1-q_(i+1))
        <= -1.

  Here sum_i q_i+2 sum_i(1-q_(i-1))(1-q_(i+1)) >= 2. The expression is
  multi-affine on the cube; at vertices with 0,1,2,3 coordinates equal to
  one its values are respectively 6,3,2,3. Adding the three perturbation
  errors changes the sum by at most 6 delta < 1. Exact Nash at positive
  hazards would require each perturbed gap to be nonnegative, impossible.

Thus the WHOLE root Nash set is the singleton all-Continue throughout (2.3),
not merely a neighborhood in which all-Continue remains strict. Backward
induction from the final payoff V' now forces all earlier dates to Continue
and preserves V' as their continuation. This step is uniform in N.

### Original unrestricted regret stays positive

Evaluate the selected law in r. Write U_0 for its prescribed payoff and W_0
for the pivot's Never response. Since only the final date has finite mass,

    U_0-W_0 = q_0 Delta_0(q;0),
    |Delta_0(q;0)| <= 2 delta.

The original deleted-opponent Never product is
D_0=(1-q_1)(1-q_2). Its difference from 18/49 is at most
|q_1-4/7|+|q_2-1/7| <= 4 delta. Quitting at any date after the menu gives
the pivot W_0+D_0, hence its improvement is

    W_0+D_0-U_0 >= 18/49-6 delta > 1/3.

This is one legal pure finite deviation, so it already lower-bounds full
behavioral exploitability. QED.

### Scope and next mechanism

The example itself already has a geometric approximate-menu bypass, recorded
in the reviewed source notebook. Therefore this is not a positive-gap game.
The proposition only strengthens the exact-selector falsifier to every small
terminal-table perturbation simultaneously. It should prevent treating global
terminal perturbation as a repair of the exact-selection restriction.

Private planned-action transfers and genuinely approximate Nash laws evade
the theorem's hypotheses. The next concrete test is whether a direct
approximate-response construction can exploit this freedom without demanding
near-fixity of the entire stopping-law vector or adding public correlation.

## 3. Bounded primary-literature check

The primary article *The APS approach for undiscounted quitting games*,
Ashkenazi-Golan, Krasikov, Rainer and Solan, International Journal of Game
Theory 55, article 19 (published 2 April 2026), was inspected at
<https://link.springer.com/article/10.1007/s00182-026-00982-6>.
Sections 1–2 explicitly restrict the characterized payoff set to Flesch
absorption paths with one continuous quitting owner at each time; the set
may be empty, and extension to general absorption paths is left open.
It therefore supplies no arbitrary-table existence theorem for this route.
The paper normalizes own-singleton rewards to zero and assumes negative
Never rewards, unlike the project's fixed zero-Never convention; no silent
adapter between those models is used here.

## 4. Private Never bonuses: exact identities and a global-selection test

This is a different auxiliary normal-form game. On the common finite menu
F_N, player i receives the original terminal payoff PLUS b_i if its own
privately planned stopping clock is Never. The bonus is paid even when
another player terminates the game earlier. It is not an all-Never terminal
credit and is not a nearby quitting reward table.

In the canonical own-singleton case (1,0,0,0), take b_0=0 and
0 <= b_i <= delta for the other players. If p is an exact Nash product law
of this auxiliary finite game, then every original menu deviation gain for
player i is at most b_i. For nonpivots, the unrestricted original cap equals
the menu cap: every pure clock beyond the menu has the same value as Never,
because its own singleton is zero. The pivot's original menu debt is zero.
Consequently

    original full exploitability <= max(delta, max(0,L_0)),
    L_0 = W_0 + D_0 - U_0,

where D_0 is the product of nonpivot Never masses and W_0 is the ORIGINAL
Never response. This uses the actual unused-Never slack U_0-W_0. Small D_0
alone is neither the defined objective nor a necessary condition.

### Conditional-tail and prepend transport

Write S_i(t) for the marginal survival probability of player i to date t,
and assume all these probabilities are positive. The conditional tail of
an exact auxiliary Nash law is an exact auxiliary Nash law with bonuses

    b_i^(t) = b_i / product_{j != i} S_j(t).

Indeed a tail terminal-payoff gain is multiplied ex ante by joint survival,
whereas changing the planned-Never probability changes the bonus only on
that player's own survival event. Dividing the complete deviation inequality
by joint survival gives the formula. Conditioning preserves independence.

Conversely, let a tail auxiliary Nash law have original payoff u, Never
masses z_i and bonuses b_i. Set v_i=u_i+b_i z_i. Prepend a usual one-shot
Nash root q against continuation v, and put a_i=1-q_i. The prefixed law is
auxiliary Nash with bonuses

    b'_i = b_i product_{j != i} a_j.

For a player continuing at the root, its original continuation contribution
plus the new bonus is

    product_{j != i} a_j * u_i + b'_i z_i
      = product_{j != i} a_j * (u_i+b_i z_i).

Immediate quitting has no planned-Never bonus. General finite deviations
decompose into their current choice and conditional tail, proving the full
claim, not just a comparison of current hazards. The prefixed augmented
payoff is exactly the ordinary root Bellman payoff against v.

These identities do NOT construct a good equilibrium of the global
auxiliary game. They show that reducing bonuses by independently prepending
exact roots is ordinary Nash--Bellman recursion in AUGMENTED payoffs. It
would be a mistake to rename this local recursion a new direct existence
mechanism. Selection over the entire finite-game equilibrium correspondence
remains mathematically distinct and is the question tested next.

### Exact successful calibration on the robust falsifier

On Section 2's rational table, let pivot 0 be uniform on
{0,...,N-1} and all other players choose Never. Original payoffs are
(1,7,7,0). Player 1's response at a date 0 <= t < N is (7t+8)/N,
with maximum 7+1/N; its Never response is 7. Player 2's response is
(7t+5)/N, at most 7, and its Never response is 7. Player 3's finite response
is -1/N, at most its Never value zero. Every pivot response pays at most 1.
Thus the full original regret is exactly 1/N, solely at player 1.

Give player 1 the private Never bonus b_1=1/N, and give the other two
nonpivots any nonnegative bonuses. The same law is EXACT auxiliary Nash.
This is a completely explicit sequence that escapes Section 2, using a
joint law change and a planned-action transfer. It is already in the
solo-Q class of the existing global-bonus notebook, not a new class.

### A cyclic calibration with two equal vanishing bonuses

For the cyclic table in
`CODEX_HILBERT__CANONICAL_PIVOT_BOUNDARY_HOMOTOPY.md`, the solo-pivot
family cannot be approximately equilibrated. Player 2's reward at {0} is
-1 and its reward at {0,2} is zero. Against every proper solo-pivot law,
its prescribed Never value is -1 while quitting at date zero pays zero.
Thus the preceding solo-pivot calibration does not apply.
The following direct finite construction nevertheless works. It tests a
common positive bonus for both active nonpivots; it is not a new UE claim
for that already-solved table.

Explicitly, for nonempty S and i=0,1,2, with g=(1,0,0) and predecessor
p=i-1 modulo three, this table is

    r_i(S) = g_i-1 + 3*1_{p in S} + 1_{i in S}
               - 2*1_{i in S}*1_{p in S},
    r_3(S) = 1_{3 not in S}.

Never pays zero, independently of these nonempty-coalition formulas.

Let T=3K, K >= 1. At date t only player t modulo 3 may Quit, with probability
h_t. Put h_T=1 and h_(T-1)=x, where 2/3 < x < 1. For t <= T-2 define

    h_t = 2(1-h_t)h_(t+1),
    h_t = 2^k x / [2^(k+1)x+1-2x],   k=T-1-t.

Every earlier hazard lies strictly between 1/2 and 1. Player 3 always
Continues. The pivot is proper because h_T=1.

For i=0,1,2, let F_i(t) denote the original payoff from choosing pure clock
t. At an own date, F_i is a local peak; the following successor date has
the same value. Across a successor date s followed by a predecessor date,
the difference between consecutive own-date peaks is

    S_-i(s) [-h_s + 2(1-h_s)h_(s+1)].

This is zero wherever the displayed recurrence holds. The intervening
predecessor date is below the peak, because its one-step difference is
S_-i(s)[-h_s+(1-h_s)h_(s+1)]=-S_-i(s)h_s/2.
These formulas follow directly from this table's singleton/tie values:
at an opponent successor absorption waiting loses 1, at predecessor
absorption waiting gains 2 relative to tying. They check every finite pure
response, not only the support.

All pivot peaks equal 1, including every pure clock after T. Its Never
value is 1-D_0 <= 1. Player 1's peaks equal 2h_0. At its final successor
date T-1 the recurrence need not hold, and its Never response falls below
the peak by

    b_1 = S_-1(T-1)(3x-2).

Player 2's peaks equal zero, and its Never response is below zero by

    b_2 = S_-2(T).

The remaining late finite responses do not exceed these peaks. Giving
players 1 and 2 exactly these private Never bonuses makes every used
action, including Never, optimal. Pivot and dummy need no bonus. Hence
the entire law is exact auxiliary Nash on F_(T+1).

For completeness, equal bonuses can be selected without assuming an
unknown equilibrium. Write d_k=2^k x+1-2x and a(k)=d_k/d_(k+1). Then

    b_1/b_2 = (3x-2)
      * [product_{l=1}^{K-1} a(3l)]
      / [product_{l=0}^{K-1} a(3l+1)].

This ratio is continuous on [2/3,1], is zero at 2/3, and exceeds one at 1.
For the last claim, a(k) is strictly increasing at x=1. Pair the numerator
factor a(3l) with a(3l-2), the first K-1 denominator factors. Each ratio
exceeds one, and the remaining denominator factor is less than one.
The intermediate value theorem supplies x_K in (2/3,1) with
b_1=b_2=delta_K. Since every preterminal Continue mass is below 1/2,

    0 < delta_K <= 2^(-2K),
    original debt_i = b_i z_i <= 2^(-3K),  i=1,2,

and pivot/dummy original debts vanish. Therefore common bonus levels
delta_K tend to zero along explicit finite laws with full regret tending
to zero. This does NOT assert the construction at every prescribed bonus
level, in particular not at the restricted choice delta=1/N.

### What the global test has and has not established

The universal exact terminal-perturbation selector is falsified. The global
private-Never-bonus selector is NOT falsified by these examples: both admit
exact auxiliary Nash laws with small ACTUAL full regret. The local bonus
transport formula supplies no producer beyond existing exact-root recursion.
No argument here guarantees, for arbitrary canonical tables, a finite menu
and small bonuses whose auxiliary Nash correspondence meets small L_0.
That missing global selection statement is the genuine remaining gap; the
successful calibrations should not be substituted for it.

## 5. Exact failure of a compact discontinuous-game theorem for the BONUS game

The preceding positive test does not establish that a standard compact-game
existence theorem applies. A concrete attempted implication was:

    positive private Never bonuses for all nonpivots
      => weak transfer quasi-continuity of the compact mixed clock game
      => existence by a discontinuous-game Nash theorem.

The first implication is false, even on Section 2's solved table. This is a
failure of a specified topological mechanism, NOT a failure of existential
global auxiliary-Nash selection.

### Exact bad branch for any fixed small bonus vector

Fix b_0=0 and 0 <= b_1,b_2,b_3 <= 1/1000. At every common deadline N, let
all players Continue before N-1, let player 3 choose Never, and put final
core hazards

    q_0 = 2/7-(b_1+4b_2)/7,
    q_1 = 4/7-(2b_1+b_2)/7,
    q_2 = 1/7-(4b_1+2b_2)/7.

Every core hazard is interior. Substitution gives original final gaps
(0,b_1,b_2), so the auxiliary gaps after subtracting the private bonuses
are exactly zero. Dummy Never is strictly best. The common augmented
values of each core player's final Quit and Never are

    V_0 = 7[1-(1-q_1)(1-q_2)],
    V_1 = 7[1-(1-q_0)(1-q_2)] + b_1,
    V_2 = 7[1-(1-q_0)(1-q_1)] + b_2.

The dummy's value is V_3=1-(1-q_1)(1-q_2)+b_3. Each V_i is strictly above
its own singleton s_i, uniformly in these small bonuses. Any earlier finite
pure clock pays only s_i and receives no bonus, hence is strictly worse.
This proves exact Nash of the WHOLE finite auxiliary normal form. No
off-path or Markov restriction was imposed.

Equip laws on the one-point compactification of the dates with weak
convergence. These Nash profiles p^N converge to all-Never as N tends to
infinity. At all-Never, the pivot receives zero and can obtain one by
quitting immediately. The limit is therefore not equilibrium of the
auxiliary infinite clock game.

More strongly, fix ANY profile y of proposed unilateral deviation laws,
allowing each y_i to have arbitrary unbounded support. For nonpivots, every
finite pure clock after N-1 pays its original Never value V_i-b_i <= V_i;
every earlier clock pays s_i < V_i; and Never pays V_i. Thus y_i's gain
against p^N is nonpositive for every N. The same assertion holds for the
dummy. For the pivot put D=(1-q_1)(1-q_2)>0. Its gain is exactly

    (1-V_0) y_0({0,...,N-2})
      + D y_0({N,N+1,...}).

If y_0 has positive finite-clock mass alpha, this tends to
(1-V_0)alpha < 0. If y_0=Never, it is identically zero. Consequently, for
every fixed deviation PROFILE y, all players' gains are nonpositive along
all sufficiently large N. There is no neighborhood of all-Never and fixed
deviation profile that gives some player a strict gain throughout that
neighborhood.

This directly falsifies weak transfer quasi-continuity, including its
player-changing quantifier. It is stronger than merely observing a payoff
graph discontinuity or failure of payoff security. The check covers
unrestricted behavioral deviations, not just fixed finite dates.

### Precise paper boundary

I inspected Definitions 3.1 and 3.3 and Theorems 3.1 and 3.2 of Nessah and
Tian, *Existence of Equilibrium in Discontinuous Games*, March 2010 author
version, <https://people.tamu.edu/~gtian/nash-equilibria-nessah-tian-2010-03.pdf>.
Theorem 3.1 requires weak transfer quasi-continuity and strong diagonal
transfer quasiconcavity. Theorem 3.2 instead requires weak transfer
continuity, along with compactness, convexity, boundedness and ordinary
own quasiconcavity. The former continuity property is explicitly refuted
above; the latter is stronger and therefore also refuted. No applicability
claim or substitute theorem is inferred from the paper's abstract.

### Why this is NOT an obstruction to the global existential selector

Fix b_1>0 and any b_2,b_3 >= 0 in the same box. For every N with
1/N <= b_1, Section 4's uniform-pivot profile is exact Nash of the SAME
finite auxiliary game, and has original full regret 1/N. Thus its COMPLETE
equilibrium correspondence contains both the bad branch above and a good
branch. Failure of compact weak transfer continuity, or convergence of a
bad branch to a nonequilibrium point, cannot refute existence of a good
selector from that complete correspondence.

The global problem remains genuinely unproved here: from arbitrary
canonical game data, produce vanishing small bonuses and menus on which
some auxiliary equilibrium has small actual L_0. None of Sections 2 or 5
rules that out. A proof needs an additional global argument, not the invalid
weak-continuity implication and not the local augmented-payoff NB identity.

## 6. Entire-correspondence calculation and final research verdict

### Joint scale is essential even for the full bonus correspondence

For Section 2's rational table define

    M_N(delta) = min full-original-exploitability(p),

where the minimum ranges over ALL bonus vectors
(0,b_1,b_2,b_3), 0 <= b_i <= delta, and ALL exact Nash product laws p
of the corresponding finite auxiliary game on F_N. This is not selection
of a single bad branch. The minimum exists: the parameter/profile domain
is compact, the finite-game Nash graph is closed, and full original
exploitability is continuous on this finite simplex. The latter is a finite
maximum, including the pivot's one omitted late value.

The feasible set is nonempty for every bonus vector by the ordinary finite
mixed Nash theorem, so there is no hidden supplied-equilibrium hypothesis.

For every FIXED N,

    lim_(delta down to 0) M_N(delta) = 18/49.

Proof: any convergent sequence of minimizing profiles for vanishing bonuses
limits to an exact ORIGINAL finite-menu Nash law. Section 2 at delta=0
shows that law is uniquely all-Continue until the final q* root, whose full
gap is 18/49. Compactness gives the lower limit, and including the zero
bonus vector gives the opposite upper bound.

But for every FIXED delta > 0,

    inf_(N >= 1) M_N(delta) = 0.

Indeed choose N with 1/N <= delta, use the uniform-pivot profile, and choose
b_1=1/N,b_2=b_3=0. Its full original gap is 1/N. Therefore

    lim_(delta down to 0) inf_N M_N(delta) = 0,
    inf_N lim_(delta down to 0) M_N(delta) = 18/49.

The limit-order difference concerns the ENTIRE auxiliary equilibrium
correspondence and an actual full-regret objective. Freezing the menu and
then removing perturbations is not a valid test of joint menu/bonus
selection. This exact calculation does not claim the first limit is zero
for arbitrary tables.

### Exact remaining sufficient theorem, not a new universal restriction

One genuinely global positive idea was to lower common private bonuses
from a value B > 2R. At that upper value Never strictly dominates every
finite clock for all nonpivots, so the complete auxiliary Nash set is
nonpivots Never and pivot an arbitrary proper finite law. It has L_0=0.
However the direct family on this upper face does not generally extend to
small bonuses. If the pivot is uniform on N dates, put
k_i=r_i({0}) and v_i=r_i({0,i}) for a nonpivot. Its finite pure response is
(k_i t+v_i)/N and its original Never value is k_i. Therefore the required
Never bonus for this family is at least v_i/N-k_i when k_i<0. On the cyclic
fixture player 2 has k_2=-1,v_2=0, requiring b_2 >= 1, even though
Section 4 supplies genuinely multiplayer auxiliary equilibria at bonuses
delta_K tending to zero. Thus this attempted downward homotopy needs a
global transition to other equilibrium laws; neither large-bonus Nash
existence nor the directly computable solo branch supplies that transition.
No topological connection theorem or bound on its crossing scale is proved
here, and this calculation does not obstruct the complete correspondence.

Read `questions/FIN4_SINGLE_PIVOT_FINITE_MENU_SELECTION.md`: its original
question permits arbitrary independent approximate products, simultaneous
choice of deadline and accuracy, and no inter-accuracy nesting. It asks
for E_N <= epsilon and L_0 <= epsilon on the SAME law.

A sufficient private-bonus theorem would be the following, currently
UNPROVED here:

    For every canonical four-player reward table and epsilon > 0,
    there exist N, bonuses b_0=0 and 0 <= b_i <= epsilon (i != 0),
    and an exact auxiliary finite-game Nash law p with L_0(p) <= epsilon.

Section 4 would then give original full exploitability at most epsilon,
and the inspected terminal-all-errors theorem would give UE. The sufficient
theorem is stronger than the original question: not every approximate
product is asserted to admit exactification by bonuses ONLY at Never.
There is no proved completeness/WLOG reduction to that auxiliary class.
Even a future counterexample to this auxiliary theorem would NOT be a
negative answer to the original unrestricted approximate-selection question.

### What survives the hour's tests

The artificial restriction actually falsified is exact common-menu Nash
after arbitrary small realized-terminal reward perturbations. The fully
proved, uniform-in-deadline consequence is Section 2's original gain > 1/3
on one solved table; allowing date-dependent realized rewards does not
repair it. This is architectural evidence, not a new UE class.

The concrete alternative tested is exact Nash of a genuinely different
normal-form game, with private planned-Never bonuses. Exact constructions
show it admits good selections on both the robust rational example and a
non-solo-Q cyclic example. Local bonus scaling reduces to augmented-payoff
Nash--Bellman transport, while a proposed standard discontinuous-game
existence proof fails its actual weak-continuity hypothesis. Neither fact
decides the GLOBAL selection problem. The full-correspondence limit-order
calculation shows precisely why fixed-menu perturbation failure is not an
obstruction to choosing menu and bonus together.

Concrete next question: can a global equilibrium-correspondence argument
prove the displayed sufficient theorem for arbitrary canonical data,
using the actual L_0 including unused-Never slack? No exact temporal ancestry
is needed, and the inspected all-errors endpoint allows new laws and
deadlines at every accuracy. Recommendation: retain that genuinely global
problem as open and viable; do not infer a no-go from bad branches, compact
weak-continuity failure, or the exact-root bonus transport identity.

All displayed cyclic finite-response equalities were checked
by exact rational enumeration at x=3/4 for K=1,...,5; this is a computation
check of the written ordinary proof, not a Lean check. No Lean files, shared
indexes, or exports were modified. No staging, committing, or pushing was
performed in this work.

Independent review incorporated: CODEX_TURING_BOX checked Section 6's
entire-correspondence M_N definition, nonempty compact feasible set,
full-cap objective, zero-bonus finite-equilibrium classification used by the
fixed-N limit, and uniform-pivot joint-scale witness. The review found no
objection in that bounded scope; see
`feedback/CODEX_NASH_BOX__DIRECT_EXISTENCE_BEYOND_TEMPORALIZATION__BY_CODEX_TURING_BOX.md`.
It did not review the arbitrary reward-perturbation proposition, private
bonus transport, cyclic calibration, or discontinuous-game source audit.
