# Direct existence beyond temporalization

Author: CODEX_NASH_BOX.

Status: active independent research, resumed 2026-10-11. Section 8 now gives
a positive candidate independently checked for soundness: sufficiently large pair-participation
rewards near the hard paired singleton matrix produce proper stationary
exact terminal Nash, uniformly over bounded arbitrary remaining coordinates.
The rescaled limiting equations have an explicit positive nonsingular root.
An exact family has no pure-clock equilibrium and fails every proper
nonnegative quiet-child join test, BUT CODEX_EMMY_BOX found it is covered
by an existing persistent-base source. Section 9 explains much broader
generic containment and a failed separation attempt. Section 10 records
a global degree replacement for the local nonsingular-root producer;
its proof remains unreviewed and it does not yet supply new coverage.
No strict-new-coverage claim is made.
All arguments are ordinary mathematics, not Lean-checked or exported.
Section 7 gives a genuinely
different global cap-minimization/minimax producer for affine opposed-team
games, but a complete singleton-matrix check places that whole class inside
existing abnormal/non-Q coverage. It therefore supplies NO NEW TABLE CLASS.
Section 6's entire-correspondence limit-order
calculation has a bounded independent PASS by CODEX_TURING_BOX; Sections
2, 4 and 5 remain unreviewed ordinary proofs. No unrestricted UE proof or
positive-gap game is claimed.

Section 12 is an independently reviewed original-table singleton-calendar producer,
not a large-pair rescaling. It gives an explicit golden-ratio exact Nash
calendar, a nonzero four-variable Jacobian, and a full raw neighborhood with
upper-only joining entries and arbitrary unused entries. Its concrete
completion survives the bounded named source screens below, including the
WHOLE balanced-singleton certificate class and WHOLE persistent-base/free
selection. The canonical self-contained packet is now
[`FOUR_SINGLETON_PHASE_UNIFORM_EQUILIBRIUM.md`](../exports/FOUR_SINGLETON_PHASE_UNIFORM_EQUILIBRIUM.md).
CODEX_TURING_BOX and CODEX_EMMY_BOX independently checked soundness and the
bounded source screens; the assembled packet also passed transcription
review. This is reviewed ordinary mathematics, NOT Lean-implemented. No
completeness over all existing supplied-object verifiers is claimed. The
packet, rather than this exploratory section, is canonical. Global
nonstationary selection remains the independent research lane.

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

## 7. Resumed research: a global cap-minimizer producer, already-covered class

### Preliminary coverage checks

Two initially plausible constructions were stopped at exact overlap checks.
Full-cap common-quantile clock compression is already implemented in
`UniformEquilibrium/Quitting/Paths/CommonQuantileClockTransport.lean`; a
bounded calendar search alone cannot show its minimum regret is zero.

A weighted-observer lift with old participating rewards nonnegative, the
observer's participating rewards nonpositive, and its passive payoff above
a nonnegative combination of old payoff rows implies the existing advancing-
only F/J certificate. The more general portfolio sandwich independently
tested by CODEX_EMMY_BOX has the same overlap: Q(empty)=N, N-P(A)=F, and
Q(A)-P(A)=J, literally in `CappedClockParentRewardCertificate` from
`Classification/QuietExtension/CappedClockPointwiseDomination.lean`.
My bounded independent check is in
`feedback/CODEX_EMMY_BOX__PORTFOLIO_MIMICRY_PLAYER_ELIMINATION__BY_CODEX_NASH_BOX.md`.
Neither lift is new coverage.

### A complete ordinary positive mechanism

This proof is unreviewed ordinary mathematics. It is not a general Fin4
producer. Its purpose is to test an actual global optimization argument,
with jointly changing laws, rather than another exact-selection restriction.

Let there be one distinguished maximizer 0 and m other players J. Let the
finite terminal payoff table to 0 be g(S), with g({0})>=0 and zero Never.
For each i in J suppose a_i>0 and b_i are constants such that on EVERY
nonempty coalition,

    r_0(S)=g(S),       r_i(S)=b_i-a_i g(S).                (A)

Never still gives each player zero, not b_i. We claim this game has actual
terminal approximate Nash profiles for every positive accuracy, and hence
one ordinary uniform-equilibrium payoff. The chosen maximizer law will be
finitely supported on finite dates and will have no Never atom. This makes
the constants b_i strategically inert for every other player's deviation.

Write X for the product of the m compact stopping-law spaces on the
one-point compactification of the nonnegative integers. These are actual
countably additive laws, not relaxed correlated laws. Compactness and the
PMF bridge are supplied by the construction in
`MathUE/ProbabilityMassFunction/CompactStoppingLaw.lean`.
For x in X and each finite date t, define

    C_t(x)=E[g(first coalition) | player 0 uses pure date t].

The game surely ends by t. Thus C_t depends only on the finitely many
marginal masses at dates <=t and the complementary masses; it is a bounded,
continuous, separately affine function on X. Fix |g(S)|<=R, R>=0.

Let W(x) be player 0's Never payoff and D(x) the product of opponents'
Never atoms. Bounded convergence of the actual finite-time outcome gives

    lim_(t->infinity) C_t(x) = W(x)+g({0})D(x) >= W(x).

Consequently its FULL unrestricted response cap is

    F(x)=sup_(finite t) C_t(x),                          (B)

including Never and every behavioral mixture. The supremum of continuous
functions is lower semicontinuous. Hence F attains its global minimum v at
one actual product x*. This does not assert continuity of Never payoff.

The key selection step obtains a finite mixture of near-maximizing dates
which is simultaneously safe against every independent opponent replacement.
For a tuple y=(y_i) of arbitrary replacement laws, put

    A_t(y)=sum_(i in J) [C_t(x* with i replaced by y_i)-C_t(x*)].

Let x_h have coordinates (1-h)x_i*+h y_i. Multiaffinity gives, uniformly in
ALL t and y,

    C_t(x_h)=C_t(x*)+h A_t(y)+e_t,
    |e_t| <= K_m R h^2,      K_m=3^m-1-2m,  0<=h<=1.    (C)

Indeed the exact finite-difference expansion has a subset-S coefficient
bounded by 2^|S| R; the terms of size at least two total at most
sum_(k=2)^m binom(m,k)2^k R h^2. For m=3 this is 20R h^2.
Also |A_t(y)|<=2mR.

Fix eta>0. For sufficiently small h>0, global minimality F(x_h)>=v and
a date t within h^2 of the supremum F(x_h) imply

    C_t(x*) >= v-eta,       A_t(y) >= -eta/2.            (D)

Explicitly, (C) implies
v-C_t(x*) <=2mRh+(K_m R+1)h^2 and
A_t(y)>=(v-C_t(x*))/h-(K_m R+1)h >=-(K_m R+1)h.
Choose h so both displayed errors are below eta and eta/2, respectively.

Let I_eta={t:C_t(x*)>=v-eta}. For each y, (D) gives some t in I_eta with
A_t(y)>-eta. Each A_t is continuous in y. These open tests cover the compact
product X, so finitely many dates t in I_eta already cover it. Write T for
that finite set. Thus

    inf_y max_(t in T) A_t(y) >= -eta.                  (E)

This is a genuine finite zero-sum minimax problem: if L=max T, every test
depends only on each y_i's masses at dates <=L and the remaining mass.
Its minimizing domain is a product of finite simplices; A_t is affine on
that product (a sum of single-coordinate affine functions). Finite minimax
therefore gives one probability vector pi on T satisfying

    sum_(t in T) pi_t A_t(y) >= -eta   for EVERY y.      (F)

No convex combination of independently played profiles is being rounded.
The only mixture chosen by minimax is player 0's own legal stopping law pi.

Use that pi and retain the actual independent opponent laws x*. Player 0's
prescribed payoff lies in [v-eta,v], whereas its full cap is v. Its debt is
at most eta. In (F), set every replacement except coordinate i equal to
x_j*. All other summands then vanish, so

    U_0(pi,x* with i replaced by y_i)-U_0(pi,x*) >=-eta.

Because pi surely quits at a finite date, both games end surely regardless
of y_i. Equation (A) then gives i's gain at most a_i eta. Hence

    E_r(pi,x*) <= eta max(1,max_i a_i).                 (G)

This covers every complete behavioral deviation, not merely the finite
test calendar. The opponent laws may be censored at a sufficiently large
finite cutoff: their total removed finite-tail marginal mass tends to
zero, and the usual product coupling changes full regrets by at most four
times the original reward bound times that mass. Thus (G) also supplies
actual finite menus. The all-errors terminal endpoint selects one fixed
uniform-equilibrium payoff.

Important features: only the RESPONSE CAP F is minimized; all opponent laws
may change together. Global minimality supplies the common near-active
costate pi. No source ancestry, exact menu equilibrium, Nash--Bellman root,
private Never bonus, or profile-independent positive debt step is used.
The construction permits arbitrary simultaneous coalition rewards subject
to (A); no diffusion assumption is imposed on player 0.

### Why this class is already covered in canonical Fin4

Assume own singletons (1,0,0,0), let c_i=g({i}) for i=1,2,3, and write
c_0=1. Condition (A) forces b_i=a_i c_i. The normalized singleton matrix is

    M_0j=c_j-1,             j!=0;
    M_ij=a_i(c_i-c_j),      i!=0, all j;
    M_00=0.

If every c_i>=1, player 0's solo row weakly dominates every other player's
own singleton: r_i({0})=a_i(c_i-1)>=0. Letting only player 0 quit with a
small proper hazard is the existing solo-owner producer, irrespective of
all nonsingleton rewards. The exact full-behavior pair-premium bound is
`quittingTerminalPayoff_update_solo_other_le_pairPremium` in
`Classification/Existence/AcyclicSoloPreemption.lean`.

Otherwise choose a least-c nonpivot k, with c_k<1. Players 0 and k retain
strictly negative mutual entries, so both survive every normality layer.
Moreover row k is entrywise nonpositive on the FULL matrix, because
c_k<1 and c_k<=c_j for every nonpivot j. It remains entrywise nonpositive
on the actual nonempty core. At standard LCP offset equal to minus one,
its residual is always negative for every nonnegative vector. Thus the
actual core matrix is NOT standard Q. If it has a homogeneous simplex
solution, that existing positive branch applies; otherwise it lies in
`OrdinaryNonQMatrixBranch`. The inspected consumer
`exists_uniformEquilibriumPayoff_of_ordinaryNonQMatrixBranch` in
`Classification/LCP/OrdinaryNonQClosure.lean` already covers this class,
after the existing homogeneous/non-Q dispatch, and supplies stationary
approximate equilibria.

Correction retained explicitly: an earlier informal coverage calculation
described the core as precisely {0} plus the c_i<1 players. That is false
on ties. The actual inspected `normalLayer` definition in
`Classification/LCP/NormalCore.lean` uses a DISTINCT NONPOSITIVE witness,
not a strictly negative witness. Zero comparisons may retain extra players.
The least-c-row argument above avoids any incorrect exact-core assertion.

The exact anti-aligned case b_i=0 is even simpler: c_i=0, the full matrix
is entrywise nonpositive, with strict negative edges from and to player 0.
Here every player survives; Mz>=0 forces all nonpivot coordinates to zero
by row 0, then forces z_0=0 by any nonpivot row. There is no nonzero
homogeneous solution, so this case lies directly in OrdinaryNonQMatrixBranch.

Verdict: (B)--(G) are a genuinely different complete positive mechanism,
but not a new table-class theorem beyond the current frontier. No export
or independent export review is requested for this already-covered class.
The meaningful next question is whether the common-costate selection step
can control actual nonpivot incentives in a standard-Q class without merely
assuming global affine anti-alignment. No such extension is proved here.

### Unconditional source lemma surviving the class overlap

Steps (B) and compact minimization do not require (A). For ANY finite quitting
table and any owner whose own singleton is nonnegative, its full response cap
against actual independent opponent laws is lower semicontinuous on their
compact stopping-law product. Therefore its committed-plan punishment value
is attained by an ACTUAL independent opponent profile. The bridge is not an
attained best-response supremum: the owner's best reply may still only be
approached by finite dates tending to infinity when its singleton is positive.

The distinction matters. It is the opponents' infimum that is attained.
The proof uses precisely the finite-cylinder continuity and the inequality
Never<=lim finite dates. A negative own singleton would reverse the useful
inequality and does not satisfy this argument. The result does not prescribe
the opponent profile's payoffs, make the opponents mutually best-responding,
give a shared punishment for different owners, or eliminate any Fin4 table.

I inspected the approximate shared-floor statements in
`Quitting/Punishment/SharedPunishment.lean` and located actual finite-menu
attainment in `Quitting/Punishment/FiniteMenuPunishmentValue.lean` and the
scalar finite-root recursion. I did not find this infinite-clock actual
attainment statement in that narrow subtree search. That search is not a
proof of implementation novelty; no export is proposed for this source lemma.

## 8. Collision-dominated stationary selection: a positive asymptotic source

### Complete raw statement and current status

This is an ordinary proof candidate independently checked in bounded scope
by CODEX_TURING_BOX, not Lean-checked. It is a producer from raw
reward restrictions, not a hypothesis supplying a stationary root, response
values, or a certificate. Independent proof and existing-source coverage
checks are needed before any export or strict-new-coverage claim.

Let I={0,1,2,3}, Never payoff zero, and let the four reference singleton
vectors be

    r^0(0)=(1,4,0,0),       r^0(1)=(4,1,0,0),
    r^0(2)=(0,0,1,4),       r^0(3)=(0,0,4,1).

Thus the literal singleton comparison matrix is

    Gamma=[0,3,-1,-1; 3,0,-1,-1;
           -1,-1,0,3; -1,-1,3,0].                     (S1)

**Candidate theorem.** For every finite R>=0 there are delta>0 and M0>0
such that EVERY real table satisfying the following restrictions, for ANY
M>M0, has an exact stationary terminal Nash profile against all behavioral
replacements and one fixed original-game uniform equilibrium payoff:

1. All sixteen singleton coordinates are within delta of r^0.
2. For each two-player coalition A and each i in A,
   r_i(A)=M+c_i(A), with |c_i(A)|<=R.
3. Every nonsingleton coordinate not specified in item 2 has absolute
   value at most R.

There is no relation between the bounded coordinates. In particular all
twelve pair residuals c, twelve pair passive rewards, sixteen triple
rewards, and four grand rewards may vary independently. For an interior
choice of these bounds this is a full sixty-coordinate raw open class,
not a strategy-defined neighborhood. The theorem is asymmetric in scale:
pair participant rewards grow like M, the other nonsingleton coordinates
remain bounded. It does not transport any equilibrium back to an arbitrary
unmodified reward table.

The produced hazards have the form

    q_i=z_i/M,       1/18<z_i<1/6.                     (S2)

At the limiting reference singletons, z_i tends to 1/9. For each fixed
table these rates are proper and constant across dates; the resulting
independent geometric clocks are legitimate original-game behavior.

### Exact stationary owner equations

For arbitrary q in (0,1)^4, write p_i(A) for the product probability that
exactly coalition A of I−{i} quits at a live date. Set

    alpha_i=p_i(empty),
    Q_i=sum_(A subset I-i) p_i(A) r_i(A+i),
    B_i=sum_(nonempty A subset I-i) p_i(A) r_i(A).

The actual stationary prescribed value is

    U_i=[q_i Q_i+(1-q_i)B_i]/[1-(1-q_i)alpha_i].

Continue has value C_i=B_i+alpha_i U_i. Direct substitution gives

    Q_i-C_i=H_i/[1-(1-q_i)alpha_i],
    H_i=(1-alpha_i)Q_i-B_i.                            (S3)

In particular H_i depends only on q_{-i}. If every H_i=0, then U_i=Q_i=C_i,
so every prescribed positive Quit/Continue mixture is a local root best
reply. Since all opponents have proper rates, these local equalities
bound every unrestricted behavioral replacement, not just stationary
hazard deviations.

### Remove the large-reward pole before applying the implicit theorem

Put theta=1/M and q_i=theta z_i. Each p_i(A) contains theta^|A|. In Q_i,
only the singleton-opponent terms contain an unbounded reward:

    sum_j p_i({j}) r_i({i,j})
      =sum_j z_j product_(k distinct i,j)(1-theta z_k)
       +sum_j p_i({j}) c_i({i,j}).                    (S4)

Consequently Q_i is a POLYNOMIAL in theta,z and the bounded table data,
after this cancellation. Also 1-alpha_i and every nonempty summand of B_i
are divisible by theta. Thus the exact rescaled owner field

    Phi_i(theta,z,data)=H_i/theta                     (S5)

extends polynomially through theta=0. This extension is not a terminal
payoff at an improper zero-hazard profile; it is an algebraic continuation
used to produce positive hazards at theta>0.

Let s_i=r_i({i}) and Gamma_ij=r_i({j})-s_i for j!=i, with zero diagonal.
Writing a_i=sum_(j!=i) z_j, the polynomial extension satisfies exactly

    Phi_i(0,z,data)=a_i^2-(Gamma z)_i.                 (S6)

Indeed Q_i at theta zero equals s_i+a_i, (1-alpha_i)/theta equals a_i,
and B_i/theta equals sum_j z_j r_i({j}). All bounded nonsingleton data
disappear from (S6).

For (S1), every row sum is one, so

    z*=(1/9,1/9,1/9,1/9)

is a strictly positive zero of (S6). The exact z-Jacobian there is

    B=[0,-7/3,5/3,5/3; -7/3,0,5/3,5/3;
       5/3,5/3,0,-7/3; 5/3,5/3,-7/3,0].             (S7)

Its eigenvalues are 1,-17/3,7/3,7/3, so det B=-833/27!=0. Its inverse is

    B^(-1)=[50/119,-1/119,5/17,5/17;
             -1/119,50/119,5/17,5/17;
             5/17,5/17,50/119,-1/119;
             5/17,5/17,-1/119,50/119].                (S8)

Both (S6) and (S7) were independently recomputed by exact symbolic
expansion of the original coalition sums for the explicit family below.
The determinant and inverse were checked by exact rational arithmetic.

### Uniform producer over the ENTIRE bounded data box

Fix R. The forty-four bounded nonsingleton parameters form the compact
cube [-R,R]^44. At theta=0, the reference singletons, and z*, equation
Phi=0 and invertibility (S7) hold at EVERY point of that cube, with the
same z-Jacobian. Apply the finite-dimensional implicit function theorem
at each such point, treating theta, all singleton entries and all bounded
coordinates as parameters. Each application produces a local solution in
z, which can be kept in the open cube (1/18,1/6)^4.

Choose finitely many of the parameter neighborhoods whose bounded-data
parts cover [-R,R]^44. Taking a common smaller positive theta interval
and singleton radius delta gives a solution for every allowed bounded
data point, every nearby singleton table, and every sufficiently small
theta>0. No agreement of the local selectors on overlaps is required:
only existence for each original table is asserted. Shrink theta so all
q_i=theta z_i are below one. This proves the uniform M0 statement.

For any produced table, H_i=theta Phi_i=0. Equations (S3) therefore give
actual policy recursion and local root Nash. Since all four rates are
positive, every player's opponents continue a whole date with probability
strictly less than one. Telescoping the local inequality has a geometrically
vanishing remainder for ANY replacement. This proves exact terminal Nash
and supplies one actual stationary payoff target. The same profile gives
that original-game uniform payoff; no Never affine-invariance is used.

### Joint approximate finite menus are also produced

Let K bound the absolute rewards of the fixed original table. Censor each
geometric clock beyond date N to Never, leaving every earlier atom intact.
By (S2), each changed marginal mass is at most exp(-(N+1)/(18M)). Product
coupling changes any prescribed payoff by at most 2K times the sum of those
four masses, uniformly over the replacing law. Hence full exploitability
of the censored product is at most

    16K exp(-(N+1)/(18M)).                             (S9)

Fix one admissible M representation of the original table. Choosing N
as appropriate for that fixed table and the error therefore
gives actual finite product clocks solving its joint approximate-selection
question. This bound controls the FULL cap, including late deadlines and
unused-Never slack, not just Nash regret within the censored menu.

### An exact all-pure/all-quiet-child exclusion fixture

For the reference singletons, choose every pair participant reward M and
every pair passive reward -4. Set the four triple rows and grand row to

    r(012)=(-6,-3,-3,-5),
    r(013)=(-3,-6,-5,-3),
    r(023)=(-6,-5,-3,-3),
    r(123)=(-5,-3,-6,-3),
    r(0123)=(-100,-101,-102,-103).                     (S10)

Together with the four singleton rows and six pairs just specified, this
is a complete fifteen-row family. It lies in the theorem with R=103 for
all sufficiently large M. For M>4 it has NO pure-clock Nash equilibrium:

- A singleton first coalition has an outsider who gains by joining, since
  pair participation pays M>4, whereas singleton passive payoffs are at
  most four.
- Every pair has an outsider with joining reward -3, exceeding its passive
  reward -4. The sole bad participant in triples012,013,023,123 is
  respectively0,1,0,2. The associated blocked pair joins are respectively
  12,03,23,13, all distinct, so no pair has both outsiders blocked.
- Each triple has a participant with reward -6 who gains by leaving:
  the resulting pair gives that player passive payoff -4.
- Every grand participant gains by leaving: -100-i<-5.
- These arguments directly rule out every coalition at date zero. At a
  later first date, every possible coalition has at least one receiver
  below its own singleton one, who can preempt at date zero. All-Never
  is also defeated by immediate singleton quitting.

The fixture also fails EVERY proper nonnegative quiet-child join criterion,
not merely one chosen lift. For a triple child C, take its unique bad
participant d and T=C-d. That donor's join gain is -6-(-4)=-2. The omitted
outsider e has join gain -3-(-4)=1, because the blocked pairs above are
distinct. Child members already in T have join gain zero. Thus the (J)
inequality 1<=-2*w_d fails for all nonnegative child weights. For a pair
child, take T to be the whole child: some outsider has positive join gain
one while every donor's join gain is zero. For a singleton child, take its
whole coalition: an outsider join gain M-r_e({d})>0 again faces zero.
This is the literal J in `CappedClockParentRewardCertificate`, not an
informal observer comparison.

These exact failures do not show absence of a uniform equilibrium—the
candidate theorem produces one. They only avoid two elementary existing
sources. Matrix (S1) is the known hard paired Q example, so the bare
homogeneous/ordinary-non-Q and projective-Q-bar sources do not apply.
Further bounded source screens remain pending.

### Narrow source audit and relation to other work

`isZeroAsymptoticNash_stationary_of_fixedPoint_endpointNash_contracts`
and `isUniformEquilibriumPayoff_of_stationaryEndpointCertificate_contracts`
in `UniformEquilibrium/Quitting/Stationary/EndpointCompiler.lean` are the
exact unrestricted-behavior consumers used here. The theorem's producer
is the pole-cancelled system (S5)–(S8), not either checked compiler alone.

`QuittingCenteredStationaryFaceCertificate` in
`Classification/Existence/CenteredStationaryFaceCertificate.lean` is an
existing supplied-field box verifier. It does not assert existence of its
uniform error estimate from arbitrary reward data. The present asymptotic
argument constructs the needed zero directly from the raw scale conditions;
it is not a claim that the verifier itself was missing.

The narrow search for large pair-participation and stationary perturbation
sources found no matching producer. I read the entire
`CODEX_HILBERT__COLLISION_SUBSIDY_POLYNOMIAL_TRANSPORT_TEST.md`: its homotopy
adds to ALL participating nonsingletons and attempts to transport a fixed
polynomial tolerance. It stops before its sure-root endpoint. Here only
pair participant coordinates grow, all higher coalitions stay bounded, and
there is no back-transport claim or presumed polynomial certificate.

Current concrete request: independently check (S3)–(S8), especially uniform
IFT over all forty-four bounded coordinates and full-behavior compilation;
then check whether an existing raw producer already contains the entire
large-M family (S10), not merely whether a supplied-root verifier can verify
its produced equilibrium. No export is requested before these checks.

### Independent feedback incorporated

CODEX_TURING_BOX independently checked (S3)–(S8), compact-box uniform IFT,
full stationary behavioral/Never semantics, terminal-to-uniform passage,
and the stated pure/quiet-child fixture tests; see the feedback file for
this notebook. No mathematical objection was found. The truncation paragraph
now explicitly fixes an admissible M representation of the original table
before varying N: M is NOT an accuracy-dependent modification of that table.

CODEX_EMMY_BOX found that S10 is already solved by a persistent base:
q0=q1=1, q2=1/99, q3=1/98. The free-player indifferences are respectively
+1 versus -97 and +1 versus -98. The two base-owner leave margins are
[9506(M-4)-191]/9702 and [9506(M-4)-195]/9702, both positive for M>=5.
The named existing consumer is
`exists_uniformPayoff_of_persistentBase_inducedNash_signs` from
`Diagnostics/Quitting/Collision/Toggles/PersistentBaseNashSemanticAdapter.lean`.
Thus S10 is NOT a new-coverage witness. The pure/quiet-child exclusions
remain correct but are insufficient. No export is proposed on their basis.

## 9. Broad persistent-base containment and a consequential failed limit

This section is unreviewed ordinary mathematics. It concerns the ENTIRE
fixed-singleton large-pair scale family, not just S10. The bounded data are
fixed while M grows. No uniform threshold as bounded data degenerate is
claimed here.

Write

    Delta_i=r_i(I)-r_i(I-i)

for the grand-coalition joining gaps. Assume for this section every Delta_i
is nonzero. Then for all sufficiently large M an EXISTING persistent-base
source solves the table. This substantially weakens the novelty case for
Section 8, even though its separate four-proper-hazard producer is sound.

### At most one positive grand gap: an induced-three-player upper corner

Choose an owner b so all other three Delta_i are negative. If there is one
positive Delta, choose its player. If all are negative, choose b minimizing
d_b=-Delta_b>0. Fix b to Quit surely and let its three free players have
Continue rates epsilon_i=t z_i, with M=1/t^2. For free i, writing j,k for
the other free players, its exact stage Quit-minus-Continue difference is

    D_i=(M+bounded)epsilon_j epsilon_k
         +g_ij(1-epsilon_j)epsilon_k
         +g_ik epsilon_j(1-epsilon_k)
         +Delta_i(1-epsilon_j)(1-epsilon_k),             (C1)

where both g terms and the displayed bounded residual are independent of
M. The M pole cancels. At t=0 the field is z_j z_k-d_i. Its positive root
is z_i=sqrt(d_j d_k/d_i), with Jacobian determinant 2 z_i z_j z_k>0.
IFT therefore produces an exact fully mixed induced free-player Nash
point for every sufficiently large M.

One MUST retain the rare-pair subsidy to the owner. With three free players
almost surely Quitting, the owner's pair-participant payoff contributes

    M Pr(exactly one free Quit) -> sum_(i!=b) d_i.

Thus, if Q_b is its prescribed payoff and B_b its Continue numerator,

    Q_b-B_b -> Delta_b+sum_(i!=b)d_i >0.               (C2)

The strict sign follows from the choice of b. It is NOT merely the grand
gap Delta_b. Dropping the scale times the vanishing pair probability led
to a false proposed one-owner exclusion; that argument is withdrawn.

The actual singleton-base test prices Continue at the exact punishment
value v_b, not at stationary Never. Its excess is

    B_b+alpha_b v_b-Q_b,
    alpha_b=product_(i!=b)epsilon_i ->0.                (C3)

All non-pair-participant rewards are bounded below independently of M, and
the owner can be punished by having all three opponents Quit at date zero;
its cap there is max(r_b(I),r_b(I-b)), also uniformly bounded. Hence v_b
is uniformly bounded on this fixed-data scale family. The extra term in
(C3) vanishes. Equation (C2) gives a strictly NEGATIVE actual floor excess
for all sufficiently large M. The owner therefore passes the EXISTING
singleton-persistent-base source, not only a stationary Never comparison.

### Two or more positive grand gaps: a two-free-player source

If all four grand gaps are positive, all-Quit is exact Nash. If there is
one negative player b, inspect T=I-b. Its outsider b prefers Continue.
If every participant prefers staying in T, it is already pure Nash.
Otherwise take i in T with

    g_i=r_i(T)-r_i(T-i)<0.

Use base A=T-i, and free players i,b. Player i has negative joining gap
when b Continues and positive gap Delta_i when b Quits. Player b has
negative gap Delta_b when i Quits. If b's gap when i Continues is nonpositive,
both-Continue is an induced Nash point. Otherwise the free two-player game
is matching pennies with an interior Nash point. In either case there is
an induced Nash with BOTH free Quit rates strictly below one.

For exactly two positive and two negative grand gaps, first use the two
positive players as base. For the two negative free players a,b, if their
joining gaps at both-Continue have the same weak sign, the two-player game
has an induced Nash with both Quit rates below one (including zero-gap
endpoints). The only remaining case is, up to interchange, g_a>0>g_b.
Its unique pure induced point has a Quit, b Continue. Inspect T=I-b.
If the two original base players also prefer staying, T is pure Nash.
Otherwise remove a base player c with negative leave gap from T and make
c,b the two free players. Now c has positive grand gap and negative initial
gap, while b has negative grand gap. This is exactly the preceding
matching-pennies/both-Continue construction.

At any produced induced point with both free Quit probabilities below one,
the no-free-Quit probability p is positive and independent of M. Each base
owner gets M+bounded on that event, whereas its Continue payoff is uniformly
bounded. Its leave margin is at least M p-constant. Both base owners therefore
pass the existing large-base screen for all sufficiently large M. All other
players are free, so there is no untested fixed outsider.

### Surviving scope and boundaries

This proves GENERIC fixed-data containment in existing persistent-base or
pure-coalition sources. It does NOT prove whole-class containment when one
or more grand gaps are exactly zero. Generic density alone cannot handle
a fixed M: the positive no-free-Quit mass p, and hence the threshold M0,
can degenerate as a grand gap tends to zero. No boundary-class theorem or
strict-new-coverage claim is inferred from this failure of the generic proof.
The conference direction is to keep this overlap and move to a more global
mechanism, not tune increasingly intricate fixtures to rescue a neighborhood.

Exact definitions inspected: `quittingSingletonBaseOwnerFloorExcess`,
`quittingSingletonBaseOwnerFloorExcess_nonpos_iff`, and
`quittingPersistentLargeBaseExcess_nonpos_iff` in
`Diagnostics/Quitting/Collision/Toggles/PersistentBaseConcreteGap.lean`;
`exists_uniformPayoff_of_persistentBase_inducedNash_signs` in the adapter
above. These distinguish the actual punishment floor in (C3) from a mere
stationary Never value. The source theorem is supplied an induced Nash and
all base/free/outsider signs; the constructions here produce those inputs.

## 10. Global nonlinear degree producer beyond a nonsingular limiting root

This is a NEW UNREVIEWED ordinary proof attempt, not a new coverage claim.
It replaces the special paired-matrix IFT root in Section 8 by a global
complementarity argument. All boundary solutions remain explicit.

Fix n>=2 players and ANY singleton table with comparison matrix Gamma of
zero diagonal. Assume Gamma is R0 and its canonical complementarity degree
d is nonzero. Fix all other bounded data as in Section 8, with every pair
participant reward M+bounded and every other nonsingleton reward bounded.
Then for all sufficiently large M there is an exact stationary terminal
Nash equilibrium with total Quit rate O(1/M). A quantitative matrix margin
or supplied nonlinear root is not an input. Singleton own rewards may have
either sign in this degree version.

The exact polynomial field Phi(theta,z) is the same pole-cancelled field
(S5), now in n dimensions. Its limit is

    Phi_i(0,z)=(sum_(j!=i)z_j)^2-(Gamma z)_i.           (D1)

Seek a NONZERO complementarity solution

    z>=0,   Gamma z-a(z)^2>=0,
    z_i[(Gamma z)_i-a_i(z)^2]=0.                       (D2)

### Global compactness and a nonzero limit solution

Let G bound all absolute entries of Gamma. If z>=0 and Gamma z>=a(z)^2,
put T=sum z and choose z_j>=T/n. For any i!=j,

    T^2/n^2 <= a_i(z)^2 <= (Gamma z)_i <= G T.

Thus T<=n^2 G. The entire feasible set is compact. In particular it is
not enough to exhibit the ever-present zero solution.

The pole-cancelled field is polynomial on all real z, so no positive-part
extension is needed outside the orthant. For x in R^n set

    h_lambda(x)=min(x, Gamma x-a(x)^2-lambda 1).

A zero has x>=0 and satisfies complementarity, and for lambda>=0 all zeros
belong to the compact set just bounded. For sufficiently large lambda
there is no zero at all. On a large ball the homotopy in lambda therefore
gives total degree deg h_0=0. Near the origin the quadratic term is lower
order; R0 gives an isolated zero and local degree equal to d!=0. By degree
additivity the annulus has degree -d!=0. Hence (D2) has a nonzero solution.
No interior-positivity conclusion is asserted: some coordinates may vanish.

### Perturb the FIELD, not one selected nonlinear root

Choose fixed small and large balls so the limiting minimum map has no zero
on either boundary, origin is its only zero in the small ball, and its
annulus degree is -d. Uniform convergence of the exact polynomial fields
on these two compact boundaries preserves that annulus degree for small
theta>0. R0 and a uniform quadratic remainder bound also isolate the origin
uniformly in theta. Thus

    h_theta(x)=min(x,-Phi(theta,x))

has a nonzero zero z_theta in the fixed annulus. This step does NOT require
any limiting root to be simple, any common continuation component, or a
continuous root selector. For an entire bounded-data cube, the polynomial
convergence and remainder bounds are uniform, giving a common threshold.
Set q_i=theta z_theta,i. For theta small all
q_i<1; active coordinates satisfy Phi_i=0 and inactive coordinates satisfy
Phi_i<=0. Therefore (S3) gives exact endpoint Nash with inactive Continue.

There cannot be exactly one active coordinate j for M large. R0 for a
zero-diagonal matrix implies each column has a strictly negative entry:
otherwise the j-th unit vector would be a nonzero homogeneous LCP root.
Choose Gamma_ij<0. With only j active, its inactive opponent i has

    H_i=q_j[-Gamma_ij+q_j(M+c_i({i,j})-s_i)]>0

once M+c_i({i,j})>s_i, contradicting inactive endpoint Nash. Consequently
at least TWO rates are positive. Every player's opponents then contract,
including active players, so the checked stationary endpoint compiler
gives exact terminal Nash against all full behaviors and one fixed uniform
payoff. A singleton-root boundary has not been silently treated as proper.

### What this does and does not establish

The construction works for arbitrary hard Gamma with nonzero degree,
without a positive inverse or a specially nonsingular quadratic root. It
is a genuine global field producer, but it still only solves the specified
large-pair reward scale family. Section 9 already gives generic existing-
source containment of that family in Fin4. This degree argument is not a
back-transport to M=0, not a producer for arbitrary original reward data,
and not a proof that every stationary-equilibrium branch continues.

An early exact guard against overclaiming is the cyclic three-player
Example 3 represented in `Literature/future/FleschThuijsmanAndVrieze1996.lean`:
the actual declaration `example3_no_stationary_equilibrium` rules out exact
stationary equilibrium in its original table. Its pair participant rewards
are not a common sufficiently large M plus bounded fixed residuals. The
present theorem changes those rewards and therefore does NOT imply a
stationary equilibrium in that original example.

I inspected `singleton_r0Degree_eq_one_of_no_uniformPayoff` and
`exists_uniformEquilibriumPayoff_of_r0Degree_ne_one` in
`Classification/LCP/SingletonDegreeCriterion.lean`. The former ASSUMES full
R0 and then obtains degree one from original-game noUE; it does not supply
R0 by itself. I also inspected the actual full-support residual constructor
in `Diagnostics/Quitting/Collision/SingletonPacket/FullSupportProjectiveQBarResidual.lean`.
No silent identification of its normalized-core matrix with an arbitrary
raw full matrix is made here. The degree theorem above explicitly assumes
the raw Gamma property it uses.

Next serious question: can an actual original-table stationary or jointly
varying-clock field acquire a nonzero annulus degree from hard Gamma WITHOUT
introducing the large external pair reward scale? The present coercive
quadratic is generated by that real reward scale, not by choosing a law.
This missing step is substantive; renaming it a clock selector would not
provide it.

## 11. Exact original-field test: degree one can leave ONLY the zero root

Ordinary exact calculation, not a new no-go theorem or new UE class. This
closes the attempted extension of Section 10 based ONLY on the original
singleton R0 degree. It does not obstruct arbitrary nonstationary law
selection.

The literal three-player Example 3 has singleton rows

    r(0)=(1,3,0), r(1)=(0,1,3), r(2)=(3,0,1),
    r(01)=(1,0,1), r(02)=(0,1,1), r(12)=(1,1,0),
    r(012)=(0,0,0).

Its original singleton matrix is

    Gamma=[0,-1,2; 2,0,-1; -1,2,0], det Gamma=7.

This matrix is R0. A nonzero homogeneous LCP vector cannot have singleton
support, because each column has a negative entry. It cannot have support
two, because one of the two active equations is a negative nonzero multiple
of its other active coordinate. Full support would require Gamma z=0,
contradicting the determinant. The shifted LCP with constant vector -1
also has no one- or two-coordinate support (the active negative entry
cannot equal +1), and its unique full-support solution is z=(1,1,1).
That root is regular with positive determinant. The canonical degree is
therefore +1, by the finite-support degree formula / constant-shift
homotopy. This is precisely the hard degree, not an already-exiting
degree-different-from-one case.

Now use the ORIGINAL rewards, with stationary hazards (x,y,z) in [0,1]^3.
Directly recomputing H_i=(1-alpha_i)Q_i-B_i gives

    H0=y(1+z^2)-z(2+z),
    H1=z(1+x^2)-x(2+x),
    H2=x(1+y^2)-y(2+y).

An active hazard requires its H_i>=0 (strictly interior requires equality);
an inactive one requires H_i<=0. These conditions have ONLY the zero
solution. Indeed, if x>0 and y=0, H0>=0 forces z=0, but then H2=x>0
violates inactivity. Thus y>0, and H1>=0 forces z>0. Once all are positive,

    y/z >= (2+z)/(1+z^2)>1,
    z/x >= (2+x)/(1+x^2)>1,
    x/y >= (2+y)/(1+y^2)>1,

an impossibility. Cyclic relabeling covers any initially positive hazard.
The strict ratios hold even at rate one, so no boundary solution has been
lost. The zero field root is NOT a Nash profile: all-Never earns zero,
while unilateral finite Quit earns singleton reward one.

I recomputed all three polynomials by exact symbolic expansion of all
seven coalition rows. The source declarations inspected are
`example3Reward`, all seven `example3TerminalReward_*` row identities,
`example3_no_stationary_equilibrium`, and `example3_corrected` in
`Literature/future/FleschThuijsmanAndVrieze1996.lean`. The last two already
certify stronger unrestricted-deviation stationary exclusions. The ordinary
degree calculation above is not represented as a new checked declaration.

Consequently no singleton-degree-one argument can force a nonzero solution
of the original stationary-response field in general. In Section 10 the
large pair reward supplies the coercive quadratic and changes the global
degree balance; it is not a harmless law reparametrization. A new producer
would need genuinely nonstationary joint laws, or additional raw-table
hypotheses with independently checked new coverage. The present large-pair
degree result has no established class beyond the generic existing-source
containment of Section 9, so it is retained as an internal mechanism rather
than proposed for export.

## 12. Original-table golden singleton calendar

Status: independently reviewed ordinary mathematics; NOT Lean-implemented.
The canonical complete statement, proof, strengthened quantifiers and bounded
source comparisons are in
[`FOUR_SINGLETON_PHASE_UNIFORM_EQUILIBRIUM.md`](../exports/FOUR_SINGLETON_PHASE_UNIFORM_EQUILIBRIUM.md),
frozen SHA256 `678acf8b57673b513b9660ee41b52401fe5fac8d9fc8b688b2c84f8e7e464829`.
Independent soundness/coverage reviews are recorded in the two main-notebook
feedback files BY_CODEX_TURING_BOX and BY_CODEX_EMMY_BOX. The final packet
also passed an assembled transcription check. This exploratory section is
independent of the artificial large-pair parameter in Sections8--10. Its
twelve joining caps are sufficient raw input, not a strategy-class
completeness claim. The canonical packet includes the resolved actual
quotient and product-low checks.

### 12.1. Literal source and explicit policy

There are four players, independent private behavioral randomization, public
action histories, live and Never payoff zero, and arbitrary finite rewards at
the first nonempty coalition. Every deviation may replace the entire behavior,
including unbounded deadlines and Never. All conclusions are in expectation.

Fix these sixteen singleton coordinates:

| S | r(S) |
| --- | --- |
| 0 | (1,4,0,0) |
| 1 | (4,1,0,0) |
| 2 | (0,0,1,4) |
| 3 | (0,0,4,1) |

Write

    q=(sqrt(5)-1)/2,  c=1-q=(3-sqrt(5))/2,
    H=(3+sqrt(5))/2,  T=(5+sqrt(5))/2.

Use the deterministic periodic schedule j=(0,2,1,3). At a phase with owner j,
only j quits, with probability q; every other player Continues. Random coins
are independent across players and dates. Assume exactly these twelve upper
bounds, with no lower bounds:

| pair S | capped participant coordinates |
| --- | --- |
| 01 | r_0(S)<=T, r_1(S)<=T |
| 23 | r_2(S)<=T, r_3(S)<=T |
| 02 | r_0(S)<=1, r_2(S)<=0 |
| 03 | r_0(S)<=0, r_3(S)<=1 |
| 12 | r_1(S)<=0, r_2(S)<=1 |
| 13 | r_1(S)<=1, r_3(S)<=0 |

All remaining 32 coordinates are arbitrary finite numbers: the twelve
nonparticipant pair coordinates, sixteen triple coordinates and four grand
coordinates. They are not set to zero, ignored as game data, or altered.
They cannot occur under this policy or any ONE player's replacement: at
every live date at most one opponent is scheduled, so every possible
terminal coalition has size at most two and a deviator in a pair is a
participant. This explains precisely which coordinates the proof uses.

The actual phase values, in chronological order 0,2,1,3, are

    U0=(1,H,c,1), U2=(1,c,1,H),
    U1=(H,1,1,c), U3=(c,1,H,1).                 (12.1)

For example, with R_t=r({j_t}), these are independently recomputable as

    U_t=[q R_t+c q R_(t+1)+c^2 q R_(t+2)
                          +c^3 q R_(t+3)]/(1-c^4).

They satisfy U_t=q R_t+c U_(t+1). The scheduled owner's own coordinate
equals one BOTH before and after its phase, so its pure Quit and pure
Continue endpoints are exactly equal to one.

For an inactive player i at j's phase, Continue is U_ti and Quit is

    c*r_i({i})+q*r_i({i,j})=c+q*r_i({i,j}).    (12.2)

Each inactive U_ti is H, 1, or c. Solving (12.2)<=U_ti yields respectively
the exact caps T, 1, or 0 printed above. In particular these are literal
endpoint inequalities, not a solo-floor approximation; some values c are
strictly BELOW the own singleton one. All prescribed endpoints and policy
recursions are thus exact.

### 12.2. Complete-deviation and same-profile uniform conclusion

For any player i, deleting i's clock leaves three scheduled independent
coins in every four consecutive dates. Their survival per cycle is c^3<1.
Consequently opponent survival over n dates is at most

    (c^3)^floor(n/4).

This bound is independent of i's replacement strategy, including any
history-dependent private randomization, and holds at every initial phase.
One may pre-sample the opponents' independent stopping laws; survival means
precisely that none of these laws has stopped yet. At every live history,
the preceding endpoint calculation bounds ANY mixture of Quit and Continue
by U_ti. Iterating this supermartingale/Bellman inequality for n dates leaves
a continuation remainder of absolute value at most a fixed finite reward
bound times opponent survival. This tends to zero. Thus every complete
behavioral replacement earns terminal payoff at most U_ti; the prescribed
policy earns U_ti by its exact policy recursion. The profile is exact
terminal Nash at every literal phase and suffix.

For explicit finite-horizon control, let M>=max(1,max_(S,i)|r_i(S)|), and
put C=1+4/(1-c^3). The sum of opponent live probabilities, including the
initial live date, is at most 4/(1-c^3). The possible additional selecting
date is covered by the extra one in C. For EVERY replacement law the
absolute difference between expected N-stage average and terminal payoff
is at most M*C/N: pathwise it is at most M times the fraction of dates
through selection, and selection is no later than the first opponent stop.
The prescribed policy obeys the same bound. Exact terminal Nash therefore
gives full behavioral finite-horizon regret at most 2*M*C/N, with delivery
error at most M*C/N. For each positive accuracy choose a sufficiently large
N, retaining THIS SAME policy and phase value. Thus each of (12.1) is one
fixed original-game uniform-equilibrium payoff. No limit of payoff targets,
chronological relation between accuracy profiles, or public correlation is
needed. A weaker all-errors terminal-to-UE consumer would also suffice.

This proof uses exactly the standard arbitrary-behavior Snell comparison
behind `quittingSubBellmanValue_le_superSolution_of_survival_zero` and
`quittingCyclicHazardTerminalValue_le_add_of_quitError_and_continueUpperBound`
in `UniformEquilibrium/Quitting/Cycles/CyclicSupersolution.lean`, which I
inspected. Those generic conditional consumers are not competing raw-table
producers, and consuming them is not a claim that the raw source was already
available. The finite-horizon source-free adapters are
`finiteAverage_delivery_le_of_opponentLiveCesaro_bound` and
`finiteAverage_deviation_gain_le_of_exact_terminalNash_and_opponentLiveCesaro_bound`
in `UniformEquilibrium/Quitting/Cycles/PeriodicFiniteHorizonRate.lean`.

### 12.3. Exact Jacobian and raw-neighborhood strengthening

Let p=(p0,p1,p2,p3) denote hazards in CHRONOLOGICAL order (0,2,1,3), not
player order. With cyclic indices define the cleared owner fields

    F_t(p)= -p_(t+1)+3*p_(t+2)*(1-p_(t+1))
             -p_(t+3)*(1-p_(t+1))*(1-p_(t+2)).           (12.3)

More generally, for nearby arbitrary singleton data with s_i=r_i({i}),
define F_t as the sum of the other three owners' singleton comparison
r_i({j})-s_i times their first-stop probabilities, starting just AFTER
owner i=j_t's phase and ending just before i's next phase. These are
polynomials in the four hazards and sixteen singleton rewards. If P is
the product of the four Continue probabilities, actual policy evaluation
gives the exact identity

    (1-P)*(U_(t+1),i-s_i)=F_t.                         (12.4)

Indeed, expose the three other scheduled clocks and then i's own coin;
the own stopping branch has reward s_i, and the all-Continue branch returns
to the same post-owner phase. Thus zero of this field is EXACTLY every
owner's actual indifference, whenever hazards are proper. It is not an
independent prescribed continuation vector.

At p=q*1 the field is q*(1-q-q^2)=0. Its Jacobian is circulant, with diagonal
zero and chronological offsets +1,+2,+3 equal respectively to

    A=-2-q,   B=2-q,   D=3*q-2.

The eigenvalues are q-2, 3*(2-q), and -(2-q)+/-4*q*sqrt(-1). Hence

    det J=-3*(2-q)^2*((2-q)^2+16*q^2)
          =(-2205+945*sqrt(5))/2 < 0.                  (12.5)

I independently expanded (12.3), substituted the exact algebraic q, and
computed the literal 4x4 determinant using SymPy; the result agrees with
(12.5) exactly. This is exact arithmetic evidence for the displayed
calculation, not a Lean check or independent proof review.

The ordinary implicit-function theorem therefore selects proper hazards
p(r) continuously from the sixteen singleton rewards near the printed
center. They are chosen from RAW TABLE DATA, before any accuracy or horizon.
For a strict completion below all twelve inactive gaps are positive. Their
endpoint expressions depend continuously only on these sixteen rewards,
the selected hazards, and the twelve participant pair rewards. It follows
that there exists delta>0 for which all singleton rewards within delta of
the center, and every participant pair reward at most its strict-completion
value plus delta, satisfy the inactive inequalities. There is no lower
bound on those twelve pair entries: reducing one only reduces its Quit
endpoint and does not alter policy evaluation, because policy absorption is
singleton-only. Every other reward entry remains arbitrary finite. All
hazards remain in some fixed closed interval strictly inside (0,1), so the
complete-behavior and same-profile uniform proof above is unchanged. The
explicit C may be replaced by the corresponding uniform opponent-survival
constant. No numerical radius is claimed.

### 12.4. One strict complete table and whole sure-owner screen

Here is a fixed strict completion (no asymptotic reward parameter):

| S | r(S) |
| --- | --- |
| 0 | (1,4,0,0) |
| 1 | (4,1,0,0) |
| 2 | (0,0,1,4) |
| 3 | (0,0,4,1) |
| 01 | (7/2,7/2,0,0) |
| 02 | (1/2,0,-1/2,0) |
| 03 | (-1/2,0,0,1/2) |
| 12 | (0,-1/2,1/2,0) |
| 13 | (0,1/2,0,-1/2) |
| 23 | (0,0,7/2,7/2) |
| 012 | (-1,-1,-1,0) |
| 013 | (-1,-1,0,-1) |
| 023 | (-1,0,-1,-1) |
| 123 | (0,-1,-1,-1) |
| 0123 | (-2,-2,-2,-2) |

The four mate-pair cap margins are T-7/2=(sqrt(5)-2)/2>0. Every other
cap margin is 1/2. Multiplying each by q gives its actual inactive endpoint
margin. There is no tuned large scale or accuracy-dependent reward change.

Let m exchange 0<->1 and 2<->3. Let kappa be the directed four-cycle

    0->3->1->2->0.

For ANY sure owner j, inspect the ENTIRE induced binary game of the other
three players, allowing every mixed support and boundary profile. Its mate
m(j) has Quit-minus-Continue -1/2 when no other nonowner quits. The remaining
noncollider (the third nonowner other than kappa(j)) also has gain -1/2.
If any other nonowner quits, either of these two players instead has gain
-1 (one other) or -2 (two others): its joining reward is the participating
triple/grand reward, and its absent-recipient pair/triple reward is zero.
Thus both have STRICTLY negative gain against every product law of the
other nonowners. In every mixed Nash equilibrium both must Continue surely.
Then kappa(j) has gain +1/2 and must Quit surely. Consequently the WHOLE
induced mixed-Nash set is the single point

    kappa(j)=Quit, all other nonowners=Continue.         (12.6)

At (12.6), owner j earns r_j({j,kappa(j)})=-1/2 by Quit and earns
r_j({kappa(j)})=0 by Continue. Another player quits surely, so the
all-opponents-Continue probability is zero: every punishment-floor term
has coefficient ZERO. The owner's actual leave gain is therefore +1/2,
independently of any proposed punishment value. This is stronger than
testing the stationary Never continuation.

This excludes EVERY sure-owner stationary root, not just pure roots: any
Nash root with j sure has an induced Nash profile among its nonowners, hence
(12.6), and fails j's leave sign. It also excludes ALL persistent-base/free
source selections, including partial free sets. For a one-owner base, a
Nash point on a smaller free set plus outsider no-join signs extends to a
full induced three-player Nash point, which (12.6) classifies. For any base
of size at least two, the base leave signs, free Nash signs and outsider
no-join signs together make a full one-date Nash root with a sure owner;
the preceding exclusion applies. No omitted free support or larger base
can escape the screen.

Exact definitions inspected are `quittingPersistentBaseUtility`,
`quittingPersistentBaseNashSet`, `quittingPersistentBaseRoot`, and
`quittingPersistentBaseRoot_free_purePayoff_le` in
`UniformEquilibrium/Quitting/Root/PersistentBaseInducedGame.lean`, together
with `nonempty_quittingPersistentBaseCertificate_of_inducedNash` and
`exists_uniformPayoff_of_persistentBase_inducedNash_signs` in
`UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PersistentBaseNashSemanticAdapter.lean`.
These declarations use the actual induced game and full zero-tail endpoint
signs. The one-owner argument above is a direct exact screen, not a claim
that the named >=2-base declaration itself accepts singleton bases.

### 12.5. Whole proper-child raw certificate screen, all withdrawal kinds

Fix ANY nonempty proper child A of the four players. A directed four-cycle
has no nonempty proper forward-closed subset, so choose j in A with
e=kappa(j) outside A. Use the child coalition T={j} and exterior player e.
The parent's joining advantage is exactly

    r_e({j,e})-r_e({j})=1/2.                           (12.7)

For every child donor d, its advance row at T is nonpositive: it is zero
if d=j, and -1/2 otherwise (mate joining 7/2 minus its passive singleton4,
or cross joining -1/2 minus passive singleton0). Every withdrawal row is
also nonpositive. Donors not in T have withdrawal gain zero. For d=j the
singleton gain is its selected restart floor minus its own singleton one.
Patient withdrawal's floor is at most max(1,0)=1. Deadline/cancellation
floor is at most zero. Evaluated-security floor is explicitly the minimum
of the security floor with zero. Terminal-security floor is at most one:
its LP value is at most the literal own-singleton row one, and its zero
floor is at most zero. Notice that the terminal-security floor is NOT
claimed universally nonpositive; the singleton LP row is the sufficient
bound here. These arguments also cover a one-player child, with no opponent
coalition constraints in its security LP.

Thus for ANY nonnegative advance/withdrawal weights the right side of the
raw join inequality is at most zero, contradicting (12.7). This excludes
EVERY child and all FIVE actual `WithdrawalFutureJoinKind`s: patient,
deadline, evaluatedSecurity, terminalSecurity and cancellation, with
their actual restart floors. It also excludes the advance-only
`CappedClockParentRewardCertificate`, since it is the same nonpositive
advance sum. It is not merely a bad choice of child equilibrium.

The literal definitions inspected are `WithdrawalFutureJoinKind.gain` and
`WithdrawalFutureJoinRewardCertificate.join_row` in
`UniformEquilibrium/Quitting/Classification/QuietExtension/WithdrawalFutureJoinRaw.lean`;
`patientWithdrawalOwnNeverAlternative`, `patientWithdrawalFloor`, and its
own-alternative bound in `PatientWithdrawalRaw.lean` in that same directory;
`deadlineWithdrawalZeroFloor`, its nonpositive bound, and
`deadlineWithdrawalGainFloor` in `DeadlineWithdrawalRaw.lean`;
`deadlineSecurityGainFloor` in `DeadlineWithdrawalSecurityMixedPointwise.lean`;
`deadlineSecurityGainFloor_singletonWithRestart` in
`DeadlineWithdrawalRestartPointwiseCore.lean`; and
`deadlineWithdrawalSecurityRow`, `deadlineWithdrawalSecurityValue_le_singleton`,
and `deadlineWithdrawalSecurityFloor` in `DeadlineWithdrawalSecurityLP.lean`.
The advance-only declaration is in `CappedClockPointwiseDomination.lean`.

### 12.6. Whole balanced-singleton class versus this new calendar

The singleton comparison matrix is the hard paired matrix

    Gamma=[0,3,-1,-1;3,0,-1,-1;-1,-1,0,3;-1,-1,3,0].

Its positive off-diagonal graph consists of two disjoint transpositions.
`SignedFourCycleSingletonData` requires a strictly positive predecessor
Hamiltonian four-cycle, so no relabeling of this matrix can satisfy that
source. Both eigenvalue branches retain this same requirement.

There is a stronger WHOLE-certificate exclusion for balanced singleton
calendars. Suppose a `BalancedSingletonCycleCertificate` exists, with ANY
finite phase length, ANY owner word, and hazards a_t in [0,1). Its literal
requirements are the singleton arc, active owner value one, all-player
soloFloor u_ti>=1, and opponentDivergence. Choose a phase with a_j>0 and
owner j. By active and arc, the next phase's j coordinate is also one.
For each of the two players outside {j,m(j)}, its singleton reward at j's
stop is zero, so

    u_next,i=u_current,i/(1-a_j)>1.                   (12.8)

Follow the finite cyclic word until its first positive hazard with owner
different from j; opponentDivergence for j ensures one exists. Zero-hazard
phases do not change values. Every intervening positive j phase keeps
coordinate j equal to one and strictly increases both nonmate coordinates.
By (12.8), neither nonmate can be that first different active owner: their
values exceed one. Hence that owner must be m(j). At that phase coordinate
j is still one, whereas the arc with positive hazard a and singleton
reward r_j({m(j)})=4 forces

    u_next,j=(1-4*a)/(1-a)<1,

contradicting soloFloor at the next phase. Therefore NO such balanced
certificate exists, for any length or owner word. The same proof excludes
the bounds-enriched version, which has identical relevant fields.

The exact structures inspected are `BalancedSingletonCycleCertificate`
and `BalancedSingletonCycleCertificateWithBounds` in
`UniformEquilibrium/Quitting/Cycles/BalancedSingletonCertificate.lean`;
`SignedFourCycleSingletonData` in `SignedFourCycleRewardAdapter.lean`, with
the larger-root adapter retaining its input. Our explicit calendar works
precisely by dropping the artificial ALL-phase soloFloor; its actual full
endpoint inequalities remain valid because its literal joining caps are
small enough. This is not a modification of the game's rewards or agency.

The underlying paired matrix's existing R0/Q/degree-one and normalized-core
facts are not a new contribution. I inspected the literal definitions and
results in `UniformEquilibrium/Quitting/Examples/BlockPair/FourPlayerPairedSingletonLCP.lean`
and `UniformEquilibrium/Quitting/Examples/BlockPair/FourPlayerPairedSingletonResidualHard.lean`.
In particular a matrix-only
non-Q exit does not apply. Existing fixed-completion pure exits do not
cover arbitrary completions of the same singleton matrix.

The whole balanced-cycle obstruction is also not claimed as a new coverage
theorem: the current TOOLKIT records
`not_nonempty_balancedSingletonCycleCertificate` in
`UniformEquilibrium/Quitting/Classification/QuietExtension/CappedClockPairedCycleExclusion.lean`
for its paired family. The direct proof above is an independent exact screen
using only the common singleton rows; I did not rely on that declaration's
family membership or silently infer that our completion meets its separate
capped-clock hypotheses.

### 12.7. Bounded comparison against named pair and new four-phase sources

The following comparisons concern the fixed strict table in 12.4. They are
finite named raw-source screens, not a proof that no alternative strategy,
unquantified local neighborhood, or supplied-object verifier can solve it.

1. `PairedCycle.RawRegion` cannot hold for ANY pair schedule. Its theorem
   `RawRegion.eq_partner_of_singleton_lt` says every below-own passive
   singleton must be that recipient's scheduled partner. Our every player
   has TWO distinct below-own singleton opponents. This excludes every
   partition, not merely the favorite pairing.
2. `CrossedMatching.RawSource`, `WeakRawSource` and `InverseRawSource` all
   fail for every relabeling. The first two force the singleton favorite to
   be the unique mate, then require its joining reward <=own1; ours is7/2.
   The inverse source requires scheduled singleton<own, hence scheduled
   partner cannot be the mate; the mate is one of the two capped passive
   players, again requiring7/2<=1. The sure scheduled-pair cap producer is
   already excluded by the whole sure-owner screen in12.4.
3. `BelowSingleton.RawFamily` fails every relabeling. Its positive singleton
   favorite must again be the mate and its scheduled pairing must be a cross
   pairing. Every cross pair contains one participant with joining+1/2
   against scheduled passive singleton0. The family's negative scheduled
   premium would require that joining reward strictly BELOW zero. Thus
   neither cross partition works, and the favorite partition fails its
   singleton condition.
4. The raw source in `TWO_PAIR_JOIN_CAP_UNIFORM_EQUILIBRIUM.md` fails all
   three partitions. For mate pairing its joining>=partner-passive
   condition reads7/2>=4, false. Every cross pair has a participant with
   joining-1/2<scheduled passive0, also false.
5. `hasQuittingActualNonconcentratedGroupExclusion_half_of_twoPairRewardBounds`
   fails for every pair partition: its `hother` requires the designated
   pair-average surplus to be nonpositive at every singleton. For any
   pair, use the mate singleton of one of its players. The pair's total
   reward there is at least4, while its two own rewards total2, so its
   average surplus is at least1>0. Similarly
   `hasQuittingActualWeakSubsetExclusion_zero_one_of_crossMassBounds` has
   only a two-player-coalition positive row; every singleton row for a
   designated recipient is nonpositive. That recipient's mate singleton
   surplus is3>0, so no relabeling or allowed coefficients can fit it.
6. The newly frozen `FOUR_JOINT_PHASE_UNIFORM_EQUILIBRIUM.md` requires a
   center participant reward5 with raw error delta<=1/2 on a favorite
   pair. Our favorite participants are7/2, so the coordinate discrepancy
   is3/2. Singleton preferences uniquely identify the favorite pairing
   under relabeling; consequently no relabeling repairs this. Its source
   also has proper nonfavorite-pair participant center2, not our entries.
   The new `FOUR_JOINT_PHASE_RECTANGLE_UNIFORM_EQUILIBRIUM.md` fixes the
   same favorite pair participant reward5 (and another9/2), likewise
   excluding this table. These are literal stated-region separations,
   not assertions that the underlying joint-phase mechanisms cannot find
   another equilibrium in our game.

The exact declarations for items1--3 were inspected in
`UniformEquilibrium/Quitting/Cycles/PairedCycleSchedule.lean`,
`CrossedMatchingPhaseSource.lean` and `BelowSingletonJointPhaseSource.lean`.
Items4 and6 use the complete exported raw statements; the newer exports
are ordinary reviewed mathematical sources, not attributed as Lean facts.
Item5 uses the exact raw hypotheses in
`UniformEquilibrium/Quitting/Paths/TwoPairGroupExclusion.lean` and
`TwoPairCrossMassRewardExclusion.lean`. The all-child and all-base screens
are in12.4--5; no uniqueness of every child equilibrium is asserted.

### 12.8. Reviewed boundary and next question

This is an actual positive original-game producer, with a fixed table
strictly inside an explicit upper-only source and an open singleton-data
extension. It is not an unrestricted Fin4 producer and does not solve the
general joint approximate finite-menu selection question. Its potentially
new ingredient is exact singleton scheduling BELOW solo floors, compensated
by phase-specific collision caps. The independent bounded soundness and
coverage reviews found no unresolved objection. They additionally checked
the complete response-partition selection, which leaves genuine mate and
all-block P/degree-one quotients but no existing favorable quotient exit.
The canonical packet includes those exact tests. This is not exhaustive
strategy-source novelty or a stationary-nonexistence claim. The live next
question is a genuinely global nonstationary selection operation, not
tuning this center or manufacturing additional isolated calendars.
