# A vanishing private Never bonus selects useful finite equilibria on VANISH

Identity: CODEX_HILBERT. Ordinary mathematics, not independently reviewed or
Lean-checked. No export or arbitrary-table producer claim.

**Status.** A specified global selector among equilibria of vanishingly
perturbed finite games succeeds on VANISH, although every exact equilibrium
of its original finite game has a fixed full-regret gap. The same proof works
for the raw family with pivot outside reward R≥2. It uses a concrete
comparison law proved from that family, not one assumed for arbitrary games.
A known relabelled fixture rules out universal success with this one fixed
subsidized label; adaptive choice of the perturbed player remains unresolved.

## 1. Game, auxiliary payoff, and exact selection rule

The canonical VANISH table has four players. Indices 1,2,3 have cyclic
predecessor i⁻ and successor i⁺. For every nonempty coalition S define

    r_0(S)=1 if 0∈S, and 2 otherwise;
    r_i(S)=0                              if i∈S;
           −1                             if i∉S and 0∈S;
           2·1_(i⁻∈S)−1_(i⁺∈S)          otherwise, i=1,2,3.

Never pays zero. Stopping laws are independent and complete unilateral
behavioral replacements are legal. The own-singleton vector is (1,0,0,0).

Given accuracy ε>0, first choose an integer K≥1 such that 4^(−K)≤ε,
and then fix

    N=3K,       ξ=4^(−K),       J=8^(−K).

The auxiliary finite normal-form game has action set
F_N={0,…,N−1,Never} for each player. At a pure planned-action tuple A,
its payoff is the original terminal payoff plus

    ξ·1_(A_2=Never) in coordinate 2, and zero in all other coordinates.
                                                               (A)

The bonus is paid in the synthesis game even when another player's earlier
Quit ends original play. It is NOT an original quitting reward, a public
signal, a legal-play incentive supplied to the final profile, or a change
confined to the all-Never outcome. We use this auxiliary finite game only
to select independent laws, then evaluate those laws in the ORIGINAL game.

Among all mixed Nash equilibria of (A):

1. maximize the pivot's probability p_0(Never);
2. on that maximizing set, maximize its original payoff U_0(p).

Choose any maximizer remaining after these two operations. The finite-game
Nash set is nonempty and compact: each pure deviation inequality is a closed
polynomial inequality on a finite product of simplices. Both objectives are
continuous. Thus both maxima are attained; this specifies a nonempty class
of selected laws without assuming good full-regret values or a particular
equilibrium branch. Every final maximizer will satisfy the bound below.

The rule does not minimize full regret, impose a common nonpivot law, or use
entropy, a temperature, support floors, or a prescribed equilibrium tail.

## 2. A concrete comparison equilibrium of the auxiliary game

The following laws are a comparison point, not the definition of the
selector. Let p°_0=Never and, for i=1,2,3, let

    p°_i(3k+i−1)=2^(−k−1)          (0≤k<K),
    p°_i(Never)=2^(−K).                                  (2)

These are independent laws on the selected menu. At each designated date
the corresponding player Quits with conditional probability 1/2.

Here are the complete menu comparisons establishing that (2) is EXACT Nash
in (A). They are evaluated in the original table before adding the bonus.

The pivot's pure Quit-at-t payoff is 2−S(t), where S(t) is the probability
all opponents survive strictly before t. This is nondecreasing. At the last
menu date N−1, S(t)=2J, whereas its Never payoff is 2(1−J). Hence Never
is a menu best reply. Its only prescribed action is Never.

For a nonpivot i, every coalition containing i gives it zero, so the value
from Quit at t is exactly the expected reward accumulated from opponents'
absorption strictly before t. For players 1 and 3 that cumulative value is
zero at their prescribed finite dates and at Never. Between those dates it
is nonpositive: the successor's negative contribution is followed by the
predecessor's compensating positive contribution in each cycle. Thus every
prescribed action of players 1 and 3 is a menu best reply of value zero.

For player 2, the cumulative value at the beginning of opponent cycle k is
1−4^(−k). After player 1's date it is 1, and after player 3's date it is
1−4^(−k−1). Hence every prescribed finite date 3k+1 gives exactly 1,
every other finite date gives at most 1, and Never gives 1−4^(−K).
Adding the sole bonus ξ=4^(−K) makes Never tie the finite best responses
at value 1. All its prescribed actions are now optimal as well.

This verifies every pure menu response for every player. Linearity in the
own mixed law verifies every mixed menu response, so (2) is exact auxiliary
Nash, with

    p°_0(Never)=1,       U_0(p°)=2−2J.                   (3)

For an additional payoff check, original U(p°)=(2−2J,0,1−J,0).
Its coordinate-2 expected bonus is ξ·2^(−K)=J, making its auxiliary
payoff exactly 1. The positive menu error of the ORIGINAL law is essential:
we have not made an exact original finite-menu equilibrium good by selection.

The complete-response cumulative calculation in (2) is the one in
`gpt/VANISH.md`'s second response and its self-contained preservation
`CODEX_RENY__CANONICAL_EXACT_FINITE_MENU_SEPARATION.md`. The new deduction
here is the asymmetric auxiliary equilibrium and its extremal-selection
comparison; the geometric approximate law is not offered as a new discovery.

## 3. Every selected auxiliary law has small original full regret

Let p be any output of the two maximizations in Section 1. From (3), the
first optimum equals one; hence p_0=Never. The second comparison gives

    U_0(p)≥2−2J.

For ANY laws with p_0=Never in this table, put
D_0=∏_(i=1,2,3)p_i(Never). Since pivot payoff is two on every possible
absorbing coalition,

    U_0(p)=W_0(p)=2(1−D_0),       so D_0≤J.              (4)

The pivot is unperturbed, so its original menu debt is zero. Its pure
responses at or after N all have payoff W_0+D_0, since its singleton is
one. Therefore its full unrestricted debt is exactly D_0≤J.

Players 1 and 3 are also unperturbed, so their original menu debts vanish.
Their zero singletons make every omitted late response equal to Never;
their full debts therefore vanish too.

For player 2, auxiliary Nash against any replacement law μ on F_N gives

    U_2(μ,p_−2)−U_2(p)
      ≤ξ[p_2(Never)−μ(Never)]≤ξ.

Consequently its original menu debt is at most ξ. Its singleton is zero,
so its full debt is likewise at most ξ. This bounds all late dates and
Never, not just the finite pure tests used in auxiliary Nash existence.

Altogether, for every selected law,

    (d_0,d_1,d_2,d_3)≤(J,0,ξ,0),
    E_full(p)≤ξ=4^(−K)≤ε.                              (5)

These are actual original-game debts. The selected laws are genuine finite
four-law approximate equilibria, with no cross-accuracy compatibility
assumption. The all-errors terminal consumer yields a fixed uniform payoff;
the table already had one, so the new claim is a selector method check.

The exact integrated finite-menu semantics were checked in
`IsQuittingFiniteDeadlineNash` and `isQuittingFiniteDeadlineNash_iff_pure`
in `UniformEquilibrium/Quitting/Terminal/FiniteDeadlineReplyCap.lean` and
`singlePivot_nonpivot_fullCap_eq_menuCap`,
`singlePivot_pivot_fullCap_eq_max_menu_never_add_deletedNever`, and
`singlePivot_pivot_fullDebt_eq_max_menuDebt_scalar` in
`UniformEquilibrium/Quitting/Terminal/SinglePivotFiniteMenuSource.lean`.
The auxiliary payoff (A) is a separate ordinary finite game, not asserted
to be one of those original quitting-table definitions.

## 4. The precise raw-table comparison inequality

Keep the nonpivot rewards above except that their payoff when the pivot
absorbs is −h, with arbitrary h>0. Change the pivot's payoff outside its
membership from two to R>1. Everything else remains specified as above.

Under comparison law (2), the nonpivot calculations are unchanged because
the pivot Never occurs in an absorbing coalition. For the pivot,

    Never value=R(1−J),
    largest finite menu value=R−2(R−1)J,
    Never minus largest finite value=(R−2)J.              (6)

Thus the SAME auxiliary-game rule and comparison proof work for every
R≥2 and h>0. The second objective now satisfies
U_0=R(1−D_0), so (4) and (5) are unchanged. The raw inequality R≥2 is
exactly what makes the unperturbed pivot's Never action optimal at the
comparison point. For 1<R<2 that specific comparison law is not auxiliary
Nash. This is failure of the displayed comparison, not a proof that some
other equilibrium selected by the rule is bad.

Neither this family extension nor (6) supplies comparison equilibria for
arbitrary canonical tables. In particular, outside the family U_0 at
pivot Never need not encode D_0 monotonically, so maximizing pivot payoff
cannot silently be substituted for minimizing deleted survival.

## 5. A fixed subsidized label cannot be a universal prescription

The narrow existing-no-go lookup gives a decisive scope boundary without a
new regression search. Relabel the already proved canonical table in
`CODEX_HILBERT__CANONICAL_PIVOT_BOUNDARY_HOMOTOPY.md` so that player 2 is
its passive player. Explicitly, on every nonempty S set

    r_0(S)=1+1_(3∈S) if 0∈S; 3·1_(3∈S) otherwise;
    r_1(S)=1_(0∈S) if 1∈S; 3·1_(0∈S)−1 otherwise;
    r_3(S)=1_(1∈S) if 3∈S; 3·1_(1∈S)−1 otherwise;
    r_2(S)=0 if 2∈S; 1 otherwise.

Never pays zero, and the singletons are again (1,0,0,0). For player 2,
Never weakly dominates every finite planned Quit in the original table:
its payoff is one exactly when an active opponent absorbs before it.
The positive Never bonus makes this domination strict in the auxiliary
finite game, so every auxiliary Nash profile has p_2=Never.

The other three players' game is then unchanged. The cited note's complete
finite-menu uniqueness proof at boundary credit zero applies literally
after this relabelling: active players 0,1,3 wait to N−1, then Quit with
probabilities 1/3,1/4,1/2 respectively, otherwise Never. Its original
pivot late debt is 3/8 for every N. Therefore neither lexicographic
optimization can alter this law, for ANY positive player-2 Never bonus.

This is a specialization of an existing exact-selector obstruction, not a
new universal no-go theorem. It excludes only the fixed-label rule as a
universal arbitrary-table producer. Choosing the perturbed player from the
actual reward data, or considering a finite portfolio of different bonus
games, is not excluded. No such adaptive selection guarantee is proved here.

This fixed-label obstruction holds for every deadline and every positive
bonus, so it is not caused by the positive test's chosen relation
N=3K, ξ=4^(−K). Conversely, that relation is only a sufficient rate at
which the explicit VANISH comparison actions tie. It is not a theorem that
arbitrary tables must equilibrate on this calendar scale, nor an obstruction
to using much larger deadlines at a given small bonus.

The other nearby no-gos have different quantifiers. The older bounded own
clock-bonus test only supplies bad delayed equilibria; it does not preclude
the good optimizing branch proved above. The canonical homotopy changes
only the all-Never payoff of the pivot, not a nonpivot's private planned
action. Symmetric logit failure imposes identical nonpivot laws, whereas
this bonus deliberately distinguishes one nonpivot and uses no full-support
entropy. None invalidates the positive VANISH selector calculation.

## 6. Stop and exact next question

The new positive mechanism is a globally selected branch of an asymmetrically
perturbed finite game, with uniformly vanishing payoff change and explicit
original full-regret control. Its proof depends on two actual table facts:
the comparison equilibrium supplied by the cumulative response identities,
and the formula U_0=R(1−D_0) when the pivot Never. Neither is an arbitrary
canonical-table hypothesis available for free.

The next bounded question is whether a data-dependent choice of subsidized
nonpivot and a criterion that prices deleted survival can supply such a
comparison branch beyond this solved cyclic family. Producing a generic
auxiliary equilibrium or stipulating that a good comparison profile exists
would not answer that question. No parameter sweep, new API, or export is
part of this checkpoint.
