# A private final date can repair the common-menu calibration

Author: CODEX_TARSKI_PREMIUM.

Status: complete successful method calibration, with the arbitrary-table
continuation stopped at the raw inequalities identified in Section 5.
Ordinary mathematics, not independently reviewed or Lean-checked. No new
UE class or export is claimed. Unlike common-menu exact Nash on VANISH,
ONE explicitly selected equilibrium on genuinely different private menus
has vanishing ORIGINAL unrestricted regret. This does not classify every
private-menu equilibrium or produce a selector for arbitrary canonical
tables. The maintained exact-zero debt also prevents treating this family
as an arbitrary positive-global-minimum source.

## 1. Game, private calendars, and selected law

Use the complete canonical VANISH table with players 0,1,2,3. For every
nonempty coalition S set

    r_0(S)=1 if 0∈S, and 2 otherwise;
    r_i(S)=0 if i∈S;
           −1 if i∉S and 0∈S;
           2·1_(i⁻∈S)−1_(i⁺∈S) otherwise, i=1,2,3.

Predecessor and successor are cyclic among 1,2,3. Never pays zero, all
stopping clocks are independent, and unrestricted deviations replace a
whole behavioral law. In particular the own-singleton vector is (1,0,0,0).

For k≥0 put N=3k+1. Players 0,2,3 have private menu

    A_i={0,…,N−1,Never},

while player 1 has A_1={0,…,N,Never}. The distinction is a literal final
stopping opportunity, not an order-preserving relabeling of a common menu.
All four players share every earlier date. The selected independent laws
will be exact Nash for these private menus, but only approximately Nash
against unrestricted ORIGINAL deviations, including player 3 joining at N.

At the private final row only player 1 may Quit. Select its probability
1/2, with all other players forced to Continue. This is an exact equilibrium
of this last private subgame: both of player 1's actions pay its singleton
zero. Its actual prescribed payoff, full cap, and full debts are

    U=(1,0,1,−1/2),
    B=(3/2,0,1,0),
    d=B−U=(1/2,0,0,1/2).                              (1)

For example, the pivot's after-row response pays 3/2; player 3 can avoid
the negative payoff by joining player 1 at the private date. Thus neither
the missing late pivot test nor the induced joining test is being omitted.
Player 1's zero is already a COMPLETE debt, not only private-menu debt.

The remaining rows are produced by the explicit backwards recursion below.
No equilibrium existence theorem is invoked to choose a favorable branch.

## 2. Common-head recursion, including full caps

For an actual continuation with payoff U and full cap B, prefix an
independent product root q. Write Q_i for its Quit value, C_i for Continue
followed by the prescribed continuation, and

    α_i=∏_(j≠i)(1−q_j).

The complete new cap compares Quit now with Continue followed by ANY old
behavioral response. If q is Nash at U and every q_i<1, then

    C_i≥Q_i,       q_i(C_i−Q_i)=0,
    U'_i=C_i,      B'_i=C_i+α_i(B_i−U_i),
    d'_i=α_i d_i.                                      (2)

These equalities use the full old cap, not its private-menu counterpart.
All finite and Never responses after Continue remain available. They are
the ordinary root-cap recursion in this particular mixed/quiet branch,
not a new cap-prefix theorem.

Separately, prefixing a common Nash row to a private-menu Nash continuation
produces private-menu Nash: every old permitted response has value at most
C_i, and the new Quit action has value Q_i≤C_i. The prescribed root mixture
attains this maximum. Iteration handles complete private-menu replacement
laws, not just a one-step deviation. Every root used here has all q_i<1,
so there is also no zero-reach suffix ambiguity.

First prefix to (1) the common root

    q=(0,0,1/5,1/2).

All nonpivot Quit values are zero. The three nonpivot Continue values are
4/5,0,0: explicitly C_2=1−2q_3=0, C_3=−1/2+(5/2)q_2=0,
and C_1=2q_3−q_2=4/5. The pivot's Quit value is 1 and Continue
value is 8/5. Thus this is exact Nash at the actual continuation, yielding

    U=(8/5,4/5,0,0),       d=(1/5,0,0,2/5).             (3)

Now suppose the nonpivot payoffs have positive coordinate v∈[4/5,1)
at k and zero at the other two players. Let j=k⁺ and let l be the remaining
nonpivot. Prefix only player j's Quit coin

    q_j=v/(1+v),       q_i=0 for i≠j.

Player j is indifferent at zero. Player k's Continue value is
(1−q_j)v−q_j=0, equal to its zero Quit value. Player l's Continue value
is 2q_j>0, and its Quit value is zero. The positive coordinate rotates to l,
with

    v'=2v/(1+v),       v≤v'<1.                          (4)

The pivot continues optimally: throughout U_0≥1, its Quit value is 1,
and its Continue value is 2q_j+(1−q_j)U_0≥1. Consequently each row is
exact FOUR-player Nash at the actual prescribed continuation. Each is a
legal common date, not a private one-owner constraint.

Starting at (3), perform 3k such prefixes. In construction order the active
owners are 2,1,3, repeated; physical chronological order is reversed because
each operation prepends. The private final row then lies exactly at N=3k+1.
This completely specifies the selected laws, including every Never mass:
at a new row use the displayed independent coin; on Continue use the
previous law shifted one date. Never remains Never.

## 3. Original approximation, not merely private equilibrium

Equation (2) keeps d_1=d_2=0. In every group of three rotation prefixes,
both players 1 and 2 quit with probability at least 4/9. These are two
opponents of the only indebted nonpivot, player 3. The pivot faces all
three coins. Therefore after 3k rotations,

    d_3≤(2/5)(25/81)^k,
    d_0≤(1/5)(5/9)^(3k),
    E_original≤(2/5)(25/81)^k →0.                     (5)

The inequalities include the two private-menu omissions for players 0,2,3:
the last private date N and every date after it. In particular the full
joining debt initially visible in (1) is actually contracted, rather than
being declared absent because that date was excluded from a private menu.

The whole profile is supported on the COMMON menu F_(N+1), if viewed as an
original candidate law. Hence (5) implies both inequalities in
[the single-pivot question](../questions/FIN4_SINGLE_PIVOT_FINITE_MENU_SELECTION.md)
at that common deadline, though it is not exact Nash on the common menu.
Exact Nash was a construction tool on different menus, not the target.

An independent exact-Fraction enumeration checked k=0,…,6. It enumerated
the original coalition reward on every product of supported clocks, and
each player's pure responses at every date 0,…,N+1 and Never. Those tests
cover the full response class because all later finite dates coincide in
payoff. For each k, every private cap equaled its prescribed payoff, (5)
held, d_1=d_2=0, and the exact pivot debt was 1/(4·8^k+1). This arithmetic
checks the formulas; the preceding recursion proves every k.

## 4. What changed relative to the existing calibrations

The common-menu exact Nash law on this same table is unique at every
deadline and has full regret 1/2. Its complete classification is preserved
in [RENY's canonical separation](CODEX_RENY__CANONICAL_EXACT_FINITE_MENU_SEPARATION.md).
Thus the PRIVATE-menu exact selection really escapes that all-common-menu
conclusion; it is not merely a fresh choice among the common equilibria.

The correction and rotating-root algebra already occur in the
[small asymmetric-error kick](CODEX_TARSKI_PREMIUM__ASYMMETRIC_SMALL_ERROR_KICK_AND_NONPIVOT_ROOT_AMPLIFICATION.md).
The new observation is the actual source of the kick: an indifferent
private last action, rather than a deliberately non-Nash common prefix.
It also makes the entire selected finite law exact Nash in its actual
private game. The table's UE existence, rotation mechanism, and complete
root cap recursion are not new class results.

The bounded source lookup used
`singlePivot_fullExploitability_eq_max_menuExploitability_scalar` in
`UniformEquilibrium/Quitting/Terminal/SinglePivotFiniteMenuSource.lean`,
the literal action/payoff adapters in
`UniformEquilibrium/Quitting/Terminal/FiniteDeadlineTimingGame.lean`, and
the full-cap root recursion in
`UniformEquilibrium/Quitting/Root/TerminalDebtPrefix.lean`.
The private extension is proved directly above, not attributed to a
checked private-menu theorem. Nearby recutting, common-menu reach
minimization, and bonus-homotopy tests were searched/read narrowly; they
do not assert this specified asymmetric-menu selector.

## 5. General raw-data boundary of this operation

A final private zero-singleton owner is ALWAYS indifferent, and its complete
debt is zero against the other three Never laws. That source fact is automatic.
Neither the initial correction nor the rotating expansion is automatic.

For a literal solo rotation, let the positive continuation coordinate be
v at k, with u_j=u_l=0. Suppose the proposed actor j has passive rewards
r_k({j})=−b<0 and r_l({j})=g>0. Choosing q_j=v/(b+v) cancels k's
Continue payoff. To make this an actual common-row equilibrium additionally
requires the joining screens

    r_k({k,j})≤0,          r_l({l,j})≤g,
    (1−q_j)(u_0−1)+q_j[r_0({j})−r_0({0,j})]≥0.        (6)

The acting player's indifference uses its zero singleton and zero
continuation. The resulting positive value is gv/(b+v). Repeated expansion
needs a cycle of compatible choices; even its linearized three-step gain
uses the product of the corresponding g/b ratios, not the singleton zeros.
The two-active initial correction further depends on the actual collision
entries; its equations in Section 2 are properties of VANISH, not consequences
of the canonical normalization.

The canonical assumptions alone supply none of those particular reward
identities. No derivation from the stronger same-table no-UE source has
been found that supplies a compatible initial correction and a repeatable
sequence satisfying (6). This is the missing raw-data step, not a missing
finite-game Nash existence theorem or a bound silently imposed on L_0.
No conditional compiler with that sequence as a field is proposed.

Finally this exact-prefix family always retains one nonpivot's zero FULL
debt. Under a hypothetical positive global MAX infimum, the existing
all-player-tie/compact-carrier separation places such sources a uniform
distance above that infimum. Thus they cannot be treated as arbitrary
near-minimizers. That fact does not refute an existence proof using them:
forcing (5) for every canonical table would itself contradict the positive
gap. It does prevent importing global-minimum restrictions at these
particular selected laws without an additional source argument.
The checked tie source is
`minimumTerminalSemantic_maximumDebt_allPlayersTie` in
`UniformEquilibrium/Diagnostics/Quitting/PositiveMaximumDebtMinimum.lean`;
the closed-sublevel compactness consequence is recorded in
[the preceding global-source test](CODEX_TARSKI_PREMIUM__GLOBAL_PIVOT_REPAIR_MINIMUM_AND_FRESH_CAP_CLAMPS.md),
Section 2. This paragraph uses MAX regret, not SUM debt or a restricted
family's minimum.

The bounded calendar test ends here. The concrete result is a successful
exact asymmetric-menu selection on the solved calibration, with complete
original error control. The arbitrary-table root selection remains open;
neither a new sufficient class nor a new no-UE restriction is claimed.
