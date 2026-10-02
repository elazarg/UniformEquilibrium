# A slack-aware solo prefix and all-player ties at a positive MAX minimum

Identity: CODEX_HILBERT. Ordinary-mathematics proof draft, not independently
reviewed or Lean-checked. The finite theorem supplies one explicit new-date
competitor in part of the actual-payoff region U≥s. Its global consequence
strengthens the two-maximal-debtor assertion to equality of every player's
debt with the maximum. Neither result resolves the all-tied region.

## 1. Exact question and surviving timing move

Let I be a finite nonempty player set, r(S) a vector of terminal rewards for
each nonempty coalition, |r_i(S)|≤M, and M>0. Infinite all-Continue pays
zero. Players use independent stopping laws on ℕ∪{Never}, and every
unilateral behavioral response is allowed. Write

    s_i=r_i({i}),       U_i=prescribed payoff,
    B_i=full unilateral response supremum,
    d_i=B_i−U_i≥0,      E=max_i d_i.

The bounded retiming test began with swaps of two literal hazard blocks.
Pure swaps/compressions that remain in the same N-domain cannot improve a
GLOBAL m_N optimizer, by the definition of that minimum. Changes to only
the pivot tail are already included in its complete inner minimization.
Neither observation is a new counterexample to a genuinely enlarged move.

The first fruitful test instead exposes one new date and lets one selected
player stop there with a small private probability, retaining the entire old
profile one date later on survival. It does not supply a successful tail,
select a best-response law, or require the new root to be Nash. It changes
the selected player's overall finite/Never masses, so it is broader than a
permutation of fixed clock atoms. This distinction is explicit: no theorem
that a survival-preserving block swap always improves has been proved.

The falsifiable claim checked here is: **if U≥s and some coordinate has
strict slack below the positive maximum m, this solo prefix strictly lowers
all full regrets below m.**

## 2. Exact unrestricted cap formula for the solo prefix

Select k and h∈[0,1]. At a new initial date k Quits with probability h,
while everyone else Continues; on survival all players use their entire old
laws shifted by one date. Private sampling realizes the product law without
public correlation. Denote the resulting semantic pair by (U',B').

For k, whose opponents certainly Continue at the new date,

    U'_k=h s_k+(1−h)U_k,
    B'_k=max(s_k,B_k).

For j≠k put a_j=r_j({k}) and b_j=r_j({k,j}). Its complete cap and payoff are

    U'_j=h a_j+(1−h)U_j,
    B'_j=max((1−h)s_j+h b_j, h a_j+(1−h)B_j).

The two cap branches are Quit immediately and Continue then use an
arbitrary complete response against the original opponents. The Never
response is included in the latter branch. This argument requires no cap
attainment and no conditional payoff on a null event.

If U≥s, then B_k≥U_k≥s_k, and these formulas become

    d'_k=d_k+h(U_k−s_k),
    d'_j=max((1−h)(s_j−U_j)+h(b_j−a_j), (1−h)d_j).
                                                               (2.1)

Thus the moved coordinate can rise, while all other high-debt coordinates
contract unless their new immediate-Quit branch becomes binding. The first
term in that maximum is at most 2Mh. This is the full cap calculation, not
an analysis of only the responses active at the old profile.

## 3. A strict one-date competitor

Suppose all d_i≤m, 0<m≤2M, U≥s, and d_k≤m−ζ with ζ>0. Set

    h=min(ζ/(4M), m/(16M)).                              (3.1)

Then 0<h≤1/8. For the moved player, U_k−s_k≤2M gives

    d'_k≤m−ζ+2Mh≤m−ζ/2≤m−hm,

where hm≤ζ/2 follows from m≤2M and h≤ζ/(4M). For every other player,

    2Mh≤m/8≤(1−h)m,
    (1−h)d_j≤(1−h)m.

Equation (2.1) therefore proves

    E(U',B')≤m−hm<m.                                   (3.2)

This is a literal independent-product move from any actual source having
the displayed properties. The moved player's old regret need not be zero,
and it need not be the canonical pivot. No Nash root is used: its own
one-stage Nash defect is exactly h(U_k−s_k). The existing generic
maximum-defect estimate can lose the useful old slack m−d_k; retaining the
coordinate formulas is what proves (3.2).

## 4. Finite global geometric-repair consequence

Now take the canonical four-player table with s=(1,0,0,0), M≥1. For N≥0,
nonpivot laws range over F_N={0,…,N−1,Never}; the pivot has an arbitrary
head before N, a geometric finite tail starting at N, and a Never atom.
Include the relaxed boundary α=0<λ, where α is the first tail atom and λ
the finite tail mass. Let m_N be the joint global repair LP minimum.

Choose any global optimizer with m=m_N>0 and U≥s. If its coordinate k has
gap ζ=m−d_k>0, the solo-prefix competitor gives

    m_(N+1)≤m_N−m_N min(ζ/(4M),m_N/(16M)).             (4.1)

For a literal optimizer the calendar bookkeeping is immediate: every old
nonpivot date shifts by one and the selected nonpivot, if any, gains an
atom at zero. All nonpivots lie in F_(N+1). The pivot's shifted tail is
still geometric; if the selected player is the pivot, its entire old law
is simply multiplied by 1−h and an atom h is added at zero. It therefore
belongs to the same geometric family at cutoff N+1. N=0 causes no problem.

For α=0<λ, choose positive-α implementations with the same U and all
debts at most their relaxed values plus ε. Keep h and k fixed. The estimates
in Section 3 gain at most ε, and every resulting competitor is still in
the SAME N+1 family. Letting ε→0 proves (4.1) as an inequality of values.
The relaxed optimizer is not assigned a nonexistent literal stopping law.

Global optimality is used only to identify the old objective with m_N and
to compare the new competitor with m_(N+1). The theorem does not assume
that a finite-domain minimizer attains the unrestricted global infimum.

## 5. Every coordinate ties at a positive unrestricted MAX minimum

Let C be the closure in finite-dimensional (U,B)-space of all actual
semantic pairs. It is compact, and its debts are nonnegative. Put

    m=min_(U,B)∈C max_i(B_i−U_i)=inf_p E(p).

Suppose m>0 and (U,B)∈C attains it. The checked MAX singleton-margin theorem
gives B_i−s_i≥m for every i. Since d_i≤m, this implies U_i≥s_i.

**Theorem.** Every player i satisfies B_i−U_i=m at this pair.

Indeed if d_k<m, choose ζ=m−d_k and the h in (3.1). The fixed-root
semantic prefix is continuous and maps C into itself. The unrestricted
cap formulas of Section 2 therefore hold at the possibly nonattained pair.
Equation (3.2) puts its prefixed pair strictly below the defining minimum,
a contradiction. Equivalently, prefix actual approximating profiles by
this fixed root; their semantic pairs converge to the strictly improved
pair, so sufficiently late approximants are actual strict competitors.

This theorem concerns every minimum pair, not a favorable selected minimum,
and holds for arbitrary signed rewards and arbitrary finite I. With one
player, all-Continue or a sure finite Quit is already exact Nash, so the
positive-minimum premise is impossible. There is no same-source actual
attainment claim.

For canonical m_N, truncating only the three nonpivot laws of an arbitrary
actual profile and then applying geometric compression proves m_N↓m.
Consequently every full semantic cluster of global repair optimizers has
all debts equal to m if m>0. This uses the actual global limit, not the
false assertion that each finite m_N optimizer already has all debts equal.

## 6. Narrow source comparison and exact limit of the test

The route was the literal-prefix and maximum-minimum entries in
`docs/TOOLKIT.md`, followed by these declarations inspected in place:

- `quittingTerminalSemanticPrefix`,
  `continuous_quittingTerminalSemanticPrefix`, and
  `quittingTerminalSemanticPrefix_mem_carrier` in
  `UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`.
- `quittingTerminalDeviationDebt_rootThenContinuation_le` and its
  coordinate-defect version in
  `UniformEquilibrium/Quitting/Root/TerminalDebtPrefix.lean`.
- `minimumTerminalSemantic_exploitabilitySingletonMargin` and
  `minimumTerminalSemantic_exploitabilityIs_allContinuePlateau` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPlateauDynamicCostate.lean`.

The latter MAX declarations yield B_i−s_i≥m and all-Continue existence at
U, not the asserted equality of every debt coordinate. The bounded search
in these MAX files, their weighted-budget neighbors, and ControllerTester
found no all-player tie theorem; this is not an exhaustive priority claim.
The minimum-SUM nonnegative-weight chamber has a different objective and
cannot be silently substituted.

The earlier two-maximal-debtor proof is Section 11 of
`CODEX_HILBERT__EXTREMAL_REWARD_TABLE_VARIATIONAL_TEST.md`; RENY's
`CODEX_RENY__MAXIMUM_DEBT_MINIMUM_TIES_AND_ACTUAL_ROOT_UNIQUENESS.md`
independently proves that fact and uses it for actual-U root uniqueness.
The present strict solo-prefix competitor uses extra temporal freedom,
not only a mixture in one old law. FRECHET's approximate-root contraction
retains a maximum root-defect budget; (4.1) instead spends the specific
owner's slack and leaves all old high-debt coordinates contracting.

The retiming-source search also inspected the player-deleted clock
definitions in `Research/Quitting/StochasticButtonUnilateralCompression.lean`.
They warn that a joint clock is not deviation-invariant; no payoff or cap
equivalence is supplied there. The full `gpt/CLOSED_REPAIR_PLATO.md` was
read as a stated no-go: its family is closed under nonincreasing unilateral
replacements, but has global value zero and is not a global m_N minimum.
Its conclusion does not exclude this new-date coordinated prefix.

This tranche does not prove a general improving two-block swap. It yields
the explicit one-date contraction (4.1) and the all-player tie consequence.
At an all-tied pair, (2.1) makes the selected owner's debt rise or stay
equal when U_k≥s_k, so the same argument stops. Constructing a coordinated
retiming move in that remaining region is still open; no fresh winning
continuation or constant refinement is supplied here.
