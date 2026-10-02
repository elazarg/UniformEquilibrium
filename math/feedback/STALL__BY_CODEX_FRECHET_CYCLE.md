# Independent review of STALL

Reviewer: CODEX_FRECHET_CYCLE.

## Verdict and reviewed surface

PASS as ordinary mathematics, with a provenance/novelty qualification rather
than a mathematical repair. The submission proves uniqueness of all finite-menu
Nash **stopping laws**, not uniqueness of complete behavioral representatives.
Its unrestricted exploitability, persistent Never masses, zero-boundary stall,
and explicit stationary equilibrium are correct. It does not give a new
conjecture-facing exclusion beyond existing all-horizon exact-menu examples.
Recommended disposition: preserve as a nonnegative-payoff regression, not a
duplicate export.

The complete original was read before feedback or comparison with other
reviews:

- `gpt/STALL.md`, 555 lines, SHA-256
  `0a8149762836946c208a07f4190e9c32340a05c52474b236fa4cbb4ad532bedb`.
- `gpt/verify_exact_menu_obstruction.py`, SHA-256
  `a1e238263ce3c762176feb5efb4cfc8ce5487ad324fe2312b533c7b24ac69522`.

The companion was read completely before execution. It passed its exact
algebra, stationary identities, and finite-response tests. It does not enumerate
all mixed equilibria; the universal uniqueness conclusion rests on the proof
checked below. No Lean build was run for this review. Named source declarations
were inspected statically; no new Lean theorem is claimed for STALL.

## 1. Table, punishment, and root identities

Players 0, 1, 2 have the following core rewards:

| Quitters | Core reward |
| --- | --- |
| 0 | (1, 3, 3) |
| 1 | (3, 0, 3) |
| 2 | (3, 3, 0) |
| 01 | (4, 1, 3) |
| 02 | (1, 3, 4) |
| 12 | (3, 4, 1) |
| 012 | (2, 2, 2) |

Spectator 3 leaves these core rewards unchanged whenever a core player quits.
Its own reward is 1 when a core player quits without it, and 0 when it joins.
The singleton 3 and Never rewards are zero. Thus every reward lies in [0,4]
and the own-singleton vector is s = (1,0,0,0).

The exact punishment vector is P = s. Player 0 guarantees at least 1 by quitting
immediately, and all-Never opponents cap it at 1. For each other player all
rewards are nonnegative, while all-Never opponents cap its payoff at its zero
singleton. These are separate unilateral bounds; no simultaneous realization
of punishment coordinates is assumed.

For core indices modulo 3, with q the core root and v its continuation,

    D_i := Q_i − C_i
         = (s_i − v_i)(1−q_(i+1))(1−q_(i−1))
           + q_(i+1) − 2q_(i−1).

The four opponent-coalition toggles verify this formula directly. The Nash
conditions are q_i > 0 ⇒ D_i ≥ 0 and q_i < 1 ⇒ D_i ≤ 0. Spectator hazard h
replaces v by (1−h)v for the core game. For spectator 3,

    Q_3 = 0,
    C_3 = H(q) + (1−H(q))v_3,
    H(q) = 1 − ∏_(i=0,1,2)(1−q_i).

These identities include all collision rows, not just singleton rewards.

No core player can quit surely at a Nash root, for any continuation: if q_i=1,
then D_(i+1)=q_(i−1)−2<0, forcing q_(i+1)=0. Then D_(i−1)=1 forces
q_(i−1)=1, after which D_i=−2 is impossible. This argument also applies with
the spectator present through the effective continuation above.

## 2. Exact roots at zero and at the resulting payoff

At continuation zero, H(q)>0: otherwise player 0 gains 1 by joining any sure
spectator or by quitting alone. Hence the spectator strictly continues. No core
coordinate can be zero. For example, q_0=0 and q_1>0 force q_2=0 through D_2,
after which D_0=1 contradicts q_0=0. If q_0=q_1=0, the inequality for player 1
forces q_2=0, again a contradiction. With q_0>0, q_1=0 would force q_2=1,
already excluded; then D_1 forces q_2>0.

Thus all three coordinates are interior and all three D_i vanish. Writing

    θ = 3/2 − √2,

the unique admissible solution is

    q* = (2θ, θ, 4θ, 0),
    4θ² − 12θ + 1 = 0.

The other quadratic root is inadmissible. The resulting payoff is

    u_i = 3[1 − ∏_(j≠i, j<3)(1−q*_j)]  (i<3),
    u_3 = H(q*).

Every coordinate satisfies u_i>s_i. At continuation u, spectator 3 strictly
continues at every root. If a core coordinate q_i were positive, its Nash
inequality and u_i>s_i would imply q_(i+1)>2q_(i−1). Positivity propagates
around the cycle and summing gives a contradiction. Hence all-Continue is the
unique exact Nash root at u. The same argument works throughout the open
region v_i>s_i for core players and v_3>0; this is a genuine strict basin.

## 3. All finite-menu Nash laws, including the zero-reach issue

Let N≥1 and F_N={0,…,N−1,Never}. Strategies are independent private stopping
laws. An arbitrary strategic-game Nash profile need not initially be assumed
subgame-perfect. The submission correctly supplies the missing reach argument.

Suppose k were the first row with zero joint continuation. Before k the joint
live probability is positive. One-date changes followed by a fixed legal
finite-menu continuation are unilateral stopping-law deviations, so the root
at k is Nash against its chosen actual continuation. The no-sure-core argument
excludes every core player as a sure quitter. Therefore spectator 3 must be
sure. Its actual continuation payoff is nonnegative. Its Nash inequality
0=Q_3≥C_3≥H(q) forces every core player to continue. But then player 0 can
join the sure spectator and obtain 1 instead of 0, a contradiction.

Consequently every live row before the deadline has positive joint
continuation. At each such row a unilateral replacement of a conditional
suffix changes initial payoff by joint reach times the suffix payoff change.
An improving conditional deviation would therefore improve the original
strategic-game payoff. This is exactly why ordinary Nash, without an added
sequential-equilibrium requirement, licenses backward induction here.

The last row has continuation zero, hence root q* and payoff u. Every preceding
row has continuation u, hence is all-Continue. Therefore every exact mixed
Nash law equals

    p_i = q*_i δ_(N−1) + (1−q*_i) δ_Never,
    p_3 = δ_Never.

Existence follows by the same recursion, checking each permitted suffix
response. This is uniqueness of product stopping laws. Actions after absorption
and other strategically irrelevant parts of a behavioral representative remain
unconstrained. N=0 is a separate trivial all-Never menu, not covered by the
displayed positive-deadline classification.

The relevant general source bridge is
`timingLawTail_isNash_of_isNash_of_positiveContinue`, with the payoff identity
`timingMixedPayoff_withTail_sub`, in
`UniformEquilibrium/Diagnostics/Quitting/FiniteDeadlineTimingRecursion.lean`.
The declarations explicitly require positive current continuation and do not
assume a subgame-perfect refinement. This requirement has been proved, not
silently dropped, for STALL.

## 4. Complete behavioral caps and the two Never masses

Set

    β = (1−θ)(1−4θ) = 7θ = 21/2 − 7√2 > 1/2,
    ρ = (1−2θ)β = 35√2 − 49 > 0.

The unique exact-menu laws use Never with positive probability for player 0.
Thus its equilibrium payoff equals its Never response payoff u_0. Quitting at
any date t≥N adds exactly β: the other three players all Never with probability
β and player 0's singleton is 1. Every original-menu response pays at most u_0.
Hence its full unrestricted debt is β. Every other player's singleton is zero,
so every newly available post-deadline finite response agrees with Never; their
full debts remain zero. Therefore

    (d_0,d_1,d_2,d_3) = (β,0,0,0),
    E = β,
    Pr(all four Never) = ρ.

This is a complete-response statement: with opponents fixed, every unilateral
behavioral response induces a stopping law and its payoff is a mixture of pure
finite-date and Never payoffs. There is no omitted off-path behavioral gain.

Three numerical roles should remain distinct. β is deleted-player-0 Never
mass and, coincidentally for this table, the sum of marginal hazards at q*.
ρ is joint all-player Never mass. The root's actual absorption probability is
1−ρ, not β. All three are deadline-independent positive constants.

The exact production cap decomposition is in
`UniformEquilibrium/Quitting/Terminal/SinglePivotFiniteMenuSource.lean`:
`singlePivot_nonpivot_fullCap_eq_menuCap`,
`singlePivot_pivot_fullCap_eq_max_menu_never_add_deletedNever`, and
`singlePivot_fullExploitability_eq_max_menuExploitability_scalar`.
The corresponding exact-menu debt declarations also apply to these formulas.

## 5. Anchored stall versus an actual stationary equilibrium

For a finite exact root/Bellman block with terminal annotation zero, the unique
backward roots are q* at the final row and all-Continue at earlier rows. Its
total marginal-hazard sum is β and its total absorption sum is 1−ρ, regardless
of length. At every fixed date the finite-menu hazards converge to
all-Continue while the backward annotations equal u. The actual all-Continue
tail payoff is zero, not u. The claimed zero-boundary phantom is therefore
correct; it is not an actual realization of the limiting annotations.

The boundary condition matters. The same game has the actual stationary root

    q̄ = (1/4,0,0,0),   v = (1,3,3,1),   b=3/4.

Against continuation v its Quit payoffs are (1,1/4,1,0), and its Continue
payoffs are v. Thus it is exact supported-row-perfect and satisfies Bellman
equality. Every restart absorbs geometrically with survival b^t.

The unrestricted response verification does not rely only on row perfection.
Player 0 faces all-Never opponents: every finite date pays 1 and Never pays 0.
For j=1,2, quitting at t pays

    3(1−b^t) + (1/4)b^t r_j({0,j}) ≤ 3,

while Never pays 3. Spectator 3 obtains 1−b^t by quitting at t and 1 by Never.
These exhaust pure finite and Never responses, hence all behavioral deviations.
The displayed profile is an exact unrestricted terminal Nash equilibrium.

Truncating this stationary pivot after N dates gives

    U = (1−b^N)(1,3,3,1),
    d_0 = b^N,
    d_1 = d_3 = 0,
    d_2 = (1/4)b^(N−1),
    E = b^N.

For example, player 2's best finite date N−1 pays 3−2b^(N−1), versus
3−(9/4)b^(N−1) for Never. Player 1's corresponding finite payoff is
3−(11/4)b^(N−1), below Never. Thus the stated full-cap estimates include the
last-date collision and are correct.

The actual stationary self-loop can be repeated for arbitrary charge from its
own payoff v. Accordingly the zero-terminal-boundary result is not a bound on
free-start exact forward capacity and is not a forward-packet impossibility.

## 6. Exact comparison with prior results

The submission's comparison to a one-date regression is insufficient as a
novelty account. The relevant stronger predecessors are:

1. `notes/CODEX_ROOT__CANONICAL_EXACT_MENU_OBSTRUCTION_SOURCE.md` preserves the
   earlier EXACT_EXAMPLE theorem, independently reviewed in
   `feedback/EXACT_EXAMPLE__BY_CODEX_FRECHET_CYCLE.md`. It already proves all-N
   uniqueness for canonical singleton vector (1,0,0,0), exact full debt 18/49,
   fixed positive joint Never mass 90/343, a strict all-Continue basin, and an
   explicit geometric approximate bypass. Its unique last root is
   (2/7,4/7,1/7,0). The same zero-anchored stall/phantom conclusion follows
   immediately from its proved root classification. Its table also has P=s:
   pivot Quit guarantees 1, core nonpivots have nonnegative rewards, and the
   spectator can guarantee 0 by Never; all-Never opponents give the matching
   upper bounds. Exact punishment equality is therefore not a new separation.
2. `notes/CODEX_RENY__CANONICAL_EXACT_FINITE_MENU_SEPARATION.md` proves another
   reviewed ordinary all-N canonical example (the VANISH family), including no
   finitely supported exact Nash despite an infinite exact equilibrium. Its
   earlier HILBERT predecessor is a complete but unreviewed draft, not a
   separately checked production theorem.
3. The production declarations `existsUnique_finiteDeadlineTimingNash`,
   `finiteDeadlineTimingNash_exploitability_eq_hardDeadlineDebt`, and
   `quarter_lt_finiteDeadlineTimingNash_exploitability` in
   `UniformEquilibrium/Diagnostics/Quitting/FinFourHardDeadlineTimingNashUniqueness.lean`
   already give every-deadline uniqueness and an every-selector unrestricted
   debt barrier for a different, noncanonical hard-deadline table. Their
   quantifiers range over all mixed Nash laws, not merely a backward-selected
   sequence. These source declarations were inspected; this review did not
   rerun their Lean builds.

The general unique-all-Continue propagation mechanism also has a production
home: `quittingAnchoredPath_backward_rigidity_of_unique_allContinue` and
`quittingAnchoredPath_root_eq_allContinue_and_absorption_eq_zero` in
`UniformEquilibrium/Quitting/Bellman/Finite/AllContinueBasinRigidity.lean`.
The table-specific entrance q*→u remains STALL's calculation.

What STALL adds is a compact, entirely nonnegative [0,4] reward table and clean
cyclic algebra realizing these phenomena. The irrational root and stronger
numerical debt threshold are fixture refinements, not elimination of another
previously live exhaustive route. The strict basin is real but not new in scope.

## 7. Conjecture-facing disposition

`questions/FIN4_SINGLE_PIVOT_FINITE_MENU_SELECTION.md` asks for a menu size and
one profile with both small menu regret and a small late-pivot defect. It does
not require exact finite-game Nash. Its text explicitly says that failure for
every exact finite-menu selector is not a negative answer unless approximate
selectors and complete behavioral profiles are excluded. STALL's own truncated
geometric laws meet the approximate target. No question correction is needed.

The broader free-start forward-packet question likewise does not prescribe a
zero terminal annotation. The actual stationary v self-loop directly prevents
using STALL's anchored stall against that question. Independently, all three
nonpivots Never and a geometric pivot starting after any finite deadline give
the same exact terminal equilibrium; the compensated/geometric route is not
excluded either.

There is no unresolved mathematical objection to the submitted fixture at its
stated scope. There is no new arbitrary-table producer, no all-behavior positive
gap, and no new negative answer to the current approximate finite-menu question.
Under `exports/README.md`, a duplicate all-exact-selector obstruction with a
nonnegative-table refinement does not justify a new export. Preserve the
regression and the qualifications above; no further proof program is needed
for this intake.
