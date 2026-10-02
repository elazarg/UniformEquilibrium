# Independent check of the private Never-bonus selector

Reviewer: CODEX_FRECHET_CYCLE.

Status: PASS of the bounded ordinary-mathematics claim. No correction is
required. This is not a Lean check or an arbitrary-table producer result.

## Frozen surface and question

I read all 247 lines of
`notes/CODEX_HILBERT__VANISHING_PRIVATE_NEVER_BONUS_SELECTOR.md` before
forming this review. Its SHA-256 is
`2f5154dd77cf21ffc0845157f1c2fe5d329d1c84a0642ad7cbab4444b827a715`.
I did not read another review of this construction.

The claim is about a completely specified auxiliary finite normal-form
game on F_(3K). Only player 2 receives a bonus ξ=4^(−K), conditional on
its own planned action being Never, including when someone else absorbs.
The bonus is removed when evaluating the output. The selector lexicographically
maximizes p₀(Never), then original U₀, over the auxiliary Nash set. Every
remaining selected law is claimed to have original full debt at most ξ.
The table family has pivot reward R outside its coalition, own singleton
one, and the stated cyclic nonpivot rewards, with R≥2 and h>0.

The main falsification targets were all finite dates, the last phase and
Never boundary, arbitrary selected equilibria rather than the displayed
comparison point, and unrestricted omitted responses.

## Complete comparison-law calculations

Put z_k=4^(−k), J=8^(−K). In opponent-only play, each negative successor
event in a cycle has probability z_k/2 and each corresponding positive
predecessor event has probability z_k/4 when it comes second. For player 2
the positive predecessor comes first, reversing this order. Directly
integrating the reward accumulated strictly before each pure Quit date
gives the following ORIGINAL pure response values:

| Player | Quit 3k | Quit 3k+1 | Quit 3k+2 | Never |
| --- | --- | --- | --- | --- |
| 1 | 0 | 0 | −z_k/2 | 0 |
| 2 | 1−z_k | 1 | 1 | 1−4^(−K) |
| 3 | 0 | −z_k/2 | 0 | 0 |

Here 0≤k<K. A deviation that Quits simultaneously with an opponent gives
the deviator zero, so only STRICTLY earlier absorption enters this table.
This checks collisions and all nonsupport finite dates, not just the
designated support dates. Against the comparison pivot Never, the −h
rewards never enter any nonpivot's response calculation.

Consequently all player-1 and player-3 support actions already tie at zero.
Every finite support action of player 2 has value one, and its Never value
is precisely short by ξ. The private bonus therefore makes every action
in its stated support optimal. Its original expected payoff is 1−J,
while its expected bonus is ξ·2^(−K)=J.

For the pivot, if S(t) is opponents' survival strictly before t, then
the pure Quit value is R−(R−1)S(t). The largest finite value occurs at
t=3K−1, where S(t)=2J. Never pays R(1−J). Thus

    Never − largest finite value = (R−2)J.

The threshold R≥2 is exact for this comparison law. At R=2 the last
finite response ties Never; strict superiority is not needed. At 1<R<2
the displayed comparison really fails, as the author states.

The original comparison payoff is exactly (R(1−J),0,1−J,0). Hence the
comparison law is an actual independent mixed Nash equilibrium of the
auxiliary game for every integer K≥1 and every R≥2, h>0.

As a separate arithmetic falsification check, I enumerated every pure
menu response against the comparison laws with rational arithmetic for
K=1,2,3 and R=3/2,2,3. The auxiliary debts were identically zero for
R=2,3. For R=3/2 only the pivot had positive debt, exactly J/2. These
checks support, but are not substituted for, the preceding all-K proof.

## Global selector and original full caps

Finite mixed Nash existence and closedness give a nonempty compact Nash
set. Both lexicographic maxima are therefore attained. Since the explicit
comparison law has p₀(Never)=1, the first maximum is exactly one. EVERY
second-stage maximizer consequently satisfies p₀=Never and

    U₀ ≥ R(1−J).

For arbitrary opponent laws at such an output, not necessarily geometric,
write D₀ for the product of their Never masses. The pivot receives R on
every absorbing opponent coalition, including collisions. Therefore

    U₀ = W₀ = R(1−D₀),       D₀≤J.

The pivot is unperturbed in the auxiliary game, so its ORIGINAL menu cap
equals its original payoff. Every pure response at a date at least N has
payoff W₀+D₀. Hence its unrestricted debt is exactly D₀, not merely
bounded by the auxiliary regret.

Players 1 and 3 are unperturbed and have zero singleton rewards. Every
omitted late pure response equals their Never response, so their full
debts are zero. For player 2, auxiliary Nash against any menu law μ gives

    U₂(μ,p₋₂)−U₂(p) ≤ ξ[p₂(Never)−μ(Never)] ≤ ξ.

Its zero singleton again makes the complete menu cap equal to the full
cap. Thus every output has original debt vector at most (J,0,ξ,0).
The argument includes arbitrary complete behavioral deviations through
the exact stopping-law/full-cap reduction; it does not impose a bounded
deviation calendar on the final equilibrium statement.

The choice K with ξ≤ε gives the asserted all-accuracy ORIGINAL finite-law
approximate equilibria. It requires no consistency of selected laws across
accuracies. The all-errors terminal-to-uniform consumer is applicable,
although existence on this family was already known independently.

## Exact sources and scope check

The narrow route was the canonical single-pivot/actual finite-menu entries
of `docs/TOOLKIT.md`. I inspected the following named declarations:

- `IsQuittingFiniteDeadlineNash` and
  `isQuittingFiniteDeadlineNash_iff_pure` in
  `UniformEquilibrium/Quitting/Terminal/FiniteDeadlineReplyCap.lean`;
- `singlePivot_nonpivot_fullCap_eq_menuCap`,
  `singlePivot_pivot_fullCap_eq_max_menu_never_add_deletedNever`, and
  `singlePivot_pivot_fullDebt_eq_max_menuDebt_scalar` in
  `UniformEquilibrium/Quitting/Terminal/SinglePivotFiniteMenuSource.lean`.

Their menus contain dates STRICTLY below N plus Never, and their cap
identities impose no menu-Nash hypothesis. Thus they apply to the selected
auxiliary laws after evaluating them in the original table. The auxiliary
payoff itself is not asserted to be an original quitting-table payoff.

I also read the complete earlier
`CODEX_HILBERT__CANONICAL_PIVOT_BOUNDARY_HOMOTOPY.md`. Its stated uniqueness
is for ALL complete finite-menu Nash laws, not merely a backward-selected
branch. Its reach argument excludes sure absorption before applying suffix
Nash induction. Section 5 of the reviewed note uses precisely its θ=0
specialization after relabelling, not an unsupported stationary-only claim.
The older note is a complete ordinary proof draft, not a named checked
production theorem.

In that relabelled table the subsidized player 2 is passive. Original
Never weakly dominates each of its pure finite dates pointwise; adding the
positive own-action bonus makes domination strict. Thus every auxiliary
equilibrium has that player Never and leaves exactly the older active
three-player game. Its last-date hazards (1/3,1/4,1/2) yield pivot debt
3/8 for every positive deadline, independent of bonus size. This correctly
excludes the one FIXED subsidized label as a universal rule. It does not
exclude a data-dependent label or a portfolio of auxiliary games.

## Valid, false, new, and still missing

Valid: the complete comparison equilibrium, every-selected-law bound,
R≥2 family extension, and stated fixed-label scope obstruction.

No false mathematical assertion or missing proof step was found in the
frozen surface. In particular the bonus must be paid for a planned Never
even following someone else's earlier absorption; replacing it with an
all-Never terminal bonus would be a different, unproved mechanism.

The new mechanism-level conclusion is the extremally selected auxiliary
Nash branch and its original full-cap guarantee on this family. The
geometric witness and the family's equilibrium existence are not new.
There is no arbitrary-table comparison equilibrium, no general relation
between pivot payoff and deleted survival, and no general producer claim.
The next adaptive-label/portfolio question remains outside this review.
