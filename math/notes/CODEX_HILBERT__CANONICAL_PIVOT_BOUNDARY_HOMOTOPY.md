# Canonical pivot boundary credit and exact-menu selection

Identity: CODEX_HILBERT. Status: complete ordinary-mathematics proof draft,
with exact symbolic arithmetic checked separately. No independent review,
Lean implementation, export, or general approximate-selection impossibility
is claimed.

## Question and current decisive result

For four-player quitting tables with own singletons (1,0,0,0), test the
auxiliary finite timing game that changes ONLY all-Never payoff to θe₀,
0≤θ≤1. All terminal rewards remain original. Can choosing its exact Nash
equilibria control original finite-menu error and omitted pivot debt?

The following explicit table has exactly one such Nash product
law at EVERY deadline. Consequently an extremal selection among exact Nash
equilibria cannot change its law. At θ=0 its original unrestricted debt is
3/8 at every deadline, solely for the pivot. More generally, no choices of
deadlines and credits θ can make BOTH the original finite-menu error and
original pivot late debt vanish along these auxiliary exact Nash laws.
The table nevertheless has an
exact periodic terminal Nash profile. Thus the stronger exact-menu selection
target fails; this does not refute approximate-menu selection.

## Exact table and branch

Active players are 0,1,2, with predecessor i−1 modulo three. For nonempty S:

    r₀(S) = 1+1_{2∈S} if 0∈S; 3·1_{2∈S} otherwise;
    rᵢ(S) = 1_{i−1∈S} if i∈S; 3·1_{i−1∈S}−1 otherwise, i=1,2;
    r₃(S) = 0 if 3∈S; 1 otherwise.

Never in the ORIGINAL game pays zero. Own singletons are exactly e₀.
This is the previously recorded positive-singleton cyclic table shifted by
one in coordinates 1,2,3 on terminal outcomes ONLY. All-Never opponents
show punishment normality directly, without using that transformation.

Let 0<y≤1/2 and θ=(1−4y²)/(1−y²). At T=N−1 the active Continue masses are

    a₀=1/(1+y),  a₁=(1+y)/(1+2y),  a₂=1−y;

each active player chooses T with probability 1−aᵢ and Never otherwise.
Player 3 chooses Never. All Continue at dates before T. The equations are

    2a₂−1=θa₁a₂,
    2a₀−1=a₀a₂,
    2a₁−1=a₀a₁.

The auxiliary continuation values immediately before T are

    v=(1+y, y/(1+y), y/(1+2y), 1−R),
    R=a₀a₁a₂=(1−y)/(1+2y),  D₀=a₁a₂.

All earlier pure Quits give own singleton, strictly less than v. Thus this
is an actual Nash law on the whole menu, not merely a root comparison.

## Uniqueness against all finite-game selectors

At any reached row, no active player can Quit surely: q₀=1 forces q₁=0,
then q₂=1, then q₀=0; the two cyclic variants are identical. These comparisons
are independent of the suffix, because another named player quits surely.
If player 3 quits surely, any positive active root hazard makes its Continue
strictly better (reward 1 on active absorption, nonnegative suffix payoff).
If all active hazards are zero, pivot Quit gains 1 against the sure dummy,
contradiction. Hence every reached root has positive joint Continue chance.

The same argument applies inductively to every reached date. It follows
every suffix is literally reached and must itself be finite-menu
Nash: copy the prefix and change only the conditional suffix law. This
justifies backward induction without imposing subgame perfection off path.
The ex-ante gain is exactly joint prefix reach times conditional gain;
independence is retained by conditioning each marginal on its own survival.
At each reached row, the prescribed current marginal is consequently Nash
against changing that current action while retaining the conditional tail.

At the final date, some active hazard is positive for θ<1; otherwise pivot
Quit beats Continue. Hence player 3 strictly chooses Continue. The active
root gaps are

    Δ₀=1−2q₂−θa₁a₂,
    Δ₁=1−2q₀−a₀a₂,
    Δ₂=1−2q₁−a₀a₁.

Sure hazards are already excluded. The remaining boundary cases are:

- If q₀=0 and q₂>0, then Δ₁=q₂>0 forces q₁=1, which forces q₂=0.
  Hence q₂=0, but then Δ₀=1−θa₁>0 forces q₀=1.
- If q₁=0, the first case gives q₀>0; then Δ₂=q₀>0 forces q₂=1,
  already excluded.
- If q₂=0, then Δ₀>0 forces q₀=1, already excluded.

Thus all active hazards are interior. Their equalities
give exactly the displayed y branch: with a₂=1−y,
a₀=1/(1+y), a₁=(1+y)/(1+2y), and θ=(1−4y²)/(1−y²).
This parametrization is one-to-one from y∈(0,1/2] to θ∈[0,1).
Indeed θ′(y)=−6y/(1−y²)²<0, with endpoint values one and zero.

At any preceding date whose suffix payoff is v, dummy Quit yields 0 and
Continue is strictly positive, so q₃=0. For active players the root gaps are

    Δ₀=1−2q₂−a₁a₂v₀,
    Δ₁=1−2q₀−a₀a₂(1+v₁),
    Δ₂=1−2q₁−a₀a₁(1+v₂).

Since v₀>1,v₁>0,v₂>0, any zero active hazard forces the other two zero.
Explicitly, q₀=0 gives Δ₂=a₁(1−v₂)−1<0, so q₂=0;
then Δ₁=−v₁<0 gives q₁=0. If q₁=0, then
Δ₀=a₂(2−v₀)−1<0, so q₀=0 and the first case applies.
If q₂=0, then Δ₁=a₀(1−v₁)−1<0, giving q₁=0.
The strict inequalities hold also when their parenthesized coefficient is
negative, since aᵢ∈[0,1]. Sure hazards are already excluded.
At an interior root the equalities imply

    v₀a₁ = 2−1/a₂ ≤ a₂,
    (1+v₁)a₂ = 2−1/a₀ ≤ a₀,
    (1+v₂)a₀ = 2−1/a₁ ≤ a₁.

Multiplication forces v₀(1+v₁)(1+v₂)≤1, contradicting the strict floors.
Thus all active hazards are zero. Backward induction proves uniqueness of
the complete product law, including the dummy's law, at every finite menu.

At θ=1, the unique last-stage Nash is instead all-Continue. To see this,
the same boundary analysis rules out any positive hazard with one zero
active hazard: q₀=0 forces q₂=0 and then Δ₀=q₁ forces q₁=0;
the other zero cases reduce to this one. If all active hazards were interior,
the three displayed multiplicative inequalities with coefficients all one
would force equality in 2−1/aᵢ≤aᵢ, hence aᵢ=1, a contradiction.
If all active hazards are zero but the dummy has positive hazard, pivot
Quit yields 1 whereas Continue yields at most 1−q₃<1. Thus q₃=0.
The continuation is again (1,0,0,0), so induction proves the unique full
law is all-Never at every deadline. This verifies the homotopy endpoint
rather than inferring its selectors from a limit.

## Original-game errors and surviving approximate route

Nonpivot payoffs are unperturbed; their original full caps equal their menu
caps since their singleton rewards are zero. Their full debts vanish.
For the pivot, its original menu cap is 1+y, Never value W₀=3y, and

    E_menu = θR,
    L₀ = W₀+D₀−U₀ = D₀[1−θ(1−a₀)].

Here L₀−E_menu=(1−θ)D₀≥0, so full debt equals L₀. At θ=0, y=1/2,
E_menu=0 and L₀=3/8. As θ↑1, y↓0, both E_menu and L₀ tend to 1.

This falsifies a SPECIFIED global selection mechanism, not just an
every-selector inference from existence: at each N and θ select a Nash law
minimizing R (or L₀), or maximizing the pivot payoff. The feasible Nash set
is a singleton, so all these selections produce exactly the same law.
Even allowing arbitrary deadline-dependent θ_N cannot repair the mechanism.
For θ<1, R≥1/4, so E_menu=θR→0 forces θ→0, whence L₀→3/8.
An infinite θ=1 subsequence instead has E_menu=1. There is therefore no
sequence of exact Nash profiles of these auxiliary games with both desired
original-game errors tending to zero.

For completeness, the successful infinite profile has active owner i at
phase i modulo three, quitting with probability 1/2; all others Continue.
Its three phase-value vectors in the PRESENT canonical table are

    v⁰=(1,1,0,1),  v¹=(1,0,1,1),  v²=(2,0,0,1).

Each vector is exactly half the owner's singleton payoff plus half the next
vector. The owner's Quit and Continue values agree. The successor's Quit
value is 1/2 below its Continue value; the remaining active nonowner is
indifferent. Dummy Continue pays 1 and Quit pays 0. These comparisons hold
at every phase. Under any complete unilateral deviation, at least two active
opponent hazards per cycle remain, so deleted survival contracts geometrically.
Bounded Bellman comparison therefore caps every unrestricted response by
the displayed value. This proves exact terminal Nash directly.

Each active marginal's mass beyond the first 3m dates is 2^(−m). Move those
tails to Never, separately for each player. The total marginal variation
tends to zero, uniformly bounding both prescribed payoff differences and
every unilateral-deviation payoff difference by the elementary product
coupling. Hence the resulting laws on F_(3m) have vanishing FULL regret,
and therefore vanishing menu error and pivot excess. Exact and approximate
menu selection are genuinely different on this SAME canonical table.

## Source comparison and exact novelty limit

The route chosen through `docs/TOOLKIT.md` is the actual finite timing menu
and displayed reply-cap interface. I inspected:

- `quittingFiniteDeadlineReplyCap`, `IsQuittingFiniteDeadlineNash`, and
  `isQuittingFiniteDeadlineNash_iff_pure` in
  `UniformEquilibrium/Quitting/Terminal/FiniteDeadlineReplyCap.lean`;
- `timingLawTail_isNash_of_isNash_of_positiveContinue` in
  `UniformEquilibrium/Diagnostics/Quitting/FiniteDeadlineTimingRecursion.lean`;
- `timingNash_unique_and_payoff`, `existsUnique_finiteDeadlineTimingNash`,
  `finiteDeadlineTimingNash_exploitability_eq_hardDeadlineDebt`, and
  `quarter_lt_finiteDeadlineTimingNash_exploitability` in
  `Diagnostics/Quitting/FinFourHardDeadlineTimingNashUniqueness.lean`;
- that theorem's exact `reward`, `solo_reward_zero`, and the other three
  `solo_reward_*` declarations in
  `Diagnostics/Quitting/FinFourHardDeadlineTimingNashBarrier.lean`;
- the worst-table supremum and limit in
  `Diagnostics/Quitting/FinFourHardDeadlineTimingNashWorstCase.lean`;
- `nonUniqueNashProfile_isNash` and its exact alternate profile in
  `Diagnostics/Quitting/FixedPrefixTimingNashNonuniqueness.lean`.

The conditional-tail argument is already checked for original zero-Never
menus; its proof by the exact joint-reach gain factor applies unchanged to
the finite auxiliary boundary θe₀ used here. That extension is ordinary
mathematics here, not a claim about the existing declaration's telescope.

Selection-independent exact-menu barriers in GENERAL reward tables are
already known. In particular the checked hard-deadline table has own
singletons (1/2,−1,−1,−1), one pivot debt, unique complete finite Nash laws,
and a positive debt floor at every deadline. The recent sharp parametric
version in `gpt/ATTEMPT_SHARP_FINITE_DEADLINE_CEILING.md` likewise has negative
nonpivot singletons and proves uniqueness, not just a bad branch. No new
general no-go or constant improvement is claimed here.

The present strengthening is the canonical singleton vector e₀ (hence
automatic all-player normality), together with a complete test of the
specified all-Never boundary-credit selection mechanism. It is not obtained
by transporting the old bad equilibrium through the new normalization:
that transformation does NOT transport finite-menu Nash laws.
Indeed directly subtracting its three −1 singleton rewards on terminal
outcomes and dividing by 1/2 turns the CHECKED old hard-deadline table into
a canonical table with a pure terminal Nash: player 1 Quit0, all others Never.
The payoff is (2,0,2,2); pivot joining yields 0 instead of 2, player 1 has
only payoff zero against all-Never opponents, and each dummy joining yields
zero instead of 2. Every late pure date gives the same payoff as Never
against the sure first quitter. Thus normalization destroys that old
exact-menu obstruction on this concrete table.

The fixed-prefix packet's separate nonuniqueness correction concerns yet
another table and is not a falsifier of the uniqueness proof here. We have
explicitly excluded off-path dummy exits and proved literal reach of every
finite suffix before applying induction.

## Remaining scope

This tranche stops at the exact mechanism-level falsifier. The canonical
approximate-menu selection question remains open; it succeeds on this test
table via the explicit periodic construction. No new general producer was
obtained from the boundary homotopy. An independent check, if requested,
should attack the no-sure-root and backwards uniqueness arguments before
considering any export qualification.
