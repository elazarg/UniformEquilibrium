# Bounded private timing incentives and the all-selector reach theorem

Identity: CODEX_HILBERT. Status: ordinary mathematical proof of a concrete
failure of selector forcing. No contradiction to the robust no-uniform-payoff
reach theorem is obtained. No Lean implementation or export is proposed.

The finite-error transfer is valid uniformly in the deadline. Nevertheless,
on the explicit all-positive-singleton Fin4 table below, every sufficiently
small action-only timing perturbation still admits a fully delayed finite
Nash branch. In particular a small penalty on planned Never leaves literal
Never masses and positive ORIGINAL-game unrestricted debt. The table is
solved by an exact periodic terminal Nash profile, so this is not a
counterexample under the no-uniform-payoff hypothesis.

## 1. Question and reviewed source

RENY Section 12 asserts that for a fixed Fin4 table with no uniform payoff,
there are H≥1, e_*>0, and ρ>0 such that EVERY independent finite timing
e_*-Nash profile at EVERY N≥H satisfies R(N−H)≥ρ. The constants precede
both the deadline and the selector. I read that section and the complete
independent review
`feedback/CODEX_RENY__APPROXIMATE_FINITE_TIMING_NASH_AND_REACH__BY_CODEX_SKEPTIC.md`
before this test.

The proposed attack is to perturb the auxiliary finite normal-form game by
uniformly small own-action bonuses, use finite Nash existence, and attempt
to force early absorption. These bonuses are not changes of quitting
terminal rewards. In particular an own planned finite date receives its
bonus even if another player absorbs earlier. All actual payoffs, caps,
and reach below are evaluated in the ORIGINAL quitting game.

The inspected route is the finite timing encoding and its imports:

- `quittingFiniteDeadlineTimingGame`,
  `quittingTerminalPayoff_finiteDeadlineTimingProfile_eq_mixedEU`, and
  `quittingFiniteDeadlineTimingProfile_update_pureTime_eq_mixedEU` in
  `UniformEquilibrium/Diagnostics/Quitting/FiniteDeadlineTimingGame.lean`;
- `KernelGame.mixed_nash_exists` in
  `UniformEquilibrium/ProofView/Concepts/Existence/NashExistenceMixed.lean`;
- the already inspected complete stopping-law/pure-time cap adapter in
  `UniformEquilibrium/Quitting/Paths/CounterfactualStoppingLaw.lean`.

A narrow search in the finite-deadline, retained-tail timing, and deadline
cap-selection files found no existing own-action incentive theorem used
here. This is not a repository-wide novelty claim.

## 2. Uniform original-error transfer

Write A_N={0,…,N−1,Never}. Let F_i(a) be the original pure timing payoff,
and let β_i:A_N→ℝ be any deterministic own-action bonus. Define

    F̃_i(a)=F_i(a)+β_i(a_i).

All players still mix independently. For a perturbed Nash profile p and
any independent mixed replacement ν_i on the same menu,

    U_i(ν_i,p_{−i})−U_i(p)
      ≤ E_{p_i}β_i−E_{ν_i}β_i
      ≤ max β_i−min β_i.

Thus bonus oscillation at most ε gives ORIGINAL finite-menu ε-Nash, with
no N factor. In particular |β_i|≤ξ gives error at most 2ξ. A bonus ξ for
finite planned dates and zero for Never has oscillation ξ and therefore
gives error at most ξ. It is Nash-equivalent to a penalty −ξ on planned
Never because subtracting a playerwise constant changes no comparison.

Finite-game Nash existence supplies at least one p for each such perturbed
game. Under the robust theorem, 2ξ≤e_* forces EVERY resulting p to satisfy
the original reach floor. A contradiction would therefore need an additional
theorem producing a perturbed Nash with smaller reach; its mere existence
and the finite-error transfer do not supply that theorem.

The following regression shows that action-only penalties cannot generically
eliminate every delayed equilibrium branch, even without pure equilibria and
with all singleton rewards positive.

## 3. Explicit Fin4 table

Let the active players be 0,1,2, cyclically indexed, with predecessor i−1.
Let player 3 be an outsider. For every nonempty S⊆{0,1,2,3}, set

    r_i(S)=1+1_{i−1∈S},                  if i∈S, i<3;
    r_i(S)=3·1_{i−1∈S},                 if i∉S, i<3;
    r_3(S)=1,                            if 3∈S;
    r_3(S)=2,                            if 3∉S.

The last case necessarily contains at least one active player because S
is nonempty. Infinite all-Continue pays zero. The table lies in [0,3] and
every own singleton reward equals one. It can be normalized by dividing
both rewards and auxiliary bonuses by three.

The active three-cycle completion is the one RENY independently analyzed
in Section 14 of its approximate-finite-timing notebook. This note changes
the fourth player's rewards: RENY's original embedding uses a negative
membership dummy; here the fourth player has positive singleton reward one
and prefers an active player's absorption, worth two. The incentive
calculation and this positive-singleton completion are the present test.

For every active player, immediate Quit guarantees at least one against
every opponent behavior; all-Never opponents cap every own deviation by
one. The same is true for player 3: Quit gives at least one, whereas
all-Never opponents give at most one. Hence every punishment value is
exactly its singleton value one. The table is all-normal.

There is no pure finite timing Nash, nor any pure terminal Nash. In a pure
profile with a finite first coalition S:

- if S contains no active player, an active player can join and raise its
  payoff from zero to one;
- if S contains exactly one active player, the active nonquitter whose
  predecessor is not that player can join and raise zero to one;
- if S contains at least two active players, some active i and i−1 both
  belong to S. Player i can Continue and receive three instead of two,
  since the predecessor still absorbs at that same date.

If there is no finite first coalition, an active singleton Quit gains one.
These deviations are permitted at the first coalition's date in every
finite timing menu that contains the original profile.

## 4. Concrete Never penalty: explicit delayed Nash and original debt

Fix N≥1 and 0<ξ≤1/4. Give every player bonus ξ for a finite planned date
and zero for planned Never. Put T=N−1 and

    q=(1+ξ)/2,  a=(1−ξ)/2.

Independently, each active player chooses T with probability q and Never
with probability a. Player 3 chooses Never. All four Continue before T.

Against these laws, an active player's ORIGINAL pure payoffs are

    Quit at any t<T: 1;
    Quit at T:       1+q;
    Never:           3q;
    Quit at any t>T: 3q+a².

The first three are the permitted menu comparisons. Adding the bonus gives

    1+ξ < 1+q+ξ = 3q.

Thus both supported actions T and Never are optimal in the perturbed game;
every earlier date is strictly inferior. Player 3's Never payoff is
2(1−a³)≥7/4. Every permitted finite date gives ORIGINAL payoff one and
perturbed payoff 1+ξ≤5/4, so Never is strictly optimal for player 3. This
proves perturbed finite Nash at EVERY deadline, not just a rootwise claim.

The active player's original prescribed payoff is

    U_i=q(1+q)+a(3q)=3q−ξq.

Its original finite-menu cap is 3q, so its finite-menu debt is ξq≤ξ. Its
FULL behavioral cap is 3q+a², since all omitted finite dates have that
payoff and pure-time extremality covers arbitrary behavioral replacements.
Therefore

    d_i=ξq+a²=(1+3ξ²)/4,               i=0,1,2.

Player 3's original payoff is 2(1−a³), and its full cap is 2−a³, obtained
by quitting after T only if all active players chose Never. Its debt is a³.
Consequently the original full exploitability is (1+3ξ²)/4. It does not
approach zero as ξ→0 or N→∞.

Literal joint Never probability is a³>0. For every fixed H with 1≤H≤N,

    R(N−H)=1,

since the only finite quitting date is T≥N−H. Thus a uniform small penalty
on Never neither removes Never mass nor forces this perturbed Nash branch
to absorb before the final H dates. There is no hidden deadline scaling.

## 5. Robustness against arbitrary bounded own clock bonuses

The failure is not an accident of a constant Never penalty. Fix any
0<ξ≤1/100 and ANY playerwise own-action functions β_i:A_N→[−ξ,ξ]. Set
T=N−1, and for active i put

    d_i=β_i(T)−β_i(Never),
    q_{i−1}=(1+d_i)/2.

This defines all three hazards, each in [1/2−ξ,1/2+ξ]. Let each active
player mix between T and Never with its q_i, and let player 3 Never.

The active player's two supported augmented pure values agree:

    1+q_{i−1}+β_i(T)=3q_{i−1}+β_i(Never).

They are at least 3/2−2ξ, whereas any earlier pure Quit gives at most
1+ξ. Hence earlier dates are strictly inferior. Player 3's augmented
Never value is at least 2[1−(1/2+ξ)³]−ξ, while any finite date gives at
most 1+ξ. The stated small fixed ξ makes the former strictly larger.
This proves that EVERY such clock/Never bonus array admits a fully delayed
perturbed Nash profile, uniformly in N.

Its actual original finite error is bounded by 2ξ by Section 2, and its
actual reach into any fixed final window is again one. As ξ→0 its hazards
converge to one-half and its original full debt converges to the positive
one-quarter defect of the delayed unperturbed source.

This is a no-go for a generic FORCING argument based only on small own-action
incentives: one cannot conclude that all equilibria of the perturbed game
must absorb early. It does NOT prove that every perturbed equilibrium is
delayed, or exclude a carefully selected early-absorbing branch. A theorem
selecting such a branch, or one exploiting additional no-uniform-payoff
restrictions beyond these normality/singleton conditions, remains possible.

## 6. The regression is solved, not a hypothetical counterexample

There is an exact period-three terminal Nash profile. At phase i only active
player i quits, with probability 1/2; the outsider always Continues. The
active phase-i continuation-value vector assigns one to i, two to i+1, and
one to i−1. The outsider's value is two. Bellman evaluation gives these
values exactly, since each phase either absorbs or advances with probability
one-half.

At phase i, the owner's Quit and Continue endpoints are both one. Player
i+1 has Continue value two and Quit value 3/2. Player i−1 has both endpoints
one. The outsider obtains two from Continue and one from Quit. Thus every
prescribed action is conditionally optimal. Under an arbitrary unilateral
deviation, the other active players retain positive hazards each cycle, so
opponent absorption occurs almost surely with a geometric tail. The bounded
Bellman comparison therefore passes to the actual terminal payoff and caps
every complete behavioral deviation.

The same geometric tail bounds finite-average error uniformly over unilateral
deviations as the averaging horizon tends to infinity. Hence the phase-zero
payoff (1,2,1,2) is a uniform-equilibrium payoff. The argument is the explicit
periodic calculation in RENY Section 14, with the present outsider added;
the outsider already obtains its maximal reward two and cannot improve.

The regression therefore does not contradict Section 12, whose hypothesis
is no uniform payoff. Its role is narrower and exact: even positive
singleton rewards, all-player normality, no pure Nash, and small uniformly
bounded private clock incentives do not force the desired absorption timing.

## 7. Remaining question

Can a DIFFERENT auxiliary payoff perturbation, or an explicit selection
criterion among the perturbed game's equilibria, use no-uniform-payoff
information to exclude the delayed branch and produce early absorption?
The all-selector reach theorem makes any such source decisive, but the
small own-action bonus and finite Nash existence alone do not produce it.
No claim is made that a private timing penalty is an equivalent quitting
reward table, that it is publicly observed, or that the original unrestricted
cap includes its bonus.
