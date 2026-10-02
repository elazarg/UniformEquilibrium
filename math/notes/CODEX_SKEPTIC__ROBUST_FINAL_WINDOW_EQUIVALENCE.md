# Positive singleton payoff and the robust final-window equivalence

Author: CODEX_SKEPTIC.

## Current status

The proposed reverse implication is valid. For a Fin4 zero-Never quitting
game with at least one strictly positive singleton self-reward, the robust
all-selectors final-window property is equivalent to nonexistence of a
uniform-equilibrium payoff. The forward implication is the reviewed RENY
source theorem; the reverse implication below works for any finite nonempty
player set and is elementary ordinary mathematics, not newly Lean-checked.

This is an exact finite-game reformulation, not a finite certificate or a
producer of small unrestricted regret. No genuinely new attack beyond the
already available finite-clock upper search is established here. Section 6
explains the quantifier obstruction and the precise additional theorem a
survival-based attack would need.

This task was coordinated with RENY and HILBERT; neither was asked to repeat
the reverse proof. No new independent review of this notebook is claimed.
The existing reviews concern only the forward implication, as linked below.

## 1. Complete statement

Fix a finite nonempty player set I and a reward table r_i(S) for every
nonempty coalition S. Choose M>0 with |r_i(S)|≤M. The all-Never outcome pays
zero. Players use independently privately randomized complete stopping
laws on the nonnegative integers together with Never; the corresponding
hazards are literal behavioral strategies in the quitting game. A unilateral
deviation may replace one player's complete law.

For a profile p, let U_i(p) be prescribed terminal payoff, let B_i(p) be the
supremum payoff over all such unilateral replacements, and put

    d_i(p)=B_i(p)−U_i(p),     E(p)=max_i d_i(p),
    A(p)=Pr_p(all players Never).

Each d_i is nonnegative because the deviator may retain its prescribed law.
Let s_i=r_i({i}). At deadline N≥1 the finite menu is
{0,…,N−1,Never}. A product law is finite-menu ε-Nash when all unilateral
replacements on this same menu improve payoff by at most ε. Define its
literal reach before date t by

    R_p(t)=Pr_p(all planned dates are ≥t or Never).

Define the robust final-window property RF(r) by

    ∃ H≥1, ε_*>0, ρ>0,
      ∀ N≥H, ∀ deadline-N finite-menu ε_*-Nash p,
        R_p(N−H)≥ρ.                                  (RF)

One may require ρ≤1 without changing the property. The finite-menu class is
nonempty by finite-game mixed Nash existence, so the statement is not
vacuous. Using “every ε≤ε_*” instead gives the same property, by inclusion
of the finite-menu Nash classes.

**Generic reverse implication.** If s_j>0 for some player j, then

    RF(r) ⇒ r has no uniform-equilibrium payoff.

More strongly, if a uniform-equilibrium payoff exists and s_j>0, then for
every H≥1, ε>0, ρ>0, and prescribed lower deadline bound N₀, there is a
finite-clock actual profile p and a deadline N≥max(H,N₀) such that

    E(p)<ε,      p is finite-menu ε-Nash at N,
    R_p(N−H)=A(p)<ρ.                                 (1)

**Fin4 equivalence.** For four players and at least one positive s_j,

    RF(r) ⇔ r has no uniform-equilibrium payoff.       (2)

The right-to-left implication of (2) is RENY Section 12. Its ordinary proof
and complementary completed reviews are in:

- [RENY's source notebook](CODEX_RENY__APPROXIMATE_FINITE_TIMING_NASH_AND_REACH.md);
- [HILBERT's review of Sections 1–11 and bounded source comparison](../feedback/CODEX_RENY__APPROXIMATE_FINITE_TIMING_NASH_AND_REACH__BY_CODEX_HILBERT.md);
- [SKEPTIC's independent first-crossing derivation](CODEX_SKEPTIC__ROBUST_APPROXIMATE_FINAL_WINDOW_REACH.md)
  and [Section 12 review](../feedback/CODEX_RENY__APPROXIMATE_FINITE_TIMING_NASH_AND_REACH__BY_CODEX_SKEPTIC.md).

The forward theorem does not require the positive-singleton assumption as
an extra input: under no uniform payoff a positive terminal gap applied to
all-Never already yields such a singleton. The assumption is necessary when
using RF alone to infer nonexistence.

## 2. Individual debt bounds joint Never mass

For every profile and every player, with no sign assumption,

    d_j(p) ≥ s_j A(p).                               (3)

Here is a direct argument avoiding either cap attainment or conditional Nash.
Write a_i for player i's Never mass. For each finite t, replace only player
j's Never atom by a planned quit at t, leaving all its originally finite
atoms unchanged. This is a legal new complete stopping law, privately
sampled independently of the other players.

Couple it to the original law by this deterministic transformation. If the
original j-date is finite, nothing changes. If it is Never and some opponent
quits before t, the terminal outcome is also unchanged. On the event that
every player was Never, the new outcome is singleton {j}, giving exact
payoff gain s_j. The remaining possibly changed event is

    j was Never, and the opponents' first finite date is ≥t.

Its probability tends to zero; it does not include opponents who are all
Never. Both payoff values are bounded by M, so its contribution to the
expected gain has absolute value at most 2M times that probability. The
deviation gains therefore tend to s_j∏_i a_i=s_j A(p).

Every such gain is at most d_j(p), whose definition is a supremum over all
complete deviations. Taking the limit proves (3), without claiming that the
limiting gain is attained by one deviation. For s_j>0, it follows that

    A(p) ≤ E(p)/s_j.                                 (4)

The inspected declaration `singletonReward_le_nashError_div_never` in
`UniformEquilibrium/Quitting/Classification/Existence/ApproximateEquilibriumVanishingNeverAlternative.lean`
already gives the required maximum-error consequence for actual global
root-sequence approximate Nash profiles with positive joint Never mass.
Its premise is unrestricted root-sequence Nash, not finite-menu Nash.

The stronger playerwise form (3) is ordinary mathematics here. Its late-date
step matches the inspected
`quittingTerminalPayoff_update_finiteTime_tendsto_never_add_opponentNever_mul_singleton`
in `UniformEquilibrium/Quitting/Terminal/CompactStoppingLawCapUpperBound.lean`:
late pure quitting tends to Never payoff plus opponent Never product times
the own singleton reward. That declaration requires neither opponent
properness nor cap attainment.

## 3. Finite-clock approximation preserves unrestricted error

For a fixed complete product law p and cutoff L≥1, replace every finite
stopping atom at dates t≥L by Never, separately for each player. Retain all
original Never mass and all finite atoms before L. Call the result p^L and
let θ_L be the sum of moved marginal masses. Countable additivity gives
θ_L→0. This is a statement for each fixed profile, not uniform tightness of
an entire family of approximate equilibria.

The obvious independent coupling disagrees in some coordinate with
probability at most θ_L. Hence, for every player i,

    |U_i(p^L)−U_i(p)|≤2Mθ_L.

Against any fixed complete unilateral replacement of i, couple only the
opponents; the same bound holds uniformly over that replacement. Taking
suprema gives |B_i(p^L)−B_i(p)|≤2Mθ_L. Consequently

    |d_i(p^L)−d_i(p)|≤4Mθ_L,
    |E(p^L)−E(p)|≤4Mθ_L.                             (5)

The cutoff preserves independence. It does not delete an original Never
atom or assume small opponent-deleted survival. In particular, the weaker
“same finite root prefix” bound is not being mistaken for a vanishing
full-cap error; that bound need not vanish when an opponent is Never with
positive probability. The moved *late finite mass* does vanish.

The finite-clock and density declarations inspected before this argument
were:

- `Math.Probability.exists_finset_pmfFiniteComplementMass_lt` in
  `MathUE/ProbabilityMassFunction/DiscreteTightness.lean`;
- `stoppingLawLateFiniteMass_eq_one_sub_none_sub_finiteHead` and the retained
  prefix definitions in
  `UniformEquilibrium/Quitting/Paths/StoppingLawFiniteTail.lean`;
- `pmfTV_quittingCounterfactualOutcomeLaw_update_le` in
  `UniformEquilibrium/Quitting/Paths/CounterfactualStoppingLaw.lean`, which
  contracts a general stopping-law marginal TV change to finite terminal-law
  TV, and can be iterated over changed coordinates;
- `finiteClockDecodeLaw_support` and `finiteClockDecodeLaw_coordinates` in
  `MathUE/ProbabilityMassFunction/FiniteClockCoordinates.lean`, including the
  separate Never atom and zero auxiliary after-support coordinate;
- `FinFourRationalFiniteClockProfileCompleteness.realCap_eq_continuationBestResponseValue`,
  `continuous_realExploitability`, `rationalMass_tendsto`, and
  `exists_checkedCandidateAt_of_finiteClockStoppingLaws` in
  `Research/Quitting/FinFourRationalFiniteClockProfileCompleteness.lean`.

The finite-product TV theorem in `MathUE/PMFProduct/TotalVariation.lean`
was also inspected. Its coordinate types are finite; it is not silently
applied as stated to infinite stopping-time alphabets. The direct coupling
above and the general-TV counterfactual declaration supply that extension.

## 4. Proof of the reverse implication, with deadline order explicit

Suppose a uniform-equilibrium payoff exists. The inspected semantic endpoint
`quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors`
in `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`
supplies actual terminal profiles of arbitrarily small unrestricted E.

Fix H≥1, ε>0, ρ>0, and N₀. Put

    b = min(ε, s_j ρ)/2 > 0.

First choose an actual profile with E<b/2. Then choose its finite cutoff
L≥1 so 4Mθ_L<b/2. By (5), the truncated actual profile p^L satisfies

    E(p^L)<b<ε,     A(p^L)≤E(p^L)/s_j<ρ.

Finally choose N≥max(L+H,N₀). All of p^L's finite support is before L,
so it is a legitimate profile on the deadline-N menu. Because its
*unrestricted* error is below ε, every deviation in that enlarged menu
also has gain below ε. For N−H≥L, all its possible finite quits have
already occurred, and therefore

    R_{p^L}(N−H)=A(p^L)<ρ.

This proves (1). It contradicts any proposed RF triple, proving the generic
reverse implication and, with the reviewed forward theorem, (2).

The order of choices is essential: accuracy and window first; actual
unrestricted approximation second; its finite cutoff third; enlarged menu
last. No uniformly bounded cutoff, computable modulus, or same profile for
every accuracy is claimed. The existing semantic endpoint supplies the
fixed-payoff quantifier in UE; this argument does not re-prove uniformization.

## 5. Exact positive and negative tests

**Positive singleton and equality in (3).** Let player 0 receive one when it
belongs to the first quitting coalition and zero otherwise. Each other
player receives −1 if it belongs to that coalition and zero otherwise.
Prescribe all other players Never; player 0 quits at zero with mass 1−a
and Never with mass a. Then A=a, U_0=1−a, B_0=1, and d_0=a=s_0 A.
At a=0 this is exact terminal Nash with immediate absorption. For every H,
the same profile at N=H+1 has R(N−H)=0. RF fails as predicted.

**Positivity cannot be omitted.** On four players take
r_i(S)=−1 when i∈S and zero otherwise. All-Never is exact terminal Nash
and a uniform equilibrium. In every finite-menu ε-Nash profile, deviating
to Never gives player i zero, so

    Pr(i belongs to the first quitting coalition)≤ε.

The total absorption probability β is at most the sum of these four
probabilities, hence β≤4ε. At every date R(t)≥1−β≥1−4ε. Thus RF holds
with H=1, ε_*=1/8 and ρ=1/2 although UE exists. All singleton self-rewards
are negative. For the concrete one-date product root with all Quit
probabilities 1/8, each player's debt is exactly 1/8 and the reach is
(7/8)^4=2401/4096≥1/2. The universal argument, not this single example,
establishes RF on the table.

**Finite-menu Nash is not preserved by deadline enlargement.** Use the
normalized hard-deadline table from
`FinFourHardDeadlineTimingNashBarrier.reward`. Its two active players have
reward pairs (1/2,−1) at {0}, (1,−1) at {1}, and (0,0) at {0,1}; the two
dummies receive negative membership rewards and are prescribed Never.
At deadline one, prescribe Quit-zero probabilities 1/2 and 1/3 for the two
active players, respectively. Each is indifferent between date zero and
Never, so all finite-menu debts equal zero. Declaring the same laws at
deadline two adds date one. Player 0 then has gain exactly 1/3; the other
debts remain zero. Hence enlarging the menu is invalid for a merely finite
Nash source. The proof in Section 4 explicitly uses a full-regret bound.

Independent Fraction enumeration of all pure stopping choices checked the
last example: finite debts (0,0,0,0) at menu {0,Never}, and
(1/3,0,0,0) at {0,1,Never}. It also checked the negative-membership root
value 2401/4096. No floating-point evidence is used.

## 6. Finite witnesses, infinite quantifiers, and actual attack value

For a rational reward table and rational positive ε,ρ, a strict violation
of a proposed H,ε,ρ is finitely checkable: display a finite rational product
law, its deadline N, all finite pure-menu deviation inequalities, and the
rational inequality R(N−H)<ρ. The finite Nash inequalities suffice because
payoff is affine in the deviator's mixed timing law. Checking such a witness
does NOT require solving the unrestricted deviation problem.

If UE exists and s_j>0, these witnesses can be chosen rational with strict
finite Nash inequalities. Section 4 gives a strict *full*-regret margin;
at its fixed finite clock, rational simplex approximation preserves this
margin and the strict Never-mass inequality. The same enlarged-deadline
argument then applies. The inspected rational completeness theorem already
supports such full-regret approximation; requiring an additional strict
Never-mass inequality uses only continuity of the finite product.

This does not finitely certify RF. Its positive assertion still requires
one triple that works for every deadline and every finite-menu source.
Checking any finite list of deadlines leaves all larger deadlines open.
Conversely, refuting one proposed triple does not refute RF: another triple
could still work. Under UE the strict witness search terminates for every
specified triple, but witnessing all those terminations is not one finite
certificate of UE. For arbitrary real rewards, exact numerical comparisons
are not automatically executable at all.

Thus the equivalence yields no demonstrated new attack beyond a reformulation.
One can minimize reach over the finite ε-Nash set at each chosen N, obtaining
a concrete finite-game search objective, but there is no proved mechanism
that carries its small-reach witnesses to smaller errors or defeats every
possible fixed triple. Independent clock searches do not supply that
mechanism. Existing exact finite-clock upper search already produces
small-unrestricted-regret witnesses when those exist.

A genuinely new attack would need an additional source construction or
renewal theorem proving failure of every RF triple from arbitrary
positive-singleton Fin4 game data, without assuming UE or an already small
unrestricted regret. For example, a source-retaining operation that drives
reach below any prescribed threshold at fixed positive finite-menu accuracy,
while keeping the cut farther than any prescribed H from the deadline,
would suffice. No such operation is established by (2). The original
omitted-date/nonpayer-cap consumer problem has not disappeared.

## Scope and next question

This is a bounded source audit and ordinary proof, with no claim of new
Lean verification, finite decision algorithm, or export qualification.
Only this owned gitignored notebook was added. No Lean, exports, shared
indexes, or other authors' notes were edited.

The concrete next question is whether a game-derived family of finite-menu
near-equilibria has early reach tending to zero while its distance from the
deadline tends to infinity, at a genuinely fixed positive error allowance.
Producing such a family would attack RF directly; obtaining it by first
assuming terminal approximation would merely repeat the reverse proof.
