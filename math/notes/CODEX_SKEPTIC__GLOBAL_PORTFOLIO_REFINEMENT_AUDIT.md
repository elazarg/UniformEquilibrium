# Global portfolio refinement: operation audit

Author: CODEX_SKEPTIC.

## Status and verdict

Completed one bounded mathematical operation audit. No uniform full-cube
accuracy refiner was obtained. Two exact results survive: homogeneous reward
transfer refines a cover on smaller concentric cubes but supplies no
additional improvement on the normalized boundary; and maximum regret is
convex in each individual stopping law, yet a positive-regret profile can
globally minimize regret against every one-player replacement. An explicit
simultaneous independent two-player change escapes the latter trap.

The local counterexample concerns proposed operations, not the existence of
a full-cube cover at a specified small accuracy. It does not show that a
more informed global refinement procedure is impossible. The proofs here
are ordinary mathematics, unreviewed and not checked in Lean. No exports,
Lean edits, new search campaign, or implementation project were made.

## Question

Suppose a finite family of actual rational finite-clock product policies
strictly epsilon-covers the entire normalized Fin4 reward cube, with regret
against all behavioral deviations and zero Never payoff. Can one derive a
strictly smaller-accuracy full-cube cover by an explicit game-theoretic
operation on those policies and their certified reward regions? The source
cover is supplied; neither uniform equilibrium nor vanishing regret is
assumed. All policy randomizations must be independently available in the
quitting game.

The operations tested are reward normalization/perturbation with certificate
transfer, independent combination of locally certified policies, repeated
finite blocks, and exact optimization of one complete stopping law. A
refinement means new strategic accuracy beyond the supplied cover's existing
strict slack; simply renaming its exact maximum regret is not the desired
operation. The earlier compactness theorem does not answer this question.

## 1. Sources selected

The exact reward robustness and homogeneity declarations are in
`Research/Quitting/TerminalExploitabilityRewardRobustness.lean`; the relevant
portfolios and exact scale resolver were audited in
`CODEX_SKEPTIC__FIN4_BLINDSPOT_RESTART.md`. Narrow inspection of
`arch/DECIDE_CONTROLLER_TESTER.md` and `docs/TOOLKIT.md` separates reward
robustness, private stopping-law mixture, and conditional target-matched
packet amplification. The zero-Never normalization constraint was checked
against `CODEX_EULER__FIN4_SEARCH_SPACE_INVENTORY.md`.

Actual declaration reads under their imports:

- `abs_quittingTerminalExploitability_sub_le_of_reward_close`,
  `quittingTerminalPayoff_scaleQuittingReward`,
  `quittingContinuationBestResponseValue_scaleQuittingReward`, and
  `quittingTerminalExploitability_scaleQuittingReward` in
  `Research/Quitting/TerminalExploitabilityRewardRobustness.lean`;
- `quittingRootExpectedPayoff_update_coord_eq_mix` in
  `UniformEquilibrium/Quitting/Root/CoordinateMarginalMixture.lean`;
- `quittingTerminalPayoff_update_stoppingLawMixture_eq` in
  `UniformEquilibrium/Quitting/Paths/StoppingLawMixture.lean`; and
- `quittingTerminalPayoff_update_sub_le_two_mul_bound_mul_stoppingLawTV` in
  `UniformEquilibrium/Quitting/Paths/StoppingLawExposure.lean`.

The finite unrestricted deviation menu, product-law realization, and reward
polynomials are the exact finite-clock declarations already audited in
`CODEX_SKEPTIC__FIN4_BLINDSPOT_RESTART.md`. The maintained toolkit's exact
charged-packet amplifier requires a source-matched packet producer at every
reachable state; the supplied reward-cube portfolio has no such field.

The existing
`CODEX_HAHN__FINITE_CLOCK_EXPLOITABILITY_KKT_BOUNDARY_OR_CROSS_AMPLIFICATION.md`
keeps both the newly exposed deadline and adverse changes in another active
player's gain. The finite pure-clock response-cycle packet explicitly
separates external strategy-revision cycles from an in-game chronology.
The exact finite-deadline Nash selection exclusion was source-audited in the
preceding notebook and remains applicable: that restriction is not used as
a producer here. Narrow searches for coordinatewise maximum-regret minima
and private-mixture preservation found no duplicate of the concrete
coordinatewise trap below in the selected source neighborhood.

## 2. What reward transfer alone actually guarantees

Write R=[−1,1]^60 and E_r(p) for a profile's full terminal exploitability.
For a supplied finite portfolio P let G_P(r)=min_{p∈P}E_r(p), and assume
G_P(r)≤h throughout R, where 0<h<2. The finite strict cover in the question
provides such an h below its requested epsilon by exact portfolio checking;
this h is existing slack, not new strategic improvement.

### Proposition 2.1: radial improvement on the interior

For every reward table r with M=||r||∞≤1,

    G_P(r) ≤ M h.

If M=0, all terminal rewards and all regret vanish. Otherwise r/M∈R and
homogeneity of every prescribed and deviating payoff gives
E_r(p)=M E_{r/M}(p). Minimize over the same finite portfolio. In particular
the same portfolio gives accuracy ρh on the smaller cube ρR, 0<ρ<1.
Nothing in this step lowers its worst bound on the boundary M=1.

### Proposition 2.2: optimal bound in the scaling-plus-distance calculus

Suppose the only certificate available for a selected policy at a queried
normalized table q is E_q(p)≤h. For λ≥0, homogeneity and 2-Lipschitz reward
robustness yield the transfer bound

    E_r(p) ≤ λh + 2||r−λq||∞.

For every r, the exact best bound of this form is

    inf_{λ≥0, q∈R} [λh+2||r−λq||∞] = h||r||∞.

Proof: the distance from r to λR is max(0,M−λ), so minimize
λh+2 max(0,M−λ). It decreases up to λ=M and increases afterward, since
0<h<2. Equality is achieved by q=r/M and λ=M when M>0.

At a normalized boundary table this lower limit is h. Multiple queried
policies, each used only through the same h certificate, do not lower it;
each candidate transfer bound is at least h. Repeated transfers also do not
help: the triangle inequality collapses their accumulated distances to at
least the direct distance for the product scale. A better bound can come
from better actual policy slack or signed information in individual regret
rows, but those are additional input beyond this scalar transfer argument.

This is a limitation of a specified certificate calculus, not a theorem
that arbitrary reward perturbation cannot help find better policies.
In particular it leaves open using the full reward-polytope inequalities
to control the sign of every relevant gain change.

### Terminal translations do not supply missing scale

Positive affine changes of complete outcome utilities preserve incentive
comparisons, including the Never outcome. In the repository normalization,
Never is zero both before and after the transformation, so its translation
constant must be zero. Subtracting a constant only from the terminal rewards
is not equivalent. Already with one active player, changing its singleton
reward from −1 to +1 while keeping Never at zero changes the all-Never
profile's regret from zero to one. Thus centering terminal rewards and
forgetting the shifted Never payoff cannot amplify a global cover.

## 3. Exact regression: private gluing and repeated blocks

Take players {0,1,2,3}. For every nonempty coalition S, let A=S∩{0,1}.
Both active players receive

    0 if A is empty;
    −1 if A is either singleton;
    +1 if A={0,1}.

Each passive player i∈{2,3} receives −1 if i∈S and zero otherwise.
All rewards are normalized, all behavioral randomization is independent,
and Never pays zero. The payoff rules specify all sixty coordinates.

Two actual rational finite-clock profiles are exact terminal equilibria:
all-Never, and the pure active-pair quit at date zero with passive players
Never. In the former every finite unilateral quit pays −1; in the latter
an active player gets the maximum reward +1 and a passive player cannot
improve on zero.

Now mix each active player's marginal independently, taking Quit at date
zero with probability 1/2 and Never otherwise. Call this profile p. The
two singleton outcomes each have probability 1/4 and the pair has probability
1/4, so the active payoffs are −1/4. Against the other player's law,
immediate Quit has value zero, Never has value −1/2, and any later finite
Quit has value −1. Thus both active caps are zero and

    E_r(p)=1/4.

The independent midpoint of two exact equilibrium policies is therefore
not even an exact equilibrium. Choosing one common public index between
the two complete policies would have different joint laws. Since a publicly
observed index chooses between exact equilibria, it would retain zero
regret, but that external correlated choice is not a resource provided by
the quitting game. No such choice is used here.

Replaying p's root twice, with independent fresh marginal coins when the
first root survives, is legal but also not an error contraction. Each active
law then has masses 1/2 at date zero, 1/4 at date one, and 1/4 at Never.
The first block's unconditional active payoff is −1/4 and its joint
survival is 1/4, so two-block payoff is −5/16. Immediate Quit still gives
zero, while all later or Never responses are worse. Hence the repeated
profile has exact exploitability 5/16 > 1/4.

The missing invariant is explicit: replay replaces the zero Never tail
payoff by a negative continuation payoff. The static guarantee on p's
original regret does not control that replacement. Existing matched-target
prefix/cycle consumers require precisely such additional continuation data.

## 4. Stronger obstruction: exact one-coordinate optimization can stall

### Proposition 4.1: a positive coordinatewise global minimum

For the table and midpoint profile p of Section 3, every complete unilateral
replacement τ_i satisfies

    E_r(p[i←τ_i]) ≥ E_r(p)=1/4.

The quantifier includes arbitrary infinite-support behavioral stopping laws;
it is not a one-date or finite-controller calculation.

Proof for an active replacement, say player 0: let a be its probability of
quitting at date zero, b its total probability of quitting at any later
finite date, and c=1−a−b its Never mass. Player 1 still has masses 1/2 at
zero and 1/2 at Never. Both active prescribed payoffs are

    U = −b−c/2 = −1/2+a/2−b/2.

Player 0 can quit at zero for payoff zero, so its debt is at least
1/2−a/2+b/2. Player 1 can quit at zero for payoff 2a−1, so its debt is
at least 3a/2−1/2+b/2. If a≤1/2 the first lower bound is at least 1/4;
if a≥1/2 the second is at least 1/4. The same calculation applies to
player 1's replacement. In fact any b>0 makes the displayed maximum
strictly larger than 1/4.

For a passive replacement, active play at date zero is unchanged. If neither
active player quits, any later passive-only exit gives both active players
zero, just as Never does. Thus their payoffs remain −1/4. Either active
player can still quit immediately for expected payoff zero, because the
active reward ignores passive membership. Their debt remains at least 1/4,
regardless of the passive player's complete stopping law. This proves the
claim.

Consequently an algorithm that repeatedly minimizes full maximum regret over
one player's entire law can remain at p forever. Allowing all pure dates,
the omitted deadline, arbitrary diffuse laws, and Never does not repair
this one-coordinate obstruction.

### The useful surviving convexity and a legal joint repair

For fixed opponents, E_r is convex in any one prescribed player's complete
stopping law. That player's cap is independent of its own law and its payoff
is affine. For every other player, each fixed deviation's gain is affine in
the changed law, so its cap-minus-payoff is a supremum of affine functions.
Their finite maximum is convex. This proves separate convexity, which is
consistent with the coordinatewise trap; it does not imply joint convexity.

The trap is escapable without correlation. Give both active players Quit
probability t at date zero and Never probability 1−t. For 1/3≤t≤1/2,
their common payoff and cap are

    U(t)=3t²−2t,     B(t)=2t−1,
    E(t)=4t−1−3t².

At t=1/3, E(t)=0. With t=1/2−s, 0≤s≤1/6,

    E(t)=1/4−s−3s².

Thus a simultaneous independent decrease of both hazards strictly improves
regret. At the midpoint, the two active gain gradients in the two hazard
coordinates are (−1/2,3/2) and (3/2,−1/2). A change of either coordinate
alone makes one of these gains rise; direction (−1,−1) makes both decrease.
This is an exact finite descent direction, not a public mixture of policies.

The parent investigation's observation that a positive maximum-regret
minimum has multiple tied debtors is compatible with this example: here
both active players are tied at 1/4. The example is only a coordinatewise
minimum, not a global minimum over all profiles. It shows why multiple tied
debtors do not by themselves orient one-player repair, and it makes no
counterexample claim against that global-minimum result.

## 5. Consequence for a genuinely global refinement attempt

The surviving radial lemma gives a useful interior guarantee from any supplied
full-cube cover. To improve the entire cube, an operation must also improve
the normalized boundary. The common-bound reward-transfer calculus cannot
do this, and local policies cannot be glued by treating independent private
mixing as common-index mixing. Replaying a finite policy needs continuation
control, and coordinatewise full-regret minimization can stall strictly
above zero.

A concrete next test for a proposed boundary refiner is therefore the finite
simultaneous-direction problem: at a rational profile, include every tied
pure-deviation gain, including the new after-support alternatives if the
clock is enlarged, and find one feasible change of the independent marginal
laws which decreases them all. The regression supplies a positive instance
with direction (−1,−1), while exact one-coordinate updates fail. A finite
direction calculation is meaningful; a guarantee that such a direction or
another constructive exit exists at every relevant boundary table is the
unproved game-theoretic part.

This note does not assume that guarantee, a retained target, public
correlation, or already smaller regret. No operation audited here converts
an arbitrary full-cube strict epsilon cover into a uniformly smaller one
without additional mathematical input. This is the bounded experiment's
verdict, not a universal impossibility theorem for portfolio refinement.

## 6. Exact regression record

The existing independent coalition-law evaluator was reused in memory; no
new search or package was made. The exact Fraction outputs were:

    all-Never: 0;
    pure active pair: 0;
    independent midpoint: 1/4;
    simultaneous one-third hazards: 0;
    two repetitions of the midpoint block: 5/16.

Reproduce from `math/`:

```bash
python - <<'PY'
from fractions import Fraction as Q
import importlib.util
spec = importlib.util.spec_from_file_location(
    'portfolio', 'experiments/CODEX_SKEPTIC__FINITE_PORTFOLIO_REGRESSIONS.py')
m = importlib.util.module_from_spec(spec)
spec.loader.exec_module(m)
r = tuple(
    Q(0 if mask & 3 == 0 else 1 if mask & 3 == 3 else -1) if i < 2
    else Q(-1 if mask & (1 << i) else 0)
    for mask in range(1, 16) for i in range(4))
never = [{None: Q(1)} for _ in range(4)]
policies = [
    never,
    [{0: Q(1)}, {0: Q(1)}, *never[2:]],
    [{0: Q(1, 2), None: Q(1, 2)} for _ in range(2)] + never[2:],
    [{0: Q(1, 3), None: Q(2, 3)} for _ in range(2)] + never[2:],
    [{0: Q(1, 2), 1: Q(1, 4), None: Q(1, 4)} for _ in range(2)] + never[2:]]
values = tuple(m.exact_exploitability(p, 2 if k == 4 else 1, r)
               for k, p in enumerate(policies))
assert values == (Q(0), Q(0), Q(1, 4), Q(0), Q(5, 16))
print(values)
PY
```

The infinite-law coordinatewise inequality is proved algebraically in
Section 4; finite rational evaluations alone would not establish it.
The note remains internal and awaits independent review. One concrete next
question is whether the full active-response direction problem has an
exhaustive constructive alternative under the full-cube cover hypothesis.
