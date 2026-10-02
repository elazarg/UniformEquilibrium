# Stationary repair and the local degree at all Continue

Author and independent reviewer: CODEX_LERAY_CARDINAL.

Status: the main mathematical claims of
[`CARDINAL_FREE_LCP_INDEX_ESCAPE.md`](../gpt/CARDINAL_FREE_LCP_INDEX_ESCAPE.md)
pass this independent review. The results are ordinary mathematics using
classical integer Brouwer degree; their new composition is not checked in
Lean. This is an internal assessment, not an export or a claim of general
quitting-game existence. The companion program supplies finite algebraic
regressions only. No mathematical objection remains in this review.

The two substantive gains relative to the resolved predecessor packets are:

1. A universal quantitative conversion of an original discounted stationary
   equilibrium into an original stationary approximate terminal equilibrium,
   with a cap against every behavioral replacement.
2. A direct local degree calculation at zero discount which yields escaped
   original discounted equilibria for every finite player count, preserving
   stationary approximate implementation and giving exact stationary terminal
   Nash under nonnegative own-singleton rewards.

The complete stationary cap formula, ambient displacement derivative,
classical integer LCP degree, and nonnegative-inverse approximation are
existing ingredients. They are not new theorems of the packet.

## Self-contained question and semantics

Fix a finite player set of size n ≥ 2, real reward vectors r(S) for all
nonempty coalitions S, and M > 0 bounding every absolute reward coordinate.
Players independently randomize Continue or Quit at each live stage. The
first nonempty quitting coalition absorbs; the live stage and Never pay
zero. The only public live history is the sequence of all-Continue rows.
Every unilateral behavioral replacement, including every deterministic
deadline and Never, is allowed. Before absorption, private randomization
induces an independent law on the finite dates and Never.

For stationary hazards q, let C = ∏ᵢ(1−qᵢ), a = 1−C, sᵢ = rᵢ({i}),
and Γᵢⱼ = rᵢ({j})−sᵢ. Rows are recipients, columns singleton quitters.
Let V(q) be the expected terminal payoff, Bᵢ(q) the supremum of player i's
terminal payoff over every replacement, and E(q) = maxᵢ(Bᵢ(q)−Vᵢ(q)).

The questions are whether a positive-absorption discounted equilibrium can
be repaired within {q,q₁e₁,…,qₙeₙ}, and whether R0 together with integer
LCP degree κ(Γ) ≠ 1 produces such equilibria at a fixed positive distance
from all Continue. A supplied-root repair and a raw-matrix producer are
different conclusions. Neither is completeness of stationary strategies
for arbitrary quitting games.

## Stationary repair: valid with all boundary cases

For player i let αᵢ = ∏ⱼ≠ᵢ(1−qⱼ), bᵢ = 1−αᵢ, Qᵢ the reward expectation
on Quit, and Hᵢ the one-row absorbing reward contribution on Continue.
For discount complement λ ∈ (0,1), put d = 1−λ and L = 1−dC.
The prescribed live value is uᵢ = d a Vᵢ/L. The actual Bellman inequalities
imply Qᵢ ≤ aVᵢ/L and Hᵢ+αᵢuᵢ ≤ aVᵢ/L, including both cube faces.
The face signs of Dᵢ = (1−dαᵢ)Qᵢ−Hᵢ have the packet's orientation.

Against stationary opponents, a deadline t pays

    (1−αᵢᵗ) Hᵢ/bᵢ + αᵢᵗ Qᵢ                 when bᵢ > 0.

Never pays Hᵢ/bᵢ, and arbitrary private clocks average these values.
Consequently Bᵢ = max(Qᵢ,Hᵢ/bᵢ). If bᵢ = 0, all opponents play Never
and Bᵢ = max(sᵢ,0). This is a complete behavioral cap, with no restriction
to stationary deviations or a bounded menu of dates.

The packet's estimates (2.4)–(2.6) follow. In particular the sign-sensitive
step can be seen directly from

    a(bᵢ+λαᵢ)/(bᵢL) − 1 = λ(a−bᵢ)/(bᵢL) ≥ 0.

Thus Vᵢ ≤ 0 implies Hᵢ/bᵢ ≤ Vᵢ when bᵢ > 0. The potentially very
slow deleted-opponent clock introduces no positive continuation debt for
this player. The remaining Quit debt is bounded by Mλ/a.

Write x = λ/a. If x > 1, the universal bound E ≤ 2M suffices. For
0 < x ≤ 1 put θ = √x/2. If every bᵢ ≥ θa, keep q and use
E(q) ≤ Mx(1+1/θ). Otherwise choose k with bₖ < θa. Then
qₖ > (1−θ)a, and every other player's deleted clock has bⱼ ≥ qₖ.

If Vₖ ≤ 0, keep q. The preceding sign argument controls k and the
large deleted clocks control the others. When bₖ = 0, the positive
owner hazard and discounted face condition force sₖ ≥ 0; together
with Vₖ = sₖ ≤ 0 this gives sₖ = 0 and zero owner debt. No division
by bₖ is used in that branch.

If Vₖ > 0, retain only qₖ. Conditional on prescribed absorption, the
probability of a coalition other than {k} is bₖ/a. Hence every payoff
coordinate is within 2Mbₖ/a of r({k}). Separately, coupling the outsider
j's opponent row before and after the deletion bounds the change in its
Quit endpoint by 2Mbₖ. Both estimates are necessary: prescribed payoff
closeness alone would not control the outsider's counterfactual coalition.
The resulting outsider debt is at most Mx+4Mθ, while owner debt is at
most 2Mθ. Therefore some p in the stated finite list satisfies

    E(p) ≤ min(2M, M[x+2√x]) ≤ 3M√(λ/a).

The construction uses neither extra information nor correlated clocks.
It remains valid for signed collisions, zero hazards, and sure-quitting
hazards. A fixed positive terminal gap γ, even if imposed only on
stationary profiles, consequently forces every discounted equilibrium to
have a ≤ 9M²λ/γ², with the packet's sharper inverted bound also valid.
This necessary condition does not exclude games needing nonstationary
strategies.

## Integer degree: the domain and both homotopies are valid

Extend D polynomially to the whole real hazard space, and define
Fλ(q) = clip(q+D(λ,q)), Gλ = Id−Fλ. Every zero of Gλ is in [0,1]ⁿ.
For λ > 0 it is an actual discounted stationary equilibrium. On
Ω = (−1,2)ⁿ, the homotopy from Fλ to the cube center has images in
[0,1]ⁿ, so its displacement has no boundary zero and degree +1.

At λ = 0, G₀ is a continuous map even at all Continue; no singular
discounted value is assigned there. In an ambient neighborhood,
D(0,q) = −Γq+O(‖q‖²). Upper clipping is inactive sufficiently near zero,
while lower clipping gives the exact identity G₀(q) = min(q,−D(0,q)).

R0 means min(z,Γz) has only the zero root. Compactness of the full unit
sphere and positive homogeneity give ‖min(z,Γz)‖ ≥ c‖z‖ for c > 0.
The quadratic error is smaller than this margin on a sufficiently small
closed neighborhood. Thus the straight comparison homotopy has no
boundary zero, and zero is locally isolated with local degree κ(Γ).
Joint continuity makes the same boundary safe for every sufficiently
small λ ≥ 0. Excision and additivity then give

    deg(Gλ, Ω \ closure(W), 0) = 1−κ(Γ).

This includes λ = 0. If κ ≠ 1, there is an outer root for every small
positive λ, with maxᵢqᵢ > δ for one fixed δ > 0. Degenerate roots,
binding inactive coordinates, nonisolated outer root sets, and upper
faces cause no gap. The invariant is a total degree; degree 2 is not
a count of exactly two equilibria. There is no unproved localization
of all discounted equilibria and no choice of a translated LCP anchor.

Combining this source with the repair gives stationary terminal errors
tending to zero. Repair retains absorption at least δ/2 for small λ.
Compactness of the payoff vectors selects one fixed target before the
final accuracy. The packet's fixed-profile geometric timing bounds show
that the selected stationary profile works for every sufficiently large
horizon, uniformly over all behavioral deviations. Deleted clocks may
approach zero as accuracy improves: the horizon threshold may depend on
the selected profile, so no common deleted-clock lower bound is needed.

## Exact stationarity and the signed boundary

Under R0 and κ ≠ 1, the outer zero-discount root q* has positive absorption.
If at least two
hazards are positive, every player's opponents eventually quit almost
surely and the terminal cap formula makes the Bellman root exact Nash.
If k is the sole active player, every outsider has a contracting deleted
clock; k's missing response is Never. It is unprofitable precisely when
sₖ ≥ 0. Therefore nonnegative own-singleton rewards suffice for an exact
stationary terminal Nash equilibrium and same-profile uniform approximate
finite-horizon implementation at its fixed terminal payoff.

The weaker raw sufficient condition in Section 4 also passes. A sole-owner
zero-discount root h eₖ, 0 < h ≤ 1, has outsider inequalities exactly

    rⱼ({k}) ≥ (1−h)sⱼ + h rⱼ({j,k})          for every j ≠ k.

The owner's displacement is zero regardless of sₖ. Infeasibility of this
one-variable system for each negative sₖ therefore excludes every bad
sole-owner root and suffices for the same exact conclusion. It need not
exclude any signed collision rewards.

The packet's two-player signed example is a stronger boundary witness
than merely a discontinuous limiting best reply. Its matrix is
Γ = [[0,−1/2],[−1/2,0]], which is R0 and has κ = 0: the LCP with
right-hand side −1 has no root. Yet the game has no exact stationary
terminal Nash equilibrium. If q₀ > 0, player 1's Quit endpoint is
−1/2+3q₀/2 > −1, its Never value, so exact stationary optimality forces
q₁ = 1. Against that hazard player 0 strictly prefers Continue, forcing
q₀ = 0, a contradiction. If q₀ = 0 and q₁ > 0, player 1 improves by
Never; if both hazards vanish, player 0 improves by Quit. The displayed
positive-parameter discounted family nevertheless has terminal regret
tending to zero. An exact signed strengthening of Theorem B is false.

## Weak inverse, finite censoring, and rational approximation

For a strictly positive inverse B and negative determinant, homogeneous
complementarity is impossible: a nonzero nonnegative slack w gives
h = Bw > 0, contradicting complementary slackness. At right-hand side
−1 the unique root is B1 > 0, with local index sign(det Γ) = −1.
The R0 margin bounds all roots along bounded right-hand-side homotopies,
so this calculates κ correctly.

The weak-inverse approximation is the existing predecessor lemma for
n ≥ 3. With K = J−I, the Neumann expansion of (Γ−eK)⁻¹ is nonnegative
term by term. If both its constant and first-order (i,j) terms vanish,
row i and column j of B have the same singleton support {k}. Invertibility
and n ≥ 3 supply a positive entry Bᵤᵥ with u,v ≠ k, making the indicated
second-order term positive. This also explains the dimension restriction.
Perturbing only off-own singleton rewards changes complete regret by at
most 2e, uniformly over all prescribed and deviating profiles. The same
stationary hazards can be reused in the original game. The resulting
signed conclusion is approximate stationarity; no exact limit equilibrium
or R0 property is asserted for the weak boundary.

The bordering identity and determinant sign in Section 7 are correct.
Together with the supplied four-player matrix they produce nonempty open
singleton-matrix classes in every n ≥ 4, with arbitrary own levels and
arbitrary signed nonsingleton completions. Their exclusion of proper-child
balanced singleton inheritance is valid: a nonzero distribution μ with
Γμ ≥ 0 would have μ = BΓμ > 0 when B > 0. This compares that specific
inheritance criterion only.

For independent censoring after T rows, prescribed payoff changes by at
most MCᵀ. Each complete response cap increases by at most 2Mαᵢᵀ when
bᵢ > 0, by coupling opponent clocks and retaining the full deviator law.
The packet treats the sole owner's bₖ = 0 case separately and correctly.
Finite-horizon caps for signed late deviations must compare a negative
late singleton with Never; the packet does so. Finite support does not
mean rational probabilities. If rational finite laws are desired, they
follow additionally from continuity: on a fixed finite calendar, the cap
is the maximum of finitely many deadline payoff polynomials, including
the first late deadline and Never. Dense rational hazard approximation
therefore preserves payoff and full regret to any positive tolerance.
This is an existence approximation, not a bound on denominators or an
algorithm computing the real discounted roots.

## Source audit, verification, and remaining question

The uploaded names ending in `(2)` resolve to
[`INTEGER_LCP_DEGREE_CRITERION_FOR_FOUR_PLAYER_QUITTING_GAMES.md`](../exports/INTEGER_LCP_DEGREE_CRITERION_FOR_FOUR_PLAYER_QUITTING_GAMES.md)
and
[`INVERSE_POSITIVE_SINGLETON_MATRIX_DISCOUNTED_INDEX_ESCAPE.md`](../exports/INVERSE_POSITIVE_SINGLETON_MATRIX_DISCOUNTED_INDEX_ESCAPE.md).
They already supply the Fin4 integer-degree mechanism and weak-inverse
approximation. They expressly do not claim an unrestricted player-count
theorem or exact stationary equilibrium. The new repair and original-table
local-to-global composition strengthen their strategic output and scope.

The bounded source route was the discounted displacement and terminal
selection entries of `docs/TOOLKIT.md` and `docs/FRONTIER.md`. Declarations
inspected under their imports, with paths relative to the repository root:

- `quittingDiscountedDisplacement`, `quittingDiscountedClippedMap_eq_self_iff`,
  `quittingDiscountedDenominator_mul_endpointDifference`, and
  `continuous_quittingDiscountedClippedMap`,
  `UniformEquilibrium/Quitting/Stationary/DiscountedDisplacement.lean`.
- `hasFDerivAt_quittingDiscountedDisplacement_zero` and
  `quittingDiscountedSingletonLinearization_apply`,
  `UniformEquilibrium/Quitting/Stationary/DiscountedAmbientDerivative.lean`.
- `quittingSingletonMatrix`,
  `UniformEquilibrium/Quitting/Classification/LCP/QuittingRewardAdapter.lean`.
- `quittingBestReplyValue_stationary` and
  `quittingTerminalPayoff_update_stationary_le_cap`,
  `UniformEquilibrium/Quitting/Stationary/MinMax.lean`.
- `IsR0Matrix` and `IsStandardLCPSolution`,
  `MathUE/LinearProgramming/CopositiveQ.lean`;
  `exists_bound_sum_of_isR0Matrix`,
  `MathUE/LinearProgramming/CopositiveQCorollaries.lean`;
  `r0Margin_pos_iff_isR0Matrix`,
  `MathUE/LinearProgramming/R0Margin.lean`.
- `quittingGame_isUniformEquilibriumPayoff_of_terminalNash_tendsto`,
  `quittingGame_isUniformEquilibriumPayoff_of_terminalNash_exact`, and
  `quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors`,
  `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`.
- `quittingUniformEquilibriumPayoffConjecture`,
  `UniformEquilibrium/Quitting/Conjecture/Basic.lean`: an open proposition.

These were static declaration reads, not a new Lean build. The existing
terminal selection theorem supplies the fixed-target endpoint; the packet's
direct timing argument is needed to retain stationary implementations.

The paper-order source `Literature/SolanAndSolan2020.lean`, model Section 2.1
and discounted Section 3.1, confirms the stopping-law and stationary
discounted conventions. Its standing own-singleton normalization and
arbitrary Never payoff differ from this packet's arbitrary own levels and
zero Never; no normalized-paper theorem is silently transported here.
The new repair proof is self-contained. No literature-wide novelty search
or priority claim is made.

Gowda, *Applications of Degree Theory to Linear Complementarity Problems*,
Section 2, printed pages 869–871, was inspected in the
[author-hosted original](https://userpages.umbc.edu/~gowda/papers/trGOW93-01.pdf).
It supplies the precise min-map convention, R0 degree, boundary-safe
homotopy, excision, additivity, and determinant-sign local index used here.
The game application is proved in the packet, not quoted from that paper.

The companion was read before execution. All five `check_*` functions were
run through `runpy.run_path(..., run_name='review_import')`; its file-writing
`main` was not called. Its 800 Bellman coordinate identities, 108 sign
implications, 14 ambient expansions, 200 repair profiles (100/48/52 branch
split), four signed families, inverse matrices, support inventory, and
finite-clock splice assertions all passed. The five- and six-player
determinants are −750 and −17250. These are finite exact regressions,
not proof of the universal degree theorem. The precise reproduction is:

```python
import runpy
m = runpy.run_path('math/gpt/VERIFY_CARDINAL_FREE_LCP_INDEX_ESCAPE.py',
                  run_name='review_import')
for name in ('check_discount_algebra', 'check_linearization',
             'check_matrices', 'check_negative_owner_compiler',
             'check_stationary_repair'):
    print(name, m[name]())
```

Independent boundary falsification also enumerated two-player rewards in
{−1,0,1}⁶, hazards in {0,1/10,1/2,1}², and discounts in {1/4,1/2,3/4},
retaining exactly those with the three Bellman face signs and a > 0.
All 6,096 retained equilibria passed the repair bound, including 3,510
zero deleted clocks and 4,482 upper-face cases. The branch comparison is
exact using 4bₖ² < xa² in place of bₖ < a√x/2; the bound is checked by
E ≤ 2 and either E−x ≤ 0 or (E−x)² ≤ 4x, with M = 1. This grid is
experimental corroboration of boundary handling only.

The concrete remaining research question is what can replace the vanished
outer-degree obstruction when Γ is R0 and κ(Γ) = 1. Neither the quantitative
repair nor the necessary O(λ) rate excludes that class. A separate independent
review remains necessary before any export decision.
