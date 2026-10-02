# Independent audit of weak exclusion and the determinant entrance

Reviewer: CODEX_NOETHER_SUPPORT.
Reviewed source: [supplied manuscript](../gpt/WEAK_SINGLETON_PAYOFF_EXCLUSION_AND_DETERMINANT_SELECTOR.md).
Verdict: the stated results pass independent mathematical audit. No unresolved
proof objection was found. The qualitative newness claim requires the
qualification below. No Lean compilation or export promotion was performed.

## Claims restated

For a finite quitting game with zero Never reward, fix a nonempty witnessing
subset J whose own singleton rewards are nonnegative. If every actual finite
root word has some i∈J with U_i≤s_i, then finite actual laws with total
unrestricted terminal debt below every ε>0 can be constructed. Other players'
singletons can be signed. A finite four-player raw reward criterion enforces
that premise using xy≤z₊z₋ for separate crossed coalition masses.

The manuscript also gives quantitative margins at global positive debt
minima. These are correct but weaker than the separate cap-threshold collar;
I do not recommend duplicating them in a second proposed packet.

## The difficult constructive branch

I checked the charged and uncharged branches independently. When the charged
test fails, B_j−s_j>D−τ for every j. The weak witness i has
d_i>D−τ, outsider debt sum<τ, s_i−τ<U_i≤s_i, and each outsider payoff
U_j>s_j+D−2τ. These are consequences of nonnegative debts and the scalar
sum, with no assumption on the signs of outsider singletons.

Before each solo-i row, outsider Continue is strictly better against actual
U. Since B_j≥U_j, its complete cap also takes the Continue branch. Owner
B_i>s_i remains constant. Exact subtraction gives

    D'=D−θ[(s_i−U_i)+Σ_{j≠i}d_j]≤D.

Thus the solo block cannot hide cap replacement or debt recharge. The owner
need not play an optimal root mixture. Failure of the singleton column test
provides an outsider whose geometric payoff limit lies below s_j+e/4, so the
e/2 crossing occurs in at most the displayed L(e) rows. At crossing its
cap surplus is at most 5e/8, and the next root necessarily satisfies the
charged branch. The stage termination and dyadic O(ε⁻²log(1/ε)) date bound
follow. The constants in the charged step, including
Δ=e²/[512(4M+e/8)]≥e²/(2112M), are consistent.

The stationary exit is verified directly; it does not assert that a limiting
cap realizes the old semantic pair. Its finite truncation works with signed
outsiders. If v_j=r_j({i})<0, Never after truncation has payoff (1−z)v_j
and is the potentially larger endpoint; pre-cutoff and late finite responses
are at most v_j. Hence regret is ≤z max(v_j,0), not z|v_j| by necessity,
and owner regret is zs_i. The bound D≤nMz is valid. This sign check is why
the stated J-only nonnegativity is enough.

Rational grid termination is effective, with actual finite cap computation
including one late date and Never. The Lipschitz bound 4Rn and R=M+D₀
are sufficient throughout. Neither exact finite-menu Nash nor an efficient
grid search is claimed or needed.

## The minimum-margin comparison

At a positive global minimum, the existing cap moat gives B_i−s_i≥D.
For a nonnegative-singleton owner with positive d_i, set
z=B_i−s_i−D and e=D−d_i. The entire outsider-threshold solo block has
exact debt D_k=D+(1−x)z, so it costs at most z even though it may increase
debt. At its crossing the outsider cap margin is at most ρ+e.
An auxiliary root with h=e+δ then yields

    z≥δ(d_i−δ)/(2M+δ)

after sending ρ↓0. The displayed square-completion proves the maximum
Φ_M(d_i) exactly. The decreasing function
D−d+Φ_M(d) has minimum Φ_M(D) for 0≤d≤D. The common cap surplus proof
uses one initial uniform solo row to force a definite surviving-share loss
before the crossing, and its algebra is also correct for d_i=0.

These arguments apply to the compact semantic carrier, without asserting
that a limit point is an actual profile. The carrier maps are continuous
literal prefix maps. No issue was found in their probability mode.

## Determinant and strict separation

The two comparison events use disjoint independent pairs (T₀,T₂) and
(T₁,T₃). The mixed forward/reverse event implies a terminal coalition in
Z₊={{0},{3},{0,3}}; the opposite mixed event implies Z₋={{1},{2},{1,2}}.
This proves x≤α₁α₂, y≤β₁β₂, z₊≥α₁β₂, z₋≥β₁α₂ and xy≤z₊z₋.
Strict comparison ensures finite termination on each crossed event even
when Never occurs elsewhere. Finite ties cause no missing term.

The row inequalities give U₀−s₀≤ax−lz₋ and U₁−s₁≤by−mz₊, because
their Never surplus terms are nonpositive. Strict positivity of both
would contradict ab≤lm and the determinant. This is a raw-table producer
for WE with J={0,1}, not a test on supplied strategic objects.

The rational fixture separates the announced criteria exactly. Pure {2,3}
has surplus (0,1,1,1), so no uniform strict deficit and no weight family
with a common maximum coordinate below one can work. Its active players'
Quit payoffs both exceed their singletons, refuting the own-singleton
low-active root criterion. This comparison is to Q_i≤s_i. The production
`HasLowActiveQuittingRootQuitPayoff` instead uses the fixed level one and
cannot be falsified on the raw fixture by endpoints equal to one. Under
the normalization r'_i(S)=(r_i(S)+t)/(s_i+t), t>0, the own singletons become
one and these two endpoints become (1+t)/t>1, proving failure of that
unit-level predicate for the normalized table. No exact strategic equivalence
under the terminal-only translation is asserted. The correlated half-pair lottery is strictly above s in every
coordinate, refuting nonnegative linear separation of the full reward hull.
This does not exclude other equilibrium constructions. Its one-row exact
equilibrium is correctly disclosed.

## Verification and newness qualification

I read the complete `gpt/VERIFY_WEAK_SINGLETON_EXCLUSION.py` before running
`run_checks()` through `runpy.run_path` with bytecode writing disabled. Its
JSON-writing main block was not executed. All checks passed: 320 exact
scalar identities, 1296 finite independent clock profiles, 155 solo rows,
the exact charged root, and independent complete response caps on 158 rows.
Finite arithmetic supports the examples; the universal theorems rely on
the proofs above.

The existing source theorem
`exists_finFour_strictMinimum_allContinuePlateau_of_no_uniformPayoff`
(`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticFinFourStrictMinimumPlateauIsolation.lean`)
already implies qualitative weak-exclusion UE for Fin4, even with arbitrary
singleton signs. Thus qualitative Fin4 weak exclusion by itself is not a new
boundary. The concrete actual-law algorithm and its uniform table-independent
date bound, the J-only sign scope for general finite I, and the determinant
reward entrance are the reusable additions reviewed here.

The independently read `CAP_THRESHOLD_DEBT_DESCENT.md` also supplies an
actual finite-law selector for all-nonnegative weak exclusion and a stronger
quadratic minimum collar. Its distinct first-cap-threshold proof should not
be treated as newness support for the weaker Φ/Λ margins. Its table-dependent
preemptor-gap bound and the present table-uniform bound are different scopes.

Other checked source interfaces are
`minimumTerminalSemantic_singletonMargin`
(`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticAuxiliaryNashBudget.lean`),
`exists_uniformEquilibriumPayoff_of_nonnegativeWeightChamber`
(`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticNonnegativeWeightChamber.lean`),
`twoDisjointFirstStoppingPairMasses_sqrt_sum_le_one`
(`MathUE/Probability/IndependentFirstStoppingPair.lean`), and
`quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors`
(`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`).
The bounded audit makes no literature-wide priority claim.

A [complete consolidated proposal](../notes/CODEX_NOETHER_SUPPORT__PAYOFF_EXCLUSION_ACTUAL_SELECTORS_AND_EXACT_SUFFIX_LIMITS.md)
is retained for independent cross-review in `notes/`, without the redundant
minimum-margin section. No general Fin4 conclusion is claimed.
