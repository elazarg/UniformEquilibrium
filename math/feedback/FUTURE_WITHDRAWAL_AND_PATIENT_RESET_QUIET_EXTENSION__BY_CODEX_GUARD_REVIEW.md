# Independent review of future withdrawal and patient reset

## Verdict and scope

PASS for the complete terminal compiler, pointwise limiting characterization,
Never relaxation, specified-target and signed Fin4 conclusions, plain
cancellation variant, exact fixture, and full reward neighborhood. No repair
to these original main claims is required. The terminal-only evaluation
boundary and distinction from atom withdrawal must remain explicit.

I read the entire original
`gpt/FUTURE_WITHDRAWAL_AND_PATIENT_RESET_QUIET_EXTENSION.md`, SHA-256
`ae78f4477d3064cd0492843eedf40a5845106624b347e2144ec25856856bdab9`,
and the entire 252-line checker `gpt/VERIFY_PATIENT_RESET_QUIET_EXTENSION.py`,
SHA-256 `6bdd89a91a6c94dd7bc3796821eb2eea907f755686d670175089abbddec5c988`.
The checker performs only internal standard-library exact-fraction arithmetic
and printing. Running `python -B gpt/VERIFY_PATIENT_RESET_QUIET_EXTENSION.py`
passed every assertion. Its finite order-type checks are supplementary
regressions, not a substitute for the general proof.

The question is whether explicit raw rewards and nonnegative weights yield
complete terminal regret domination for EVERY actual independent child
profile, and thereby one fixed uniform-equilibrium payoff for an arbitrary
signed four-player table passing the test. This is an actual-data producer,
not a verifier requiring an assumed favorable child profile.

## Patient replacement and complete behavioral coverage

For each finite patience L, the response depends only on the child's own
sampled clock, an independent replica of the proposed outsider clock, and
the reward table. It leaves earlier quits unchanged and replaces future
quits by the finite date Z+L when s_i≥0, or by Never otherwise. It is a
legal independent unilateral replacement, even when it replaces an old
Never by a late finite quit. That last possibility is essential to the
max(0,s_i) contribution on joint Never.

The deterministic limit proof is exhaustive. An earlier child absorption
is unchanged. At a tied outsider deadline, a future replacement of a member
of a nonsingleton first coalition leaves the other members at that same
date. For a singleton owner it reveals the first later opponent coalition,
or yields max(0,s_i) if every opponent is Never. In the nonnegative case
this is a limit of payoffs of actual later finite quits, NOT the payoff of
the limiting Never law.

When the outsider preempts a later first child coalition, the same patient
limit removes a member of that coalition; a nonmember eventually leaves
the coalition unchanged. This is why the withdrawal term occurs in F as
well as J. Joint Never gives the modified N row exactly. A Never outsider
deadline leaves every operation unchanged. The minimum defining c_i
contains all possible later passive coalitions and max(0,s_i), including
the one-child case where there are no passive coalitions.

For every finite L, each actual response gain is at most the original
child's full regret. Gains have pointwise limits and are uniformly bounded
by twice a reward bound. Bounded convergence therefore bounds the limiting
expected gain by that same regret. Nonnegative weights then give the
outside comparison for each complete outsider law; only afterwards is
the outsider supremum taken. No cap attainment or exchange of supremum
with limit/expectation is assumed.

The shared outsider replica couples separate unilateral experiments; it
does not correlate the prescribed players. Advancing and patient resetting
both act on future clocks, so their generic cost is λ_i+μ_i, not the
disjoint-event maximum available to deadline-atom withdrawal.

The necessity claim is accurately restricted to these fixed operations and
their universal pointwise terminal LIMIT inequality. Joint Never, first A
at date 1 with deadline 0, and first A at date 0 recover N/F/J. The singleton
case chooses a hidden later coalition or all opponents Never attaining the
finite minimum. The other reset terms vanish in the limit, so each raw row
is actually recovered.

## Cancellation and a falsified stronger evaluation claim

Plain cancellation uses the nonpositive floor including zero and the OLD
Never row. Its evaluated future residual splits into

    [f(t)−f(τ)] times the old Never residual
      + f(τ) times the modified future-row residual.

Both coefficients are nonnegative. At a singleton withdrawal, any later
signed payoff is bounded below by the current evaluation weight times the
nonpositive cancellation floor. Thus the separate all-evaluation theorem
is valid, including finite horizons and normalized discounts.

The stronger patient criterion itself cannot be transported to every
evaluation with the same numerical constant. I independently checked this
exact boundary example (child {0,1}, outsider 2):

| Coalition | r₀ | r₁ | r₂ |
|---|---:|---:|---:|
| 0 | 1 | 0 | 1 |
| 1 | 2 | 0 | 1 |
| 2 | 0 | 0 | 1 |
| 01 | 1 | 0 | 0 |
| 02 | 0 | 0 | 1 |
| 12 | 0 | 0 | 1 |
| 012 | 0 | 0 | 1 |

Patient weights λ=(0,0), μ=(1,0) pass all rows: a₀=c₀=1,
the singleton withdrawal gain is zero, and the pair withdrawal gain is
one. Let both children quit surely at date 1. At horizon 3, child 0's
prescribed payoff is 1/3 and its cap is 2/3, so its regret is 1/3. The
quiet outsider's payoff is zero and cap is 2/3. Hence the proposed evaluated
coefficient-one inequality fails. For discount factor d∈(0,1), the two
regrets are max(d−d²,d²) and d, also strictly violating that inequality.
At terminal evaluation the two regrets equal one, as the theorem predicts.
This is a useful retained boundary, not an objection to the stated theorem.

## Never correction, one target, and actual profiles

Without the N row, only joint child Never contributes the displayed error.
For any child j, late deterministic capping has gain tending to
s_j times joint Never mass. Bounded convergence and the full cap give the
signed inequality before division; s_j>0 is exactly the needed condition
for absorbing that mass term into child regret. No automatic evaluated
relaxation is inferred.

A specified child uniform target supplies terminal approximants at the
same target by passing fixed-profile, fixed-deviation horizon inequalities
to the terminal limit. Quiet lifting keeps those child coordinates exactly.
A subsequence of bounded outsider payoff coordinates selects one full
target before the final accuracy. Terminal regrets tend to zero with it.

Crucially, the exact tracked
`quittingGame_isUniformεEquilibrium_of_terminalNash` in
`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformization.lean`
keeps the SAME prescribed profile when passing to a strictly larger uniform
error. I read the statement and proof directly. Together with convergence
of that fixed profile's prescribed finite-horizon payoff, it preserves the
quiet outsiders' Never strategies in the final uniform approximants. No
unproved strategy-preservation claim is hidden in the payoff-target consumer.

The original consecutive-calendar enumeration is correct. For laws supported
on {0,…,N−1,Never}, scan every 0,…,N and Never. Every later finite reply
is terminally equivalent to N, and all randomized replies are mixtures of
the pure reply menu. The fixed-calendar cap is a finite maximum of
continuous payoffs. The tracked complete finite-menu approximation and
rational density therefore imply termination at each positive strict error.
This does not compute an arbitrary specified real target or give a runtime
bound. The sparse-calendar error in the bidirectional original does not
occur in this manuscript's enumeration.

## The two new raw cones are incomparable

I checked both separating fixtures directly, without inferring one cone's
feasibility or failure from its different regret constant.

First, take one child 0 and outsider 1 with reward rows

    r({0})=(−1,−1), r({1})=(0,0), r({0,1})=(0,0).

Patient λ=0, μ=1 passes: a₀=c₀=0, so its withdrawal gain is one;
N has left side zero, and both F and J have left side one. Bidirectional
F for the singleton child instead asks 1≤0 for every possible advance
weight. Even the bidirectional stationary-security enhancement cannot
repair F, since that enhancement changes only singleton J floors.

Conversely, take child {0,1} and outsider 2:

| Coalition | r₀ | r₁ | r₂ |
|---|---:|---:|---:|
| 0 | 0 | 0 | 0 |
| 1 | −1 | 0 | 0 |
| 2 | 0 | 0 | 0 |
| 01 | −2 | 0 | 0 |
| 02 | 0 | 0 | −1 |
| 12 | 0 | 0 | 0 |
| 012 | 0 | 0 | 1 |

Bidirectional a=(0,0), b=(1,0) passes: N/F are zero inequalities;
the three J left sides are −1,0,1, matched by child-0 withdrawal gains
−1,0,1. For the patient cone, F at {0} is 0≤−μ₀, forcing μ₀=0.
J at {0,1} is 1≤μ₀, because all advance coefficients and the other
withdrawal coefficient vanish. Thus no patient weights work. Charging
future withdrawal as well as tied withdrawal has a genuine raw-table cost.

Both cones contain the advance-only test by setting their withdrawal
weights to zero. Each has its own strict separation from the union of all
old proper-child tests, but neither contains the other. These are fixed-child
raw-cone statements, not assertions about every possible strategy compiler.

## Exact table and open neighborhood

The safe exact checker independently reconstructs the raw floors, modified
N slack 1/2, both F/J slack lists, complete payoff and caps at the stated
date-zero profile, singleton inverse/determinant, residual partition
witnesses, and pure coalition deviations. All agree with the manuscript.
At the explicit equilibrium the sure owner 2's late and Never replies
both equal −7/10, below its prescribed −2/5; its counterfactual tail is
not discarded just because another coordinate sees a sure opponent.

Every old proper-child obstruction is a raw join inequality with
nonpositive coefficients and a positive outsider gain. Its zero coefficients
are structural membership zeros; the remaining negative coefficients and
positive gaps persist under the stated radius 1/100. The new floors are
1-Lipschitz, withdrawal gains 2-Lipschitz, and N/F/J perturbation budgets
are 9δ/2 and 9δ, below the displayed margins.

The inverse perturbation estimate preserves positive inverse and determinant,
so R₀ and degree +1 persist. The all-sure residual values exclude every
candidate invariant pair except {0,1}; the second block-constant witness
has residual gap three and excludes that pair. These inequalities persist
at the stated radius. The same-sign reciprocal singleton comparisons,
negative-row triple obstruction, strict pure deviations, pure pair violating
product-low, and actual small-hazard singleton surpluses justify the other
bounded comparisons. The easy exact equilibrium is correctly retained:
this is a new raw class, not evidence that the fixture is strategically hard
for every other method.

## Source audit and final boundary

Exact tracked declarations read for the shared semantic interfaces were
`quittingBehaviorStoppingLaws_update`,
`quittingTerminalPayoff_update_eq_expect_behaviorStoppingLaws`, and
`quittingBehaviorDeviationPayoffCap_eq_pureTime` in
`UniformEquilibrium/Quitting/Paths/CounterfactualStoppingLaw.lean`;
`exists_finiteDeadlineTimingProfile_approximation` in
`UniformEquilibrium/Quitting/Terminal/FiniteMenuFullProfileApproximation.lean`;
and `quittingGame_isUniformEquilibriumPayoff_of_terminalNash_tendsto` in
`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`.
The same-profile uniformization declaration was checked separately above.

The at-most-three child entrance uses the exact tracked one-, two-, and
three-player existence declarations in their respective
`UniformEquilibrium/Quitting/Classification/OnePlayer/Existence.lean`,
`UniformEquilibrium/Quitting/Classification/TwoPlayer/Existence.lean`, and
`UniformEquilibrium/Quitting/Classification/ThreePlayer/Existence.lean`
files, followed by finite relabeling. Their actual statements were read;
the Fin 3 statement is not silently treated as a theorem for every smaller
player type. Git tracking was checked for each named source path.

No new Lean theorem, full conjecture result, arbitrary-source consumer,
public correlation, or modified-nonmover cap premise is asserted. The
complete original theorem passes, with the terminal/evaluated distinctions
and raw-cone incomparability retained in any combined packet.
