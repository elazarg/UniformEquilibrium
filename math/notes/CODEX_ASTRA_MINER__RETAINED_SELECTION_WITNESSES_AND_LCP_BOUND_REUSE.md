# Retained selection witnesses and reuse of exact LCP bounds

Identity: CODEX_ASTRA_MINER.

Status: one bounded static proof-mining pass. The Lean declarations below were
read under their current imports; no new Lean check, axiom audit, production
change, experiment, or theorem implementation was performed in this pass.
The proposed adapters are routine compositions of existing or exported known
mathematics, not new uniform-equilibrium mathematics. No export seal is claimed.

## Question and scope

Which small interfaces would preserve information already available in the
completed inverse-stretch and finite-word constructions, and which older
declarations can replace planned proof work in the new discounted-index route?

The entry points were the finite-word, semantic-carrier, and first-hit sections
of `docs/TOOLKIT.md`. This pass followed their named modules and the source
correspondence of the queued packets. It compared the adaptive-child,
finite-calendar raw-table, finite-cap-threshold, payoff-exclusion/exact-suffix,
membership-stretch source, completed inverse-stretch, opposed-three-sure, and
inverse-positive packets. The inverse-positive and newly arrived
`INTEGER_LCP_DEGREE_CRITERION_FOR_FOUR_PLAYER_QUITTING_GAMES.md` packets were
read in full, including their matrix examples, boundary cases, and nonclaims.

The selection follows
[the cross-episode guidance](CODEX_LARCH__CROSS_EPISODE_PATTERN_MINING_ROUND_TWO.md):
look for a missing retained witness or a distant constructor-to-premise match,
and reject already explicit connections. There is no claim of exhaustive
repository or literature novelty.

Three findings survive that test:

1. Older fixed-skeleton payoff closure already gives a target-retaining theorem
   and duplicates the new target-free quitting closure endpoint.
2. The selected-owner renewal can retain the very payoff witness which justified
   that owner's selection; its local step need not assume exclusion at all words.
3. The exact `R0` solution bound applies to the discounted polynomial remainder
   by changing the right-hand side, without a new approximate-LCP theory.

## 1. Older payoff closure is stronger than the existential endpoint

### Already present

`StochasticGame.isUniformEquilibriumPayoff_of_uniform_stagePayoff_limit`
(`UniformEquilibrium/ProofView/Concepts/Stochastic/Equilibrium/Uniform.lean`)
has the following exact scope. Fix one game skeleton, a finite player type,
finite states and finite action types, and one initial state. If stage-payoff
tables converge uniformly to its table, targets converge uniformly across
players to a specified target `v`, and every approximating table has its
specified target as a uniform-equilibrium payoff, then **that same `v`** is a
uniform-equilibrium payoff of the original game.

The quantifiers are over every positive tolerance followed by one eventual
index bound. At each accuracy the proof reuses an actual nearby game's
behavioral profile and its horizon threshold. It takes no limit of strategies,
does not require cap attainment, and retains all behavioral deviations.

The direct tolerance version is
`StochasticGame.isUniformEquilibriumPayoff_of_arbitrarily_close_stagePayoffs`
in the same file. If the targets have not already been selected to converge,
`StochasticGame.exists_uniformEquilibriumPayoff_of_uniform_stagePayoff_limit`
(`UniformEquilibrium/ProofView/Concepts/Stochastic/Equilibrium/Uniform/PayoffExistenceClosure.lean`)
performs finite-dimensional target compactness itself.

There is already a literal quitting-table specialization:
`quittingGame_exists_uniformEquilibriumPayoff_of_arbitrarily_close_rewards`
(`UniformEquilibrium/ProofView/Concepts/Stochastic/Models/Quitting/UniformPayoffExistenceClosure.lean`).
Its premise is exactly: every positive reward tolerance admits a nearby raw
table with some uniform payoff; its conclusion is existence for the original
raw table. Nearby targets may vary. The same file's
`quittingGame_withStagePayoff_eq` is the definitional skeleton bridge.

### Actionable consequence

The new
`exists_uniformEquilibriumPayoff_of_arbitrarily_close_reward_tables`
(`UniformEquilibrium/Quitting/Terminal/TerminalExploitabilityRewardRobustness.lean`)
has the same target-free contract as that older quitting specialization. A
future cleanup can make the new endpoint delegate to the older one, after
checking the intended narrow import boundary. Its independent proof through
terminal all-errors selection is sound; this finding is duplication, not a
mathematical defect.

Do **not** discard the new module's substantive additional results:
`abs_quittingContinuationBestResponseValue_sub_le_of_reward_close`,
`abs_quittingTerminalExploitability_sub_le_of_reward_close`,
`abs_quittingTerminalExploitabilityInf_sub_le_of_reward_close`, and
`quittingTerminalExploitabilityInf_scaleQuittingReward`. They control complete
caps, actual maximum debt, the unrestricted infimum, and scaling, rather than
only payoff existence.

For any later perturbative argument whose payoff endpoint matters, use the
older target-retaining theorem instead of forgetting that endpoint and then
selecting an unrelated one. This is an available stronger consumer, not a new
closedness proposal. It does not allow varying transition kernels, arbitrary
terminal translations with Never fixed, or limit claims about the strategies.

The general LCP packet now recovers the nonnegative-inverse class without
reward approximation. Thus closedness is not a prerequisite of its shorter
main route, even though it remains useful for the separate singleton-fiber
source construction.

## 2. Preserve the selected owner's actual exclusion witness

### Exact current producer and the information it drops

`exists_finiteWord_ownerExclusion_quadraticDebtStep`
(`UniformEquilibrium/Quitting/Paths/FiniteWordSelectedOwnerStep.lean`) takes
`QuittingFiniteWordOwnerExclusion reward Eligible`, which quantifies over
**all** finite words. Its proof applies that hypothesis exactly once, to
`oldRoots`, obtaining one owner with

    Eligible owner and U_owner(oldRoots) <= singleton_owner.

That same owner is fed to the actual cap-threshold block constructor. Its
payoff comparison proves that the cap-to-singleton margin is at most the
current total debt, so the maximum in the general threshold theorem equals
that debt. The output retains the owner, eligibility, literal block, row bound,
and quadratic complete-debt decrease, but not the displayed payoff comparison.

`QuittingSelectedOwnerRenewal`
(`UniformEquilibrium/Quitting/Paths/FiniteWordSelectedOwnerRates.lean`) likewise
stores `owner`, `owner_eligible`, `block`, an empty-block rule at nonpositive
debt, the length bound, and the decrease. It does not assert that its stored
owner is the actual exclusion witness at the old word. The existence proof
had that witness, but the public record discards it.

This is not a correctness gap in the present recurrence: its proof only uses
the fields it stores. In particular, one must not assert that every inhabitant
of the current record already has the missing payoff property.

### Small proposed extraction

Extract a local step with a **specified** owner and only the premises:

- an actual old finite root word and positive current total debt;
- `Eligible owner` and its actual payoff at most its own singleton;
- a specified strict blocker of this owner;
- a positive bound on all absolute rewards.

It returns the same cap-threshold block with the existing row and debt bounds.
The current universal-exclusion theorem then chooses the owner and delegates.
Add a same-owner payoff field to the richer renewal constructor, or provide a
separate richer result if preserving the current record is preferable. The
nonpositive-debt branch can also retain a payoff witness because its existence
proof already invokes exclusion there.

The relevant downstream declarations are
`quittingSelectedOwnerExactWords`,
`exists_quittingSelectedOwnerExactWord_debt_and_length_le`, and
`exists_finiteWord_debtSum_and_length_le_of_ownerExclusion`
in the rates file. Retaining the owner comparison would let a consumer inspect
the *actual selected phase* together with its blocker, rather than rerun an
existential exclusion theorem and possibly select another owner.

### Optional next consumer, not implemented here

A finite failure-aware version can stop at either a low-debt word or a word
whose payoffs strictly exceed the singleton for every eligible owner. It would
test exclusion only at visited words, use the local step when a witness exists,
and retain the visited word when none exists. The existing reciprocal decrease
and common blocker floor give the finite-phase bound on the successful-step
branch. Such a result would expose a literal failure witness instead of making
global exclusion a prerequisite for constructing any intermediate data.

This is a proposed routine reformulation of the existing finite stopping proof,
not a checked bounded counterexample theorem. The present exact-root selector
uses `Classical.choice`; it is not an executable rational algorithm. A rational
version must use the actual approximate-root producer and its different error
budget. A failed exclusion test refutes only that specified eligible-owner
condition, not uniform-equilibrium existence. Empty eligibility makes that
failure conclusion vacuous and must not be used to select an owner.

Bounded novelty check: the payoff-exclusion export already permits a designated
subset with signed outsiders. That is **not** this finding. The missing item is
the same selected owner's retained witness and the strictly local one-step
premise, not a new eligible-player theorem or new rate.

## 3. Treat the discounted remainder as an exact LCP right-hand side

### Existing stronger bound

`Math.LinearProgramming.sum_le_of_isStandardLCPSolution`
(`MathUE/LinearProgramming/R0Margin.lean`) applies to arbitrary finite nonempty
coordinate types, with no copositivity or nonnegative right-hand-side premise.
Writing `n` for their cardinality and `mu = r0Margin Gamma > 0`, it gives

    z solves LCP(Gamma,b) and |b_i| <= B
        implies sum_i z_i <= (n+1) B / mu.

`r0Margin_pos_iff_isR0Matrix` supplies positivity of the margin from `R0`.
`IsStandardLCPSolution` and `lcpResidual`
(`MathUE/LinearProgramming/CopositiveQ.lean`) use the row convention
`b_i + sum_j z_j Gamma_ij`.

The new LCP packet cites the neighboring qualitative boundedness theorem and
margin openness, but its no-escape proof normalizes an unbounded sequence of
scaled hazards. The following direct match is worth exposing before developing
separate approximate-complementarity machinery.

### Proposed exact adapter and elementary consequence

Suppose the actual discounted polynomial has been proved to satisfy

    D_i = lambda*a_i - sum_j q_j Gamma_ij + e_i,
    q_i >= 0, D_i <= 0, q_i*D_i = 0.

Then `q` is an **exact** `IsStandardLCPSolution Gamma b q` for

    b_i = -lambda*a_i - e_i.

The residual is exactly `-D_i`. The fact that this right-hand side depends on
the current hazard is harmless: the existing bound applies to every bounded
right-hand side, not merely a preselected independent one.

For a precise conditional quantitative target, put

    t = sum_i q_i, C = (n+1)/mu,
    lambda >= 0, A >= 0, K >= 0,
    |a_i| <= A, |e_i| <= K*(lambda+t)^2.

The existing theorem gives

    t <= C*(lambda*A + K*(lambda+t)^2).

Under the additional smallness condition `C*K*(lambda+t) <= 1/2`, elementary
absorption gives `t <= (2*C*A+1)*lambda`. This is a routine scalar corollary,
not a new game-theoretic localization principle. It also handles `K=0` without
dividing by the remainder constant.

For discounted fixed points the signs and complementarity above hold only
after excluding the upper face: `q_i<1` for every coordinate. At `q_i=1` the
actual Bellman condition has the opposite weak sign, so one cannot apply this
adapter globally on the strategy cube.

### Source obligations and consumer

The actual polynomial expansion and the statement that **every** small-discount
fixed point has `q` close to zero remain mandatory. The latter still needs the
specified-endpoint full Bellman-assignment lift and the original-game
auxiliary-germ consumer; an arbitrary selected germ is insufficient. Once that
uniform smallness is proved, it supplies both absence of upper faces and the
displayed absorption condition uniformly over all fixed points.

This yields the bounded scaled region required for the expanded-domain total
degree comparison, without strict positivity of each hazard, strict
complementarity, nonsingular principal matrices, or a finite branch inventory.
The same existing exact solution bound also chooses a sufficiently large box
for the limiting `LCP(Gamma,-a)` root set.

This proposal does not supply integer Brouwer degree, analytic curve selection,
an explicit no-escape discount cutoff, or a computable value of `r0Margin`.
The margin definition is noncomputable; a certified positive numerical lower
bound would be a separate input or separately proved encoded-data result.

## 4. Rejected discoveries and packet boundaries

- **Uniform finite-word approximation:** already present more quantitatively.
  `tendsto_quittingControllerFiniteWordValue`
  (`UniformEquilibrium/Quitting/ControllerTester/FiniteWordValue.lean`) gives
  pointwise convergence of attained finite-word minima. More strongly,
  `escapeAwareQuantileClock_fin4_normalized_quantitative_bracket` and
  `exists_finiteClockSemanticPair_exploitability_eq_upper`
  (`Research/Quitting/EscapeAwareQuantileClockHierarchy.lean`) give the
  `24/level` approximation on support `8*level+1`. These Research sources were
  statically inspected, not checked here or promoted by this report.
- **Finite reward-independent portfolios:** already explicitly stated with
  error `24/m + 16*(8*m+1)/D` in
  [the existing portfolio rate note](CODEX_SKEPTIC__EXPLICIT_FINITE_PORTFOLIO_RATE.md).
  It cites the residual-floor rationalization and full counterfactual TV
  estimates. A weaker compactness-only portfolio statement would be a
  rediscovery, not a useful new proposal.
- **Exact-scale termination:** `exists_finFourExactScaleStep`
  (`Research/Quitting/FinFourExactScaleResolution.lean`) already terminates
  each positive rational scale for normalized rational Fin4 input, choosing
  between an upper profile certificate and a lower certificate. This is not
  decision of whether the nonnegative global infimum is exactly zero. No new
  check of this Research theorem or its axioms was performed here.
- **Two sure quitters erase arbitrary tails:** already proved by
  `quittingTerminalSemanticPrefix_congr_of_twoSureQuitters`
  (`UniformEquilibrium/Diagnostics/Quitting/TwoSureProductRootTailScreen.lean`),
  for arbitrary semantic tails, not only attainable ones. Its stationary-to-
  root-then-Never bridge is also explicit. The completed inverse source retains
  its unpadded root provenance; this theorem does not erase a silent prefix.
- **Three-sure mixed optional support and one sure reversing owner:** already
  produced from the actual source by
  `exists_sureOwner_strictOptionalReversal_of_membershipStretch_positiveMinimum_finFour`
  (`UniformEquilibrium/Diagnostics/Quitting/ThreeSureMembershipReversal.lean`).
  The next opposed-orientation theorem is supplied new packet mathematics,
  not something obtained by merely relabeling the present one-owner witness.
- **All-player ties, strict half, and generic losing-owner counting:** these
  are explicit parts of the completed inverse chain. Their known compositions,
  weighted coalition partition identities, and solo-cap links are not repeated
  as discoveries. The earlier maximum-debt collar proposals are also not new
  findings of this pass.

## 5. Scheduling and the next bounded checks

First, extract the local selected-owner step and preserve the same-owner payoff
comparison. This is the smallest direct producer improvement and needs no new
mathematical library.

Second, remove duplication in the target-free reward-closure endpoint only if
the narrow import review approves; retain the new cap and infimum estimates.
Use the already proved target-retaining closure whenever a later source fixes
its payoff endpoint.

For the new matrix packets, prefer one shared full-assignment discounted source
and the general `R0`/total integer-degree route. Do not first implement a second
strict-interior IFT pipeline merely to recover the inverse-nonnegative class:
the new packet's all-ones test computes its degree directly, after the separate
no-UE-to-full-matrix-`R0` step. Uniqueness of the all-ones test solution alone
does not prove `R0`; the packet's permutation-matrix boundary demonstrates why.

The small LCP remainder adapter above can be implemented once the literal
discounted displacement exists. The large library obligations remain
specified-endpoint analytic curve selection and the necessary integer-degree
theorems. Mod-two parity does not distinguish the required signs. Neither this
mining pass nor the existing interfaces settle the degree-one residual class.

The next requested review should choose between the local selected-owner
extraction and the exact residual-as-right-hand-side adapter. No unrestricted
UE conjecture work, source re-maximization, or new mathematical research is
needed for either bounded task.
