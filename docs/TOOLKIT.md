# Uniform-equilibrium toolkit

This page organizes the integrated formal corpus by mathematical job. It is a
maintained interface map, not a progress report: headline declarations are in
[`STATUS.md`](STATUS.md), the mathematical boundary is in
[`FRONTIER.md`](FRONTIER.md), and the promotion process is in
[`PIPELINE.md`](PIPELINE.md).

The central distinction is between a **compiler**, which turns a supplied
certificate into a uniform payoff, and a **producer**, which constructs that
certificate from more primitive game data.  A verifier, compactness theorem,
or counterexample restriction is not silently counted as either one.

## Dependency shape

```text
game or analytic data
        |
        v
producer / selector -----> certificate or executable path
                                  |
                                  v
                         verifier / compiler
                                  |
                                  v
                   IsUniformEquilibriumPayoff

closure and transfer tools move proved results between nearby games or
payoff descriptions; diagnostics and no-go results constrain every branch
without producing a witness.
```

## Canonical project entry points

| Family | Canonical import | What it exports |
| --- | --- | --- |
| Uniform-payoff consequences | `UniformEquilibrium/Diagnostics/Uniform/Consequences.lean` | Semantic waist dependencies, target equivalence under vanishing payoff gaps, potential shaping, tail-width and bounded-work characterizations, and transition discontinuity. |
| Adaptive-potential systems | `UniformEquilibrium/Certificates/Adaptive/PotentialSystemTools.lean` | The single `AdaptivePotentialSystemAt` structure together with retargeting, profile transport, ledger conversion, finite-time bounds, and owner-separated assembly. |
| Quitting terminal selection | `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean` | The equivalence between terminal approximate Nash existence at every accuracy and uniform-payoff existence for finite quitting games. |
| Diagonal target tails | `UniformEquilibrium/Quitting/Terminal/TargetTail/DiagonalTargetTail.lean` | Exact-prefix plus player-indexed closed-tail compilation and its counterexample restriction. |
| Support-retaining paths | `UniformEquilibrium/Quitting/Paths/SupportWitnessUniform.lean` | Infinite support-rational paths, finite periodic witnesses, and signed, absolute-weighted, and single-seam projective-lasso compilation. |
| Cyclic `K/N` finite words | `UniformEquilibrium/Quitting/Cycles/CyclicKofNPlayerPhaseHazards.lean` | Translated-block support clocks, positive player-and-phase hazards, canonical terminal evaluation, and a finite exact-Nash compiler. |
| Essential APS | `UniformEquilibrium/Quitting/EssentialAPS/All.lean` | The complete singleton-flow APS layer, including the adaptive-mesh capstone. |
| Projective packets and lassos | `UniformEquilibrium/Quitting/Projective/LassoAll.lean` | Matching-order analytic packets, packet-target mismatch, resolved-chart/Farkas contracts, exact signed monodromy, finite charged return, forward-block single-seam closing, and lasso compilation. |
| Punishment-completed cycles | `UniformEquilibrium/Quitting/Punishment/CompletedCycle.lean` | Coupled phase-switch caps, exact instant-punishment characterization, and exact absorbing cycles completed coordinatewise by contraction or credible punishment. |
| Truncated-ledger boundary | `UniformEquilibrium/Quitting/Debt/Ledger/TruncatedLedgerCapBoundary.lean` | The sound package compiler interface together with one- and two-player counterexamples to treating it as a universal normal form. |
| Face circulations | `UniformEquilibrium/Quitting/Circulation/FaceCirculationAll.lean` | Certificate/orbit production, finite charged closing, the compatible compact-path route, concrete payoff examples, and boundary analyses. Use `UniformEquilibrium/Quitting/Circulation/MultiOwnerFaceCirculationFiniteClosing.lean` for the finite compiler. |
| Boundary holonomy | `UniformEquilibrium/Quitting/Boundary/Holonomy/All.lean` | Source-retaining fixed-cutoff compactness together with residual, self-similar, tangent, and realized-coordinate analysis. |
| Reward closure | `GameTheory/GameTheory/Concepts/Stochastic/Models/Quitting/UniformPayoffExistenceClosure.lean` | Fixed-skeleton quitting-game existence under uniform reward limits and dense solved approximants. |
| General nonexistence certificates | `UniformEquilibrium/Diagnostics/Uniform/NonexistenceCertificate.lean` | A uniform positive exploitability gap at arbitrarily late finite horizons rules out every uniform-equilibrium payoff. |
| Quitting terminal exploitability | `UniformEquilibrium/Quitting/Terminal/ExploitabilityGap.lean` | Terminal gaps and the equivalence between finite-quitting nonexistence and some fixed positive terminal gap. |
| Quitting counterexample localization | `UniformEquilibrium/Diagnostics/Quitting/CounterexampleRegime/StoppingLaw/FiveWayLocalization.lean` | Nonexistence produces one counterexample regime, an exhaustive stopping-law frontier for that regime, and its five-way localization. No converse is claimed from the branch data. Singleton compression is an ambient handoff, not a source-matched chronology. |
| Positive-collision reached rows | `UniformEquilibrium/Diagnostics/Quitting/CounterexampleRegime/StoppingLaw/ReachedRowDebtLocalization.lean` | The canonical positive-collision branch yields a strict subsequence and an explicit uniform positive lower bound for one fixed non-observer's legal reached-row gain; nonconvergence is a projection. This does not provide source re-entry or an exact return. |
| Exact repair certificates | `UniformEquilibrium/Diagnostics/Quitting/ExactRepairCertificate.lean` | Proof-carrying cutoff-one, stationary, and cyclic certificate checkers. `UniformEquilibrium/Diagnostics/Quitting/CutoffOneMixedActual.lean` instantiates the cutoff-one checker for an exact rational table and names its zero payoff. |

Import an internal file directly when its narrower interface is the point of
the proof. The umbrellas are navigation and project-integration boundaries,
not external compatibility promises or a ban on precise dependencies.

## Semantic waist and terminal bridge

`GameTheory/GameTheory/Concepts/Stochastic/Equilibrium/Uniform.lean` owns
`StochasticGame.IsUniformEquilibriumPayoff` and
`HasUniformDeviationCapConstructor`.  Their exact equivalence is the
construction waist: a candidate mechanism is complete only after it supplies
the uniform finite-horizon delivery and unilateral-deviation bounds encoded by
that constructor.

For finite quitting games, a producer that already names its payoff target
should retain that target through the terminal-to-uniform bridge.
`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalTargetSemantics.lean`
owns the exact and per-accuracy approximate-target interfaces, while
`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`
also compiles a sequence whose errors tend to zero and whose terminal payoffs
tend to a specified target, provided terminal Nash profiles occur arbitrarily
far along that sequence.  Limits of terminal-payoff vectors remain in the
canonical reward cube, as does every uniform-equilibrium target; the
target-free fallback selects a payoff in that cube from terminal approximate
equilibria available at every positive accuracy.  Compact target selection is
not a substitute for an exact or convergent target already supplied by the
producer.  Terminal verification, target selection, and uniformization remain
separate steps in lower-level proofs.

`UniformEquilibrium/Certificates/Adaptive/PotentialSystemTools.lean` is the transformation facade for the
proof-facing adaptive-potential waist. It deliberately reuses the one
`AdaptivePotentialSystemAt` definition: consolidation here means a canonical
API surface, not a second structure. Public stopping and response compilers
remain separate because they add causal-law realization and credibility
obligations.

## Positive construction families

| Family | Required input | Production output | Remaining nonclaim |
| --- | --- | --- | --- |
| Diagonal target tail | Accuracy-indexed exact Nash--Bellman prefixes with small joint survival and player-indexed target-closed tails | Terminal approximate equilibria and hence a uniform payoff | Does not construct the prefixes or prove their survival certificate. |
| Support witness | At every tolerance, a support-wise approximately optimal root path, divergent absorption, and continuation-by-continuation individual rationality; alternatively a finite periodic witness with one absorbing phase | A terminal `3ε` profile and target-free uniform-payoff existence | Does not produce the paths or cycles for arbitrary games. |
| Cyclic `K/N` finite word | A translated finite block word with positive hazards on every scheduled player-phase pair and exact root Nash at every canonical successor value | Every cyclic entry value is a uniform-equilibrium payoff | Does not produce the finite Nash certificate for an arbitrary reward table; prescribed proper positive-hazard words fail for the self-membership reward. |
| Signed projective lasso | An accepted target and, at every tolerance, a finite root word whose signed survival-weighted monodromy is small relative to absorption for every cyclic entry phase, with support optimality and punishment rationality | Exact periodic correction, a divergent support-rational path, and a uniform payoff | Matching analytic packet extraction neither accepts its endpoint nor constructs the required physical candidate; absolute-weighted variation is only a stronger compatibility interface. |
| Finite charged forward packets | At every charge target, one exact finite forward Bellman packet in a fixed compact carrier, with support optimality and punishment rationality | Compact charged return, a single-seam lasso, and a uniform payoff | Does not produce the packets or consume the complementary bounded-charge branch. |
| Essential APS | A compact convex functional unique-live component with finite-window face avoidance, terminal-freeness, and bounds | A coherent executable path, qualitative deleted-player survival, adaptive finite meshes, and a uniform payoff for every initial component value | Does not prove that an arbitrary game has a nonempty component; pointwise full jumps remain outside the adaptive logarithmic mesh. |
| Multi-owner face circulation | A bounded balanced circulation with positive phase ratios, one common ratio ceiling below `1`, and a payoff floor above the quitting punishment value | Arbitrarily charged finite packets and a uniform payoff by finite closing; independently, a chronological compact path | Does not construct such a circulation for every game or identify the selected target with a named certificate vertex. |
| Punishment-completed finite cycle | An exact absorbing Nash--Bellman cycle where each coordinate either contracts in deleted survival or has punishment value at most its selected solo value | The selected phase value is a uniform-equilibrium payoff; the nonnegative-solo admissible-cycle compiler is a corollary | Does not produce an exact cycle, and does not cover an isolated coordinate whose punishment value exceeds its negative solo value. |
| Two-player closure | An arbitrary finite two-player quitting game | Unconditional uniform-payoff existence, with an explicit zero, owner-solo, blocker-solo, or joint-exit target in each branch | Does not extend the pair-repair classification to three or more players. |
| Three-player closure | An arbitrary finite quitting game on `Fin 3` | Unconditional uniform-payoff existence | Does not settle four or more players or the general stochastic-game proposition. |

The essential-APS and circulation families contain genuine producers relative
to their stated structured inputs.  They are conditional positive strata, not
generic quitting-game existence theorems.

## Reusable infrastructure

| Tool | Module | Use |
| --- | --- | --- |
| Discrete hazard stopping | `MathUE/Probability/DiscreteHazardStopping.lean` | Survival products, first-hit weights, total stopping mass, and bounded stopped-payoff accounting independent of quitting games. |
| Survival products | `MathUE/SurvivalProduct.lean` | Generic finite-product and cumulative-hazard estimates shared by stopping arguments. |
| Compact finite-prefix relations | `MathUE/Topology/CompactFinitePrefixRelation.lean` | Inverse-limit selection from compatible compact finite prefixes; used by circulation paths. |
| Finite charged return | `MathUE/FiniteChargedReturn.lean`, `MathUE/CompactFiniteChargedReturn.lean` | Converts sufficiently charged finite prefixes in one compact carrier into a close ordered block with fixed charge, without one orbit uniform in the target. |
| Finite phase occupation duality | `MathUE/Probability/PhaseOccupationDuality.lean` | Semantic/LP primal equivalence, bounded attainment, phase-bias decoding, and strong duality conditional on occupation feasibility. |
| Cyclic exposure | `MathUE/CyclicExposure.lean` | Sharp exposure bounds for finite permutation systems; the shared-punishment calculation is an application. |
| Cyclic `K/N` collapse | `MathUE/GroupAction/CyclicKofNCollapseClassification.lean` | Exact `N / gcd(K,N)` minimum translated-block period, classification of attainable stabilizer factors, and explicit primitive-block fiber lifts. |
| Nonperiodic Snell supersolution | `UniformEquilibrium/Quitting/Paths/InfinitePathSupersolution.lean` | Turns exact Continue transport, vanishing local Quit error, and survival decay into history-dependent unilateral caps. |
| Target-anchored stopping tail | `UniformEquilibrium/Quitting/Terminal/TargetTail/TargetAnchoredTail.lean` | Constructs one player's stationary-opponent closed tail at a prescribed target. |
| Joint-survival selection | `UniformEquilibrium/Quitting/Paths/JointSurvivalSelection.lean` | Identifies compactly selected continuation values with actual infinite-path terminal values under joint-survival decay. |
| Projective first-event algebra | `MathUE/ProjectiveBellmanPacket.lean` | Exact cemetery/absorption normalization and Bellman balance before any chart or recurrence argument. |
| Affine equality/Farkas alternative | `MathUE/AffineEqualityFarkas.lean` | A finite feasible-tangent-or-dual-row alternative; strategic decoding and arc lifting are separate inputs. |

Phase-occupation duality is optimization infrastructure.  Until a concrete
strategic construction supplies a feasible phase occupation, it is not itself
a game or strategy producer.

## Closure and transfer

- `GameTheory/GameTheory/Concepts/Stochastic/Equilibrium/Uniform/AsymptoticPayoffEquivalence.lean` transfers an exact target across
  profile-uniform finite-average payoff gaps tending to zero.
- `GameTheory/GameTheory/Concepts/Stochastic/Equilibrium/Uniform/ExpectedPotentialShaping.lean` applies that transfer to bounded
  expected-potential coboundaries with an `O(1/T)` endpoint telescope.
- `GameTheory/GameTheory/Concepts/Stochastic/Equilibrium/Uniform/PayoffExistenceClosure.lean` proves target-free existence closure
  under uniform stage-payoff limits on a fixed finite skeleton.
- `GameTheory/GameTheory/Concepts/Stochastic/Models/Quitting/UniformPayoffExistenceClosure.lean` specializes the closure theorem
  to uniformly convergent quitting reward tables.
- `GameTheory/GameTheory/Concepts/Stochastic/Models/Quitting/RootPerturbation.lean` gives local one-coordinate payoff and regret
  bounds; it should not be confused with target-free closure.

These tools transport a supplied mechanism or existence result.  They do not
supply density of solved games or construct a missing certificate.

## Boundary analysis and diagnostics

`UniformEquilibrium/Quitting/Boundary/Holonomy/All.lean` has two complementary compactness modes.
Fixed-cutoff and fixed-last lifts retain the actual root block, endpoints, and
provenance.  Tangent compactness retains only bounded coefficient coordinates
and normalized safety obstructions.  Neither mode closes the escaping-length
problem: the first cannot compactify unbounded literal length, and the second
does not prove realized-image closedness or provide a decoder.

The general reverse diagnostics are:

- arbitrarily thin eventual payoff/deviation intervals are equivalent to
  uniform-payoff existence;
- a fixed target is uniform exactly when it has a bounded excess-work
  certificate;
- positive tail width and late exploitability gaps give exact nonexistence
  witnesses;
- for finite quitting games, existence of some fixed positive terminal
  exploitability gap is exactly equivalent to nonexistence; and
- convergence of transition kernels alone does not preserve uniform-payoff
  targets.

`UniformEquilibrium/Quitting/Debt/Ledger/TruncatedLedgerCapCounterexample.lean` adds a certificate-specific
fence: even a solved two-player zero-solo game need not admit a common-cutoff
truncated-ledger package.  The package compiler is sound, but its hypothesis is
not a necessary normal form for equilibrium existence.

`UniformEquilibrium/Diagnostics/Quitting/CyclicKofNFeasibilityObstruction.lean`
separates the cyclic compiler from a producer: constant, phase-varying, and
player-and-phase positive hazards on a prescribed proper translated block all
fail for one bounded self-membership reward, although that game has a trivial
full-support uniform payoff.  Independently,
`UniformEquilibrium/Diagnostics/Quitting/CyclicKofNSupportedRootRetentionNoGo.lean`
shows that positive retention of one fixed chronological singleton atom over
the finite orbit prefix cannot generate a proper rotating supported-root word.

These characterize or falsify proposed routes.  They are not forward
construction mechanisms.

## Semantic fences

The following distinctions are load-bearing across the toolkit:

1. probabilistic stopped-law accounting is not strategic law realization;
2. a public response or detector is not a credible punishment certificate;
3. positive occupation circulation does not transport a continuation target
   without a separate harmonicity or target-identification theorem;
4. compact coefficient projections do not imply closedness of the set of
   realized strategic blocks;
5. terminal approximate Nash, fixed-profile uniform approximation, and a
   uniform-equilibrium payoff are different notions until a named bridge is
   invoked;
6. a fixed-target closure theorem and target-free existence closure solve
   different problems;
7. positive debt on one explicit legal chain is not positivity of the optimized
   minimum over all chains;
8. the general polynomial Bellman variety is not the physical
   vanishing-discount domain until an explicit slice such as `0 < disc ≤ 1` is
   imposed;
9. a neutral or subsingleton promotion socket—including a vacuous `CellFiber`
   instance—is not realization, compatibility, or an all-accuracy producer;
   and
10. a global occupation that cancels signed defects across different recurrent
    SCCs is not one legal path.  Flow synthesis must choose one reachable
    recurrent component or prove a separate strategic common-randomization
    theorem.

## Universal declaration leaves

Consult [`STATUS.md`](STATUS.md) for the generated declaration kind of the
general and finite-quitting propositions. The truncated-ledger package is a
valid conditional compiler, while its universal-producer claim is refuted by
the two-player counterexample indexed above. The positive compilers narrow
what a universal producer must supply, but are not silently an arbitrary-game
producer.

For new work, first identify the row above whose required input is closest to
the available data.  If no row accepts it, record the missing adapter or
producer explicitly.  In particular, failed subgame reinsertion should preserve
the entering player or marked join inequality, and failed flow synthesis should
preserve the recurrent component and componentwise separator rather than
creating another parallel compiler surface.
