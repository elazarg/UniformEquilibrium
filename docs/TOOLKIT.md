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
| Directed transport theory | `MathUE/DirectedTransport.lean` | Exact and lax path transport; path-category, SCC, condensation, and categorical-retract normal forms; complete-lattice closure; additive cycle and signed-circulation duality; sparse rational and integral finite-inequality certificates; and max-affine path, slack, gauge, and holonomy theory. |
| Uniform-payoff consequences | `UniformEquilibrium/Diagnostics/Uniform/Consequences.lean` | Semantic waist dependencies, target equivalence under vanishing payoff gaps, potential shaping, tail-width and bounded-work characterizations, and transition discontinuity. |
| Adaptive-potential systems | `UniformEquilibrium/Certificates/Adaptive/PotentialSystemTools.lean` | The single `AdaptivePotentialSystemAt` structure together with retargeting, profile transport, ledger conversion, finite-time bounds, and owner-separated assembly. |
| Quitting terminal selection | `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean` | The equivalence between terminal approximate Nash existence at every accuracy and uniform-payoff existence for finite quitting games. |
| Diagonal target tails | `UniformEquilibrium/Quitting/Terminal/TargetTail/DiagonalTargetTail.lean` | Exact-prefix plus player-indexed closed-tail compilation and its counterexample restriction. |
| Support-retaining paths | `UniformEquilibrium/Quitting/Paths/SupportWitnessUniform.lean` | Infinite support-rational paths, finite periodic witnesses, and signed, absolute-weighted, and single-seam projective-lasso compilation. |
| Cyclic `K/N` finite words | `UniformEquilibrium/Quitting/Cycles/CyclicKofNPlayerPhaseHazards.lean` | Translated-block support clocks, positive player-and-phase hazards, canonical terminal evaluation, and a finite exact-Nash compiler. |
| Balanced singleton cycles | `UniformEquilibrium/Quitting/Cycles/BalancedSingletonCertificate.lean` | A one-owner-at-a-time cyclic Bellman certificate with owner indifference, passive-player solo floors, and one positive opponent hazard per player compiles to exact terminal values, explicit square-root finite-horizon Nash/delivery bounds, and a uniform-equilibrium payoff. Finite mesh and collision caps are inferred automatically, so nonsingleton coalition rewards remain arbitrary. |
| Essential APS | `UniformEquilibrium/Quitting/EssentialAPS/All.lean` | The complete singleton-flow APS layer, including the adaptive-mesh capstone. |
| Projective packets and lassos | `UniformEquilibrium/Quitting/Projective/LassoAll.lean` | Matching-order analytic packets, packet-target mismatch, resolved-chart/Farkas contracts, exact signed monodromy, finite charged return, forward-block single-seam closing, and lasso compilation. |
| Punishment-completed cycles | `UniformEquilibrium/Quitting/Punishment/CompletedCycle.lean` | Coupled phase-switch caps, exact instant-punishment characterization, and exact absorbing cycles completed coordinatewise by contraction or credible punishment. |
| Truncated-ledger boundary | `UniformEquilibrium/Quitting/Debt/Ledger/TruncatedLedgerCapBoundary.lean` | The sound package compiler interface together with one- and two-player counterexamples to treating it as a universal normal form. |
| Generated-secant chronological debt | `UniformEquilibrium/Quitting/Debt/Dynamic/ChronologicalDebtShadowing.lean`, `UniformEquilibrium/Quitting/Debt/Dynamic/ExactChronologicalData.lean` | The game-independent two-discount identity gives the sharp `C + 2A` shadowing bound, and its quitting adapter compiles bounded executable data with controlled prescribed and direct-debt forcing, vanishing joint and deleted-player survival, and small initial debt into a terminal `4 * eta` equilibrium. `QuittingChronologicalDebtShadowingCertificate.terminalExploitabilityGap_le` bounds every terminal gap by `4 * eta`, and `quittingGame_exists_uniformEquilibriumPayoff_of_chronologicalDebtShadowing_all_errors` turns certificates at every positive accuracy into one uniform-equilibrium payoff. `exactOfRoots` supplies exact zero-forcing bookkeeping for any root schedule, but it copies the schedule's actual exploitability into the candidate debt and is not a small-debt producer. |
| Stopping-law conditioning and exposure | `MathUE/Probability/DiscreteHazardMixture.lean`, `MathUE/ProbabilityMassFunction/GeneralTotalVariation.lean`, `UniformEquilibrium/Quitting/Paths/StoppingLawExposure.lean` | Finite-cutoff conditioning of a two-component hazard mixture is the exact posterior convex mixture, with posterior difference, odds, and denominator-lower-bound estimates. The explicit source-survival `lambda²`, target-survival `1` example has posterior tending to one and rules out any source-independent linear bound in the prior weight. Arbitrary-PMF total variation controls bounded expectations; for quitting stopping laws it is bounded by the two ever-quit masses, so a profitable radial or nested-radial reset carries quantitative finite stopping mass. These are fresh-law estimates, not residual-port stability after conditioning. |
| Literal opponent-Green debt account | `UniformEquilibrium/Quitting/Root/TerminalDebtGreenAccount.lean`, `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPointwiseDefectGreenRegression.lean` | Actual terminal debt along a literal root sequence satisfies an exact one-step deleted-player-survival account and finite Green telescopes, including bounded-tail and paid-hazard forms. A four-player harmonic regression has vanishing joint survival, vanishing survival after deletion of any one player, and active coordinate defects tending to zero, while every active suffix retains terminal deviation debt at least `1/2`; deleting both active players leaves survival exactly one. Thus pointwise defect decay and the individual deleted-clock limits do not by themselves bound the Green sum or terminal debt. |
| Source-matched chronological boundary | `UniformEquilibrium/Diagnostics/Quitting/CounterexampleRegime/StoppingLaw/SourceMatchedChronologicalData.lean`, `UniformEquilibrium/Diagnostics/Quitting/CounterexampleRegime/StoppingLaw/SourceMatchedChronologicalSurvival.lean`, `UniformEquilibrium/Diagnostics/Quitting/CounterexampleRegime/StoppingLaw/SourceMatchedRadialFreshPacketExposure.lean` | Source-matched radial reset profiles produce executable scheduled roots and their exact chronological data. A repeated finite sample has vanishing joint and deleted-player survival under explicit one-period contraction. Independently, a positive balanced circulation produces a fresh simultaneous radial packet with two distinct positive marginals and one finite cutoff exposing the joint and every one-player-deleted clock by a fixed coefficient times the genuine frontier scale. This packet-local exposure is not persistent residual chronology. The checked regressions show that a debt-decreasing frozen reset need not create opponent exposure and that exact zero forcing need not make the initial debt small. The missing block/splice producer must still obtain contraction and non-tautological candidate tails from the reset-cube packet. |
| Exact charged-packet amplification | `MathUE/ChargedPacketAmplification.lean`, `UniformEquilibrium/Quitting/Bellman/Finite/TerminalExploitabilityPacketAmplification.lean` | `exists_path_charge_gt_of_uniform_tube_packet` concatenates genuine source-matched finite relation paths available at every reachable tube state into paths of arbitrarily large charge. `QuittingTerminalExploitabilityWitness.false_of_uniform_reachable_packet_producer` then contradicts the canonical finite prefix-charge capacity. This is the final consumer of an exact packet producer: it does not lift a stopping-law tangent to a predecessor path, identify residual gain with relation charge, or prove persistent packet availability after the source changes. |
| Full admissible-cycle amplification | `UniformEquilibrium/Quitting/Bellman/Finite/PositiveAdmissibleCycle.lean`, `UniformEquilibrium/Quitting/Bellman/Finite/TerminalExploitabilityCycleExclusion.lean` | `quittingGame_exists_uniformPayoff_of_positive_admissible_cycle` iterates any positive closed path in the full punishment-floor admissible exact Nash--Bellman relation, decodes arbitrarily charged literal finite prefixes, and obtains a uniform-equilibrium payoff. `quittingGame_exists_uniformPayoff_of_positive_admissible_return` reduces this to one positive exact edge plus an exact admissible return. The terminal-exploitability adapter proves that every such cycle has zero charge under a positive terminal gap. These are exact return consumers; they do not construct an edge or return from stopping-law geometry. |
| Exact atom-stack charge obstruction | `UniformEquilibrium/Diagnostics/Quitting/CounterexampleRegime/StoppingLaw/Atom/ExactPrefixCharge.lean` | `QuittingStoppingLawAtomExactPrefixChronology.absorptionSum_tendsto_zero_of_twoActive` proves that the total literal one-row absorption charge of the increasingly long exact access stacks tends to zero whenever two distinct minimum-debt owners are active. The stacks therefore cannot themselves produce unbounded prefix charge. This does not rule out appending a separate positive exact edge with an admissible return. |
| Finite linear charged capacity | `MathUE/FiniteLinearChargedCapacity.lean`, `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/LinearChargedCapacity.lean` | `normalizedPositiveChargedCirculation_iff_unboundedFeasibleCharge` is the exact recession theorem for flat finite charged columns. `stoppingLawFlatTangent_chargedCirculation_xor_strictLyapunovWeight` adapts it to a regime-free flat stopping-law tangent family; in the no-circulation arm, `exists_stoppingLawFlatStrictWeight_capacityBound_of_noCirculation` supplies one positive weight and a universal orthant-feasible charge bound. These are numerical tangent-space statements, not semantic realization or executable chronology. |
| Terminal-semantic splice noncompositionality | `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticCommonWitnessNoncompositionality.lean` | Two explicit profiles have the same complete terminal semantic pair and the same first-stage joint survival, but different player-zero-deleted survival. Prefixing the same collision continuation changes player zero's best-response envelope from `2` to `1 + s`. The semantic pair plus joint survival is therefore not a splice-compositional state descriptor; a labelled deleted clock is genuinely additional data. This is an explicit regression, not a classification of all sufficient state enlargements. |
| Random quitting payoff processes | `UniformEquilibrium/Quitting/PayoffProcess/All.lean` | Measurable approximate-Nash selection, conditional-expectation backward induction, dominated tail approximation, and exact finite-prefix/tail payoff accounting compile every integrably dominated almost-surely convergent quitting payoff process with unit solo exit and capped joint exit in the limit into an adapted `epsilon`-equilibrium for each positive `epsilon`. |
| Face circulations | `UniformEquilibrium/Quitting/Circulation/FaceCirculationAll.lean` | Certificate/orbit production, finite charged closing, compatible compact paths, and cumulative-budget marked-atom consumers. Use `UniformEquilibrium/Quitting/Circulation/MultiOwnerFaceCirculationFiniteClosing.lean` for finite closing and `UniformEquilibrium/Quitting/Circulation/KActiveMarkedAtomBudgetPathConsumer.lean` for the diffuse-clock compiler. |
| Boundary holonomy | `UniformEquilibrium/Quitting/Boundary/Holonomy/All.lean` | Source-retaining fixed-cutoff compactness together with residual, self-similar, tangent, and realized-coordinate analysis. |
| Simon Question 1 boundary | `MathUE/Topology/SimonViabilityBudgetCompiler.lean`, `UniformEquilibrium/Quitting/Classification/AbnormalPlayers.lean` | The seven topological hypotheses are formalized literally, their local escape clause yields a common positive scale and an exact one-edge budgeted prefix, and compatible finite prefixes at every horizon with one common diverging variation budget compile to the requested unbounded extended orbit. The abnormal-player layer separately supplies the attained positive minimum abnormality gap. The seven hypotheses alone have not been proved to produce the compatible prefix family, so `QuestionOneAffirmative` remains an open proposition. |
| Corrected quitting classification boundary | `UniformEquilibrium/Quitting/Classification/Existence/All.lean` | A supplied pointwise alternative compactifies to four fixed branches: stationary, instant punishment, well-supported absorption, or diffuse stationarily generated approximate equilibria. The fourth branch has an exact normal form: bounded-horizon positive-live cells already produce a uniform payoff, vanishing live mass produces instant punishment, and the remaining positive-live divergent-horizon family yields a well-supported absorbing sequence or an all-Continue phantom limit retaining a separate punishment endpoint. A checked one-player phantom shows that the forward value need not equal that punishment endpoint. Neither the pointwise extraction from arbitrary approximate equilibria nor the residual phantom compactification is proved, so this does not close AGKRS Theorem 3.4. |
| Reward closure | `UniformEquilibrium/ProofView/Concepts/Stochastic/Models/Quitting/UniformPayoffExistenceClosure.lean` | Fixed-skeleton quitting-game existence under uniform reward limits and dense solved approximants. |
| General nonexistence certificates | `UniformEquilibrium/Diagnostics/Uniform/NonexistenceCertificate.lean` | A uniform positive exploitability gap at arbitrarily late finite horizons rules out every uniform-equilibrium payoff. |
| Quitting terminal exploitability and minimum semantic debt | `UniformEquilibrium/Quitting/Terminal/ExploitabilityGap.lean`, `UniformEquilibrium/Quitting/Terminal/PositiveMinimumSemanticDebt.lean` | Terminal gaps and the equivalence between finite-quitting nonexistence and some fixed positive terminal gap. For inhabited finite player types, `exists_uniformEquilibriumPayoff_iff_hasZeroMinimumTerminalSemanticDebt` identifies existence exactly with zero attained minimum total semantic debt, while `not_exists_uniformEquilibriumPayoff_iff_hasPositiveMinimumTerminalSemanticDebt` identifies nonexistence with a positive attained minimum. |
| Full-core deadlock contraction | `UniformEquilibrium/Quitting/Classification/LCP/FullCore/All.lean` | The named four-player completion family, its full normal-core proof, exact coordinatewise contraction factors, semantic fixed-pair realization, the resulting `1227/96755` upper bound on every global debt floor, and the downstream bound on every terminal exploitability gap. This does not prove zero minimum debt or uniform-payoff existence. |
| Full-core deadlock reduced lassos | `UniformEquilibrium/Quitting/Classification/LCP/FullCore/DeadlockReducedSingletonLassoBarrier.lean` | Every finite reduced cyclic word of active ideal-singleton blocks for the displayed deadlock matrix has strictly positive debt at every phase. The proof includes the exact homogeneous complementarity obstruction. It gives no word-length-uniform positive floor and does not cover non-singleton chronology. |
| Singleton-tight minimum-face iteration | `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticSingletonTightMinimumFaceIteration.lean` | Exact owner-prefix iteration on a singleton-tight minimum face, convergence to a carrier washout point, identification of the owner cap with the punishment value and of debt with the punishment gap, stationary-solo consequences, and the resulting atomic-handoff-or-deletion alternative. |
| Sorin uniform-payoff segment | `UniformEquilibrium/Examples/Sorin/UniformPayoffSegment.lean` | A weighted Blackwell--Ferguson account strategy, exact finite-law Bellman and energy identities, almost-sure absorption, all-horizon behavioral deviation bounds, and the unconditional inclusion `(a, 2(1-a))` for every `1/2 <= a <= 2/3`. |
| Source-matched stopping-law reset cubes | `UniformEquilibrium/Diagnostics/Quitting/CounterexampleRegime/StoppingLaw/SourceMatchedResetCube.lean`, `UniformEquilibrium/Diagnostics/Quitting/CounterexampleRegime/StoppingLaw/SourceMatchedRadialResetCube.lean` | A flat charged circulation yields legal radial weights and one variable-scale reset cube whose normalized frozen active star tends coordinatewise to zero while its normalized diagonal charge tends to a positive limit. Integer chattering independently gives uniform `O(1/N)` frozen-prefix control. The exact carrier minimum controls every face from below. Exact nested bilinearity gives a uniform `O(lambda²)` fixed-pure-time affine remainder and `eventually_all_sourceMatchedRadialFacePayoff_affineRemainder_le` upgrades it to `o(lambda)` uniformly over faces and quit times. `exists_sourceMatchedRadial_commonPassport_or_edgeWitnessSwitch` therefore selects all approximate witnesses internally and retains only cap nonadditivity as an input; `sourceMatchedRadialFaceCapNonadditivity_le_or_hasNegativeSquare` localizes failure of that input to one literal negative cap square. `exists_sourceMatchedResetCubePureTimeWitnessSwitch_of_abs_debtCurvature` independently turns a budgeted debt square into an off-diagonal edge witness switch. These are static certificates and supply no chronological carrier path. |
| Paid radial cap-square dispatch | `UniformEquilibrium/Diagnostics/Quitting/CounterexampleRegime/StoppingLaw/SourceMatchedRadialPaidDispatch.lean` | An oriented pure-time witness switch retains its ordered source and receiving witnesses, exact first-disagreement live mass, and the division-free bound `gain <= 2 * M * liveMass`. A later receiving witness is a paid owner refusal; an earlier receiving witness with sufficiently small selection error yields a legal paid outsider endpoint deviation through the exact forced-owner atomic barrier. The localized radial theorem consumes a negative cap square above the fixed-witness quadratic budget, and the asymptotic theorem retains one fixed finite strategic label and its scale-normalized lower bound. This reroutes the cap-square branch to the existing paid atomic geometry; it neither eliminates that live leaf nor re-enters the resulting row into a reset cube or renewal chronology. |
| Active stopping-law transfer cycles | `UniformEquilibrium/Diagnostics/Quitting/CounterexampleRegime/StoppingLaw/OffDiagonal/ActiveTransferCycle.lean` | `entry_or_activeTransferCycle` proves that every stopping-law frontier has either a zero-debt support entry or a period-at-least-two cycle of positive tangent transfers among active debtors, independently of the total-slope sign. One uniform edge margin survives along the literal profile subsequence, and every cycle edge is simultaneously realized as a positive frozen debt edge of one legal common-source reset cube. Along the ordered cube path, each reached edge retains half the transfer or a crossed two-reset square has explicit positive absolute curvature. This binary rerouting does not consume positive total slope or turn profile-cube chronology into quitting-play chronology. |
| Positive-total-slope full-reset endpoint | `UniformEquilibrium/Diagnostics/Quitting/CounterexampleRegime/StoppingLaw/OffDiagonal/PositiveTotalSlopeEndpoint.lean`, `UniformEquilibrium/Diagnostics/Quitting/CounterexampleRegime/StoppingLaw/OffDiagonal/PositiveTotalSlopeAtomAccess.lean` | A supplied positive-total-slope mover has a literal source-relative full-reset debt excursion, a legal mover gain converging to its entire base debt, and a compact endpoint cluster whose mover debt is zero. `exists_offDiagonal_tangent_ge_average` selects an observer with tangent entry at least the average of total slope plus the entire mover debt over the other players. Its common pure-time response has vanishing endpoint debt, and its existing atom-interface charge is `7/16` of that entry. The same mover, observer, charge, and source rank are retained through arbitrarily long exact finite prefix stacks. The full endpoint is counterfactual, not a reached continuation; no anchored return, Bellman rebase, or contradiction follows. |
| Exact-diagonal stopping-law endpoints | `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticStoppingLawVanishingRegretTangentExtraction.lean`, `UniformEquilibrium/Diagnostics/Quitting/CounterexampleRegime/StoppingLaw/OffDiagonal/PotentialCoDecreaseEndpoint.lean`, `UniformEquilibrium/Diagnostics/Quitting/CounterexampleRegime/StoppingLaw/OffDiagonal/PotentialCoDecreaseCurvature.lean`, `UniformEquilibrium/Diagnostics/Quitting/CounterexampleRegime/StoppingLaw/OffDiagonal/PotentialCoDecreaseCurvatureDispatch.lean` | Vanishing-regret replacement selection upgrades every maintained frontier to exact tangent diagonal and zero limiting full-replacement mover debt. `exists_finiteSupportRankExit` re-extracts at same-minimum endpoints and proves finite termination in positive slope, support entry, charged circulation, or an off-minimum paid row. The data-bearing curvature adapter retains both approximate pure-time witnesses and dispatches every sufficiently late row to its legal owner/outsider temporal orientation under the terminal-gap error budget. It does not re-enter that local deviation into a reset family, exact return, or executable chronology. |
| Finite-quitting uniform-existence boundary | `UniformEquilibrium/Diagnostics/Quitting/UniformExistenceBoundary.lean` | `hasFiniteSupportRankExit_of_hasPositiveMinimumTerminalSemanticDebt` connects the compact positive-minimum obstruction to finite support-rank termination. `nonempty_vanishingDebtAtomAccess` proves that every extracted frontier already has a fixed vanishing-debt atom alternative, independently of its exit tag; `exists_vanishingDebtAtomAccess_of_supportEntry` retains the actual zero-debt support-entry recipient. The open interfaces ask precisely for chronological debt-shadowing certificates from those static atoms or for a positive exact admissible return from the paid row. The two conditional capstones consume those outputs through existing checked compilers; they do not prove either missing producer. |
| Equivariant security--welfare assembly | `UniformEquilibrium/Quitting/Classification/EquivariantSecurityWelfareAssembly.lean` | Phase-equivariant security at one representative transports to every player at every phase, pins each phase target below that player's punishment value, and combines with a positive weighted phase-welfare cap to produce a uniform-equilibrium payoff. A terminal row above the punishment-priced target total refutes the corresponding welfare cap. |
| Collision-anchored preemption geometry | `UniformEquilibrium/Diagnostics/Quitting/CounterexampleRegime/PreemptionGeometry.lean` | On at most four players, one collision owner roots one of six simple strict-preemption lassos and the collider occupies one of seventeen canonical positions. Every marked position is realizable with an explicit normalized gate matrix; every cycle vertex lies in the normal core. See [`PREEMPTION_GEOMETRY.md`](PREEMPTION_GEOMETRY.md). |
| Aligned collision and preemption | `UniformEquilibrium/Quitting/Boundary/Repair/AlignedPreemptionCollision.lean` | In the sequential two-solo screen, the follower's exact immediate-Quit gain is the owner's rate times the collision gain; the preemption inequality does not enter. Every repair mechanism fails under a terminal exploitability witness. When the collider's punishment value is at most its solo payoff, blocker balance is automatic, leaving owner endpoint failure or a profitable spectator join. The universal aligned two-cycle realization has a uniform-equilibrium payoff. |
| Coupled Bellman--collision reduction | `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticCoupledBellmanCollisionReduction.lean` | Persistent mass on one fixed pair, vanishing defects of both pair members, and return to the minimum-debt fiber force one fixed third player to have a uniformly positive legal reached-row gain along a strict subsequence. Without the return hypothesis, the exact alternative is nonvanishing shifted-tail excess or that third-player gain. |
| Terminal semantic joint-reset lift | `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticJointResetLift.lean` | A finite left-regular band of coupled reset modes, its exact `FinDist` semiconjugacy with semantic prefixing, and debt, payoff-spine, and cap-retention observables. The invariant reset hull need not have positive debt. |
| Quitting terminal exploitability localization | `UniformEquilibrium/Diagnostics/Quitting/CounterexampleRegime/BoundedSelfResetLocalization.lean` | For every starting-profile sequence in a terminal exploitability witness, a pure-time self-reset chain of length at most `card(I)+1` yields either an observer-absent forced-owner wall or an observer-containing reached-row gain. The certificate records a fixed terminal and explicit positive mass/gain floors. No converse is claimed from the branch data. |
| Positive-target reached rows | `UniformEquilibrium/Diagnostics/Quitting/CounterexampleRegime/StoppingLaw/ReachedRowDebtLocalization.lean` | Every positive observer-containing target yields a strict subsequence and an explicit uniform positive lower bound for one fixed non-observer's legal reached-row gain; nonconvergence is a projection. This does not provide source re-entry or an exact return. |
| Exact repair certificates | `UniformEquilibrium/Diagnostics/Quitting/ExactRepairCertificate.lean` | Proof-carrying cutoff-one, stationary, and cyclic certificate checkers. `UniformEquilibrium/Diagnostics/Quitting/CutoffOneMixedActual.lean` instantiates the cutoff-one checker for an exact rational table and names its zero payoff. |
| Solan--Vieille boundary table | `UniformEquilibrium/Quitting/Examples/SolanVieilleBoundaryEquilibrium.lean`, `UniformEquilibrium/Quitting/Examples/SolanVieilleBoundaryNonstationarity.lean` | An exact period-two equilibrium and its uniform payoff coexist with quantitative exclusion of all sufficiently accurate stationary or uniformly near-all-Continue terminal approximate equilibria. |

Import an internal file directly when its narrower interface is the point of
the proof. The umbrellas are navigation and project-integration boundaries,
not external compatibility promises or a ban on precise dependencies.

## Semantic waist and terminal bridge

`GameTheory/GameTheory/Stochastic/Uniform.lean` owns the canonical
`Stochastic.Game.IsUniformEquilibriumPayoff` and its deviation-cap constructor.
`UniformEquilibrium/ProofView/Concepts/Stochastic/Equilibrium/Uniform.lean`
owns the project proof view, and
`UniformEquilibrium/ProofView/Native/Equilibrium.lean` proves their exact
finite-horizon Nash and uniform-payoff equivalence for finite states and
actions. A candidate mechanism is complete only after it supplies the uniform
finite-horizon delivery and unilateral-deviation bounds encoded by that
semantic waist.

The native bridge also retains source data below payoff equivalence.
`IsRealizablePublicHistory` and
`isRealizablePublicHistory_publicHistoryOfTrace`
(`UniformEquilibrium/ProofView/Native/History.lean`) record that every
canonical public stage is source-coherent and belongs to the support of the
actual proof-view transition.  For bounded comparison,
`native_runBehavioral_eq_of_support_agreement` and
`exists_nativeMixed_publicHistoryLaw_eq_compiled`
(`UniformEquilibrium/ProofView/Native/Semantics.lean`) respectively require
profile agreement only on histories exposed by the run and realize the exact
compiled public-history law by a mixed contingent policy.  The mixed witness
depends on the profile and horizon; it is not one mixed profile valid at all
large horizons and therefore is not by itself a uniform-equilibrium compiler.

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
| Cumulative-budget marked paths | At every accuracy, compatible compact finite prefixes with a fixed activity cap and a cumulative total-absorption budget tending to infinity; alternatively one fixed singleton mark with divergent cumulative mass in the one-active stratum | One infinite support-rational path with nonsummable absorption and hence a uniform-equilibrium payoff | Does not produce the finite prefixes or prove that one singleton label survives across them. Pointwise positive marked mass is unnecessary, but cumulative divergence is essential. |
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
| Survival coboundaries | `MathUE/Probability/SurvivalCoboundary.lean` | Exact varying-hazard survival-weighted telescopes and finite-difference remainder identities. |
| Discounted backward recursion | `MathUE/Probability/DiscountedBackwardRecursion.lean` | Prefix-discrepancy Abel bounds, exact terminal shadow contraction, and summable block-tail accounting; it does not construct an infinite recursion. |
| Compact finite-prefix relations | `MathUE/Topology/CompactFinitePrefixRelation.lean` | Inverse-limit selection from compatible compact finite prefixes; used by circulation paths. |
| Budgeted compact-prefix relations | `MathUE/Topology/CompactBudgetedPrefixRelation.lean` | Inverse-limit selection while preserving every elapsed cumulative continuous-weight budget, plus the resulting nonsummability criterion. |
| Logarithmic block discretization | `UniformEquilibrium/Quitting/AbsorptionPath/LogarithmicBlockDiscretization.lean` | Exact unique-quitter, continuation-product, and quadratic collision estimates for logarithmic hazard blocks. The continuous derivative/Bellman adapter is not supplied. |
| Supremum witness switching | `MathUE/Optimization/SupremumTwoResetWitnessSwitch.lean` | `orientedSupremumWitnessSwitch_of_abs_mixedDifference` retains source and receiving approximate witnesses, receiving regret and gain, the reverse source-edge budget, and the oriented rectangle, without assuming attainment. `finiteCubeAffineRemainder_eq_squareCurvatureSum` identifies every fixed-witness affine remainder with the exact triangular square sum, and `finiteCubeCapNonadditivity_le_or_hasNegativeSquare` localizes excessive cap nonadditivity. `finiteCube_commonPassport_or_edgeWitnessSwitch` is the finite-scale priority split: either one selected face witness has a literal quantitative edge regret drop, or the full-face witness obeys an explicit all-face passport bound. |
| Pure-time witness-switch decoding | `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPositiveSlopeRectangle.lean`, `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticStoppingLawResetCubeOrientation.lean` | `exists_pureTimeWitnessSwitchCertificate_of_abs_debtCurvature` pays the prescribed-payoff, fixed-witness, and `3 * eta` budgets and returns both the signed cross-distribution rectangle atom and a separate profitable receiving-edge terminal-difference atom of charge `charge + eta`. `exists_resetCubePureTimeSquareEdgeWitnessSwitch_of_abs_debtCurvature` localizes its diagonal regret change to an actual off-diagonal reset edge with raw charge `(charge + eta) / 2`, while retaining the enclosing square, changed-coordinate identity, and endpoint containment. These are static terminal-law and cube certificates; they do not construct a common source, chronology, or renewal blocks. |
| Survival-weighted suffix regret | `UniformEquilibrium/Quitting/Paths/SurvivalWeightedSuffixRegret.lean` | `quittingRelativePureTimeTerminalValue_sub_prefixTransport` proves exact source-to-suffix transport for relative quit delays explicitly rebased to absolute dates, and `quittingPureTimeSuffixRegret_le` gives the resulting unconditional `sSup` regret bound without attainment or boundedness hypotheses. `quittingPureTimeFirstDisagreementValue_sub_eq_opponentSurvival_mul` exactly decodes the difference between quit-now and any later finite-or-`Never` pure-time plan at their first disagreement; `quittingPureTimeEarlierValue_sub_later_eq_opponentSurvival_mul` is its finite absolute-time specialization. No reset-cube chronology or renewal producer is supplied. |
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

- `UniformEquilibrium/ProofView/Concepts/Stochastic/Equilibrium/Uniform/AsymptoticPayoffEquivalence.lean` transfers an exact target across
  profile-uniform finite-average payoff gaps tending to zero.
- `UniformEquilibrium/ProofView/Concepts/Stochastic/Equilibrium/Uniform/ExpectedPotentialShaping.lean` applies that transfer to bounded
  expected-potential coboundaries with an `O(1/T)` endpoint telescope.
- `UniformEquilibrium/ProofView/Concepts/Stochastic/Equilibrium/Uniform/PayoffExistenceClosure.lean` proves target-free existence closure
  under uniform stage-payoff limits on a fixed finite skeleton.
- `UniformEquilibrium/ProofView/Concepts/Stochastic/Models/Quitting/UniformPayoffExistenceClosure.lean` specializes the closure theorem
  to uniformly convergent quitting reward tables.
- `UniformEquilibrium/ProofView/Concepts/Stochastic/Models/Quitting/RootPerturbation.lean` gives local one-coordinate payoff and regret
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

`QuittingFiniteDeadlineNashProfile.semanticDebt_le_escapeCharge` and
`TerminalSemanticGlobalDebtBarrierCertificate.Certificate.floor_le_sum_finiteDeadlineEscapeCharge`
(`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticFiniteDeadlineNashEscalation.lean`)
escalate a supplied behavioral realization of a finite-deadline stopping Nash
profile to the unrestricted terminal game.  The only residual charge is the
opponent survival probability to the deadline times the positive singleton
self-reward.  The module is a consumer: it does not construct the finite mixed
Nash equilibrium or its behavioral realization.

`TerminalSemanticGlobalDebtBarrierCertificate.Certificate.ofPotential` and
`TerminalSemanticGlobalDebtBarrierCertificate.Certificate.ofApproximatePotentialLimit`
(`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticGlobalDebtBarrierCertificate.lean`)
turn an exact separated Lyapunov potential, or a supplied pointwise limit of
vanishing-error potentials, into a global semantic-debt barrier.  The limit
consumer does not supply the compactness theorem needed to extract a common
limit from a family of finite certificates.

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
    theorem; and
11. the three branch propositions in
    `UniformEquilibrium/Quitting/Classification/ExistenceBranches.lean`
    are source vocabulary, not the source characterization.  Nothing states or
    proves the equivalence between existence of approximate equilibria and the
    disjunction of the branches, and the instant-punishment branch is written
    in a constant-row shape that is sufficient for, but not equivalent to, the
    source's.

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
