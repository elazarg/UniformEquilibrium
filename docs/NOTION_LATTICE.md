# The notion lattice

This is the maintained notion map. Its cluster IDs are local to this document.
Status markers distinguish theorems proved in Lean, definitional consequences,
conditional theorems, open implications, false implications, and pairs for
which no comparison is meaningful. The edge tables record relationships for
which the declared surface supplies a theorem, an explicit hypothesis gap, a
counterexample or mathematical reason, or an explanation of nonapplicability;
they are not a complete pairwise matrix.

**Scope, stated honestly.** This is a selected inventory of the notions
enumerated in §1 and exposed
through `UniformEquilibrium/README.md`,
`GameTheory/GameTheory/Concepts/Stochastic/Equilibrium/Uniform.lean`,
`GameTheory/GameTheory/Languages/MultiRound/StochasticGame.lean`, the
quitting-specific files, and the modules they import or are imported by. It does **not**
establish that this universe is exhaustive or certify the global consistency
of the repository's definitions. Auxiliary predicates are included only when
an edge below uses them. Section 5 records the explicit absence claims on which
the map relies; §1 is a floor, not a ceiling.

**Why a registry, not a matrix.** "Uniform" is a horizon quantifier, not a
payoff functional; `IsUniformEquilibriumPayoff` is already a payoff-level
predicate, so it cannot be a matrix column alongside functionals like
`finiteAveragePayoff`. `IsεAsymptoticNash` is parameterized by an *arbitrary*
payoff functional `u`, so no fixed matrix cell can hold it — each
instantiation of `u` is a different edge. §1 records nodes with five
independent fields (payoff functional, strategy class, quantifier order,
approximation regime, game scope); §2 records directed edges between nodes.
The small per-cluster tables in §2 are views generated from that edge list,
not the primary structure.

Every theorem claim below includes its Lean name and source location. A verdict
of **PROVED IN LEAN** applies only under the hypotheses stated in its row.

## 1. Registry of nodes

Columns: payoff functional the notion is stated against; strategy class
quantified over; quantifier order (per-horizon / uniform-in-horizon /
asymptotic / stationary-fixed-point); approximation regime (exact / ε /
vanishing-ε family); game scope (general finite `StochasticGame`, a
restricted class, or quitting-only).

### Cluster 0 — ground floor, one-shot kernel games

| ID | Lean name | File:line | Payoff functional | Strategy class | Quantifier order | Approximation | Game scope |
|---|---|---|---|---|---|---|---|
| K0 | `KernelGame.IsNash` | `GameTheory/GameTheory/Concepts/Equilibrium/SolutionConcepts.lean:68` | one-shot `eu` | pure/mixed strategy of a `KernelGame` | none (single shot) | exact | any `KernelGame` |
| K1 | `KernelGame.IsεNash` | `GameTheory/GameTheory/Concepts/Equilibrium/ApproximateNash.lean:43` | one-shot `eu` | as K0 | none | ε | any `KernelGame` |

`K0` and `K1` are registry labels, not declaration names.

Not stochastic-game notions themselves, but the base every stage-level and
horizon-level notion below reduces to (`isεHorizonNash_iff_horizonGame`,
`stageKernelGame`, `stageGame`).

### Cluster 1 — stagewise, Markov, and legal-play restrictions

| ID | Lean name | File:line | Payoff functional | Strategy class | Quantifier order | Approximation | Game scope |
|---|---|---|---|---|---|---|---|
| M1 | `StochasticGame.IsStagewiseNash` | `GameTheory/GameTheory/Languages/MultiRound/StochasticGame.lean:71` | raw `stagePayoff`, separately at every state | pure `MarkovProfile` (state → action, no randomization) | none — one-stage deviations, universally over states | exact | any `StochasticGame` |
| M2 | `StochasticGame.IsMixedStageNash` | `GameTheory/GameTheory/Concepts/Stochastic/Core/StageGame.lean:100` | `mixedStageEU`, separately at every state | mixed Markov (`State → ∀ i, PMF (Act i)`) | none — one-stage mixed deviations, universally over states | exact | any `StochasticGame` |
| M3 | `StochasticGame.IsεLegalMarkovNash` | `GameTheory/GameTheory/Concepts/Stochastic/Transform/ActionLegality/Normalization.lean:119` | raw `stagePayoff`, deviations restricted to `Legal` | pure `MarkovProfile`, legal actions only | none | ε | state-dependent legal action sets |
| M4 | `StochasticGame.IsεNormalizedMarkovNash` | `GameTheory/GameTheory/Concepts/Stochastic/Transform/ActionLegality/Normalization.lean:129` | `normStagePayoff` (illegal actions padded) | pure `MarkovProfile` | none | ε | as M3, padded presentation |
| L1 | `StochasticGame.IsεLegalHorizonNash` | `GameTheory/GameTheory/Concepts/Stochastic/Transform/ActionLegality/BehaviorTransfer.lean:298` | `finiteAveragePayoff` | legal `BehaviorProfile`, tested against legal deviations | one horizon | ε | state-dependent legal action sets |
| L2 | `StochasticGame.IsLegalUniformEquilibriumPayoff` | `GameTheory/GameTheory/Concepts/Stochastic/Transform/ActionLegality/BehaviorTransfer.lean:332` | `finiteAveragePayoff`, target `v` | accuracy-dependent legal `BehaviorProfile`, tested against legal deviations | uniform-in-horizon, ∀ε∃σ | vanishing-ε family | state-dependent legal action sets |

M1 is a stagewise pure Nash predicate, not a Markov-perfect equilibrium. At
each state it compares only
`G.stagePayoff s (fun i => σ i s) who` against one-stage deviations at one
state, exactly the field `stagePayoff` and nothing downstream of it; the
transition kernel and cross-state continuation effects are invisible to each
comparison, although the predicate requires the comparison at every state. The
declared surface has no continuation-aware, Markov-perfect equilibrium notion:
no
`IsMarkovPerfectNash`, no fixed-point-in-value-function predicate outside the
discounted Bellman machinery of Cluster 2, which is stated for a *fixed*
discount factor, and no `β → 1` or average-reward Markov-perfect predicate.

`M1` has **zero importers** anywhere in `GameTheory/` outside its own
declaration file (`rg -l IsStagewiseNash GameTheory/` returns only
`GameTheory/GameTheory/Languages/MultiRound/StochasticGame.lean`). It is not merely disconnected
from the uniform-equilibrium tower; nothing in the tree uses it at all.

### Cluster 2 — discounted

| ID | Lean name | File:line | Payoff functional | Strategy class | Quantifier order | Approximation | Game scope |
|---|---|---|---|---|---|---|---|
| D1 | `StochasticGame.IsDiscountedεNash` | `GameTheory/GameTheory/Concepts/Stochastic/Equilibrium/Discounted.lean:1057` | `discountedPayoff β` | full `BehaviorProfile` | fixed `β`, single-shot deviation test | ε | any `StochasticGame` |
| D2 | `StochasticGame.IsDiscountedStationaryBellmanEq` | `GameTheory/GameTheory/Concepts/Stochastic/Equilibrium/Discounted/Fink.lean:1007` | `discountedAuxEU β` (Bellman value `V`) | stationary mixed `StationaryMixedProfile` | fixed `β`, Bellman fixed point | exact | any `StochasticGame` (Fink 1964) |

### Cluster 3 — finite-horizon and uniform (behavior strategies)

| ID | Lean name | File:line | Payoff functional | Strategy class | Quantifier order | Approximation | Game scope |
|---|---|---|---|---|---|---|---|
| U1 | `StochasticGame.IsεHorizonNash` | `GameTheory/GameTheory/Concepts/Stochastic/Equilibrium/Uniform.lean:80` | `finiteAveragePayoff` at fixed `T` | full `BehaviorProfile` | per-horizon (one `T`) | ε | any `StochasticGame` |
| U2 | `StochasticGame.IsUniformεEquilibrium` | `GameTheory/GameTheory/Concepts/Stochastic/Equilibrium/Uniform.lean:88` | `finiteAveragePayoff` | full `BehaviorProfile` | uniform-in-horizon (`∃T₀∀T≥T₀`) | ε | any `StochasticGame` |
| U3 | `StochasticGame.IsUniformEquilibriumPayoff` | `GameTheory/GameTheory/Concepts/Stochastic/Equilibrium/Uniform.lean:97` | `finiteAveragePayoff`, target `v : Payoff ι` | full `BehaviorProfile`, may depend on ε | uniform-in-horizon, ∀ε∃σ | vanishing-ε family | any `StochasticGame` — **the central notion** (Solan–Vieille Def. 2.1 / Mertens–Neyman) |
| U4 | `StochasticGame.HasUniformDeviationCapConstructor` | `GameTheory/GameTheory/Concepts/Stochastic/Equilibrium/Uniform.lean:174` | `finiteAveragePayoff`, target `v` | full `BehaviorProfile` | as U3, split into on-path + deviation-cap clauses | vanishing-ε family | any `StochasticGame` |
| U5 | `StochasticGame.IsUniformScheduledMarkovEquilibriumPayoff` | `UniformEquilibrium/VanishingDiscount/Fink/MarkovEndpoint.lean:27` | `finiteAveragePayoff`, target `v` | **scheduled-Markov** (`ℕ → StationaryMixedProfile`) only | as U3 | vanishing-ε family | any `StochasticGame` |
| U6 | `StochasticGame.IsεAsymptoticNash` | `GameTheory/GameTheory/Concepts/Stochastic/Equilibrium/Asymptotic.lean:40` | **arbitrary** `u : BehaviorProfile → ι → ℝ` | full `BehaviorProfile` | asymptotic (whatever `u` encodes) | ε | any `StochasticGame`; a family of nodes, one per `u` |

U6 is not one node but a schema: every instantiation of `u` (limiting
functional) is a distinct payoff notion. Two instantiations matter below:
`u = quittingTerminalPayoff reward` (Cluster 7) and the liminf-average
functional, for which no Lean `Prop` is defined (Cluster 4).

### Cluster 4 — liminf/limsup-average (no Lean `Prop` exists for either)

**There is no Lean node here for either aggregation** — no
`IsLiminfAverageEquilibrium` and no `IsLimsupAverageEquilibrium` `Prop`
anywhere in the tree (`grep -rn "def.*LiminfAverage\|LiminfAverageEquilibrium\|
def.*LimsupAverage\|LimsupAverageEquilibrium" GameTheory/` returns no
matches). The infinite-play measure itself **is** built —
`StochasticGame.infinitePlayMeasure`
(`GameTheory/GameTheory/Concepts/Stochastic/Core/Probability/InfinitePlayMeasure.lean:159`), by the Ionescu-Tulcea
theorem from the game's transition kernel and a fixed behavior profile — and
`GameTheory/GameTheory/Concepts/Stochastic/Equilibrium/Asymptotic/LiminfAverageBridge.lean`
uses it directly, with no representation
hypothesis, via `StochasticGame.pathwiseAveragePayoff`
(`GameTheory/GameTheory/Concepts/Stochastic/Equilibrium/Asymptotic/LiminfAverageBridge.lean:414`) and
`StochasticGame.integral_pathwiseAveragePayoff`
(`GameTheory/GameTheory/Concepts/Stochastic/Equilibrium/Asymptotic/LiminfAverageBridge.lean:461`). The same module states four
bridge theorems for witnesses supplied by U3 to the literature's liminf- and
limsup-average games — one deviation-direction and one on-path-direction
theorem for each aggregation — every one unconditional in its pathwise
realization. Exactly
one of the two directions is unconditional in its *mathematics* for each
aggregation (Fatou for liminf-deviation and limsup-on-path; nothing for
liminf-on-path and limsup-deviation without an extra a.s.-convergence
hypothesis). Recorded as edges in §2.4, not as nodes.

### Cluster 5 — monitored / realized-action repeated games

The base type is `KernelGame`/`PublicMonitoring`, not `StochasticGame`. PM1,
PM2, and P2 connect to Cluster 3 through the one-state adapter
`realizedActionStochasticGame`; R1–R3 use a distinct unmonitored strategy type.

| ID | Lean name | File:line | Payoff functional | Strategy class | Quantifier order | Approximation | Game scope |
|---|---|---|---|---|---|---|---|
| R1 | `KernelGame.IsεFiniteRepeatedNash` | `GameTheory/GameTheory/Concepts/Repeated/Uniform.lean:47` | `finiteAveragePayoff` (repeated) | `RepeatedProfile` | per-horizon | ε | any `KernelGame` |
| R2 | `KernelGame.IsUniformεEquilibrium` | `GameTheory/GameTheory/Concepts/Repeated/Uniform.lean:55` | as R1 | `RepeatedProfile` | uniform-in-horizon | ε | any `KernelGame` |
| R3 | `KernelGame.IsUniformEquilibrium` | `GameTheory/GameTheory/Concepts/Repeated/Uniform.lean:61` | as R1, plus `HasLongRunAveragePayoff` | `RepeatedProfile`, one fixed profile | fixed profile, ∀ε | exact convergence + ε-family | any `KernelGame` |
| PM1 | `PublicMonitoring.IsεFiniteRepeatedNash` | `GameTheory/GameTheory/Concepts/Repeated/Monitoring.lean:622` | monitored `finiteAveragePayoff` | `MonitoredProfile` | per-horizon | ε | monitored `KernelGame` |
| PM2 | `PublicMonitoring.IsUniformεEquilibrium` | `GameTheory/GameTheory/Concepts/Repeated/Monitoring.lean:630` | as PM1 | `MonitoredProfile` | uniform-in-horizon | ε | monitored `KernelGame` |
| P1 | `PublicMonitoring.IsUniformEquilibrium` | `GameTheory/GameTheory/Concepts/Repeated/Monitoring.lean:636` | monitored `finiteAveragePayoff` | `MonitoredProfile`, one fixed profile | as R3 | as R3 | monitored `KernelGame` |
| P2 | `PublicMonitoring.IsUniformEquilibriumPayoff` | `GameTheory/GameTheory/Concepts/Stochastic/Transform/Repeated/RealizedActionRepeatedAdapter.lean:86` | monitored `finiteAveragePayoff`, target `v` | `MonitoredProfile`, may depend on ε | as U3 | vanishing-ε family | monitored `KernelGame` |

### Cluster 6 — zero-sum discounted / Mertens–Neyman

| ID | Lean name | File:line | Payoff functional | Strategy class | Quantifier order | Approximation | Game scope |
|---|---|---|---|---|---|---|---|
| Z1 | `StochasticGame.IsZeroSum` | `GameTheory/GameTheory/Concepts/Stochastic/ZeroSum/Basic.lean:329` | game-class predicate, not an equilibrium notion | — | — | — | two-player, `Payoff (Fin 2)` |
| Z2 | `discountedShapleyValue` / `shapleyBehaviorProfile` + `shapleyBehaviorProfile_isDiscountedNash` | `GameTheory/GameTheory/Concepts/Stochastic/ZeroSum/Basic.lean:158`, `GameTheory/GameTheory/Concepts/Stochastic/ZeroSum/Basic.lean:256`, `GameTheory/GameTheory/Concepts/Stochastic/ZeroSum/Basic.lean:607` | `discountedPayoff β` | stationary play of the Shapley optimal pair | fixed `β : ℝ≥0`, `β < 1` | exact (ε=0) | zero-sum two-player |
| Z3 | `StochasticGame.IsRowTrackingCertificate` / `SecuresCol` | `UniformEquilibrium/SpecialCases/ZeroSum/MertensNeyman/Criterion.lean:909`, `UniformEquilibrium/SpecialCases/ZeroSum/MertensNeyman/Criterion.lean:1601` | finite-horizon securing guarantee | history-adaptive strategy | uniform-in-horizon | ε | zero-sum two-player |

### Cluster 7 — quitting-specific

Quitting games are ordinary `StochasticGame`s with `Act = Bool`
(quit/continue) and a specific `stagePayoff`/`transition` built by
`quittingGame`. The M/L/D/U notions above apply to them unchanged, while the Z
notions additionally require their two-player and zero-sum hypotheses. Cluster
5 instead uses `KernelGame` or `PublicMonitoring` and reaches stochastic games
only through the adapter edges below. The
notions below exist **only** for quitting games — no general-game analogue
is defined anywhere in the tree.

| ID | Lean name | File:line | Payoff functional | Strategy class | Quantifier order | Approximation | Game scope |
|---|---|---|---|---|---|---|---|
| Q1 | `IsεQuittingRootNash` | `UniformEquilibrium/Quitting/Root/FirstBranch.lean:209` | `quittingRootExpectedPayoff` (root mixture + free continuation vector) | one-shot `ι → PMF Bool` at the root | none | ε | quitting only |
| Q2 | `IsεQuittingRootEndpointNash` | `UniformEquilibrium/Quitting/Root/SuccessorCertificate.lean:113` | as Q1, tested at the two pure endpoints | as Q1 | none | ε | quitting only |
| Q3 | `HasUniformDeviationUpperApproximation` | `UniformEquilibrium/Quitting/Terminal/ToUniformDeviationApproximation.lean:42` | any limiting functional `u` vs. `finiteAveragePayoff` | full `BehaviorProfile` | uniform-in-horizon, one-sided | ε | stated generally; used only for quitting |
| Q4 | `quittingTerminalPayoff` | `GameTheory/GameTheory/Concepts/Stochastic/Models/Quitting/Asymptotic.lean:201` | expected absorption-weighted terminal reward | full `BehaviorProfile` | — (a payoff functional, not an equilibrium notion) | exact | quitting only |
| Q5 | `IsQuittingZeroSolo` | `UniformEquilibrium/Quitting/Punishment/ZeroSoloDisjunct.lean:54` | reward-table admissibility class, not an equilibrium notion | — | — | — | quitting only |
| Q6 | `HasAdmissibleAbsorbingQuittingCycle` | `UniformEquilibrium/Quitting/Punishment/ZeroSoloDisjunct.lean:153` | as Q5 | — | — | — | quitting only |

`IsUniformEquilibriumPayoff` (U3) itself applies verbatim to quitting games
(instantiated at `quittingGame reward`); it is not a separate node, but every
edge into U3 in §2.6 is stated for `G = quittingGame reward`.

## 2. Directed edges

Each edge is `source → target : VERDICT`, evidence, and the hypothesis
gap if the edge is conditional. Only selected edges between comparable nodes (same or
transportable payoff functional, compatible strategy classes) are listed;
pairs with no shared payoff functional and no known transport (e.g. Q1 vs.
D1) are omitted rather than padded with N/A, per the registry-not-matrix
design — the two clusters share nothing to compare.

### 2.1 Ground floor, stagewise, and legal-play edges (Clusters 0–1)

| Edge | Verdict | Evidence |
|---|---|---|
| M1 → (K0 of `stageKernelGame s`) | **PROVED IN LEAN** | `isStagewiseNash_iff_all_stage_nash` (`GameTheory/GameTheory/Languages/MultiRound/StochasticGame.lean:84`) — full iff, per state. |
| M2 at the Dirac lift of a pure profile → M1 | **MATHEMATICALLY IMMEDIATE; NOT PACKAGED IN LEAN** | This is a meaningful specialization: pure deviations are included among M2's mixed deviations, and `pmfPi` of a Dirac family is Dirac. No named theorem connects the two predicates. |
| M1 → M2 at the Dirac lift | **MATHEMATICALLY IMMEDIATE; NOT PACKAGED IN LEAN** | Pure one-stage Nash extends to mixed deviations by linearity of expectation. No named theorem packages this Dirac bridge. |
| A fixed M1 profile, or its Dirac M2 lift, → U1/U2 under general controlled transitions | **FALSE BY FINITE EXAMPLE; NOT FORMALIZED HERE** | In a one-player two-state game, let the prescribed action at the first state pay `1` and remain there, while an action paying `0` moves to an absorbing state paying `2`. The prescribed action is stagewise Nash at both states, but switching once gains over every horizon `T > 2`; thus its Markov behavior lift is neither exact U1 at those horizons nor U2 at small error. |
| Existence of M1/M2 → existence of a U3 target for a general game | **OPEN** | No theorem derives a uniform-equilibrium payoff from stagewise Nash data. For finite nonempty action sets, M2 always exists (`exists_isMixedStageNash`, `GameTheory/GameTheory/Concepts/Stochastic/Core/StageGame.lean:108`), so an unrestricted M2-existence bridge would settle the general existence proposition rather than follow from a fixed-profile argument. |
| M2 → U1, **restricted to action-independent transitions** | **PROVED IN LEAN (restricted)** | `isεHorizonNash_markovBehaviorProfile` (`GameTheory/GameTheory/Concepts/Stochastic/Classes/TransitionIndependent.lean:149`), for every horizon and `ε ≥ 0`. It assumes finite players, states, and action sets, together with `hκ : ∀ s a, G.transition s a = κ s` and the supplied mixed stage-Nash profile. |
| Action-independent game → existence of a U3 target | **PROVED IN LEAN (restricted)** | `exists_uniformEquilibriumPayoff_of_isActionIndependent` (`GameTheory/GameTheory/Concepts/Stochastic/Classes/TransitionIndependent.lean:227`). It assumes finite players, states, and nonempty finite action sets, plus `G.IsActionIndependent`; it constructs its own mixed stage-Nash profile. |
| Action-independent game → one profile satisfying U2 for every `ε > 0` | **PROVED IN LEAN (stronger equilibrium-profile statement)** | `exists_forall_isUniformεEquilibrium_of_isActionIndependent` (`GameTheory/GameTheory/Concepts/Stochastic/Classes/TransitionIndependent.lean:207`) assumes finite players, states, and nonempty finite action sets and constructs a single Markov profile that works at every positive accuracy. |
| M4 → M3 | **PROVED IN LEAN** | `isεLegalMarkovNash_of_normalized` (`GameTheory/GameTheory/Concepts/Stochastic/Transform/ActionLegality/Normalization.lean:142`) — for a supplied legality predicate with a legal action at every player-state pair, a legal normalized-Nash Markov profile is Nash for the legality-constrained game. |
| M3 → M4 | **PROVED IN LEAN** | `isεNormalizedMarkovNash_of_legal` (`GameTheory/GameTheory/Concepts/Stochastic/Transform/ActionLegality/MarkovConverse.lean:110`) assumes a supplied legality predicate with a legal action at every player-state pair and a legal M3 profile. |
| L1 on `normalizedGame` ↔ L1 on the original game | **PROVED IN LEAN** | `isεLegalHorizonNash_normalizedGame_iff` (`GameTheory/GameTheory/Concepts/Stochastic/Transform/ActionLegality/BehaviorTransfer.lean:310`), for a supplied legality predicate with a legal action at every player-state pair. Both prescribed play and deviations are restricted to legal strategies. |
| L2 on `normalizedGame` ↔ L2 on the original game | **PROVED IN LEAN** | `isLegalUniformEquilibriumPayoff_normalizedGame_iff` (`GameTheory/GameTheory/Concepts/Stochastic/Transform/ActionLegality/BehaviorTransfer.lean:343`), under the same legality data and restricted strategy class. |
| Unrestricted U1 on `normalizedGame` + legality of the prescribed profile → L1 on the original game | **PROVED IN LEAN** | `isεLegalHorizonNash_of_isεHorizonNash_normalizedGame` (`GameTheory/GameTheory/Concepts/Stochastic/Transform/ActionLegality/Disintegration.lean:678`). The converse unrestricted behavior-level transfer is not asserted. |
| A fixed M3/M4 profile → unrestricted U1/U2 under general controlled transitions | **FALSE BY THE SAME FINITE EXAMPLE; NOT FORMALIZED HERE** | Take every action to be legal in the two-state example above. Then M3 and M4 reduce to the same exact stagewise condition, while the profitable state-changing deviation still refutes U1 at long horizons and U2 at small error. |
| Existence of M3/M4 → existence of an unrestricted U3 target | **OPEN** | The Markov-level normalization results concern single-stage deviations and do not supply an unrestricted uniform-payoff bridge. The all-actions-legal specialization reduces this existence question to the stagewise boundary above. |

### 2.2 Discounted ↔ Uniform (Clusters 2–3)

| Edge | Verdict | Evidence |
|---|---|---|
| D2 → D1 (a Bellman equilibrium's stationary play is an exact discounted Nash) | **PROVED IN LEAN** | `IsDiscountedStationaryBellmanEq.isDiscountedεNash` (`GameTheory/GameTheory/Concepts/Stochastic/Equilibrium/Discounted/Fink.lean:1301`), with `ε = 0` and no zero-sum assumption. It assumes finite players, states, and action sets; `0 ≤ β < 1`; and a uniform stage-payoff bound `|stagePayoff s a who| ≤ U`. The deviation proof uses `discountedPayoff_le_of_bellman_ge` (`GameTheory/GameTheory/Concepts/Stochastic/Equilibrium/Discounted.lean:381`). |
| Z2 (D1 specialized to zero-sum + Shapley profile) | **PROVED IN LEAN** | `shapleyBehaviorProfile_isDiscountedNash` (`GameTheory/GameTheory/Concepts/Stochastic/ZeroSum/Basic.lean:607`), exact (`ε = 0`), for finite states and nonempty finite action sets with `β : ℝ≥0` and `β < 1`. |
| D2-family (certificates arbitrarily close to one target, uniformly over states and players) → U3 | **PROVED IN LEAN, conditional on `hcert`** | `isUniformEquilibriumPayoff_of_fink_certificates` (`GameTheory/GameTheory/Concepts/Stochastic/Equilibrium/Discounted/Fink.lean:1387`). For every `η > 0`, `hcert` supplies `0 ≤ β < 1`, a stationary profile, Bellman value `V`, a bound `C ≥ 0`, a D2 certificate, `|V| ≤ C`, and `|V s who - v who| ≤ η` for every state and player. |
| D1 (single fixed β) → U3 | **OPEN** | `isUniformEquilibriumPayoff_of_fink_certificates` isolates the missing all-accuracy, state-uniform target stabilization. `UniformEquilibrium/VanishingDiscount/Fink/TangentCounterexample.lean`, `UniformEquilibrium/VanishingDiscount/Fink/SelectionCounterexample.lean`, and `UniformEquilibrium/VanishingDiscount/Fink/DiscountBiasNoGo.lean` obstruct specific selection mechanisms, not D1 → U3 itself. |
| Z3-pair (`IsRowTrackingCertificate` + `SecuresCol`) → U3, zero-sum | **PROVED IN LEAN, conditional on both certificates** | `uniformValue_of_rowColumnTrackingCertificates` (`UniformEquilibrium/SpecialCases/ZeroSum/MertensNeyman/Criterion.lean:1619`) assumes a two-player zero-sum game with finite state and action sets and yields target `(w, -w)`. The conditional constructors are `trackingCertificate_of_discountBiasControl` (`UniformEquilibrium/SpecialCases/ZeroSum/MertensNeyman/Criterion.lean:926`) and `trackingCertificate_of_runningDeficit` (`UniformEquilibrium/SpecialCases/ZeroSum/MertensNeyman/Criterion.lean:1557`); neither supplies both certificates for every zero-sum game. |
| Forced linear running-deficit realization in the Big Match → eventual payoff lower bound `1/4` against all-Right | **FALSE** | `not_eventually_one_quarter_le_payoff_rightContinueDeficitProfile` (`UniformEquilibrium/Examples/BigMatch/DeficitIndexNoGo.lean:246`). This refutes that explicit realization, not Z3 → U3 or every possible running-deficit constructor. |

In `isUniformEquilibriumPayoff_of_fink_certificates`, the `0 ≤ C` conjunct is
redundant: the proof binds it as `hC` at
`GameTheory/GameTheory/Concepts/Stochastic/Equilibrium/Discounted/Fink.lean:1401`
but does not use it. Dropping that conjunct gives an immediate strengthening
of the theorem's signature; the remaining absolute-value bound on `V` is used.

### 2.3 Within Cluster 3 (the uniform ladder)

| Edge | Verdict | Evidence |
|---|---|---|
| U3 ↔ U4 | **PROVED IN LEAN** | `hasUniformDeviationCapConstructor_iff` (`GameTheory/GameTheory/Concepts/Stochastic/Equilibrium/Uniform.lean:186`), full iff in both directions for finite players. |
| U2 unfolds to `∀T≥T₀, U1` | **DEFINITIONAL** | U2 is the quantifier wrapper around U1 (`GameTheory/GameTheory/Concepts/Stochastic/Equilibrium/Uniform.lean:88`). |
| U3 ⇒ `∀ε>0 ∃σ, U2` | **PROVED IN LEAN** | `IsUniformEquilibriumPayoff.exists_isUniformεEquilibrium` (`UniformEquilibrium/Conjecture/UniformExistenceConjecture.lean:97`) is stated for finite players with decidable equality; its only proposition hypotheses are `hv : G.IsUniformEquilibriumPayoff s₀ v` and `0 < ε`. It drops the payoff-proximity clause from the selected U3 witness. |
| For some `ε > 0`, no U2 witness exists → no U3 target exists | **PROVED IN LEAN** | `not_exists_uniformEquilibriumPayoff_of_no_uniformεEquilibrium` (`UniformEquilibrium/Conjecture/UniformExistenceConjecture.lean:109`) is the target-free contrapositive of the preceding projection. It needs no limiting payoff functional or convergence hypothesis. |
| U2 → U6 for a supplied pointwise limit `u`, with the same profile and error | **PROVED IN LEAN, conditional on `hlim`** | `isεAsymptoticNash_of_isUniformεEquilibrium` (`GameTheory/GameTheory/Concepts/Stochastic/Equilibrium/Asymptotic.lean:52`) requires no positivity hypothesis on `ε`; it assumes `hlim : ∀ τ who, Tendsto (finiteAveragePayoff · τ who) atTop (𝓝 (u τ who))`. |
| U3 → U6 for a supplied pointwise limit `u`, at every `ε > 0` | **PROVED IN LEAN, conditional on `hlim`** | `exists_isεAsymptoticNash_of_isUniformEquilibriumPayoff` (`GameTheory/GameTheory/Concepts/Stochastic/Equilibrium/Asymptotic.lean:71`) is the positive-accuracy U3→U2 projection followed by the preceding primitive bridge. |
| For some `ε > 0`, no U6 witness for `u`; and `hlim` holds → no U3 target exists | **PROVED IN LEAN, conditional on `hlim`** | `not_exists_uniformEquilibriumPayoff_of_no_asymptoticNash` (`GameTheory/GameTheory/Concepts/Stochastic/Equilibrium/Asymptotic.lean:87`) assumes `0 < ε`, nonexistence of an `IsεAsymptoticNash u ε` profile, and the same profilewise pointwise convergence `hlim`. |
| U3 → U5 (scheduled-Markov witness exists) | **FALSE** | For the Big Match, `isUniformEquilibriumPayoff_fairPayoff_via_publicPhase` (`UniformEquilibrium/Examples/BigMatch/PublicPhase.lean:420`) proves U3 at `fairPayoff` (`UniformEquilibrium/Examples/BigMatch/PublicPhase.lean:157`), definitionally `(1/2, -1/2)`, from `.live`; `not_isUniformScheduledMarkovEquilibriumPayoff_half` (`UniformEquilibrium/Examples/BigMatch/NoMarkov.lean:58`) refutes U5 at that state and target. |
| U5 → U3 | **PROVED IN LEAN** | `IsUniformScheduledMarkovEquilibriumPayoff.isUniformEquilibriumPayoff` (`UniformEquilibrium/VanishingDiscount/Fink/MarkovEndpoint.lean:39`) — forgetting the scheduled-Markov form of the witness. |
| U1 ↔ K1 of `horizonGame` | **PROVED IN LEAN** | `isεHorizonNash_iff_horizonGame` (`GameTheory/GameTheory/Concepts/Stochastic/Equilibrium/Uniform.lean:125`) — full iff for finite players. |

The primitive U2→U6 proof uses `hlim` only at the prescribed profile and at
each unilateral update, in the deviating player's coordinate. A proof-local
bridge with exactly those convergence assumptions would be strictly stronger;
the global pointwise hypothesis remains appropriate for the public theorem
asserting that `u` is a payoff functional induced on every profile.

### 2.4 Liminf/limsup-average (Cluster 4) — mirrored, not doubled

`GameTheory/GameTheory/Concepts/Stochastic/Equilibrium/Asymptotic/LiminfAverageBridge.lean`
separates the two aggregations explicitly; they must not be merged. The
infinite-play measure is proved in Lean (`infinitePlayMeasure`,
`GameTheory/GameTheory/Concepts/Stochastic/Core/Probability/InfinitePlayMeasure.lean:159`),
so every edge below is
unconditional in its pathwise *realization* — no
representation hypothesis remains anywhere in this cluster. What remains
conditional is a genuine mathematical fact about a.s. convergence, and it is
conditional for exactly one direction of each aggregation, mirrored: liminf's
deviation direction is free and its on-path direction costs `hconv`; limsup's
on-path direction is free and its *deviation* direction costs `hconv`. This
is the exact opposite pairing, not two free directions for either notion.

| Edge | Verdict | Evidence |
|---|---|---|
| One U3 witness `σ, T₀, hσ` at error `ε`, one deviation, and a nonnegative uniform stage-payoff bound → liminf-average cap `v who + 2ε` | **PROVED IN LEAN; no `hconv`** | `deviation_liminf_le_of_isUniformEquilibriumPayoff` (`GameTheory/GameTheory/Concepts/Stochastic/Equilibrium/Asymptotic/LiminfAverageBridge.lean:480`), using real Fatou `integral_liminf_le_of_bounded_of_eventually_le` (`GameTheory/GameTheory/Concepts/Stochastic/Equilibrium/Asymptotic/LiminfAverageBridge.lean:208`). `infinitePlayMeasure` supplies pathwise realization; the theorem still requires the displayed U3 witness and payoff bound. |
| Eventual lower bounds on expectations alone → the same lower bound on `E[liminf A_T]` | **FALSE FOR GENERAL BOUNDED PROCESSES; NOT A GAME COUNTEREXAMPLE** | The module docstring at `GameTheory/GameTheory/Concepts/Stochastic/Equilibrium/Asymptotic/LiminfAverageBridge.lean:70` gives the moving-bump/typewriter-sequence reason. It shows that pinned expectations alone are insufficient; it does not formalize a stochastic-game counterexample to a U3 implication. |
| One U3 witness, a nonnegative uniform stage-payoff bound, and a.s. convergence of `σ`'s pathwise averages → `v who - ε ≤ E[liminf A_T]` | **PROVED IN LEAN, conditional on `hconv`** | `onPath_le_liminf_integral_of_isUniformEquilibriumPayoff` (`GameTheory/GameTheory/Concepts/Stochastic/Equilibrium/Asymptotic/LiminfAverageBridge.lean:512`), via `le_integral_liminf_of_bounded_of_tendsto_ae_of_eventually_le` (`GameTheory/GameTheory/Concepts/Stochastic/Equilibrium/Asymptotic/LiminfAverageBridge.lean:347`). |
| One U3 witness and a nonnegative uniform stage-payoff bound → `v who - ε ≤ E[limsup A_T]` | **PROVED IN LEAN; no `hconv`** | `onPath_le_limsup_integral_of_isUniformEquilibriumPayoff` (`GameTheory/GameTheory/Concepts/Stochastic/Equilibrium/Asymptotic/LiminfAverageBridge.lean:543`), via reverse Fatou `le_integral_limsup_of_bounded_of_eventually_le` (`GameTheory/GameTheory/Concepts/Stochastic/Equilibrium/Asymptotic/LiminfAverageBridge.lean:315`) and `liminf_neg_eq_neg_limsup` (`GameTheory/GameTheory/Concepts/Stochastic/Equilibrium/Asymptotic/LiminfAverageBridge.lean:193`). |
| Eventual upper bounds on expectations alone → the same upper bound on `E[limsup A_T]` | **FALSE FOR GENERAL BOUNDED PROCESSES; NOT A GAME COUNTEREXAMPLE** | The sign-dual moving-bump example in the module docstring at `GameTheory/GameTheory/Concepts/Stochastic/Equilibrium/Asymptotic/LiminfAverageBridge.lean:100` has constant expectations `1/2` and pathwise limsup `1`. It refutes the process-level inference, not a stochastic-game U3 implication. |
| One U3 witness, a nonnegative uniform stage-payoff bound, and a.s. convergence of the deviation profile's pathwise averages → limsup cap `v who + 2ε` | **PROVED IN LEAN, conditional on `hconv`** | `deviation_limsup_le_of_isUniformEquilibriumPayoff` (`GameTheory/GameTheory/Concepts/Stochastic/Equilibrium/Asymptotic/LiminfAverageBridge.lean:575`), via `integral_limsup_le_of_bounded_of_tendsto_ae_of_eventually_le` (`GameTheory/GameTheory/Concepts/Stochastic/Equilibrium/Asymptotic/LiminfAverageBridge.lean:379`). |

**No theorem in the declared surface discharges `hconv` for either
aggregation.** It is an additional mathematical property of the specific process
(`pathwiseAveragePayoff`), not missing infrastructure: `IsUniformEquilibriumPayoff`
pins expectations and nothing more, and pinned expectations do not force a.s.
convergence (the moving-bump family above, and its dual, are the reason).

### 2.5 Repeated/monitored (Cluster 5) ↔ Uniform (Cluster 3)

| Edge | Verdict | Evidence |
|---|---|---|
| PM1 ↔ U1, via `realizedActionStochasticGame` and realized-action monitoring | **PROVED IN LEAN** | `isεFiniteRepeatedNash_iff_isεHorizonNash` (`GameTheory/GameTheory/Concepts/Stochastic/Transform/Repeated/RealizedActionRepeatedAdapter.lean:467`) is for a `realizedActionMonitoring.MonitoredProfile`, not an R1 `RepeatedProfile`. It assumes finite players, decidable player equality, finite outcomes, and finite strategy sets. |
| PM2 ↔ U2, via the same adapter | **PROVED IN LEAN** | `isUniformεEquilibrium_iff` (`GameTheory/GameTheory/Concepts/Stochastic/Transform/Repeated/RealizedActionRepeatedAdapter.lean:493`) has the same monitored-profile and finiteness hypotheses. |
| P2 ↔ U3, via the same adapter | **PROVED IN LEAN** | `isUniformEquilibriumPayoff_iff` (`GameTheory/GameTheory/Concepts/Stochastic/Transform/Repeated/RealizedActionRepeatedAdapter.lean:539`) assumes finite players, decidable player equality, finite outcomes, and finite strategy sets. |
| R1/R2 ↔ U1/U2 via this adapter | **N/A** | R1/R2 use unmonitored `RepeatedProfile`s. The cited realized-action adapter transports the distinct monitored predicates PM1/PM2; it does not state a theorem about R1/R2. |
| R3 → payoff-level notion, plain `KernelGame` (no monitoring) | **N/A** | No `KernelGame.IsUniformEquilibriumPayoff` is defined — only the monitored generalization P2 exists (in namespace `KernelGame.PublicMonitoring`). There is nothing to compare R3 against at the unmonitored level. |
| A fixed monitored uniform equilibrium plus its specified long-run target → P2 at that target | **PROVED IN LEAN** | `IsUniformEquilibrium.isUniformEquilibriumPayoff_of_hasLongRunAveragePayoff` (`GameTheory/GameTheory/Concepts/Stochastic/Transform/Repeated/RealizedActionRepeatedAdapter.lean:93`) assumes finite players and decidable player equality. |
| P1 → ∃target, P2 | **PROVED IN LEAN** | `IsUniformEquilibrium.exists_isUniformEquilibriumPayoff` (`GameTheory/GameTheory/Concepts/Stochastic/Transform/Repeated/RealizedActionRepeatedAdapter.lean:124`) assumes finite players and decidable player equality; P1 itself supplies the long-run target. |
| P2 → P1 | **OPEN** | The docstring at `GameTheory/GameTheory/Concepts/Stochastic/Transform/Repeated/RealizedActionRepeatedAdapter.lean:84` states that the converse would require a coherent selection/compactness theorem and is not asserted. |

### 2.6 Quitting-specific (Cluster 7) ↔ general (Clusters 3, 0)

| Edge | Verdict | Evidence |
|---|---|---|
| Q1 ↔ Q2 | **PROVED IN LEAN** | `isεQuittingRootEndpointNash_iff_isεQuittingRootNash` (`UniformEquilibrium/Quitting/Root/SuccessorCertificate.lean:124`), full iff for finite players. |
| Terminal payoff of one arbitrary behavioral deviation = terminal value of its induced root-sequence hazard | **PROVED IN LEAN; PAYOFF IDENTITY, NOT A NASH COMPILER** | `quittingTerminalPayoff_update_eq_rootSequenceHazardTerminalValue` (`UniformEquilibrium/Quitting/Cycles/BehaviorPureTimeExtremality.lean:222`). It does not mention Q1/Q2 or conclude terminal Nash. |
| `∀ε>0, ∃σ, U6` instantiated at `u = quittingTerminalPayoff` ↔ `∃v, U3` for `quittingGame reward` | **PROVED IN LEAN** | `quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors` (`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean:163`) is a full iff. Unlike the directional, partly conditional liminf/limsup bridges in §2.4, this terminal bridge needs no extra pathwise-convergence hypothesis: `quittingTerminalPayoff` is a finite absorption-weighted sum, and `tendsto_finiteAveragePayoff_quittingGame` (`GameTheory/GameTheory/Concepts/Stochastic/Models/Quitting/Asymptotic.lean:221`) proves its Cesàro-limit identity. |
| Q3 + terminal U6 at error `ε` + prescribed-play convergence → U2 at every `ε' > ε` | **PROVED IN LEAN** | `isUniformεEquilibrium_of_isεAsymptoticNash_of_upperApproximation` (`UniformEquilibrium/Quitting/Terminal/ToUniformDeviationApproximation.lean:57`). For quitting games, `quittingGame_isUniformεEquilibrium_of_terminalNash_finite` (`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformization.lean:187`) supplies Q3 and convergence from finite-game data. Neither theorem uses Q1/Q2. |
| Q5 ∨ Q6 (zero-solo or admissible-cycle) → ∃v, U3 for that reward table | **PROVED IN LEAN (conditional on the disjunction, per table)** | `exists_uniformEquilibriumPayoff_of_zeroSolo_or_admissibleCycle` (`UniformEquilibrium/Quitting/Punishment/ZeroSoloDisjunct.lean:171`). |
| "every reward table satisfies Q5 ∨ Q6" (the disjunction is exhaustive) | **FALSE** | `not_forall_isQuittingZeroSolo_or_hasAdmissibleAbsorbingQuittingCycle` (`UniformEquilibrium/Quitting/Boundary/Repair/DisjunctionCounterexample.lean:674`) proves the disjunction is not exhaustive, so the conditional theorem above does not yield unconditional existence for quitting games. |
| M1 (stagewise pure Nash) instantiated at `quittingGame reward` → any of Q1–Q4, U3-for-quitting | **N/A** | M1 has no `quittingGame` instantiation in the declared surface, and no theorem connects it to the general or quitting-specific boundary notions. |
| `quittingUniformEquilibriumPayoffConjecture` (the open conjecture, quitting case) | **OPEN PROPOSITION** | `quittingUniformEquilibriumPayoffConjecture` (`UniformEquilibrium/Quitting/Conjecture/Basic.lean:153`) is a proposition definition, not a theorem. It is not a relation between two notions, but it is the existence statement toward which the quitting edges above point. |

## 3. General/quitting boundary, stated explicitly

Notions that exist **only** for quitting games, with no general-game
counterpart anywhere in the tree: Q1 (`IsεQuittingRootNash`), Q2
(`IsεQuittingRootEndpointNash`), Q4 (`quittingTerminalPayoff`), Q5
(`IsQuittingZeroSolo`), Q6 (`HasAdmissibleAbsorbingQuittingCycle`), and the
quitting-specific combinatorial machinery feeding Q5/Q6. Q3
(`HasUniformDeviationUpperApproximation`) is stated at general-game
generality (any `u`, any `StochasticGame`) but is used nowhere outside the
quitting bridge chain — a general-purpose tool with a quitting-only import
graph, not a quitting-only definition.

Conversely, the general stochastic-game notions M1–M4, L1–L2, D1–D2, and
U1–U6 can be instantiated on `quittingGame reward`, since it is an ordinary
`StochasticGame` with `Act = Bool` (L1/L2 additionally require supplied
legality data). R1–R3, PM1–PM2, and P1–P2 are repeated-game notions on
`KernelGame` or `PublicMonitoring`; only PM1–PM2 and P2 have the one-state
realized-action adapter edges recorded above. Nothing in the declared surface instantiates
M1 at a quitting game or gives a direct theorem from Q1/Q2 to M1/M2; quitting
compilers use Q1/Q2 only as local root conditions inside stronger path or cycle
packages.

## 4. Highlighted open implication without a bridge theorem

**P2 → P1** (§2.5) requires the coherent selection/compactness theorem named in
the module docstring
(`GameTheory/GameTheory/Concepts/Stochastic/Transform/Repeated/RealizedActionRepeatedAdapter.lean:84`). No such theorem
is asserted, and no pipeline row is assigned. The reverse direction and the
existential-target consequence are proved in Lean under the conditions stated
in §2.5.

## 5. Declared absences

- `IsStagewiseNash` has one declaration file and no importers in `GameTheory/`.
- No `IsLiminfAverageEquilibrium` or `IsLimsupAverageEquilibrium` `Prop` exists
  in `GameTheory/`; §2.4 records bridge theorems rather than notion nodes.
- `GameTheory/GameTheory/Languages/MultiRound/StochasticGame.lean` defines the
  only `StochasticGame` structure.
  `GameTheory/GameTheory/Concepts/Stochastic/Core/Basic.lean` reopens its
  namespace rather than defining a second structure.

Thus the stochastic-game notions in Clusters 1–4, 6, and 7 use the same
underlying `StochasticGame` structure. Cluster 5 instead uses `KernelGame` and
`PublicMonitoring`; its connections to stochastic games are exactly the
adapter edges stated in §2.5. The open edges above are not artifacts of a
second `StochasticGame` definition.
