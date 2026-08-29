# Uniform-equilibrium research experiments

This directory is deliberately isolated from the production theorem graph.
Its programs are small executable falsifiers or finite-model prototypes for
research ideas. Production modules never import this directory. A successful
finite run is evidence only for its stated bounded claim and does not promote
that claim into the production import graph.

An experiment result records its tracked executable source, exact reproduction
command, assumptions, limitations, and compact evidence. A checked-in payload
whose generator is unavailable instead has a deterministic integrity checker;
its owning experiment record states the provenance loss. Generated caches, logs,
screenshots, and raw runs are not experiment records. Experiments may import
Research; Research must not import this directory.

## Directory lifecycle

- The top-level registered programs form the reproducible base
  suite listed below; keep their paths stable because `run_all.py` and
  `RESULTS.md` refer to them directly.
- [`../quitting_repair_cegis/`](../quitting_repair_cegis/) is the tracked exact-rational
  repair search package.
- `../certsearch/` contains certificate-guided searches.
- `../counterexample_pairwise_consistency/` contains the pair/triple
  consistency campaign and its exact witnesses.
- `../counterexample_search/` contains focused falsifier programs.

Python caches, `*.olean`, screenshots, and logs are generated products rather
than experiments and should not be stored here.

Every registered program must be source-reproducible and listed in
`run_all.py`. The repository audit rejects missing or untracked sources and
production imports of experiments. Remove an abandoned program from the
registry; do not rely on generated output to keep it running.

Proposed adversarial searches that have not yet been implemented are specified
in [`PROPOSALS.md`](PROPOSALS.md). Each proposal records its exact finite
protocol and the proof required before any result can be promoted beyond
bounded experimental evidence.

Run the registered base suite with:

```text
python Experiments/Base/run_all.py
```

The repository gate also checks that every Base Python program is registered,
has a uniform `run()` entry point, emits a unique experiment identifier, and
passes through the suite:

```text
python scripts/check_experiment_registry.py --execute
```

The suite uses only the Python standard library. The runner prints a
machine-readable JSON summary, and each experiment contains internal
assertions for its stated finite claims. Exact external data is not itself a
Lean proof: promotion requires constructing the named production certificate.

| ID | Program | Question tested |
|---|---|---|
| E01 | `jointly_controlled_group_lottery.py` | Does a finite-group signal give unilateral-deviation-proof public randomness, and exactly where does transition factorization enter? |
| E02 | `inhomogeneous_hazard_scheduler.py` | Which vanishing schedules amplify recurrent hazards, and which irreversible leaks remain fatal? |
| E03 | `path_complete_livsic.py` | When do edge charges admit a global account potential, and what does a path-complete family add? |
| E04 | `atlas_progress_analyzer.py` | If atlas leaves are treated as stuck proof terms, which constructors lack concrete elimination rules? |
| E05 | `arc_orientation_scan.py` | Can changing an equilibrium arc alter its limiting support/orientation in small exact models? |
| E06 | `owner_monodromy.py` | Can owner-custody failure be represented as a computable cocycle/monodromy obstruction? |
| E07 | `kelly_debt_boundary.py` | Can likelihood evidence with quadratic information growth pay a linear punishment debt? |
| E08 | `causal_state_minimizer.py` | How large is the exact predictive-state quotient of a finite hidden process? |
| E10 | `small_game_census.py` | Can an exact exhaustive census separate generic equilibrium-support phenomena from degenerate curiosities before an atlas-scale census is attempted? |
| E11 | `continuous_time_resolvent.py` | Does the reduced Abel resolvent coincide with an exponentially killed continuous-time generator model? |
| E12 | `collateral_account.py` | Is a bounded potential exactly a finite escrow bound for its pathwise account increments? |
| E14 | `predictive_compression.py` | When does contraction make a finite quantized belief filter uniformly accurate, and how can rare observations break it? |
| E15 | `sigma_delta_lottery.py` | Can one robust random phase give exact one-time marginals and bounded prefix discrepancy for a rational rate stream? |
| E16 | `abel_turnpike_retargeting.py` | How can an Abel boundary layer retain positive mass while every fixed-policy Cesaro occupation converges to a different sustainable target? |
| E17 | `multiscale_filter_bank.py` | Can one logarithmically slow calendar amplify finitely many polynomial access scales while making inverse-power monitoring bills sublinear? |
| E18 | `transition_algebra.py` | What algebra and commutant are generated by endpoint-like transition/payoff operators, and where do transient nilpotent modes live? |
| E19 | `player_representation.py` | How does player payoff space split into common, deviator, opponent-average, and redistribution channels? |
| E20 | `cyclic_fourier_abel_cesaro.py` | Which cyclic representation modes survive a slow-kernel Abel limit but disappear under every fixed-policy Cesaro limit? |
| E22 | `markov_hodge_currents.py` | Can finite stationary edge fields be decomposed canonically into gradient and divergence-free current components, including owner-valued cancellation? |
| E23 | `adiabatic_markov_tracking.py` | Does a moving two-state invariant law track when parameter variation is asymptotically slower than the closing spectral gap, and fail at the critical scale? |
| E24 | `metastable_schur_confluence.py` | Is effective-generator and effective-reward elimination independent of the order in which fast transient states are removed? |
| E25 | `thermal_equilibrium_selection.py` | Do different temperature/discount scalings select different stationary logit branches and targets in Big Match and Sorin's absorbing game? |
| E26 | `entropy_current_debt.py` | How do irreversible current, entropy production, tilted pressure, and linear payoff debt scale near detailed balance? |
| E27 | `common_reversible_dirichlet.py` | Do distinct reversible kernels with a shared invariant law admit one exact coercive Dirichlet geometry under arbitrary switching? |
| E28 | `finite_controller_cycle_verifier.py` | Once a deterministic controller is fixed, do positive cycles and potentials give short exact deviation certificates? |
| E29 | `exact_rate_memory_blowup.py` | How much recurrent phase memory is required to generate an exact reduced rational rate with bounded discrepancy? |
| E30 | `contextual_cycle_sat.py` | Can selector synthesis be hard even when every proposed contextual cycle certificate is easy to verify? |
| E31 | `commit_reveal_coin.py` | Which timing and abort assumptions separate robust simultaneous coins from vulnerable sequential and commit/reveal protocols? |
| E32 | `threshold_secret_sharing.py` | Does threshold sharing create a genuine secret phase, and exactly which privacy is lost when shares are public? |
| E33 | `live_entropy_budget.py` | Can a finite hidden or public seed provide a linear tail of conditional unpredictability? |
| E34 | `cap_nash_endpoint_transport_search.py` | Do the cap–Nash endpoint transport and auxiliary excess-budget inequalities survive exact finite-grid checks? |
| E35 | `minimum_plateau_q_budget_search.py` | Do the minimum-plateau Q-budget restrictions survive an exact four-player negative control and stationary-root screen? |
| E36 | `semantic_final_regime_search.py` | Are the final minimum-semantic atomic and marked-plateau passports finitely consistent while admissible pure roots are absent? |

The output records `status`, the exact checks performed, and limitations. A
negative or inconclusive result is retained: these scripts are intended to kill
attractive but false interfaces early.

The final three registered programs are paired with their detailed reports:

- [`CAP_NASH_ENDPOINT_TRANSPORT_AUDIT.md`](CAP_NASH_ENDPOINT_TRANSPORT_AUDIT.md)
  (`E34`, `cap_nash_endpoint_transport_search.py`);
- [`MINIMUM_PLATEAU_Q_BUDGET_SEARCH.md`](MINIMUM_PLATEAU_Q_BUDGET_SEARCH.md)
  (`E35`, `minimum_plateau_q_budget_search.py`); and
- [`SEMANTIC_FINAL_REGIME_SEARCH.md`](SEMANTIC_FINAL_REGIME_SEARCH.md)
  (`E36`, `semantic_final_regime_search.py`).
