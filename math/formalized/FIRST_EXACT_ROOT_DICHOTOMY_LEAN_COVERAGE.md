# First exact-root dichotomy: Lean coverage

Packet: `FIN4_FIRST_EXACT_ROOT_SURVIVAL_OR_UNIQUE_SURE_RESET.md`.

`StationaryQuitNowCapPinSource.firstExactRoot_dichotomy` in
`UniformEquilibrium/Diagnostics/Quitting/FirstExactRootStationaryDichotomy.lean`
assembles conclusions (1)–(10) from the actual stationary source and the
absence of a uniform-equilibrium payoff. It works for arbitrary finite player
types, not only four players. The source retains the eventual attained Quit0
cap, positive named debt, reward bound, and cap convergence. Source payoff
bounds, a positive carrier minimum, and a positive terminal gap are derived.

## Literal outputs

- `eventually_all_exactRoot_bounds` gives the uniform absorption floor and
  named-coordinate and total debt expenditures for every compatible root.
- `FirstStationaryRootPositiveBranch` retains one common source/root
  subsequence, positive survival, the literal copied-root Quit0 response,
  its exact gain, and the resulting debt lower bound.
- `FirstStationaryRootZeroBranch` retains one common subsequence for the
  source, root, and endpoint selection: a unique sure limiting owner,
  vanishing outsider debt, the owner debt floor, an attained shifted cap,
  and positive opponent reach. The same limiting stationary root has zero
  outsider debts and an attained Never cap with a terminal-gap gain.
- `exists_stationary_quitNow_or_never_completeCap` in
  `UniformEquilibrium/Quitting/Stationary/CompleteEndpointChoices.lean`
  includes stationary opponents who Continue surely; no contraction or
  interiority assumption was added.

The component compactification and response theorems reside in
`FirstExactRootCompactification.lean` and `FirstExactRootSurvivalResponses.lean`
under `UniformEquilibrium/Diagnostics/Quitting/`.

## Regression and limits

`UniformEquilibrium/Quitting/Examples/UniqueSureNeverReactivationRegression.lean`
proves the displayed exact root, its unique sure owner, the source's unique
debtor with debt one fifth, the owner's attained Never cap, and the repaired
child's outsider Quit0 gain one twelfth. `root_isZeroNash_exactTail` supplies
the exact-root compatibility at the zero auxiliary continuation. That
auxiliary continuation is not claimed to be a carrier point.

Neither branch produces a renewed cap pin, a returned minimum source, or a
uniform-equilibrium payoff. The regression shows why the stationary Never
repair alone does not provide renewal. It is not a counterexample to uniform
equilibrium existence.

## Verification

Targeted Lean checks and named dependency builds passed. Independent review
checked packet conclusions (1)–(10), actual-source hypotheses, the common
selector, unrestricted caps, and the numerical regression. Its requested
exact-root compatibility statement was added and checked. The integrated full
`lake build`, including the exhaustive axiom audit, passed with 11435 jobs.
Trust, import-graph, documentation, duplicate-proof, reward-bound, and
redundant-hypothesis checks passed. All 113 Python tests passed with
`TMPDIR=/dev/shm`; the default temporary location was rejected by a safety
test because a pre-existing `/tmp/.git` directory contains that location.
