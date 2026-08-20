# Four-player quitting counterexample candidate search

This bounded experiment searches for four-player quitting reward tables that
resist an approximate equilibrium, following the negative route of GitHub issue
#40. It is reproducible numerical evidence about four parameterized families of
behavioral profiles. It is not a theorem, not a Lean check, and not evidence
that any table fails to admit a uniform equilibrium.

## Model

Players `1..4` simultaneously choose Continue or Quit at every stage. The first
stage with a nonempty quitting set `S` ends the game and pays the reward vector
`r_S` in `R^4`. If nobody ever quits the payoff is `0` to everyone. A profile is
an independent per-player, per-stage quitting hazard, possibly time-varying.

Exploitability of a profile is the maximum over players of the deviator's best
unilateral behavioral-deviation value minus that player's on-path value, taken
as a maximum over the phases of the profile. A counterexample table would keep
exploitability bounded below by a fixed `g > 0` over *all* profiles. This
program only searches inside four bounded architecture classes, so it can
report that no profile *in those classes* was found below the kill threshold.

Payoff entries are clamped to `[-4, 4]`.

## Seed table

The Solan-Vieille (2001) Section 3 table is the boundary seed:

```text
r{1}=(1,4,0,0)      r{2}=(4,1,0,0)      r{3}=(0,0,1,4)      r{4}=(0,0,4,1)
r{1,2}=(1,1,1,1)    r{1,3}=(1,1,1,0)    r{1,4}=(1,0,1,1)
r{2,3}=(0,1,1,1)    r{2,4}=(1,1,0,1)    r{3,4}=(1,1,1,1)
r{1,2,3}=(1,0,0,0)  r{1,2,4}=(0,1,0,0)  r{1,3,4}=(0,0,0,1)  r{2,3,4}=(0,0,1,0)
r{1,2,3,4}=(-1,-1,-1,-1)
```

The table is known to admit an approximate equilibrium through a period-2
two-quitter architecture, so it is not a counterexample. It is used to
calibrate the attack battery.

## Necessary-condition filters

A candidate must pass all filters at margin `g` (default `0.1`), with
`r_empty := 0`.

1. **Toggle instability.** At every coalition `S` including the empty set and
   the full set there is a player `i` with
   `max(r_{S+i}(i), r_{S-i}(i)) >= r_S(i) + g`.
2. **Viable owner.** Some player `i` has `r_{i}(i) >= g`.
3. **Collider and preemptor.** Every viable owner `i` (that is,
   `r_{i}(i) > -g`) has some `j != i` with `r_{i,j}(j) >= r_{i}(j) + g` and
   some `j != i` with `r_{j}(j) >= r_{i}(j) + g`.
4. **Preemption cycle.** In the digraph with edge `i -> j` when
   `r_{j}(j) >= r_{i}(j) + g`, every viable owner has an out-edge and every
   head of an edge has an out-edge; a directed cycle must be reachable from
   some viable owner.
5. **Iterated normal core.** With `m_{ij} = r_{j}(i) - r_{i}(i)`, player `i` is
   normal in a surviving set `T` when some `j` in `T`, `j != i`, has
   `m_{ij} <= 0`. Iterating removal of non-normal players from the full player
   set reaches a core; the core must have all four players. Smaller cores are
   covered by existing theorems.
6. **Simplex-normalized LCP screen.** Reject tables that admit an obvious
   equilibrium payoff. For each nonempty support `S` inside the core the square
   system `sum_j lambda_j r_{j}(i) = r_{i}(i)` for `i` in `S`, together with
   `sum_j lambda_j + lambda_0 = 1`, is solved exactly by Gaussian elimination;
   the tail weight `lambda_0` carries payoff `0`. A solution counts when all
   weights are nonnegative within `1e-7`, every remaining core player weakly
   prefers the mixture to quitting alone, and every non-core player weakly
   prefers it to `max(0, r_{i}(i))`. A strictly positive tail weight is
   accepted only when every solo-self payoff `r_{i}(i)` is at most `0`: after
   the spending phase the continuation is `0`, so any player with a positive
   solo-self payoff would quit late, and the tail-weighted mixture is not a
   strategically consistent screen hit.

Filter 6 is a heuristic screen, not a formal equilibrium gate: it looks only at
mixtures over *singleton* quitting rewards plus a tail paying zero, so it
neither certifies nor excludes equilibria supported on simultaneous quitting.
Note also that filter 2 already forces some `r_{i}(i) >= g > 0`, so on any table
that reaches filter 6 the consistency condition rules out every strictly
positive tail weight, and only fully spending mixtures can count as hits.

## Attack battery

A candidate dies when any attack finds a profile with exploitability at most
`eps_kill` (default `0.02`).

The evaluator shared by attacks A, C, and D is exact given the profile. For a
periodic hazard matrix `p[i][t]` the stage outcome distribution is a product of
Bernoullis, so with
`P_t(S) = prod_{i in S} p[i][t] * prod_{i not in S} (1 - p[i][t])` the on-path
values solve the periodic recursion
`V_t = sum_{S nonempty} P_t(S) r_S + P_t(empty) V_{t+1}`, unrolled around the
cycle in closed form. A deviator faces a phase-indexed optimal-stopping problem
whose value is the maximum over the `2^P` deterministic phase-indexed stopping
policies; each policy value is again a closed-form cyclic solve, so the
enumeration gives the exact best response up to floating point. Quitting at
phase `t` pays `sum_{T subset of others} q_t(T) r_{T+i}(i)`, which includes the
exact collision terms.

When no absorption is possible at all around a cycle the recursion is solved as
value `0`, matching the never-quit payoff.

- **A. Stationary.** Rates `x` in `[0,1]^4`, evaluated as the `P = 1` case. Full
  `6^4 = 1296` grid over rates `{0, 0.02, 0.1, 0.3, 0.6, 1}` plus Nelder-Mead
  from the grid optimum and four fixed starts. For `P = 1` the policy
  enumeration reduces to `max(quit-now value, never value)`, the closed form for
  a stationary environment.
- **B. One-quitter cyclic.** All `20` cycles on subsets of size `2, 3, 4` up to
  rotation, with per-phase absorption probabilities `q_k`. On-path values solve
  `V_k = q_k r_{v_k} + (1 - q_k) V_{k+1}`. Deviator values again come from
  enumerating the `2^m` stopping policies, where the scheduled quitter `v_k`
  who deviates simply passes through his own phase without absorption. Four
  Nelder-Mead starts per cycle.
- **C. Two-quitter periodic.** The Solan-Vieille repair shape: `21` period-2 and
  `40` period-3 schedules assigning an active pair to each phase, with two free
  hazards per phase and zero hazard for the inactive players. Collisions inside
  the active pair are exact, since C is evaluated by the shared periodic
  evaluator. Three Nelder-Mead starts per schedule.
- **D. General periodic.** Free hazards `p[i][t]` for periods `1, 2, 3, 4, 6`,
  optimized by Nelder-Mead over `4P` logistic variables from five fixed and
  three seeded-random starts.

Attacks run cheapest first (A, B, D, C). During the search the battery is
abandoned as soon as its running minimum drops to the incumbent score, which is
sound for the accept decision because the minimum over the remaining attacks
can only be smaller; every accepted table therefore carries a complete,
untruncated battery score. The reported best table is always re-evaluated with
the complete battery.

## Search protocol

Three independent random-restart hill-climbing chains, with RNG seeds `40`,
`41`, and `42`. A proposal perturbs a random subset of one to eight table
entries by Gaussian noise, clamped to `[-4, 4]`: the step size is `sigma = 0.25`
usually and `jump_sigma = 0.6` with probability `0.2`, so a chain can leave a
basin without waiting for a restart. Proposals failing any filter are discarded
without an evaluation, and the results file records which filter rejected each
one. The score of a candidate is the minimum exploitability found across the
whole battery, so a higher score is more counterexample-like. A chain accepts
only strict improvements and restarts from the seed table after `40` consecutive
non-improving evaluations.

Chains are pure functions of their seed and budgets, so they run in separate
processes; `--workers` changes wall time and not results. Each chain's best
table then goes through the deep re-attack described below, and that verdict,
not the search-time score, decides whether anything survived.

## Reproduction

Run from the repository root with Python 3 (standard library only; numpy and
scipy are not available in this environment and are not used). Let
`DIR=Experiments/singleton_collision_candidate_search`. Then:

```text
python $DIR/singleton_collision_candidate_search.py \
  --evaluations 500 --time-budget 100000
```

That writes `results.json`: three chains of `500` evaluations each, seeds
`40,41,42`, with every chain's best table deep-re-attacked in the same run. It
is deterministic given those flags. `--margin`, `--kill`, `--sigma`,
`--jump-sigma`, `--jump-probability`, `--chain-seeds`, and `--restart-patience`
expose the remaining constants.

The two budgets are a per-chain evaluation cap and a wall-clock cap, whichever
binds first. Only the evaluation cap gives a machine-independent result: a run
stopped by the clock does fewer evaluations on a slower or busier machine and
lands on a different table. The recorded run therefore passes a wall-clock
budget large enough that the evaluation cap binds, and each chain records which
cap ended it under `termination` with a `reproducible_across_machines` flag. The
`--time-budget` default is `600` seconds, per the original protocol; it is
raised here only so the recorded artifact is reproducible.

The per-chain budget is `500` rather than the `2000` originally sketched.
`2000` per chain is roughly two hours of wall time per chain here, and the deep
re-attack results below show that extra hill-climbing evaluations mostly buy
overfitting of the cheap battery rather than genuinely harder tables, so the
budget was spent on stress-testing instead.

Every run begins with an evaluator cross-validation on `--self-check-trials`
random tables and profiles (default `300`, its own fixed RNG seed) and aborts if
it fails. The check verifies four identities: that the closed-form on-path
recursion agrees with the separate decomposition of a phase into the player's
own quit and continue branches; that exploitability is never negative, as it
must be since a pure best response dominates the on-path mixture; that the same
non-negativity holds for the separate one-quitter evaluator; and that for period
one the policy enumeration reproduces an independently written stationary closed
form. Half the trials draw hazards log-uniformly down to `1e-16`, because that
near-degenerate regime is where the optimizers actually spend their time and is
not reached by uniform draws. Measured errors are recorded under
`evaluator_self_check` in the results files.

### Deep re-attack

The search-time battery is deliberately cheap, since it runs once per candidate.
A table that survives it is therefore only interesting if it also survives a far
heavier search: many more restarts, a finer stationary grid, and general periods
up to `8`. Every chain's best table gets this treatment automatically, recorded
under `chains[i].best.deep_reattack`, and the same stress test can be pointed at
a saved results file on its own:

```text
python $DIR/singleton_collision_candidate_search.py \
  --reattack $DIR/results.json --output $DIR/results_reattack.json
```

The deep verdict supersedes the search-time score for the table it examines.
Running it takes under a minute per table, which is itself worth noting: the
search-time battery is weak relative to what is affordable, and its numbers
should be read as loose upper bounds rather than as class minima.

## Outcome

Seed calibration, from `results.json`:

- the seed passes all six filters. Filter 6 finds the equal mixture of the four
  singleton rewards, weight `0.2` each with tail weight `0.2`, paying
  `(1,1,1,1)`, but does not count it: the tail weight is strictly positive while
  every solo-self payoff is `1 > 0`, so the mixture fails the consistency
  condition above. Note the direction of this: passing filter 6 only means the
  screen found no obvious equilibrium payoff, and the seed does admit an
  approximate equilibrium, which is exactly why the seed is a boundary
  calibration table rather than a counterexample;
- attack C kills the seed: the best schedule found is the period-2 alternation
  of pairs `{1,3}` and `{2,4}` with per-phase hazards about `0.254` and `0.266`,
  at exploitability `2.6e-05`. Optimizing that known schedule on its own reaches
  `1.7e-10`, so the implementation reproduces the published repair;
- attacks A, B, and D fail to kill the seed, at best exploitability `0.0605`
  (stationary), `0.0834` (one-quitter cyclic), and `0.0506` (general periodic).
  The stationary figure is consistent with the source paper's claim that this
  table has no stationary approximate equilibrium, but a bounded grid plus
  Nelder-Mead search is evidence for that claim, not a proof of it.

Search outcome: **no counterexample candidate survives.** Three chains of `500`
evaluations each, seeds `40`, `41`, `42`, all terminating on the evaluation cap.
Every chain's search-time score sits above the `0.02` kill threshold, and every
one of them collapses under the deep re-attack:

| chain | restarts | search score (binding) | deep score (binding) |
| --- | --- | --- | --- |
| `40` | `3` | `0.026252` (two-quitter) | `2.7e-05` (two-quitter) |
| `41` | `6` | `0.030103` (one-quitter) | `1.5e-06` (two-quitter) |
| `42` | `3` | `0.027203` (two-quitter) | `4.7e-04` (two-quitter) |

Three chains out of three produced a search-time survivor, and all three were
killed by two to four orders of magnitude. In every case the winning profile was
a two-quitter schedule the cheap attack had failed to find.

Filters barely bind. Across `1539` proposals only `39` were rejected, all by
just two of the six conditions: toggle instability `30`, iterated normal core
`9`. Filters 2, 3, 4, and 6 never rejected anything in this run, so near the
seed they are not what constrains the search.

**Every apparent survivor has been an optimizer artifact.** This happened at
three successive strengths of attack, and it is the most important thing this
experiment established:

- a table scoring `0.026070` against the search-time battery fell to `0.002923`
  under the first version of the deep re-attack;
- a table scoring `0.030103` at search time survived *that* version at
  `0.029331`, and fell to `1.5e-06` once the stress test was widened to include
  period-four two-quitter schedules;
- the widening also moves ordinary numbers: search-time stationary scores of
  `0.0447`, `0.0453`, `0.0346` become deep scores of `0.0266`, `0.0349`,
  `0.0332` on the same three tables, for the same profile family.

In each case the hill climb had found a table whose equilibrium the weaker
search happened to miss, not a table without an equilibrium. The deep re-attack
in the checked-in source is the widened version, so the recorded verdict is
taken at that strength. Nothing here came close to surviving, and the honest
lesson is that a high search-time score is evidence about the optimizer, not
about the table.

## Assumptions and limitations

- **Bounded architecture classes.** The battery covers stationary profiles,
  one-quitter cycles, two-quitter period-2 and period-3 schedules, and free
  periodic hazards of period at most `6`. Behavioral profiles that are
  history-dependent beyond a fixed phase counter, aperiodic, or of larger
  period are not searched at all. A table surviving the battery would be a
  *candidate* only.
- **Fine-block limit in attack B.** Attack B assumes that inside the block
  assigned to player `v_k` only `v_k` quits, so a deviator quitting in that
  block never collides and receives `r_{i}`. Collisions vanish in that limit by
  assumption; they are not computed. Attacks A, C, and D compute collisions
  exactly.
- **Local optimization.** Nelder-Mead with finitely many starts finds local
  minima. A reported exploitability is an upper bound on the true minimum over
  its class, so a *kill* is trustworthy while a *survival* may only mean the
  optimizer missed the equilibrium. This limitation is visible in the recorded
  seed diagnostics, and it is not small. Class D contains classes A and C as
  subspaces, yet on the seed its unstructured search over `4P` variables reports
  `0.0506` where C's structured search reports `2.6e-05`. Sharper still, D's own
  optimum on the seed is attained at period `1`, which *is* class A, at `0.0506`
  against the `0.0605` that A reports for the identical family: two searches
  over the same four-dimensional set disagree by `0.01`. Only the smaller number
  is meaningful, and the true minimum of either class may be smaller than both.
  This is why the score is the minimum over the whole battery, and why a
  surviving table would need re-attacking before anyone took it seriously.
- **Floating point.** Values are IEEE doubles. A cycle's total absorption is
  computed by summing logarithms and applying `expm1`, not by subtracting a
  product of factors from one, and absorption counts as absent only when it is
  exactly zero. This is not a cosmetic choice. The subtractive form with an
  absolute `1e-13` cutoff was the original implementation, and it silently
  reported the never-quit branch as worth zero once the optimizers pushed
  hazards to about `1e-14`, which they routinely do while chasing the
  fine-block limit. Because the on-path and deviator recursions absorb at
  slightly different rates, they crossed that cutoff at different moments and
  produced a negative exploitability of `-0.14` on one table, which is
  impossible. The self-check now covers that regime. The LCP screen uses pivot
  tolerance `1e-12` and feasibility tolerance `1e-7`.
- **Filters are heuristics.** Filters 1 through 5 are necessary-looking
  structural conditions assembled for this screen, and filter 6 is an explicit
  heuristic. None of them is proved here to be necessary for a table to be a
  counterexample, so a table rejected by a filter has not been shown to admit an
  approximate equilibrium.
- **The search optimizes the battery, not the mathematics.** Hill climbing on a
  score that is itself the output of a bounded local search rewards tables whose
  equilibria the optimizer happens to miss. All three chains demonstrate this
  concretely rather than hypothetically: each ended above the kill threshold,
  and each was then killed by two to four orders of magnitude by a stronger
  search over the *same four classes*. Any future survivor must be
  deep-re-attacked, and even a survivor of that is only a candidate. The deep
  re-attack itself has no claim to being final: it was widened once already,
  after a table survived its earlier version.
- **Nothing here is a theorem.** Killing every architecture the program knows
  about proves nothing about the set of all behavioral profiles, and failing to
  kill a table proves nothing about the nonexistence of an approximate
  equilibrium for it.
