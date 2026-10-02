# Software and mathematics audit of the Fin4 value oracle

Reviewer: `CODEX_GODEL`

## Gate verdict

**FAIL as a runnable table-search/value-oracle artifact.  REVISE as a
mathematical reference checker.**

The mathematical reduction to a direct hazard cube is valuable and the core
finite-clock expression appears correct.  The shipped software, however, is
not a value oracle, not a table search, and not suitable for a 24--48 hour
run.  It contains exact expression and certificate primitives but none of the
search, checkpoint, coordination, or bounded-resource machinery claimed by the
larger theorem document.  A concrete recursion bug also prevents evaluation
at levels far below those required by meaningful scale contracts.

No file in `../fin4_value_oracle/` was modified during this audit.

## What is actually implemented

`fin4_value_oracle.py` implements:

- exact rational hazard/law conversion;
- the direct finite-clock hazard expression for one supplied rational table
  and level;
- exact point evaluation through the legacy interval DAG evaluator;
- a lower-tree certificate schema and verifier;
- a Lipschitz robust-box wrapper around a supplied positive lower tree;
- the arithmetic constants for a configurable scale; and
- the scalar outer-point elimination formula.

It reexports the legacy `TreeSearch`, but does not wrap it in a complete
lower/upper resolver.

It does **not** implement:

- Theorem C's certified Cauchy oracle;
- Theorem D's terminating configurable two-sided resolver;
- rational-hazard enumeration or any other primal/upper search;
- reward-table enumeration, optimization, mutation, or candidate generation;
- Theorem G's finite reward-cube atlas or a cover checker;
- a command-line search or verification interface for the new certificates;
- checkpoint/resume;
- parallel or distributed work coordination; or
- resource limits, progress reporting, early cancellation, or run manifests.

Thus this is a checker/library skeleton, not a real table search.

## Clean-clone and one-command audit

The README's only test command is `pytest -q`, but `pytest` is not declared in
a requirements or project file and is absent in the supplied environment.
The command fails with exit code 127.  The mathematical checker itself is
standard-library only, but the documented test path is not.

Running

```text
python3 fin4_value_oracle.py
```

exits successfully while doing nothing and printing nothing.  There is no
`main`, argument parser, input schema example, search command, output
directory, or certificate-verification command.  There is no package metadata
or install step.  A user cannot start a search from a clean clone with one
command.

## Correctness bug: recursive DAG evaluation fails at small levels

The expression factory stores nodes in topological order, but
`legacy_exact_search.ExprFactory.eval_interval` evaluates them recursively.
The chronological prefix expressions form deep addition chains.  On the dense
normalized table with every reward coordinate equal to one, exact point
evaluation gives:

```text
level 1:  PASS
level 5:  PASS
level 10: RecursionError
level 12: RecursionError
level 15: RecursionError
level 18: RecursionError
level 20: RecursionError
```

At level 20 the represented clock has only 161 dates.  The failure occurs in
`ExprFactory.eval_interval`, before any search.

This is fatal for the advertised scale contracts.  Representative exact
contracts are:

```text
epsilon=1,   alpha=1/2:    N=49,    T=393,    variables=1,572
epsilon=1/10,alpha=1/2:    N=481,   T=3,849,  variables=15,396
epsilon=1/10,alpha=99/100: N=24,001,T=192,009,variables=768,036
```

All are beyond the observed recursion failure.  Raising Python's recursion
limit is not a robust repair: tree verification and assembly are recursive as
well, and the underlying DAG already has a topological order suitable for an
iterative evaluator.

## Search-state and 24--48 hour audit

The inherited `TreeSearch` is breadth-first.  Every pending node stores:

- a complete dictionary containing an interval for every hazard variable; and
- its complete split path.

Every split copies the full dictionary twice.  The queue is a Python list and
uses `pop(0)`, adding linear queue-shift cost.  There is no disk spill and no
memory ceiling.

On one seeded level-one problem (36 variables, 2,594 DAG nodes), 1,000 exact
steps took approximately 10 seconds, produced no leaf at all, and left 1,001
full pending boxes in memory.  Breadth-first longest-side subdivision reaches
depth only logarithmically in processed nodes.  Merely splitting every one of
36 variables once along all branches requires the depth-36 frontier, on the
order of `2^36` boxes, unless earlier interval pruning happens.  At realistic
levels there are thousands to hundreds of thousands of variables.

Accordingly, an unattended 24--48 hour run would not perform a table search.
For a lower-tree call it would likely do one of:

- fail immediately with `RecursionError` at a meaningful level;
- exhaust RAM as the in-memory BFS frontier grows;
- spend its entire run subdividing a single supplied table without producing
  a leaf or useful upper profile; or
- slow sharply from list queue operations and exact rational interval growth.

Disk growth is currently zero only because no checkpoint, log, or result is
written.  If a final tree were ever assembled, its serialized size could be
proportional to an enormous leaf set.  There is no streaming certificate
format or quota.

## Checkpoint, resume, and deterministic coordination

There is no checkpoint or resume state.  `TreeSearch` exposes in-memory
`pending` and `leaves`, but no stable serializer records:

- the reward hash and normalized table;
- level and threshold;
- expression/certificate format version;
- frontier boxes and split paths;
- closed leaves;
- upper candidates;
- work counters; or
- heuristic state.

Termination, `SIGINT`, machine restart, or process failure loses all work.

The current single process is deterministic in a weak sense: variable order,
midpoint cuts, and exact arithmetic are deterministic.  There is no
coordination layer, however.  No stable task identifiers, leases, idempotent
worker results, duplicate suppression, deterministic merge, or multi-process
protocol exists.  Calling it deterministic distributed search would be
incorrect.

## Early stopping and exact/heuristic boundary

The code has no heuristic component, so it does not currently blur heuristic
results into exact claims.  It also has no actual upper search.  This means it
cannot exploit the most important early-stop event: finding an actual hazard
profile below the current threshold.  The inherited lower tree can stop only
after certifying the entire cube.

For a usable two-sided oracle, heuristic optimizers may propose hazard profiles
or reward tables, but every accepted upper profile must be recomputed exactly,
and every accepted lower result must be a verified complete tree.  Heuristic
scores, failure to find a profile, elapsed time, or exhaustion of a selected
table set must never be reported as lower evidence.

The theorem document correctly says the direct checker is not Lean-checked and
does not consume the inert source.  The README should additionally state that
the Cauchy oracle, configurable resolver, reward atlas, and table search are
mathematical constructions not implemented by this package.

## Mathematical audit

The following ordinary-mathematics claims survive this review:

- **Theorem A:** `eta <= F_N <= eta + 24/N`, using actual common-quantile
  compression and the 2-Lipschitz semantic objective.
- **Theorem B:** the radius-box minimization identity
  `A_N = max(0, F_N - 24/N)`.
- **Hazard surjectivity:** the polynomial hazard cube maps onto all four
  finite-clock marginal simplexes, with rational right inverses on rational
  laws.
- **Theorems C and D as existence/computability arguments:** strict-margin
  interval completeness and rational hazard density can be dovetailed to
  produce certified brackets or the configurable lower/upper alternative.
  These algorithms are not implemented here.
- **Theorem E:** positive gap is the union of the open semialgebraic strata
  `F_N > 24/N`.
- **Theorem F:** the robust-box constants follow from the 2-Lipschitz reward
  bound.
- **Theorem G as an ordinary compactness/effective-enumeration theorem,** once
  the lower neighborhoods use strict extra margin and the finite rational-box
  cover itself is included in the certificate.  No such atlas generator or
  cover verifier is shipped.

The direct hazard expression agreed with the legacy exact terminal semantics
on all 20 supplied seeded rational cases.  All seven supplied test functions
passed when invoked manually, and both modules passed `py_compile`.

One semantic qualification remains necessary.  A lower certificate proving
`eta(r) >= gamma` proves a positive cap-supremum gap.  An arbitrary opponent
profile need not attain its cap exactly.  If a downstream theorem requires a
literal deviation with a weak gain bound, approximate cap attainment safely
gives any smaller gap, for example `gamma/2`; the software or documentation
must not silently claim literal attainment at `gamma`.

## Test gaps

The current tests are useful but too small and too local.  Missing tests
include:

- a dense nonzero table at a contract-generated level (this would catch the
  recursion failure);
- a successful nontrivial lower-tree certificate and JSON round trip;
- a successful positive robust-box certificate and corrupt-box rejection;
- exact after-support versus Never tests through the new hazard expression;
- a complete lower/upper scale resolver integration test;
- checkpoint interruption and byte-identical resume;
- deterministic worker merge and duplicate-result tests;
- bounded-memory frontier spill;
- clean-clone one-command smoke and 10-minute soak tests; and
- an end-to-end reward-table candidate that is heuristically proposed and
  then either exactly rejected or certified.

## Required repair list

### P0: make exact evaluation and verification reliable

1. Replace recursive DAG evaluation with an iterative topological evaluator.
2. Build large sums/products as balanced DAGs where practical.
3. Replace recursive tree verification/assembly with iterative traversals or
   an explicitly bounded-depth certificate format.
4. Add the dense level-10-and-above regression before claiming any configured
   scale works.

### P0: implement the claimed oracle

5. Implement the actual lower/upper dovetail: exact tree search plus rational
   or heuristic-proposed hazards verified by `terminal_semantics`.
6. Implement the finite bracket refinement from Theorem C and the one-shot
   resolver from Theorem D.
7. Provide commands such as `search-table`, `bracket`, `verify`, and `resume`,
   with documented JSON reward input and certificate output.
8. Add `from_json` and independent verification paths for robust-box and
   bracket/atlas certificates.

### P0: make long runs survivable

9. Replace list BFS and full-box copying with a compact persistent frontier,
   a `deque`/priority queue, and delta-encoded dyadic boxes.  Use adaptive
   best-first or depth-first work ordering rather than a uniform BFS grid.
10. Add atomic periodic checkpoints containing a versioned problem hash,
    frontier, leaves, upper incumbent, counters, and deterministic heuristic
    state.
11. Add bounded RAM, disk-backed frontier spill, certificate streaming, disk
    quotas, graceful signal handling, and explicit exit statuses.
12. Emit regular progress metrics: evaluated boxes, pruned boxes, frontier
    size, incumbent upper value, certified lower threshold, RAM/disk use, and
    checkpoint age.

### P1: implement real table search and deterministic coordination

13. Add a clearly heuristic candidate-table generator or exact rational-table
    enumerator.  Keep candidate scores outside the trusted certificate path.
14. Define deterministic work IDs from reward hash, level, threshold, and
    split path; add leases, idempotent result files, duplicate suppression, and
    sorted deterministic merge for multi-worker runs.
15. Stop and cancel competing work immediately when an exact upper witness or
    complete lower tree resolves a query.
16. For reward-cube atlas mode, implement and verify the finite rational-box
    cover, not merely the certificates attached to individual boxes.

### P1: clean-clone usability and claim hygiene

17. Supply a `pyproject.toml` or a standard-library test runner, pin optional
    test dependencies, and make the README command work on a clean clone.
18. Include a bounded smoke example and one command that creates a run
    directory, manifest, checkpoint, logs, and exact result.
19. Add a feature matrix distinguishing proved mathematics, implemented exact
    verification, implemented exact search, optional heuristics, and Lean
    coverage.
20. Preserve the theorem document's honest nonclaim: even a global value
    certificate does not construct or consume the source-attached inert
    machine.

## Bottom line

The direct hazard formulation is a sound mathematical simplification and a
promising exact certificate kernel.  The current package should not be sent on
a long run or described as a table search.  Its next gate is not optimization
tuning; it is implementing a total two-sided oracle with nonrecursive exact
evaluation, durable bounded state, and a real command-line workflow.
