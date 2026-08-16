# Engineering roadmap

This is the living engineering plan for the current tree. It records desired
architecture, active priorities, and acceptance criteria. It is not a
changelog. Repository-transition provenance belongs in
[`TRANSITION.md`](../TRANSITION.md); ordinary implementation history belongs
in Git.

The roadmap does not authorize a stable downstream API or a GameTheory2
cutover. Exact theorem truth remains in Lean, while promotion and evidence
rules remain in [`PIPELINE.md`](PIPELINE.md).

## Priority order

1. Normalize assumptions that retained finite data can supply canonically.
2. Raise proof bodies toward short mathematical arguments over reusable APIs.
3. Preserve ownership, dependency direction, and narrow module interfaces.
4. Keep trust, generated evidence, and repository inventories reproducible.
5. Prepare a semantic waist for GameTheory2 without changing the dependency.

Work should be split into independently checkable vertical slices. A slice is
ready to merge only when its public statements, downstream callers, and
repository gates agree.

## Maintained engineering invariants

### Trust and build surface

- Project code contains no `sorry`, `admit`, explicit axioms,
  `native_decide`, `implemented_by`, unsafe declarations, partial definitions,
  or project-owned `set_option` commands.
- Warnings remain errors; global linter weakening is not an implementation
  technique.
- `AxiomAudit.lean` imports every project-owned Lean module. Only `propext`,
  `Quot.sound`, and `Classical.choice` are permitted library axioms.
- Lean options are scoped to the smallest library that needs them.
- Lean 4.32.2 and the committed dependency pins define the supported build.

### Ownership and dependencies

- `MathUE` owns project-generic mathematics and does not import game-semantic
  `GameTheory.*` modules.
- `UniformEquilibrium` owns integrated game-semantic results.
- `Research` may contain checked exploratory work, but it does not retain full
  copies of declarations already owned by `MathUE` or `UniformEquilibrium`.
- Production modules do not depend on `Research` or `Experiments`.
- Lean umbrellas are authoritative inventories. Every production module is
  reachable through the intended umbrella, and broad umbrellas are not used as
  convenience imports inside ordinary source modules.
- High-fan-in semantic infrastructure lives in a neutral owner rather than in
  `Diagnostics` or an example module.

### Reproducibility

- Generated evidence names its source data and generator when they exist.
- If original generation inputs are unavailable, the repository states that
  limitation and checks only reproducible integrity properties.
- Synchronization tooling operates on explicit staging directories and never
  treats the live repository as a cleanup target.
- Transition-specific paths, keep/drop decisions, and source-revision facts
  remain confined to `TRANSITION.md`.

## Assumption normalization

Remove a hypothesis only when retained data proves the same fact without
weakening the conclusion or changing later hypotheses. Classification must
inspect the complete elaborated telescope and, for data declarations, the
constructed body. A constant absent from the final displayed proposition may
still index a later hypothesis or a proof-carrying object.

Every touched declaration receives a two-sided strength review:

- derive or remove assumptions that retained data already supplies; and
- state the strongest stable conclusion proved by the argument, rather than a
  needlessly specialized corollary.

When that strengthening needs a wider API or mathematical redesign, record it
as an explicit review target instead of silently leaving the opportunity
unexamined. Mechanical censuses identify known syntactic families; a zero
census is never a claim that every theorem telescope is logically minimal.

### Finite quitting reward bounds

For a finite quitting reward table, use
`GameTheory.quittingRewardBound reward`, the finite sum of absolute reward
coordinates. Its nonnegativity and coordinate bounds are canonical. The L1
choice also controls row and subtable sums without introducing separate
cardinality factors.

Keep an arbitrary bound `M` when it occurs in a quantitative result, indexes
retained data, or couples a later hypothesis to the same scale. Do not ask a
caller for `0 ≤ M` when a retained coordinate-bound hypothesis and an
available player witness prove it internally. The reward-bound census and its
nonnegativity ratchet are enforced at zero by
`scripts/check_reward_bounds.py`.

`Research.General.FourRoleObstructionReduction.PositiveMinimumPlateau`
intentionally stores one positive reward bound that also determines explicit
mass-floor denominators. It is a coherent quantitative certificate, not a
removable theorem hypothesis.

### Order and inhabitance hypotheses

Do not carry both a strict inequality and its weak consequence for the same
simple endpoint. Normalize proof arguments in constructed terms to the strict
proof's `.le` projection. The narrow census in
`scripts/check_redundant_order_hypotheses.py` covers this schema and is enforced
at zero.

Do not retain a separate finite-type instance when a `Fintype` instance is
already in the same telescope. Likewise, a named membership witness supplies
the corresponding simple collection-nonemptiness proof, and an equality can
transport or decide simple endpoint bounds. These narrow schemas are enforced
at zero by `scripts/check_derivable_telescope_hypotheses.py`.
The ratchet reads explicit declaration binders only; section variables,
`include` commands, instance-indexed results, and body-derived facts remain
manual obligations under the complete-telescope rule above.

Derive `Nonempty ι` locally from a named player when the instance is used only
inside the proof. Retain it when an instance-indexed definition occurs in the
result or later telescope. Treat `DecidableEq` similarly: proof-local finite
bookkeeping can often use classical decidability, while computational data and
instance-indexed statements may genuinely retain the parameter.

Extend deterministic censuses one coherent hypothesis family at a time, and
use Lean elaboration as the call-site oracle.

## Proof and API quality

### Mathematical interfaces

- Put game-independent finite-sum, probability, topology, and optimization
  lemmas in `MathUE`.
- Prefer one parameterized theorem over player-by-player or fixed-arity copies.
- Express capstones as orchestration over named mathematical seams: certificate
  decoding, incompatibility, normalization, and semantic compilation should be
  independently reusable.
- Keep reader-facing declarations in `Theorems` as thin restatements that
  delegate to the owning proof.
- Do not expose scratch namespaces or generic helper lemmas through broad game
  namespaces.

The finite-product PMF API and finite-weight variation API are the canonical
owners for their respective calculations. New consumers should use them rather
than recreating nested expectation expansions or signed-mass estimates.

### Proof implementation

Use the tactic matched to the mathematical residue:

- `grind only` for closed finite propositional, membership, update, and
  extensionality bookkeeping;
- `ring` or `ring_nf` for polynomial normalization;
- `linarith` or `nlinarith` for ordered-ring consequences;
- `norm_num` and `omega` for concrete arithmetic; and
- named analytic or topological lemmas for limiting arguments.

Golfing is valuable when it exposes the right abstraction. It is not a reason
to hide a missing semantic lemma behind broad automation. Repeated isomorphic
proofs, long local simp inventories, and Cartesian case trees are signals to
extract an interface before shortening the final proof.

Large declarations should have an explicit mathematical reason to remain
large. Proofs that combine several conceptual steps should be decomposed at
those steps, with the public capstone reduced to composition. Generated literal
data is excluded from source-golf judgments but must have a deterministic
freshness or integrity check.

## Module and import design

- Use the narrowest direct imports needed by a module.
- Break dependency inversions by moving shared structures and semantic lemmas
  to neutral owners, not by creating forwarding cycles.
- Keep diagnostic examples downstream of the semantic interfaces they test.
- Split large files at stable mathematical boundaries while preserving public
  declaration ownership.
- Prefer hierarchical facades and generated inventories to hand-maintained
  mega-umbrellas.

Any module move or new file requires regeneration of `AxiomAudit.lean` and a
fresh import-graph check. A source-only refactor still requires compilation of
the changed owner and representative downstream consumers.

## Acceptance gates

Use narrow checks while iterating, then run the gates appropriate to the risk:

```text
lake env lean path/to/File.lean
lake build Module.Name
python3 scripts/check_docs.py
python3 -m unittest discover -s scripts -p 'test_*.py'
python3 scripts/check_import_graph.py
python3 scripts/check_proof_duplicates.py
python3 scripts/check_reward_bounds.py --check --max-nonnegative 0
python3 scripts/check_redundant_order_hypotheses.py --check
python3 scripts/check_derivable_telescope_hypotheses.py --check
python3 scripts/check_trust.py
```

Run a full `lake build` for changes to toolchains, Lake configuration,
dependency pins, umbrellas, module inventory, or broad semantic APIs. The full
build must include the nonvacuous exhaustive axiom audit. Report the exact
checks run; a static audit or focused build is not a full-build claim.

## GameTheory integration invariants

GameTheory supplies the native stochastic runner and uniform-payoff predicate.
The exact project proof view, quitting semantics, and ownership boundary are
specified in
[`GAMETHEORY_INTEGRATION.md`](GAMETHEORY_INTEGRATION.md). Engineering changes
must preserve the finite-law, finite-payoff, unilateral-update, and
uniform-payoff equivalences. Private `FinDist` representations and parallel
game foundations are outside the architecture.
