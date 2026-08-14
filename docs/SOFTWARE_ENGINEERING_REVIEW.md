# Software-engineering review

This is the durable engineering review of the current tree. It records
software structure and proof-production risks, not theorem status or a stable
downstream API. Extraction and repository-transition facts are recorded only
in [`TRANSITION.md`](../TRANSITION.md).

## Baseline

The reconstruction baseline completed a full `lake build` with 10,155 jobs and
ran a nonvacuous `AxiomAudit` over the project-owned declarations. At review
start, the inventory had 911 `UniformEquilibrium` Lean modules and 1,375
project-owned Lean files scanned by the trust checker. The production boundary
is the pinned `GameTheory` submodule.

The review initially found 16 `UniformEquilibrium` modules that were not
reachable from `UniformEquilibrium.lean`. This is an integration defect, not
evidence that those modules are invalid. The import-graph check identifies the
exact paths and should be the authoritative count as the tree changes.

The reviewed Lean surface in `MathUE`, `UniformEquilibrium`, `Research`, and
`Theorems` contains 1,363 files and approximately 528,643 lines. These are
maintenance measurements, not evidence of mathematical progress.

## Strengths

- The semantic waist, evidence seals (`M`, `L`, `A`, `C`), and repository lanes
  separate checked mathematics from experiments, research, and attribution.
- Generated status/frontier sources, local-link checks, warnings-as-errors,
  and the exhaustive axiom audit provide useful repeatable gates.
- The project intentionally avoids a compatibility-API promise and keeps
  generic mathematics in `MathUE` and game semantics in `UniformEquilibrium`.
- CI exercises documentation, trust, unit-test, and full-build gates; narrow
  module checks remain available for iteration.

## Findings

### Scanner and inventory

1. The trust scanner mishandled Lean prime-suffixed identifiers: a prime in
   `value'` could be read as the start of a character literal, hiding a later
   forbidden token. The scanner needs identifier-aware lexical handling plus
   regression tests for multiple primes, escapes, nested comments, and
   strings. A clean scan is not a substitute for those tests.
2. Sixteen UE modules are not umbrella-reachable: the 15-module closure rooted
   at `UniformEquilibrium.Quitting.Examples.BlockPair.All`, and
   `UniformEquilibrium.Quitting.Root.TerminalSemanticPrefixMetric`. The
   inventory must classify each as an intentional quarantine leaf, a missing
   import edge, or an ownership error; importing every file without reviewing
   that classification is not a fix.
3. `MathUE.LinearProgramming.SingletonLCP` crosses the generic boundary by
   importing game-semantic `GameTheory.Basic`. It must move behind an allowed
   generic interface or be reclassified; `MathUE` must not absorb that
   dependency accidentally.

### Dependency shape and ownership

4. Architecture and certificate layers depend on each other in places (for
   example, enforcement ledgers and compilers), and `Quitting` and
   `Diagnostics` also cross-import. These inversions make facades and local
   checks less effective and blur ownership of semantic interfaces.
5. The production umbrellas and several modules use broad imports.
   `UniformEquilibrium.lean` has 486 imports, including redundant direct
   `MathUE.*` imports after importing `MathUE`, and the diagnostics aggregator
   `CounterexampleRegimeAll.lean` has 255 imports and no declarations. Large
   files and internal declarations therefore behave like an implicit API,
   increasing rebuild and review cost. `lakefile.lean` also raises recursion
   and instance-synthesis limits globally; their necessity should be measured
   and ratcheted rather than expanded.
6. `Research` contains eleven one-import forwarding shims and promoted forks
   whose current owner or relationship to production is not apparent.
   `PhaseOccupationDuality`, `GraphDirectedPeriodicLift`,
   `WeightedSecurityWelfareAssembly`, and `DiscreteHazardStopping` retain
   bodies or descriptions superseded by production modules. Each needs a
   disposition: retain a genuine residual delta, replace with a canonical
   reader-facing alias, or remove it from the Research inventory.
7. The K11 implementation has a maintained entry point but lacks durable
   generator/source-data provenance. A future regeneration must be able to
   identify its inputs, transformations, generated leaves, and checker without
   relying on an informal working-tree memory. Transition provenance remains
   in [`TRANSITION.md`](../TRANSITION.md).
8. `scripts/sync_from_source.py` is historical reconstruction tooling that can
   remove production files absent from the old source snapshot. It must be
   frozen as staging-only tooling with a guard that rejects the live repository
   as a target; it must not become a synchronizer for current development.

### Proof engineering and duplication

9. Current tactic counts are heavily skewed toward explicit case and algebraic
   expansion: 2 `grind`, 659 `fin_cases`, approximately 4,163 `linarith`, 1,392
   `nlinarith`, 2,545 `ring`/`ring_nf`, and 2,111 `norm_num` occurrences. These
   are lexical occurrence counts, not theorem counts or quality scores, but
   they identify useful pilots for replacing brittle case trees with reusable
   lemmas or bounded automation.
10. Twelve handwritten fixed-arity PMF Fubini implementations, plus one local
    forwarding declaration, duplicate the same Fin3/Fin4 product-expectation
    proof instead of using a shared API. Two long proofs in
    `Quitting/Cycles/ConditionedDiffuseCompiler.lean` separately rebuild
    closely related signed-mass and bounded-expectation estimates. This
    multiplies maintenance and makes semantic mismatches harder to detect.
11. `MathUE/Probability/AnalyticOccupationFlow.lean` (913 lines),
    `UniformEquilibrium/SpecialCases/SingleController/NoTrap.lean` (398
    lines), and the conditioned-diffuse compiler family contain long,
    interleaved proof structures. Their decomposition should preserve exact
    declarations while exposing small algebraic and probabilistic interfaces.
12. Sixty Lean files exceed 1,000 lines and eleven exceed 2,000. The largest
    production files combine multiple conceptual layers, notably
    `MertensNeyman/AccountStrategy.lean` (4,382 lines) and `Fink/Limit.lean`
    (3,923 lines). Splits should follow theorem interfaces, not line quotas.

## Remediation record

- The lexical scanner now distinguishes prime-suffixed Lean identifiers from
  character literals, with regression tests covering the masking failure.
- A checked import-graph inventory now enforces production reachability and
  lane boundaries. The 16 production orphans are integrated, and the
  game-facing quitting-reward adapter has moved out of `MathUE`.
- Eleven declaration-free Research forwarding modules were removed. Their
  canonical owners are the imported production or experiment modules:
  `EndpointBackwardStability`, `EquivariantAveraging`,
  `LedgeredDissipativity`, `SignedTargetTransport`,
  `TerminalSemanticCausalQuitAggregation`, `CertifiedBoundaryPolyhedron`,
  `DirectionBarycenter`, `JoinMonotoneUniform`, the two terminal-semantic
  carrier modules, and `MathUE.Interval.PolynomialLipschitz`.
- Four promoted Research bodies were removed in favor of their maintained
  owners: `MathUE.Probability.PhaseOccupationDuality`,
  `MathUE.Topology.GraphDirectedPeriodicLift`, the production weighted-security
  assembly/bias pair, and the generic discrete-hazard stopping API and its
  checked consumers. No compatibility claim is made for the removed Research
  namespaces.
- The two surviving K11 numeric payloads now have a structured integrity
  manifest and deterministic checker. The exact migration source revision and
  adjacent source tree contain neither the named JSON input nor its emitter,
  so this is explicitly not a reproducible numerical generator or an
  independent source-data adapter.
- Historical reconstruction is now staging-only: its preflight rejects live,
  repository, overlapping, broad, and symlink targets, and `--dry-run` emits a
  deterministic operation manifest before any mutation.
- The public-response enforcement ledger is now a certificate interface; its
  diagnostic boundary witness remains with the public-response architecture,
  and generic adaptive payoff bounds live with `PotentialSystem`. There is no
  remaining `Certificates` to `Architectures` import.
- Reusable terminal exploitability, debt descent, equality-stratum, Nash-defect,
  and player-reindex interfaces now live below Diagnostics in the quitting
  hierarchy. The private-recommendation absorbing obstruction is classified as
  a diagnostic. Checked rules reject future `Quitting` to `Diagnostics` and
  `Certificates` to `Diagnostics` edges while permitting diagnostic consumers.
- A dependent finite-product expectation step now owns the PMF Fubini
  argument, with homogeneous Fin3 and Fin4 corollaries. All thirteen local
  declarations (twelve handwritten implementations and one forwarding alias)
  were removed; consumers now name the shared theorem directly.
- A game-independent finite-weight Jordan-decomposition interface now handles
  unequal-mass subprobability weights without manufacturing a cemetery atom.
  The two parallel conditioned-diffuse expectation arguments delegate to it.
  The one-sided singleton domination shows that only target collision mass
  contributes to reverse variation, strengthening the whole-law coefficient
  from `3 M s²` to `2 M s²` and the deleted-player coefficient from `3 M s²`
  to `(3/2) M s²`; the checked compiler constants are propagated downstream.
- The full-interval sure-set counterexample now records one finite witness
  table and one membership-toggle gap lemma. The general pure-set Nash
  characterization turns that lemma into the exclusion theorem, replacing
  seven repeated behavioral-deviation arguments. Fin3 subset enumeration is
  confined to `fin_cases` and decidable bookkeeping.
- The K11 terminal-table bridge is now stated for an arbitrary four-player
  hazard row. Four resource-bounded table computations share one explicit
  local normalization script, and the phase theorem is only an instantiation;
  combining all four computations in one declaration exceeded Lean's fixed
  heartbeat budget.
- The FTV three-phase rigidity proof now separates role-order deductions from
  real inequalities and solves both continuation vectors through one affine
  half-mixture lemma. A bounded `grind only [Function.update]` pilot replaces
  one definitional update split. Trials that required broad Fin/vector rule
  sets were rejected in favor of clearer `fin_cases`, `decide`, or `simp`.
- The analytic occupation-flow development now separates certificate encoding
  from normalization and the final alternative. Seven named lemmas expose
  stabilization, circulation decoding, branch incompatibility, converse
  normalization, and separator decoding; the former 378-line capstone is a
  20-line orchestration proof with the same public statement.
- The single-controller no-trap proof now delegates finite closed-region
  perturbation and zero-gap optimality to `MathUE`, and Vrieze LP
  decode/bump/re-encode work to a game-facing adapter. The original 398-line
  file is a 140-line graph-to-optimality argument with unchanged public
  declarations.
- The conditioned-diffuse compiler is split at its finite-law seam. The law
  module owns coalition measures, product-law comparison, conditioning, and
  forced-Continue estimates; the compiler owns strategic assembly. The split
  preserves the stronger constants established by the finite-weight API.
- The 4,382-line Mertens--Neyman account development is now a sequential
  Bellman, memory, Puiseux, and algebraic stack behind a thin reader-facing
  umbrella. The 3,923-line Fink limit development is similarly divided into
  core compactness, stationary compilers, corrected-target calculus, and
  indexed calendars; two generic summability tests moved to `MathUE`.
- The paired-singleton period-two stationary obstruction now bundles its four
  gain polynomials by player and proves one recentering equivariance theorem.
  A finite argmin replaces the hand-built coordinate-order tree, and the
  product-law calculation is stated once for an arbitrary player. Eight raw
  and normalized coordinate expansions were removed; the file now has 28
  private declarations rather than 35.

## Proof-quality and grind policy

- Every promoted theorem remains a kernel-checked Lean declaration under its
  stated imports. `sorry`, `admit`, explicit axioms, `native_decide`,
  `implemented_by`, unsafe/partial declarations, project-owned `set_option`,
  and weakened warning/linter settings are forbidden.
- `grind`, `fin_cases`, and other automation are acceptable for local routine
  work when they produce an ordinary checked term, have a bounded and
  reproducible command, and do not conceal a missing mathematical interface.
  Prefer a named lemma or shared API when a proof is repeated, huge, or
  sensitive to elaboration order.
- For a touched finite or propositional case tree longer than roughly ten
  lines, development must try `grind?` or replace the tree with a symmetry,
  finite table, or reusable lemma. Commit a constrained `grind only [...]`
  proof when it is stable and clearer. Keep `ring`, `norm_num`, `omega`,
  `linarith`, filters, and analytic tactics in their proper domains.
- Changed proof bodies over 80--100 lines receive decomposition review; bodies
  over 150 lines require an explicit reason not to extract named mathematical
  steps. These are review ratchets, not claims that short proofs are
  intrinsically better.
- Generated numerical or certificate data is evidence until a deterministic
  checker or kernel-checked consumer validates it. Tactic counts and line
  counts measure maintenance risk; they do not provide `M`, `L`, `A`, or `C`.
- A proof ratchet must preserve the exact statement and quantifiers. Never
  weaken a claim, widen imports, or add a trust escape hatch merely to reduce
  grind.

## GameTheory2 preparation and scope

The detailed compatibility census, semantic target, staged port, and acceptance
gates are recorded in [`GAMETHEORY2_MIGRATION_PLAN.md`](GAMETHEORY2_MIGRATION_PLAN.md).
The inspected successor is source-incompatible, has no quitting API, changes
PMF/history/profile semantics, and currently has no fetchable remote, so this
is not an import-path substitution. Cutover is explicitly deferred. No
parallel dependency, speculative port, or compatibility claim belongs in the
present roadmap; any reopening requires a separate decision and an updated
transition record.

## Conclusion

The project has strong proof-integrity and research-lane foundations, but its
large manually curated surface needs boundary, ownership, dependency, and
proof-maintenance ratchets. The companion roadmap sequences those controls as
preparatory phases and keeps mathematical closure separate from engineering
progress.
