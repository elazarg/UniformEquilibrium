# Software-engineering review

This is the durable engineering review of the current tree. It records
software structure and proof-production risks, not theorem status or a stable
downstream API. Extraction and repository-transition facts are recorded only
in [`TRANSITION.md`](../TRANSITION.md).

## Baseline and current census

### Historical reconstruction baseline

The reconstruction baseline completed a full `lake build` with 10,155 jobs and
ran a nonvacuous `AxiomAudit` over the project-owned declarations. At review
start, the inventory had 911 `UniformEquilibrium` Lean modules and 1,375
project-owned Lean files scanned by the trust checker. These are historical
review-start measurements, not the current post-cleanup census. The production
boundary is the pinned `GameTheory` submodule.

The pre-cleanup normal-root build subsequently completed all 10,160 jobs and
reported an `AxiomAudit` pass for 43,570 declarations, with only `propext`,
`Quot.sound`, and `Classical.choice` permitted. A successful scoped-option
build also completed all 10,160 jobs with `synthInstance.maxSize = 1024`
scoped to the `UniformEquilibrium` library. After the Phase10 ownership cleanup,
the current normal-root build completed all 10,147 jobs; its generated
`AxiomAudit` checked 43,241 declarations with the same three permitted library
axioms.

The review initially found 16 `UniformEquilibrium` modules that were not
reachable from `UniformEquilibrium.lean`. This is an integration defect, not
evidence that those modules are invalid. The import-graph check identifies the
exact paths and should be the authoritative count as the tree changes.

### Current post-cleanup census

Measured after the Phase10 ownership cleanup, the reviewed Lean surface in
`MathUE`, `UniformEquilibrium`, `Research`, and `Theorems` contains 1,355 files
and 522,217 lines. The trust checker and import-graph checker each currently
report 1,367 project-owned/local modules. The direct dependency census is 56
modules; the new edge is the game-facing `GameTheory.Basic` import of
`QuittingRewardAdapter`, recorded in
[`GAMETHEORY2_MIGRATION_PLAN.md`](GAMETHEORY2_MIGRATION_PLAN.md). There are 61
files over 1,000 lines and 8 over 2,000 lines. These are maintenance
measurements, not evidence of mathematical progress.

## Strengths

- The semantic waist, evidence seals (`M`, `L`, `A`, `C`), and repository lanes
  separate checked mathematics from experiments, research, and attribution.
- Generated status/frontier sources, local-link checks, warnings-as-errors,
  and the exhaustive axiom audit provide useful repeatable gates.
- The project intentionally avoids a compatibility-API promise and keeps
  generic mathematics in `MathUE` and game semantics in `UniformEquilibrium`.
- CI exercises documentation, trust, unit-test, and full-build gates; narrow
  module checks remain available for iteration.

## Review-start findings

### Scanner and inventory

1. The trust scanner mishandled Lean prime-suffixed identifiers: a prime in
   `value'` could be read as the start of a character literal, hiding a later
   forbidden token. The scanner needs identifier-aware lexical handling plus
   regression tests for multiple primes, escapes, nested comments, and
   strings. A clean scan is not a substitute for those tests.
2. Sixteen UE modules were not umbrella-reachable: the 15-module closure rooted
   at `UniformEquilibrium.Quitting.Examples.BlockPair.All`, and
   `UniformEquilibrium.Quitting.Root.TerminalSemanticPrefixMetric`. The
   inventory must classify each as an intentional quarantine leaf, a missing
   import edge, or an ownership error; importing every file without reviewing
   that classification is not a fix.
3. Historical review snapshots identified a `MathUE`/`GameTheory.Basic`
   boundary crossing. The current owner is the game-facing
   `QuittingRewardAdapter`, and the adapter is no longer in `MathUE`; the
   remaining direct edge is recorded in the current migration census. Future
   changes must not move that semantic dependency back into generic `MathUE`.

### Dependency shape and ownership

4. Architecture and certificate layers depended on each other in places (for
   example, enforcement ledgers and compilers), and `Quitting` and
   `Diagnostics` also cross-imported. These inversions made facades and local
   checks less effective and blur ownership of semantic interfaces.
5. The production umbrellas and several modules used broad imports.
   `UniformEquilibrium.lean` had 486 imports, including redundant direct
   `MathUE.*` imports after importing `MathUE`, and the diagnostics aggregator
   `CounterexampleRegimeAll.lean` had 255 imports and no declarations. Large
   files and internal declarations therefore behaved like an implicit API,
   increasing rebuild and review cost. `lakefile.lean` also raised recursion
   and instance-synthesis limits globally; their necessity should be measured
   and ratcheted rather than expanded.
6. `Research` contained eleven one-import forwarding shims and promoted forks
   whose current owner or relationship to production is not apparent.
   `PhaseOccupationDuality`, `GraphDirectedPeriodicLift`,
   `WeightedSecurityWelfareAssembly`, and `DiscreteHazardStopping` retain
   bodies or descriptions superseded by production modules. Each needs a
   disposition: retain a genuine residual delta, replace with a canonical
   reader-facing alias, or remove it from the Research inventory.
7. The K11 implementation had a maintained entry point but no durable
   generator/source-data provenance. A future regeneration must be able to
   identify its inputs, transformations, generated leaves, and checker without
   relying on an informal working-tree memory. Transition provenance remains
   in [`TRANSITION.md`](../TRANSITION.md).
8. `scripts/sync_from_source.py` was historical reconstruction tooling that
   could remove production files absent from the old source snapshot. It must be
   frozen as staging-only tooling with a guard that rejects the live repository
   as a target; it must not become a synchronizer for current development.

### Proof engineering and duplication

9. Review-start tactic counts were heavily skewed toward explicit case and
   algebraic expansion: 2 `grind`, 659 `fin_cases`, approximately 4,163
   `linarith`, 1,392 `nlinarith`, 2,545 `ring`/`ring_nf`, and 2,111 `norm_num`
   occurrences. The final reviewed counts are 3, 599, 4,081, 1,362, 2,484,
   and 2,078, respectively. These are lexical occurrence counts, not theorem
   counts or quality scores; they identify useful pilots rather than tactic
   quotas.
10. Twelve handwritten fixed-arity PMF Fubini implementations, plus one local
    forwarding declaration, duplicated the same Fin3/Fin4 product-expectation
    proof instead of using a shared API. Two long proofs in
    `Quitting/Cycles/ConditionedDiffuseCompiler.lean` separately rebuilt
    closely related signed-mass and bounded-expectation estimates. This
    multiplied maintenance and made semantic mismatches harder to detect.
11. `MathUE/Probability/AnalyticOccupationFlow.lean` (913 lines),
    `UniformEquilibrium/SpecialCases/SingleController/NoTrap.lean` (398
    lines), and the conditioned-diffuse compiler family contained long,
    interleaved proof structures. Their decomposition should preserve exact
    declarations while exposing small algebraic and probabilistic interfaces.
12. The historical census counted sixty Lean files over 1,000 lines and eleven
    over 2,000. The current post-cleanup census counts 61 over 1,000 and 8 over
    2,000. The largest historical production files combined multiple
    conceptual layers, notably
    `MertensNeyman/AccountStrategy.lean` (4,382 lines) and `Fink/Limit.lean`
    (3,923 lines). Splits should follow theorem interfaces, not line quotas.

### Current large-file residuals

The post-cleanup census leaves eight files over 2,000 lines:

- maintained production monoliths: `MertensNeyman/Account.lean` (2,586),
  `SingleController/Basic.lean` (2,290),
  `Quitting/AbsorptionPath/MarkedAbsorptionCylinder.lean` (2,056),
  `Architectures/PublicResponse/CredibilityCriterion.lean` (2,045), and
  `Examples/BigMatch/Uniform.lean` (2,031);
- generic mathematics: `MathUE/NormalizedFarkasBasis.lean` (2,080) and
  `MathUE/BoundedDiscrepancyCirculation.lean` (2,041); and
- Research numeric infrastructure: `Research/Quitting/BlockPair/K11/JacobianCache.lean`
  (2,167), whose payload/provenance remains a maintenance risk.

The 61 files over 1,000 lines remain a proof-maintenance and rebuild-cost risk.
The Phase10 cleanup removed stale owners and exact cross-lane body copies, but
it did not claim these remaining files are decomposed, that K11 data is
regenerable, or that broad semantic dependencies have disappeared.

The final semantic-duplication audit found no remaining P0/P1 ownership fork.
One consumerless P2 analogue remains in
`Research/General/MaxAffineHolonomySemigroup.lean`: it uses `NNReal`
coefficients rather than the production `QuittingMaxAffineSummary`, so it is
not an exact copy, but a later cleanup should either delete it or provide an
explicit conversion. Static/dynamic debt-edge and anchored/unanchored packet
pairs likewise retain distinct typed semantic statements; their common
algebra may merit future extraction, but they are not competing owners.

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
- Phase10 canonical ownership cleanup removed the stale Research audit shims,
  duplicate stationary/cycle owners, and Research copies whose maintained
  declarations now live in production or `MathUE`. Surviving Research
  consumers import those canonical owners; this is an ownership cleanup, not a
  claim that the underlying mathematics is newly proved.
- The exact cross-lane duplicate ratchet is now enforced by
  `scripts/check_proof_duplicates.py` and eleven regression tests. It rejects
  normalized Research proof bodies of at least 250 characters that exactly
  copy a `MathUE` or `UniformEquilibrium` body; the current check passes. This
  is intentionally narrower than semantic-equivalence detection.
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
  owned by one `MathUE` classification theorem and uses `fin_cases` with
  decidable bookkeeping. Two distinct sure-exit regressions also share one
  semantic strict-toggle obstruction.
- The K11 conditional compiler now has one compositional owner ending at
  `ConditionalPackage`; the weaker 572-line parallel compiler and its duplicate
  active-equation adapter were removed. Eight per-player endpoint/immediate
  table leaves remain separate because combining each four-branch computation
  exhausts the fixed declaration heartbeat budget; they are explicit,
  same-owner resource leaves rather than competing compiler APIs.
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
- Generic one-sided finite-sum, finite-product, and squeeze limits now live in
  `MathUE.Topology.FiniteLimitDecomposition`. Both analytic packet families
  delegate their excluded-product, bounded-remainder, and endpoint-mixture
  limits to that interface. Charged and signed projective lassos likewise use
  one checked value-correction theorem instead of parallel compiler bodies.
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
- The production umbrella now delegates generic inventory entirely to its
  leading `import MathUE`; 56 redundant direct `MathUE.*` imports were removed.
  The three Research users of `CounterexampleRegimeAll` now import only their
  actual declarations. The inventory facade retains all 255 diagnostic imports
  but is only 274 lines rather than 1,039, with its mathematical narrative
  owned by `docs/design/COUNTEREXAMPLE_SEARCH_REGIME.md`.
- Twelve CurveSelection implementation namespaces, containing 275
  declarations, now live under `Math.CurveSelection.Internal` rather than
  public-looking `*Scratch` names. All internal consumers and the one Research
  consumer were updated without compatibility aliases. The architecture check
  rejects new MathUE `*Scratch` namespaces, redundant root MathUE imports, and
  ordinary consumers of inventory-only facades.
- A fresh build with Lean's resource defaults completed 10,156 of 10,160 jobs
  and isolated one failure in `MetrizableMarkedAbsorptionPath`. Neither the
  historical recursion-depth increase nor the pending-synthesis-depth increase
  fixes it; both were removed. Lean 4.32.2 defaults these limits to 512 and 1,
  respectively, and defaults `synthInstance.maxSize` to 128. Only the latter is
  relevant: 698 fails and 699 passes in the direct source check. The retained
  value is 1,024, half the historical setting, and is scoped to the
  `UniformEquilibrium` library rather than all seven project libraries.

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

The ten remediation phases installed checked boundary, inventory, ownership,
provenance, duplication, and proof-maintenance ratchets while preserving the
project's theorem statements and trust policy. The current tree passes a full
10,147-job build and a nonvacuous audit of 43,241 declarations. This is an
engineering result, not a claim that the uniform-equilibrium conjectures have
been solved or that every proof has reached its final mathematical form.

Residual maintenance risk is concentrated in the 61 files over 1,000 lines,
the eight files over 2,000 lines, the non-regenerable K11 numeric payload, and
a few explicitly classified typed semantic analogues. GameTheory2 remains a
separate, source-incompatible cutover blocked on a reproducible remote and the
semantic adapter work recorded in the migration plan.
