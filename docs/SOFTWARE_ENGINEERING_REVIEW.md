# Software-engineering review

This is the living software-engineering assessment of the current tree. It
describes present strengths, risks, and review standards; it is not a record of
the sequence by which the tree acquired them. Ordinary implementation history
belongs in Git; scoped historical evidence remains with its owning record.

Exact theorem truth remains in the Lean declarations under their imports. This
review does not turn a proposition, conditional theorem, Research module, or
generated computation into an unconditional mathematical result.

## Overall assessment

The repository has unusually strong trust and evidence boundaries for an
active Lean research project. Its main engineering risk is the scale and
density of the quitting development. Large
semantic APIs, deeply dependent proof terms, and many specialized consumers
make apparently local improvements propagate widely. The right response is a
small number of stable mathematical interfaces, not more compatibility layers
or broader automation.

The project should continue to optimize for research audit and theorem
development rather than a frozen downstream API. Public names still need clear
ownership, but source compatibility is subordinate to honest mathematical
structure and maintainable proofs.

## Structure and ownership

### Strengths

- `MathUE`, `UniformEquilibrium`, `Research`, `Experiments`, `Theorems`, and
  `Literature` have distinct stated purposes.
- The semantic contract and evidence seals separate checked mathematics from
  adapters, consumers, experiments, and open propositions.
- Lean umbrellas, the exhaustive axiom audit, generated status sources, and
  documentation checks provide machine-checkable inventories.
- Reader-facing `Theorems` modules are thin restatements over declarations
  owned by the mathematical development.
- Cross-lane exact proof-body duplication is rejected mechanically.

### Required boundaries

- `MathUE` may use Mathlib and generic GameTheory mathematics, but it must not
  own game-semantic declarations or import semantic `GameTheory.*` modules.
- Quitting-specific semantics belong below `UniformEquilibrium.Quitting`, not
  in generic probability or optimization modules.
- Production code must not depend on `Research`, `Experiments`, or diagnostic
  examples.
- High-fan-in semantics must not be owned by `Diagnostics`; move the interface
  to a neutral quitting owner and keep the diagnostic as a consumer.
- A forwarding file needs a real compatibility or reader-facing purpose.
  Otherwise it should not exist merely to preserve a former module path.

### Residual structural risks

Several files still span multiple mathematical layers or carry substantial
proof-maintenance cost. Representative review targets include:

- `UniformEquilibrium/SpecialCases/ZeroSum/MertensNeyman/Account.lean`;
- `UniformEquilibrium/SpecialCases/SingleController/Basic.lean`;
- `UniformEquilibrium/Quitting/AbsorptionPath/MarkedAbsorptionCylinder.lean`;
- `UniformEquilibrium/Architectures/PublicResponse/CredibilityCriterion.lean`;
- `UniformEquilibrium/Examples/BigMatch/Uniform.lean`;
- `MathUE/NormalizedFarkasBasis.lean`;
- `MathUE/BoundedDiscrepancyCirculation.lean`; and
- `Experiments/certsearch/block_pair/K11/JacobianCache.lean`.

Line count alone does not justify a split. A split is warranted when a file
combines separable concepts, forces unrelated consumers through a broad import,
or hides reusable mathematics inside a capstone proof.

The highest-value declaration-level decomposition targets are more specific:

- the direction-barycenter estimate should separate finite product-law
  partition bounds, singleton-event approximation, and stationary-value
  decoding;
- finite analytic branch coverage should separate formal-root branch
  construction, eventual branch separation, and sequence coverage;
- exact and approximate punishment-completed cycles should share one suffix
  selection and punishment-stitching engine, with exact root Nash exposed as a
  specialization rather than a parallel long compiler; and
- stopping-law tangent extraction should separate best-response selection,
  compact subsequence extraction, and the diagonal, inactive-coordinate, and
  total-debt constraints on the limiting tangent packet.

These are interface problems, not requests to compress the existing proofs in
place. A successful refactor leaves the public capstone as the composition of
the named mathematical seams.

Inventory-only diagnostic facades remain useful as navigation roots, but
ordinary modules should not import them. Narrow hierarchical facades are
preferable to manually curated mega-umbrellas.

## Lean design and mathematical APIs

### Designs to preserve

- `MathUE.PMFProduct.FiniteFubini` owns finite-product expectation
  decomposition; consumers should not recreate Fin3 or Fin4 expansions.
- `MathUE.Probability.FiniteWeightVariation` owns the signed finite-weight
  comparison used by conditioned-diffuse arguments. Its unequal-mass,
  subprobability formulation is the relevant abstraction.
- The analytic occupation-flow capstone delegates certificate representation,
  normalization, incompatibility, and decoding to named lemmas.
- The single-controller no-trap result separates generic closed-region LP
  perturbation from the game-facing Vrieze adapter.
- The conditioned-diffuse development separates finite-law comparison from
  strategic compilation.
- The Fink-limit and Mertens--Neyman account developments expose sequential
  conceptual modules behind narrow umbrellas.
- K11 has one compositional conditional compiler owner. Its per-player
  endpoint and immediate table leaves are explicit resource-bounded
  computations, not parallel compiler APIs.

### API smells requiring review

- Four or more isomorphic local helper theorems usually indicate a missing
  indexed theorem, equivariance statement, or finite table abstraction.
- A declaration with a proof body longer than one conceptual argument should
  expose named seams before its public capstone.
- A long simp list of domain definitions often signals that the semantic API
  is too low-level.
- A theorem parameter used only to construct another hypothesis should be
  tested for internal derivability from retained finite data.
- A touched theorem should be checked in both directions: minimize its
  assumptions and expose the strongest stable conclusion its proof already
  establishes. Flag wider strengthening opportunities when they cannot be
  taken without redesigning the surrounding API.
- Proof arguments embedded in constructed roots or profiles are still API
  parameters even when proof irrelevance makes their values mathematically
  immaterial. Normalize them to a canonical proof when a stronger retained
  hypothesis supplies one.
- Generic analytic lemmas should not be exported through broad game
  namespaces merely because their first consumer is a game proof.

The assumption rules and deterministic censuses are specified in
[`ENGINEERING_ROADMAP.md`](ENGINEERING_ROADMAP.md). In particular, arbitrary
quantitative bounds remain when they control a result or later datum; only
derivable companion hypotheses are removed.

## Low-level proof implementation

The goal is a short mathematical proof over an adequate interface, not a low
tactic count. Use automation according to the residue it solves:

- bounded `grind only` for finite propositional reasoning, membership,
  `Function.update`, and small extensionality obligations;
- `ring` and `ring_nf` for polynomial identities;
- `linarith` and `nlinarith` for ordered-ring consequences;
- `norm_num` and `omega` for concrete arithmetic; and
- named filter, compactness, integration, or topology lemmas for analytic
  arguments.

For a touched finite case tree of nontrivial size, try one of three designs:

1. an indexed theorem over the player or role;
2. transport under an actual symmetry or equivalence; or
3. a finite witness table plus one generic gap theorem.

Use `grind?` as an exploration tool, then keep only a constrained and readable
result. A large generated rule set or broad semantic unfolding is usually
worse than `fin_cases`, `decide`, or a named lemma.

Review changed proof bodies around 80--100 lines for decomposition. A body over
150 lines needs an explicit mathematical reason to remain whole. These are
review triggers, not hard measures of theorem quality.

Proof golfing is successful when it reveals the true lemma boundary, deletes
duplicated semantic setup, or makes a capstone read like its paper proof. It is
not successful when it merely compresses a brittle expansion.

## Trust and reproducibility

- Project source forbids `sorry`, `admit`, explicit axioms, `native_decide`,
  `implemented_by`, unsafe declarations, partial definitions, project-owned
  `set_option`, and warning-policy weakening.
- `AxiomAudit.lean` is exhaustive over project-owned modules and permits only
  `propext`, `Quot.sound`, and `Classical.choice` from the library stack.
- The lexical trust scan has regression coverage for Lean prime identifiers,
  comments, strings, and character literals. It supplements kernel checking;
  it does not replace it.
- K11 numeric payloads have deterministic integrity checks. Their missing
  original generator/input boundary is stated in
  `Experiments/certsearch/block_pair/K11/MANIFEST.md`; integrity verification is
  not independent numerical regeneration.
- Generated data should be excluded from proof-golf metrics while remaining
  subject to provenance and freshness checks.
- `scripts/sync_from_source.py` is staging-only and must reject the live tree,
  repository targets, overlapping roots, and unsafe links.

## Current review gates

The minimum repository-wide review surface is:

```text
python3 scripts/check_docs.py
python3 -m unittest discover -s scripts -p 'test_*.py'
python3 scripts/check_import_graph.py
python3 scripts/check_proof_duplicates.py
python3 scripts/check_reward_bounds.py --check --max-nonnegative 0
python3 scripts/check_redundant_order_hypotheses.py --check
python3 scripts/check_derivable_telescope_hypotheses.py --check
python3 scripts/check_trust.py
```

Run focused Lean checks for every changed owner and representative consumer.
Run a full `lake build` when changes affect module inventory, umbrellas,
toolchain or Lake configuration, dependency pins, or a broad semantic API.
Report focused and exhaustive evidence separately.

## GameTheory integration

GameTheory's `Stochastic.Game`, `FinDist`, Protocol histories,
initial-state-indexed behavior profiles, and native uniform-payoff predicate
form the semantic foundation. `UniformEquilibrium/ProofView/Native/` proves the
history, finite-law, finite-average-payoff, unilateral-update, and
uniform-payoff correspondences used by the indexed PMF proof view. Quitting
semantics are project-owned above that boundary, and Fink consumers use the
integrated stochastic interfaces.

The ownership and validation rules are in
[`GAMETHEORY_INTEGRATION.md`](GAMETHEORY_INTEGRATION.md). The main engineering
risk is accidental duplication or bypass of that boundary, especially through
private finite-distribution representations.

## Review conclusion

The current engineering direction is sound: maintain strict trust and lane
boundaries, remove derivable assumptions, consolidate semantic owners, and
replace long proof scripts with mathematical interfaces. Remaining risk is
concentrated in large multi-concept files, instance-heavy quitting APIs,
non-regenerable numeric source data, and changes that bypass the proved native
semantic boundary. None of these risks is evidence for or against the
mathematical uniform-equilibrium conjecture.
