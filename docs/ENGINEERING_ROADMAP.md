# Engineering roadmap

This is a preparatory engineering plan. It does not authorize a rewrite, a
stable API, or a GameTheory2 cutover. Exact theorem truth remains in Lean;
promotion and evidence rules remain in [`PIPELINE.md`](PIPELINE.md).

## Progress table

| Phase | Work | Status | Acceptance gate |
| --- | --- | --- | --- |
| 1 | Review baseline | Complete | Review facts and measured risks are recorded |
| 2 | Trust scanner | Complete | Prime-aware scanner and lexical regression suite pass |
| 3 | Import graph and inventory | Complete | Zero unexplained orphans and boundary violations |
| 4 | Ownership, Research, provenance, sync | Complete | Every shim/fork and sync decision has an owner and manifest |
| 5 | Facades and dependency inversions | Complete | Architecture/certificate and Quitting/Diagnostics edges are layered |
| 6 | Proof ratchets, product and variation APIs | Complete | Shared finite-weight identities replace selected duplication |
| 7 | Finite-case grind pilots | Complete | Pilot proofs reduce brittle expansion without weakening claims |
| 8 | Monolith decomposition | Complete | Long proof files split behind checked interfaces |
| 9 | Imports, internal APIs, options | Complete | Narrow imports and scoped options pass build and trust gates |
| 10 | Final audit | Complete | Current generated audit, full build, and repository gates pass |
| 11 | Assumption normalization | In progress | Known derivable hypotheses are internalized |

## Phase gates

### 1. Review baseline

Keep the completed 10,155-job full build and nonvacuous axiom audit as the
engineering baseline. Record the 911 UE modules, 1,375 trust-scanned Lean
files, 16 umbrella orphans, and proof-tactic counts (2 `grind`, 659
`fin_cases`). The gate is documentation review, not a theorem claim.

### 2. Trust scanner

Make lexical handling aware of prime-suffixed identifiers. Add tests for
forbidden tokens after one or more primes, character escapes, strings, and
nested comments. Acceptance is the unit suite plus `python scripts/check_trust.py`
passing over the complete project, with no change to the forbidden-token or
warnings-as-errors policy.

### 3. Import graph and inventory

Run the import-graph checker across all umbrellas with
`python3 -m unittest scripts/test_check_import_graph.py` followed by
`python3 scripts/check_import_graph.py`. Classify the 16
non-reachable UE modules, the `SingletonLCP` generic-boundary violation, and
any production-to-Research/Experiments edges. Acceptance is a checked,
repeatable inventory with zero unexplained diagnostics; no module moves solely
to improve a count.

### 4. Ownership, Research, provenance, and sync

Audit stale Research shims and promoted forks. Give each a retain, replace,
promote, or quarantine disposition. Add a durable K11 generated-data record;
if its original source or producer is absent, preserve that limitation and
check only what can be reproduced. Freeze `sync_from_source.py` as historical
staging-only tooling and add a guard that rejects the live repository as a
target; do not adapt it into a current-tree synchronizer. Acceptance is a
reproducible integrity check with an explicit non-regeneration boundary and an
owner for every exception; historical transition facts stay in
[`TRANSITION.md`](../TRANSITION.md).

### 5. Facades and dependency inversions

Design narrow semantic facades to break the Architecture/Certificate and
Quitting/Diagnostics inversions. Acceptance is an import graph with the
intended direction, no cyclic layer dependency, and unchanged checked
consumers. Do not duplicate GameTheory foundations or silently broaden the
strategy class.

### 6. Proof ratchets, finite products, and finite-weight variation

Introduce a generic finite-product PMF Fubini step and use it to remove local
fixed-arity proofs. Extract the finite-weight Jordan-decomposition estimate
behind the conditioned-diffuse compiler; preserve its subprobability semantics
instead of forcing it through probability total variation. Specify ratchets
for proof size, repeated algebra, and exact quantifiers. Acceptance is a
kernel-checked pilot, trust-clean source, a documented consumer for each new
interface, and checked downstream constants for any strengthened estimate.

### 7. Finite-case grind pilots

Select representative `fin_cases`-heavy proofs and compare named lemmas,
bounded `grind`, and existing automation. Keep only improvements that are
reproducible and reviewable. Acceptance requires no forbidden escape hatch,
no weakened statement, and recorded before/after proof-maintenance evidence;
tactic counts alone are not success criteria.

### 8. Monolith decomposition

Prepare seams for `AnalyticOccupationFlow`, `NoTrap`, the conditioned-diffuse
compiler family, `AccountStrategy`, and the Fink limit stack. Split by
mathematical interface, not arbitrary line count, and preserve declaration
ownership and downstream imports. Replace the period-two stationary
coordinate tree by a player-indexed symmetry argument. Acceptance is narrow
compilation of each new module, full consumer compilation, and no new broad
import.

### 9. Imports, internal APIs, and options

Reduce broad umbrella imports, expose intentional internal facades, and audit
the centralized Lean options in `lakefile.lean`. Acceptance is a full build,
trust scan, and import-graph check with warnings-as-errors preserved and no
project-owned global weakening.

### 10. Final audit

The scoped-option build completed all 10,160 jobs before the ownership cleanup.
After that cleanup, the current generated audit and normal-root build completed
all 10,147 jobs. `AxiomAudit` checked 43,241 project declarations and reported
only the permitted `propext`, `Quot.sound`, and `Classical.choice` library
axioms. The exact cross-lane duplicate ratchet, trust scan, import graph,
documentation checks, unit suite, generated-data checker, and build-artifact
check form the closing gate. No unexplained production orphan, lane-boundary
violation, or exact Research-to-production proof-body fork remains.

### 11. Assumption normalization

Remove hypotheses that finite source data can supply canonically, beginning
with coordinate bounds on finite quitting reward tables. The parser-audited
phase-entry measurement is 689 definitions and theorems in 175 files: 521
with a dischargeable reward-bound triple and 168 retaining genuine coupling.
Of the latter, 152 mention the chosen constant in the result and 16 use it in
a later hypothesis. Classification inspects the entire retained telescope,
rather than only the final result; the simpler result-only criterion would
misclassify those 16 declarations.

The first stable normalization slice removes 192 of the 521 dischargeable
triples and leaves 329 across 95 files. The complete set of 168 coupled
quantitative declarations is unchanged. This is progress toward the phase
gate, not completion of it.

A follow-up telescope audit internalizes four qualitative or independently
bounded cases that the initial classifier conservatively retained. The live
census is therefore 493 declarations: 329 removable and 164 genuinely
coupled. That refinement also removes two derivable nonnegativity hypotheses
and a punishment-bound hypothesis that had become dead through five local
wrappers.

The census recognizes the narrow `M`/`B`/`C` coordinate-bound schema in Lean
definitions, theorems, lemmas, abbreviations, and opaque declarations. It
handles grouped Unicode binders, strict implicits, equation declarations,
identifier primes, nested comments, and colons inside result binders. It is
not a Lean parser and does not inventory structure fields. The separately
audited `PositiveMinimumPlateau.reward_bound` field remains intentional: the
same positive constant controls reward coordinates and explicit mass-floor
denominators throughout that quantitative certificate.

Keep arbitrary bounds in quantitative conclusions and wherever later data are
bounded by the same constant. The canonical bound is the finite sum of
absolute reward coordinates: besides bounding each coordinate, it controls
row and subtable totals without extra cardinality factors. For qualitative
declarations, construct that bound internally and propagate the stronger API
through all callers. Process dependency layers bottom-up and use Lean
elaboration as the call-site oracle, because field notation, namespace
shortening, rewriting, direct canonical proof arguments, and partial
applications make textual call graphs incomplete.

Acceptance requires a deterministic census, zero remaining declarations in
the audited removable schema, explicit classification of retained quantitative
parameters, narrow checks for each layer, and a final exhaustive axiom audit
and build. Use `python3 scripts/check_reward_bounds.py` for the inventory and
its opt-in `--check` mode for the zero-candidate closing gate. The same audit
then expands to other recurring hypotheses that are
canonically derivable from retained finite data; no claim of globally minimal
logical hypotheses is inferred merely from the absence of compiler warnings.

## Deferred dependency decision

GameTheory2 preparation is limited to the census, semantic waist, and staged
gates in [`GAMETHEORY2_MIGRATION_PLAN.md`](GAMETHEORY2_MIGRATION_PLAN.md). The
cutover itself is deferred: no parallel dependency or speculative port is part
of these phases. A future cutover requires a published successor pin, separate
decision, acceptance build, and updated transition record.
