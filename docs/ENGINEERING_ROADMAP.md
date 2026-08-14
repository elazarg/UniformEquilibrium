# Engineering roadmap

This is a preparatory ten-phase plan. It does not authorize a rewrite, a
stable API, or a GameTheory2 cutover. Exact theorem truth remains in Lean;
promotion and evidence rules remain in [`PIPELINE.md`](PIPELINE.md).

## Progress table

| Phase | Work | Status | Acceptance gate |
| --- | --- | --- | --- |
| 1 | Review baseline | Complete | Review facts and measured risks are recorded |
| 2 | Trust scanner | Complete | Prime-aware scanner and lexical regression suite pass |
| 3 | Import graph and inventory | Complete | Zero unexplained orphans and boundary violations |
| 4 | Ownership, Research, provenance, sync | Complete | Every shim/fork and sync decision has an owner and manifest |
| 5 | Facades and dependency inversions | In progress | Architecture/certificate and Quitting/Diagnostics edges are layered |
| 6 | Proof ratchets and Fubini API | Queued | Shared PMF identities replace selected duplication |
| 7 | Finite-case grind pilots | Queued | Pilot proofs reduce brittle expansion without weakening claims |
| 8 | Monolith decomposition | Queued | Long proof files split behind checked interfaces |
| 9 | Imports, internal APIs, options | Queued | Narrow imports and scoped options pass build and trust gates |
| 10 | Final audit | Pending prior phases | All audits, full build, and documentation checks are green |

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

### 6. Proof ratchets and Fubini API

Introduce shared fixed-arity PMF Fubini lemmas and use them in a small pilot.
Specify ratchets for proof size, repeated algebra, and exact quantifiers;
include conditioned-diffuse duplication in the inventory. Acceptance is a
kernel-checked pilot, trust-clean source, and a documented consumer for each
new interface.

### 7. Finite-case grind pilots

Select representative `fin_cases`-heavy proofs and compare named lemmas,
bounded `grind`, and existing automation. Keep only improvements that are
reproducible and reviewable. Acceptance requires no forbidden escape hatch,
no weakened statement, and recorded before/after proof-maintenance evidence;
tactic counts alone are not success criteria.

### 8. Monolith decomposition

Prepare seams for `AnalyticOccupationFlow`, `NoTrap`, and the conditioned-
diffuse compiler family. Split by mathematical interface, not arbitrary line
count, and preserve declaration ownership and downstream imports. Acceptance
is narrow compilation of each new module, full consumer compilation, and no
new broad import.

### 9. Imports, internal APIs, and options

Reduce broad umbrella imports, expose intentional internal facades, and audit
the centralized Lean options in `lakefile.lean`. Acceptance is a full build,
trust scan, and import-graph check with warnings-as-errors preserved and no
project-owned global weakening.

### 10. Final audit

Run the complete documentation gate, trust tests and scan, import-graph
inventory, generated axiom audit, and full `lake build`. Recheck every
Research/sync/provenance exception and record measurable build output. The
phase closes only with no unexplained orphan or boundary violation and with
the review documents refreshed.

## Deferred dependency decision

GameTheory2 preparation is limited to the interface inventory and compatibility
harness described above. The cutover itself is deferred: no parallel
dependency, speculative port, or migration schedule is part of these phases.
A future cutover requires a separate decision, acceptance build, and updated
transition record.
