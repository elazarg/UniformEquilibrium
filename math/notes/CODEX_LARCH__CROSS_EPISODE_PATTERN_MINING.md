# Cross-episode code-pattern mining: pilot and selection method

Author: CODEX_LARCH. Bounded static research audit, 2026-09-07.

## Question and decision

Can code patterns reveal implicit mathematical theories without rereading
the full development or repeating the proof engineer's local mining?

The user's constraint is central: closely timed changes were already visible
to the proof engineer and the immediate proof-mining pass. Such changes are
poor primary candidates. Search for connections across separate mathematical
development episodes and weakly connected interfaces instead.

The bounded pilot found no new theory. Two apparently strong cross-date
proof-pattern matches failed mathematical review: their relationships were
already explicit. This is useful evidence about the search method, not
evidence that the codebase contains no implicit theories.

No Lean source was changed or compiled. This note records a static audit and
a proposed discovery method, not an experiment establishing mathematical
claims or an exhaustive novelty search.

## 1. What the cheap pilot actually tested

Starting from history through `33552e5`, with other concurrent worktree edits
present, the pilot used the existing declaration-scanning utilities from
`scripts/check_proof_duplicates.py` and `scripts/check_trust.py`.

It scanned theorem bodies in `MathUE`, `UniformEquilibrium`, and `Research`.
Comments and strings were removed; lexical identifiers were replaced by a
placeholder while tactic names, mathematical punctuation, selected operators,
and numeric constants were retained. These fingerprints are deliberately
coarse and are NOT Lean alpha-equivalence or semantic equivalence.

Two retrieval methods were tried:

1. Whole-body fingerprint equality, retaining substantial proofs in different
   path branches with file-introduction dates at least three days apart.
2. Shared 60-token subproof windows, sampled every ten tokens, retaining
   pairs with at least two matching windows, different path branches, and
   file-introduction dates at least four days apart. Very common fragments
   were dropped as boilerplate.

The first method mostly surfaced generic finite-sum and expectation helpers.
The second exposed the two leads below, plus known compact-prefix
generalizations and other likely helper duplication. Raw scratch outputs
were used only to rank source inspections, not as theorem evidence. The
parameters were pilot choices, not calibrated measures of novelty.

File introduction date was the cheapest initial metadata, but the review
showed why it is insufficient: it can be a migration date, and two distant
files may lie in one direct mathematical dependency chain.

## 2. Rejected lead: collision mass versus small-hazard expansion

The strongest generic-math match connected:

- `collisionMass_eq_one_sub_continueMass_sub_singletonMass`
  (`MathUE/PMFProduct/CollisionMass.lean`);
- `smallHazardExpectation_sub_tail_sub_linearization_eq`
  (`MathUE/PMFProduct/SmallHazardExpectation.lean`).

CODEX_LARCH_GEOMETRY independently inspected the source relationship and
nearby theory. The common argument is the weighted partition of nonempty
coalitions into singletons and coalitions of cardinality at least two.
The repeated blocks establish disjointness, coverage, and sum reindexing.

The dependency is already explicit: `SmallHazardExpectation` imports
`SmallHazardBounds`, which imports `CollisionMass`. The expectation remainder
uses the collision estimates. A broader Boolean interaction expansion is
also already represented by `quittingRootExpectedPayoff_eq_continuation_add_multilinearValue`
in `UniformEquilibrium/Quitting/Bellman/Finite/BooleanMobiusAdapter.lean` and associated
research notes. The bounded review also found prior recognition in
`MERIDIAN_BLINDSPOTS.md` and the hidden-reset value-of-information notebook.

Verdict: a common weighted-partition helper could remove repetition, but no
missing mathematical theory or new UE consumer was identified. The source
relationship overrules the apparently favorable time separation.

## 3. Rejected lead: solo-floor completion versus no-harm generation

The strongest game-semantic match connected:

- `isUniformEquilibriumPayoff_soloReward_of_soloFloor_of_punishmentIR`
  (`UniformEquilibrium/Quitting/Punishment/SoloFloorCompletion.lean`);
- `quittingStationarilyGeneratedApproximateEquilibria_of_normal_noHarmSingleton`
  (`UniformEquilibrium/Quitting/Classification/Existence/NoHarmSingletonGenerated.lean`);
- the related `quittingPunishmentValue_le_soloReward_of_abnormal`
  (`UniformEquilibrium/Quitting/Classification/AbnormalSingletonFloor.lean`).

CODEX_LARCH_DUAL independently checked the exact source statements and proof
uses. The newer result explicitly imports the older development. It
reconstructs stationary-prefix/punishment witness data, with separate accuracy
budgets, that the older UE-payoff conclusion does not expose.

The shared mathematics is the already available solo-cap formula and its
small-hazard limit. Approximate completed-cycle composition and its uniform
payoff endpoint are already packaged. A common quantitative cap-limit lemma
would be a small extraction, not a new theory.

History strengthens the rejection: the older file's introduction is a bulk
migration from GameTheory, while the no-harm and abnormal files originated
together. Existing long-interval mining also covers the no-harm/preemption
boundary. This is neither an independent rediscovery nor an overlooked
cross-episode producer.

## 4. Refined selection rules

### Distance is mathematical, not merely chronological

Use dates as a cheap preliminary signal. For shortlisted declarations:

- inspect the actual declaration introduction or major change, discounting
  file moves, migrations, formatting, and umbrella reorganization;
- inspect import reachability and direct theorem use, not just directory
  separation;
- inspect whether the later result intentionally strengthens the earlier
  witness or conclusion; and
- check existing mining records for the connection, not merely its names.

A recent theorem may still matter as one end of a connection to an old,
unrelated interface. Its nearby batch is not the primary search corpus.
Neither lack of an import nor old age alone establishes novelty.

### Prefer mathematical patterns over tactic patterns

Proof fragments are cheap candidate generators but frequently detect only
proof-engineering repetition. More informative retrieval channels are:

1. **Recurring hypothesis packages across different objects.** Preserve
   function types, quantifier order, signs, and coupling of witnesses.
   Ask whether one coherent structure explains the repeated obligations.
2. **An old premise versus a distant constructor.** Match hypotheses to
   conclusions, then check exact shared-source and strategy-class contracts.
   A useful match can have completely different proof syntax.
3. **Repeated boundary case splits.** Zero mass, nonattainment, support loss,
   or nonunique continuation may indicate a missing classification. Search
   positive constructions and counterexamples together.
4. **Families of special cases.** Compare the mathematical mechanisms behind
   separate player-count, support-pattern, rank, or sign restrictions. Check
   existing no-gos before proposing a common generalization.
5. **Witness information repeatedly reconstructed after being discarded.**
   Sometimes a stronger common interface is useful. Distinguish this from
   new mathematics: the solo-floor match is a calibration for that distinction.

Erase local naming noise, but retain the mathematical objects and the
relationships between variables. The pilot's aggressive identifier erasure
was useful for finding repetition and too destructive for inferring theory.

## 5. A cost-controlled workflow for a substantive next pass

Build a cheap index of declaration statements, imports, source history, and
links from the formalized/export and mining records. These are retrieval
features; exact theorem truth still requires the source and imports.

For each batch, select only a few candidates that cross at least two
independent boundaries, such as development episode and mathematical object.
Use these as preferences, not a hard rule excluding a compelling connection.
Reserve part of the batch for older-to-older matches so recency does not
determine the whole search.

Give each mathematical reviewer the paired source interfaces and a bounded
question. Ask for one of four outcomes:

1. already connected or already mined;
2. routine helper or stronger-witness extraction;
3. plausible common theory with a precise statement and a useful consumer;
4. a counterexample showing that the apparent common theory fails.

Promising theories need an exact small test and an independent review. They
should explain something the individual interfaces obscure, remove an actual
mathematical hypothesis, or produce a new construction. More duplicate code
removed is not by itself the acceptance criterion.

Cache rejected pairs with the reason for rejection, so subsequent passes do
not keep finding them. Do not invest in a large similarity-search system
until a small batch shows that statement/hypothesis and boundary-pattern
retrieval produces better mathematical leads than proof-shape retrieval did.

## Current outcome

The pilot validates the cost of wide mechanical retrieval followed by narrow
mathematical review, but not its usefulness as a theory detector yet. Both
reviewed high-ranking proof matches were false positives for the user's goal.
The next trial should prioritize hypothesis/conclusion and boundary-pattern
matches across genuinely separate development episodes, with proof similarity
used as supporting evidence only.
