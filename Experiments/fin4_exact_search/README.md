# Exact Fin4 scale search

## Clean-clone quickstart

This package needs only Python 3.11 or newer and the standard library. From a
fresh clone at the repository root, run the complete focused validation gate:

```bash
python3 Experiments/fin4_exact_search/validate.py
```

Then inspect an exact scale and start a resumable search using only tracked
files:

```bash
python3 Experiments/fin4_exact_search/run.py scale 100

python3 Experiments/fin4_exact_search/run.py search \
  --table Experiments/fin4_exact_search/examples/zero_table.json \
  --epsilon 100 --max-steps 4 \
  --checkpoint /tmp/fin4-zero.checkpoint.json.gz \
  --output /tmp/fin4-zero.certificate.json.gz

python3 Experiments/fin4_exact_search/run.py campaign \
  --table Experiments/fin4_exact_search/examples/zero_table.json \
  --start-epsilon 100 --work-dir /tmp/fin4-zero-campaign \
  --stop-after-scales 3
```

The large demonstration accuracy intentionally uses the smallest hierarchy
level. No installation, network access, `pytest`, generated repository file,
or `ephemeral/` runtime input is required. An optional editable install is
described below.

This package is a self-contained exact experiment for normalized rational
four-player quitting tables. It implements the reviewed ordinary-mathematics
scale-resolution contract directly, without importing or reading conference
files at runtime.

For a rational accuracy `epsilon > 0`, the fair search advances two exact
producers:

- a rational interval branch-and-bound tree proving
  `epsilon / 4 <= eta(r)`; and
- an exhaustive rational finite-clock enumeration seeking an actual profile
  of unrestricted terminal exploitability below `3 * epsilon / 4`.

The mathematical scale theorem says one of these searches terminates. The
current Lean repository does **not** yet contain the scale resolver or the
counterexample semidecision theorem. This package is an experiment and exact
reference implementation, not a kernel-checked implementation of them.

## Trust and claim boundary

Only exact `fractions.Fraction` recomputation accepts a table, profile, or
certificate. Heuristics influence candidate order only.

A verified global lower tree proves `gamma <= eta(r)` against every behavioral
profile. Because a cap is a supremum, this does not assert that one deviation
attains gain `gamma`. It yields the project's terminal-gap witness at any
strictly smaller value, for example `gamma / 2`.

A verified profile certificate contains four independent marginal stopping
laws, a finite clock, and a separate Never atom. Its cap includes all
payoff-distinct deterministic dates and Never and therefore represents the
complete behavioral deviation class through the checked pure-time extremality
semantics.

Nontermination, an unfinished checkpoint, an exhausted bounded upper region,
or a failed heuristic region proves nothing. This is not a decision procedure
for `eta(r) = 0`, and the package makes no claim of practical termination on
hard instances. No positive-gap Fin4 table is currently included.

The executable unit here is one table at one rational scale. The mathematical
productive fork runs those units at dyadic accuracies, and the mathematical
counterexample semidecision additionally dovetails over every normalized
rational table. This package supplies the exact inner worker, checkpoints,
regions, and finite manifests; it does not silently launch an exhaustive
rational-table enumeration or an infinite dyadic campaign. Such an outer
scheduler must preserve fairness across every table and scale. A lower
certificate from any worker is globally useful immediately after exact local
verification; a finite run of upper results is never a zero-gap certificate.

## Installation and smoke test

The runtime uses only Python 3.11 or newer and the standard library.

From the repository root:

```bash
python3 Experiments/fin4_exact_search/run.py validate-table \
  Experiments/fin4_exact_search/examples/zero_table.json

python3 Experiments/fin4_exact_search/run.py scale 1/10

python3 Experiments/fin4_exact_search/run.py search \
  --table Experiments/fin4_exact_search/examples/zero_table.json \
  --epsilon 100 \
  --max-steps 4 \
  --checkpoint /tmp/fin4-zero.checkpoint.json.gz \
  --output /tmp/fin4-zero.certificate.json

python3 Experiments/fin4_exact_search/run.py verify \
  /tmp/fin4-zero.certificate.json
```

The deliberately large smoke-test accuracy gives hierarchy level one. At a
research-scale accuracy such as `1/10`, the required level is `961`, the
finite clock has `7689` dates, and even constructing and searching the exact
problem is expensive. Always inspect `scale` before allocating a remote job.

An editable install is optional:

```bash
python3 -m pip install -e Experiments/fin4_exact_search
fin4-exact-search --help
```

There are no third-party runtime requirements.

## Input format

A table file has all fifteen nonempty coalition masks and four rational
payoffs per mask:

```json
{
  "players": 4,
  "rewards": {
    "1": ["0", "1/2", "-1", "0"],
    "2": ["0", "0", "0", "0"],
    "3": ["0", "0", "0", "0"]
  }
}
```

The displayed fragment must be completed through mask `15`. Rational values
may be integers, strings such as `"-3/7"`, `[numerator, denominator]`, or
`{"num": ..., "den": ...}`. Every coordinate must lie in `[-1,1]`.
`validate-table` prints the canonical SHA-256 table identifier used by remote
work regions.

## Main search and checkpoints

Run a bounded slice:

```bash
python3 Experiments/fin4_exact_search/run.py search \
  --table TABLE.json --epsilon 1/2 \
  --max-steps 10000 --max-seconds 3600 \
  --checkpoint state.json.gz --checkpoint-every 100 \
  --output certificate.json.gz
```

Resume it exactly:

```bash
python3 Experiments/fin4_exact_search/run.py search \
  --table TABLE.json --epsilon 1/2 \
  --checkpoint state.json.gz --resume \
  --max-steps 10000 --output certificate.json.gz
```

For a remote handoff, stop at a checkpoint boundary, copy the compressed
checkpoint together with the unchanged table (for example with `scp` or
`rsync`), and run the same command with `--resume` on the receiving machine.
The loader recomputes and compares the table hash, accuracy, hierarchy level,
lower target, and upper target before accepting the state.

The checkpoint stores both producer states and whose turn comes next. The
lower frontier stores exact sparse box changes and a flat tree under
construction. The upper frontier stores the diagonal, `(clock, denominator)`
pair offset, and product rank. Checkpoints and certificates may use `.json.gz`.
Writes are atomic through a sibling temporary file.

Exit status `0` means a certificate was written and exactly verified. Status
`2` means the allotted work ended with no conclusion. A finite remote region
that was completely exhausted without a certificate uses status `3`.

## Automated coarse-to-fine campaign

The `campaign` command automates the iterative process suggested by `scale`.
At scale `k` it uses

```text
epsilon_k = start_epsilon / refinement^k
```

and fairly advances the exact lower and upper searches. A verified lower
certificate stops the campaign with a positive lower bound on `eta(r)`. A
verified profile certificate is saved and the campaign advances to the next,
finer scale. By default `refinement` is `2`.

Start a long run with a time budget:

```bash
python3 Experiments/fin4_exact_search/run.py campaign \
  --table TABLE.json --start-epsilon 1 \
  --work-dir results/TABLE_CAMPAIGN \
  --max-seconds 86400
```

Resume the exact state later:

```bash
python3 Experiments/fin4_exact_search/run.py campaign \
  --table TABLE.json --start-epsilon 1 \
  --work-dir results/TABLE_CAMPAIGN --resume \
  --max-seconds 86400
```

The work directory contains one deterministic compressed campaign checkpoint,
every verified per-scale certificate, and a final summary when the campaign
reaches a terminal status. Completed profile certificates are reverified on
resume. Moving the complete directory to another machine preserves all
relative certificate references.

Long runs print one concise line at scale changes and periodically thereafter:

```text
progress scale=2 epsilon=1/4 level=385 steps=20000 lower_nodes=... lower_pending=... upper_diagonal=... upper_clock=... upper_rank=... elapsed_s=...
```

The defaults report every 10,000 steps or 60 seconds, whichever comes first,
and checkpoint every 1,000 steps. Use `--report-every`, `--report-seconds`, and
`--checkpoint-every` to change those frequencies. `Ctrl-C` writes a final
checkpoint before exiting. Resource limits pause with exit status `2` and the
explicit message `no mathematical conclusion`.

For finite smoke tests or resource planning, `--stop-after-scales N` stops
after `N` verified profile scales. This is only an engineering target: even a
long finite sequence of improving profile certificates is not a zero-gap or
uniform-equilibrium proof. If `eta(r)=0`, the unrestricted campaign is expected
to keep producing finer profiles forever; if `eta(r)>0`, it is expected
eventually to stop on a verified global lower certificate.

## Exact implementation improvements

The outer problem is regenerated from the table and never trusted from a
payload. Compared with the initial reference prototype, this engine uses:

- a hash-consed sparse expression DAG;
- iterative sparse dependency evaluation, not recursive expression descent;
- prefix sums for pure-deviation values, reducing cap construction from a
  quadratic to a linear number of clock rows;
- balanced sum/product/max expression trees;
- flat indexed certificate trees and iterative verification, so Python's
  recursion limit is not a correctness boundary;
- sparse box deltas in lower checkpoints;
- composition rank/unrank for upper enumeration, avoiding materialization of
  all simplex laws; and
- deterministic exact region identifiers and mergeable lower subtrees.

The exact lower splitter always chooses a coordinate of maximal width after
normalizing by its root width. This fairness is part of the mathematical
strict-margin completeness argument. Heuristic scoring is not allowed to
replace it.

## Batch mode

The manifest in `examples/batch.json` illustrates targeted table jobs:

```bash
python3 Experiments/fin4_exact_search/run.py batch \
  --manifest Experiments/fin4_exact_search/examples/batch.json \
  --work-dir /tmp/fin4-batch \
  --max-steps 1000 --checkpoint-every 100
```

Each job has an `id`, table path relative to the manifest, rational `epsilon`,
and optional `max_steps` or `max_seconds`. Every job gets a separate compressed
checkpoint and certificate. Batch completion still has the same claim
discipline: an unfinished job says nothing.

## Manual multi-machine coordination in one GitHub Issue

Use one dedicated GitHub Issue discussion as a manual work ledger. Do not let
workers post automatically. Each worker computes a canonical region locally,
posts a time-limited claim, sends heartbeats, and posts a certificate hash or a
release. The Issue is coordination only; comments are never trusted evidence.

Every descriptor fixes:

- canonical table SHA-256;
- rational epsilon and derived quantile level;
- work kind; and
- a deterministic subregion:
  - lower: a list of exact box splits `(variable, cut, side)`;
  - upper: a half-open diagonal range `[start,end)`;
  - heuristic: an algorithm name and half-open seed range; or
  - full: the whole fair scale resolver.

The `region_id` is the work kind followed by the first twenty hexadecimal
digits of the SHA-256 of canonical descriptor JSON.

### Generate work descriptors

An upper enumeration range:

```bash
python3 Experiments/fin4_exact_search/run.py region \
  --table TABLE.json --epsilon 1/2 --kind upper \
  --diagonal-start 2 --diagonal-end 20 \
  --output upper-2-20.region.json
```

A deterministic complete lower partition:

```bash
python3 Experiments/fin4_exact_search/run.py partition-lower \
  --table TABLE.json --epsilon 1/2 --depth 8 \
  --output lower-partition.json --regions-dir lower-regions
```

The `256` emitted lower descriptors are disjoint and cover the global root
box. To split one claimed lower region further, extract its `parameters.prefix`
array to `prefix.json` and run:

```bash
python3 Experiments/fin4_exact_search/run.py partition-lower \
  --table TABLE.json --epsilon 1/2 --depth 4 --prefix prefix.json \
  --output child-partition.json --regions-dir child-regions
```

A bounded deterministic heuristic range:

```bash
python3 Experiments/fin4_exact_search/run.py region \
  --table TABLE.json --epsilon 1/2 --kind heuristic \
  --seed-start 0 --seed-end 100000 \
  --output heuristic-0-100000.region.json
```

For a single machine owning the complete fair resolver, use `--kind full`;
the resulting descriptor is also accepted by `scan-region`:

```bash
python3 Experiments/fin4_exact_search/run.py region \
  --table TABLE.json --epsilon 1/2 --kind full \
  --output full.region.json
```

Run or resume a claimed region with `scan-region`. Its checkpoint contains the
canonical descriptor and is rejected if moved to a different table or region.

```bash
python3 Experiments/fin4_exact_search/run.py scan-region \
  --table TABLE.json --region upper-2-20.region.json \
  --checkpoint upper-2-20.state.json.gz \
  --max-steps 1000000 --output upper-2-20.certificate.json.gz
```

An upper or heuristic certificate is globally useful immediately. A lower
regional certificate proves only its declared box. Once every leaf of a
complete lower partition is certified, merge them and verify the global tree:

```bash
python3 Experiments/fin4_exact_search/run.py merge-lower \
  --output global-lower.certificate.json.gz \
  lower-results/*.certificate.json.gz

python3 Experiments/fin4_exact_search/run.py verify \
  global-lower.certificate.json.gz
```

### Issue message templates

Use UTC timestamps and a lease long enough for the next planned checkpoint.
Copy the canonical descriptor or attach it and give the printed canonical
`descriptor_sha256`. If attaching a file, also give its ordinary file hash.

Claim:

```text
CLAIM
region_id: lower-0123456789abcdef0123
worker: MACHINE_OR_PERSON
lease_until_utc: 2026-08-29T18:00:00Z
descriptor_sha256: FULL_SHA256
descriptor_file_sha256: FULL_FILE_SHA256
descriptor: attached lower-....region.json
checkpoint_start: none
command: python3 Experiments/fin4_exact_search/run.py scan-region ...
```

Heartbeat or lease extension:

```text
HEARTBEAT
region_id: lower-0123456789abcdef0123
worker: MACHINE_OR_PERSON
time_utc: 2026-08-29T15:00:00Z
lease_until_utc: 2026-08-29T21:00:00Z
steps: 250000
checkpoint_sha256: FULL_SHA256
status: unresolved; no mathematical conclusion
```

Release:

```text
RELEASE
region_id: lower-0123456789abcdef0123
worker: MACHINE_OR_PERSON
time_utc: 2026-08-29T16:00:00Z
checkpoint_sha256: FULL_SHA256
reason: resource limit / maintenance / reassignment
handoff_location: HUMAN-PROVIDED URL OR NONE
```

Split and handoff:

```text
SPLIT
parent_region_id: lower-0123456789abcdef0123
worker: MACHINE_OR_PERSON
time_utc: 2026-08-29T16:30:00Z
parent_checkpoint_sha256: FULL_SHA256
child_partition_sha256: FULL_SHA256
children: lower-AAA..., lower-BBB..., ...
parent_status: released after exact child partition generation
```

Exact result:

```text
RESULT
region_id: upper-0123456789abcdef0123
worker: MACHINE_OR_PERSON
time_utc: 2026-08-29T17:00:00Z
certificate_kind: fin4-rational-finite-clock-profile-v1
certificate_payload_sha256: FULL_CANONICAL_PAYLOAD_SHA256
certificate_file_sha256: FULL_FILE_SHA256
certificate_location: HUMAN-PROVIDED URL
local_verify_command: python3 Experiments/fin4_exact_search/run.py verify FILE
local_verify_output: valid exact profile certificate: ...
```

For a regional lower result, say `certificate_scope: regional`; it becomes a
global lower bound only after a complete partition is merged and the merged
certificate verifies locally.

### Stale-claim recovery

A claim is stale only after its `lease_until_utc` has passed without a later
heartbeat. A replacement worker posts:

```text
RECLAIM_STALE
region_id: lower-0123456789abcdef0123
new_worker: MACHINE_OR_PERSON
time_utc: 2026-08-29T22:00:00Z
observed_lease_until_utc: 2026-08-29T21:00:00Z
last_heartbeat_comment: ISSUE COMMENT URL
checkpoint_used: HASH/LOCATION OR none; restarting deterministically
new_lease_until_utc: 2026-08-30T04:00:00Z
```

If two machines accidentally overlap, keep the first unexpired claim and ask
the other to release or split. Duplicate results may be useful as independent
checks but should not be mistaken for extra coverage.

No Issue message, file hash, or claimed solver status accepts a result. A
recipient downloads the file, checks its SHA-256, and runs the exact local
`verify` command. Lower regional certificates must additionally be assembled
into a complete partition and the merged tree verified.

## Tests

Run the standard-library suite from the repository root:

```bash
PYTHONPATH=Experiments/fin4_exact_search \
  python3 -m unittest discover \
    -s Experiments/fin4_exact_search/tests -v
```

The tests cover exact late deviations, profile certificates, rational
composition rank/unrank, seeded direct-versus-DAG agreement, checkpoint
resumption, deterministic regions, and a depth-1200 invalid flat tree which is
rejected without hitting Python's recursion limit.

## Limitations

- Exact outer systems grow rapidly with `1 / epsilon`; interval dependency
  bounds can remain wide for a very long time.
- Checkpoints can become large. Compression reduces disk size, not the memory
  needed to resume a frontier.
- The upper enumerator is complete but intentionally elementary. It is not an
  efficient nonlinear equilibrium solver.
- The stationary-grid heuristic is incomplete and untrusted; exhaustion has
  no meaning.
- Exhaustion of one finite upper diagonal range says only that the range has
  no accepted profile.
- A regional lower tree is not a global certificate until exact merge and
  verification succeed.
- There is no automated GitHub communication and no remote execution service.
- No result here carries a Lean evidence seal.
