# Exact Fin4 discovery search

This package searches normalized rational four-player quitting tables using one
exact equality-free finite-clock resolver.  It needs Python 3.11 or newer and
the standard library only.

## Clean-clone quickstart

From the repository root:

```bash
python3 Experiments/fin4_exact_search/validate.py

python3 Experiments/fin4_exact_search/run.py discover \
  --work-dir fin4-search-results
```

`discover` is the unattended coarse-to-fine campaign.  It needs no external
table file: it deterministically rationalizes and normalizes the tracked hard-
candidate corpus, then searches candidates in scale-major order.  Repeating
the same command resumes the checkpoint in the work directory automatically.

There is no default wall-clock stop or final scale.  The command continues
until it verifies a positive-gap certificate or is interrupted.  `Ctrl-C` and
`SIGTERM` preserve the most recent atomic quantum checkpoint; work inside the
interrupted quantum may be repeated.

For a shell-managed two-day allocation on Linux:

```bash
timeout --signal=TERM --kill-after=5m 48h \
  python3 Experiments/fin4_exact_search/run.py discover \
  --work-dir fin4-search-results
```

The process reports the current candidate, scale, exact steps, lower-tree
size, upper enumeration position, elapsed time, and peak resident memory.  It
keeps one expression DAG and one exact resolver resident.  Completed resolver
state is released before its certificate is independently reconstructed and
verified.

## Mathematical contract

For a rational accuracy `epsilon > 0` and `0 < alpha < 1`, the resolver fairly
advances two exact producers:

- a rational interval branch-and-bound proof of
  `alpha * epsilon <= eta(reward)`; and
- exhaustive rational finite-clock profile enumeration seeking an actual
  profile of unrestricted terminal exploitability below `epsilon`.

The finite-clock level is the least positive `N` satisfying

```text
24 / N < (1 - alpha) * epsilon.
```

The lower tree proves a finite-clock threshold of

```text
alpha * epsilon + 24 / N.
```

The common-quantile transport theorem then gives the displayed global lower
bound `alpha * epsilon` against every behavioral profile.  Since a cap is a
supremum, a verified lower bound `gamma <= eta(reward)` yields the project's
terminal-gap witness at any strictly smaller value, for example `gamma / 2`;
it does not claim that one deviation attains gain exactly `gamma`.

A verified profile certificate contains four independent marginal stopping
laws, all represented finite dates, and a separate Never atom.  Its cap checks
all payoff-distinct pure dates and Never, which covers the complete behavioral
deviation class through pure-time extremality.

Only exact `fractions.Fraction` recomputation accepts a table, profile, or
certificate.  Heuristics may order candidates but cannot accept a result.

Nontermination, timeout, an unfinished checkpoint, or any finite sequence of
profile certificates proves nothing about `eta(reward)=0`.  This is a
semidecision procedure for positive gaps over the searched candidate stream,
not a decision procedure for the quitting-game conjecture.

## Commands

The public CLI has one formulation and five commands:

```text
discover        search the tracked candidate corpus indefinitely
search          run one explicit table at one exact scale
scale           display the exact contract used by search/discover
verify          independently verify a produced certificate
validate-table  validate and hash a normalized rational table
```

Inspect a scale:

```bash
python3 Experiments/fin4_exact_search/run.py scale 1/10
```

Run or resume one explicit table/scale problem:

```bash
python3 Experiments/fin4_exact_search/run.py search \
  --table TABLE.json --epsilon 1/2 \
  --checkpoint state.json.gz \
  --output certificate.json.gz \
  --max-steps 10000 --max-seconds 3600

python3 Experiments/fin4_exact_search/run.py search \
  --table TABLE.json --epsilon 1/2 \
  --checkpoint state.json.gz --resume \
  --output certificate.json.gz \
  --max-steps 10000
```

Verify a result independently:

```bash
python3 Experiments/fin4_exact_search/run.py verify certificate.json.gz
```

Exit status `0` means a certificate was produced and verified.  Status `2`
means the allotted work ended with no conclusion.

## Input format

A table file contains all fifteen nonempty coalition masks and four rational
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

The fragment must be completed through mask `15`.  Values may be integers,
rational strings such as `"-3/7"`, `[numerator, denominator]`, or
`{"num": ..., "den": ...}`.  Every coordinate must lie in `[-1,1]`.

Validate and print its canonical SHA-256 identifier:

```bash
python3 Experiments/fin4_exact_search/run.py validate-table TABLE.json
```

## Checkpoints and resource behavior

Checkpoint and certificate files may use `.json.gz`.  Writes use a sibling
temporary file followed by atomic replacement.  A checkpoint records both
the lower and profile producers and whose turn comes next.  Resume validates
the table hash, accuracy, scale level, and all threshold parameters before
accepting state.

The lower proof tree grows linearly with explored proof nodes because it is
prospective certificate data.  Its live DFS state uses one mutable interval
map and constant-size sibling/restore events rather than retaining copied maps
for every frontier box.  The upper producer enumerates rational compositions
by rank without materializing the simplex.

The optional `--max-seconds` bound is cooperative and checked between exact
operations.  A single expression-DAG build or interval step may overrun it.
The external `timeout` command sends `SIGTERM`, allowing the Python process to
finish the current exact quantum and save its checkpoint.

## Multi-machine sharding

Split `discover` across machines with one shared shard count and distinct
indices:

```bash
python3 Experiments/fin4_exact_search/run.py discover \
  --work-dir fin4-shard-2-of-8 \
  --shard-count 8 --shard-index 2
```

Indices range from `0` through `N-1`.  Use one dedicated GitHub Issue as a
manual lease board.  Before starting, each worker posts:

```text
CLAIM
commit: GIT_SHA
campaign_id: PRINTED_CAMPAIGN_ID
shard: I/N
start_epsilon: 4
refinement: 2
alpha: 1/2
denominator: 10000
worker: MACHINE_OR_PERSON
lease_until_utc: ISO_8601_UTC
checkpoint: LOCAL_OR_SHARED_LOCATION
```

Two claims with the same commit, campaign ID, and shard are duplicate work.
A heartbeat repeats those fields and adds the exact-step count and checkpoint
SHA-256.  A worker releasing a shard posts the final checkpoint hash and its
human-provided location.  After a lease expires, another worker may post
`RECLAIM_STALE` and resume the published checkpoint or restart the
deterministic shard.

Issue comments coordinate work only.  A result counts only after downloading
the certificate and running the local `verify` command.

## Installation and tests

No installation is required.  An editable install is optional:

```bash
python3 -m pip install -e Experiments/fin4_exact_search
fin4-exact-search --help
```

Run the complete clean-clone gate:

```bash
python3 Experiments/fin4_exact_search/validate.py
```

Or run the standard-library test suite directly:

```bash
PYTHONPATH=Experiments/fin4_exact_search \
  python3 -m unittest discover \
    -s Experiments/fin4_exact_search/tests -v
```

The tests cover exact late deviations, independent-law profile certificates,
rational composition rank/unrank, direct-expression agreement with terminal
semantics, deep iterative proof state, exact checkpoint resumption, candidate
sharding, and the one-resident-resolver memory gate.

## Limitations

- Exact expression systems grow rapidly as `epsilon` decreases.
- Interval dependency bounds can remain wide for a very long time.
- Checkpoints can become large; compression reduces disk size, not resume
  memory.
- The complete profile enumerator is intentionally elementary.
- Candidate discovery is targeted, not an exhaustive enumeration of all
  rational reward tables.
- No positive-gap Fin4 table is currently included.
- No result from this Python package carries a Lean evidence seal.
