# Games/ — counterexample-search game portal

A local game portal whose play sessions are search over four-player quitting
reward tables for uniform-equilibrium counterexample candidates. See
`DESIGN.md` for the full contract (model, wire formats, HTTP API, game
designs).

## Run it

```
python3 Games/serve.py
```

That's the whole setup: Python standard library only, no install step, no
build step. It serves the portal and every game at `http://127.0.0.1:8710/`.
Pick a different port with `--port`:

```
python3 Games/serve.py --port 9000
```

The server binds `127.0.0.1` only (not reachable from other machines) and
runs until you stop it with Ctrl+C.

For anything other than actually playing — automated tests, ad hoc smoke
checks, one-off curl sessions — point persistence at a scratch directory
instead of the shared default:

```
python3 Games/serve.py --data-dir /tmp/games-scratch
```

`Games/data/` is shared by every agent's server process and is **never**
deleted or truncated by anyone, including to clean up your own test debris —
see the Persistence section of `DESIGN.md`. `--data-dir` is how you avoid
touching it at all.

## Where things live

- `Games/serve.py` — entry point.
- `Games/server/` — the HTTP layer: routing, static file serving, request
  validation, the background job registry for deep attacks, and JSONL
  persistence. Pure I/O plumbing; all game-theoretic computation is reached
  lazily through `server/engine_adapter.py` from `Games/engine/`.
- `Games/engine/` — the shared, pure-function evaluator/attack/filter engine.
- `Games/portal/`, `Games/games/{standoff,sequencer,breeder,atlas}/` — static
  front ends, served at `/`, `/standoff/`, `/sequencer/`, `/breeder/`,
  `/atlas/` respectively.
- `Games/data/` — where everything you do gets recorded, as append-only
  JSONL: `candidates.jsonl` (every table submitted by a game, with the
  server's own evaluation and evidence tier) and `profiles.jsonl` (every
  killing profile submitted to the shared attacker library). Created
  automatically on first run. Nothing here is rewritten in place; status
  changes are appended as small update records and merged when read.

Run the server's own test suite from `Games/`:

```
python3 -m unittest discover server/tests
```

## What a "survivor" means

Every table a game produces is re-scored by the server's own engine before
it is recorded — never by whatever the browser computed during play. A table
that survives an attack level is evidence that a *bounded search* over that
level's profile families did not find a way to exploit it below the kill
threshold. It is not a theorem, not a proof, and not evidence that no
profile exists that would exploit it. Every output of this portal is a
*proposal*, to be re-verified offline (see `Games/scripts/verify_candidates.py`
and, ultimately, the Lean development) before it means anything
mathematically.
