# Games/ — counterexample-search game portal

## Purpose

A local HTML game portal whose play sessions are search over four-player
quitting reward tables for uniform-equilibrium counterexample candidates.
Player experience is shaped so that natural play walks toward tables with a
high exploitability floor. Every promising table is persisted with provenance
and evaluation evidence; a game session that leaves no durable record is
worthless.

`Games/` is deliberately gitignored and NON-INTERFERING: nothing here touches,
imports into, or runs checks on the Lean development or repo scripts. Read
access to the rest of the repository is fine (especially
`Experiments/singleton_collision_candidate_search/`); write access is Games/
only. Nothing in Games/ makes mathematical claims — every output is a
*proposal* re-verified offline. Do not run git, lake, or `scripts/*.py`.

## Mathematical model (fixed, N = 4)

Players 0..3 simultaneously choose Continue/Quit each stage. First nonempty
quitter set S ends the game paying reward row r_S in R^4; no absorption ever
pays 0 to everyone. Entries clamped to [-4, 4].

The reference implementation of everything below is
`Experiments/singleton_collision_candidate_search/singleton_collision_candidate_search.py`
(read-only). Its README documents filters 1-6 and attack battery A-D. The
engine is a faithful port of that math; parity with the original script is a
hard requirement, enforced by tests.

Key scoring notions:
- **Profile**: periodic per-player hazards `{period P, hazards[P][4]}`, each in [0,1].
- **Exploitability** of a profile on a table: max over players of (best
  unilateral deviation value − on-path value), maximized over phases; best
  response computed exactly by enumerating the 2^P phase-indexed stopping
  policies (closed-form cyclic solves).
- **Table score** = minimum exploitability found by the attack battery.
  Higher = more counterexample-like. Kill threshold eps_kill = 0.02;
  target margin g = 0.1.

## Wire formats (authoritative; do not change unilaterally)

**Table**: JSON array of 16 arrays of 4 numbers. Index = coalition bitmask
(bit i set = player i quits). Row 0 must be all zeros. Values in [-4, 4].

**Profile**: `{"period": P, "hazards": [[h0,h1,h2,h3], ...]}` with P rows,
hazards in [0,1]. P in 1..8.

**Attack levels** (measured on this machine, Solan-Vieille seed):
`"replay"` (library only, ~10 ms), `"quick"` (explicitly reduced `*_quick`
variants of ALL five attack families — not just stationary — ~250 ms),
`"standard"` (the full faithful A/B/C/D battery, ~5 s; the reference script
costs the same, and the battery is kept faithful rather than trimmed to a
target — interactive callers wanting fast rejection use abandon-at-kill,
which collapses to ms whenever an earlier attack kills), `"deep"` (heavy
re-attack, ~75 s; background job). Library replay is prepended at every level.

**Evidence tiers** (string enum, ordered weakest-to-strongest kill evidence):
`"unattacked"`, `"survivor-quick"`, `"survivor-standard"`, `"survivor-deep"`
(these grade *effort spent without a kill*, never proof of anything), and for
killed tables `"numerical-narrow"` (best score in [0.5*eps_kill, eps_kill]),
`"numerical-wide"` (score < 0.5*eps_kill), `"exact"` (rational-snapped profile
re-verified with exact arithmetic).

## HTTP API (single local server, default port 8710)

`python3 Games/serve.py [--port 8710]` starts everything. Stdlib only
(ThreadingHTTPServer). Static mounts: `/` -> `Games/portal/`,
`/standoff/` -> `Games/games/standoff/`, `/sequencer/` -> `Games/games/sequencer/`,
`/breeder/` -> `Games/games/breeder/`, `/atlas/` -> `Games/games/atlas/`.

JSON endpoints (POST bodies and responses are JSON; errors:
`{"error": "..."}` with 4xx/5xx). Non-finite floats are sanitized before
serialization: `inf` -> 1e9, `-inf` -> -1e9, `nan` -> null; clients should
treat any score >= 1e9 as "nothing found by this attack", not a real value:

- `POST /api/evaluate` `{table, profile}` ->
  `{"exploitability": g, "per_player": [g0..g3], "on_path": [v0..v3],
    "best_deviations": [{"player": i, "value": v, "policy": [bool per phase]}]}`
- `POST /api/attack` `{table, level}` (level != deep) ->
  `{"score": s, "binding_attack": name, "level": lvl, "elapsed": secs,
    "breakdown": {attack_name: {"exploitability": e, "profile": {...}}}}`
  Attack names: `"library_replay"`, `"stationary"`, `"one_quitter_cyclic"`,
  `"two_quitter_periodic"`, `"general_periodic"`.
- `POST /api/attack` with `level:"deep"` -> `{"job": id}`;
  `GET /api/jobs/<id>` -> `{"status": "running"|"done"|"error", "result": ...}`
- `POST /api/attack_batch` `{tables: [...], level: "replay"|"quick"}` ->
  `{"results": [attack-response-shaped, ...]}` (order preserved; for atlas).
- `POST /api/filters` `{table}` ->
  `{"pass": bool, "filters": {"1_toggle_instability": {"pass":b, ...detail}, ...}}`
  Filter keys are the engine's verbatim names (matching the reference script's
  `FILTER_NAMES`, e.g. `"6_no_lcp_solution"`) — treat them as opaque labels.
- `POST /api/harden` `{table, profile}` -> the rational-snap result from
  `engine.rational.harden` (whether a small-denominator snapped profile still
  kills at eps_kill, exactly). Backs the `"exact"` tier; used by sequencer.
  A pure preview: it persists nothing — recording happens only when the client
  submits the SNAPPED profile via POST /api/profiles. Ledger readers must
  expect the tradeoff: snapping trades margin for exactness, so exact-tier
  profiles typically sit close to eps_kill (e.g. a 1.7e-10 float kill snaps
  to an exact 128/6475 ~ 0.0198) — near-threshold exact records are normal,
  not degraded.
- `GET /api/tables/curated` -> `{"tables": [{"id", "name", "table",
    "known_score": s|null, "note"}]}` — must include the Solan-Vieille seed and
  the three chain-best tables read (read-only) from
  `Experiments/singleton_collision_candidate_search/results.json`.
- `POST /api/candidates` `{table, game, session, provenance}` ->
  `{"id", "record"}`; server evaluates at `standard` level before recording.
- `GET /api/candidates?limit=50` -> `{"candidates": [records newest first]}`
- `POST /api/profiles` `{profile, source: {game, session, table_id|table}}` ->
  `{"id"}` — submit a killing profile into the shared attacker library.
- `GET /api/stats` -> `{"candidates": n, "best_score": s, "library_profiles": n,
    "kills": n, "games": [...]}`.

## Persistence (Games/data/, append-only JSONL, one JSON object per line)

- `candidates.jsonl`: `{"id", "created" (iso8601), "table", "game", "session",
  "provenance" (free-form dict incl. action trace summary), "evaluation"
  (attack response), "tier", "status": "proposed"|"verified"|"killed",
  "killed_by" (profile or null)}`
- `profiles.jsonl`: `{"id", "created", "profile", "source",
  "kills": [{"candidate_id"|"table_hash", "score"}]}`
- Never rewrite lines; status changes are appended as
  `{"id", "update": {...}, "updated": iso8601}` lines merged on read.
- **Games/data/ is never deleted or truncated, by anyone, for any reason** —
  including cleanup of one's own test debris. Multiple agents' server
  processes share this directory, so "leftover clutter" may be someone else's
  record. Automated tests and smoke tests MUST run against a scratch
  directory via `python3 Games/serve.py --data-dir <path>`; anything written
  to the default Games/data/ stays. Records that turn out to be junk are
  marked dead by appending an update line, never by removing bytes.

The attacker **library** is central: every profile that ever killed a table is
replayed (cheap, exact) against every new candidate first. It is the
difficulty curve of every game and the CEGIS memory of the portal.

`Games/scripts/verify_candidates.py` runs the deep re-attack over proposed
candidates offline and appends tier/status updates.

## Engine layout (Games/engine/, pure functions, no I/O except curated loader)

- `model.py` — table/profile types, masks, validation, hashing.
- `evaluator.py` — exact periodic evaluator + 2^P best-response enumeration.
- `filters.py` — filters 1-6.
- `attacks.py` — attacks A-D + Nelder-Mead (port from the experiment script).
- `battery.py` — level orchestration (replay/quick/standard/deep), cheapest-first
  with early abandon exactly like the experiment.
- `library.py` — pure replay of a profile list against a table.
- `rational.py` — snap-to-small-denominator + exact Fraction re-evaluation for
  the "exact" tier.
- `curated.py` — loads seed + chain-best tables from the experiment results.json.
- `tests/` — `python3 -m unittest discover Games/engine/tests` must pass:
  parity vs the original script (import it via importlib from its path; compare
  evaluator outputs on seeded random tables/profiles to 1e-9), plus the
  self-check identities (on-path decomposition, non-negative exploitability,
  stationary closed form).

## Game design contract (every game)

UX beats uniformity. There is no human maintainer who needs to grok a shared
stack; the ONLY hard invariant is honesty of the persistent record:

- **Authoritative at record time, free at play time.** The server re-scores
  every submitted table with the shared engine before persisting; the recorded
  evaluation is the engine's, never the client's. During play, a game may do
  anything: embed its own in-browser JS port of the evaluator for zero-latency
  feedback (strongly encouraged where interaction is continuous — sequencer,
  standoff animations), precompute, approximate, or ignore the engine
  entirely. Client math can drive feel; it cannot drive the ledger.
- Runs locally with no install: self-contained static files served by the
  portal server, no CDNs at runtime, no build step required to *run*. Beyond
  that, each game picks whatever client tech serves its UX (canvas, WebAudio,
  WebGL, inlined libraries are all fine).
- Mock mode: `?mock=1` uses canned contract-shaped responses so the UI can be
  developed and demoed without the server.
- Confidence rendering: kill margin and tier must be visible (grain/wobble/
  beat — see each game). Never render "not killed" as "counterexample".
- Every promising table is submitted via `POST /api/candidates` with game name,
  client-generated session UUID, and an action-trace summary. Every killing
  profile found by a player is submitted via `POST /api/profiles`.
- **Subspace restriction is allowed — with a reason (user decision).** A game
  may explore only a portion of the possibly-counterexample space (quantized
  payoffs, a parameterized family, preserved symmetries, fixed rows) when
  that genuinely serves the experience — discrete moves that read as cards,
  phenotype coherence, a controllable dimensionality. Three obligations:
  (a) the reason is stated in the game's README; (b) the restriction is
  recorded in every submission's provenance (e.g. `subspace: {lattice: 1/4}`)
  so the research side knows which region was searched; (c) the restriction
  is never presented as coverage — a subspace with no survivors says nothing
  about the rest of the space, and the ledger view must not imply otherwise.
- **Full diegesis (hard UX rule, from user feedback).** The player is never
  informed by anything from the solution domain — no "exploitability",
  "profile", "table", "filter", "candidate", "tier", "server", "0.02",
  no raw floats, no coalition bitmasks — at ANY point in normal play. The
  fiction carries every meaning: scores are in-fiction quantities, targets
  are in-fiction objects, outcomes are in-fiction events. The ONE exception:
  each surface has a single dedicated, non-intrusive affordance (a small
  corner icon, consistent across games — "the ledger") that opens the
  research view: the raw table, real scores and tier, provenance, and the
  honest statement of what the result is and is not evidence of. That view
  is where the repo's honesty language lives, verbatim and complete; the
  play surface simply never speaks the domain language at all, and so never
  makes a claim. It's a game; the player should have fun playing a game.
- **Show, don't tell.** Landing surfaces are full-viewport and zero-scroll;
  a game starts in ONE click; "about" text lives behind a small per-tile
  affordance, never inline. In-game state is communicated visually (gauges,
  color, motion, sound, fiction) — never as a panel the player must read to
  play. Instruments auto-start with sensible defaults on load; configuration
  is optional, not a prerequisite.
- **The goal is always visible (user feedback).** Every game keeps one short
  in-fiction objective permanently on the play surface — a single "do X!"
  the player can re-read at any moment ("Settle the room", "Breed one the
  lab will take") — with visible progress toward it. A one-shot coach mark
  teaches a control; it is not a goal. If a player looks at the screen cold
  and cannot say what they are trying to achieve, the surface is wrong.
- **Navigation stays in the tab.** Hand-offs between games navigate the
  current tab (the map/machine state must survive via cache/localStorage);
  never window.open/_blank.
- **No empty states, no manuals.** A game opens mid-play: a target already
  loaded, a hand already dealt, a pen already breathing — never "load X to
  begin" or a disabled primary button as the first thing seen. Controls are
  taught by doing (contextual first-use hints at most), never by a printed
  list of shortcuts on the play surface. Any help beyond that lives in the
  ledger affordance too — one quiet door for everything out-of-fiction.

### standoff (roguelite designer)
Western standoff fiction: four gunslingers around a table you rig. Player
edits the table under an edit-point budget (structural moves: perturb rows,
strengthen a collider, rotate roles), then rings the bell: attack waves arrive
cheapest-first (library replay -> stationary -> one-quitter -> general
periodic -> two-quitter), each wave a named antagonist with a tell; health bar
= current min exploitability vs eps_kill. Survive all waves -> boss (deep
attack as background job) -> survivor submitted as candidate. Runs are short
and re-rollable; the growing library makes later runs harder and says so.

### sequencer (player as attacker)
A 4-track step-sequencer / rhythm machine. Pick a target (curated tables and
proposed candidates from the API). Drag per-phase hazard bars (period 1-8);
live per-player exploitability meters and a ghost overlay of the current best
deviation — computed by an in-browser JS port of the exact evaluator at
interaction rate (the math is small: cyclic closed forms + 2^P policy
enumeration), with `/api/evaluate` used to confirm at rest. Goal: drive exploitability under eps_kill —
the machine "locks into groove". Then a "harden" action rational-snaps the
profile (server-side) toward the `exact` tier. Success kills the candidate and
feeds the library. Audio encouraged: score as detune/beat frequency.

### breeder (interactive evolution)
3x3 grid of creatures whose phenotype is drawn from table structure
(preemption digraph -> body plan, magnitudes -> proportions, filter margins ->
health). Pick parents; offspring via structural mutation/crossover, filtered
for legality (filters 1-5) before display; each shown with its quick-attack
floor. Lineage view. High scorers auto-submitted as candidates. The player
only needs taste.

### atlas (map painter)
Choose a 2-parameter slice: table(x, y) = clamp(A + x(B-A) + y(C-A)) over
curated/candidate tables A, B, C. Progressive-refinement pixel grid colored by
binding attack, with grain/alpha by margin tier and fog for unattacked, via
`/api/attack_batch` (replay then quick). Click a pixel to inspect the table
and hand it to standoff/sequencer via a `?table=` URL payload. The goal-feel:
find and expand pale regions.

### portal (lobby)
`Games/portal/index.html`: names and one-line pitches for the four games,
recent-candidates ticker, library/kill counters (`/api/stats`), tier legend,
and a plain paragraph stating exactly what a "survivor" is evidence of (bounded
search effort, not a theorem).

## Non-interference rules (hard)

- Write only inside `Games/`. Read-only everywhere else.
- Python stdlib only (the repo has no numpy/scipy). No network access at runtime.
- No git operations, no lake, no repo scripts, no edits to CLAUDE/AGENTS/docs.
- Cross-platform: pathlib, no symlinks, no shell-outs; must run on WSL via
  `python3 Games/serve.py`.
