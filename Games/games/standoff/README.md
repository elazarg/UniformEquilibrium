# standoff

Four gunslingers, one table, and a payout sheet only you can touch. You are the
fixer. Your job is to rig the stakes so that no arrangement the four of them can
find ever holds — whatever they settle on, somebody always has an itch to move
first.

Underneath: a four-player quitting reward table, and the player is hill-climbing
it toward a high exploitability floor without ever being shown a matrix.

## Running

Served by the portal at `/standoff/`:

```
python3 Games/serve.py
```

then open <http://localhost:8710/standoff/>.

Query parameters:

- `?mock=1` — offline demo. Contract-shaped responses are computed in the
  browser by `js/eval.js` against canned curated tables. Nothing is recorded and
  a badge says so on screen.
- `?table=<urlsafe-base64 JSON>` — start a run from a handed-in table (this is
  how atlas hands one over). Both a bare 16x4 array and `{"table": [...]}` are
  accepted.

## The loop, and the API calls behind it

A run is five bells and a boss, five to fifteen minutes, re-rollable.

| beat | what the player does | API |
| --- | --- | --- |
| pick a table | curated list, or "shuffle a fresh deck" | `GET /api/tables/curated` |
| spend edit points | play cards from a hand of five pre-rolled structural moves | `POST /api/filters` on each committed edit |
| ring the bell | waves arrive cheapest-first | `POST /api/attack` at `replay`, then `quick`, then `standard` |
| survive five bells | the Marshal takes a long look | `POST /api/attack` `level:"deep"`, then `GET /api/jobs/<id>` |
| survive the Marshal | the table is written down | `POST /api/candidates` |
| lose | the gang keeps the schedule that beat you | `POST /api/profiles` |
| always | "the gang knows N tricks" | `GET /api/stats` |

One `POST /api/attack` per level; the waves of that level are then staged one at
a time from the response `breakdown`, so five antagonists cost at most three
round trips. `quick` already returns every attack, but the expensive callers are
still staged from the `standard` response so that what the player sees is the
strength the engine actually spent.

Three readings are never treated as verdicts: a breakdown key that is absent, one
that is `null` (as the four non-replay keys are at `replay` level), and a
sanitized non-finite value. Payoffs are clamped to `[-4, 4]`, so a real
exploitability cannot exceed 8; the API sanitizes infinity to `1e9` and NaN to
`null`, and an attack with nothing to try — an empty attacker library, most
often — comes back as the former. None of the three moves the nerve bar, and the
Ghosts arriving to an empty book say so in fiction.

When the library is what killed the table, the death screen names the stored
profile from `breakdown.library_replay.source`, which the engine reports as
`{"id": <profile id>, "source": {game, session, table_id|table}}` — rendered as
"the schedule filed as 51bd1f48, off an earlier table of yours". A bare string,
a `note`, or a plain id are accepted too, and a missing one falls back to
generic wording.

## The antagonists

They arrive in the order the engine battery orders them, cheapest first.

| attack | who | tell |
| --- | --- | --- |
| `library_replay` | The Ghosts | they do not aim; they repeat a draw somebody already wrote down |
| `stationary` | Clay Stillwell, the Statue | the same odds every beat, forever |
| `one_quitter_cyclic` | The Kettleman Carousel | one man per beat, the turn passing round the table |
| `general_periodic` | The Drifter | every man on his own private clock |
| `two_quitter_periodic` | The Paired Draw | two draw together, then the other two — the one that empties rooms |
| `deep` | The Marshal | does not hurry, does not stop |

## Which numbers are whose

The hard invariant is that the ledger only ever records the engine's numbers.

- Every reading that moves the nerve bar comes from `POST /api/attack`.
- The recorded score is whatever the server computes at `POST /api/candidates`;
  when it differs from the number the player watched, the victory screen says so
  and says which one counts.
- `js/eval.js` is a browser port of the exact periodic evaluator and of filters
  1&ndash;5. It exists to grey out illegal cards instantly, to animate killing
  schedules, and to run mock mode. Anything it produces that reaches the screen
  is labelled a hunch, and the one place a client number is quoted (the card
  hover line) names the single attack family and the coarse grid it came from.
- The port was checked against
  `Experiments/singleton_collision_candidate_search/singleton_collision_candidate_search.py`:
  the evaluator agrees to 4.4e-16 over 60 seeded table/profile pairs including
  near-degenerate hazards down to 1e-16, and filters 1&ndash;5 agree exactly on
  120 tables. That check is a development check, not a shipped test.

Card legality is previewed with the client filters and then confirmed with
`POST /api/filters` before the edit is committed; if the server disagrees the
edit is discarded, the card is re-stamped, and no points are spent.

## Diegesis, and where the numbers went

The play surface never states a number, a threshold, or a word from the
mathematics. State is carried by the gauge, by colour and motion, and by what
the room says:

- **The nerve gauge** maps the current minimum exploitability onto the interval
  between the kill line (the left edge, marked red) and the target margin (the
  right edge, marked green), with no readout. The closer the best-found
  arrangement came to settling the table, the grainier the bar and the harder it
  shivers. A pale notch marks the best the table held this run; a small medal
  marks the best ever, so a run has something visible to beat.
- **Bells and favours** are pips, not counts.
- **Callers** are figures crowding the doorway and a strip of portrait chips.
  There is no roster: their names are learned by watching them attack.
- **Readings** are phrases — "a hair from settling", "they very nearly had it",
  "restless — nowhere near settling".
- **Cards** show a fictional blurb; the precise edit is recorded in the
  provenance action trace but never printed.

**The ledger**, behind the one brass affordance in the corner (labelled "the
ledger", per the portal-wide convention), is the single exception and holds
everything the fiction withholds: the kill threshold and target margin, the last
reading, the worst of the round, the best margin survived, the personal best,
the killing exploitability and which attack found it, the deep score, the
server's recorded score, the evidence tier, the record id, the session, the raw
reward table, the filter verdicts, and the honesty statement in full.

Two books are kept, and the game never confuses them: the **gang's book** is the
attacker library, the timings they have already learned; **the ledger** is the
research view, kept by the county clerk. Losing copies a timing into the gang's
book; surviving files the sheet with the clerk.

A run opens mid-play — a table already dealt, a hand already in front of you,
the bell live. Choosing a different table is one click behind "deal again". On a
first visit only, one playable card is spotlit with a single coach line; after
the first bell it never appears again.

## Material identity

Lamplight, wood, brass, smoke. The room is oiled plank grain under a single
guttering lantern whose flicker drives the light on the canvas; anything the
house owns is brass (the rail, the gauge bezel, the bell, the favour coins, the
one affordance that opens the ledger); the cards are printed handbills on foxed
paper with a letterpress refusal stamp; tobacco haze drifts between the player
and the table, faint enough never to obscure a reading. The ledger is the only
surface in the building that is not lamplit: ruled cream paper with a red margin
rule and ink, because it is a different kind of object.

## The lattice: money comes in bits

standoff plays on the **quarter sublattice** of `[-4, 4]`. Every card moves
stakes by a whole number of quarters, and the whole table is snapped after each
committed edit.

The reason is experiential, and it is the fiction's own: a quarter is *two
bits*, so a card can name its effect in money — "a sweeter payday if they both
go at once — six bits more" — instead of printing a float. Edits read as card
play, tables become memorable and shareable, and a run is reproducible from its
action trace.

This is a **restriction of the search, not coverage of it**. Tables off this
lattice are never examined by this game. Every submission records the
restriction under `provenance.subspace`:

```json
{"lattice": "1/4", "range": [-4, 4], "holds": true,
 "started_on_lattice": true, "note": "..."}
```

`holds` is *checked* against the table actually being submitted rather than
assumed, so a run that began off-lattice (a handed-in `?table=` payload whose
snapped form would fail filters 1-5 starts where it is) reports itself honestly.
The Solan-Vieille seed is already exactly on the lattice; the three chain-best
tables snap onto it without losing legality.

## What a survivor is

A survivor is a table that a bounded, local search over a handful of profile
families failed to settle: a library replay, a stationary grid, one-quitter
cycles, general periodic hazards, and two-quitter schedules, each with finitely
many local optimizations. That is a record of search effort. It is not a proof
that no settling profile exists, and it says nothing about profiles outside
those families. Every apparent survivor in the recorded experiment turned out to
be an optimizer artifact once it was attacked harder. The victory screen says
this in full, every time.

## Files

- `index.html`, `style.css` — shell and saloon palette; no web fonts, no CDNs.
- `js/eval.js` — exact periodic evaluator, filters 1&ndash;5, Nelder-Mead, and a
  local attack battery for mock mode.
- `js/curated_mock.js` — canned curated tables for `?mock=1` only.
- `js/api.js` — portal API client, mock backend, 503 warm-up retries, job polling.
- `js/audio.js` — synthesized WebAudio: bell, per-antagonist stings, draws, drone.
- `js/scene.js` — the canvas stage: gunslingers, chip stacks (solo draws), grudge
  cords (collision stakes), preemption arrows, the pot, and the antagonists.
- `js/moves.js` — the card deck and the legality annotation.
- `js/game.js` — the run state machine: rounds, waves, boss, submission.
- `js/main.js` — DOM layer, nerve bar, timing-strip vignette, overlays, boot.

## Keyboard

`1`&ndash;`5` play the corresponding card, `Enter` rings the bell, `h` opens the
ledger. Nothing needs the keyboard; the mouse plays the whole game.

## Names

The saloon has its own names for the decks it keeps, so what the player reads is
fiction whatever the server calls a table. The server's `id` and `name` still
travel in the submission provenance and are shown in the ledger; a table the
saloon does not recognize gets a stable nickname derived from its id.
