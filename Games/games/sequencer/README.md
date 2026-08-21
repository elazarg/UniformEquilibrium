# sequencer — player as attacker

A four-channel step sequencer built as a piece of backline hardware: anodised
panel, silkscreened labels, engraved scale marks, jewel lamps and phosphor
bars. Four hands — Rye, Boone, Cass and Wren — pulse around a loop, and you
drag their bars until nobody in the room would rather break the standoff. When
the room settles you can cut the groove to brass.

Behind the fiction: the pattern is a periodic hazard profile, a settled room is
a profile whose exploitability the portal's engine measures below the kill
threshold 0.02 on the target table, cutting to brass is the engine's rational
snap plus a submission to the shared attacker library, and posting a bounty is
`POST /api/candidates`. Each act keeps its fiction name for its whole flow.

Served by the portal at `/sequencer/`. No build step, no CDN, no install.
`?mock=1` is a rehearsal: everything is answered locally and nothing is ever
recorded. `?table=<urlsafe-base64 JSON>` loads a room handed over from another
game.

## The surface

The machine opens mid-play: a room is already loaded, a pattern is already
running, and the transport is moving before any click. The objective is
engraved on the panel next to the nameplate and never leaves it — "settle the
room — bring the needle to the notch" — with its own linear needle showing the
progress toward it, and it changes state as you get there ("almost — the room
is settling", "the room is quiet — cut it to brass", "on the shelf — take
another room"). Nothing on the play surface states a number or a piece of
domain vocabulary:

* the panel is the tension display — a hot VU wash and scanline grain above,
  settling to a phosphor-green floor as the room comes to rest. It does not
  vibrate: the only motion is a single short judder when a channel actually
  fires, and none at all under `prefers-reduced-motion`;
* the transport button is the VU meter: the arc is how far the room is from
  settling, its colour runs from hot orange to phosphor green, and the notch
  is the settling line;
* each channel strip has a lamp that brightens with that channel's urge to
  break ranks, and the one that would break is marked on the grid with ghost
  strike marks;
* one caption line says who would break and where ("Boone breaks on 2 and 4",
  "Rye would rather wait it out");
* the objective's needle and the transport gauge are the same reading, so the
  goal and the progress toward it are one object, and the needle's track keeps
  a fixed place and width whatever the objective currently says;
* sound is the second channel: each hand has a voice, and the drone's beating
  slows to consonance as the room settles.

Controls are taught by doing — a first-visit nudge and a first-hover hint —
and never printed on the surface.

## The ledger

One quiet corner button, worded and placed like its siblings in the other
games, opens the research view, and it is the only place
this game speaks plainly: the honest statement of what a settled room is and
is not evidence of, the room's real name and id, the raw reward table, the
live client evaluation, the server's own reading and evidence tier, the exact
rational value after hardening, submission ids, and an exact-value editor for
the selected step. Everything out-of-fiction lives there, one click away.

## What is honest here

* Live feedback comes from `evaluator.js`, an in-browser port of the exact
  periodic evaluator. It drives feel only.
* Nothing is recorded until the server engine says so: a settling is confirmed
  by `POST /api/evaluate` at rest, hardened by `POST /api/harden`, and the
  profile enters the shared library through `POST /api/profiles`. Without a
  confirmation there is no celebration and no progression.
* Cutting to brass submits the *snapped* profile when the engine's exact
  rational re-evaluation still kills at the threshold, and claims the `exact`
  tier only then. A rehearsal re-checks its snap in floating point and says so.
* Values the API sanitized (`inf` -> 1e9, `nan` -> null) are treated as "not
  recorded": they never reach a gauge, a ranking, or the settling test.
* With the house unreachable the machine still plays, using a room bundled
  with the page; nothing about it can be recorded, which is what an
  unreachable server already means.

## Files

| file | role |
| --- | --- |
| `index.html`, `style.css`, `app.js` | the play surface and the ledger |
| `evaluator.js` | exact periodic evaluator, ported from the reference script |
| `audio.js` | WebAudio machine: four voices plus a tension drone, wall-clock transport |
| `api.js` | portal API client and the offline rehearsal |
| `vectors.js`, `mockdata.js` | generated data (see `tools/`) |
| `selftest.js`, `selftest.html` | evaluator self-check, browser page |
| `tools/run_selftest.js` | the same self-check under node |
| `tools/gen_vectors.py`, `tools/gen_mockdata.py` | regenerate the generated data |
| `tests/` | the browser checks and their runner and stub servers |

## Checks

```
node Games/games/sequencer/tools/run_selftest.js          # evaluator parity
python3 Games/games/sequencer/tests/run_browser_tests.py  # the six browser checks
python3 Games/games/sequencer/tools/gen_vectors.py        # regenerate vectors.js
python3 Games/games/sequencer/tools/gen_mockdata.py       # regenerate mockdata.js
```

`tests/run_browser_tests.py` drives headless Chrome over six pages, each a real
load of `index.html` with its real module graph: the whole play flow in
rehearsal (including a scan of the play surface for domain vocabulary and raw
floats), every `?table=` arrival shape as a real page load, the real atlas
"Attack it" navigation into this game, the house answering 503, sanitized
`1e9`/`null` values, and the transport with its ghost overlay. It starts the
portal server itself with `--data-dir` on a scratch directory, so no check can
write to `Games/data/`. Point it at a browser with `--chrome PATH` or
`$SEQUENCER_CHROME` if none of the usual locations exist.

If the module graph ever fails to evaluate at all — a stale cached script, a
missing asset — an inline watchdog in `index.html` says so on the panel
instead of leaving an empty machine, and `boot()` is wrapped so that a throw
still leaves a playing machine.

The self-check compares the browser evaluator against 31 hard-coded vectors
whose expected values were produced by
`Experiments/singleton_collision_candidate_search/singleton_collision_candidate_search.py`,
and re-runs that script's identities in JavaScript: non-negative
exploitability, the on-path decomposition, and period-one agreement with a
separately written stationary closed form. None of the checks write to
`Games/data/`; browser harnesses run against a scratch copy, a stub server, or
`--data-dir`.

## Hazard control

The bars are logarithmic over six decades (1 down to 1e-6, silence at the
bottom of the travel); each hairline in a cell is one decade.

Precision is spatial, not modal. While dragging a bar, how far the pointer has
strayed sideways from the slot sets how much of the movement lands: full gain
over the slot, a tenth of it for every 200px pulled away, down to a thousandth.
A dashed tether back to the slot, a halo that closes down as the hand steadies,
and the lit decade band on the bar show it while it happens — no numbers, and
nothing to know in advance.

| gesture | effect |
| --- | --- |
| drag | coarse: the whole range in one bar height |
| drag, pulled sideways | steadier the further out — one tenth per 200px |
| shift-drag / shift-wheel | finer still, multiplying on top of the pull |
| alt-drag (or ctrl/cmd) | finer again, also multiplying |
| wheel | one step up or down |
| double-click | silence the step, or bring it back |
| arrows (with shift, alt) | keyboard nudge at three resolutions |
| PageUp / PageDown | double or halve |
| Home / End | off / full |
| the ledger's value box | type an exact hazard, e.g. `2.5e-4` |
