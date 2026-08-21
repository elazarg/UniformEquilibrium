# atlas

A living survey map. Pick three anchor tables A, B, C and atlas sweeps the
plane `table(x, y) = clamp(A + x(B-A) + y(C-A))` for `(x, y)` on and around
`[0,1]^2`, painting each patch of the plane by whichever attack family killed
it, with a wandering "still wild" glow for patches that survived the pass.

## Subspace restriction (DESIGN.md "restriction is allowed — with a reason")

Reward tables live in a 60-dimensional box (16 coalitions x 4 players). Atlas
deliberately restricts every session to the 2-parameter plane
`table(x, y) = clamp(A + x(B-A) + y(C-A))` through three chosen anchor tables,
rather than searching that whole space directly.

**Reason:** a plane is what a human can actually see and paint in one
sitting — pan across it, zoom into it, watch it resolve. Anything with more
free parameters stops being something a player can look at and just becomes
numbers again, which is the opposite of the point. It is a UX restriction,
not a claim about where counterexamples can or cannot live; nothing here
should be read as "the interesting region is a plane."

Every claim staked from atlas records the three anchor ids and the `(x, y)`
coordinate that produced it in its submission provenance, so the restriction
actually searched is always recoverable downstream. The restriction is
surfaced in the ledger for every selected patch (which anchors, which
coordinate) and is never presented there or anywhere else as coverage of the
unrestricted table space.

## Playing

Load it; it starts scouting immediately with a default trio of anchors. Pan
and zoom the map, tap a patch of ground to bring up its card, then rig it,
attack it, or claim it. The single "the ledger" affordance in the corner
opens the ledger: the real reward table, the real score and evidence tier,
which three anchors and which coordinates a claimed patch came from, and the
project's honesty statement about what any of this is (and is not) evidence
of. Nothing outside that panel uses the solution domain's vocabulary.

Run via the portal (`python3 Games/serve.py`) at `/atlas/`. Query params:
`?mock=1` for an offline demo with a synthetic field standing in for the
server (a badge says so on screen); `?a=`/`?b=`/`?c=` (urlsafe-base64 JSON
tables, falling back to a bare `?table=` for slot A) to hand in anchors —
this is how a "rig it"/"attack it" round trip and cross-game handoffs work.

## Files

- `index.html`, `style.css` — the map, the ledger drawer, the coach mark and
  toast, styled as survey-chart parchment (aged paper, a printed grid, a
  slow rotating sweep line, an ink-blot ping on every patch that resolves) —
  the same material the portal's own atlas poster tile promises.
- `api.js` — real API wrappers plus the `?mock=1` switch and urlsafe-base64
  helpers.
- `mock.js` — canned contract-shaped responses (the real Solan-Vieille seed
  table plus synthetic stand-ins) for offline demo mode.
- `atlas.js` — the quadtree/scheduler engine, camera, rendering, and all UI
  wiring in one file; every recorded score comes from the shared engine via
  `POST /api/attack_batch`, never a client-side estimate.
