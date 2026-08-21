# breeder — pick the ones you like

A 3x3 pen of creatures. Each creature *is* a four-player quitting reward
table (see `Games/DESIGN.md`), drawn as a procedural organism: the shape, the
limbs, the coloring, and the breathing are all read off the table's
structure, never typed in by hand. The player only needs taste — every score
that matters comes from the shared engine, never from the client.

## Running

Served by the portal (`python3 Games/serve.py`, then `/breeder/`). Works
standalone under `?mock=1` with canned contract-shaped responses, no server
needed. Accepts `?table=` (urlsafe-base64 JSON, the wire format below) as an
injected parent for generation 0.

## The goal

DESIGN.md's "the goal is always visible" rule: a persistent banner
(`#goal`, top-left, mirroring the ledger door at top-right) states the
objective in-fiction — "breed one the lab will take" — with a ring gauge
(`#goalRingFill`) as the only progress indicator, filling toward this
session's strongest not-yet-taken specimen's proximity to the kill line.
No number is ever shown; the ring and the per-cell aspiration star
(`.leading-badge` on the strongest current specimen) are the whole signal.
When a specimen is actually taken, the banner celebrates and re-arms with
"the lab wants more," then settles back to the standing objective — same
vocabulary chain as the lab badge and the toast ("the lab wants this one" ->
"taken to the lab" -> "the lab wants more").

## What is honest here

Every score shown anywhere — on a creature's aura, in a toast, in the ledger
— is the shared engine's answer to `POST /api/attack` or `/api/attack_batch`,
never a client-side estimate. `POST /api/filters` (or its `?mock=1` stand-in
in `js/filters-mock.js`) decides which offspring are even legal to show;
illegal ones are discarded before the player ever sees them. Nothing is
recorded until the server re-scores it: `POST /api/candidates` is the only
path onto the ledger, and it happens automatically the moment a specimen
clears the kill line at both the quick and standard attack levels.

The play surface speaks only the pen/lab fiction (full diegesis, per
`Games/DESIGN.md`) — no "exploitability", "profile", "tier", "0.02", no raw
table. The one dedicated door out of the fiction is **the ledger**
(`#hoodBtn`): it shows the real tables, real scores and tiers, per-round
rejection counts by (opaque) filter name, and this file's
disclaimer paragraph verbatim. It never claims a surviving specimen is a
counterexample, and it never implies the restriction below is coverage of
the whole space.

## Phenotype mapping (table structure -> creature)

Deterministic in the table's contents only (`util.hashTable` seeds the small
decorative PRNG), so the same table always draws the same creature, and
structurally similar tables draw similarly — that's what lets taste
correlate with search at all.

- **Preemption digraph** (edge `i -> j` when `r_j(j) >= r_i(j) + 0.1`, the
  same margin the engine's filters use): a player's out-degree becomes the
  number of antler-like forks at their limb tip; in-degree becomes limb
  thickness; every edge draws a dashed tendril between limb tips. A viable
  owner able to reach a cycle in this digraph (the structural condition
  behind filter 4) draws a slow rotating halo around the body.
- **Solo-self reward** `r_i(i)`: that player's limb length (magnitude) and
  hue (moss-green near zero, warmer for positive, cooler for negative).
- **Overall diagonal magnitude/sign**: body size and body hue/lightness.
- **Size-3 coalition sign patterns** (the four rows with three quitters):
  number of distinct patterns becomes the count of skin spots.
- **Viable-owner count** (filter 2's condition, `r_i(i) > -0.1`): eye count.
- **Quick-attack score vs. the kill line**: a tier band (thriving / wary /
  about to fall) that drives an outer glow (aura), breathing rate and
  amplitude, and — only in the critical band — a grain flicker or a wobble
  jitter plus limb droop. This is the confidence rendering DESIGN.md asks
  for; it is never rendered as "this is a counterexample."
- **Binding attack name**: a small predator-icon badge (ghost / spider /
  wolf / eagle / snake for `library_replay` / `stationary` /
  `one_quitter_cyclic` / `two_quitter_periodic` / `general_periodic`).
- **Auto-submission**: a specimen that clears the kill line at the standard
  level gets a persistent flask badge — visually, "the lab wants this one";
  narratively, it has been "taken to the lab."

## Genetics (`js/genetics.js`)

- **Mutation** (`mutateRows`): perturbs 1-6 table entries by a small,
  occasionally large, whole number of lattice steps (see restriction below).
- **Collision strengthening** (`strengthenCollision`): pushes one member of a
  chosen multi-player coalition to clearly win that collision — a sharper
  preemption edge, i.e. a visibly different limb.
- **Role permutation** (`permuteRoles`): relabels all four players by a
  random permutation, remapping the coalition bitmask and the payoff column
  consistently, so an isomorphic table renders as a similarly-shaped
  creature.
- **Crossover** (`crossover`): per coalition row, inherits one parent's row
  whole or blends the two (averaged, then lattice-snapped).

`spawnCandidates` mixes these across a batch of 9 pre-filter candidates from
1-2 selected parents; illegal ones (checked via `POST /api/filters`) are
silently discarded and regenerated until 9 legal offspring are collected or
an attempt budget is spent.

## Subspace restriction (DESIGN.md "restriction is allowed — with a reason")

Every value this file *writes* — mutation deltas and blended crossover
values — is snapped to a **1/8 lattice** (`LATTICE_STEP = 0.125` in
`genetics.js`). Whole-row-inherited crossover rows and the curated seed
tables keep their original precision; the lattice applies only to freshly
generated values.

**Reason:** the phenotype map above is deliberately continuous in the
table's numbers (limb length, hue, body size all move smoothly with
magnitude), which is what makes "this looks like that" a workable proxy for
"this table is structurally like that one." An unrestricted mutation can
jump a payoff anywhere in `[-4, 4]` in one step, which breaks that
continuity: a "child" can look nothing like its parent even though one
number moved. Confining generated values to a shared, visible step size
keeps a lineage legible as a family and keeps taste-driven search doing real
work instead of fighting noise. It is not claimed to help find
counterexamples faster than an unrestricted search would — only to make the
*game* work, which is the whole point of a taste-driven surface.

Every auto-submitted candidate's provenance is stamped
`subspace: { lattice: 0.125 }` (see `app.js`'s `checkAutoSubmit`), so any
downstream reader of `Games/data/candidates.jsonl` knows the region actually
searched. The restriction is surfaced in the ledger (`.restriction-note` in
`index.html`) and is never presented there or anywhere else as coverage of
the unrestricted table space — a subspace with no survivors says nothing
about the rest of it.

## Files

- `index.html`, `style.css` — the pen (light "terrarium" theme: moss, glass,
  soft daylight), the ledger drawer, toasts.
- `js/util.js` — hashing/PRNG, `?table=` decode, generic helpers.
- `js/tablemath.js` — shared structural readings (preemption edges, viable
  owners, iterated-normal core, owner-reaches-cycle) used by both the
  phenotype and the mock filters.
- `js/filters-mock.js` — best-effort JS port of filters 1-6 for `?mock=1`
  only; the real legality gate is always `POST /api/filters`.
- `js/genetics.js` — mutation/crossover operators and the lattice
  restriction.
- `js/creature.js` — table -> SVG phenotype.
- `js/lineage.js` — champion-path persistence and the borderless filmstrip.
- `js/api.js` — real API wrappers plus `?mock=1` canned responses (the
  curated mock tables are literal conversions of the actual Solan-Vieille
  seed and the three chain-best tables in
  `Experiments/singleton_collision_candidate_search/results.json`, not
  invented data).
- `js/app.js` — generation loop, selection/breeding, auto-submission, the
  ledger panel.

## Checks

No build step. `node --check` on each `js/*.js` file catches syntax errors;
there is no project-owned test harness inside this game folder (the shared
engine's own tests live under `Games/engine/tests/`, run from the repo's
`Games/` directory, not from here).
