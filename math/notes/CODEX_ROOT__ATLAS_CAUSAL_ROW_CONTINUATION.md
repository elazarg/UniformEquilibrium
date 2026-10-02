# Fin4 atlas causal-row continuation

Author: `CODEX_ROOT`

## Status

Research question and candidate reduction, not a proved theorem.  The
geometric step is exact; the quantitative/source-preserving consumer is open.

## Question

Start with an actual Fin4 atlas endpoint carrying:

- an actual profile `sigma`;
- a marked date `t`;
- a nonempty pure quitting coalition `A` at that date with unconditional
  stage mass at least `lambda > 0`; and
- literal equality of the complete live-root tail after `t` with the selected
  atlas tail.

Can one continue the pure same-stage endpoint dynamics from this row and
prove, without changing the source tail, one of:

1. an exact terminal Nash profile;
2. quantitative tail escape at the selected minimum scale;
3. a common-host or complementary-pair monodromy producer; or
4. a source-preserving well-founded descent?

The desired conclusion is about unrestricted behavioral deviations.  A
finite toggle orbit alone is not enough.

## Exact finite mechanism

At a nonempty pure root `A`, a pure endpoint update by player `i` replaces
`A` by `A △ {i}` and preserves the complete post-date tail literally.  If
the new coalition is nonempty, absorption at the marked row remains certain
conditional on reach.  Hence all later behavior of the mover is irrelevant
for that row and the endpoint gain is a literal one-row behavioral gain.  A
finite iteration of such nonempty toggles therefore has only three finite
outcomes:

- a root with no profitable toggle;
- a repeated nonempty coalition, hence horizontal monodromy; or
- a singleton whose owner is profitably removed, producing the empty
  all-Continue root and exposing the preserved tail.

The first case is a terminal Nash only when the root comparison uses the
correct behavioral continuation cap.  In the singleton-removal case the
owner's Continue value must likewise use the full cap of the preserved tail,
not merely its prescribed payoff.

This suggests a directed reduction

```text
concentrated singleton
  -> exact terminal Nash / tail escape / monodromy,
```

which would merge the concentrated node into the other two remaining atlas
nodes.  It is not yet proved by the checked atlas interface.

## Why the obvious proof is incomplete

The current concentrated endpoints supply a literal target row and tail, but
not in every origin a cap-Nash certificate for the target-side copied prefix.
In particular, the owner-compressed origin from
`FIN4_MINIMUM_SINGLETON_CLOCK_COMPRESSION.md` changes the suffix seen by the
copied exact source stack.  Exactness of that stack remains source-side only.

Moreover, removing the last quitter changes a sure-exit row into an
all-Continue row.  The resulting gain is governed by the mover's unrestricted
tail cap.  An endpoint comparison against the prescribed tail payoff cannot
justify the transition.  Approximate cap attainment may escape to arbitrarily
late dates, so a bounded-time substitute is invalid.

## Potential quantitative route

For the singleton owner `j`, opponents are unchanged by any pure-time
replacement, so its cap is exactly preserved.  Its source payoff is a convex
combination of pure-time values against those opponents.  Simultaneously, its
singleton terminal mass is the same stopping-law average of the opponents'
survival weights.  A two-coordinate selection argument may therefore give:

```text
a high-survival pure time with small owner payoff loss
or
a source-matched paid early/late pure-time pair.
```

The second branch would carry the nonlocal timing information that a raw
toggle loses.  The first branch still needs cross-coordinate cap control:
changing `j`'s stopping law can alter every other player's unrestricted cap
by order one.  Whole-stopping-law debt convexity or a minimum-fiber normal
cone is the likely source of that control, but no such estimate is proved
here.

## Inspected declarations

- `FinFourAtlasConcentratedSingletonEndpoint` in
  `Research/Quitting/FinFourProducerAtlas/SemanticConnections.lean`;
- `QuittingTerminalExploitabilityWitness.concentratedSingletonStrategicDispatch`
  in `Research/Quitting/ConcentratedSingleton/StrategicDispatch.lean`;
- `exists_concentrated_singleton_or_tailEscape_or_otherDefect` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticResetReprojectionConcentratedConsumer.lean`;
- `quittingLiteralOneDateProfile` and the same-stage routing declarations
  used by `FIN4_MINIMUM_SINGLETON_CLOCK_COMPRESSION.md`; and
- `minimumTerminalSemantic_is_allContinuePlateau` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticAuxiliaryNashBudget.lean`.

## Next check

Formulate the two-coordinate stopping-law selection lemma with an explicit
payoff-loss parameter, then test whether the atlas minimum-fiber convexity
identities bound the other three debt coordinates along the selected
one-player chord.  A useful result must either complete the reduction above
or produce a paid row with stronger source/atom alignment than the paid row
already available at every profile.
