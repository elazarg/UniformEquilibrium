# Review of two renewed sure clocks

Reviewer: CODEX_GROMOV

Reviewed exact SHA-256:
`0aae1de8d4dafa8e19e33d927156aefd727c6f165def3985e8b986cbf1667d07`

## Verdict

**PASS as a semantic adapter, not a consumer.** Two distinct prescribed sure
finite clocks allow every strategy to be truncated after their common
deadline without changing the prescribed terminal law, any prescribed
payoff, or any player's unrestricted behavioral cap. The renewal argument
really accumulates and preserves those two clocks after two distinct cap
installations.

The note's warning about sequential cap attainment is essential. The two-
clock property by itself does not prevent an exact full-response cycle, even
when the two clocks remain fixed and sure throughout the cycle.

## Exact finite-clock regression

The following embeds the checked four-step response-cycle table into profiles
with two permanent sure clocks.

For coalitions contained in `{0,1}`, use

```
             {0}   {1}   {0,1}
player 0:      1     1       0
player 1:      0    -1       1
```

Set players 2 and 3's coordinates to zero, and set the whole reward vector to
zero for every coalition containing player 2 or player 3. Fix `H>=1`. Players
2 and 3 always Quit at date `H`. Then the pure-clock profiles

```
(H+1,H+1,H,H)
 -> (0,H+1,H,H)
 -> (0,0,H,H)
 -> (H+1,0,H,H)
 -> (H+1,H+1,H,H)
```

form a literal exact unrestricted-best-response cycle, with movers
`0,1,0,1` and gain one on every edge.

- At the first state, player 0 obtains zero from the `{2,3}` clock and obtains
  one by Quit0.
- At the second, player 1 changes the `{0}` outcome of value zero into the
  simultaneous `{0,1}` outcome of value one.
- At the third, player 0 changes value zero at `{0,1}` into value one at
  `{1}` by waiting past date zero.
- At the fourth, player 1 changes value `-1` at `{1}` into value zero by
  waiting past the permanent `{2,3}` clock.

Each displayed response attains the complete cap: the two fixed sure clocks
make everything after date `H` outcome-equivalent, and direct inspection of
the finitely many regions before, at, and after the first opponent deadline
gives the stated maxima. Every profile in the cycle has two distinct sure
finite clocks. The table still has an exact equilibrium (for example player 2
Quits at date zero and all other players Never), so its global minimum debt is
zero.

This does not falsify the positive-minimum renewed source. It does falsify any
local implication

```
two sure finite clocks + exact sequential cap attainment
  -> terminal Nash or convergent response dynamics.
```

Any consumer must use the positive-global-minimum/no-uniform-payoff source
structure or the special move-to-front geometry of the renewed cap clocks,
not finite complete semantics alone.

## Delta review of frozen revision

Frozen exact SHA-256:
`e596e78d2476e72d7cc561a77b4b7507c24a3ac682dc69946ffc23629bbc735d`

**PASS.** The only material clarification strengthens the bookkeeping from
the earlier provisional inclusion to `G_m ⊆ G_(m+1)`: installing a cap changes
only the current owner, and that owner is itself assigned a finite sure clock,
so no existing sure-clock label is lost. The truncation theorem, semantic
scope, and nonconsumer boundary are unchanged. The response-cycle regression
above applies unchanged to this frozen revision.
