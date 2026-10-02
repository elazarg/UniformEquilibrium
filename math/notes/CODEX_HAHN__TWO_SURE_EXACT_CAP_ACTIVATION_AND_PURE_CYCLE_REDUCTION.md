# Two sure clocks allow exact activation of every spectator, but only reduce to the pure response-cycle waist

Author: `CODEX_HAHN`

## Status

**Exact ordinary mathematics; source-preserving reduction, not Lean-checked
and not a terminal consumer.**  A two-sure exact-cap response orbit need not
retain a proper active set.  Before selecting positive-gap moves, one may
replace each non-pure spectator by a finite pure-time exact cap response,
even when that spectator has zero debt.  In Fin4 at most two such preparatory
updates are needed.

The resulting profile is pure-clock and has literal finite replacement
ancestry from the same source.  The existing canonical pure-clock response
map then gives a pure minimum hit or an entirely off-minimum finite response
cycle.  Thus the fixed-spectator Never cylinder is useful extra data for a
particular selector, but it is not an unavoidable residual of the two-sure
source.

This reduction does not preserve a previously marked paid row through the
preparatory updates and does not consume the resulting horizontal cycle.

## 1. Self-contained activation theorem

Let `I=Fin 4` and let `P` be an actual behavioral profile in a bounded
quitting game.  Suppose two distinct players use deterministic finite
stopping times in `P`.

For every player `i`, player `i`'s unrestricted behavioral cap against
`P_{-i}` is attained by a deterministic finite pure stopping time.

Indeed, at least one of the two sure-clock players is distinct from `i`.
Call it `a`, and let its deadline be `H`.  Under every unilateral deviation
of `i`, player `a` still Quits by `H`.  Against the fixed opponents, every
random behavioral response of `i` is a probability distribution over pure
stopping times and Never, so its payoff is a convex combination of the
corresponding pure-time values.  Times later than `H` and Never are all
outcome-equivalent, because the game has already stopped at or before `H`.
The cap is therefore the maximum of the finite menu of pure times through
`H+1`, and is attained by a finite pure time.

Replacing `i` by such an attainer has exact gain `d_i(P)>=0` and sets the
new own debt to zero.  If `i` was not already a deterministic finite-clock
player, one of the original two sure-clock players remains unchanged and
the mover becomes a second sure-clock player.  Thus the hypothesis
regenerates.

Apply this operation successively to the at most two coordinates which are
not deterministic finite clocks.  One obtains an actual pure-clock profile
`Q` after at most two literal unilateral replacements.  Every preparatory
edge is an exact unrestricted cap response, has nonnegative gain, and its
target is literally the next source.

## 2. Source and gap bookkeeping

Suppose `P` has finite unilateral-replacement ancestry from an actual source
`X`.  Appending the preparatory updates gives the same kind of literal finite
ancestry from `X` to `Q`; no carrier representative or unrelated profile is
selected.

If the reward table has a terminal exploitability gap `Gamma>0`, that is a
table-wide statement and therefore still applies at `Q` and at every later
profile.  The zero-gain preparatory steps do not weaken it.  Starting at `Q`,
the canonical pure-clock selector may at every node choose a maximum-debt
player and an inherited-alphabet exact response.  In Fin4 each selected
response gains at least `Gamma` (or at least `D_*/4` when that is the chosen
global gap normalization), and the checked finite-alphabet argument reaches
within `6^4` steps either:

1. an actual pure-clock profile on the global minimum-debt fibre; or
2. a literal entirely off-minimum exact unrestricted-response cycle.

Absolute deadline drift is absent from this canonical horizontal reduction.
For a pure-clock profile a cap attainer can be chosen from immediate Quit,
the earliest finite opponent deadline, and Never.  These choices stay in the
finite alphabet inherited from `Q`, together with `0` and Never.  An
alternative selector may represent Never by successively later finite
clocks, but that is only a noncanonical calendar representation of the same
horizontal response region.

## 3. What is and is not preserved

The activation preserves:

- the reward table and its positive terminal gap;
- actual behavioral profiles;
- literal target-to-next-source equality for the preparatory edges;
- finite replacement ancestry from the incoming source; and
- complete unrestricted cap attainment on every preparatory edge.

It does **not** preserve a paid first-disagreement row previously marked in
`P`.  Replacing a spectator can alter the reach probability, conditional
opponent law, and gain at that old row.  The later pure-clock response edges
have fresh exact gains and fresh first-disagreement rows, but these are not
the same passport.

Accordingly this theorem may be used for the source-faithful finite response
cycle reduction.  It may not be used where the downstream consumer requires
the original marked row, its receiving time, or its post-mark tail to survive
unchanged.

## 4. Consequence for the active-set split

For a fixed chosen orbit, active-set stabilization and the escaping-cut
argument correctly produce an actual fixed-spectator Never cylinder.  The
present theorem shows that this proper-active branch is selector-dependent:
one can instead activate every spectator exactly before beginning the
positive-gap response selection.

After this normalization the genuine residual is the already known one:

```text
actual two-sure source
  -> at most two exact nonnegative cap updates
  -> actual pure-clock source
  -> pure minimum hit or finite off-minimum exact-response cycle.
```

The near-minimum family of cycles enters the checked minimum-chord/support
contraction.  A uniformly off-minimum family enters the checked signed
source-retraction/paid-port arm.  Neither output is a new terminal consumer.

## 5. Boundary tests

1. **The activated player may have zero debt.**  Then the preparatory update
   has zero gain, but exact cap attainment and pure-clock insertion remain
   valid.  Strict gain is unnecessary for activation.
2. **The activated player may be one of the original sure players.**  The
   existence proof still has the other sure player as a screen.  For the
   at-most-two-step normalization one only needs to activate nonsure players.
3. **Never as a cap maximizer.**  It is represented by the finite time
   `H+1`, where `H` is one unchanged sure opponent's deadline.  This is
   outcome-equivalent for the mover's response problem.  It is not asserted
   to preserve every other player's cap under subsequent deviations.
4. **Loss of the marked row.**  A newly activated spectator can Quit before
   an old paid mark and screen it completely.  Hence ancestry alone cannot
   be upgraded to marked-passport preservation.
5. **No temporal interpretation.**  Preparatory and canonical arrows are
   external complete-strategy replacements, not live dates of one
   Nash--Bellman chronology.

## Sources inspected

- `notes/CODEX_SPINOZA__RECENTERED_PAID_TAIL_EXACTIFIES_TO_TWO_SURE_RESPONSE_ORBIT.md`;
- `notes/CODEX_SPINOZA__TWO_SURE_CAP_ORBIT_ACTIVE_SET_AND_ESCAPING_CUT_RECENTERING.md`;
- `formalized/FIN4_FINITE_PURE_CLOCK_EXACT_RESPONSE_CYCLE.md`;
- `formalized/FIN4_SIGNED_SOURCE_RETRACTION_AND_NEAR_MINIMUM_RESPONSE_CYCLE_CONTRACTION.md`;
- `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticFinitePureTimeResetArrival.lean`, especially `exists_pureTime_bestReply_of_opponent_quitsAt`;
- `UniformEquilibrium/Diagnostics/Quitting/PureTimeCapAttainment.lean`; and
- `UniformEquilibrium/Diagnostics/Quitting/PureTimeSelectedExactResponseOrbit.lean`.

## Next exact question

Can the fresh first-disagreement row of the uniformly off-minimum pure
response cycle be aligned with the incoming marked source before spectator
activation, or can positive minimum debt orient the finite cycle without
using any preserved old mark?  Without one of those genuinely global inputs,
the all-pure normalization reaches the same paid-port SCC rather than closing
it.

