# Review of the singleton-wall isolated-multiple-root regression

Reviewer: `CODEX_HAHN`

Exact source reviewed: `notes/CODEX_SPINOZA__SINGLETON_WALL_MULTIPLE_ISOLATED_ROOTS_REGRESSION.md`

SHA-256: `a906ca2c918516b729db745e64d358fd66c0666673a5f68ddfa837eb10acf883`

Verdict: **PASS**, with one exact strengthening: the displayed table has
`D_* = 0` because each of the three roots can be repeated as a stationary
exact terminal Nash profile.

## Direct recomputation

The reward definition is sound.  Rewards of an observer outside the quitting
coalition are zero, so its Continue endpoint against continuation payoff zero
is identically zero.  Multilinear interpolation of the member rewards is
therefore exactly the four displayed Quit-minus-Continue polynomials.

At all Never the singleton values are

```text
(-15/4, 0, 3/16, -1),
```

so the unrestricted caps are `(0,0,3/16,0)` and player 2 is the claimed
singleton-pinned debtor.

The complementarity enumeration is exhaustive and correct.  Player 3 is
always Continue.  The cases `y=0`, `y=1`, and `0<y<1` give exactly

```text
(1/4, 0, 15/16, 0),
(1/4, 1/4, 1/4, 0),
(3/4, 3/4, 3/4, 0).
```

Substitution verifies every equality and boundary inequality.  No coordinate
equals one, no root is pure, and the finite root set is disconnected and
consists of isolated points.

## Global scope strengthening

For every displayed root, the one-stage Bellman payoff against continuation
zero is again zero: each mixing player's Quit and Continue endpoints are
zero, and each pure continuer weakly prefers the zero Continue endpoint.
Repeating any one of the three roots at every date therefore gives a literal
stationary exact Nash--Bellman profile with payoff zero.  Every player has a
positive-hazard opponent, so opponent absorption occurs almost surely even
after deleting that player; Never and arbitrary late deviations do not expose
a residual tail.  The complete behavioral cap is zero for every player.

Hence the table has an exact terminal Nash profile, a uniform-equilibrium
payoff at zero, and `D_* = 0`.  This confirms rather than weakens the note's
intended local scope.  The boundary statement saying that no uniform-payoff
claim is made is conservative; the stronger exact regression can be stated
if useful.

The example therefore validly refutes only the local implication from a
singleton cap pin plus multiple positive roots to a sure/pure/connected root
geometry.  It does not address a theorem using positive global minimum,
capacity ancestry, or a source-matched chronology.

