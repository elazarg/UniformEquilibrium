# Review of host-release three-player Nash-lift sign reversal

Reviewer: `CODEX_HAHN`

## Frozen object

Reviewed
`notes/CODEX_SPINOZA__HOST_RELEASE_THREE_PLAYER_NASH_LIFT_SIGN_REVERSAL.md`
at exact SHA-256
`8be2529fa678877e24761ace86b15ba9aad6e990b037a20b2ba7f965a3a918ea`.

## Verdict

**PASS as exact ordinary mathematics and as a sharp adapter no-go.**  The
universal quantifier over all exact terminal Nash profiles of the deleted
three-player game is valid.  The example correctly has global minimum debt
zero and therefore does not address the positive-minimum case.

## Reconstruction

At the supplied source, player `0` Quits at date zero and the other three
players Quit at date one.  The host obtains zero.  Moving the host to date
one changes the terminal coalition to all four players and gives it one;
the three possible pure-time response values are `0,1,0`, so this is an
exact unrestricted cap response with debt one.  Player `1` can improve by
`epsilon` by joining at date zero, while players `2,3` have no positive
debt.  Thus the claimed singleton-host release input is present.

In the deleted game, player `1`'s payoff is `epsilon` exactly on the event
that it belongs to the finite terminal coalition.  Immediate Quit guarantees
`epsilon`, which is also the global upper bound on its payoff; exact Nash
therefore forces participation with probability one.  For players `2,3`,
Never guarantees zero and the prescribed payoff is minus `epsilon` times
their participation probability; exact Nash forces both probabilities to
zero.  Hence every exact deleted-game terminal Nash law, regardless of its
calendar distribution, terminates in coalition `{1}` almost surely.

Restoring the host at date zero pays it zero whether player `1` stops at date
zero or later.  Restoring it at date one pays `-1` only if player `1` stops
at date zero and zero otherwise.  The released action is therefore weakly
worse for every deleted-game exact Nash profile, proving the claimed sign
reversal.

The displayed full-game equilibrium is also correct: `{0,1}` Quit at date
zero and `{2,3}` Never.  Player `0` loses by leaving, player `1` loses by
leaving, and players `2,3` lose by joining.  This proves `D_*=0` for the
regression and keeps its scope honest.

## Falsification checks

- The proof uses terminal participation probabilities, not independence or
  stationary play.  It therefore covers arbitrary behavioral exact terminal
  Nash profiles of the deleted game.
- A player who chooses Never cannot belong to a finite terminal coalition;
  the zero payoff used for players `2,3` is exact even if the opponents never
  terminate.
- The host's restored date-one action ties player `1` only on the event
  `tau=1`; the note accounts separately for `tau=0`, `tau=1`, and `tau>1`.
- The example proves failure of a cap-preserving lift from the supplied
  source data.  It does not prove failure under positive global minimum or
  under a source-to-equilibrium law-displacement bound.

## Exact surviving contribution

The three-player existence theorem cannot consume the singleton-host bubble
even when one may choose *any* exact deleted-game equilibrium: equilibrium
selection can necessarily erase the coalition on which the source host gain
was paid.  The remaining theorem must use the positive-global-minimum/source
law to price that coalition-law displacement, or else produce a different
source-attached response before making the lift.
