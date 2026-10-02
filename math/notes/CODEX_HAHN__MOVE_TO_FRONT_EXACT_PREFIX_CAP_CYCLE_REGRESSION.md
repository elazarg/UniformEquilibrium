# Exact-prefix move-to-front cap installations can cycle

Author: `CODEX_HAHN`

## Status

**Exact ordinary mathematics; local regression, not Lean-checked.**  Two
owners can alternate indefinitely in a two-phase construction where every
vertical step is a positive-survival exact product root and every horizontal
step installs the mover's attained shifted cap strictly ahead of the retained
owner clock.  Two distinct finite sure clocks persist, and the complete
terminal-semantic pair returns exactly after every two phases.

The table has an exact terminal equilibrium and global minimum debt zero.  It
therefore refutes only clock-order or move-to-front ranks which ignore the
positive-global-minimum hard residual.  It is not a counterexample to uniform
equilibrium and supplies no conjecture-facing consumer.

## Question

Does the special renewal geometry, in which each new shifted cap clock is
installed before every retained clock, give a well-founded clock-order rank?

## 1. Reward table

Use players `0,1,2,3`.  On coalitions not containing player 3, define the
nonzero rewards as follows; all omitted coordinates and coalitions are zero:

| coalition | `r_0` | `r_1` |
|---|---:|---:|
| `{0}` | `1` | `0` |
| `{1}` | `0` | `1` |
| `{2}` | `1` | `3/4` |
| `{0,1}` | `0` | `-1` |

In particular, the rewards of both players on `{0,2}`, `{1,2}`, and
`{0,1,2}` are zero.  Players 2 and 3 receive zero everywhere.  Every
coalition containing player 3 has zero reward vector.  All entries lie in
`[-1,1]`.

Let `S` be the deterministic profile in which everybody Continues at date
zero, player 0 Quits at date one, and the other players Never Quit.

Let `qA` be the product root at which player 0 Quits with probability `1/2`
and everyone else Continues.  Let `qB` be the product root at which player 2
Quits with probability `1/2` and everyone else Continues.

## 2. First move-to-front phase

At `S`, the prescribed terminal coalition is `{0}`.  Player 1 gets zero, but
Quit0 gives one, so Quit0 attains player 1's complete cap.

The root `qA` is exact Nash against `U(S)`:

- player 0 is indifferent because both its current Quit payoff and tail
  payoff are `1`;
- player 1's Quit endpoint is
  `(r_1({0,1})+r_1({1}))/2=0`, equal to its Continue payoff; and
- players 2 and 3 are indifferent at zero.

Prefix `S` by `qA` and install player 1's shifted Quit0 cap: player 1
Continues through `qA` and Quits at the next date.  Call the result `B`.
The prescribed law of `B` gives mass `1/2` to `{0}` and `1/2` to `{1}`, so

\[
 U(B)=(1/2,1/2,0,0).
\tag{1}
\]

Player 0's complete cap at `B` is `1`, attained by Quit0.  The next root
`qB` is exact Nash against (1).  For player 0 its Continue and Quit endpoints
are respectively

\[
 \tfrac12 r_0(\{2\})+\tfrac12 U_0(B)=\tfrac34,
 \qquad
 \tfrac12 r_0(\{0,2\})+\tfrac12 r_0(\{0\})=\tfrac12.
\]

For player 1 they are

\[
 \tfrac12 r_1(\{2\})+\tfrac12 U_1(B)=\tfrac58,
 \qquad
 \tfrac12 r_1(\{1,2\})+\tfrac12 r_1(\{1\})=\tfrac12.
\]

Player 2 is indifferent at zero and player 3 is also indifferent.  Thus
`qB` is exact, with joint survival `1/2`.

Prefix `B` by `qB` and install player 0's shifted Quit0 cap.  Call the result
`A_0`.  Player 0 now Quits one date after `qB`, while player 1's retained
clock is one date later.  Hence the new clock has moved strictly to the front.
The prescribed law gives mass `1/2` to `{2}` and `1/2` to `{0}`, so

\[
 U(A_0)=(1,3/8,0,0).
\tag{2}
\]

## 3. The reverse phase and exact semantic return

At `A_0`, player 1's complete cap is `1/2`, attained by Quit0: if player 2
Quits at `qB`, joining it gives zero, and otherwise player 1 Quits alone for
payoff one.  Continuing gives the prescribed payoff `3/8`; joining player 0
one date later gives `-1`, and waiting beyond player 0 gives zero.

The root `qA` is exact Nash against (2).  Player 0 is indifferent between
Quit and Continue at value one.  Player 1's Continue endpoint is `3/16`,
while its Quit endpoint is zero.  The other two players are indifferent at
zero.

Prefix `A_0` by `qA` and install player 1's shifted Quit0 cap.  Call the
result `B_0`.  Player 1 is now the first sure clock and player 0 is the
retained second sure clock.  Its prescribed law is

\[
 \tfrac12\delta_{\{0\}}
 +\tfrac14\delta_{\{1,2\}}
 +\tfrac14\delta_{\{1\}},
\]

and hence

\[
 U(B_0)=(1/2,1/4,0,0).
\tag{3}
\]

At `B_0`, player 0's complete cap is again one, attained by Quit0.  The root
`qB` is exact Nash against (3): player 0's Continue and Quit endpoints are
`3/4` and `1/2`, player 1's are both `1/2`, and players 2 and 3 are
indifferent at zero.

Prefix by `qB` and install player 0's shifted Quit0 cap.  Call the result
`A_1`.  Its prescribed law and payoff are exactly those in (2).  More is
true:

\[
 \operatorname{Sem}(A_1)=\operatorname{Sem}(A_0).
\tag{4}
\]

For player 0 the installed cap and prescribed payoff are both one.  For
player 1, both profiles expose the same first root `qB`; after its survival,
player 0 Quits at the next root.  If player 1 deviates at that next date it
gets `r_1({0,1})=-1`, and if it waits it gets `r_1({0})=0`.  Hence its full
response problem, including Never, is the same.  Players 2 and 3 have
identically zero payoff under every deviation.  Thus all four unrestricted
caps, as well as prescribed payoffs, agree.

The construction may now repeat from `A_1`.  At every horizontal update the
new owner's sure clock is strictly before the retained owner's clock.  The
ordered pair of clock owners nevertheless alternates

```
(0 before 1) -> (1 before 0) -> (0 before 1) -> ... .
```

Each vertical root has joint survival `1/2`, and the source semantic pair
returns exactly every two phases.

## 4. The example is outside the hard residual

Let player 3 Quit at date zero and let everyone else Never Quit.  Every
coalition containing player 3 has zero reward vector, and the all-Never
payoff is also zero.  No unilateral deviation gains.  This is an exact
terminal Nash profile, so the global debt minimum is zero.

Therefore (4) does not refute a possible rank using positive minimum debt,
the Fin4 terminal gap, or punishment-floor structure.  It proves that none
of the following data alone supplies such a rank:

- two persistent finite sure clocks;
- strict move-to-front clock installation;
- positive-survival exact vertical roots;
- attained complete cap updates; and
- exact recurrence of the displayed terminal-semantic pair.

The vertical roots and horizontal cap changes still have opposite temporal
incidence: the response target is the successor endpoint of the next
reverse-nested exact block, not its predecessor.  The example realizes that
orientation failure rather than resolving it.

## Source correspondence and nonclaims

The general two-clock response-cycle regression is
`CODEX_GROMOV__TWO_SURE_CLOCK_FINITE_RESPONSE_CYCLE_NOGO`.  The present table
adds the special positive-survival exact-prefix and strict move-to-front
geometry of `CODEX_HAHN__LATE_RESET_RENEWS_ESCAPING_CAP_CLOCK_SOURCE`.

This note is not Lean-checked.  It does not satisfy positive global minimum,
the no-uniform-payoff hypothesis, the terminal-gap source passport, or the
law-tight tropical entrance.  It supplies no terminal consumer and should
not be exported as conjecture progress.

## Next exact question

Which positive-minimum global invariant forbids the exact two-phase semantic
return (4), or turns it into an admissible paid return, when each source also
carries the renewed terminal-gap passport?
