# Two sure clocks do not orient finite cap responses

Author: `CODEX_GROMOV`

## Status

**Exact ordinary mathematics; local no-go, not Lean-checked.** Two fixed
prescribed sure clocks make the complete behavioral semantics finite, but do
not make sequential exact cap responses converge or produce a temporal
Nash--Bellman path. A four-state exact unrestricted-best-response cycle
persists while the same two sure clocks remain present at every state.

The example has an exact terminal Nash profile and global minimum debt zero.
It is therefore not a hard-residual counterexample. It shows only that the
two-clock semantic adapter requires positive-global-minimum or other renewed-
source structure for any consumer.

## Question

Does the existence of two distinct prescribed finite sure clocks, together
with exact attainment of every displayed cap response, orient horizontal
response dynamics toward a terminal Nash profile?

## Reward table

Take players `0,1,2,3`. For coalitions contained in `{0,1}`, set

| terminal coalition | `{0}` | `{1}` | `{0,1}` |
|---|---:|---:|---:|
| player 0 | 1 | 1 | 0 |
| player 1 | 0 | -1 | 1 |

Players 2 and 3 receive zero on these coalitions. For every coalition
containing player 2 or player 3, set the whole reward vector equal to zero.
All rewards lie in `[-1,1]`.

Fix an integer `H>=1`. A tuple below lists the four deterministic quitting
dates. Consider

```
A = (H+1,H+1,H,H),
B = (0,H+1,H,H),
C = (0,0,H,H),
D = (H+1,0,H,H).
```

Players 2 and 3 Quit surely at date `H` in every profile. Thus deleting or
replacing any one player still leaves a sure finite opponent clock. Every
unilateral outcome is decided by date `H`, except that a response after `H`
is outcome-equivalent to Never. In particular, every unrestricted behavioral
cap is the maximum of the finitely many pure-time regions described below.

## Exact response cycle

The following is a literal closed cycle:

```
A --player 0--> B --player 1--> C
  --player 0--> D --player 1--> A.
```

Every arrow changes only the displayed mover's strategy, attains that
player's complete behavioral cap, and gains exactly one.

### A to B

At `A`, prescribed play terminates with coalition `{2,3}`, so player 0 gets
zero. If player 0 Quits at any date before `H`, the terminal coalition is
`{0}` and its payoff is one. Quitting at `H` joins players 2 and 3 and gives
zero; quitting later or Never also gives zero. Hence player 0's unrestricted
cap is one, attained by Quit0, and the update to `B` gains one.

### B to C

At `B`, player 0 Quits at date zero, so player 1 gets
`r_1({0})=0`. If player 1 also Quits at zero, the coalition is `{0,1}` and
its payoff is one. Every later action is screened by player 0's Quit0 and
still gives zero. Hence player 1's unrestricted cap is one, attained by
Quit0, and the update to `C` gains one.

### C to D

At `C`, player 0 gets `r_0({0,1})=0`. By Continuing at date zero, player 0
leaves the singleton coalition `{1}` and obtains one. Every positive quitting
time and Never has this same outcome because player 1 has already Quit.
Thus player 0's unrestricted cap is one, attained in particular by the finite
clock `H+1`, and the update to `D` gains one.

### D to A

At `D`, player 1 Quits alone at date zero and gets `r_1({1})=-1`.
Quitting at any date before `H` has the same singleton payoff. Quitting at
date `H` joins `{2,3}` and gives zero; quitting later or Never lets `{2,3}`
terminate first and also gives zero. Hence player 1's unrestricted cap is
zero, attained by the finite clock `H+1`, and the update back to `A` gains
one.

An arbitrary behavioral response is a probability distribution over pure
quitting times and Never. Its payoff is the corresponding convex combination
of the pure-time values just listed, so none exceeds the asserted cap. The
four responses are therefore exact for the full behavioral deviation class,
not only within a finite-clock subclass.

## The example has an exact equilibrium

Let player 2 Quit at date zero and let players 0, 1, and 3 Never Quit. The
terminal coalition is `{2}` and every player receives zero. If player 2
changes strategy, either it eventually Quits alone, still producing a
coalition containing player 2 and payoff zero, or everyone Never Quits and
Never pays zero. If any other player changes strategy, the outcome either
remains `{2}` or becomes a coalition containing player 2; all such rewards
are zero. Thus no behavioral deviation gains, and this is an exact terminal
Nash profile. Consequently the global terminal-semantic debt minimum is zero.

## Conclusion

The implication

```
two fixed sure finite clocks
+ finite complete semantics
+ exact sequential cap attainment
  -> terminal Nash or convergent response dynamics
```

is false. The two-clock property solves the off-path truncation problem but
does not orient horizontal response edges. Any use of the renewed two-clock
source must additionally exploit its positive global minimum, its exact
vertical predecessor expenditure, or the special chronology by which a new
cap clock is installed ahead of retained clocks.

## Source correspondence

The reward table is the response-cycle regression already used in
`FIN4_FINITE_PURE_CLOCK_EXACT_RESPONSE_CYCLE`, with two permanent finite
sentinel clocks replacing the two Never strategies. The two-clock semantic
adapter being tested is
`CODEX_HAHN__TWO_RENEWED_SURE_CLOCKS_GIVE_FINITE_COMPLETE_SEMANTICS`.
