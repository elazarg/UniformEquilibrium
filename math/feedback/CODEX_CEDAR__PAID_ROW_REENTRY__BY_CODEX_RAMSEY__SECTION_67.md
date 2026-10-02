# Review of Section 67

Reviewer: `CODEX_RAMSEY`

Verdict: **PASS**.

For each player `i`, joining any fixed nonempty opponent coalition `A`
changes its payoff from `b_i(A)` to `b_i(A)-1`, while quitting alone pays
`-1`.  Never against arbitrary opponent clocks always gives either zero or a
value of `b_i(A)` and is therefore nonnegative.  Against all-Never opponents,
the best of Never and any finite solo Quit is zero.  Hence every punishment
value is exactly zero.

The first coalitions of the four deterministic profiles are, in order,
`{1},{2},{3},{1}`.  Direct substitution into (67.1) gives

```text
U^0=U^3=(-1,0,1),
U^1=(1,-1,0),
U^2=(0,1,-1).
```

The cap calculation is also exact.  At each node the current singleton owner
can wait past its cyclic successor and receive one; the player already
receiving one cannot improve; the third player has cap zero.  This yields

```text
B^0=B^3=(1,0,1),
B^1=(1,1,0),
B^2=(0,1,1),
```

and the displayed debt vectors.  At each update, the mover's pure-time payoff
is `-1` before its successor's time, `0` when tying the successor, and `1`
after it, including Never.  Thus the new deterministic time is an exact best
response with gain two and zero updater debt.  Since opponents are
deterministic, every behavioral stopping law is a probability mixture of
these pure-time payoffs, so the same value one is the unrestricted behavioral
cap.  The path returns exactly because `U^3=U^0`.

The canonical floor clips in (67.4) follow from the zero punishment vector.
More generally, fix any tail `V>=0`.  Conditional on a nonempty opponent Quit
set `A`, forced Quit gives `b_i(A)-1` while Continue gives `b_i(A)`.  On the
all-opponents-Continue event, Quit gives `-1` while Continue gives `V_i>=0`.
Therefore Quit is strictly dominated by Continue against every product root,
for every player.  The unique exact endpoint-Nash root is all-Continue; its
charge is zero and its Bellman predecessor equals `V`.  Repeating this
argument at each edge proves that every finite exact floor-admissible path
from any floor-safe tail is constant and zero-charge.  It applies in
particular to all `V^j` and `B^j`.

The scope is stated correctly.  All-Never is itself an exact terminal
equilibrium in this table, because every finite unilateral Quit pays `-1`.
Thus the example is not a terminal-gap, positive-minimum, or paid-frontier
instance.  It is an exact collective no-go for converting the output fields
of the behavioral payoff-return construction by nodewise floor clipping; it
does not rule out a nonlocal exact excursion supplied by additional source
structure.
