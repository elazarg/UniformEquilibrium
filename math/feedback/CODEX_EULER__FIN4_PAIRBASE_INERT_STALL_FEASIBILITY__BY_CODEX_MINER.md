# Independent review of the Fin4 pair-base inert-stall feasibility boundary

Reviewer: `CODEX_MINER`

Target:
[`CODEX_EULER__FIN4_PAIRBASE_INERT_STALL_FEASIBILITY.md`](../notes/CODEX_EULER__FIN4_PAIRBASE_INERT_STALL_FEASIBILITY.md)

Verdict: **PASS at the stated internal negative-screen scope.** The rational
regression, unrestricted-deviation calculations, unique all-Continue cap
root, exact global failure, and the sixteen-vertex Gray-cycle feasibility
screen are correct. I found no mathematical objection. The note correctly
does not claim a full terminal-gap realization, control of the opaque
canonical root selector in the Gray screen, or elimination of the inert arm.

## 1. Rational table and actual profile

For

```text
r_i(S)=2  if i is not in S,
       =1  if S={i},
       =0  if i is in S and |S|>=2,
```

and the date-zero quitting coalition `B={0,1}`, the prescribed payoff is

```text
U=(0,0,2,2).
```

The unrestricted caps can be computed without any stationarity restriction.
If player 0 deviates, player 1 still Quits surely at date zero. Player 0 gets
zero by joining and two by Continuing; all later behavior is irrelevant.
The same holds with 0 and 1 exchanged. If player 2 or 3 deviates, players 0
and 1 still absorb at date zero; Continuing gives two and joining gives zero.
An arbitrary randomized behavioral deviation is only a mixture of those two
date-zero endpoints. Hence

```text
B=(2,2,2,2),
d=(2,2,0,0),
D=4.
```

This verifies the free-player solved coordinates and owner `o=2`'s zero
debt using the full behavioral envelope.

The complete law is the point mass on `{0,1}`. In the definition of
`quittingTerminalOpponentIncidenceMass`, the event for `(who,other)=(2,0)`
is precisely a terminal coalition containing 0, with `0!=2`; its mass is one.
The note does not need coalition exclusion of the reset owner for this
incidence calculation, though the displayed outcome excludes 2 as well.

Finally player 0's two deterministic pure times are literal: Quit at date
zero joins `{0,1}` and pays zero, while Never lets player 1 quit alone and
pays two. This is a same-profile paid first-disagreement row of gain two.

## 2. Unique all-Continue cap root

Fix any player `i` and any product distribution of the other players' current
actions at tail `b=(2,2,2,2)`. If `i` Quits, it receives one when no opponent
Quits and zero when at least one opponent Quits. Its forced-Quit endpoint is
therefore at most one. If `i` Continues, an opponent Quit produces a coalition
not containing `i` and payoff two, while no opponent Quit gives continuation
value `b_i=2`. Its forced-Continue endpoint is exactly two.

Thus Continue is strictly dominant for every player at every opponent mixed
row. Every exact product Nash root must put probability one on Continue in
every coordinate. The cap root is uniquely all Continue, so the regression
does not rely on how `Classical.choose` selects among roots.

After an all-Continue prefix the actual profile is merely delayed. Its law,
terminal payoff, unrestricted cap, and debt vector are unchanged. The same
strict-dominance calculation therefore applies inductively at every cap-lift
depth, and the paid row shifts with full gain two. Corollary 3.3 is exact.

## 3. Exact location of the global failure

At all Never, every player can obtain its singleton payoff one or retain the
Never payoff zero. Thus `U=0`, `B=(1,1,1,1)`, and total debt is four.

For the profile with exactly player `i` Quitting at date zero, the quitter
gets one and each outsider gets two. Against Never opponents, the quitter's
best behavioral replacement is worth `max(1,0)=1`. Against the sure quitter,
an outsider gets two by Continuing and zero by joining; later behavior cannot
matter after date-zero absorption. Hence every coordinate is already at its
unrestricted cap and the total debt is zero.

Since semantic debt is nonnegative, this gives global minimum zero and an
exact terminal Nash profile. It simultaneously falsifies the positive-
minimum and terminal-gap ambient fields. The regression consequently realizes
the local target/paid/incidence/inert identities but does not instantiate the
full `FinFourSameSourcePaidResetCapPort`. The note states this separation
correctly.

## 4. Pure-profile debt formula

Formula (5.1) is the exact unrestricted debt at a pure date-zero coalition.

- If `i in S` and another player remains after `i` leaves, the only effective
  alternatives are membership in `S` and absence from `S` at date zero.
- If `S={i}`, leaving produces Never payoff zero; quitting later reproduces
  the same singleton payoff and adds no third cap value.
- If `i notin S` with `S` nonempty, the only effective endpoints are
  Continuing outside `S` and joining `S` at date zero.
- If `S=empty`, arbitrary finite quitting gives the singleton payoff and
  Never gives zero.

Thus `delta_i(S)` is exactly the positive part of the other membership
endpoint minus the current payoff, including both empty-boundary cases. A
terminal gap indeed implies all sixteen disjunctions (5.2). This is only a
necessary restriction because the terminal-gap predicate quantifies over all
behavioral profiles.

## 5. Gray-cycle feasibility screen

The displayed word visits every vertex of the four-dimensional coalition
cube once and returns to the empty vertex. Consecutive vertices differ in
exactly one membership. For a fixed player `i`, its coordinate edges form a
perfect matching of the cube, so two distinct used `i`-edges cannot share an
endpoint. The instruction “source payoff zero, target payoff one” is therefore
conflict-free coordinate by coordinate.

The two empty-boundary assignments are also correct. The first edge

```text
empty -> {0}
```

uses the fixed empty payoff zero and sets `r_0({0})=1`. The last edge

```text
{3} -> empty
```

cannot put payoff one at the fixed empty endpoint, so setting
`r_3({3})=-1` gives the same unit gain. Every unused coordinate edge may be
set to zero at both endpoints because coordinate edges partition the vertex
set. Hence every vertex has its displayed outgoing gain exactly one, proving
the pure screen with `Gamma=1`.

At the pair base `{0,1}`, the next Gray edge is player 0 leaving. Directly
from the assignments,

```text
U=(0,1,0,0),
B=(1,1,0,0),
d=(1,0,0,0).
```

The coordinate-2 and coordinate-3 join edges at this base are unused, so both
free coordinates have zero debt. Owner 2 is therefore reset, the pure law
has unit `(2,0)` incidence, and player 0 has the unit paid leave row. The
singleton diagonal is

```text
(r_0({0}),r_1({1}),r_2({2}),r_3({3}))=(1,0,0,-1),
```

which is coordinatewise at most the displayed cap. Therefore all Continue
is an exact cap root at this target.

The construction does not establish uniqueness of that root, and it does not
control which exact root the opaque canonical selector chooses. Nor do the
sixteen pure inequalities imply positive debt for every mixed or history-
dependent profile. These are precisely the nonclaims made in the note, so the
Gray screen is used at its correct strength.

## 6. Novelty and export verdict

The sharp contribution is the source-separation boundary:

```text
local pair-base solved/reset/incidence/paid data
+ unique inert all-Continue cap selection
  does not by itself contradict a quitting reward table;

the first failure of the exact regression is global positive minimum /
terminal exploitability away from that source.
```

The rational example is stronger than the pre-existing abstract cap-face
warning because it co-realizes the full local pair-base paid row on one actual
Fin4 profile and makes the cap root unique. The Gray construction separately
shows that adding all sixteen pure-profile gap inequalities still does not
create a finite incidence contradiction.

This is a useful internal no-go screen, but I agree with the author's current
non-export status. It neither realizes the full behavioral/global hypotheses
nor decisively refutes an implication that uses them. A future export would
need a named accepted negative-screen obligation broad enough to treat this
local/global separation as its endpoint, or a further theorem consuming the
remaining mixed/global quantifier.
