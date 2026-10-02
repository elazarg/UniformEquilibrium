# Review of Proposition 24.1

Reviewer: `CODEX_RAMSEY`

Verdict: **PASS** in the stated local-interface scope.

## Packet, floors, and crossed/preemption data

The half-half mixture of the singleton rows `{0}` and `{1}` is exactly

```text
(1,1,1,1).
```

The supported own coordinates are pinned at one, all four own singleton
payoffs are one, and the crossed inequalities are exactly

```text
r_0(2)=0 < 1=r_2(2) < 2=r_1(2),
r_1(3)=0 < 1=r_3(3) < 2=r_0(3).
```

The PP preemption inequalities at bare gap `g=1` hold with equality in both
coordinates.  This is only algebraic satisfaction of the checked screen; the
note correctly does not infer a terminal exploitability witness.

All payoffs to an absent player are nonnegative, so Never guarantees zero
against every opponent profile and `chi_i>=0`.  The displayed sure opponent
coalitions prove the reverse bounds:

```text
i=0: Continue at {1,3} gives 0, Quit at {0,1,3} gives -10;
i=1: Continue at {3}   gives 0, Quit at {1,3}   gives -1;
i=2: Continue at {0}   gives 0, Quit at {0,2}   gives -1;
i=3: Continue at {0,1} gives 0, Quit at {0,1,3} gives -1.
```

Because an opponent coalition quits surely at the first row, every unilateral
behavioral deviation reduces to that Quit/Continue endpoint choice.  Hence
all four punishment values are exactly zero, not merely at most one.

## Persistent face and induced Nash calculation

Every edge of

```text
{0}->{0,1}->{0,1,2}->{0,1,2,3}
   ->{0,2,3}->{0,3}->{0}
```

has the displayed strict sign.  Direct endpoint averaging in the fixed-base
game gives

```text
Delta_1=1-2p_3,  Delta_2=2p_1-1,  Delta_3=2p_2-1.
```

The Nash support conditions have the unique solution
`p_1=p_2=p_3=1/2`: either strict side of `p_1=1/2` propagates around the
three best responses to a contradiction, while at equality player 1's
mixing forces `p_3=1/2` and player 3's mixing forces `p_2=1/2`.

The eight present-face payoffs of player 0 sum to `-13`, so `V_0=-13/8`.
After player 0 leaves, only the cell `{1}` contributes one and the empty cell
uses `chi_0=0`, giving `L_0=1/8`.  Thus `L_0-V_0=7/4` exactly.

## Exhaustive cube check

I independently enumerated all 16 coalitions.  The first outgoing coordinate
at masks `0,...,15` is

```text
0,1,0,2,0,1,0,3,0,3,1,0,0,2,2,0,
```

exactly (24.8).  In fact no membership edge has zero advantage, and every
vertex has at least one strict outgoing edge; hence there is no pure terminal
sink.

I also independently enumerated the four backgrounds for each of the six
coordinate pairs.  With the note's sign-word convention the result is

```text
01: ++++, ++++, +---, +--+
02: +-++, +++-, +-+-, -+--
03: +-++, +--+, ++++, ++-+
12: +-++, +++-, --+-, -+--
13: ++-+, +---, ++++, ++-+
23: ++-+, -+--, -+-+, +++-
```

which matches (24.9).  A directed square has word `++--` in one orientation
or `--++` in the reverse orientation; neither occurs.

## Scope

The table therefore really is an exact sharpness regression for the claimed
finite interface: crossed normalized support-two data, exact zero punishment
values, PP preemption signs at unit gap, a persistent strict six-cycle, and a
large A.2 base-leave gap do not force a pure sink or strict directed square.

It has not been shown to carry a terminal exploitability gap and is not a
uniform-equilibrium counterexample.  Nor does the static induced-Nash gap
produce a chronology.  The note states both nonclaims explicitly, so no
scope repair is required.
