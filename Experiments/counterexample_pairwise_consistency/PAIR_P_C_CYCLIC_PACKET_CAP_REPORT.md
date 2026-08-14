# `P x C`: exact packet/cap compatibility and the residual capacity problem

## Classification

**Open.**  The exposed packet equations and the punishment-rational
zero-charge cap are exactly compatible on one rational four-player reward
table.  The same table, however, has a repeatable positive-charge exact
Bellman--Nash cycle, so it fails the universal bounded-path clause of `C`.

This is therefore not a `Consistent` pair witness.  It is an exact negative
control showing that the local cap clauses do not approximate the universal
capacity clause: the latter is the entire unresolved part of this pair for
the construction below.

The exact executable checks are in
`pair_p_c_cyclic_packet_cap_probe.py`.

## One common rational reward table

Use players `I = {0,1,2,3}`.  Every nonsingleton coalition pays zero to every
player.  The singleton columns, with payoff coordinates as rows, are

```text
             owner 0   owner 1   owner 2   owner 3
player 0        0          2         -1          0
player 1       -1          0          2          0
player 2        2         -1          0          0
player 3        0          0          0         -1.
```

Thus the full table is specified on all `15` nonempty coalitions, is rational,
and has reward bound `M = 2`.

### Exact punishment values

For each `i in {0,1,2}`, quitting immediately guarantees zero: every
coalition containing `i` pays player `i` zero.  Opponents who always Continue
hold the player's best payoff to

```text
max(r_i({i}), 0) = 0.
```

Hence `chi_i = 0` for these three players.

Player `3` guarantees zero by Never, because every coalition not containing
`3` pays it zero.  Against opponents who always Continue, its best choice is
Never rather than its solo payoff `-1`.  Hence `chi_3 = 0` as well.  The
punishment vector is exactly

```text
chi = (0,0,0,0).                                               (1)
```

This calculation uses arbitrary behavior strategies in both directions:
the displayed Quit/Never strategies are lower guarantees, while the fixed
all-Continue opponent profile supplies the matching upper bounds.

## Full table-wide packet defect

Let `(lambda,z)` be any normalized singleton packet satisfying all of (15) in
Question 172 for this table.  Write `lambda_i` as `l_i`.

For player `3`, the solo and punishment inequalities give `z_3 >= 0`, while
the singleton mixture is `m_3 = -l_3`.  Since `z_3 <= m_3` and `l_3 >= 0`,

```text
l_3 = 0,       z_3 = 0.                                      (2)
```

For the other three players, solo and punishment values are both zero.  Their
mixtures are

```text
s_0 = 2 l_1 - l_2,
s_1 = 2 l_2 - l_0,
s_2 = 2 l_0 - l_1.                                           (3)
```

Packet feasibility gives `s_i >= z_i >= 0`.  If any of `l_0,l_1,l_2` were
zero, the cyclic inequalities in (3) would successively force a second mass
to zero and then make the remaining row negative.  Therefore

```text
l_0,l_1,l_2 > 0,
l_0+l_1+l_2 = 1,
z_0=z_1=z_2=0.                                                (4)
```

This characterizes the entire normalized packet family, including its target
coordinates; it is not merely one selected strict packet.

Adding (3) gives

```text
s_0+s_1+s_2 = 1,                                             (5)
```

so some active owner `i` has `s_i >= 1/3`.  The cyclic inequalities also give
`l_i >= 1/7` for every `i`: for example

```text
l_1 <= 2 l_0,   l_2 <= 2 l_1 <= 4 l_0,
1 = l_0+l_1+l_2 <= 7 l_0,
```

and the other cases follow by rotation.  In particular `0 < l_i < 1`.

Because the active owner's diagonal reward and target are zero, its refusal
gain over the unconditioned mixture is exactly

```text
R_i(lambda) - m_i(lambda)
  = [l_i/(1-l_i)] s_i
  >= l_i s_i
  >= 1/21.                                                    (6)
```

Consequently the single exact rational margin

```text
delta = 1/21                                                  (7)
```

works for **every** normalized packet of this full reward table, with

```text
0 < l_i < 1,
z_i = 0 < m_i(lambda),
m_i(lambda) + delta <= R_i(lambda).
```

The packet family is nonempty: `lambda=(1/3,1/3,1/3,0)` and `z=0` gives
`m=(1/3,1/3,1/3,0)`.  Its active refusal values are all `1/2`.

Thus `P` is established in its table-wide form, not only at a chosen packet.

## The local `C` geometry is exact

Set

```text
w = (0,0,0,0).                                                (8)
```

By (1), `w >= chi`; it lies in the reward box `[-2,2]^4`.  Every solo reward
is at most its coordinate of `w`: equality holds for players `0,1,2`, and
`-1 < 0` for player `3`.  Hence all-Continue is an exact one-stage Nash
action at `w`.  Its Bellman successor is again `w` and its absorption charge
is zero.

The constant sequence `w_t=w` therefore supplies an exact boxed
punishment-rational cap carrier and a limiting zero-charge all-Continue
self-loop.  This verifies the exposed augmented-cap/self-loop equations.
It does **not** claim provenance from a selected `T` tail; no such tail is
part of this pair witness.

## Why this is not a `P x C` consistency witness

Define three punishment-rational states

```text
u_0 = (0,1,0,0),
u_1 = (0,0,1,0),
u_2 = (1,0,0,0),                                             (9)
```

and let `a_i` assign Quit probability `1/2` to player `i` and zero to every
other player.  Direct evaluation gives

```text
F(a_0,u_0)=u_1,
F(a_1,u_1)=u_2,
F(a_2,u_2)=u_0.                                              (10)
```

Each action is exact Nash at the displayed state.  At the first edge:

* player `0` is indifferent between its zero continuation and its zero solo
  reward;
* player `1` receives `(1/2)1 + (1/2)(-1)=0` by Continue and zero by Quit;
* player `2` receives `1` by Continue and zero by Quit; and
* player `3` receives zero by Continue and `-1/2` by Quit.

The other two edges are rotations of the same calculation.  Every state in
(9) is at least `chi`, every edge lies in `[-2,2]^4`, and every edge has
charge `1/2`.  Repeating (10) gives exact punishment-rational finite chains
of charge

```text
Q_N = N/2                                                     (11)
```

for arbitrary `N`.  Hence no finite universal charge bound exists.

This also rules out a common shortcut: a table-wide strict packet defect plus
a punishment-rational all-Continue cap does not imply bounded capacity.  A
positive packet excess can be stored chronologically in rotating continuation
coordinates even though no static packet is complementary.

## Precise residual system

The pair remains open at exactly the following completion problem.

Find a rational four-or-more-player reward table and a finite `C` such that:

1. its complete normalized packet set is nonempty and admits one uniform
   refusal margin `delta>0` as in (16);
2. its behavioral punishment vector `chi` is computed against arbitrary
   opponent profiles;
3. it has a boxed punishment-rational cap `w` with `r_i({i}) <= w_i`, so the
   all-Continue root is an exact zero-charge self-loop; and
4. for every `N`, every `v^0 >= chi`, and every exact chain

   ```text
   v^(t+1)=F(a^t,v^t),   v^t in [-M,M]^I,
   ```

   one has `sum_t q(a^t) <= C`.

For the natural zero-collision completion above, item 4 is false by (9)--(11).
Changing only nonsingleton collision rewards leaves all singleton packet
equations (2)--(7) unchanged, but changes the one-stage deviation inequalities
that validate (10).  Thus the smallest live residual is:

```text
choose the nonsingleton rewards so that collision deviations destroy every
unbounded exact packet-rotation path, while preserving the punishment floors
used by the normalized packet family.                              (R_PC)
```

Checking only the local cap at `w`, only stationary positive-charge roots, or
only a selected family of paths is insufficient.  `(R_PC)` retains the
universal finite-capacity quantifier and is the regime-faithful `P x C` seam.

## Validation and scope

Run:

```text
python Experiments/counterexample_pairwise_consistency/pair_p_c_cyclic_packet_cap_probe.py
```

The probe uses `fractions.Fraction` only.  It checks the complete 15-coalition
table, the exact punishment-floor strategies, the packet witness, all packet
grid masses with denominators `1` through `120` (as a regression, with no
tolerance), the cap self-loop, every pure deviation at the three cycle edges,
and a 60-edge prefix of total charge `30`.  The continuum-wide packet margin
and the arbitrary-repeat charge failure are the symbolic arguments above,
not numerical inferences from the grid.

The construction uses four players, so it respects the cardinal lower bound
of a hypothetical counterexample.  It is not asserted to survive passive
player extension: new singleton owners enlarge the universally quantified
packet family and must be re-audited.  No terminal instability, tail
occupation, cap-as-suffix realization, or counterexample-regime provenance is
claimed.
