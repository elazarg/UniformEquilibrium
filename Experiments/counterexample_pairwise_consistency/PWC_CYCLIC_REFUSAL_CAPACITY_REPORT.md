# `P x W x C`: linked refusal occupation versus global charge capacity

## Classification

**Open.**  A refusal-linked packet and periodic-window obstruction do not by
themselves contradict global finite punishment-floor charge capacity.  The
missing implication is an exact realization theorem from the periodic
occupation data into the complete punishment-floor Nash--Bellman
correspondence.

There is nevertheless a sharp exact negative control.  One rational
four-player table has all of the following on common data:

1. a table-wide packet refusal margin `delta = 1/21`;
2. a funded punishment-rational packet `(lambda,z)`;
3. canonical periodic windows whose normalized singleton occupation is
   exactly `lambda`, and whose same fixed refusal player gains by more than
   `delta`; and
4. a repeatable exact punishment-floor Nash--Bellman cycle using precisely
   the packet owners and carrying charge `3/2` per turn.

Item 4 violates `C`.  Thus the construction is not a consistency witness for
the full triple.  It shows that the desired charged return really occurs in
the collision-flat model, and isolates the only place where a globally
capacity-bounded table would have to escape it: collision deviations or some
other exact-root obstruction must prevent the packet occupation from lifting
to a repeatable floor path.

The exact checks are in
[`pwc_cyclic_refusal_capacity_probe.py`](pwc_cyclic_refusal_capacity_probe.py).

## One common rational table and punishment floor

Use players `{0,1,2,3}`.  Every nonsingleton coalition pays zero.  Singleton
columns, with payoff recipients as rows, are

```text
             owner 0   owner 1   owner 2   owner 3
player 0        0          2         -1          0
player 1       -1          0          2          0
player 2        2         -1          0          0
player 3        0          0          0         -1.
```

The complete table is rational and bounded by `M=2`.  Its punishment vector
is exactly zero.  Players `0,1,2` guarantee zero by quitting immediately,
while every coalition containing the player pays it zero; opponents who all
Continue give the matching upper bound.  Player `3` guarantees zero by Never,
and opponents who all Continue again give the matching upper bound because
its solo payoff is `-1`.  Hence

```text
chi = (0,0,0,0).
```

## `P`: full packet margin and the selected funded packet

For `lambda=(l0,l1,l2,l3)`, packet feasibility forces `l3=0`, target `z=0`,
and

```text
m0 = 2 l1 - l2 >= 0,
m1 = 2 l2 - l0 >= 0,
m2 = 2 l0 - l1 >= 0.
```

The exact argument in `PAIR_P_C_CYCLIC_PACKET_CAP_REPORT.md` proves that
every feasible normalized packet has some active owner with refusal gain at
least

```text
delta = 1/21.
```

For the selected packet take

```text
lambda = (1/3,1/3,1/3,0),       z = (0,0,0,0).
```

Then

```text
m = (1/3,1/3,1/3,0),
R_i(lambda) = 1/2       for i=0,1,2.
```

In particular the packet is strictly funded at every active coordinate and
is exactly punishment-rational: `chi=z<m`.  This is the refusal geometry from
`SingletonPacketDefectAlgebra`, not the underfunded phase geometry.

## `W`: an exact occupation-linked refusal family

At date `t`, let players `0,1,2` each quit with

```text
p_t = 1 / (200 * 2^t),
```

and let player `3` always Continue.  Canonical window `W_n` periodically
repeats dates `n,...,2n`.

At each phase all three singleton-owner probabilities are equal.  Chronology
and periodic restart multiply them by the same survival weight.  Therefore
the normalized singleton-owner terminal occupation of every window is
exactly

```text
mu_n = (1/3,1/3,1/3,0) = lambda.
```

Fix refusal player `0`.  At a phase with hazard `p`, prescribed absorption
among the three active players has singleton ratio

```text
3 p (1-p)^2 / (1-(1-p)^3),
```

and the average player-0 singleton payoff is `1/3`.  Collisions pay zero, so
every periodically restarted prescribed value is at most `1/3`.

After player `0` refuses, the two opponent hazards remain.  Conditional on
phase absorption its payoff is

```text
p(1-p) / (1-(1-p)^2) = (1-p)/(2-p).
```

For `p <= 1/200`, this is at least `199/399`.  A periodic value is a convex
combination of these phase ratios, so every canonical window satisfies

```text
refusal_0(W_n) - delivery_0(W_n)
  >= 199/399 - 1/3
   = 22/133
   > 1/21 = delta.
```

Thus the table-wide packet margin, selected packet, window occupation, fixed
player, fixed refusal branch, and positive margin all live on one exact data
set.  No target/delivery equality is inserted: `z_0=0`, while the late
delivery approaches `m_0=1/3`.

## The packet-support rotation becomes an exact charged cycle

Define floor states

```text
u0 = (0,1,0,0),
u1 = (0,0,1,0),
u2 = (1,0,0,0).
```

At `u_i`, let owner `i` quit with probability `1/2` and every other player
Continue.  Direct Bellman evaluation gives

```text
F(a0,u0)=u1,
F(a1,u1)=u2,
F(a2,u2)=u0.
```

Every row is exact Nash.  The mixing owner is indifferent at its zero solo
value; every deviating outsider gets zero because all collision and own-solo
payoffs are zero, while the prescribed successor coordinate is nonnegative.
Every state dominates `chi=0`, and every edge has charge `1/2`.

The cycle uses the same three owners that support `lambda`, in the same cyclic
singleton preference geometry.  Its charge is `3/2`; arbitrary repetition
gives exact punishment-floor prefixes of unbounded charge.  Consequently

```text
quittingPunishmentFloorPrefixChargeCapacity reward = top.
```

The common table therefore fails `C` for a mathematically relevant reason,
not through an unrelated dummy-player loop.

## What global capacity does and does not say

Finite global capacity already says that every exact reachable charged cycle
has zero charge and supplies a bounded budget-to-go potential decreasing by
the literal charge along every exact floor edge.  It does not map a behavioral
periodic window, its singleton occupation, or its refusal evaluator to an
edge of that exact correspondence.

The refusal inequality is static:

```text
z_i < m_i(lambda) < R_i(lambda).
```

It gives a positive averaged singleton drift at one coordinate.  If exact
singleton-owner roots realizing that drift exist, a finite block can spend
some of the bounded potential while moving through continuation space.  This
is fully compatible with finite capacity.  A contradiction requires either
arbitrarily repeatable progress or a positive exact return.  Neither follows
from a positive static drift alone.

The negative control exhibits both missing layers:

1. zero collision rewards make the packet-owner rows exact floor edges; and
2. the three continuation buffers close those edges into an exact return.

General collision rewards can destroy the first layer without changing the
singleton packet algebra and affect late small-hazard window values only at
collision order.  They can also change the behavioral punishment floor, which
must be recomputed rather than assumed.  This is precisely the live route by
which a table satisfying global `C` could retain `P x W`.

## Branch separation

### Phase branch

Suppose an occupation bridge pins a stabilized active player's target to its
solo reward and the periodic phase evaluator has the same target limit.  A
fixed phase gap gives

```text
m_i(lambda) + eta <= z_i.
```

This contradicts packet funding `z_i <= m_i(lambda)` before capacity enters.
Therefore a genuine funded packet cannot arise from that phase branch with
the stated target link.  If a phase obstruction persists, the missing object
is the funding/target bridge itself, not a charge argument.

### Refusal branch

For `0 < lambda_i < 1`, support pinning and a fixed refusal gap imply

```text
z_i < m_i(lambda) < R_i(lambda),
```

and the owner mass is quantitatively nonvanishing.  If `chi_i <= z_i`, the
occupation data is already a genuine packet.  The obstruction reinforces `P`
rather than contradicting it.  Capacity becomes relevant only after an exact
root/path realization is supplied.

## Precise missing theorem

The clean missing statement is an **occupation-to-floor-return alternative**.
In a regime with global finite capacity, for a periodic refusal subsequence
whose singleton occupations converge to a funded punishment-rational packet
with margin `delta>0`, prove one of:

1. some compatible periodic window has terminal exploitability below the
   claimed common margin; or
2. the linked packet/window data generates a closed exact
   punishment-floor Nash--Bellman path of positive charge (equivalently,
   exact prefixes of arbitrarily large charge).

For an executable proof, this should be split into two named interfaces.

* **Exact charged lift.**  Convert the linked owner occupation and full
  product-law/collision data into exact floor edges, with the packet target or
  a canonically related reachable state as their continuation datum.  All
  outsider collision deviations and the complete punishment floor must be
  checked.
* **Renewable return.**  Show that the lift can be renewed after spending a
  fixed positive amount of charge, or close it by an exact endpoint return.
  Merely producing one positive edge or one selected cap path is insufficient;
  a bounded potential can pay for finitely many such edges.

The first interface is absent from `P x W`; the second is the finite-tower or
attachment seam already visible in the global charge API.  The collision-flat
table proves both in one exact special case.  Establishing either interface
in general would be substantive; establishing both would rule out the
refusal branch of the full triple.

## Scope

* The witness has four players and uses one complete rational reward table.
* The packet/window occupation equality is exact, not asymptotic.
* The phase and refusal branches are not conflated.
* Local zero-charge cap facts are not presented as global capacity.
* No annotation/payoff equality, cap-as-suffix realization, or optimized-tail
  provenance is assumed.
* The result does not prove that `P x W x C` is consistent or inconsistent;
  it reduces the live triple to exact charged lift plus renewable return.
