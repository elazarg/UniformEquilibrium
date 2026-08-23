# `T x P x C`: lock-clean packet/cap interface and the residual `O/G` seam

## Classification

**Open for the full triple; the exposed common-data equations are exactly
compatible.**

One rational four-player reward table simultaneously has:

- a positive-hazard exact dynamic-debt phantom tail `T`;
- the table-wide packet property `P`, with one positive refusal margin over
  its entire normalized packet family;
- exact punishment-floor transport of the augmented caps along the same tail,
  bounded positive charge on every selected cap segment, and a zero-charge
  limiting all-Continue cap;
- no nonempty pure coalition lock, including the four strict singleton-join
  restrictions forced by global finite capacity.

This is not a witness to full `C`.  The universal charge bound over the
complete exact punishment-floor root correspondence is unproved.  Nor is the
tail known to have optimized/projective provenance.  The construction shows
that packet preference, exact selected cap transport, and every promoted pure
lock screen do not themselves manufacture a charged return.  The remaining
problem is genuinely the occupation interface `O` together with global
capacity `G`, not another singleton inequality.

The exact audit is
[`triple_t_p_c_packet_capacity_probe.py`](triple_t_p_c_packet_capacity_probe.py).
It imports the common table and tail from
[`triple_t_w_c_lock_clean_probe.py`](triple_t_w_c_lock_clean_probe.py), so the
two checks cannot silently drift to different reward data.

## 1. The single shared reward table

Let `I={0,1,2,3}`.  The singleton columns are

```text
             owner 0   owner 1   owner 2   owner 3
player 0        1         2/3        5/3        5/3
player 1       5/3         1          2          0
player 2       2/3        5/3         1          2
player 3        2         5/3        1/3         1.
```

The pair rewards are

```text
r({0,1})=(11/12,1/2,1/8,1/8),
r({0,2})=(1/2,1/8,11/12,1/8),
r({2,3})=(1/8,1/8,1/2,7/12),
r({1,3})=(1/8,1/4,1/8,1/2),
r({1,2})=(1/8,1/2,1/2,1/8),
r({0,3})=(1/2,1/8,1/8,1/2).
```

Every triple pays zero to its members and `1/8` to its unique spectator; the
grand coalition pays zero.  Thus `M=2`.

All rewards are nonnegative, so Never guarantees zero.  If all three
opponents Quit immediately, Continue pays `1/8` and joining pays zero.  Hence

```text
0 <= chi_i <= 1/8                                           (1)
```

for every player.  The upper enclosure, rather than an unsupported exact
formula for `chi`, is all that the packet and selected-cap arguments use.

## 2. The complete normalized packet family

Every diagonal singleton reward is one.  For a probability vector `lambda`,
write

```text
m_i = sum_j lambda_j r_i({j}),        h_i=m_i-1.
```

If `(lambda,z)` satisfies the packet clauses (15) of Question 172, then

```text
h_i >= 0 for every i,                                      (2)
z_i=1 whenever lambda_i>0.                                (3)
```

Conversely, any probability vector satisfying (2), together with `z=(1,1,1,1)`,
is a packet: the solo and complementarity clauses are immediate and (1)
supplies punishment rationality.  Thus the mass projection of the full packet
family is the explicit rational polytope

```text
Lambda={lambda>=0 : sum_i lambda_i=1 and R lambda >= 1}.   (4)
```

It is nonempty.  At `lambda=(1/4,1/4,1/4,1/4)`,

```text
m=(5/4,7/6,4/3,5/4).                                     (5)
```

### No complementary packet

Suppose a packet were complementary.  On its positive support `S` it would
satisfy `m_i=1`.  For each of the `15` nonempty supports, solve exactly the
normalization equation and these active equalities.

- A singleton support gives a pure mass, and every such mass violates at
  least one of the four funding inequalities in (2).
- Every two-element support solution collapses to a singleton endpoint and
  therefore either has the wrong support or is globally underfunded.
- The four three-element candidates are

  ```text
  S={0,1,2}: (-1,4/3,2/3,0),
  S={0,1,3}: (1/3,4/9,0,2/9),
  S={0,2,3}: (1,0,-1/3,1/3),
  S={1,2,3}: (0,-3,2,2).
  ```

  Three have a negative coordinate.  The remaining candidate is globally
  funded, but `m_3=44/27>1`, so it is not complementary on its support.
- The full-support solution is `(1,0,-1/3,1/3)`, which is not full or
  nonnegative.

The probe performs this support enumeration by exact Gaussian elimination.
It follows that every `lambda` in (4) has an active coordinate with `h_i>0`.

Define the continuous function

```text
g(lambda)=max_i lambda_i h_i.
```

The compact polytope (4) contains no zero of `g`, so it has a minimum
`epsilon>0`.  Pure masses are not feasible, and for an active coordinate
with `lambda_i h_i>=epsilon`, the exact refusal identity is

```text
R_i(lambda)-m_i(lambda)
  = [lambda_i/(1-lambda_i)] h_i
  >= lambda_i h_i
  >= epsilon.                                               (6)
```

Because `z_i=1<m_i`, this is precisely the table-wide packet conclusion.
Choosing any positive rational `delta<=epsilon` gives a single rational
margin for every packet.  This proves `P` on the continuum; the finite grid
in the probe is only a regression check.

## 3. The common tail and selected cap geometry

Put `k=t+4` and

```text
p_t=1/k^2,               s_t=(k-1)/k,
x_t=(0,p_t,0,0).
```

Only player `1` carries physical hazard.  Prescribe

```text
v_t=r({1})+(3/4)s_t e_0,
d_t=        (1/2)s_t e_0,
w_t=v_t+d_t=r({1})+(5/4)s_t e_0.                           (7)
```

The identity `s_t=(1-p_t)s_(t+1)` gives the exact Bellman and dynamic-debt
recursions.  The only positive-debt player never Quits and the only mixer has
zero debt, so the diagonal debt seam vanishes identically and

```text
w_t=F(x_t,w_(t+1))                                        (8)
```

with `x_t` exact Nash at the displayed continuation.  All caps lie above the
punishment enclosure (1) and in `[-2,2]^4`.  With `eta=1/4`,

```text
d_t(0)>=3/8>eta,       d_t(0)->1/2,
v_t(0)->17/12,         U_0(x^(t))->0.                       (9)
```

The owner clock is bounded by `log 4`.  The cap limit is

```text
w_infinity=(23/12,1,5/3,5/3),                             (10)
```

where all-Continue is an exact zero-charge self-loop.  Moreover,

```text
w_(t+1)(0)-w_t(0)=5/[4k(k+1)] >= p_t.                     (11)
```

Thus every selected cap segment has positive but uniformly bounded charge,
and its scalar cap coordinate has a strict one-way change dominating that
charge.  No segment of this selected ray is a return.

These are the same tail actions and the same augmented caps, not unrelated
objects copied onto one table.

## 4. The packet is not the tail occupation

The normalized owner-hazard occupation of every positive-charge tail window
is the pure atom

```text
lambda^tail=e_1.
```

Its player-0 singleton mixture is

```text
m_0(e_1)=r_0({1})=2/3<1.                                  (12)
```

It therefore fails packet funding.  The funded packet polytope (4) exists on
the same table but is not derived from the tail.  This is an exact failure of
the occupation/admissibility bridge `O`, rather than a small-error issue.

In particular, the refusal preference in (6) is a statement about a funded
singleton lottery.  It does not by itself define an exact Bellman root at a
tail cap, and it cannot be inserted as an edge of (8).

## 5. Strict joiners remove pure locks but do not produce a return

Every one of the `15` nonempty pure quitting coalitions fails the exact Nash
test at its own set reward.  For the four singleton owners, designated
strict joiners are

```text
0 -> 2,       1 -> 0,       2 -> 3,       3 -> 1.          (13)
```

For each arrow the join payoff exceeds the watch payoff by `1/4`; its solo
endpoint is also strictly better.  Hence the affine join gain is positive at
every singleton-owner rate.  This passes the full promoted coalition-lock
screen, not just its positive-solo corollary.

The direction of this fact matters.  A strict joiner destroys the putative
pure singleton fixed root.  It does not select a replacement exact mixed
root, identify a packet owner with a cap edge, or close an endpoint cycle.
Combining (6), (11), and (13) therefore yields no charged return without an
additional realization statement.

The exact model proves that all currently exposed local equations and every
pure-lock restriction coexist.  It does **not** prove that the complete root
correspondence has no mixed positive-charge fixed point, no charged cycle,
and no arbitrarily long nonrecurrent charged path.  Establishing all of those
uniformly is exactly `G`; a bounded search cannot certify it.

## 6. Residual `T x P x C` system

The full triple remains open at three named interfaces.

1. **Occupation/admissibility `O`.**  Produce from the actual tail a limiting
   singleton mass that is simultaneously funded, punishment-rational, and
   aligned with the player witnessing the packet refusal defect.  Equation
   (12) shows that tail occupation alone does not do this.
2. **Global capacity `G`.**  Control every boxed punishment-floor exact root,
   not only the selected ray.  Equivalently, construct a bounded budget
   potential on the complete root correspondence, or find a positive-charge
   return and thereby contradict `C`.
3. **Optimized provenance `M`.**  In the terminal exploitability witness the exact-D
   tail comes from cutoff-wise optimized zero-boundary minimizers.  The
   hand-built tail (7) does not claim that origin.

A useful closing theorem would connect `O` to `G`: turn a funded tail-derived
packet refusal into an exact floor-admissible edge whose endpoint can be
reused, or show that failure of such reuse strictly decreases the global
capacity budget.  The present singleton support and coalition-lock facts are
not sufficient for that step.

## Validation

Run

```text
python Experiments/counterexample_pairwise_consistency/triple_t_p_c_packet_capacity_probe.py
```

All identities use `fractions.Fraction`.  The probe checks the complete
15-coalition reward table, all 15 proposed complementary supports, a rational
packet witness, 256 exact-D/cap edges, the full pure-coalition-lock screen,
and a finite packet-grid regression.  The continuum-wide packet margin is the
support-elimination plus compactness argument above, not an inference from the
grid.

The construction uses four players and so respects the known cardinal lower
bound.  Player extension is not asserted: new singleton columns change the
universally quantified packet family and the complete root correspondence.
