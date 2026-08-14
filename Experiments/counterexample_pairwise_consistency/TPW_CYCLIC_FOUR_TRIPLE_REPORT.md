# T x P x W: one exact cyclic four-player common-data witness

## Classification

**Consistent for the exposed common-data `T x P x W` equations.**

One rational four-player reward table supports, with the single margin

```text
eta = delta = 1/52,
```

all of the following at once:

- the table-wide packet theorem `P`, not merely one favorable packet;
- one nonstationary summably absorbing exact dynamic-debt tail `T`, with the
  original debt, clock, Bellman, and honest-payoff identities unchanged; and
- every canonical periodic window of that same selected tail, with player 2
  on the exact finite-phase evaluator branch and a behavioral deviation gain
  at least `2/7 > eta/2`.

The only adjustment to the earlier `T x P` witness is made **before** the
canonical family is defined: discard original date zero, reindex the remaining
tail by `a~_t=a_(t+1)`, and then form

```text
W~_n = (a~_n,a~_(n+1),...,a~_(2n)).
```

This is a suffix choice, not the deletion of an inconvenient window from an
already fixed canonical family.  It is legitimate because every `T` equation
and bound is suffix-stable.  It is also necessary: the discarded one-phase
word `W_0=(a_0)`, whose owner hazard is `1/3`, is an exact stationary
equilibrium and is not exploitable.

This classification concerns the exposed triple.  Optimized-minimizer and
projective provenance are still absent.  In fact the same table fails both
global terminal instability and global punishment-floor charge capacity on
an explicit exact self-loop, so this is not a counterexample to Question 172.

## 1. Common table, packet, and margin

Use players `I={0,1,2,3}`, with indices modulo four.  The singleton columns
are

```text
                 singleton quitter j
payoff row i       0   1   2   3
             0     1   0   0   4
             1     4   1   0   0
             2     0   4   1   0
             3     0   0   4   1
```

and every coalition with at least two quitters pays `-4` to every player.
Thus `M=4`, every positive singleton cap is `K_i=1`, and the behavioral
punishment values obey `chi_i<=1`: opponents can all Continue forever, against
which a player can obtain at most its solo payoff one.

The full table-wide packet proof is unchanged from
`TP_TAIL_PACKET_CYCLIC_FOUR_REPORT.md`.  For every normalized packet `(lambda,z)`
satisfying (15), every coordinate of `lambda` is at least `1/13`, the target
is pinned to `z=(1,1,1,1)`, and some active player has

```text
refusal_i(lambda) - m_i(lambda) >= 1/52.
```

This is a uniform theorem over the entire feasible packet polytope.  For a
concrete nonempty instance, the symmetric mass has

```text
lambda = (1/4,1/4,1/4,1/4),
z      = (1,1,1,1),
m_i    = 5/4,
R_i    = 4/3.
```

It is funded, punishment-rational, complementary, and has refusal gap `1/12`.
We retain the weaker table-wide margin

```text
eta = delta = 1/52
```

as the common margin for all three clusters.

## 2. The shifted tail preserves T exactly

At original absolute date `k`, only player 0 has positive hazard:

```text
p_k = 1/(2^(k+2)-1).
```

Put

```text
A_k = 1/2^(k+1),       P_k = 1-A_k,
v_k = (1, 1+3 A_k, P_k, P_k),
d_k = (1,0,0,0).
```

The earlier report proves every displayed Bellman--Nash, exact dynamic-debt,
conservation, survival, and honest-payoff identity for every `k>=0`.  Select
the suffix

```text
a~_t = a_(t+1),  v~_t = v_(t+1),  d~_t = d_(t+1).
```

Equivalently, its hazard and honest absorption probability are

```text
p~_t = 1/(2^(t+3)-1),
A~_t = 1/2^(t+2).
```

Every consecutive shifted pair is still an exact edge.  In particular,

```text
P_(t+1) = (1-p_(t+1)) P_(t+2),
d~_t(0) = (1-p~_t)d~_(t+1)(0) + p~_t d~_t(0) = 1,
```

and all nonowner debt equations are zero identities.  Owner 0's opponent
clock remains literally zero because no opponent ever quits.  The total
charge is a suffix of the original summable series, every root has positive
hazard, and `a~_t` tends to all-Continue.

The honest suffix payoff still keeps the Never boundary separate:

```text
U_i(a~^(t)) = A~_t r_i({0}),
v~_t(0) = d~_t(0) = 1,
v~_t(0)-U_0(a~^(t)) = 1-A~_t -> 1.
```

Hence the same selected owner satisfies

```text
eta <= d~_t(0) <= K_0,
v~_t(0) -> 1 >= eta,
sum opponent-clock = 0 <= log(52).
```

No tail property was weakened to accommodate `W`.

## 3. Exact canonical periodic evaluator

For a canonical shifted window, use the original absolute endpoints

```text
s=n+1,       e=2n+1.
```

Its pass survival and absorption are

```text
c_n = product_(k=s)^e (1-p_k) = P_s/P_(e+1),
m_n = 1-c_n > 0.
```

Periodic repetition therefore absorbs almost surely.  Only player 0 can be
the prescribed quitter, so the prescribed periodic delivery to player 2 is
exactly

```text
U_2(W~_n^infinity) = r_2({0}) = 0.
```

If player 2 stops at absolute phase `k` in the first pass, where `s<=k<=e`,
its exact payoff is

```text
B_(n,k) = [product_(u=s)^(k-1) (1-p_u)] (1-5p_k)
        = (P_s/P_k)(1-5p_k).                              (W1)
```

The factor `1-5p_k` is the payoff from quitting surely at that phase: player 2
gets `1` if player 0 Continues and `-4` if player 0 simultaneously Quits.

These first-pass phase values are strictly increasing.  With
`x=2^(k+1)>=4`, exact algebra gives

```text
(1-p_k)(1-5p_(k+1)) - (1-5p_k)
  = 6(x+1)/[(2x-1)(4x-1)] > 0.                            (W2)
```

Multiplication by the positive survival prefix preserves the inequality.
Every phase value is positive after the shift.  An occurrence in a later pass
is its first-pass value multiplied by `c_n^j<1`, and refusal/Never pays zero.
Consequently player 2's exact finite evaluator is

```text
max(refusal, all calendar stops) = B_(n,e),
```

the last phase of the first pass.  Thus the witness player is fixed, the
branch type is fixed, and even the within-window optimizer has the canonical
rule `phase(n)=n` (the last relative phase).

The first phase already supplies a uniform rational bound:

```text
B_(n,e) >= B_(n,s) = 1-5p_s >= 1-5/7 = 2/7 > 1/104=eta/2.
```

By the exact pure-stopping-time reduction, this finite maximum is the
supremum over **all unilateral behavioral deviations**, not merely pure or
stationary alternatives.  Therefore every reindexed canonical window obeys

```text
E(W~_n^infinity) >= 2/7 > eta/2.
```

The stabilized infinite set can be all `n>=0`.

## 4. Tail occupation: floor holds and funding fails

Every nonzero hazard in the selected tail belongs to player 0.  Hence every
normalized tail-window owner occupation, and every normalized singleton law
of its periodic restart, is exactly

```text
lambda^tail = e_0.
```

The annotation limit is

```text
z^tail = (1,1,1,1),
```

while its singleton mixture is column zero:

```text
m(lambda^tail) = (1,4,0,0).
```

The punishment floor **does hold**: `chi_i<=1=z^tail_i` for every player.
Complementarity holds on the only active atom, and the positive-debt owner is
that atom.  Funding nevertheless fails exactly in rows 2 and 3:

```text
z^tail_2 = z^tail_3 = 1 > 0
          = m_2(lambda^tail) = m_3(lambda^tail).
```

The periodic witness is player 2 on the phase branch, so this is the exact
phase-underfunded alternative in `CP172_ANSWER_REVIEW.md`: its phase value tends
to the solo/target value one while prescribed delivery is the unfunded
mixture coordinate zero.

The funded table-wide packet from `P` remains a different object.  It is not
silently identified with `lambda^tail`.  Thus the triple witness proves that
even exact common-tail canonical windows do not supply the missing occupation
and admissibility bridge `O`.

## 5. Separation from provenance and the global regime

### Optimized-minimizer/projective provenance

The shifted tail is an exact, indefinitely extendable rational tail in the
canonical boxes.  No cutoff-wise optimized zero-boundary chain is constructed,
no minimizing objective is checked, and no projective extraction from such
minimizers is proved.  The additional provenance field `M` remains open and
could exclude this tail.  Exposed triple consistency does not establish
`M x T x P x W` consistency.

### Global terminal instability A fails

At the discarded original date, repeat forever the stationary root in which
only player 0 quits with probability `p=1/3`.  Absorption is almost sure and
the prescribed payoff is

```text
w = r({0}) = (1,4,0,0).
```

Owner 0 is indifferent between Quit and Continue at value one.  Every
nonowner's pure-Quit endpoint is

```text
(1-p)1+p(-4) = -2/3,
```

whereas its Continue endpoint is its coordinate of `w`.  Refusal is already
the prescribed action for nonowners, and the pure-time reduction excludes any
profitable behavioral deviation.  This periodic profile is therefore an exact
equilibrium with exploitability zero.  The table cannot satisfy (A) for any
positive margin.

### Global charge capacity C fails

The same pair `(w,p)` is an exact Bellman self-loop in `[-4,4]^4`.  It is
punishment-floor admissible.  For players 0 and 1, opponents all Continuing
give `chi_i<=1<=w_i`.  For players 2 and 3, the opponent profile in which
player 0 Quits surely at date zero gives best-response value zero, so
`chi_2,chi_3<=0=w_2,w_3`.

Repeating this exact root as an outward chain of length `N` has charge

```text
Q_N = N/3.
```

Therefore the universal punishment-floor charge capacity is infinite.  This
table does not satisfy the global cluster `C` (equivalently condition (B)).
The exact failure is stronger than merely declining to claim `C`.

These two global failures also explain why suffix reindexing is harmless for
the exposed experiment but cannot manufacture a counterexample property of
the reward table.

## 6. Validation and scope

Run

```text
python Experiments/counterexample_pairwise_consistency/tpw_cyclic_four_triple_exact.py
lake env lean Experiments/counterexample_pairwise_consistency/TPWCyclicFourTripleWitness.lean
```

The Python probe uses `fractions.Fraction` only.  It expands the common table
and checks the shifted Bellman, Nash-endpoint, dynamic-debt, conservation,
honest-payoff, packet, occupation, canonical-window, evaluator, equilibrium,
and self-loop identities.  Its finite loops are regression audits; (W1)--(W2)
and the Lean scalar theorems carry the arbitrary-window proof.

`TailPacketCyclicFourWitness.lean` remains the exact proof of the universal
table-wide packet margin and the original arbitrary-date tail identities.
`TPWCyclicFourTripleWitness.lean` proves the shifted phase monotonicity, common
margin, symmetric packet arithmetic, and discarded-root self-loop arithmetic
without `sorry`.

This construction is four-player and makes no cardinal-minimality or player-
extension claim.  It establishes exact exposed triple consistency and no more:
the optimized provenance `M`, the occupation/admissibility bridge `O`, and the
global counterexample properties A/C are all kept distinct.
