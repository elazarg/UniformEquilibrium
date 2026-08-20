# `T x W x C`: exact attachment residual after provenance and coalition locks

## Classification

**Open at the full triple; exact interface witness and conditional theorem.**

The production optimized/projective provenance, debt conservation, periodic
window evaluator, and finite-capacity APIs do not currently force any of:

1. an exact endpoint return connector `Gamma_n`;
2. a suffix co-realizing an endpoint cap as both payoff and unilateral
   deviation envelope; or
3. a payoff-coordinate estimate that can replace either attachment.

There is one rigorous quantitative replacement, but it lives only in the
abstract capacity potential.  If a canonical cap word is already an exact
floor-admissible path of charge `Q_n`, the global capacity potential `B`
satisfies

```text
B(w_end) - B(w_start) >= Q_n.                            (1)
```

It has no known continuity or comparison with the cap coordinates, window
delivery, refusal value, or normalized endpoint drift.  Consequently (1)
does not attach `W` to `C`.

More strongly, finite capacity does not *produce* a return connector.  Once
the selected cap word is an exact positive-charge path, finite capacity
forbids every exact return connector.  Producing one from `T x W` would be the
desired contradiction, not a consequence of `C` alone.

This report supplies a new rational four-player model on the strict-joiner
table retained from Answer C.  It has one common positive-hazard exact-D tail,
canonical blocked windows from that tail, exact floor-cap transport for the
same actions, a zero-charge limiting cap, and bounded selected cap charge.  It
also passes **all** promoted pure-coalition-lock restrictions.  The model does
not prove universal `C`, and it is not proved to have cutoff-wise optimized
projective provenance.  Thus it is an exact lock-clean witness for the exposed
attachment equations, not a consistency witness for the full triple.

The executable checks are in
[`triple_t_w_c_lock_clean_probe.py`](triple_t_w_c_lock_clean_probe.py).

## 1. What the production interfaces actually supply

The distinction between the following four outputs is load-bearing.

### Optimized provenance `M`

`QuittingCounterexampleSeamWitness.projective_limit` says that the selected
tail is a projective limit of the canonical cutoff-wise optimized zero-boundary
exact-D tails.  `CounterexampleRegimeCapCarrier` uses precisely that field to
prove that every augmented cap

```text
w_t = v_t + d_t
```

is reward-boxed and dominates the complete behavioral punishment floor.  It
also proves convergence to a boxed, floor-admissible all-Continue cap and an
exact zero-charge self-loop at the limit.

It does **not** assert that consecutive finite caps form exact charged-relation
edges.  The module docstring explicitly fences this inference.

### Exact debt and the diagonal cap seam

For an exact-D edge with displayed root `x_t`, the production cap bridge gives
the coordinatewise identity

```text
w_t(i) = F(x_t,w_(t+1))(i) + e_t(i),
e_t(i) = x_t(i,Quit) d_t(i) >= 0.                        (2)
```

Thus projective provenance puts `w_t` in the correct carrier but does not put
the chronological cap transition in the exact relation.  Exact debt
conservation proves that the diagonal seams are summable, and the boxed debt
bound gives

```text
0 <= e_t(i) <= K_i q(x_t).                               (3)
```

For late canonical windows this is only an `O(m_n)` error.  Neither the API
nor (3) gives `o(m_n)`, and the punishment-floor relation has no approximate
edge or approximate-floor closure principle.

There is a useful exact local criterion.  Combining (2) with the dynamic-debt
maximum-of-endpoints identity gives:

> **Zero-seam cap lemma.**  On an exact-D edge with nonnegative successor
> debt, if `e_t=0`, the displayed root transports the augmented cap exactly
> and is exact Nash at that augmented continuation.  Conversely, exact cap
> Bellman transport by the displayed root forces `e_t=0`.

The forward Nash claim follows because the current cap is the maximum of the
two pure augmented endpoints, while zero seam says the displayed mixture
attains that maximum.  This paper deduction is not promoted here.  The probe
checks it directly on every edge of the model below.

Even `e_t=0` is not an attachment theorem: the model below has zero seam on
every date and still has a nonvanishing normalized cap drift and a fixed
periodic phase obstruction.

### Canonical windows `W`

`CounterexampleRegimePeriodicWindows` periodically repeats the actual product
root word and evaluates the resulting behavioral profile.  It obtains a
fixed player and either refusal or a concrete phase-stop branch on an infinite
set.  The evaluator makes no assertion that the periodic phase continuation
equals an augmented cap annotation.

### Global capacity `C`

The finite-prefix capacity controls every exact boxed path whose initial
annotation dominates the punishment floor.  Equivalently, the full
floor-admissible relation has a bounded budget-to-go potential `B` satisfying

```text
B(current) + q(edge) <= B(tail).                         (4)
```

The capacity API explicitly adds no strategic producer and no reachability
claim between two distinct admissible states.  Its potential need not be
continuous or semialgebraic.

## 2. The exact conditional attachment theorem

Fix a canonical window `[n,2n]`, put

```text
w_start = w_n,
w_end   = w_(2n+1),
Q_n     = sum_(t=n)^(2n) q(x_t).
```

Assume, in addition to carrier membership, that the zero-seam cap lemma
applies at every date of this window.  Reading the word in the outward
predecessor orientation gives an exact floor-admissible path

```text
P_n : w_end -> w_start
```

of charge `Q_n`.  Applying (4) along the path proves (1):

```text
B(w_start) + Q_n <= B(w_end).                            (5)
```

Now suppose an exact floor-admissible connector existed:

```text
Gamma_n : w_start -> w_end.
```

If its charge is `G_n>=0`, (4) also gives

```text
B(w_end) + G_n <= B(w_start).                            (6)
```

Adding (5) and (6) yields `Q_n+G_n<=0`.  Hence:

> **Exact-return exclusion.** Under finite global capacity, an exact selected
> cap segment with `Q_n>0` admits no exact floor-admissible endpoint return.

Equivalently, if `T x W` can produce `Gamma_n`, the full counterexample regime
is inconsistent immediately.  That production statement is exactly the
unproved attachment seam.

There is a parallel conditional realization theorem.  Suppose a suffix at
`w_end` has actual payoff exactly `w_end` and its complete unilateral
best-response envelope is at most `w_end`.  Prepending the exact cap-seeded
word makes its honest value and finite stopping cap coincide at every earlier
date.  `QuittingCapSeededPrefix.finiteTerminalBestResponseValue_eq_cap` then
controls every finite stop in the prefix, while the suffix hypothesis controls
all deviations entering the suffix.  The concatenated profile is
zero-exploitable.  Under the full terminal-gap hypothesis this is impossible.

No such suffix is supplied by `T`, `W`, or `C`.  In particular, the periodic
window itself is not one: its realized continuation is precisely where the
stabilized `W` deviation is profitable.

These are proved **conditional seams**.  The assertion that every blocked
canonical window yields either connector or co-realizing suffix remains a
conjectural seam-to-return dichotomy.

## 3. A lock-clean rational interface model

Let the players be `I={0,1,2,3}`.  The singleton rewards are the columns

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

Every triple pays zero to its members and `1/8` to its spectator; the grand
coalition pays zero.  The sharp reward bound is `M=2`.

All rewards are nonnegative, so Never proves `chi_i>=0`.  If all three
opponents Quit at date zero, Continue pays `1/8` and joining pays zero, so

```text
0 <= chi_i <= 1/8.                                      (7)
```

The exact value of `chi` is not needed below.

### Common exact-D tail

Put `k=t+4` and

```text
p_t = 1/k^2,
z_t = (k-1)/k,
x_t = (0,p_t,0,0).
```

Only player `1` carries physical hazard.  With `r({1})` denoting the singleton
column above, prescribe

```text
v_t = r({1}) + (3/4) z_t e_0,
d_t =             (1/2) z_t e_0.                        (8)
```

The identity

```text
z_t = (1-p_t)z_(t+1)                                    (9)
```

proves exact Bellman transport.  Player `1` mixes between two endpoints equal
to `1`.  Players `2,3` strictly Continue because watching singleton `1` pays
`5/3`, above both their solo and collision endpoints.  Player `0` strictly
Continues: its Quit endpoint is

```text
1-p_t/12,
```

whereas `v_t(0)>=59/48`.

The exact dynamic-debt maximum for player `0` selects Continue and (9) gives

```text
d_t(0)=(1-p_t)d_(t+1)(0).
```

Every other debt update is zero.  Thus (8) is a literal exact-D tail.  For the
common positive scale `eta=1/4`,

```text
eta < 3/8 <= d_t(0) < 1=K_0,
v_t(0) -> 17/12,
d_t(0) -> 1/2.                                          (10)
```

The infinite tail survives with probability `z_t`; its honest suffix payoff
is

```text
(1-z_t) r({1}) = r({1})/(t+4) -> 0.                     (11)
```

Also `p_t <= 1/((k-1)k)`, so joint absorption is summable.  Exact deleted
survival equals `d_t(0)/d_(t+1)(0)`.  The standard `p<=-log(1-p)` inequality
therefore gives the owner clock bound, uniformly below `log(K_0/eta)=log 4`.

### Exact cap path

The augmented cap is

```text
w_t = r({1}) + (5/4)z_t e_0.                            (12)
```

The only positive-debt player `0` never Quits, and the only mixing player `1`
has zero debt.  Hence every diagonal seam in (2) is exactly zero.  Direct
endpoint checks give

```text
w_t=F(x_t,w_(t+1))
```

with `x_t` exact Nash at `w_(t+1)`.  By (7), every cap is punishment-rational;
all coordinates lie in `[-2,2]`.  The limit is

```text
w_infinity=(23/12,1,5/3,5/3),                           (13)
```

where all-Continue is an exact zero-charge self-loop.

The selected cap charge is genuinely bounded.  Indeed, for `k>=4`,

```text
w_(t+1)(0)-w_t(0) = (5/4)/(k(k+1)) >= 1/k^2=p_t.        (14)
```

This is a bound only on the selected exact cap ray, not universal `C`.

### Canonical windows and the fixed phase branch

For the inclusive canonical word `W_n=(x_n,...,x_(2n))`, exact telescoping
gives one-pass survival

```text
P_n = (n+3)/(n+4) * (2n+5)/(2n+4),
m_n = 1-P_n > 0.                                       (15)
```

Periodic repetition absorbs almost surely only through singleton `1`, so its
delivery is exactly `r({1})`.  Player `0` can stop at phase zero for value

```text
1-p_n/12.
```

Therefore the phase-zero gain is at least

```text
1 - 1/192 - 2/3 = 21/64 > 1/4 > eta/2.                 (16)
```

The witness player and branch are fixed for every canonical window.

The exact restart identities expose the first-order mismatch:

```text
(P_n/m_n)[v_(2n+1)(0)-v_n(0)] = v_n(0)-2/3 -> 3/4,
(P_n/m_n)[w_(2n+1)(0)-w_n(0)] = w_n(0)-2/3 -> 5/4.     (17)
```

Thus even zero diagonal seam, exact shared cap actions, debt conservation,
floor membership, and bounded selected charge do not make the normalized
attachment error vanish.

At the actual periodic continuation `2/3`, player `0`'s prescribed Continue
action is beaten by Quit, whose endpoint is `1-p_n/12`.  At the cap
continuation it is exact because Continue is worth `w_n(0)`.  The same root
word therefore remains behavioral-periodic but not annotated-periodic.

## 4. Coalition-lock audit

The promoted restriction is stronger than the original singleton screen:
full finite capacity forbids every nonempty pure quitting coalition stable
against all unilateral membership toggles.  The probe checks all `15`
nonempty coalitions.  For each set `S`, `r(S)` is the Bellman fixed point of
the pure `S` root, but that root is **not** exact Nash.  Hence the table has no
pure coalition lock.

For the singleton cases, the designated strict joiners are

```text
0 -> 2,   1 -> 0,   2 -> 3,   3 -> 1.
```

Each join payoff exceeds the singleton spectator payoff by exactly `1/4`,
and its solo endpoint is also strictly better.  The affine gain is therefore
positive at every owner rate in `[0,1]`.

This audit is only a necessary global-capacity screen.  It says nothing about
mixed exact roots, positive charged cycles, or arbitrarily long nonrecurrent
paths.

## 5. What the exact model does and does not establish

The model establishes, on one reward table and one common tail:

1. exact positive-hazard Nash--Bellman and dynamic-debt `T` equations;
2. summable absorption, positive limiting owner debt, the deleted-clock bound,
   and vanishing honest late-tail delivery;
3. the canonical `W` family with one fixed phase witness and a uniform margin;
4. boxed punishment-rational caps, exact zero-seam transport by the same root
   words, bounded positive selected cap charge, and a limiting zero-charge
   all-Continue loop; and
5. every promoted pure-coalition-lock exclusion.

It does **not** establish either load-bearing full clause:

- `G`: finite charge capacity on the complete exact floor-admissible root
  correspondence; or
- `M`: projective origin from cutoff-wise optimized zero-boundary minimizers.

Neither clause may be inferred from the exact selected cap ray.  Passing all
coalition-lock screens does not prove `G`, and a hand-built exact-D tail does
not prove `M`.  The table is therefore a lock-clean interface candidate, not
a counterexample regime and not a full triple witness.

For comparison, the simpler local cap table in
[`TC_PHANTOM_CAPACITY_REPORT.md`](TC_PHANTOM_CAPACITY_REPORT.md) satisfies the
same selected-tail/cap/window pattern but fails `G` explicitly: singleton
`{0}` is a punishment-rational exact self-loop of charge one.  The new probe
rechecks that negative control.  This is why `C` is never inferred from a
selected cap path.

## 6. Residual theorem, stated without overclaim

The remaining central triple problem is:

> Starting from the **actual optimized/projective** exact-D tail of a full
> counterexample regime, use a stabilized canonical-window obstruction and
> the complete global capacity geometry to produce either (a) a zero-seam
> exact cap segment plus an exact endpoint return, or (b) a suffix co-realizing
> the endpoint cap as payoff and deviation envelope, or (c) a new quantitative
> comparison between the capacity potential and the normalized behavioral
> drift.

The present work proves only the conditional consequences after (a) or (b)
has been produced.  It also proves by exact model that all local equations,
even after eliminating every pure coalition lock and every diagonal seam, do
not themselves produce the attachment.

The capacity-potential separation (1) is the strongest currently justified
version of (c).  Because no regularity or payoff comparison for `B` is known,
using it to close the seam remains conjectural.

## Validation

Run

```text
python Experiments/counterexample_pairwise_consistency/triple_t_w_c_lock_clean_probe.py
```

The probe uses exact rational arithmetic only.  It checks the complete
15-coalition reward table, the behavioral floor enclosure (7), all pure
coalition-lock exclusions, `256` exact-D and cap edges, `128` canonical
windows, exact survival and restart identities, the fixed phase-zero margin,
positive bounded selected cap charge, the limiting exact cap loop, and the
charge-one negative control.  Infinite-tail and arbitrary-window conclusions
use the closed formulas above, not finite-search extrapolation.

The probe intentionally prints `UNPROVED` for universal `C` and optimized
projective provenance.  No bounded search is presented as evidence for either.
