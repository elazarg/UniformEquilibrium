# Exact boundary of the Fin4 uniform-escape terminal packet

## Status

This note audits the complete source-attached uniform-escape packet against the
existing terminal compilers.  It derives two additional exact consequences:

1. a uniform source-prefix absorption bound coming from the off-minimum tail;
2. an exhaustive orientation/screening split for the fixed payer endpoint.

These consequences do **not** yet produce a terminal approximate Nash family,
a cumulative admissible-payoff near-return, a contradiction with positive
minimum debt, or a positive-gap reward table.  The packet is therefore not
consumed here.  The point of the note is to isolate the remaining bridge at the
level of the literal source chronology, rather than replacing it by another
carrier point or another static endpoint.

## Fixed notation

Let `D_* > 0` be the global minimum terminal-semantic debt, let the retained
atom mass be `mu > 0`, and put

```text
lambda = mu^2 / 8.
```

At retained rank `n`, write

- `sigma_n` for the literal source realizer before the selected cap--Nash
  prefix is attached;
- `t_n` for its actual marked date;
- `T_n` for its literal post-date behavioral tail;
- `ell_n` for the probability of reaching date `t_n` alive;
- `c_n` for the probability of continuing jointly through date `t_n`; and
- `L_n` for the finite-prefix weighted cap-defect ledger through date `t_n`.

The source convergence gives

```text
D(sigma_n) -> D_*.
```

The uniform-escape arm gives one fixed `delta > 0` with

```text
D(T_n) >= D_* + delta.
```

The marked pure pair has unconditional mass at least `lambda`, hence

```text
ell_n >= lambda.
```

Because every individual survival factor is at most one, every deleted
survival probability to the same marked date is also at least `lambda`.
Thus this packet is not in the vanishing deleted-survival/full-screening arm.

## The exact prefix identity

Apply the finite-word debt telescope to the actual roots of `sigma_n` through
`t_n`.  The complete post-date spine retained by the packet identifies the
continuation in that telescope with `T_n`, giving

```text
D(sigma_n) = L_n + c_n * D(T_n),
0 <= L_n,
0 <= c_n <= 1.
```

The selected outer cap--Nash word contributes zero local ledger.  The term
`L_n` is the ledger of the literal source segment leading to the marked date;
it need not vanish.

Consequently, for every `eta` with `0 < eta`, eventually

```text
L_n + c_n * (D_* + delta) <= D_* + eta.
```

In particular, if `0 < eta < delta`, then eventually

```text
c_n <= (D_* + eta) / (D_* + delta)
```

and therefore

```text
1 - c_n >= (delta - eta) / (D_* + delta).
```

Taking `eta = delta / 2` gives the uniform quantitative bound

```text
1 - c_n >= delta / (2 * (D_* + delta))
```

at all sufficiently large retained ranks.

This is a source-matched positive absorption statement.  It is not yet a
positive admissible return: the same identity permits the source ledger
`L_n` to pay the whole difference between the source and the off-minimum tail.
No field of the packet bounds `L_n` by the marked payer charge or rewrites it as
a sum of punishment-floor admissible Bellman edges.

## The fixed payer has only two orientations

The forced pair is

```text
S = {j, q},
```

with `j != q`, and the payer satisfies `p != q`.  The payer's actual endpoint
gain is positive, so the selected Boolean action differs from the payer's
current action at the pure pair.

There are exactly two cases.

### Deletion orientation

If the selected action is `false`, then `p` belongs to `S`.  Since `p != q`,
necessarily

```text
p = j.
```

The paid target coalition is the singleton

```text
{q}.
```

The pair source is tail-screened, but at the paid singleton player `q` can
continue and expose the literal tail `T_n`.  This is the only orientation in
which the uniform tail gap can enter a one-player endpoint comparison.
However, the packet supplies no exact cap--Nash root or admissible temporal
edge for that `q`-continuation, and no payoff return from the resulting tail to
the incoming source.  Treating the horizontal deletion itself as that temporal
edge would change the outer continuation and invalidate the stored roots.

### Join orientation

If the selected action is `true`, then `p` does not belong to `S`.  The paid
target coalition is

```text
{j, q, p}.
```

Both the pair and the triple screen the continuation against every unilateral
deviation at the marked date: after changing one player's action, at least one
other prescribed quitter remains.  Hence the payoffs and unrestricted caps of
these two pure marked profiles are independent of `T_n` after the marked date.
The inequality

```text
D(T_n) >= D_* + delta
```

therefore cannot pay the horizontal payer gain in this orientation.  It only
constrains the earlier literal source prefix through the telescope above.

## Why strict source ranks do not telescope the paid gains

The retained ranks are cofinal source ranks, but the selected realizers and
cap words at two ranks are not required to be nested.  The target at rank
`n + 1` is not the continuation of the paid target at rank `n`.  Therefore

```text
actualGain_p(n) >= lambda * D_* / 3
```

cannot be summed over ranks as a chronological charge.  Such a sum would use
horizontal alternatives from different source realizers as if they were
successive dates of one behavioral profile.

The same issue blocks a compact-limit argument: a limit of the pair and paid
semantic vectors retains the strict payer comparison, but it does not retain
an exact outer-root fixed-point identity or a backward compiler across the
horizontal seam.

## Relation to the existing consumers

`FinFourUniformEscapePacket.exists_maximalCapNash_halfFloorDispatch` applies a
maximal-absorption exact cap--Nash dispatch directly to each literal tail.  It
returns either a same-tail near-minimum selection or universal same-tail
undercharge.  It deliberately does not provide the reset-coordinate premise
or payoff recurrence required by the all-behavior compiler.

`QuittingPaidCapLiftedSource.exactTrichotomy` would close the present branch if
one could construct, from the packet itself, a source-matched paid cap port
with

```text
positive total absorption
```

and

```text
vanishing cap displacement.
```

The first quantity is available only for the literal source prefix through the
bound above.  The paid gain is available only at the horizontally replaced
pure pair.  The packet contains no checked identity equating those two
objects, and supplies no bound forcing the cap displacement across that seam
to vanish.

## Exact remaining bridge

A terminal consumer can now be reduced to either of the following equivalent
source-level constructions.

### Ledger-payment form

For a cofinal subsequence, decompose the actual source ledger `L_n` into a
punishment-floor admissible chronological path which

- keeps the literal post-date tail `T_n`;
- contains the marked pair-to-paid endpoint with charge at least
  `lambda * D_* / 3`;
- has a fixed positive cumulative retained charge; and
- has endpoint payoff displacement tending to zero.

### Seam-exactification form

After inserting the paid endpoint at the actual marked date, exactify the
outer roots while preserving

- a fixed positive reach/absorption floor;
- the complete literal post-date behavioral tail and outcome law;
- the payer's fixed positive charge; and
- cap displacement tending to zero.

Either form feeds the existing cumulative-charge or paid-cap all-behavior
compiler.  Neither form follows from the current packet fields.

## Conclusion

The complete uniform-escape packet proves more than an unrelated off-minimum
tail: it forces a fixed positive absorption budget in the actual source
prefix, rules out vanishing deleted reach, and leaves only the singleton
`p = j` orientation capable of exposing the tail at the paid endpoint.
Nevertheless the positive absorption and positive payer charge live on
opposite sides of a non-Nash horizontal seam.  The unchecked step is exactly
the conversion of the source prefix ledger into an admissible paid chronology,
or an exactification theorem that preserves the paid row.

Accordingly this note is an exact boundary result, not one of the terminal
outputs requested by the Fin4 uniform-escape question.