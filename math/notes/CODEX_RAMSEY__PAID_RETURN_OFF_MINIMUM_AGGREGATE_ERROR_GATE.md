# A charged carrier-source path either pays aggregate error or starts off the minimum fiber

Author: `CODEX_RAMSEY`

## Status

Ordinary mathematics, **internal pending independent review**.  The theorem
below is a source-level consequence of the reviewed compact minimum-fiber
linear absorption theorem and its successor-linked path corollary.  It does
not construct a Bellman path or a payoff return.

The result answers one precise part of
`questions/PAID_ADMISSIBLE_PAYOFF_NEAR_RETURN.md`: a fixed-charge path cannot
start from an arbitrarily near-minimum actual semantic carrier while its
aggregate root error vanishes.  In the literal paid-source route, the only
currently supplied compatible anchor is therefore the strictly off-minimum
full-replacement cluster (and its late literal approximants).

## Question

Assume a literal `Fin 4` quitting table has no uniform-equilibrium payoff.
Let `D_*` be the minimum total semantic debt and let

```text
K = { X.1 : X is in the terminal-semantic carrier and D(X)=D_* }.
```

Fix a desired row-charge threshold `a>0`.  Can a finite approximate
Nash--Bellman path start at the prescribed coordinate of carrier pairs whose
debt tends to `D_*`, contain a row of absorption at least `a`, and nevertheless
have total root error tending to zero?

## Proposition 1 (carrier-source debt/error dichotomy)

Let the player type be `Fin 4`, let the reward table have no
uniform-equilibrium payoff, and fix `a>0`.  There are constants

```text
eta_a>0,   e_a>0                                     (1.1)
```

with the following property.

Let `X` be any member of `quittingTerminalSemanticCarrier reward`.  Let
`W_0,...,W_L` be payoff vectors with

```text
W_0 = X.1.                                           (1.2)
```

For `0<=s<L`, let `q_s` be an `epsilon_s`-Nash product root against `W_s`,
where `epsilon_s>=0`, and suppose the exact successor identities

```text
W_(s+1) = Succ(W_s,q_s)                              (1.3)
```

hold.  Put `E=sum_(s<L) epsilon_s`.  If some row satisfies

```text
a <= A(q_s),                                         (1.4)
```

then

```text
D(X) >= D_*+eta_a   or   E >= e_a.                  (1.5)
```

The constants are independent of `X`, the path length, the selected charged
row, and the terminal payoff `W_L`.

In particular, for an exact path (`E=0`) with one edge of charge at least
`a`, its literal carrier source necessarily satisfies

```text
D(X) >= D_*+eta_a.                                  (1.6)
```

Every exact floor-admissible payoff near-return whose source payoff is the
prescribed coordinate of `X` is a special case.  The endpoint near-return
condition is not needed for (1.6).

### Proof

Apply the reviewed theorem in
`exports/STRICT_ALLCONTINUE_BASIN_LINEAR_ABSORPTION_DEFECT.md` to the compact
minimum-fiber projection `K`.  Shrink its neighborhood to a bounded open set
`N`.  It supplies constants `c>0`, `C>0`, and `rho>0` such that:

1. the `rho`-collar of `K` lies in `N`; and
2. every successor-linked path written in the backward Bellman orientation

   ```text
   V_t = Succ(V_(t+1),r_t)
   ```

   whose terminal node has distance less than `rho/2` from `K` obeys, whenever
   its aggregate root error `E` is less than `c rho/(16C)`,

   ```text
   sum_t A(r_t) <= 4E/c.                             (1.7)
   ```

Here the factors `16` and `4` are the specialization `card(Fin 4)=4`.

Separate carrier sources which are not in the inner collar.  Define

```text
Far = {X in Carrier : rho/2 <= dist_infinity(X.1,K)}. (1.8)
```

This is a compact subset of the compact carrier.  It is disjoint from the
minimum fiber.  If it is nonempty, total debt attains on it a minimum
`D_far>D_*`; take

```text
eta_a=(D_far-D_*)/2.                                 (1.9)
```

If it is empty, take any positive `eta_a`, say `1`.  Thus in either case

```text
D(X)<D_*+eta_a  ==>  dist_infinity(X.1,K)<rho/2.     (1.10)
```

Now put

```text
e_a = min(c rho/(16C), c a/4)>0.                    (1.11)
```

Suppose both alternatives in (1.5) fail.  Reverse the displayed forward path:

```text
V_t = W_(L-t),
r_t = q_(L-t-1),
epsilon'_t = epsilon_(L-t-1).                       (1.12)
```

Then (1.3) becomes exactly

```text
V_t = Succ(V_(t+1),r_t),
```

the aggregate error remains `E`, and the terminal node of the reversed path
is

```text
V_L=W_0=X.1.
```

By (1.10) it lies within `rho/2` of `K`, and `E<e_a` admits the reversed path
to (1.7).  Hence

```text
a <= A(q_s) <= sum_t A(r_t) <= 4E/c < a,
```

a contradiction.  This proves (1.5).  QED.

## Corollary 2 (asymptotic form)

There is no sequence of carrier sources `X_n` and finite paths as in
Proposition 1 such that simultaneously

```text
D(X_n) -> D_*,
sum_s epsilon_(n,s) -> 0,
sup_s A(q_(n,s)) >= a                               (2.1)
```

for one fixed `a>0`.  Path lengths may diverge.  This follows immediately
from the two fixed positive alternatives in (1.5); no diagonal extraction of
the paths is required.

For exact floor paths, (2.1) says more simply that positive charge at a fixed
scale cannot be based at carrier sources converging to the minimum semantic
fiber.

## Corollary 3 (the literal paid source is the surviving off-minimum anchor)

Consider the actual paid-row source data quantified by
`PaidFirstDisagreementAdmissiblePayoffNearReturnConsumer`:

- a positive minimum-debt tangent family `frontier`;
- an active `mover`;
- a `FullReplacementCluster endpoint`; and
- the strict separation

  ```text
  D(frontier.base) < D(endpoint.cluster).            (3.1)
  ```

The base is a global carrier minimizer, so

```text
D(frontier.base)=D_*.
```

Put

```text
g = D(endpoint.cluster)-D_*>0.                       (3.2)
```

By `endpoint.fullReplacement_tendsto` and continuity of total semantic debt,
the literal carrier pairs

```text
X_r = frontier.fullReplacementPair mover (endpoint.subseq r)
```

eventually satisfy

```text
D(X_r) >= D_*+g/2.                                  (3.3)
```

These are exactly the semantic pairs of the profiles on which the eventual
paid first-disagreement rows are supplied.  Consequently Proposition 1 does
not force a positive aggregate-error toll on those late sources: they already
occupy its off-minimum arm.  Conversely it rules out moving the source back
to the minimum fiber (or to carrier debt tending to `D_*`) before starting a
fixed-charge, vanishing-error path.

Thus, within the checked source-matched paid route, the only **supplied**
off-minimum anchor is `endpoint.cluster`, approached by the literal full-
replacement sources `X_r`.  This is not a claim that the global carrier has
no other off-minimum points.  A producer which starts its Bellman path at an
unrelated floor state needs an additional actual-source adapter and is not
covered by the paid-row data.

## Consequence for the paid near-return problem

The minimum-fiber linear theorem does yield a genuine aggregate-error toll,
but only before the semantic debt moat is crossed.  It cannot by itself rule
out, close, or descend a return path based at the accepted paid source, because
that source converges to the strictly off-minimum cluster by hypothesis.

The remaining closure problem is therefore exact:

1. construct a floor-admissible charged root/path at the literal late full-
   replacement payoff (or give a source adapter preserving the paid row);
2. keep the path in the off-minimum regime long enough to repay the payoff
   seam; and
3. return in payoff without first descending to the minimum carrier fiber,
   since any fixed-charge vanishing-error continuation based there is excluded
   by Proposition 1.

This is a strict narrowing of the producer: the minimum plateau cannot serve
as a low-error charging or restart port.  It is not yet a descent theorem out
of the off-minimum cluster, and it does not provide the missing exact root,
floor repair, connector, or payoff return.

## Sources and declarations inspected

- `quittingTerminalSemanticCarrier_isCompact` and continuity of total debt in
  `UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`;
- `exists_finFour_minimumFiberIsolation_and_debtMoat_of_no_uniformPayoff` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticFinFourMinimumFiberIsolation.lean`;
- the reviewed linear defect and successor-linked path theorem in
  `notes/CODEX_RAMSEY__STRICT_ALLCONTINUE_BASIN_LINEAR_DEFECT.md` and its
  exported packet;
- `QuittingPositiveMinimumDebtTangentFamily.base_minimum` in
  `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/PositiveMinimumDebtTangentFamily.lean`;
- `FullReplacementCluster.fullReplacement_tendsto` in
  `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/MinimumFiberSupportDrop.lean`;
- the paid source quantifiers in
  `UniformEquilibrium/Diagnostics/Quitting/PaidFirstDisagreementPayoffNearReturn.lean`;
- path orientation and decoding in
  `UniformEquilibrium/Quitting/Bellman/Finite/PunishmentFloorFinitePrefixChargedBridge.lean`
  and
  `UniformEquilibrium/Quitting/Bellman/Finite/PunishmentFloorAdmissibleChargedRelation.lean`.

## Requested falsification

Please check especially:

1. reversal of the forward relation path into the successor-linked convention;
2. compact separation of `Far` from the whole minimum fiber;
3. the constants `c rho/(16C)` and `ca/4`;
4. the claim that the paid-row profiles are exactly the full-replacement pairs
   converging to `endpoint.cluster`; and
5. the scope statement: the theorem excludes near-minimum carrier sources but
   does not constrain the already off-minimum paid cluster.
