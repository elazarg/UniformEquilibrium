# Renewable resolution along Fin4 minimum regeneration

## Scope

This note removes one quantitative obstruction from repeated
`FinFourThreeRoleMinimumTargetRegeneration`.  It does **not** orient the
regenerated endpoint edge and therefore is not a consumer of the
minimum-return component by itself.

The relevant checked interfaces are:

- `FinFourThreeRoleMinimumTargetRegeneration.resolution_le_terminalMass`,
  which says that the fresh producer's retained atom mass is at least the
  incoming packet resolution; and
- `FinFourOwnerCompressedMinimumReturnForcedPairBase.lambda_lt_terminalMass`,
  whose compression scale may be any positive real strictly below the
  retained atom mass.

Consequently repeated regeneration does not force the canonical squaring
`mu |-> mu^2 / 8` at every generation.  One can choose the next packet scale
adaptively and keep all scales uniformly positive.

## Resolution schedule

Fix an initial resolution `rho_0 > 0` and put

```text
delta = rho_0 / 2,
rho_n = delta * (1 + 1 / (n + 1)).
```

Then

```text
rho_0 = rho_0,
delta < rho_n,
rho_{n+1} < rho_n,
rho_n -> delta.
```

Suppose generation `n` uses resolution `rho_n` and its minimum endpoint
regenerates a fresh producer.  If `m_{n+1}` is the mass of the retained atom
of that producer, the checked regeneration inequality gives

```text
rho_n <= m_{n+1}.
```

Since `rho_{n+1} < rho_n`, one has

```text
0 < rho_{n+1} < m_{n+1},
```

which is exactly the strict scale premise needed to run the next owner
compression.  Induction therefore constructs every finite regeneration
chain with

```text
rho_n > delta = rho_0 / 2.
```

The same argument supports an infinite dependent-choice construction once a
source-to-packet producer is fixed at each fresh source.

## Uniform quantitative consequences

All endpoint inequalities depending monotonically on the packet resolution
remain uniformly charged along such a chain.  In particular, with fixed
positive minimum debt `D_*`, every regenerated three-role endpoint satisfies

```text
mover debt drop >= delta^2 * D_* / 8,
recipient debt rise >= delta^2 * D_* / 64.
```

Likewise any paid-cycle atom charge whose lower bound is linear in the packet
resolution retains a fixed positive lower bound obtained by replacing
`rho_n` with `delta`.

Thus vanishing regeneration scale cannot explain an indefinite
minimum-return obstruction.  The remaining problem is genuinely one of
orientation: the charged debt drop is from the packet's auxiliary minimum
`sourceLimit` to the regenerated target point, while the next packet is built
from the regenerated producer point.  No checked equality currently
identifies that next packet's auxiliary `sourceLimit` with the preceding
regenerated target, and source-faithful causalization does not insert the old
horizontal edge into the fresh chronology.
