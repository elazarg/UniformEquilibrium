# Whole-packet gate: carrier-source charge/debt/error alternative

Reviewer: `CODEX_EULER`

Packet reviewed:
[`FIN4_CARRIER_SOURCE_CHARGE_DEBT_ERROR_GATE.md`](../formalized/FIN4_CARRIER_SOURCE_CHARGE_DEBT_ERROR_GATE.md)

Verdict: **PASS**.  No repair or demotion is required.

## Statement, orientation, and proof

The Fin4, carrier-source, finite-path, product-root, and aggregate-error
quantifiers are complete.  In the forward semantic direction each root is
Nash against `W_s` and produces `W_(s+1)`.  Reversing the finite list puts the
identities in the reviewed form

```text
V_t=Succ(V_(t+1),r_t)
```

and places the actual carrier source at `V_L=W_0=X.1`.  This agrees with the
charged relation's tail-to-current semantic direction.

The `Far` subset is compact and disjoint from the complete minimum fiber.
Its nonempty debt minimum is strictly above `D_*`; the empty case is handled
correctly.  Thus `eta_a` gives the stated inner-collar implication.  The
choice

```text
e_a=min(c rho/(16C),ca/4)
```

has the exact Fin4 constants.  Failure of both alternatives yields

```text
a <= max absorption <= sum absorption <= 4E/c < a.
```

The exact path and asymptotic consequences follow without a path-length
bound or endpoint near-return assumption.

## Adapter, probability, and semantic scope

The floor-path specialization requires the source payoff to be literally the
prescribed coordinate of an actual carrier; arbitrary payoff-only floor
states are explicitly excluded.  Product absorption and one-stage root Nash
are not mislabeled as unrestricted behavioral equilibrium.  Reversal adds no
randomization or cross-date independence assumption.

The paid adapter is source-exact.  `fullReplacementPair` is definitionally
the semantic pair of `fullReplacementProfile`, and the checked convergence
field plus strict cluster debt separation gives the eventual `g/2` gap.
Those are the profiles carrying the eventual paid rows.  The packet correctly
concludes that the minimum fiber cannot serve as a low-error charging/restart
port while the already off-minimum paid cluster survives the theorem.

## Export criteria

The packet strictly narrows the named paid near-return producer by a fixed
carrier-source debt/error gate.  Its five boundary tests cover carrier
provenance, aggregate versus rowwise error, fixed charge, reversal, and the
surviving paid cluster.  The checked minimum-fiber, linear-path, paid-source,
and full-replacement declarations are accurately separated from the new
composition.  The Lean handoff preserves source payoff and edge orientation
without assuming the dichotomy as a structure field.

All `exports/README.md` gates are satisfied.  The nonclaims correctly leave
root/edge production, floor repair, off-minimum descent, repayment, cap
replacement, and uniform payoff open.
