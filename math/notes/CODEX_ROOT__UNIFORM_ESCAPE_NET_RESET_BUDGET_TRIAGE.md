# Uniform-escape net-reset budget and inert-cap triage

## Status

Initial mathematical assessment only. The argument below has nonzero value as
an accurate localization of the `FinFourUniformEscapePacket` obstruction, but
it is not a consumer, rank descent, counterexample, or proof of uniform
equilibrium.

The useful content is twofold:

1. the forced-pair paid endpoint and the positive tail-debt excess are
   genuinely orthogonal; and
2. the retained arbitrary prefix word carries a positive *signed net-reset
   budget*, but current exactification theorems do not turn that scalar budget
   into an admissible chronology.

## Question

Given a source-attached `FinFourUniformEscapePacket`, can its uniformly
off-minimum literal tails be converted into one of:

- a positive-charge punishment-floor near-return;
- terminal approximate Nash profiles;
- a renewable finite-rank source transition; or
- a contradiction to the Fin4 hard residual?

The packet's currently checked maximal-cap dispatch does not yet give any of
these conclusions.

## Valid core

### Pure-pair screening

At the marked pure pair, changing either one player's strategy still leaves
another sure quitter at that date. Consequently the changed player's payoff,
cap, and exact debt subtraction at the marked row are screened from the
post-date continuation. The paid forced-pair edge therefore does not, by
itself, consume the uniform lower bound

```text
D(tail_n) >= D_* + floor.
```

This is a substantive warning: the paid endpoint and the tail excess are
stored in the same source packet, but they are not the same chronological
resource.

### Cross-rank gains do not telescope

If `A_n -> B_n` is the paid endpoint move at rank `n`, then its mover's cap is
unchanged and its debt falls by the paid gain. But generally `B_n` is not the
next source `A_(n+1)`. For a stabilized payer `p`, the exact account is

```text
d_p(A_N) = d_p(A_0)
           - sum_{n < N} gain_n
           + sum_{n < N} rho_n,

rho_n = d_p(A_(n+1)) - d_p(B_n).
```

Thus fixed paid gains can be replenished between ranks. Any iteration theorem
must control this replenishment or provide literal successor attachment.

### Positive net-reset budget

Write one retained literal source as a finite root word above its actual tail,

```text
R_n = W_n ▷ T_n.
```

If `s_(n,t)` is survival to row `t`, `e_(n,t)` is the total root cap defect at
that row against its actual continuation, and `s_n` is survival through the
whole word, the exact prefix ledger is

```text
D(R_n) = s_n D(T_n) + sum_t s_(n,t) e_(n,t).
```

Since the source debts tend to `D_*` while the escape packet has
`D(T_n) >= D_* + floor`, eventually

```text
floor / 2
  <= (1 - s_n) D(T_n) - sum_t s_(n,t) e_(n,t).
```

This is a real quantitative consequence. It says absorption potential in the
literal word exceeds its accumulated root defects by a fixed amount.

It is nevertheless a signed scalar account, not an ordered exact
Nash--Bellman path: the literal roots contributing to the right-hand side need
not be exact cap--Nash roots. Treating this inequality as chronological charge
would be the missing step, not a consequence already proved.

## Exactification boundary

`FinFourUniformEscapePacket.exists_maximalCapNash_halfFloorDispatch` produces,
at every retained tail, a maximal-absorption exact cap--Nash root and then:

- a same-tail reset-return selection; or
- universal same-tail undercharge, together with either all-Continue being an
  exact cap root or a quantitative blocker.

The bundled `FinFourUniformEscapeConsumed` records precisely this dispatch and
is explicitly not a reset compiler.

One qualification is essential: this theorem gives **all-Continue exactness**
in one subarm, not uniqueness of all-Continue. The stronger conclusions that
every exact cap stack is a literal all-Continue stack, fixes the complete
semantic/law point, and has zero charge require a separately supplied unique
all-Continue hypothesis. Those conditional facts are checked in
`UniqueAllContinueCapStackNoGo.lean`; they must not be inferred from the escape
dispatch alone.

Thus the honest residual split is:

```text
positive exact return
or same-tail undercharge with an all-Continue root/blocker;

and, only if uniqueness is established separately,
literal zero-charge inert cap stacks.
```

## Strongest justified conclusion

The uniform-escape packet contains a fixed positive reset surplus before
exactification, while exactification can lose access to that surplus by
changing the roots and may expose an all-Continue cap obstruction. The missing
producer is therefore not another tail-debt estimate. It must connect the
literal net-reset budget to exact ordered roots, or prove that the resulting
all-Continue/blocker configuration is impossible or renewable.

A sharp next question is:

> Does the source-attached positive net-reset budget force either an exact
> half-floor return at some retained rank, a renewable finite-rank transition,
> or a Fin4 hard-residual contradiction, even when all-Continue is an exact cap
> root at every undercharged rank?

## Repository declarations inspected

- `quittingTerminalSemanticDebt_prefix_eq_continueMass_mul_add_capDefect` and
  `quittingTerminalSemanticDebtSum_prefix_eq_continueMass_mul_add_capDefect` in
  `UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/CapDebtBellmanReduction.lean`.
- `FinFourUniformEscapePacket.exists_maximalCapNash_halfFloorDispatch` and
  `FinFourUniformEscapeConsumed` in
  `Research/Quitting/FinFourProducerAtlas/SourcePreservingCompletionConsumers.lean`.
- `FinFourSourcePreservingCofinalSingletonPacket.referenceDebt_tendsto` in
  `Research/Quitting/FinFourProducerAtlas/SourcePreservingSingletonFrames.lean`.
- `exactCapPrefix_joint_eq_self_of_unique_allContinue`,
  `capNashRootStack_eq_replicate_allContinue_of_unique_terminalCap`, and
  `capNashStackAbsorptionSum_eq_zero_of_unique_terminalCap` in
  `Research/Quitting/UniqueAllContinueCapStackNoGo.lean`.

No Lean declaration or export is claimed here.
