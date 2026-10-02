# Paid cap-lifted summable port

Author: external `ChatGPT` contribution supplied by the user

Review:
[`CODEX_ROOT`](../feedback/CHATGPT_EXTERNAL__PAID_CAP_LIFTED_SUMMABLE_PORT__BY_CODEX_ROOT.md)

## Current status

The construction is valid after two scope clarifications:

1. every finite nested profile literally retains the original paid receiving
   profile as a suffix with a uniform positive reach floor; the limiting
   semantic port retains the resulting semantic/law contribution, but is not
   itself claimed to contain a suffix after infinitely many dates;
2. every finite nested profile has a shifted paid first-disagreement row of
   fixed positive gain, while the original source and receiving
   near-optimality fields remain immutable provenance at the original
   curvature carrier and are not asserted for the shifted witnesses.

Subject to those formulations, the cap lift removes the prescribed-payoff
floor assumption from the marked exact-port construction.

## Exact setting

Let `I` be finite and nonempty, let `r` be a finite quitting reward table, and
let `z*` be a global minimizer of total terminal semantic debt with

```text
D* = D(z*) > 0.
```

Let `x0` be any attained behavioral profile carrying a
`QuittingPaidFirstDisagreementRow r x0 o g` with `g>0`.  In the intended
adapter, `x0` is the full-replacement receiving profile in a
`QuittingStoppingLawCurvaturePaidWitness`.

Define recursively

```text
x_(n+1) = q_n ▷ x_n,
q_n = quittingMaximalCapPrefixRoot r x_n,
(u_n,b_n) = Sem(x_n),
D_n = sum_i (b_n(i)-u_n(i)),
a_n = Abs(q_n),
c_n = 1-a_n.
```

The maximality of `q_n` is not mathematically required; it provides a
canonical coherent choice.

## Cap lift

For every actual profile `x` and player `i`, the behavioral punishment value
is at most the best-response envelope `B_i(x)`.  Hence every `b_n` dominates
the punishment floor.

Literal semantic prefixing and exact Nash of `q_n` against `b_n` give

```text
u_(n+1) = F(q_n,u_n),
b_(n+1) = F(q_n,b_n).
```

Therefore `((b_n,q_n))_n` is an exact punishment-floor Nash--Bellman orbit,
even when `u_0` itself violates the floor.  Simultaneously, the same roots
generate the honest prescribed-payoff chronology `u_n` on the literal
profiles `x_n`.

## Debt budget and reach

Exact cap-Nash prefixing scales every semantic debt coordinate by joint
Continue mass:

```text
d_(n+1,i) = c_n d_(n,i),
D_(n+1) = c_n D_n.
```

Since every `Sem(x_n)` belongs to the actual terminal semantic carrier,
global minimality gives `D_n>=D*`.  Consequently

```text
D_n-D_(n+1) = a_n D_n >= a_n D*,
D* sum_(n<N) a_n <= D_0-D_N <= D_0-D*.
```

Thus

```text
sum_n a_n <= (D_0-D*)/D* < infinity.
```

If

```text
S_n = product_(k<n)c_k,
```

then iteration gives `D_n=S_n D_0`.  Therefore

```text
S_n >= sigma := D*/D_0 > 0                         for every n.
```

This is the literal probability, under `x_n`, that all newly prefixed roots
Continue and the unchanged receiving profile `x0` is reached.

## Shifted paid row

For a pure time `t : Option Nat`, define

```text
shift_n(none)=none,
shift_n(some t)=some(n+t).
```

Let

```text
Lambda_(n,o) = product_(k<n) OppCont(q_k,o).
```

Both shifted deviations Continue through every outer root.  Payoffs on outer
opponent absorption are identical and cancel.  Induction over the finite
outer word gives

```text
Payoff(x_n,o,shift_n(t_recv))-Payoff(x_n,o,shift_n(t_src))
  = Lambda_(n,o)
      [Payoff(x0,o,t_recv)-Payoff(x0,o,t_src)].
```

Since `OppCont(q_k,o)>=c_k`, one has

```text
Lambda_(n,o)>=S_n>=sigma.
```

The original row therefore yields a positive shifted edge of gain at least
`sigma*g`.  Applying the exact first-disagreement decoder produces a
`QuittingPaidFirstDisagreementRow r x_n o (sigma*g)` whose witnesses and
first-disagreement date are the corresponding shifts.  Its live mass is the
original row's live mass multiplied by `Lambda_(n,o)`.

The original `QuittingStoppingLawCurvaturePaidWitness`, including its two
near-optimality fields, remains stored as immutable provenance.  No
near-optimality assertion is made for the shifted witnesses at `x_n`.

## Limit port

Summability implies `a_n -> 0`, hence `q_n -> all-Continue`.  The exact orbit
increment estimate makes `b_n` Cauchy.  Its limit `b∞` remains above the
punishment floor, and closedness of exact Nash gives all Continue exact Nash
against `b∞`.  Thus `(b∞,all-Continue)` is an exact floor-safe Bellman
self-loop.

The prescribed coordinates `u_n` and the semantic debts converge as well, so
`Sem(x_n)` converges in the closed terminal semantic carrier to an
all-Continue fixed semantic port.  The uniform finite-depth reach estimate
passes to terminal-law/semantic contributions.  It is not a claim that one
behavioral profile executes `x0` after infinitely many prefixed dates.

## Source correspondence inspected

- `quittingMaximalCapPrefixRoot`,
  `quittingMaximalCapPrefixProfile`,
  `quittingMaximalCapPrefixProfile_debt_succ`,
  `minimum_mul_sum_maximalCapPrefix_absorption_le_debtDrop`,
  `summable_maximalCapPrefix_absorption`,
  `quittingTerminalSemanticPrefix_envelope_eq_rootSuccessorPayoff_of_capNash`,
  and `quittingMaximalCapPrefixPunishmentFloorPrefix` in
  `Research/Quitting/CausalTailEscapeMaxAbsorptionDispatch.lean`;
- `quittingTerminalSemanticDebt_prefix_eq_continueMass_mul_of_capNash` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalCapNashEndpointTransport.lean`;
- `quittingTerminalSemanticPair_rootThenContinuation` in
  `UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`;
- `QuittingStoppingLawCurvaturePaidWitness` in
  `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/NormalizedCurvatureStrategicDispatch.lean`;
- `exists_quittingPaidFirstDisagreementRow_of_pureTimePayoff_sub` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPaidFirstDisagreement.lean`;
- `QuittingPunishmentFloorInfiniteOrbit.SummableChargeAllContinuePort` and its
  constructor in
  `UniformEquilibrium/Quitting/Bellman/Finite/PunishmentFloorInfiniteOrbitChargeDichotomy.lean`.

## Remaining item

The cap lift produces the unconditional source-matched summable marked port
from the actual paid receiving profile under a positive global debt minimum.
It does not consume that port.  The remaining paid-route problem is the
source-matched restart/debt-descent step which spends the persistent paid mark
or the fixed signed terminal budget and thereby contradicts summability or
positive minimality.

