# AGKRS positive-joint endpoints and their summable ports are diagonal terminal-semantic limits

Author: `CODEX_MINER`

Status: **independently reviewed/PASS; subsequently formalized and
type-checked in the current working tree; no export remains.**
Independent review:
[`CODEX_RAMSEY`](../feedback/CODEX_MINER__AGKRS_DIAGONAL_EXACT_PREFIX_PORT_CLOSURE__BY_CODEX_RAMSEY.md).
The proposed summable-port implication is valid.  In fact the reached
punishment endpoint already gives a uniform-equilibrium payoff, before the
canonical orbit or its summable port is used.  The port-limit proof remains
useful as a source audit: every selected exact semantic prefix preserves zero
debt, so the limit carries both semantic coordinates and is not merely a
Bellman annotation.

This explicitly closes the positive-joint endpoint through a named diagonal
target for the finite-quitting **uniform-payoff conjecture**.  The bare
existence consequence is not new: the already checked composition of
`source.punishment_approximateEquilibriumExistence` with
`quittingGame_exists_uniformEquilibriumPayoff_of_approximateEquilibriumExistence`
also gives some uniform payoff directly.  During this audit the exact
zero-step endpoint theorem was integrated and type-checked in
`PositiveJointEndpointUniformPayoff.lean`; the reviewed orbit and port-limit
audit was subsequently implemented and type-checked in
`PositiveJointExactPrefixOrbitDiagonal.lean`.  Thus this note is not a new
export candidate.  It does not by itself prove one of
the stronger AGKRS classification branches S.1/S.2/S.3; an arbitrary uniform
payoff need not be stationary, instant-punished, or sequentially perfect in
those prescribed forms.

Initial audit performed at repository head `abb4a08`; source status rechecked
at head `26f2261` against the current changed tree.

## 1. Exact question

Let `reward` be a finite quitting reward table and let

```text
endpoint : QuittingPositiveJointPrefixReachPunishmentEndpoint reward.
```

Write

```text
pair_t = quittingTerminalSemanticExactPrefixOrbit
  reward endpoint.endpoint t,
O      = endpoint.exactPrefixOrbit.
```

Suppose

```text
port : O.SummableChargeAllContinuePort
```

has limit `L`.  Is

```text
(L,L) ∈ quittingTerminalSemanticCarrier reward
```

forced by the checked source, so that the existing diagonal-carrier consumer
gives a uniform-equilibrium payoff?

Answer: **yes**.  There is no mismatch between `O.value t` and the semantic
orbit's prescribed coordinate, and exact prefixing supplies the missing
envelope coordinate.

## 2. Stronger zero-step theorem

### Theorem A

For every reached positive-joint punishment endpoint,

\[
 (\texttt{endpoint.endpoint.1},
  \texttt{endpoint.endpoint.1})
 \in \texttt{quittingTerminalSemanticCarrier reward}.
\]

Consequently `endpoint.endpoint.1` is a uniform-equilibrium payoff.

### Proof

The endpoint field `endpoint_mem` gives

```text
endpoint.endpoint ∈ quittingTerminalSemanticCarrier reward.
```

For every player `who`, the checked theorem
`endpoint.payoff_eq_envelope who` says

```text
endpoint.endpoint.1 who = endpoint.endpoint.2 who.
```

Function extensionality and pair extensionality therefore give

```text
endpoint.endpoint =
  (endpoint.endpoint.1, endpoint.endpoint.1).
```

Rewriting `endpoint_mem` proves the displayed diagonal carrier membership.
The endpoint contains `punished : iota`, hence the player type is inhabited.
Apply

```text
isUniformEquilibriumPayoff_of_diagonal_mem_terminalSemanticCarrier
```

from `PositiveJointSummablePortPhantomReduction.lean` with target
`endpoint.endpoint.1`.  This proves Theorem A.

No port, summability, no-sure-exit hypothesis, or branch-priority hypothesis
is used.

## 3. Exact prefixes preserve diagonality

### Theorem B

For every natural time `t`,

```text
pair_t = (pair_t.1, pair_t.1).
```

In particular

```text
(O.value t, O.value t) ∈ quittingTerminalSemanticCarrier reward.
```

### Proof

Induct on `t`.

At time zero, `pair_0=endpoint.endpoint`; Theorem A's diagonal equality is the
base case.

For the successor step, assume

```text
pair_t = (pair_t.1, pair_t.1).
```

By the defining recurrence
`quittingTerminalSemanticExactPrefixOrbit_succ`,

```text
pair_(t+1) = quittingTerminalSemanticPrefix reward root_t pair_t,
```

where

```text
root_t = quittingTerminalSemanticSelectedExactRoot reward pair_t.
```

The checked selection theorem
`quittingTerminalSemanticSelectedExactRoot_isZeroNash` gives

```text
IsεQuittingRootNash reward pair_t.1 0 root_t.
```

After rewriting the induction hypothesis, apply

```text
quittingTerminalSemanticPrefix_diagonal_eq_of_isZeroNash.
```

It yields

```text
pair_(t+1) =
  (quittingRootSuccessorPayoff reward pair_t.1 root_t,
   quittingRootSuccessorPayoff reward pair_t.1 root_t).
```

The first displayed coordinate is definitionally `pair_(t+1).1`, proving the
successor diagonal equality.

The checked theorem
`quittingTerminalSemanticExactPrefixOrbit_mem_carrier` gives
`pair_t` carrier membership at every time.  By the definition of
`endpoint.exactPrefixOrbit`,

```text
O.value t = pair_t.1.
```

Rewriting by the diagonal equality proves the last assertion.

This is the exact step missed by treating `O.value` as a standalone Bellman
orbit: its construction retains a carrier-valued semantic pair behind every
payoff annotation, and exact Nash prefixing keeps that pair diagonal.

## 4. Port limit is diagonal in the carrier

### Theorem C

For every summable port `port` on `endpoint.exactPrefixOrbit`,

```text
(port.limit, port.limit) ∈
  quittingTerminalSemanticCarrier reward.
```

Hence `port.limit` is a uniform-equilibrium payoff.

### Proof

The field

```text
port.value_tendsto who :
  Tendsto (fun t => O.value t who) atTop (nhds (port.limit who))
```

holds for every player.  Since the player type is finite, `tendsto_pi_nhds`
combines these coordinate statements into

```text
Tendsto O.value atTop (nhds port.limit).
```

Taking the product of this convergence with itself gives

```text
Tendsto (fun t => (O.value t, O.value t)) atTop
  (nhds (port.limit, port.limit)).
```

Every term of that sequence belongs to the terminal-semantic carrier by
Theorem B.  The carrier is closed because
`quittingTerminalSemanticCarrier_isCompact reward` is compact in the
finite-dimensional Hausdorff payoff-pair space.  Therefore its limit
`(port.limit,port.limit)` also belongs to the carrier.

Apply
`isUniformEquilibriumPayoff_of_diagonal_mem_terminalSemanticCarrier` to obtain
the uniform payoff `port.limit`.

The summability fields `absorption_summable`, `quit_tendsto_zero`,
`limit_mem`, and `selfLoop` are not needed after `value_tendsto` is supplied.
They are used to produce that port and its convergence, but the diagonal
carrier closure itself uses only the literal convergence field.

## 5. Source-level consequences

Two immediate compositions follow.

1. Every `QuittingPositiveJointPrefixReachSource reward` has a reached
   endpoint by `exists_punishmentEndpoint`; Theorem A gives a uniform-
   equilibrium payoff.
2. Every
   `QuittingPositiveJointPrefixReachNoSureExitResidual reward` therefore also
   gives a uniform-equilibrium payoff.  Alternatively, its checked
   `wellSupported_or_summableExactPrefixPort` split gives S.3 on the first arm
   and Theorem C's uniform payoff on the second.

For the finite-quitting conjecture, there is no surviving positive-joint
summable-port obstruction.  This conclusion was already available at the
existence level from the reached suffixes' approximate equilibria; the present
argument identifies both the endpoint target and the port-limit target.
The zero-charge phantom and ballistic displaced port remain meaningful only
for the stronger attempt to force literal AGKRS branches S.1/S.2/S.3, or as
structural Bellman statements; neither is an obstruction to uniform-payoff
existence.

## 6. Source and novelty audit

Exact declarations inspected:

- `QuittingPositiveJointPrefixReachPunishmentEndpoint.endpoint_mem`,
  `debt_eq_zero`, and `payoff_eq_envelope` in
  `PositiveJointPrefixReachEndpoint.lean`;
- `quittingTerminalSemanticExactPrefixOrbit`,
  `quittingTerminalSemanticExactPrefixOrbit_succ`,
  `quittingTerminalSemanticExactPrefixOrbit_mem_carrier`, and
  `quittingTerminalSemanticSelectedExactRoot_isZeroNash` in
  `Root/SemanticExactPrefixOrbit.lean`;
- `quittingTerminalSemanticPrefix_diagonal_eq_of_isZeroNash` and
  `quittingTerminalSemanticCarrier_isCompact` in
  `Root/TerminalSemanticPair.lean`;
- `QuittingPositiveJointPrefixReachPunishmentEndpoint.exactPrefixOrbit` and
  `wellSupported_or_summableExactPrefixPort` in
  `PositiveJointEndpointSequentialReduction.lean`;
- `SummableChargeAllContinuePort.value_tendsto` in
  `PunishmentFloorInfiniteOrbitChargeDichotomy.lean`; and
- `isUniformEquilibriumPayoff_of_diagonal_mem_terminalSemanticCarrier` in
  `PositiveJointSummablePortPhantomReduction.lean`; and
- `QuittingPositiveJointPrefixReachPunishmentEndpoint.`
  `isUniformEquilibriumPayoff`,
  `QuittingPositiveJointPrefixReachSource.`
  `exists_uniformEquilibriumPayoff`, and
  `QuittingPositiveJointPrefixReachNoSureExitResidual.`
  `exists_uniformEquilibriumPayoff` in the concurrently integrated and
  type-checked `PositiveJointEndpointUniformPayoff.lean`; and
- `exactPrefixPair_eq_diagonal`, `exactPrefixValue_mem_diagonal`,
  `SummableChargeAllContinuePort.limit_mem_diagonal_of_endpoint`, and
  `limit_isUniformEquilibriumPayoff_of_endpoint` in the subsequently
  implemented and type-checked `PositiveJointExactPrefixOrbitDiagonal.lean`.

The current checked zero-step theorem is exactly Theorem A.  Therefore the
endpoint and source-level uniform-payoff conclusions are already formalized;
this note does not claim novelty for them.  The reviewed Theorems B and C are
also now formalized in the separate exact-prefix module.  A documentation
nonclaim that diagonal carrier membership is not established for the port
limit is therefore stale: it overlooks the semantic pair stored behind
`exactPrefixOrbit.value` and is contradicted by the current checked
declaration `limit_mem_diagonal_of_endpoint`.

The source-level existence consequence is nevertheless duplicated by the
checked pair

```text
QuittingPositiveJointPrefixReachSource.
  punishment_approximateEquilibriumExistence

quittingGame_exists_uniformEquilibriumPayoff_of_
  approximateEquilibriumExistence.
```

Accordingly the port-limit result should be integrated as a semantic
identity/target-selection correction, not advertised as the first proof that
the source has some uniform payoff.

This observation does not depend on the new ballistic dispatch and does not
duplicate its returned-charge S.3 theorem or displacement estimate.

## 7. Probability and strategy audit

Carrier membership is the closure of semantic pairs of actual behavioral
profiles, with the second coordinate defined by suprema over unrestricted
unilateral behavioral deviations.  Prefix preservation is the checked
literal root/profile-splicing map.  The diagonal-carrier consumer selects
actual terminal profiles whose full semantic pairs converge to the diagonal,
and converts their vanishing unrestricted debt into terminal Nash profiles.

No stationary-deviation restriction, finite-memory controller, public
randomization, or identification of a formal all-Continue payoff with the
all-Never terminal payoff is made.  The conclusion is a uniform-equilibrium
payoff, not realization of the carrier point by one literal profile.

## 8. Boundary tests and nonclaims

1. The proof works at time zero.  This confirms that port convergence is not
   secretly needed and prevents an off-by-one orientation error in the
   semantic-prefix recurrence.
2. Exactness is essential for Theorem B.  An approximate root can prefix a
   diagonal pair to a pair with positive debt; the checked diagonal-prefix
   lemma explicitly assumes zero Nash error.
3. A generic punishment-floor orbit does not carry semantic second
   coordinates and need not be diagonal.  The theorem applies specifically to
   `endpoint.exactPrefixOrbit`, whose values are projections of the checked
   semantic orbit.
4. The result does not prove S.1, S.2, or S.3 in the summable arm.  Therefore
   it does not complete AGKRS Theorem 3.4 as a classification theorem.
5. It does not say `(L,L)` is attained by a single behavior profile.  Closure
   membership plus the checked diagonal consumer is sufficient for a uniform
   payoff.

## 9. Integration status

Theorem A and its source/residual corollaries are already implemented and
type-checked in `PositiveJointEndpointUniformPayoff.lean`; do not reprove
them.  The orbit identity and port-limit membership are also implemented and
type-checked in `PositiveJointExactPrefixOrbitDiagonal.lean` under:

```text
theorem QuittingPositiveJointPrefixReachPunishmentEndpoint.
    exactPrefixOrbit_pair_eq_diagonal (endpoint : ...) (t : Nat) :
    quittingTerminalSemanticExactPrefixOrbit reward endpoint.endpoint t =
      (endpoint.exactPrefixOrbit.value t,
       endpoint.exactPrefixOrbit.value t)

theorem SummableChargeAllContinuePort.diagonal_mem_terminalSemanticCarrier
    (port : endpoint.exactPrefixOrbit.SummableChargeAllContinuePort) :
    (port.limit, port.limit) ∈ quittingTerminalSemanticCarrier reward
```

No mathematical or Lean handoff remains.  At the initial recheck boundary
both new files were untracked and imported nowhere; during the subsequent
integration pass `Existence/All.lean` was updated to import them.  Landing the
staged files remains ordinary integration work.  Do not add a new residual
structure or reprove the diagonal-carrier consumer.

## 10. Independent review

`CODEX_RAMSEY` independently checked the all-coordinate endpoint diagonality,
literal carrier membership, unrestricted diagonal consumer, exact-prefix
induction, and finite-coordinate limit passage and returned **PASS**.  The
review also identified the concurrently integrated checked zero-step theorem,
which is why this note is retained as an internal source audit rather than
promoted for export.  No mathematical objection remains.
