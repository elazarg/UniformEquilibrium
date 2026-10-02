# Independent review of AGKRS diagonal exact-prefix port closure

Reviewer: `CODEX_EULER`

Note reviewed:
[`CODEX_MINER__AGKRS_DIAGONAL_EXACT_PREFIX_PORT_CLOSURE.md`](../notes/CODEX_MINER__AGKRS_DIAGONAL_EXACT_PREFIX_PORT_CLOSURE.md)

Verdict: **PASS, no mathematical repair.**  The proposed port-limit
composition is correct, and the note's stronger time-zero theorem is also
correct: every reached positive-joint punishment endpoint already supplies a
diagonal point of the literal terminal-semantic carrier and therefore a
uniform-equilibrium payoff.  The summable port is unnecessary for that
conclusion.

I checked the result against the current declarations and also typechecked the
two-line endpoint composition, the diagonal-orbit induction, and the port-limit
carrier proof in a scratch Lean file importing
`PositiveJointSummablePortPhantomReduction.lean`.  No repository theorem was
assumed beyond the declarations listed below.

## 1. Time-zero diagonal closure

For

```text
endpoint : QuittingPositiveJointPrefixReachPunishmentEndpoint reward,
```

the field `endpoint.endpoint_mem` gives

```text
endpoint.endpoint ∈ quittingTerminalSemanticCarrier reward.
```

The checked theorem `endpoint.payoff_eq_envelope who` gives equality of the
two coordinates for every player.  Pair and function extensionality therefore
give

```text
(endpoint.endpoint.1, endpoint.endpoint.1) = endpoint.endpoint.
```

Rewriting `endpoint.endpoint_mem` proves diagonal carrier membership.  The
endpoint field `punished : iota` supplies the `Nonempty iota` instance required
by `isUniformEquilibriumPayoff_of_diagonal_mem_terminalSemanticCarrier`.
Consequently

```text
(quittingGame reward).IsUniformEquilibriumPayoff
  none endpoint.endpoint.1.
```

The exact proof term typechecks at the current head:

```text
theorem QuittingPositiveJointPrefixReachPunishmentEndpoint
    .isUniformEquilibriumPayoff
    (endpoint : QuittingPositiveJointPrefixReachPunishmentEndpoint reward) :
    (quittingGame reward).IsUniformEquilibriumPayoff none
      endpoint.endpoint.1 := by
  letI : Nonempty iota := ⟨endpoint.punished⟩
  apply isUniformEquilibriumPayoff_of_diagonal_mem_terminalSemanticCarrier
  have hdiag :
      (endpoint.endpoint.1, endpoint.endpoint.1) = endpoint.endpoint := by
    apply Prod.ext
    · rfl
    · funext who
      exact endpoint.payoff_eq_envelope who
  rw [hdiag]
  exact endpoint.endpoint_mem
```

Thus `source.exists_punishmentEndpoint` immediately implies that every
`QuittingPositiveJointPrefixReachSource reward` has some uniform-equilibrium
payoff.  Neither a no-sure-exit hypothesis nor a summability hypothesis enters
this composition.

## 2. Exact-prefix diagonality

The note's induction is exact.  At time zero the semantic orbit is the
diagonal endpoint.  At a successor time, its selected root satisfies

```text
IsεQuittingRootNash reward pair_t.1 0 root_t
```

by `quittingTerminalSemanticSelectedExactRoot_isZeroNash`.  After rewriting
the inductive diagonal equality, the checked theorem
`quittingTerminalSemanticPrefix_diagonal_eq_of_isZeroNash` makes the entire
successor semantic pair diagonal.  Its common coordinate is definitionally
`endpoint.exactPrefixOrbit.value (t+1)`.

This is stronger than saying semantic debt merely stays nonincreasing.  Debt
is exactly zero at every prefix because the complete semantic pair, not just
its prescribed projection, remains diagonal.  Exact root Nash is essential;
the same statement is false for a generic approximate prefix.

Carrier provenance is also exact:
`quittingTerminalSemanticExactPrefixOrbit_mem_carrier` applies at every time
from `endpoint.endpoint_mem`.  Hence

```text
(endpoint.exactPrefixOrbit.value t,
 endpoint.exactPrefixOrbit.value t)
  ∈ quittingTerminalSemanticCarrier reward
```

for every `t`.

## 3. Summable-port limit

For a port on `endpoint.exactPrefixOrbit`, `port.value_tendsto` gives
coordinatewise convergence of the prescribed orbit value to `port.limit`.
Finiteness of the player type and `tendsto_pi_nhds` give convergence in the
payoff space.  Taking the product with itself and using the previous section
gives a carrier-valued sequence converging to

```text
(port.limit, port.limit).
```

The terminal-semantic carrier is closed because
`quittingTerminalSemanticCarrier_isCompact reward` is compact in the
finite-dimensional Hausdorff pair space.  Its limit is therefore in the
carrier, and the checked diagonal-carrier consumer yields the uniform payoff
`port.limit`.

There is no mismatch between `exactPrefixOrbit.value` and the first coordinate
of the semantic orbit: this equality is definitional in
`QuittingPositiveJointPrefixReachPunishmentEndpoint.exactPrefixOrbit`.  The
missing second-coordinate convergence is supplied by exact diagonality, not
by `SummableChargeAllContinuePort.limit_mem`, which indeed refers only to the
punishment-floor forward carrier.

Only `port.value_tendsto` is needed once the port exists.  The other port
fields produce and analyze that convergence but are not logically needed for
this carrier-closure step.

## 4. Strategy and probability scope

`quittingTerminalSemanticCarrier` is the closure of semantic pairs of actual
behavior profiles.  Its envelope coordinate is the supremum over unrestricted
unilateral behavioral strategies.  The checked diagonal-carrier consumer
selects literal profiles whose complete semantic pairs converge to the
diagonal, converts vanishing semantic debt into unrestricted terminal Nash
error, and then invokes the checked terminal-to-uniform-payoff theorem.

Accordingly, the conclusion is not limited to stationary, pure-time, finite-
memory, or root-sequence deviations.  It also does not claim that the carrier
point is attained by one profile; closure membership is the correct input to
the existing consumer.

## 5. Frontier and novelty verdict

This closes the positive-joint source class for the finite-quitting
**uniform-payoff conjecture**.  In particular, the zero-charge phantom and the
positive displaced summable port are not surviving uniform-payoff
obstructions once their reached endpoint provenance is retained.  The current
question text saying that diagonal terminal-semantic carrier membership of the
port limit is unavailable is stale.

This does **not** prove that the endpoint or port realizes literal AGKRS branch
S.1, S.2, or S.3.  Hence it does not discharge the positive-joint consumer
required by the paper-facing classification theorem
`theorem3_4_of_prioritizedAndSummablePortClosures`, whose codomain is the
three-way AGKRS classification rather than arbitrary uniform-payoff existence.
The distinction in the reviewed note is necessary and correct.

The composition is genuinely absent from the declarations found by narrow
search.  It is a strong formalization and export candidate: the shortest
useful theorem is the time-zero endpoint consumer, with the orbit and port
lemmas retained as an audit that explains precisely why the earlier
forward-carrier nonclaim was too weak.  A packet should avoid claiming full
AGKRS classification or full conjecture closure unless the remaining source
classes are separately consumed.

## Checked declaration set

- `QuittingPositiveJointPrefixReachPunishmentEndpoint.endpoint_mem`,
  `.debt_eq_zero`, `.payoff_eq_envelope`, and
  `QuittingPositiveJointPrefixReachSource.exists_punishmentEndpoint` in
  `UniformEquilibrium/Quitting/Classification/Existence/PositiveJointPrefixReachEndpoint.lean`;
- `quittingTerminalSemanticExactPrefixOrbit`, its successor and carrier
  theorems, and
  `quittingTerminalSemanticSelectedExactRoot_isZeroNash` in
  `UniformEquilibrium/Quitting/Root/SemanticExactPrefixOrbit.lean`;
- `quittingTerminalSemanticPrefix_diagonal_eq_of_isZeroNash` and
  `quittingTerminalSemanticCarrier_isCompact` in
  `UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`;
- `QuittingPositiveJointPrefixReachPunishmentEndpoint.exactPrefixOrbit` in
  `UniformEquilibrium/Quitting/Classification/Existence/PositiveJointEndpointSequentialReduction.lean`;
- `SummableChargeAllContinuePort.value_tendsto` in
  `UniformEquilibrium/Quitting/Bellman/Finite/PunishmentFloorInfiniteOrbitChargeDichotomy.lean`; and
- `isUniformEquilibriumPayoff_of_diagonal_mem_terminalSemanticCarrier` in
  `UniformEquilibrium/Quitting/Classification/Existence/PositiveJointSummablePortPhantomReduction.lean`.
