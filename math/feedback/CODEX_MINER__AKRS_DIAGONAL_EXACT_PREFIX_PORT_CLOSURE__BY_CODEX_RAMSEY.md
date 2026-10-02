# Independent falsification of the diagonal exact-prefix port closure

Reviewer: `CODEX_RAMSEY`

Source reviewed:
[`notes/CODEX_MINER__AGKRS_DIAGONAL_EXACT_PREFIX_PORT_CLOSURE.md`](../notes/CODEX_MINER__AGKRS_DIAGONAL_EXACT_PREFIX_PORT_CLOSURE.md)

Verdict: **PASS as mathematics; no repair.  Keep internal / do not export as a
new result because the zero-step conclusion is already a checked theorem in
the current source tree.**

I attempted to falsify both the zero-step argument and the longer prefix-limit
argument.  Neither has a mathematical gap.  The decisive observation is even
stronger than the port statement: the reached endpoint is already an
all-coordinate diagonal point of the literal terminal-semantic carrier.

## Claim checked

For

```text
endpoint : QuittingPositiveJointPrefixReachPunishmentEndpoint reward
```

the note claims

```text
(endpoint.endpoint.1, endpoint.endpoint.1) ∈
  quittingTerminalSemanticCarrier reward,
```

and hence a uniform-equilibrium payoff.  It also claims that the canonical
exact semantic-prefix orbit remains diagonal and that any supplied
`SummableChargeAllContinuePort` limit is again diagonal in the carrier.

## 1. Endpoint diagonality is genuinely all-coordinate

The field `endpoint.debt_nonpos` is quantified over every `who`.  The theorem
`QuittingPositiveJointPrefixReachPunishmentEndpoint.debt_eq_zero` combines it
with
`quittingTerminalSemanticDebt_nonneg_of_mem_carrier` for every coordinate.
Then `payoff_eq_envelope who` proves

```text
endpoint.endpoint.1 who = endpoint.endpoint.2 who
```

for every player, not only for `endpoint.punished`.  Function extensionality
therefore gives the full pair equality

```text
endpoint.endpoint =
  (endpoint.endpoint.1, endpoint.endpoint.1).
```

The fixed punished label is used only to obtain `Nonempty iota` and to retain
the punishment-value equality; it is not the only zero-debt coordinate.

## 2. Carrier membership and the diagonal consumer

`endpoint.endpoint_mem` is membership in
`quittingTerminalSemanticCarrier reward`, which is literally the closure of
the range of `quittingTerminalSemanticPair reward` on executable behavioral
profiles.  Its second coordinate is
`quittingContinuationBestResponseValue`, the supremum over unrestricted
unilateral behavioral deviations.  It is not merely a Bellman annotation or
a punishment-floor point.

The checked declaration

```text
isUniformEquilibriumPayoff_of_diagonal_mem_terminalSemanticCarrier
```

in
`UniformEquilibrium/Quitting/Classification/Existence/PositiveJointSummablePortPhantomReduction.lean`
has exactly the required input and proves

```text
(quittingGame reward).IsUniformEquilibriumPayoff none target.
```

It is a theorem with an explicit proof, not an axiom.  A direct axiom query
reports only the project-allowed library axioms `propext`,
`Classical.choice`, and `Quot.sound`.

Moreover, the current source tree already contains and type-checks the exact
zero-step composition

```text
QuittingPositiveJointPrefixReachPunishmentEndpoint.isUniformEquilibriumPayoff
```

in
`UniformEquilibrium/Quitting/Classification/Existence/PositiveJointEndpointUniformPayoff.lean`.
That source file is currently untracked at the reviewed working-tree state,
so integration status should not be confused with mathematical status; the
declaration itself type-checks under its stated imports.

There is no attainment subtlety here.  A diagonal carrier point need not be
realized by one profile.  The checked consumer extracts executable profile
sequences converging in both semantic coordinates, obtains vanishing full
behavioral exploitability, and invokes the terminal-Nash convergence
consumer.  Closure membership is exactly what it needs.

## 3. Exact-prefix induction

The longer source audit also passes.

- At time zero the semantic pair is `endpoint.endpoint`, already diagonal.
- At time `t+1`,
  `quittingTerminalSemanticExactPrefixOrbit_succ` prefixes the selected root
  to the entire current semantic pair.
- `quittingTerminalSemanticSelectedExactRoot_isZeroNash` is exact Nash at the
  current prescribed coordinate.
- After rewriting the induction hypothesis, the input pair is literally
  `(tail,tail)`, so
  `quittingTerminalSemanticPrefix_diagonal_eq_of_isZeroNash` applies and
  returns equality of both successor coordinates.
- `quittingTerminalSemanticExactPrefixOrbit_mem_carrier` preserves literal
  carrier membership at every finite time.
- The definition of `endpoint.exactPrefixOrbit.value t` is precisely the
  first coordinate of this semantic pair.

Thus the proof does not conflate the payoff-only punishment-floor orbit with
the semantic-pair orbit stored behind it.  Exactness is essential: the same
argument is unavailable for approximate root Nash points.

## 4. Limit passage

For a supplied port, `port.value_tendsto who` is coordinatewise convergence
for every player.  Since the player type is finite, `tendsto_pi_nhds` gives
convergence in the payoff function space.  Pairing the sequence with itself
gives convergence to `(port.limit,port.limit)`.

Every diagonal sequence term is in the terminal-semantic carrier by the
preceding induction.  The carrier is compact, hence closed, by
`quittingTerminalSemanticCarrier_isCompact`; therefore the diagonal limit is
also in it.  No use of `port.limit_mem` as a mere punishment-floor carrier
membership is being smuggled into this step.

There is no zero-debt discontinuity: diagonality holds term by term, and both
coordinates converge to the same limit.  In fact the port's summability,
quit-limit, and self-loop fields are irrelevant once `value_tendsto` is
given.

## 5. Boundary and scope checks

- A one-player endpoint causes no empty-player problem because the endpoint
  itself carries `punished : iota`.
- At time zero the theorem already closes, ruling out an off-by-one prefix
  orientation issue.
- For a generic payoff-only floor orbit, coordinatewise payoff convergence
  alone would not provide a semantic diagonal carrier sequence.  The result
  is specific to this carrier-valued exact-prefix construction.
- The conclusion is existence of a finite-quitting **uniform-equilibrium
  payoff**.  It does not manufacture AGKRS branch S.1, S.2, or S.3, and it
  does not show that the diagonal carrier point is attained by one behavioral
  profile.

## Recommendation

The mathematics is correct and the note is a useful source audit.  It should
not be promoted as a new export: the strongest conclusion is already the
checked `PositiveJointEndpointUniformPayoff` theorem, while the prefix-port
argument is strictly downstream and unnecessary for uniform-payoff closure.
If retained internally, the source audit should mention this exact
subsumption rather than saying only that a narrow search found no composition.
