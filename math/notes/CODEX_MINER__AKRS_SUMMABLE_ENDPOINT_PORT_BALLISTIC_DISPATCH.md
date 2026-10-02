# AGKRS summable endpoint ports: returned S.3 or ballistic displacement

Author: `CODEX_MINER`

Status: **reviewed/PASS; narrow export approved.**  Independent review:
[`CODEX_EULER`](../feedback/CODEX_MINER__AGKRS_SUMMABLE_ENDPOINT_PORT_BALLISTIC_DISPATCH__BY_CODEX_EULER.md).
Post-review formalization correction: the signed-mass denominator uses the
canonical `quittingRewardBound reward`, not the raw maximum absolute terminal
coordinate.  Generic punishment-floor orbit annotations are certified only
against the canonical box.  The statement and proof below now use that bound
throughout; no branch conclusion changes.
The current checked positive-joint
endpoint reduction leaves a no-sure-exit endpoint with a summable canonical
exact-prefix port.  A positive-charge port which returns to its starting
endpoint gives literal AGKRS branch S.3.  More generally, failure of S.3 gives
one positive scale at which every charged finite segment of the port is
separated from return by an explicit cumulative-charge modulus.  At the
infinite port this yields either the zero-charge all-Continue phantom or a
quantitatively nonzero displacement carrying the checked fixed signed
terminal label.

This is a genuine consumer of the returned summable subarm into literal S.3,
but not a classification closure of the displaced or zero-charge phantom
arms.  No S.1/S.2/S.3 theorem is claimed for those two survivors.  They are
not obstructions to the uniform-payoff conjecture: the subsequently checked
`PositiveJointEndpointUniformPayoff.lean` consumes every reached endpoint
directly through its diagonal terminal-semantic carrier point.

Audit performed at repository head `fed7258`, including the current changed
sources `PositiveJointEndpointSequentialReduction.lean`,
`PositiveJointSummablePortPhantomReduction.lean`, and the paper-facing
Literature composition.  The two new source files compile at this working
tree; they are not yet part of the displayed git commit.

## 1. Exact maintained input

Let

```text
residual : QuittingPositiveJointPrefixReachNoSureExitResidual reward.
```

The new checked theorem

```text
residual.wellSupported_or_summableExactPrefixPort
```

in
`UniformEquilibrium/Quitting/Classification/Existence/`
`PositiveJointEndpointSequentialReduction.lean` already returns S.3 unless
there are

```text
endpoint : QuittingPositiveJointPrefixReachPunishmentEndpoint reward,
hnoSure  : not endpoint.HasSureExitNashPrefix,
port     : endpoint.exactPrefixOrbit.SummableChargeAllContinuePort.
```

Write

```text
O       = endpoint.exactPrefixOrbit,
v_t     = O.value t,
q_t     = O.roots t,
a_t     = quittingRootAbsorptionMass q_t,
E       = v_0 = endpoint.endpoint.1,
L       = port.limit,
A       = sum' t, a_t.
```

The endpoint is diagonal and zero-debt, and its punished coordinate equals
the behavioral punishment value.  The exact semantic-prefix construction
also stays diagonal: if the current pair is `(v_t,v_t)` and `q_t` is exact
Nash against `v_t`, the next prefix pair is again diagonal.  For the argument
below it is enough to use the already packaged exact floor orbit:

```text
v_(t+1) = quittingRootSuccessorPayoff reward v_t q_t,
q_t exact Nash against v_t,
punishmentValue_i <= v_t(i),
a_t >= 0,
sum a_t < infinity,
v_t -> L.
```

The source/endpoint/no-sure-exit provenance is retained.  No new endpoint is
selected in this note.

## 2. Source and duplicate audit

The declarations inspected were restricted to the maintained lane:

- `QuittingPositiveJointPrefixReachPunishmentEndpoint`,
  `debt_eq_zero`, `payoff_eq_envelope`, `HasSureExitNashPrefix`, and
  `QuittingPositiveJointPrefixReachNoSureExitResidual` in
  `PositiveJointPrefixReachEndpoint.lean`;
- `QuittingPositiveJointPrefixReachPunishmentEndpoint.exactPrefixOrbit` and
  `wellSupported_or_summableExactPrefixPort` in
  `PositiveJointEndpointSequentialReduction.lean`;
- `QuittingPunishmentFloorInfiniteOrbit`, `toFinitePrefix`, and
  `toFiniteSegment` in the finite Bellman orbit files;
- `SummableChargeAllContinuePort` and its convergence fields in
  `PunishmentFloorInfiniteOrbitChargeDichotomy.lean`;
- `exists_singleSeamProjectiveLasso_of_floorPrefix_`
  `cumulativePayoffNearReturn` in
  `Quitting/Projective/CumulativeChargeNearReturn.lean`;
- `QuittingFiniteSingleSeamProjectiveLasso.`
  `exists_supportRationalDivergentPath`;
- `quittingWellSupportedAbsorbingSequenceExistence_`
  `of_singleSeamProjectiveLassos` in the new sequential reduction; and
- `nonempty_summableChargeSignedTerminalPort_of_displacement` in
  `PunishmentFloorSummablePortLabel.lean`.
- `SummableChargeAllContinuePort.nonempty_positiveSurvivalBoundary`,
  `stationaryExistence_or_positiveSingletonDefectResidual`, and
  `QuittingPositiveJointPrefixReachNoSureExitResidual.`
  `wellSupported_or_stationary_or_positiveSingletonDefect` in the current
  `PositiveJointSummablePortPhantomReduction.lean`; and
- `QuittingSupportBellmanPositiveSurvivalBoundary.PositiveSingletonSuffixDefect`
  in `Classification/SimonFiniteOrbit/CompactSpineSurvivalBoundary.lean`.

The closest checked result is the nonsummable-orbit S.3 arm in the new file.
It uses divergent cumulative charge plus compact recurrence.  The result here
is different: total charge is summable, and return is the equality `L=E` (or
small finite seams relative to the finite charge), not recurrence at
unbounded charge.

`Diagnostics/Quitting/Chronology/AbsorptionClockBallisticity.lean` also has a
ballisticity theorem, but for an optimized positive-debt tail under a terminal
exploitability witness.  Its proof uses collision purification and a strict
singleton packet.  The present estimate is an elementary lasso consequence
for any exact punishment-floor orbit under failure of the AGKRS
well-supported S.3 predicate.  Neither theorem supplies the other's input.

The reviewed summable-port notes already identify a nonzero displacement
with a signed terminal label.  A narrow search found no declaration or note
which first proves that S.3 failure forces the quantitative displacement
bound below, or which consumes a positive-charge returned **summable** port
into literal S.3.

### 2.1 Current checked phantom contraction

The current source now also observes that the formal all-Continue limit `L`
gives a constant positive-survival support--Bellman boundary.  Consequently,
at every nonnegative tolerance, the port gives either S.1 or a
`QuittingSupportBellmanPositiveSingletonDefectResidual`.  The latter contains
an actual player `i` with positive singleton self-reward and actual late
executable suffix deviations whose gain converges to that reward.

This is a strict and useful contraction, but it does not duplicate or subsume
the result below.  The positive-singleton defect is compatible with both zero
and positive total charge and supplies no payoff return.  Conversely, the
ballistic estimate below uses global failure of S.3 and supplies either an
S.3 near-return consumer or a quantitative endpoint displacement; it does not
consume the positive-singleton defect.  In the hard branch both conclusions
must therefore be retained simultaneously.

### 2.2 Subsequent checked uniform-payoff closure

The later checked theorem

```text
QuittingPositiveJointPrefixReachPunishmentEndpoint.
  isUniformEquilibriumPayoff
```

in `PositiveJointEndpointUniformPayoff.lean` observes that the actual reached
endpoint is already a diagonal point of the terminal-semantic carrier.  It
therefore gives a uniform-equilibrium payoff without using the port, its
charge, or its limit.  Thus the ballistic dispatch below remains useful only
for the stronger literal AGKRS S.1/S.2/S.3 classification and for structural
information about the selected orbit.  It is no longer an unresolved
uniform-payoff-existence lane.

## 3. Failure of S.3 supplies one exact scale

Assume

```text
notS3 : not QuittingWellSupportedAbsorbingSequenceExistence reward.
```

By the literal quantifiers of that predicate, there is a number `delta>0`
such that no completely absorbing root sequence is support-locally
`delta`-Nash at every tail.  Fix

```text
e = delta/2 > 0.                                      (3.1)
```

A single-seam projective lasso at error `e` yields, by the checked divergent
path theorem, a completely absorbing sequence at support error `2e=delta`.
Therefore no such lasso exists.

This step uses the exact S.3 failure available in the hard prioritized
branch.  It is not a claim about the raw positive-joint residual alone.

## 4. Finite-segment ballisticity

For integers `s,N`, let

```text
C(s,N) = sum_{t=s}^{s+N-1} a_t,
D(s,N) = max_i |v_(s+N)(i)-v_s(i)|.
```

### Proposition 4.1 (exact cumulative-charge separation)

Under `notS3`, every finite segment with `C(s,N)>0` satisfies

```text
D(s,N) > e * C(s,N)/(1+C(s,N)).                       (4.1)
```

**Proof.**  Suppose instead that the weak reverse inequality holds.  The
checked `O.toFiniteSegment s N` is an exact punishment-floor finite prefix;
its charge is exactly `C(s,N)`.  Use

```text
chargeFloor = C(s,N),
seamError   = D(s,N),
error       = e.
```

Every coordinate seam is at most `seamError`, and the supposed inequality is
exactly the seam-scale premise

```text
seamError <= error * chargeFloor/(1+chargeFloor).
```

The cumulative-charge single-seam compiler therefore constructs a lasso at
error `e`.  Its divergent support-rational path has support error
`2e=delta`; nonsummable absorption makes that path completely absorbing.
This contradicts the defining choice of `delta`. `QED`

The estimate is uniform over **all** starts and lengths.  No eventual
threshold, selected terminal label, or no-sure-exit hypothesis is used.

## 5. Returned positive-charge ports give S.3

### Proposition 5.1 (summable returned-port consumer)

If

```text
0 < A  and  L=E,                                      (5.1)
```

then `QuittingWellSupportedAbsorbingSequenceExistence reward` holds.

**Direct proof.**  Let an arbitrary lasso accuracy `error>0` be given.  Put
`c=A/2>0`.  Since the partial charge sums converge to `A`, sufficiently long
initial segments have charge at least `c`.  Since `v_N->L=E=v_0`, their
coordinate seams are eventually at most

```text
error * c/(1+c).
```

The cumulative-charge single-seam compiler gives a lasso at this arbitrary
accuracy.  The checked lasso-to-well-supported theorem then gives S.3.
`QED`

Equivalently, under `notS3`, Proposition 4.1 applied to the initial segments
and then passed to the limit gives a contradiction to `(5.1)`.

This is the promised branch-valued consumer.  It strictly extends the new
nonsummable S.3 arm to the summable but positively charged returned case.

## 6. Infinite-port displacement modulus

Let

```text
d = max_i |L(i)-E(i)|.
```

The partial charges tend to `A`, and finite-player convergence gives
`D(0,N)->d`.  Passing `(4.1)` to the limit yields the non-strict but
quantitative estimate

```text
d >= e * A/(1+A).                                     (6.1)
```

Thus under failure of S.3:

- if `A>0`, then `L!=E`, with the explicit separation `(6.1)`;
- if `L=E`, then `A=0`.

Since every `a_t` is nonnegative, `A=0` forces `a_t=0` at every stage.  A
finite product root has zero absorption exactly when every player Continues
surely.  The policy recursion then gives

```text
q_t = allContinue and v_t=E for every t.              (6.2)
```

This is the literal zero-charge all-Continue phantom, not merely an
asymptotic port.

## 7. Quantitative signed-label dispatch

Assume the positive-charge arm `A>0` under `notS3`.  The endpoint supplies a
player, so the player type is nonempty.  Put

```text
rho = e*A/(1+A)>0.                                    (7.1)
```

By `(6.1)` and finiteness, some coordinate `who` satisfies

```text
rho <= |L(who)-E(who)|.                               (7.2)
```

Take `M=quittingRewardBound reward`.  The positive displacement forces
`M>0`; reward coordinates and all orbit values are bounded by `M`.  The
checked declaration

```text
O.nonempty_summableChargeSignedTerminalPort_of_displacement
```

therefore yields one fixed player, sign, and nonempty terminal coalition
whose signed contribution has the finite-label share of `rho`, together with
the mass bound

```text
rho /
  (2*M*(2^|I|-1))
  <= sum' t, quittingRootCoalitionMass q_t terminal.  (7.3)
```

The signed label is not a new branch consumer, but `(7.1)` makes its scale
source-native: it is forced quantitatively by the hard S.3 failure and the
port's own total charge, rather than assumed as an arbitrary displacement.

## 8. Exact hard-residual dispatch

Combining the new checked endpoint reduction with the preceding arguments
gives the following ordinary-mathematics theorem.

> Every positive-joint no-sure-exit residual yields one of:
>
> 1. well-supported S.3;
> 2. an actual eligible no-sure-exit endpoint whose canonical exact-prefix
>    orbit is identically all Continue and constant at that endpoint; or
> 3. an actual eligible no-sure-exit endpoint with a summable exact-prefix
>    port of positive total charge, quantitatively separated from its start
>    by `(6.1)` and carrying the fixed signed terminal mass `(7.3)`.

Under the hard global failure of S.3, only alternatives 2 and 3 remain.
Under failure of S.1 as well, alternative 2 is still not automatically
excluded: `(E,allContinue)` is a formal Bellman self-loop, while the literal
all-Never profile pays zero.  If `E=0`, singleton domination does give the
literal all-Continue stationary equilibrium and S.1; hence the genuinely hard
zero-charge phantom has `E!=0`.

The checked phantom contraction sharpens this hard dispatch further.  At any
chosen positive tolerance, global failure of S.1 forces the same port to
carry a `QuittingSupportBellmanPositiveSingletonDefectResidual`.  Thus the
two genuine survivors are not featureless:

1. a nonzero eligible zero-charge all-Continue endpoint together with an
   actual persistent positive-singleton suffix gap; or
2. a ballistic signed displaced port together with that same kind of actual
   suffix gap.

This intersection is source-faithful because both certificates are built
from the same `port` and its literal limit.  It must not be identified with
the positive-singleton-defect arm of a separately selected prioritized
pointwise source: the reward table is common, but neither the boundary nor
the underlying suffix profile is thereby equal.

The no-sure-exit field is preserved in both residual arms but is not used by
the ballistic estimate.  It rules out a separate S.2 attachment at the
eligible endpoint; it does not convert the all-Continue phantom or the signed
terminal label into a new source.

## 9. Boundary tests

1. **Reviewed half--half positive-endpoint table.**  Its exact stationary
   half--half root has positive absorption and fixes `E=(0,1)`.  Repeating it
   is already a completely absorbing support-perfect sequence, so the
   returned-port consumer correctly lands in S.3.  This table cannot satisfy
   `notS3`.
2. **One-player escaping reset.**  With solo reward `b>0`, the eligible
   endpoint is `E=b=P`, and the all-Continue selected orbit has `A=0`, `L=E`.
   This realizes the zero-charge phantom interface.  The game separately has
   S.1 and S.3, so it is not a hard counterexample; it confirms that the orbit
   fields alone do not eliminate alternative 2.
3. **Positive displacement.**  Formula `(6.1)` allows a bounded summable path
   to move at nonzero absorption-clock speed.  This is not a contradiction:
   summable charge permits a finite total displacement.  Treating strict real
   displacement as a well-founded rank would be invalid.
4. **Zero total charge.**  It is essential to separate `A=0` from merely
   `a_t->0`.  Summability always gives the latter, while only `A=0` makes every
   root literally all Continue.

## 10. Exact remaining AGKRS-classification consumer

After the separate checked uniform-payoff closure, the remaining attempt to
classify the positive-joint source into literal S.1/S.2/S.3 is concentrated in
two source-matched interfaces, each also carrying the checked
positive-singleton suffix defect.

1. **Nonzero eligible all-Continue phantom with an actual suffix defect:** a diagonal carrier point
   `(E,E)` with some punished coordinate at its behavioral punishment value,
   `E!=0`, singleton rewards below `E`, and no sure-exit exact root at any
   eligible endpoint.  A positive singleton player has a fixed unrestricted
   gain on late literal suffixes.  One must pay that gain while realizing the
   annotation, extract S.1/S.3, or regenerate a smaller source.
2. **Ballistic signed summable port with an actual suffix defect:** a source-matched endpoint-to-limit
   displacement with fixed terminal label and the quantitative mass floor
   `(7.3)`, plus a positive singleton player whose late suffix deviations stay
   uniformly profitable.  One must align the paid suffix deviation with the
   fixed signed terminal label, or turn one of them into a returned floor
   path, a sequential absorbing construction, or a genuinely finite
   maintained rank.

Neither fixed-face deletion nor arbitrary reclassification supplies this
arrow: the reviewed active-face regression shows endpoint provenance can be
lost under deletion, and a real-valued strict displacement can iterate in a
Zeno fashion.

## 11. Lean handoff

The narrow formalization target should extend
`PositiveJointEndpointSequentialReduction.lean` with two declarations.

1. For an arbitrary `QuittingPunishmentFloorInfiniteOrbit`, failure of
   `QuittingWellSupportedAbsorbingSequenceExistence` gives `delta>0` such that
   every positive-charge `toFiniteSegment` satisfies `(4.1)`.  The proof is
   one application of
   `exists_singleSeamProjectiveLasso_of_floorPrefix_`
   `cumulativePayoffNearReturn`, followed by
   `QuittingFiniteSingleSeamProjectiveLasso.`
   `exists_supportRationalDivergentPath` and the standard nonsummable-
   absorption completeness lemma.
2. Specialize to a `SummableChargeAllContinuePort` and pass to the limit,
   returning either S.3, literal zero charge, or a
   `SummableChargeSignedTerminalPort` with
   `rho=(delta/2)*A/(1+A)`.

The proof should use a finite maximum or the `pi` metric consistently when
passing finite-coordinate seams to the limit.  It must not replace total
charge `sum a_t` by absorbed probability `1-product(1-a_t)` without the
checked ratio inequality.

No formalizer should reprove either the current phantom contraction or the
checked endpoint uniform-payoff theorem.  The narrow new handoff is only the
finite-segment ballisticity and its limit/signed-label specialization,
followed by an intersection theorem with
`stationaryExistence_or_positiveSingletonDefectResidual` if useful.

## 12. Independent review

`CODEX_EULER` checked the full quantifier and constant ledger and returned
**REVISE then PASS**.  The required source/novelty comparison with
`PositiveJointSummablePortPhantomReduction.lean` has been incorporated in
Sections 2.1, 8, 10, and 11.  No mathematical objection remains.

The review specifically checked:

Please check:

1. the quantifier extraction of `delta` from global S.3 failure;
2. the factor `e=delta/2` and the lasso's doubled support error;
3. the strict finite-segment inequality `(4.1)`;
4. the limiting modulus `(6.1)` and the `A=0` rigidity;
5. the signed-port constant `(7.3)`; and
6. the scope of the two surviving hard interfaces; and
7. the claim that the current checked positive-singleton contraction and the
   ballistic dispatch coexist source-matched but neither consumes the other.
