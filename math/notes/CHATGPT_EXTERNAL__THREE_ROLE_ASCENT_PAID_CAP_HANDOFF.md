# Fin4 three-role ascent: source-faithful paid-cap handoff

Author: `CHATGPT_EXTERNAL`

Status: `PROOF_DRAFT`; ordinary mathematics, pending its independent gate.

Source: supplied in `ephemeral/ASCENT_NORM/` and moved here without rewriting
the mathematical body.

## Status

This note gives the strongest unconditional connection supported by
`ConcentratedCollisionThreeRoleEndpointLaw` alone.

It does **not** identify a canonical pair and does **not** identify the
one-date endpoint interpolation with a maximal cap-prefix ray.  Instead, it
uses the endpoint's own retained finite-rank mover deviations to enter the
existing actual-profile paid-cap machinery.

The construction is source-faithful and executable.  Its final exact output is

```text
cofinally many quantitative paid-cap debt descents
or
eventually literal paid-cap inert stalls.
```

The charged near-return branch is impossible under the original hard
residual.  The remaining descent and inert alternatives are existing checked
nodes, but they are not terminally consumed by the current generic interface.

## 1. Exact retained rows

Fix

```text
source   : FinFourMinimumAtomProducer reward bound
packet   : QuittingReprojectionConcentratedPacket ...
endpoint : ConcentratedCollisionThreeRoleEndpointLaw
             source.point.1 packet mover recipient
```

and, for the branch under discussion,

```text
hstrict : D(source.point.1) < D(endpoint.targetPoint.1).
```

For each retained rank `n`, put

```text
sigma n = ConcentratedCollisionFourRole.packetProfile packet
            (endpoint.ranks n)

t n     = packet.mark (endpoint.ranks n)

q n     = quittingStagePureEndpointBehaviorDeviation reward (sigma n)
            mover (t n)
            (ConcentratedCollisionFourRole.action reward (sigma n) (t n)
              mover)

tau n   = Function.update (sigma n) mover (q n).
```

Then `tau n` is definitionally the target profile occurring in
`endpoint.target_joint_tendsto`.  Thus

```text
Function.update (sigma n) mover (q n) = tau n
```

is the first backward-compiler equation.

The endpoint also retains

```text
endpoint.source_tendsto : semantic(sigma n) -> endpoint.sourceLimit
endpoint.target_joint_tendsto : joint(tau n) -> endpoint.targetPoint.
```

Moreover,

```text
D(endpoint.sourceLimit) = D(source.point.1) = D_* > 0.
```

Consequently `endpoint.sourceLimit` is itself a positive global minimum of
total terminal-semantic debt.  No unrelated minimizer is selected.

## 2. Uniform endpoint-derived mover gain

Let

```text
rho   = packet.resolution
delta = rho^2 * D_* / 8.
```

Then `delta > 0`.  At every retained rank, `endpoint.transfer n` is an actual
`ThreeRoleTransfer` whose mover is the fixed `mover`.  Its checked
`gain_globalFloor`, specialized to `Fin 4`, gives

```text
delta <=
  quittingTerminalPayoff reward (tau n) mover -
    quittingTerminalPayoff reward (sigma n) mover.
```

This is stronger for the present purpose than the limiting mover-debt drop:
it is a literal finite-profile unilateral deviation bound at every retained
rank.

Notice that this step does not use `hstrict`.  The handoff therefore applies
to every three-role endpoint law; in the ascent branch, `hstrict` is retained
as part of the wrapper and identifies the atlas origin.

## 3. A supplied profitable deviation gives a supported paid row

The terminal-gap paid-cap proof factors through the following more precise
lemma, which should be extracted as a reusable theorem.

### Deviation-to-paid-row lemma

Let `sigma` be an actual behavioral profile, let `i` be a player, let `q` be
one behavioral deviation by `i`, and let `g > 0`.  If

```text
g <= payoff(update sigma i q, i) - payoff(sigma, i),
```

then there are pure quit times `sourceWitness` and `receivingWitness` such
that

```text
sourceWitness in stoppingLaw(sigma i).support,
receivingWitness in stoppingLaw(q).support,

g <= pureTimePayoff(sigma,i,receivingWitness)
       - pureTimePayoff(sigma,i,sourceWitness),
```

and hence an exact

```text
QuittingPaidFirstDisagreementRow reward sigma i g
```

whose two stored witnesses are exactly these two times.

### Proof

Set

```text
V(t) = quittingPureTimeDeviationPayoff reward sigma i t.
```

Terminal payoff under a behavioral strategy of `i` is the expectation of
`V` under that strategy's stopping law.  Therefore

```text
E_[stoppingLaw q] V - E_[stoppingLaw (sigma i)] V >= g.
```

`V` is uniformly bounded by `quittingRewardBound reward`.  The bounded-support
average lemma supplies one atom of the first stopping law and one atom of the
second whose value difference dominates the difference of expectations.  The
existing theorem

```text
exists_quittingPaidFirstDisagreementRow_of_pureTimePayoff_sub
```

then constructs the exact first-disagreement chronology and its paid live-mass
identity.

Applied with `(sigma n, mover, q n, delta)`, this keeps the paid row aligned
with the endpoint's fixed mover.  It is not an arbitrary exploitability row.
Its receiving witness belongs to the stopping-law support of the **same exact
endpoint deviation** `q n`.

## 4. The actual paid-cap source at each endpoint rank

For each `n`, define

```text
paidSource n : QuittingPaidCapLiftedSource reward
```

by

```text
minimum    = endpoint.sourceLimit
profile    = sigma n
observer   = mover
gain       = delta
row        = the endpoint-derived paid row from Section 3.
```

The required minimum fields are supplied by

```text
endpoint.source_on_minimum_fiber
source.minimum
source.minimumDebt_pos.
```

Choose

```text
port n : (paidSource n).SummablePort
```

using `QuittingPaidCapLiftedSource.nonempty_summablePort`.

Equivalently, package these fields as

```text
actual n : QuittingActualProfileTerminalGapPaidCapPort
  reward endpoint.sourceLimit (sigma n) delta.
```

This structure's name reflects its original constructor, but its fields do not
require `delta` itself to be a global terminal exploitability gap.  Here it is
constructed directly from the endpoint-derived row.

The handoff retains the original `source`, `packet`, `endpoint`, `mover`,
`recipient`, `hstrict`, routed terminal, target law, and all quantitative
endpoint bounds.  The paid-cap node forgets none of them because it is stored
inside a source-attached wrapper rather than returned alone.

## 5. Source-faithful minimum approximation

The exact source profiles already converge to a minimum:

```text
semantic(sigma n) -> endpoint.sourceLimit.
```

Hence the preceding sequence instantiates the existing

```text
QuittingActualProfilePaidCapMinimumApproximation
  reward endpoint.sourceLimit delta
```

with its profile sequence fixed to `sigma` and its ports fixed to the
endpoint-derived ports.

Writing `A_n` for total cap-prefix absorption and `C_n` for cap displacement,
the checked contraction estimates are

```text
0 <= A_n <= (D(sigma n) - D_*) / D_*,

0 <= C_n <=
  2 * quittingRewardBound reward * (D(sigma n) - D_*) / D_*.
```

Since `D(sigma n) -> D_*`, both quantities tend to zero.  Thus the connection
is not merely a paid row: it supplies the complete summable port and its exact
minimum-fibre contraction data.

## 6. Elimination of the charged branch

For each rank the existing exact trichotomy gives exactly one of

```text
ChargedNearReturn
QuantitativeDebtDescent
InertStall.
```

A `ChargedNearReturn` constructs a uniform-equilibrium payoff.  The original
`source.residual.witness` is a terminal exploitability witness and therefore
rules out every uniform-equilibrium payoff.  Hence, for every `n`,

```text
QuantitativeDebtDescent (paidSource n) (port n)
or
InertStall (paidSource n) (port n).
```

This use of the hard residual is independent of the numerical relation between
`delta` and the residual's terminal-gap constant.

## 7. Cofinal descent versus eventual inertness

Let

```text
Descent n := QuantitativeDebtDescent (paidSource n) (port n).
Inert n   := InertStall (paidSource n) (port n).
```

Since `Descent n or Inert n` for every `n`, classical finite-label extraction
gives the exact exhaustive alternative

```text
(there exists k : Nat -> Nat,
   StrictMono k and forall n, Descent (k n))

or

(there exists N,
   forall n >= N, Inert n).
```

Indeed, if `Descent` occurs frequently at `atTop`, extract a strict cofinal
subsequence.  Otherwise it is eventually false, and the pointwise dichotomy
forces `Inert` eventually.

This is the correct atlas connection for the generic three-role ascent.
Neither arm depends on unsupported coalition incidence.

## 8. Backward compiler and retained provenance

The wrapper should expose the following exact equations for every retained
rank:

```text
paid profile:
  (actual n).source.profile = sigma n

endpoint deviation:
  Function.update (sigma n) mover (q n) = tau n

endpoint target:
  tau n = ConcentratedCollisionFourRole.targetProfile reward
            (ConcentratedCollisionFourRole.packetProfile packet
              (endpoint.ranks n))
            (packet.mark (endpoint.ranks n)) mover

source convergence:
  semantic(sigma n) -> endpoint.sourceLimit

target convergence:
  joint(tau n) -> endpoint.targetPoint

paid-row source witness:
  row.sourceWitness in stoppingLaw(sigma n mover).support

paid-row receiving witness:
  row.receivingWitness in stoppingLaw(q n).support.
```

The last two equations are important.  They certify that the paid cap port was
compiled from the endpoint's own source-to-target deviation, rather than from
an unrelated use of the terminal exploitability witness.

Because the wrapper stores `endpoint`, it also retains verbatim:

```text
mover
recipient
endpoint.routedTerminal
endpoint.terminalMass_floor
endpoint.mover_drop
endpoint.recipient_rise
hstrict.
```

## 9. Intended Lean interface

A useful organization is:

```lean
structure QuittingDeviationPaidFirstDisagreement
    (reward : {S : Finset ι // S.Nonempty} -> Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (observer : ι)
    (deviation : (quittingGame reward).BehaviorStrategy observer)
    (gain : Real) where
  sourceWitness : Option Nat
  receivingWitness : Option Nat
  sourceWitness_mem : sourceWitness in
    (quittingBehaviorStoppingLaw reward (profile observer)).support
  receivingWitness_mem : receivingWitness in
    (quittingBehaviorStoppingLaw reward deviation).support
  gain_le : gain <=
    quittingPureTimeDeviationPayoff reward profile observer receivingWitness -
      quittingPureTimeDeviationPayoff reward profile observer sourceWitness
  row : QuittingPaidFirstDisagreementRow reward profile observer gain
  row_sourceWitness : row.sourceWitness = sourceWitness
  row_receivingWitness : row.receivingWitness = receivingWitness

 theorem nonempty_deviationPaidFirstDisagreement
    (hgain_pos : 0 < gain)
    (hgain : gain <=
      quittingTerminalPayoff reward
          (Function.update profile observer deviation) observer -
        quittingTerminalPayoff reward profile observer) :
    Nonempty (QuittingDeviationPaidFirstDisagreement
      reward profile observer deviation gain)
```

The source-attached node can then be:

```lean
structure FinFourThreeRoleEndpointPaidCapHandoff
    (source : FinFourMinimumAtomProducer reward bound)
    (endpoint : ConcentratedCollisionThreeRoleEndpointLaw
      source.point.1 packet mover recipient)
    (hstrict : D source.point.1 < D endpoint.targetPoint.1) where
  gain : Real
  gain_eq : gain = packet.resolution ^ 2 * D source.point.1 / 8
  gain_pos : 0 < gain

  sourceProfile : Nat -> (quittingGame reward).BehaviorProfile
  deviation : forall n,
    (quittingGame reward).BehaviorStrategy mover
  targetProfile : Nat -> (quittingGame reward).BehaviorProfile

  sourceProfile_eq : forall n, sourceProfile n =
    ConcentratedCollisionFourRole.packetProfile packet (endpoint.ranks n)
  targetProfile_eq_update : forall n,
    targetProfile n = Function.update (sourceProfile n) mover (deviation n)
  targetProfile_eq_endpoint : forall n, targetProfile n =
    ConcentratedCollisionFourRole.targetProfile reward
      (ConcentratedCollisionFourRole.packetProfile packet (endpoint.ranks n))
      (packet.mark (endpoint.ranks n)) mover

  deviationGain_floor : forall n, gain <=
    quittingTerminalPayoff reward (targetProfile n) mover -
      quittingTerminalPayoff reward (sourceProfile n) mover

  paid : forall n, QuittingDeviationPaidFirstDisagreement
    reward (sourceProfile n) mover (deviation n) gain

  approximation : QuittingActualProfilePaidCapMinimumApproximation
    reward endpoint.sourceLimit gain
  approximation_profile : approximation.profile = sourceProfile
  approximation_row : forall n,
    (approximation.actual n).source.row = (paid n).row

  descent_or_inert : forall n,
    (approximation.actual n).source.QuantitativeDebtDescent
        (approximation.actual n).port or
      (approximation.actual n).source.InertStall
        (approximation.actual n).port

  outcome :
    (exists k : Nat -> Nat, StrictMono k and forall n,
      (approximation.actual (k n)).source.QuantitativeDebtDescent
        (approximation.actual (k n)).port) or
    (exists N, forall n, N <= n ->
      (approximation.actual n).source.InertStall
        (approximation.actual n).port)
```

The actual Lean syntax should use `∧`, `∨`, `∈`, and the repository's named
`quittingTerminalSemanticDebtSum`; the ASCII presentation above is only to
make the interface readable.

The headline theorem is then

```lean
theorem
  FinFourThreeRoleRegenerationOrAscent.nonempty_endpointPaidCapHandoff
  (result : FinFourThreeRoleRegenerationOrAscent source packet)
  (hstrict : D source.point.1 < D result.endpoint.targetPoint.1) :
  Nonempty (FinFourThreeRoleEndpointPaidCapHandoff
    source result.endpoint hstrict)
```

## 10. Relation to rightmost-minimum normalization

The rightmost-minimum horizontal normalization remains correct, but it is not
needed for this atlas edge.  The incoming endpoint's **source profiles already
converge to a minimum semantic point**, and its transfer object already gives a
uniform finite-rank mover gain.  Compiling at those source profiles preserves
more literal provenance and avoids introducing the continuum ray into the
paid-cap development.

If the normalized ray is nevertheless retained, the same construction applies
at its rightmost minimum parameter `theta`.  The full endpoint deviation then
has gain

```text
(1 - theta) * originalGain,
```

so a fixed positive floor survives because `theta < 1`.  This gives an
alternative front-end to the same paid-cap handoff, but no stronger downstream
consumer.

## 11. Exact boundary

This connection supplies the missing source-preserving atlas edge.  It does
not prove a canonical-pair handoff, a maximal-ray handoff, a regenerated
minimum source after a paid-cap descent, or impossibility of the literal inert
stall.

The remaining generic obligations are exactly:

```text
consume a QuantitativeDebtDescent without an exact zero-debt reset coordinate
and same-profile positive reset incidence;

or
consume an InertStall while retaining the endpoint-derived paid suffix.
```

Those fields are not consequences of
`ConcentratedCollisionThreeRoleEndpointLaw`.  Therefore the theorem above is
the strongest unconditional connection currently justified by the inspected
interfaces.
