# Review of `FIN4_THREE_ROLE_ASCENT_PAID_CAP_HANDOFF`

## Verdict

The central mathematical construction is valid.  In particular, the proposed
deviation-to-paid-row lemma is a real and reusable source-provenance result:
one supplied profitable behavioral deviation can be bracketed by one support
atom of its stopping law and one support atom of the prescribed stopping law,
and the resulting two pure times generate an exact paid first-disagreement row
on the literal source profile.

The final conclusion is also valid:

```text
cofinally many selected quantitative paid-cap descents
or eventually selected literal paid-cap inert stalls.
```

This is not, however, a consumer of the strict three-role ascent.  The strict
ascent hypothesis is unused, the descent sizes may converge to zero, and the
inert stalls occur on a varying sequence of actual sources.  The result is best
described as a source-aligned transition from the endpoint family into the
already open paid-cap residual, not as closure or rank progress.

## Claim reviewed

For a `ConcentratedCollisionThreeRoleEndpointLaw` with source profiles
`sigma n`, pure-endpoint target profiles `tau n`, fixed mover, and packet
resolution `rho`, the note claims:

1. every endpoint update has fixed whole-profile mover gain at least
   `delta = rho^2 * D_* / 8`;
2. that exact deviation produces a paid first-disagreement row whose source
   witness lies in the prescribed stopping-law support and whose receiving
   witness lies in the endpoint deviation's stopping-law support;
3. these rows give actual paid-cap sources and summable ports based at the
   endpoint's source minimum;
4. the family is a paid-cap minimum approximation, so total absorption and
   cap displacement tend to zero;
5. the hard-residual terminal witness excludes the charged-near-return arm;
   and
6. a cofinal-subsequence dichotomy leaves quantitative descent cofinally or
   inertness eventually.

## Steps that check

### 1. The fixed endpoint gain is literal

`ConcentratedCollisionFourRole.ThreeRoleTransfer.gain_globalFloor` in
`Research/Quitting/ConcentratedCollisionFourRoleMonodromy.lean` gives

```text
rho^2 * D_* / (2 * card I) <= gain.
```

For `Fin 4` this is exactly `rho^2 * D_* / 8`.  The definition of
`ConcentratedCollisionFourRole.gain` is the complete terminal-payoff difference
between `sigma n` and the profile obtained by updating the fixed mover to the
stored one-date pure-endpoint deviation.  The endpoint's
`transfer_mover_eq`, `endpointAction_eq`, and target-profile definition give
the claimed literal equality with `tau n`.

### 2. The deviation-to-paid-row lemma is sound

Against fixed opponents, both the prescribed mover strategy and the supplied
endpoint deviation evaluate the same bounded pure-time payoff function `V`,
under their respective stopping laws.  This is exactly
`quittingTerminalPayoff_update_eq_expect_stoppingLaw_pureTime` from
`BehaviorStoppingPayoff.lean`.

`exists_support_pair_expect_sub_le_sub` from
`MathUE/ProbabilityMassFunction/BoundedSupportAverage.lean` then supplies
support atoms `receivingWitness` and `sourceWitness` with

```text
E_q[V] - E_sigma[V]
  <= V(receivingWitness) - V(sourceWitness).
```

The fixed endpoint gain therefore yields the desired pure-time difference.
`exists_quittingPaidFirstDisagreementRow_of_pureTimePayoff_sub` from
`TerminalSemanticPaidFirstDisagreement.lean` converts that difference into the
exact first-disagreement row, retaining finite dates and Never.  A small new
wrapper is genuinely needed if the two support-membership proofs are to remain
public, because the existing row stores the times but not their membership in
the two originating stopping-law supports.

This argument does not assert that the complete endpoint strategy itself is a
single Bellman edge.  It correctly extracts one paid edge from its expectation
gain.

### 3. The source minimum is legitimate

`endpoint.sourceLimit` belongs to the semantic carrier and has total debt equal
to `source.point.1`.  Since the latter is globally minimal and has positive
debt, `endpoint.sourceLimit` is another positive global minimum.  It may
therefore be used as the `minimum` field of each
`QuittingPaidCapLiftedSource`; no attainment of that minimum is required.

The structure called `QuittingActualProfileTerminalGapPaidCapPort` does not
logically require that its row have been selected from the global terminal-gap
witness.  Its fields can be filled directly from the endpoint-derived paid
row, as the note says.  A less provenance-laden new structure name would make
the interface clearer, but this is not a mathematical issue.

### 4. Minimum-approximation contraction still applies

The source semantic pairs converge to `endpoint.sourceLimit`.  The standard
debt budget for any paid-cap source depends on global minimality and positive
minimum debt, not on how its paid row was obtained.  Hence the existing
estimates indeed imply

```text
totalAbsorption n -> 0,
capDisplacement n -> 0.
```

The fields of `QuittingActualProfilePaidCapMinimumApproximation` can therefore
be proved for this supplied family by the same argument as its existing
terminal-gap constructor.

### 5. Charged near-return is excluded

`ChargedNearReturn.uniformEquilibriumPayoff` supplies a uniform-equilibrium
payoff.  The retained `source.residual.witness` is a terminal exploitability
witness and rules out every such payoff.  No comparison between `delta` and
the witness's numerical terminal gap is needed.

### 6. The final subsequence split is exhaustive

For each natural index, the exact trichotomy and exclusion of charge give
`Descent n ∨ Inert n`.  Classically, either `Descent` is cofinal, in which case
one extracts a strictly increasing sequence of descent indices, or it is not
cofinal, in which case it is eventually false and `Inert` is eventually true.
This step is correct.

## Required qualifications

### The strict ascent hypothesis does no work

Every step above uses the source convergence and the fixed endpoint deviation
gain, but not

```text
D(source.point.1) < D(endpoint.targetPoint.1).
```

Thus the theorem is more general than advertised: any cofinal family of actual
profiles approaching a positive semantic minimum and carrying one fixed-gain
supplied behavioral deviation admits this paid-cap handoff.  Conversely, the
construction does not mathematically exploit the three-role target ascent.

This should be stated explicitly in the theorem organization.  The general
deviation-family handoff should be proved first; the strict-ascent result is
then a source-attached adapter retaining `hstrict` for future consumers.

### The conclusion is not quantitative renewal

Although every `QuantitativeDebtDescent` is strictly positive at its own
index, the family simultaneously satisfies

```text
capDisplacement n -> 0.
```

The corresponding debt-drop lower bounds can therefore tend to zero.  A
cofinal family of descents is not a well-founded descent, a uniform descent,
or a regenerated source family.

Likewise, `InertStall` concerns the arbitrarily selected summable port at one
source.  Eventual inertness along varying `sigma n` does not give one attained
inert minimum source, unique all-Continue at a limiting cap, or a reusable
chronology.

### Endpoint alignment is the only new advantage over the global witness

The hard residual already supplies a terminal exploitability gap, so existing
theorems can construct some fixed-gain paid-cap port at every `sigma n` without
using the endpoint at all.  The new mathematical content is narrower and
cleaner: the observer is the endpoint's fixed mover, and the paid witnesses are
selected from the prescribed source law and that exact endpoint deviation law.

The current `QuantitativeDebtDescent` and `InertStall` consumers do not use
this extra alignment.  It is nevertheless worth retaining because a future
consumer may need the endpoint action, roles, routed terminal, or response
provenance.  Until such a consumer is proved, this is a strengthened passport,
not strict atlas contraction.

## Recommendation

Retain the result as valid Research mathematics.  The most reusable theorem is
the general supported-deviation-to-paid-first-disagreement lemma.  The
source-attached three-role wrapper is also worth keeping because it preserves
the fixed mover and exact endpoint deviation, but its headline should say
"handoff to the paid-cap residual" rather than suggest consumption of ascent.

It should not be exported as a completed ascent consumer.  A genuinely
conjecture-facing follow-up must use the retained endpoint alignment to do at
least one of:

```text
derive the zero-debt/incidence data needed for actual paid-reset regeneration;
prove a uniform or renewable descent from the cofinal descent arm;
or contradict/consume eventual endpoint-aligned inert stalls.
```

## Sources inspected

* `Research/Quitting/ConcentratedCollisionThreeRoleEndpointLaw.lean`
* `Research/Quitting/ConcentratedCollisionFourRoleMonodromy.lean`
* `Research/Quitting/FinFourProducerAtlas/ThreeRoleRegeneration.lean`
* `Research/Quitting/PaidRowCapPortDispatch.lean`
* `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/ActualProfileTerminalGapPaidCap.lean`
* `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/ActualProfilePaidCapMinimumApproximation.lean`
* `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/Endpoint/PaidCapPortExactTrichotomy.lean`
* `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPaidFirstDisagreement.lean`
* `UniformEquilibrium/Quitting/Paths/BehaviorStoppingPayoff.lean`
* `MathUE/ProbabilityMassFunction/BoundedSupportAverage.lean`
* `docs/FRONTIER.md`
* `docs/TOOLKIT.md`
