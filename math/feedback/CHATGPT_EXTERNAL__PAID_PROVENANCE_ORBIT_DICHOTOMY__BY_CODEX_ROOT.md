# Review of paid-provenance orbit dichotomy

Reviewer: `CODEX_ROOT`

Contribution: external `ChatGPT` argument supplied by the user

## Verdict

**PASS for the assigned `PaidRowExactPortAlternative`; REVISE only if it is
presented as the complete universal paid producer.**

The literal prefix-orbit construction and the summability dichotomy are
correct.  The assigned alternative explicitly included the coordinatewise
punishment-floor inequality among its inputs, so the contribution proves that
alternative in a stronger literal-orbit form.  Separately, the current paid
first-disagreement source data do not supply that inequality for the receiving
profile's prescribed payoff; this is an upstream composition gap, not a gap in
`PaidRowExactPortAlternative`.

## What is valid

Let `xPaid` be any actual behavioral profile whose prescribed payoff `u0` is
in the canonical reward box and dominates the behavioral punishment vector.
Choose an exact product Nash root `q_n` against each current payoff `u_n`, put

```text
u_(n+1)=quittingRootSuccessorPayoff reward u_n q_n,
X_(n+1)=quittingRootThenContinuationProfile reward q_n X_n,
X_0=xPaid.
```

Then semantic prefixing is literal, every `u_n` remains above the floor, and
the relation edges form one exact floor-admissible orbit.  The original paid
profile is a literal suffix of every `X_n`; compactness is applied only after
this orbit is fixed.

If the absorption charges are nonsummable, the checked divergent-charge
recurrence selects arbitrarily close payoff visits with arbitrarily large
intervening cumulative charge.  The cumulative-charge lasso consumer closes
this arm.

If the charges are summable, the checked increment bound gives payoff
convergence, marginal Quit probabilities tend to zero, and the limit is an
exact floor-safe all-Continue self-loop.  Exact semantic prefixing also gives
coordinatewise nonincreasing terminal debt, so the full semantic pairs have a
corresponding all-Continue fixed-port limit once closedness of the terminal
semantic carrier is invoked.

Under a terminal exploitability witness and the floor hypothesis, every exact
root has each player's Quit probability strictly below one by
`QuittingTerminalExploitabilityWitness.exactFloorRoot_quitProbability_lt_one`.
Hence every finite prefix has positive joint Continue probability.  In the
summable arm the infinite prefix survival is positive, so the paid suffix is
not merely syntactically present: it retains positive reach.  This useful
strengthening should be included in any future statement of the conditional
theorem.

## Missing actual-data adapter

The required initial floor assumption is

```text
forall i, quittingPunishmentValue reward i
  <= quittingTerminalPayoff reward xPaid i.
```

It is not a field of `QuittingPaidFirstDisagreementRow`, nor is it produced by
`exists_eventually_paidFirstDisagreement`.  The normalized-curvature argument
controls best-response caps and two pure-time values; it does not show that
the receiving profile's **prescribed** payoff dominates punishment.  In
general `B_i(xPaid)` dominates the punishment value, but `U_i(xPaid)` need
not.  Replacing `U` by `B` would destroy the literal-profile Bellman identity
and reintroduce the semantic/actual-profile mismatch.

The contribution's equation (4) is therefore an additional hypothesis, not a
packaging change justified by the current source.

## Existing packaging correction

The two near-optimality inequalities are already retained by
`QuittingStoppingLawCurvaturePaidWitness` and
`exists_quittingStoppingLawCurvaturePaidWitness` in
`StoppingLaw/Endpoint/NormalizedCurvatureStrategicDispatch.lean`.
Only `exists_eventually_paidFirstDisagreement` erases them in its weaker
wrapper.  A new provenance record may add the floor and literal orbit fields,
but it should reuse rather than duplicate this checked carrier.

The arbitrary anchored exact floor-orbit constructor also already exists as
`exists_quittingPunishmentFloorInfiniteOrbit_anchored` in
`Collision/Toggles/ChargedSoloBlockerRepayment.lean`.  The new part is its
literal-profile suffix packaging, conditional on an attained floor-safe
profile.

## Mark-reach boundary

Without a terminal witness or another strict-survival hypothesis, a selected
exact root may absorb surely.  The paid profile then remains a formal suffix
but is reached with probability zero from later prefixed profiles.  A theorem
calling the limit a "marked paid port" must therefore retain either:

1. the terminal-witness floor-root strict-survival theorem; or
2. an explicit positive prefix-survival field.

Summability alone does not exclude one early charge equal to one.

## Exact remaining mathematical item

To turn this conditional theorem into the requested paid-provenance producer,
prove one of the following from the actual low-level curvature-paid data:

1. the receiving prescribed payoff is floor-safe; or
2. a source-matched transformation produces a floor-safe attained profile
   while retaining a fixed paid mark; or
3. failure of the floor inequality yields a strict semantic debt/support-rank
   descent or directly enters the cumulative near-return consumer.

No such implication is supplied here.  It is the separate upstream adapter
still needed for the active paid question.  The contribution nevertheless
passes export as the complete answer to the independently named
`PaidRowExactPortAlternative`; it must not be described as the universal paid
producer.
