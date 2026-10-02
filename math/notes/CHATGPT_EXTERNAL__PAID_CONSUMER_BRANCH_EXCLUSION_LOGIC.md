# Paid near-return consumer as a branch-exclusion statement

Author: `CHATGPT_EXTERNAL`

Status: `SOURCE-CHECKED LOGICAL REDUCTION; INTERNAL; PRODUCER OPEN`

## Claim

Fix a finite quitting reward table `reward`.  The implication packaged by
`PaidFirstDisagreementAdmissiblePayoffNearReturnConsumer reward` should be read
as a branch-exclusion assertion, not as construction of an object that can
coexist with an instantiated positive-minimum frontier.

More precisely, a positive-minimum frontier and a positive admissible payoff
near-return family for the same reward table are incompatible.  Therefore the
consumer is equivalent to nonexistence of a frontier, mover, full-replacement
endpoint, observer, gain, and eventually paid rows satisfying its complete
antecedent.

This does not prove the consumer.  It identifies its exact logical content.

## Exact reduction

Let

```text
frontier : QuittingPositiveMinimumDebtTangentFamily reward.
```

The checked method
`frontier.hasPositiveMinimumTerminalSemanticDebt` gives a strictly positive
global minimum of total terminal semantic debt.  By
`not_exists_uniformEquilibriumPayoff_iff_hasPositiveMinimumTerminalSemanticDebt`,
this implies that the game has no uniform-equilibrium payoff.  The needed
nonempty-player instance follows from
`frontier.positiveDebtSupport_nonempty`.

On the other hand, every

```text
family : QuittingPositiveAdmissiblePayoffNearReturnFamily reward
```

produces a uniform-equilibrium payoff through
`family.exists_uniformEquilibriumPayoff`.  Consequently

\[
\boxed{
  \text{positive-minimum frontier}
  \;\Longrightarrow\;
  \neg\,\text{positive admissible payoff near-return family}.
}
\]

The proof is the direct contradiction between those two checked conclusions;
no additional game argument is needed.

Now unfold
`PaidFirstDisagreementAdmissiblePayoffNearReturnConsumer reward`.  It says that
every tuple

```text
(frontier, mover, endpoint, separated endpoint debt,
 observer, positive gain, eventually paid rows)
```

produces a nonempty near-return family.  Such a family contradicts the first
coordinate of the same tuple.  Hence:

\[
\boxed{
  \mathsf{PaidConsumer}(r)
  \iff
  \text{no tuple satisfies the consumer's complete paid-branch antecedent}.
}
\]

The reverse implication is vacuous implication.  The forward implication is
the positive-minimum/near-return contradiction above.

## Flat separated endpoints

For a mover whose tangent column is flat, together with a full-replacement
endpoint having strict debt separation, the checked curvature theorem
`FullReplacementCluster.exists_eventually_paidFirstDisagreement` supplies an
observer, a fixed positive gain, and eventually paid first-disagreement rows.
Flatness here is the separate hypothesis

```text
sum observer, frontier.tangent mover observer = 0;
```

it is not a field of `FullReplacementCluster`.
Therefore existence of such an endpoint inside an actual positive-minimum
frontier falsifies the paid consumer for that reward table.

Equivalently, proving the universal paid consumer excludes every such actual
paid branch.  Exhibiting a reward table with the full antecedent would already
exhibit positive minimum terminal semantic debt and hence nonexistence of a
uniform-equilibrium payoff.

## Methodological consequence

The open arrow remains

```text
paid first-disagreement branch
    -> fixed-charge exact floor-admissible payoff near-return.
```

But it is a reductio arrow.  A successful proof assumes the paid branch,
constructs the incompatible near-return family, and thereby eliminates the
branch.  Partial constructions must not be described as jointly realizable
with a genuine positive-minimum frontier after the full consumer has been
obtained.

This also explains why the fixed positive charge threshold cannot be dropped:
the checked all-behavior compiler uses that threshold to produce the uniform
payoff that contradicts positive minimum debt.

## Source correspondence

- `PaidFirstDisagreementAdmissiblePayoffNearReturnConsumer` is in
  `UniformEquilibrium/Diagnostics/Quitting/PaidFirstDisagreementPayoffNearReturn.lean`.
- `QuittingPositiveAdmissiblePayoffNearReturnFamily.exists_uniformEquilibriumPayoff`
  is in
  `UniformEquilibrium/Quitting/Projective/PunishmentFloorNearReturn.lean`.
- `QuittingPositiveMinimumDebtTangentFamily.hasPositiveMinimumTerminalSemanticDebt`
  is in
  `UniformEquilibrium/Diagnostics/Quitting/StoppingLaw/PositiveMinimumDebtTangentFamily.lean`.
- `not_exists_uniformEquilibriumPayoff_iff_hasPositiveMinimumTerminalSemanticDebt`
  is in
  `UniformEquilibrium/Quitting/Terminal/PositiveMinimumSemanticDebt.lean`.
- `FullReplacementCluster.exists_eventually_paidFirstDisagreement` supplies
  the paid-row antecedent for flat strictly separated endpoints.

The reduction was checked against these declarations.  It is ordinary
mathematical/process evidence here, not a claim that new Lean code was
compiled.

## Nonclaims

- No paid-branch exclusion is proved here.
- No genuine positive-minimum frontier is exhibited.
- No reward-table counterexample is obtained.
- The reduction does not turn a local selected-ray regression into a global
  refutation; `base_minimum` and the complete antecedent remain essential.
