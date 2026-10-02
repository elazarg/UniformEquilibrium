# AGKRS prioritized attachment-spine contraction

## Status

**Independently reviewed PASS; internal, no export proposed.**  The
infinite source-spine arm of a prioritized positive-absorption attachment
strictly decreases, at the same tolerance and on the same reward table, to the
positive-singleton-defect arm.  The only surviving attachment endpoint is a
finite reached sure-exit row whose displayed continuation is strictly below a
punishment floor in some coordinate.

This is a genuine one-step source-type decrease, not a consumer for the whole
prioritized residual.  It does not consume the all-Continue source arm or the
positive-singleton-defect arm.  It also does not turn the finite sure-exit
endpoint into S.2: the rational value is the *current* reached payoff, whereas
the checked sure-row compiler needs punishment rationality of the displayed
continuation.

Independent review:
[`CODEX_RAMSEY__AGKRS_PRIORITIZED_ATTACHMENT_SPINE_CONTRACTION__BY_CODEX_EULER.md`](../feedback/CODEX_RAMSEY__AGKRS_PRIORITIZED_ATTACHMENT_SPINE_CONTRACTION__BY_CODEX_EULER.md).
The reviewer PASSed the conditional-rationality limit, Bellman orientation,
same-scale contraction, unique-owner localization, and coalition expansion.
The notation repair distinguishing a simplex state from its decoded product
root is incorporated below.

## Question

Let `delta>0` and let

```text
R : QuittingPrioritizedRefinedSourceResidualAt reward delta
```

whose corrected residual is the positive-absorption sharp-attachment arm.
Can the literal reached-row extension of that attachment produce a classified
AGKRS branch or a well-founded source reduction, rather than another
unprioritized case split?

The answer is yes on the infinite extension: it contracts to the existing
positive-singleton-defect arm at the *same* `delta`.  The finite extension
stops at one exact and explicit punishment-floor deficit.

## Checked sources inspected

- `UniformEquilibrium/Quitting/Classification/Existence/
  PrioritizedRefinedSourceBoundary.lean`
  - `QuittingPrioritizedRefinedSourceResidualAt`
- `UniformEquilibrium/Quitting/Classification/Existence/
  PositiveRhoLandingClassificationBoundary.lean`
  - `QuittingLowSurvivalPositiveAbsorptionSharpAttachmentResidual`
  - `QuittingSupportBellmanPositiveSingletonDefectResidual`
  - `QuittingSupportBellmanPositiveSurvivalBoundary.stationary_or_defect`
- `UniformEquilibrium/Quitting/Classification/SimonFiniteOrbit/
  PositiveRhoLandingCompactLimit.lean`
  - `QuittingLowSurvivalPositiveRhoReachedRowLimit`
  - `QuittingLowSurvivalPositiveRhoInfiniteExactSpine`
  - `finiteSureExitAttachment_or_exists_infiniteExactSpine`
  - `QuittingLowSurvivalFirstCrossingSourceAt.actualTail_rational`
- `UniformEquilibrium/Quitting/Classification/SimonFiniteOrbit/
  CompactSpineSurvivalBoundary.lean`
  - `quittingWellSupportedAbsorbingSequenceAt_or_exists_positiveSurvivalBoundary`
- `UniformEquilibrium/Quitting/Classification/SimonFiniteOrbit/
  CompactQuantitativeAlternatives.lean`
  - `exists_oneStagePunishedProfile_of_rational_support_sureQuitter`
- `UniformEquilibrium/Quitting/Classification/Existence/
  WellSupportedAbsorbingSequence.lean`
  - monotonicity and pointwise/global branch definitions
- `UniformEquilibrium/Quitting/Cycles/PhantomBoundaryRestart.lean` and
  `UniformEquilibrium/Quitting/Projective/Lasso.lean`
  - the exact normalized restart seam; see the no-shortcut audit below.

The older obstruction audit is
[`CODEX_EULER__AGKRS_PRIORITIZED_REFINED_SOURCE_CLOSURE_AUDIT.md`](CODEX_EULER__AGKRS_PRIORITIZED_REFINED_SOURCE_CLOSURE_AUDIT.md).
The present argument does not contradict it: it uses the later checked
iterable reached-row interface and contracts only one of its two outcomes.

## 1. Every uniformly reached limiting row has a rational current value

### Lemma 1 (reached-current punishment rationality)

Let

```text
row : QuittingLowSurvivalPositiveRhoReachedRowLimit base.
```

Then

```text
QuittingSimonRationalPayoffAt reward 0 row.currentValue.
```

### Proof

For the `n`th literal source selected by `row.subsequence`, put

```text
t_n = source.crossingStage + row.offset,
s_n = quittingJointSurvivalWeight source.roots 0 t_n.
```

The field `row.reached` gives one fixed `r>0` with `r<s_n` for every `n`.
Restarting `source.sourceNash` at `t_n` therefore gives an unrestricted
root-sequence Nash inequality at conditional error

```text
e_n = source.accuracy / s_n.
```

This is the same argument as
`QuittingLowSurvivalFirstCrossingSourceAt.actualTail_rational`, with
`crossingStage` replaced by `crossingStage+row.offset`.  The source accuracy
tends to zero along the nested cofinal subsequence and `s_n>=r`, hence
`e_n -> 0`.  For every player `i`, the punishment lower bound at the restarted
profile reads

```text
P_i - e_n <= TailVector(source.roots,t_n)_i.
```

The right side tends to `row.currentValue i` by
`row.currentValue_tendsto`.  Passing to the limit gives
`P_i<=row.currentValue i`.

This proof uses arbitrary behavioral deviations through the shifted
root-sequence Nash theorem.  It is not stationary rationality.

## 2. An infinite reached spine contracts at the prioritized scale

### Proposition 2 (infinite-spine semantic contraction)

Assume the player type is nonempty.  Let `delta>0`, let

```text
spine : QuittingLowSurvivalPositiveRhoInfiniteExactSpine seed,
```

and assume

```text
notStationary : not (QuittingStationary-epsilon-EquilibriumAt reward delta),
notWellSupported : not (QuittingWellSupportedAbsorbingSequenceAt reward delta).
```

Then

```text
Nonempty
  (QuittingSupportBellmanPositiveSingletonDefectResidual reward delta).
```

### Proof

Write

```text
V_n = (spine.row n).currentValue,
s_n = (spine.row n).root,
q_n = quittingRootOfSimplex s_n.
```

The orientation is the literal chronological Bellman orientation

```text
V_n = Succ(V_(n+1),q_n).
```

Indeed `spine.edge n` is

```text
IsQuittingNashBellmanEdge reward
  ((V_n,s_n),(V_(n+1),s_(n+1))).
```

Thus its first field is the displayed recursion and its second field is exact
endpoint Nash for `q_n` against `V_(n+1)`.  Exact endpoint Nash implies
zero-error support-local Nash.  The carrier fields on each reached row give
`|V_n(i)|<=quittingRewardBound reward`.

Apply
`quittingWellSupportedAbsorbingSequenceAt_or_exists_positiveSurvivalBoundary`
to `(V,q)` at tolerance `delta` (monotonicity raises zero support error to
`delta`).  The first output contradicts `notWellSupported`.  Hence obtain

```text
boundary : QuittingSupportBellmanPositiveSurvivalBoundary reward delta.
```

Apply `boundary.stationary_or_defect`.  Its stationary output is the global
stationary existence branch, which in particular supplies a stationary
`delta`-equilibrium and contradicts `notStationary`.  The other output is
exactly the claimed positive-singleton-defect residual.

No B/U identification is used.  `V_n` are Bellman annotations in backward
chronology.  The checked compact-spine semantic split is precisely what
decides whether they are actual suffix payoffs or retain a positive-survival
phantom boundary.

## 3. Strict arm decrease for a prioritized attachment

Give the three corrected residual arms the local ranks

```text
positive-absorption attachment : 1,
positive-singleton defect      : 0.
```

No rank is assigned here to the all-Continue positive-rho source arm; the
rank is only the well-founded two-element subsystem proved below.

### Theorem 3 (attachment descent or terminal floor deficit)

Suppose `R` is prioritized at `delta>0` and its residual witness is

```text
attachment :
  QuittingLowSurvivalPositiveAbsorptionSharpAttachmentResidual reward (1/2).
```

Then one of the following holds.

1. There is another
   `QuittingPrioritizedRefinedSourceResidualAt reward delta` with the *same
   four priority negations* and whose corrected residual is specifically the
   positive-singleton-defect arm.  This strictly decreases the arm rank
   `1 -> 0` at the same scale and table.
2. There is a finitely reached row `terminal` with
   - a sure quitter in `terminal.root`;
   - exact Nash--Bellman edge
     `terminal.currentValue = Succ(terminal.nextValue,terminal.root)`;
   - exact punishment rationality of `terminal.currentValue`; and
   - a strict displayed-continuation floor deficit

     ```text
     exists i, terminal.nextValue i < quittingPunishmentValue reward i.
     ```

### Proof

Apply
`attachment.consecutive.finiteSureExitAttachment_or_exists_infiniteExactSpine`.

- On the infinite-spine arm, Proposition 2 applies using
  `R.not_stationary` and `R.not_wellSupported`.  Insert the resulting defect
  into the third disjunct of
  `QuittingCorrectedPointwiseRefinedSourceResidualAt` and reuse
  `R.not_stationary`, `R.not_instant`, `R.not_wellSupported`, and
  `R.not_generated` verbatim.  This is the rank-`0` prioritized residual.

- On the finite arm, Lemma 1 gives exact rationality of
  `terminal.currentValue`; `terminal.exactEdge` gives the displayed exact
  edge.  If `terminal.nextValue` were also rational at error zero, then its
  exact endpoint Nash could be weakened to arbitrary positive tolerances and
  `exists_oneStagePunishedProfile_of_rational_support_sureQuitter` would give
  the global instant-punishment branch.  In particular it would give the
  pointwise branch at `delta`, contradicting `R.not_instant`.  Therefore
  `terminal.nextValue` is not rational at zero, which unfolds to the strict
  floor deficit above.

The relation path in the finite attachment is used only to identify the
terminal as a finite literal source extension.  No claim is made that the
intermediate nested subsequential rows form one executable profile.

## 4. The finite deficit localizes to a unique sure owner

The preceding finite alternative has a sharper exact normal form.

### Proposition 4 (unique-sure-owner floor deficit)

Under `R.not_instant`, choose any sure quitter `k` in the terminal root.  Then

1. `k` is the unique sure quitter;
2. every opponent has strictly positive Continue probability, so their joint
   Continue mass is positive; and
3. the deficient coordinate may be chosen to be `k`:

   ```text
   terminal.nextValue k < quittingPunishmentValue reward k.
   ```

### Proof

Only player `i`'s own tail coordinate enters player `i`'s endpoint difference.
If the root has a sure quitter `j != i`, absorption occurs regardless of
`i`'s action, so that coefficient is zero: changing `nextValue i` does not
change player `i`'s Quit or Continue endpoint.  It does not change any other
player's endpoint because payoff coordinates are separate.

Consequently, if there are at least two sure quitters, every coordinate has a
sure opponent.  Replacing the entire displayed tail by its coordinatewise
punishment-floor clip preserves exact support.  The clipped tail is rational
at error zero, so the checked sure-row compiler gives global S.2, contrary to
`R.not_instant`.  Thus `k` is unique.  Finiteness then makes every opponent's
Continue probability strictly positive and hence makes their product
positive.

With `k` unique, the same argument clips every coordinate `i != k` for free.
If `nextValue k` were already at least its punishment floor, this partial clip
would be fully rational and would again compile to S.2.  Therefore the unique
sure owner's own continuation coordinate is strictly below its punishment
floor.

This is stronger than the existential deficit in Theorem 3.  It is still not
an instant profile: when `k` deviates to Continue, the positive probability
that some opponent quits can couple a favorable opponent-only terminal reward
with the raised punishment continuation.

### Corollary 5 (finite pure coalition obstruction)

Let `mu(S)` be the product probability that exactly the opponent coalition
`S` quits in the terminal root.  With `k` the unique sure owner, the failure
of the floor-clipped root to be exact support-Nash is precisely

```text
sum_{S nonempty} mu(S) * r_k(S)
  + mu(empty) * P_k
  >
sum_S mu(S) * r_k(S union {k}).
```

Hence at least one of the following strict scalar obstructions holds:

```text
P_k > r_k({k}),
```

or there is a nonempty opponent coalition `S` in the product support with

```text
r_k(S) > r_k(S union {k}).
```

Indeed subtract the two endpoint expectations.  The empty-coalition summand
is `mu(empty)*(P_k-r_k({k}))`; every nonempty summand is
`mu(S)*(r_k(S)-r_k(S union {k}))`.  Their sum is positive, so one supported
summand is positive.  This turns the terminal continuation deficit into a
literal floor-above-solo or owner-leave passport.  It does **not** source-match
that pure coalition event to another Nash--Bellman row.

## 5. Why the finite floor deficit is real

Current-value rationality cannot replace continuation rationality in the
sure-row compiler.  At the scalar level, let player `0` be the unique sure
quitter, let player `1` quit with probability `1/2`, and arrange player `0`'s
payoffs so that

```text
r_0({0}) = r_0({0,1}) = 0,
r_0({1}) = 2,
terminal continuation T_0 = -2,
punishment floor P_0 = 0.
```

The prescribed sure-root current payoff is `0`, hence is floor-rational.
If player `0` Continues against the displayed continuation, its payoff is
`(1/2)2+(1/2)(-2)=0`, so the endpoint inequality is exact.  Replacing the
continuation by even the floor value `0` raises that Continue payoff to `1`.
Thus the punished one-stage splice need not be Nash.  The missing datum is
exactly rationality of the displayed tail (or an equivalent weighted
opponent-absorption bound), not rationality of the realized sure-exit row.

This is a local interface regression, not a complete game in the prioritized
hard branch.

## 6. No periodic-shortcut claim

Convergence of Bellman annotations does not by itself close a late finite
window.  The checked identity

```text
restartDelivery - farEndpoint
  = endpointDrift / absorbedMass
```

shows that the endpoint drift must be small *relative to the block's absorbed
mass*.  Summability and absolute endpoint convergence do not imply that
normalized estimate.  The present proof avoids this error by invoking the
checked exhaustive support--Bellman semantic split on the whole infinite
spine.

## 7. Scope and next question

The positive-absorption attachment's infinite extension is no longer an
independent prioritized obligation: it either gives S.3/S.1 before priority,
or strictly descends to the positive-singleton-defect arm after priority.

The remaining attachment question is now exact and finite:

> Can a finitely reached exact sure-exit row with rational current payoff but
> a unique-sure-owner floor-above-solo/owner-leave passport be converted to
> S.2/S.3, or be shown to regenerate a lower-rank source?

The all-Continue positive-rho source arm and the rank-`0`
positive-singleton-defect arm remain untouched.  This note does not close
`QuittingPrioritizedRefinedSourceResidualAt`.  The independent review PASSed
the mathematics but recommends retaining it internally until one of those
two remaining outputs receives a classified consumer.
