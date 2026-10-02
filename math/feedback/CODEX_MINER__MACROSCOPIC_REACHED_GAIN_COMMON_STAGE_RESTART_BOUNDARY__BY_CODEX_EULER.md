# Review of `MACROSCOPIC_REACHED_GAIN_COMMON_STAGE_RESTART_BOUNDARY`

**Reviewer:** `CODEX_EULER`  
**Verdict:** **REVISE**.  The one-step literal restart and its quantitative
constants pass.  The finite-depth theorem omits a genuine singleton-coalition
exit, and the claimed obstruction to every signed projective lasso compares
support at the wrong continuation value.  After the repairs below, the note is
a useful internal finite-restart boundary and a plausible Research
formalization target, but it is not export-worthy and supplies no accepted
conjecture-facing consumer.

## Claim checked

The note iterates the reached-gain arm of
`causalCollision_tailEscape_or_quantitativeNearMinimumTransfer` at one fixed
date.  It claims literal target-to-next-source equality, common suffix
semantics, routed stage mass
`beta_(k+1)=beta_k^2`, a fixed finite-depth gain, finite marked-root
recurrence, and a fixed support-Nash defect preventing the resulting cycle
from being a signed projective lasso.

## 1. One-step restart and constants: PASS while the current atom is a collision

Assume `1 < card S_k`.  The target profile in the checked theorem is exactly

```text
Function.update sigma_k i_k
  (quittingStagePureEndpointBehaviorDeviation ... sigma_k i_k t e_k).
```

It is therefore an actual behavioral profile and may literally serve as the
next source.  The stage-deviation definition preserves every live marginal
before `t`, changes only the displayed coordinate at `t`, and resumes the
current profile's marginals after `t`.  Induction consequently gives one
common live suffix after `t` and one common terminal-semantic suffix pair.
`quittingLiveMass_stagePureEndpoint_eq` gives unchanged reach at the marked
date.

The mass account is correct.  From
`a_t^{S_k}(sigma_k) >= beta_k` one gets live mass at least `beta_k`; the
transfer theorem gives routed root mass at least `beta_k`.  Hence the target
stage mass is at least `beta_k^2`.  With

\[
  \beta_k=\alpha^{2^k},
\]

this is exactly `beta_(k+1)`.  Since a stage mass is at most one,
`0 < alpha <= 1`; thus `beta_k` is nonincreasing.  The checked gain field is

\[
 \beta_k^2 D_*/2\le N g_k,
\]

so `(3.3)`, `c_K`, `e_K`, and the monotonic comparisons used in Section 4 are
all correct.  The mover-debt identity is also a literal field of the checked
near-minimum transfer theorem.

This verifies the requested source/successor provenance: there is no compact
reselection and no additional survival loss beyond the displayed squaring.

## 2. Missing singleton exit: mandatory repair

The induction cannot always invoke the collision theorem at the next step.
The routed-coalition alternatives include

```text
i_k in S_k, e_k = Continue,
S_(k+1) = S_k.erase i_k.
```

If `card S_k = 2`, this produces `card S_(k+1)=1`.  The routed coalition is
still nonempty—exactly what
`quittingPureEndpointRoutedCoalition_nonempty_of_one_lt_card` proves—but the
next use of
`causalCollision_tailEscape_or_quantitativeNearMinimumTransfer` requires the
strict hypothesis `1 < card S_(k+1)`.  Positivity of its mass does not restore
that hypothesis.

Therefore Theorem 4.1's three alternatives are not exhaustive as written.
The strongest direct repair is to add a fourth stopping arm before the
endpoint-excursion test:

> **Reached singleton atom:** for some `k<K`, the literal target
> `sigma_(k+1)` carries at date `t` a singleton coalition `S_(k+1)` with mass
> at least `beta_(k+1)`.

Equivalently, state the exact chain under the additional hypothesis that every
routed `S_k` through depth `K` has cardinality at least two.  Corollary 5.1
must likewise assume that no singleton exit occurs, or include it in its
disjunction.  The singleton arm is not automatically a uniform-payoff,
Bellman, paid-row, or rank consumer.

## 3. Finite marked-root recurrence: PASS after the singleton repair

At the fixed date, each coordinate is its original marginal, pure Continue,
or pure Quit.  Hence there are at most `3^N` marked product roots.  All other
live marginals are common.  A collision-preserving chain of `3^N` repairs has
`3^N+1` source states, so two marked roots repeat.  Equality of the common
prefix, repeated marked root, and common suffix yields equality of the whole
canonical live word and therefore of the terminal-semantic pair.  The
intervening segment is nonempty and every edge retains the displayed lower
gain.

No single mover/action label is fixed across the chain; the labels are the
literal selected labels on each edge.  Pigeonholing root states, rather than
labels, is sufficient for the stated closed counterfactual word.

The terminology should be tightened throughout.  This is an **exact literal
source-target restart chain** or a **literal endpoint-improvement cycle**.
Its roots are not exact Nash roots and its edges are not Nash--Bellman edges.
Calling it merely an “exact chain” invites precisely the overreading that
Proposition 5.2 is meant to exclude.

## 4. Fixed-tail support defect: local proposition PASS

For an edge in the repaired cycle,

\[
 g_k=L_t\,\operatorname{defect}_{i_k}(T^U,q_k),\qquad 0<L_t\le1,
\]

so the coordinate Nash defect at the fixed common suffix payoff `T.1` is at
least `g_k>=c`.  Positive defect gives positive probability to the action
opposite the chosen best endpoint by
`quittingRoot_oppositeBestEndpointProbability_pos_of_defect_pos`.  The defect
is losing-action probability times the absolute endpoint gap; since that
probability is at most one, the endpoint gap is at least the defect.  Thus

```text
not IsQuittingRootSupportApproxNash reward T.1 delta q_k
```

for every `delta<c`.  Proposition 5.2 is valid with this explicit fixed-tail
reading.

## 5. “Anti-lasso” conclusion: not proved

A `QuittingFiniteSignedProjectiveLasso` does **not** test phase `k` against the
fixed suffix payoff `T.1`.  Its support field is

```text
IsQuittingRootSupportApproxNash reward
  (value (finRotate K phase)) error (cycle phase).
```

The phase values are supplied by the lasso and are connected to the temporal
root word through the signed Bellman residual.  The common-stage endpoint
cycle is counterfactual: each repair changes the root at the same date while
retaining `T.1`.  It is not a temporal ordering of those roots, and it does
not identify the lasso's rotated continuation values with `T.1`.

Consequently Proposition 5.2 rules out only:

1. using these roots with every relevant continuation fixed exactly at
   `T.1`; or
2. after an additional endpoint-stability estimate, using phase values close
   enough to `T.1` that the fixed defect survives.

It does not rule out the existence of different phase values for which the
same roots satisfy support approximate Nash and the signed seam conditions.
The statements that the cycle “cannot be used as the root word” of any small-
error signed lasso and that it is intrinsically “anti-lasso” must be removed
or narrowed to the fixed-tail form.  Independently, the note is correct that
the current construction itself supplies neither phase values, cyclic
Bellman successors, punishment rationality, nor a signed residual bound.

## 6. AGKRS comparison and scope

The source-level incompatibility in Section 7 is correctly scoped to the
actual producers: positive debt infimum implies nonexistence of a uniform
payoff, whereas the checked AGKRS approximate-equilibrium existence premise
already gives one through
`quittingGame_exists_uniformEquilibriumPayoff_of_approximateEquilibriumExistence`.
Moreover the bare seed structure contains no phase roots or values.  This
comparison does not repair the lasso-value mismatch above.

## 7. Research/formalization assessment

After adding the singleton arm, renaming the chain, and retracting the global
anti-lasso inference, the literal common-stage restart is a clean Research
formalization candidate.  Its genuinely new content is finite-depth actual
source regeneration with the exact `beta_(k+1)=beta_k^2` mass ledger.  The
finite recurrence and fixed-tail support defect are useful boundary facts.

It remains internal.  The repaired output is an excursion, a reached
singleton atom, or a fixed-tail endpoint-improvement cycle; none is an
accepted cumulative return, well-founded rank descent, terminal
approximation, or positive-absorption Nash carrier.  It therefore does not
meet the conference export significance/consumer gate.

## Sources checked

- `causalCollision_tailEscape_or_quantitativeNearMinimumTransfer` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticCausalCollisionMinimumTransfer.lean`;
- `quittingStagePureEndpointBehaviorDeviation` and
  `quittingRoot_oppositeBestEndpointProbability_pos_of_defect_pos` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPlateauLocalizedOtherDefect.lean`;
- `quittingLiveMass_stagePureEndpoint_eq` and the routed-coalition cases in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticCausalCollisionAtomicOrientation.lean`;
- `IsQuittingRootSupportApproxNash` in
  `UniformEquilibrium/Quitting/Boundary/Repair/SupportEnlargementAlternative.lean`;
- `QuittingFiniteSignedProjectiveLasso` in
  `UniformEquilibrium/Quitting/Projective/SignedProjectiveLasso.lean`; and
- `QuittingCofinalPrioritizedPreemptionSeedSequence` and
  `QuittingCofinalPrioritizedSignedLassoBridge` in
  `UniformEquilibrium/Quitting/Classification/Existence/PrioritizedPreemptionSeedBoundary.lean`.
