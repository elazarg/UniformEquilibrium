# Answer 172 extraction: exact tail, packet, and collision claims

## Subsequent production status

The four extracted leaf families have been promoted.  The formerly missing
product-law pair-union estimate is also now proved in
`../../MathUE/PMFProduct/CollisionMass.lean` and specialized to quitting windows in
`UniformEquilibrium/Quitting/AbsorptionPath/CollisionConcentration.lean`.
Refusal survival-reweighting remains unformalized; later sections describing
the pair-union bound as pending record the state at extraction time.

## Decision

The two answer drafts contain several useful lemmas, but their broad final
diagnosis must be narrowed.

The robust conclusions are:

1. a summable-hazard suffix has best-response value converging to the
   maximal positive solo reward, with an explicit `2 M` best-response error;
2. the exact Nash--Bellman annotations converge as a whole vector, dominate
   every solo reward, and positive limiting occupation pins support
   coordinates to their solo rewards;
3. phase and refusal defects fail different packet clauses; and
4. late collision mass is negligible after conditioning on absorption,
   provided the window has positive absorption mass.

It is **not** correct to say that funding is always the missing inequality.
In the refusal branch, support pinning and a positive refusal defect make
funding strict.  The remaining missing packet clause is then the punishment
floor (or the provenance needed to apply it).

No CP172-specific Lean probes remain.  The extracted claims point directly to
their maintained owners:

- suffix best-response: `UniformEquilibrium.Quitting.Terminal.TailCompression.SummableTailBestResponse`;
- collision concentration: `MathUE.Probability.WeightedCollisionConcentration`
  and `UniformEquilibrium.Quitting.AbsorptionPath.CollisionConcentration`;
- annotation convergence and support pinning:
  `UniformEquilibrium.Quitting.Cycles.PhantomBoundaryLimitGeometry`; and
- phase/refusal packet algebra:
  `UniformEquilibrium.Quitting.Classification.SingletonPacketDefectAlgebra`.

The former Research extraction file was a duplicate of the packet-algebra
owner and is not retained as a compatibility API.  All of these results reuse
the production Bellman, pure-time extremality, Never-cap coupling, survival,
and remaining-charge APIs.

## 1. Quantitative suffix best response

Let

```text
R = sum_t quittingRootAbsorptionMass(roots_t),
K_i = max(0, r_i({i})).
```

For a suffix with `R < 1`, the deleted-player survival probability is
positive and the literal all-behavior best-response value satisfies

```text
|BR_i - K_i| <= 2 M R.
```

This is machine-checked by the canonical theorem
`abs_quittingRootSequenceBestResponseValue_sub_maxSolo_le_totalCharge_of_lt_one`
in `UniformEquilibrium.Quitting.Terminal.TailCompression.SummableTailBestResponse`.

The proof does not re-prove behavioral extremality.  Production already says
that arbitrary behavior has the same supremum as deterministic quit times
plus Never, and that the entire best-response envelope is within

```text
2 M * (1 - deleted-player survival limit)
```

of the all-Continue cap.  The canonical owner also proves the explicit
bridge

```text
1 - deleted-player survival limit <= R.
```

The prescribed suffix payoff already obeys the production bound

```text
|U_i| <= M R.
```

Consequently, if exploitability is the maximum unilateral gain, then for all
sufficiently late suffixes

```text
K - 3 M R <= E(suffix) <= K + 3 M R,
K = max_i K_i,
```

and therefore `E(suffix) -> K`.  The constants `4` and `5` in
`172-Answer-CP.md` are valid conservative heuristics but are not sharp at the
level of the existing APIs.  The compiled best-response constant is `2`; the
additional prescribed-payoff error is `1`, giving `3` for exploitability.

The condition `R < 1` is not a substantive tail restriction: for a summable
nonnegative hazard sequence, remaining suffix sums converge to zero.

## 2. Annotation convergence and support pinning

For a bounded path satisfying the exact Bellman equations

```text
value_t = F(roots_t, value_(t+1))
```

and summable joint absorption, the whole annotation vector has a common
coordinatewise limit `z`.  Moreover, for every player and start time,

```text
|value_start(i) - z_i|
  <= 2 M * sum_offset q(roots_(start+offset)).
```

This is
`exists_quittingAnnotationBoundary_of_summableAbsorption` in
`UniformEquilibrium.Quitting.Cycles.PhantomBoundaryLimitGeometry`.  It packages
the production one-step and remaining-charge estimates; no Nash assumption is
needed for convergence itself.

Exact one-stage Nash adds the solo floor:

```text
r_i({i}) <= z_i.
```

This is `quittingSingletonReward_le_annotationBoundary`.  At each date, the
pure-Quit endpoint is within `2 M` times opponent absorption of `r_i({i})`,
exact Nash keeps that endpoint below the prescribed value, and opponent
absorption is bounded by the summable joint absorption clock.

If player `i` has positive own-Quit probability along a cofinal subsequence,
then

```text
z_i = r_i({i}).
```

The canonical owner proves this directly in
`quittingAnnotationBoundary_eq_singleton_of_activeSubsequence`.  It also
proves the abstract occupation form
`quittingAnnotationBoundary_eq_singleton_of_positiveOccupation`: a positive
limiting occupation coordinate pins the player whenever every positive late
occupation supplies a positive-hazard date beyond the same cutoff.

Thus any normalized occupation limit with the elementary
positive-coordinate-to-active-date property has

```text
support(lambda) subset {i | z_i = r_i({i})}.
```

What is not yet formalized is the concrete instantiation of that abstract
property for every canonical normalized window definition used in Question
172.  The Bellman and limit part is compiled; the remaining task is finite
sum/denominator bookkeeping.

## 3. Correct phase/refusal alternative

Fix a player with proper positive owner mass `0 < lambda_i < 1`, and suppose
support pinning gives

```text
z_i = r_i({i}).
```

Write `R_i` for its conditional refusal value and

```text
m_i = lambda_i z_i + (1-lambda_i) R_i.
```

The exact identity is

```text
R_i - m_i = lambda_i (R_i - z_i).
```

The two stabilized evaluator branches therefore have opposite geometry.

### Phase-stop branch

If

```text
z_i = r_i({i}) >= m_i + eta,
```

then the target is underfunded by at least `eta`:

```text
m_i + eta <= z_i.
```

### Refusal branch

If

```text
R_i >= m_i + eta,
eta > 0,
```

then

```text
z_i < R_i,
z_i < m_i.
```

Funding is recovered strictly.  If `|z_i|, |R_i| <= M`, then also

```text
eta <= 2 M lambda_i.
```

So a fixed positive refusal margin forces a nonvanishing owner share.

The canonical theorem
`phaseUnderfunded_or_refusalFloorMissing` in
`UniformEquilibrium.Quitting.Classification.SingletonPacketDefectAlgebra`
makes the logical remainder
precise.  Assuming the funded and floor clauses do not both hold:

```text
phase branch   -> m_i < z_i;
refusal branch -> z_i < m_i and not (chi_i <= z_i).
```

The final negated-floor conclusion requires the explicit premise that the
two packet clauses do not jointly hold.  One cannot infer punishment-floor
failure merely from a refusal defect.

Degenerate cases matter:

- `lambda_i = 0`: the identity gives `R_i = m_i`, so a positive refusal gap
  is impossible;
- `lambda_i = 1`: the conditional refusal denominator is zero, so `R_i` is
  undefined and the branch must be evaluated separately;
- no opponent hazard: the behavioral refusal payoff is zero, but there is no
  normalized conditional opponent lottery.

## 4. Collision concentration and periodic singleton approximation

For one product row let

```text
alpha_t = probability of at least one quitter,
collision_t = probability of at least two quitters.
```

The analytic pair-union estimate is

```text
collision_t
  <= sum_(i<j) p_(i,t) p_(j,t)
  <= choose(n,2) * alpha_t^2,
```

because each marginal Quit event is contained in the absorption event and
there are `choose(n,2)` unordered pairs.

This stagewise pair-union statement is maintained by
`MathUE.Probability.WeightedCollisionConcentration` and its quitting-window
consumer `UniformEquilibrium.Quitting.AbsorptionPath.CollisionConcentration`.
It is stated against the production coalition-mass API rather than a second
product-law model.

The finite-window propagation is compiled.  For arbitrary nonnegative
survival weights, if

```text
collision_t <= C * alpha_t^2,
alpha_t <= rho,
```

then `Math.Probability.finiteWeightedCollisionConcentration_or_zero` proves
exactly one of:

```text
A = 0 and collisionMass = 0,
```

or

```text
A > 0 and collisionMass / A <= C * rho,
```

where `A = sum_t survivalWeight_t * alpha_t`.  No division occurs in the
zero-absorption branch.

Taking `C = choose(n,2)` gives the claim in `172-Answer-GP.md`:

```text
conditional collision mass <= choose(n,2) * sup_t alpha_t.
```

For a periodically repeated nonempty word, `A > 0` is exactly the condition
that a pass has positive absorption probability; then repeated passes absorb
almost surely.  If `choose(n,2) * rho < 1`, singleton mass is positive and its
normalized owner occupation is defined.

The canonical MathUE algebra theorem
`Math.Probability.abs_conditionalPayoff_sub_singletonMixture_le` then gives the
explicit payoff estimate

```text
|periodic delivery_i - m_i(lambda)|
  <= 2 M * collisionMass / A
  <= 2 M * choose(n,2) * rho.
```

Here `lambda` is the normalized owner distribution of singleton terminal
events in that same pass.  This is an exact finite inequality, not Big-O.

The corresponding refusal statement must use the root word with player `i`
forced to Continue.  The same collision estimate applies to its deleted-word
singleton occupation whenever deleted-word absorption is positive.  However,
identifying that occupation with the original `lambda` conditioned off `i`
requires a further survival-reweighting estimate.  The commonly stated

```text
refusal_i = R_i(lambda) + O(M * lateWindowHazard)
```

is therefore **unformalized analytic Big-O** in this extraction.  It is valid
only after controlling the change in chronological survival weights caused
by deleting player `i`.

The denominator cases are:

- pass absorption `A = 0`: collision mass is zero, the periodic profile never
  absorbs, and normalized terminal occupation is undefined;
- `A > 0` but singleton mass `S = 0`: conditional delivery exists, but no
  singleton occupation exists; the late small-hazard bound excludes this if
  `choose(n,2) * rho < 1`;
- deleted-word absorption `A_- = 0`: refusal payoff is zero and conditional
  refusal occupation is undefined;
- `A_- > 0` but deleted singleton mass `S_- = 0`: refusal delivery exists but
  no singleton refusal mixture exists; again excluded by a sufficiently
  small deleted collision ratio.

## 5. Claims not extracted

The following claims remain unformalized or should not be promoted as stated:

- the universal assertion that the ghost packet is always missing funding;
- the refusal approximation to the *original* occupation conditioned off the
  refusing player, without a survival-reweighting estimate;
- any assertion that a periodic delivery converges to the annotation target
  `z` rather than to a singleton mixture;
- any conversion of the all-Continue phantom plateau into global finite
  punishment-floor charge capacity;
- the four-player return-map and positive fixed-point calculations in
  `172-Answer-GP.md`;
- all literature-status assertions in either answer draft; and
- the Big-O versions of periodic occupation/refusal approximation until their
  constants and denominator hypotheses are made explicit.

The phantom-boundary identities in `172-Answer-GP.md` were not duplicated:
the production `PhantomBoundaryRestart` module already contains the exact
Bellman boundary decomposition and remaining-charge estimates.

## 6. Promotion recommendations

Recommended after review:

1. **Suffix best-response bound.**  Promote the explicit `2 M * tailCharge`
   theorem near `ElementaryNeverCoupling`.  Before doing so, move the general
   theorem “opponent absorption is at most joint absorption” out of the
   diagnostics namespace into a core root/survival module.
2. **Full boundary convergence.**  Promote the simultaneous vector wrapper
   and explicit modulus near `PhantomBoundaryRestart`.
3. **Support pinning.**  Promote the active-subsequence theorem near
   `NashBellmanQuitEndpointLimit`.  Keep the abstract occupation wrapper
   experimental until a canonical window occupation discharges its premise.
4. **Phase/refusal algebra.**  Promote the small scalar lemmas to the packet
   module; they are table-independent and prevent the incorrect
   funding-only diagnosis.
5. **Collision concentration.**  Promote only after the stagewise
   `choose(n,2)` pair-union bound is proved using production coalition masses.
   The zero-denominator disjunction and the `2 M C/A` payoff lemma are already
   reusable exact statements.

The extraction report remains an experiment record; its Lean claims are owned
by the canonical modules listed above, and no CP172-specific Lean probe is
retained.
