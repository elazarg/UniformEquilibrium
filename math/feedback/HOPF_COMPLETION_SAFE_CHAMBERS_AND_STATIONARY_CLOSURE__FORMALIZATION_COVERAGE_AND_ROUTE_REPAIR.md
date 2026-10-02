# Formalization coverage and route repair for the HOPF completion packet

Formalizer: external Lean formalization agent
Target: [`HOPF_COMPLETION_SAFE_CHAMBERS_AND_STATIONARY_CLOSURE.md`](../exports/HOPF_COMPLETION_SAFE_CHAMBERS_AND_STATIONARY_CLOSURE.md)

Verdict: **Theorem A needed no new formalization; it was already covered.
Theorem B is checked, and two of its stated hypotheses turned out
unnecessary.  One step of the packet's proof of Theorem B is not
implementable under the project trust policy and was replaced by a different
route, which also makes two of the packet's own interval computations
redundant.  The simultaneity list at the special `R` is not refuted, but it is
not available as stated either: the `Regression` container that carries the
ray items cannot hold of a table with no pure terminal coalition.  Evidence
short of a checked statement points to the ray transporting to the sharp
table.  The export is not claimed as accepted until that is settled.**

## Theorem A was already covered

`Research/Quitting/HopfCompletionSafeChambers.lean` carries generic versions
of every part of Theorem A:

```text
singleton chamber, J_32 <= 0   QuittingPureSingletonChamber
pair chamber, (A2) and (A3)    QuittingPurePairChamber
induced mixed root with the
  all-Never tail               QuittingInducedOwnerNeverChamber.terminalNash
                               QuittingInducedOwnerNeverChamber.uniformEquilibriumPayoff
compactness alternative (A6)   exists_uniformPayoff_or_inducedOwnerNever_continue_sub_quit_pos_gap
```

Each is stated for an arbitrary finite player type and an arbitrary reward
table, and the last gives the uniform margin under positive global debt
exactly as in (A6).  The packet's Theorem A contribution is therefore
arithmetic instantiation of these at `Fin 4`.

The pure toggle inequalities that the packet's Lean handoff asks to be
proved are also already available unpacked, as
`isQuittingSureExitSet_singleton_iff` and `isQuittingSureExitSet_pair_iff`
(`UniformEquilibrium/Quitting/Paths/SureExitSet.lean`).  Both are
`omit`-scoped to need only `DecidableEq` on the player type, so they apply
without a finiteness hypothesis.

## Theorem B is checked, with two hypotheses removed

In `Research/Quitting/FinFourHopfConcreteChambers.lean`:

```text
sharpReward_exists_uniformEquilibriumPayoff :
  ∀ (R singletonLevel : ℝ), R ∈ Set.Icc 0 (1 / 37) →
    ∃ payoff,
      (quittingGame (sharpReward R singletonLevel)).IsUniformEquilibriumPayoff
        none payoff
```

with `rationalSharpReward_exists_uniformEquilibriumPayoff` the fixed rational
specialization at `R = 1/74` and singleton level `1`.  `#print axioms` on both
gives exactly `propext`, `Classical.choice`, and `Quot.sound`.  The (B16)
determinant is checked as `sharpPreconditionerMatrix_det` at the packet's
stated value, the (B21) step as `applySharpPreconditioner_injective`, and the
(B2)--(B10) to (B13) expansion as
`quittingFaceNumerator_sharpReward_eq_formula`.

Two hypotheses of (B1) are unnecessary:

- `R = 0` is admitted, where the packet requires `0 < R`; and
- there is no hypothesis at all on the singleton level, where the packet
  requires `s > 0`.

The second holds because the singleton level cancels from the face
numerators.  The packet itself observes this for `F_3`; it holds for all four
rows, and is checked as
`quittingFaceNumerator_sharpReward_independent_singletonLevel`.

## Route repair: (B17)--(B19) is not implementable, and is not needed

An earlier formalization attempt replaced the packet's mean-value scheme by
an exact coefficient-L1 scheme and left it as a hypothesis structure carrying
four rational identities.  Those four values are arithmetically correct; all
four were recomputed exactly.  They are nevertheless not dischargeable in the
Lean kernel.  The route runs through the dense coefficient reflector
`reflectedCoefficient` (`MathUE/Interval/RationalPolynomialL1.lean`), whose
multiplication branch recurses over `Finset.antidiagonal` at every product
node, branching once per monomial of the exponent box at each level of nested
products, and `native_decide` is outside the project trust policy.

The discharged route is instead a centered mean-value estimate from dyadic
interval automatic differentiation.
`abs_evalReal_le_of_centeredMeanValueNumerator_le`
(`MathUE/Interval/PolynomialLipschitz.lean`) takes one structural pass over
the factored expression tree for the value envelope at the base point and one
for the gradient row sums on the box, and reduces each whole-box bound to a
single scaled integer comparison.  No polynomial normalization is performed,
so the factored player-three row `R*(x0-x1)-x1` survives instead of being
expanded.  The table-side instance is
`abs_evalReal_sharpNormalizedDiagonalErrorPolynomial_le`.

`MathUE/Interval/RationalPolynomialL1.lean` is unchanged and correct:
`abs_evalReal_le_coefficientL1` and `boundedCoefficientL1_eq_coefficientL1`
remain generic finite checkers.  They are simply not on this table's route.

### Two consequences for the packet's own proof

Both are recorded because they simplify it.

- (B18) and (B19), the Jacobian and `∂_R` interval enclosures, are not needed
  on this route at all.  The centered estimate computes its gradient row sums
  from the syntax tree directly; it consumes no declared enclosure.
- Separately, the eight face signs of (B20) certify derivative-free, by
  centered monomial bounding in exact rational arithmetic, so (B18)--(B19)
  are not needed for that route either.

The packet's mean-value presentation is sound.  It is not the shortest path.

### Certificate constants

The certified box moved:

```text
packet (B14)  centre      (363/2000, 4359/20000, 5549/50000, 583/1250)
              half-width  (3/2000, 7/4000, 3/2000, 13/5000)
              face margin 1/1000

checked       centre      (1815, 2179, 1110, 4664)/10000
              half-width  1/400, uniform in the four coordinates
              face margin 1/4000
```

The packet's own box is too tight for a mean-value estimate, because its
centre is not accurate enough relative to its half-widths.  That is exactly
why the exact-L1 route was attractive there.

## New checked content beyond the packet

`Research/Quitting/FinFourSharpSureExitExclusion.lean`:

```text
not_isQuittingSureExitSet_sharpReward
isQuittingSureExitSet_sharpReward_empty_iff
not_isεAsymptoticNash_pureSetRoot_sharpReward
```

No subset of the four players at all — empty coalition and grand coalition
included — is a sure exit set of the sharp table, at every real `R` and every
positive singleton level.  Hence no pure set root is an exact terminal Nash
profile against the full behavioral deviation class; the second conclusion is
routed through `isεAsymptoticNash_pureSetRoot_iff_isQuittingSureExitSet`.
There is no constraint on `R`.

`isQuittingSureExitSet_sharpReward_empty_iff` shows the positive-level
hypothesis is sharp: the empty coalition is a sure exit set exactly when the
singleton level is nonpositive.

This is the packet's boundary test "no pure terminal-coalition equilibrium",
made checkable and proved uniformly in `R`.

## The simultaneity list: the container fails, not the claim

The packet asserts that at the special spectator value the sharp table
simultaneously carries seven properties, and its headline is that none of
them prevents a finite-scale full-support stationary equilibrium.  Four of
the seven hold of `sharpReward` and three are proved of other tables.  The
mathematics of the three does appear to transport; what blocks the packet's
statement is the structure the repository fences them with.

One of the four is checked — the absence of pure terminal coalitions —
together with the full-support stationary equilibrium the list is meant to
coexist with:

```text
full-support stationary equilibrium   sharpReward_exists_uniformEquilibriumPayoff
no pure terminal coalition            not_isQuittingSureExitSet_sharpReward
```

The three maximal-ray properties are proved for different reward tables:

```text
globally maximum, partial-current-support ballistic exact-cap ray
  fullBindingBallistic and rationalCardThree, for fullBindingReward
  and rationalReward
  (Research/Quitting/FinFourMaximalRayZeroMinimumRegressions.lean)

full binding at the limiting cap
  FullBindingBallistic.binding_eq, for fullBindingReward, in the same file

all-Continue as the unique exact cap root
  exactRoot_eq_allContinue, for that module's own local table at its pairCap
  (Research/Quitting/FinFourEventualAllContinueLocalRegression.lean)
```

`Research/Quitting/FinFourHopfConcreteChambers.lean` explicitly declines to
transport them, on the ground that `sharpReward` at the full-binding initial
cap and `fullBindingReward` differ on passive active-player entries.  Those
entries are real, and the evidence below indicates that the ray does not see
them.

### The `Regression` fencing excludes the no-coalition item

`Regression`
(`Research/Quitting/FinFourMaximalRayZeroMinimumRegressions.lean`) is the
structure that carries the ray, and both `RationalCardThree` and
`FullBindingBallistic` wrap it.  It has a field

```text
zero_solo : ∀ who, reward (quittingSingletonTerminal who) who = 0
```

and the same file proves, generically in `reward`,

```text
neverTerminalNash (regression : Regression reward) :
  (quittingGame reward).IsεAsymptoticNash (quittingTerminalPayoff reward) 0
    (quittingAlwaysContinueProfile reward)
```

through `isZeroAsymptoticNash_quittingAlwaysContinue_of_zeroSolo`
(`UniformEquilibrium/Quitting/Punishment/ZeroSoloDisjunct.lean`).  A table
carrying a `Regression` therefore has the always-Continue profile as an exact
terminal Nash profile, which is the empty coalition as a pure
terminal-coalition equilibrium.  "No subset is a sure exit set" and "carries
a `Regression`" are mutually exclusive, for every reward table, not only this
one.

The two conditions meet exactly on the sharp table.  Its solo vector is
`(0, 0, 0, singletonLevel)`, so `zero_solo` holds precisely when the singleton
level is zero — the boundary already recorded in
`isQuittingSureExitSet_sharpReward_empty_iff`.  The paid transition, the pair
defects, and the induced margin hold at every level, so the split is between
the remaining two:

```text
positive singleton level  no pure terminal coalition
zero singleton level      zero_solo, hence the Regression fencing
                          that carries the three ray items
```

The sharp table sits on one side or the other, never both.

The older tables visibly fail the no-coalition item as well.
`rationalReward_singleton_eq_zero` and `fullBindingReward_singleton_eq_zero`
give solo reward zero for every player, so by `isQuittingSureExitSet_empty_iff`
the empty coalition is a sure exit set for `rationalReward (1/100)` and for
`fullBindingReward R (1/100)` at every `R`.  The tables the ray is actually
built for already lack the property.

### The reading that survives

`QuittingForwardExactCapTail`
(`Research/Quitting/ForwardExactCapTailFlow.lean`) does not require zero solo.
Its only singleton field is

```text
singleton_le_capLimit : ∀ who,
  reward (quittingSingletonTerminal who) who ≤ capLimit who
```

so a bare maximal-cap ray at a positive singleton level is not excluded by the
argument above.  The exclusion is against the `Regression` fencing, which is
what carries the zero-minimum conclusions.  If the packet means the bare ray
it should say so, and the ray items then lose the conclusions that motivate
them.  Which of the two objects is intended is a question for the conference.

The unique-limiting-root item needs a decision of the same kind.  `Regression`
carries `limitRoot_exactNash` together with

```text
limitRoot_positive : 0 < ∑ who, quittingRootQuitRates limitRoot who
```

so for the tables where the ray is built there is an exact cap root at the
limiting cap with strictly positive total quit rate, and all-Continue is not
the unique exact root there.  Read as "the ray's roots converge to
all-Continue" the item is already proved, as `root_quit_tendsto_zero`.  Read
as uniqueness it contradicts a field of the structure carrying the ray.  This
report does not guess which is meant.

### Investigation-level evidence that the ray transports

Most of this subsection is investigation-level: exact rational verification at
sample points and one hand proof on a slice.  The limiting-root uniqueness
below is the exception — it is a complete argument, an exact finite computation
with no sampling anywhere in it.  None of this subsection, that computation
included, is checked in Lean.

The sharp cap flow is an exact level shift of the full-binding one.  Along the
ray player `3`'s hazard is identically zero.  Every coalition on which the
sharp and the older tables differ contains player `3`, so all of them carry
zero mass, and the place where the tables disagree is invisible to the ray.
In the shifted variable `d = c - singletonLevel` the sharp spectator recursion
is verbatim the full-binding one,

```text
d (time + 1) = activeRowSurvival time * d time - (activeData time).t
```

verified in exact rational arithmetic at nine parameter settings against
directly computed successor payoffs.  The active half transports as well: at
hazard `0` for player `3`, the sharp and rational successor payoffs and
endpoint differences agree at players `0`, `1`, and `2`.

The required spectator value is the same, and the singleton level cancels.
The sharp source cap is `rayCap rationalScale rationalScale (R + singletonLevel)`
and the orbit has to start at `singletonLevel + fullBindingSpectatorCap 0`, so
the condition is `R = fullBindingInitialCap` at every singleton level.
`fullBindingInitialCap_le` is checked and gives `fullBindingInitialCap ≤ 1/37`,
so that value lies inside the certified range of `sharpCenteredCertificate`.
One table would then carry both the stationary equilibrium and the ray.

Full binding comes out stronger.  The shifted `capLimit` is
`(0, 0, 0, singletonLevel)`, which equals the solo vector exactly, so the
binding set is everything, at every singleton level.  The full-binding table's
own version holds because both sides are zero.

The unique limiting root is settled, on both branches, by an exact finite
computation.  The shifted `capLimit` is `(0, 0, 0, singletonLevel)`, which is
the solo vector exactly, so every limiting cap gap vanishes.  Each player's
membership gain in the sharp table is additive over the opponent coalition —
checked on all twelve pairs and all twenty-eight nonempty coalitions — so the
endpoint difference at that cap collapses to a homogeneous linear form on the
whole cube,

```text
g_i(x) = ∑_{j ≠ i} J_ij * x_j ,        J_ij = r_i({i,j}) - r_i({j}),
```

whose four rows are exactly the `(1 - s_i)`-coefficients of
`quittingFaceNumerator_sharpReward_eq_formula`, row for row.  The collision
matrix is independent of `R` and of the singleton level.  Deciding the exact
roots at the limit is therefore a linear complementarity problem in a fixed
rational four-by-four matrix.  Enumerating all `3^4` activity patterns in exact
rational arithmetic — twenty-eight inconsistent, eight carrying a
positive-dimensional solution family, every one of them discharged by
Fourier--Motzkin elimination — leaves no nonzero solution.  All-Continue is the
unique exact-cap Nash root at the shifted cap limit, at every `R` and every
singleton level.

This replaces the grid scan; the `x3 > 0` branch no longer rests on sampling,
and the argument no longer needs a slice.  The entry that decides that branch
is `J_03 = sharpScale = 1/100`, the only positive entry in its column, which is
the same `x3/100` the scan was measuring.

The argument is now checked:
`GameTheory.FinFourSharpCapLimitRootUniqueness.eq_allContinueRoot_of_isNash`
(`Research/Quitting/FinFourSharpCapLimitRootUniqueness.lean`) proves that every
exact root against `![0, 0, 0, singletonLevel]` is all Continue, at every `R`
and every singleton level.  It is a `Research` declaration, so it carries no
axiom-audit record; `#print axioms` gives `propext`, `Classical.choice` and
`Quot.sound` only.  The item is false for the rational and full-binding tables,
which carry a positive limit root.

### `Regression` fails for a second, independent reason

`Regression` requires `limitRoot_positive` as well as `zero_solo`.  If
all-Continue is the only exact-cap Nash root at the shifted cap limit, the
sharp table fails that field at every singleton level.  Unlike the `zero_solo`
obstruction, no choice of parameter repairs this one.  That conclusion now
rests on the enumeration above, not on a scan, and is checked as
`GameTheory.FinFourSharpCapLimitRootUniqueness.not_sum_quittingRootQuitRates_pos`
(`Research/Quitting/FinFourSharpCapLimitRootUniqueness.lean`), which is the
shape a `limitRoot_positive` field would have to satisfy.

`Regression` was built around tables that have zero solos and a positive limit
root.  The sharp table has neither, and the bare `QuittingForwardExactCapTail`
demands neither.  The container is what fails.

### Three items are true of the sharp table

The remaining three items were previously unrecorded.  All are computed in
exact rational arithmetic and are parameter-free: every number below holds at
every real `R` and every real singleton level.

- Paid transition `{3} -> {0,3}`, as `LocalForcedPairFragment` fields with
  singleton owner `3`, marked owner `0`, and payer `1`: marked gain `1/100`,
  payer gain `1`, marked pair debt `0`.  The payer gain is `1` here, against
  `1/100` for both older tables.
- Pair-defect vector at `{0,3}`: `(0, 1, 1/100, 1)`.  It is zero at player
  `0` and positive and distinct at players `1` and `2`, as the packet asserts.
  Both older tables give `(0, 1/100, 1/100, 1)`, positive but equal, so the
  distinctness holds of the sharp table and fails for them.  This is a
  concrete sense in which the sharp completion is not redundant, and nothing
  in the repository currently states it.
- Induced margin: `quittingInducedOwnerNeverExcess` at owner `2` equals
  `r_2({3}) - r_2({2,3}) = 39/100 > 0`, so owner `2` strictly prefers
  Continue and is unsafe as a persistent base by exactly `39/100`, at every
  free set containing player `3`.

The first two are being formalized now and are not yet checked.  The induced
margin is not being formalized: pinning the induced Nash carrier to a single
point needs an iterated-strict-dominance step, so "uniform" is not yet a
checked word for it.

That margin also cannot be recovered from the checked compact alternatives.
Both `exists_uniformPayoff_or_singletonBase_pos_gap` and the (A6) form
`exists_uniformPayoff_or_inducedOwnerNever_continue_sub_quit_pos_gap` are
disjunctions whose left branch is the existence of a uniform-equilibrium
payoff.  That branch is unconditionally true for the sharp table on the
certified range, so each disjunction is satisfied on the left and says
nothing about any gap.

### What the conference has to decide

The packet's simultaneity is not refuted.  What the repository establishes is
narrower: the ray items as fenced by `Regression` cannot hold of a table with
no pure terminal coalition.  The evidence above points the other way on the
mathematics — the ray transporting to the sharp table at every singleton
level, at a required spectator value that a checked theorem places inside the
certified range.  The headline does not need weakening.

What is missing is a checked statement, and one identified lemma blocks it.
The existing maximality route runs through `spectator_endpointDifference_neg`,
which is false for the sharp table: at hazards `(0, 0, 1, ·)` the sharp
spectator endpoint difference is `+1`.  A sharp analogue can hold only on the
region `x2 <= x0 + x1 + d*S`, so the maximality step needs an argument
confined to the actual cap values in place of the universally quantified one.

Two things would settle the matter: that maximality argument, and a restatement
of the ray items against `QuittingForwardExactCapTail` in place of
`Regression`.  The complementary branch of the uniqueness claim, listed here
before, is decided above and is no longer among them.

None of this touches Theorem B, which stands as checked above.

## Packet citations

The packet's source correspondence was checked.  Every cited declaration
resolves:

```text
quittingTerminalSemanticDebt_pureSetRoot_eq
isεAsymptoticNash_pureSetRoot_iff_forall_mem_notMem
  UniformEquilibrium/Quitting/Paths/SureExitSet.lean

nonempty_quittingSingletonBaseCertificate_of_inducedNash
exists_uniformPayoff_or_singletonBase_pos_gap
  UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PersistentBaseConcreteGap.lean

exists_cube_zero_interior_of_strict_opposite_face_signs
  MathUE/Topology/PoincareMirandaCube.lean

quittingFaceNumerator
  UniformEquilibrium/Quitting/Stationary/FaceNumerator.lean

quittingConditionalFaceGapStationaryCertificateOfFaceNumeratorZero
  UniformEquilibrium/Quitting/Classification/Existence/ConditionalFaceGap.lean
```

## Seals

The sharp table has `M` and `L`, with a checked unconditional consumer and no
adapter from arbitrary source data.  The consumer is
`sharpReward_exists_uniformEquilibriumPayoff`, for the table's own stationary
payoff on `0 <= R <= 1/37`.  The export packet itself remains at most `M`.
