# Gate review of the repaired cardinal-two exclusion

Reviewer: `CODEX_CARDTWO_GATE`

Target:
[`FIN4_STRICT_MAXIMAL_RAY_CARDINAL_THREE_BINDING_REDUCTION.md`](../exports/FIN4_STRICT_MAXIMAL_RAY_CARDINAL_THREE_BINDING_REDUCTION.md)

Additional proof under review:
[`FIN4_BINDING_PAIR_EXPLICIT_MOD_TWO_LOCAL_COUNT.md`](../../FIN4_BINDING_PAIR_EXPLICIT_MOD_TWO_LOCAL_COUNT.md)

## Verdict

**PASS at the ordinary-mathematics level after the stated repair and proof
replacement.**  The solo-probe argument repairs the missing collision signs,
and the same-resolution cubical-Sperner computation proves the cardinal-two
exclusion without a component-index theorem, a perturbation homotopy,
regularity theory, or subdivision invariance.

The current export text itself is not yet the repaired final document.  It
still asserts the two collision signs without proof and presents the heavier
signed component-index route.  It should be revised before it is treated as
the gated packet.  I did not edit it.

I find no remaining unproved *mathematical* lemma in the cardinal-two
exclusion.  What remains is source-specific Lean assembly: construct the
Bernoulli box bridge, permute the binding pair to the two trailing
coordinates, choose the late finite cap and nested neighborhoods, and feed the
already checked generic local-count theorems to the same-resolution parity
consumer.

The conclusion is deliberately narrow.  It excludes a two-coordinate binding
face only for the strict maximum-absorption ray under uniqueness of all
Continue at the limiting cap.  Source-facing, it yields only

```text
positive-absorption exact root at the limiting cap
or full binding
or binding cardinality three.
```

It does not consume any of those three outputs.

## Claim checked

Let `q_k` be maximum-absorption exact roots against finite caps `b_k` in a
four-player strict ray.  Assume their absorption is positive and tends to
zero, `b_k -> bBar`, and all Continue is the unique exact root against
`bBar`.  Let

```text
A = {i : bBar_i = r_i({i})}.
```

Then `A.card != 2`.  Since the binding face is nonempty and cannot have
cardinality one, a proper binding face has cardinality three.

## 1. The solo probe supplies the missing signs

For distinct players define

```text
delta_i(k) = b_k,i - r_i({i}),
J_ij       = r_i({i,j}) - r_i({j}).
```

If `A = {i,j}`, then both limiting defects vanish.  Probe the limiting cap by
letting only `j` Quit with a sufficiently small probability `t > 0`.

- Player `j` is indifferent because its limiting defect is zero.
- Player `i`, who is at the Continue boundary, has endpoint difference
  `t J_ij`.
- Every outsider strictly prefers Continue for all sufficiently small `t`,
  because its limiting defect is strictly positive.

Thus `J_ij <= 0` would make the probe a positive-absorption exact root at the
limiting cap, contradicting uniqueness of all Continue.  Therefore

```text
J_ij > 0 and J_ji > 0.
```

This is not a new unsupported step.  The stronger finite-player sign theorem
is checked as
`QuittingForwardExactCapTail.quittingSingletonCollisionGain_pos_of_bindingFinset_card_eq_two`
in `Research/Quitting/BindingCollisionGainPositivity.lean`.  Its underlying
solo-probe producer is
`exists_quittingSingletonCollisionGain_pos_of_unique_allContinue`.

In the both-positive support case, the finite-cap indifference equations then
force both finite defects to be strictly positive.  In a solo support case,
the solo player's finite defect is zero while its incoming collision
coefficient remains strictly positive.  These are exactly the two sign
patterns needed below.

## 2. Maximality localizes the complete finite-cap solution set

Choose a small cube `R` around the origin on which, at every sufficiently late
finite cap, both outsiders have strictly negative endpoint difference and no
coordinate is at the upper face.  This follows uniformly from their strict
limiting Continue margins, convergence `b_k -> bBar`, and continuity of the
finite endpoint-difference polynomials.

Choose a smaller relatively open cube `V` with closure and a one-mesh
thickening contained in `R`.  At a sufficiently late time `k`, the selected
root has absorption below the radius of `V`.  If `x` is any exact root against
`b_k`, finite-cap maximality gives

```text
Abs(x) <= Abs(q_k).
```

For every coordinate, `x_i <= Abs(x)`.  Hence **every** exact root against
`b_k` lies in `V`.  This is localization of the whole finite-cap Nash set,
not just of the selected root.

The required maximality is the checked theorem
`quittingMaximalCapSemanticRoot_maximal` in
`Research/Quitting/MaximalCapSemanticPrefixOrbit.lean`.  Cap convergence,
summable absorption, and eventual support on the binding face are fields or
consequences of `QuittingForwardExactCapTail` in
`Research/Quitting/ForwardExactCapTailFlow.lean`.

For sufficiently fine mesh, every vertex of a grid simplex whose label-four
anchor is in `V` lies in `R`.  Therefore all such simplices see the outsiders
as strict Continue coordinates.  Permuting the four coordinates so that the
outsiders are `0,1` and the binding pair is `2,3` is harmless: the root problem,
solution set, and the symmetric cubes `R,V` are carried bijectively.

## 3. The same-resolution local count

The reduced Sperner label is the least violating coordinate, with label four
when none violates.  In `R`, every vertex with label at least two must have
coordinates zero and one equal to zero.  Consequently, in any complete
four-dimensional Kuhn simplex counted in `V`:

- its first three chain vertices lie on that two-dimensional face and carry
  labels `2,3,4`;
- coordinate one is raised next and carries label `1`;
- coordinate zero is raised last and carries label `0`; and
- the two binding coordinates are raised in the first two steps.

This position theorem is checked as
`boxComplementarityFaceChainPosition_of_mem` in
`Research/Topology/BoxComplementarityFaceSimplexPosition.lean`.

### Both binding hazards positive

The face gains are exact affine functions with positive defects and positive
cross terms.  Put the sign-change grid bounds at the ceilings of the two
positive thresholds.  Once both bounds are at least two, there are exactly two
complete chains with anchor in `V`:

1. the origin chain, with labels `4,3,2,1,0`; and
2. the chain based one grid step below both sign changes, with labels
   `2,3,4,1,0`.

No tie convention is missing: the violations use strict negativity, and the
ceiling converts the strict real threshold exactly to an integer inequality.
The two anchors lie in `V` for fine mesh because the finite selected root is
already in the smaller localization cube.

The exhaustive enumeration and count are checked as
`boxComplementarityLocalCompleteSimplices_card_eq_two_of_sharpFace` and
`boxComplementarityLocalCompleteSimplexParity_eq_zero_of_sharpFace` in
`Research/Topology/BoxComplementarityFaceLocalCountTwo.lean`.

### Exactly one binding hazard positive

Suppose coordinate two is the solo mixer.  Exact mixing gives
`delta_2(k)=0`; on the binding face its gain is therefore

```text
g_2(x) = x_3 J_23 >= 0.
```

The coordinate is below the upper face throughout `R`, so label two is
unattainable.  No complete simplex is counted.  The other solo orientation is
symmetric.  This removes the old perturbation homotopy entirely.

The generic statements are checked as
`boxComplementarityLocalCompleteSimplexParity_eq_zero_of_soloTwo` and
`boxComplementarityLocalCompleteSimplexParity_eq_zero_of_soloThree` in
`Research/Topology/BoxComplementarityFaceLocalCountZero.lean`.

In both support patterns the local parity in `V` is eventually zero.

## 4. The contradiction uses one problem at one resolution

For the fixed finite-cap box problem, `V` is open and contains the complete
solution set.  Therefore the checked localization theorem
`BoxComplementarityProblem.eventually_localCompleteSimplexParity_eq_one`
forces the local count in `V` to be one modulo two at every sufficiently fine
resolution.  This contradicts the eventual zero calculation above at one
common sufficiently fine resolution.

The direct consumer is
`BoxComplementarityProblem.not_eventually_localCompleteSimplexParity_eq_zero`
in `Research/Topology/BoxComplementaritySpernerEventualLocalParity.lean`.
Global parity one comes from the checked cubical-Sperner specialization
`boxComplementarityLocalCompleteSimplexParity_univ`.

There is no comparison between two mesh sizes, no homotopy of games, and no
component-index sign.  The same-resolution construction is why no general
`ModTwoBoxComplementarityParitySpec` inhabitant is needed.

## 5. Exact remaining formalization boundary

The difficult finite combinatorics and the solo-probe sign lemma are already
checked independently and their focused Lean builds pass.  The remaining
source adapter must:

1. construct the Bernoulli `QuittingEndpointNashBoxBridge` at a selected
   finite cap;
2. transport the problem through a permutation placing the binding pair at
   coordinates `2,3`;
3. choose the late finite time and nested cubes `V` and `R` with the uniform
   outsider margin;
4. establish the exact affine face formulas from the quitting endpoint
   expansion;
5. split the nonempty selected support into the both-positive and solo cases;
6. invoke the checked count-two or count-zero theorem; and
7. use same-resolution eventual parity to derive `A.card != 2`.

These are real Lean obligations, but I find no concealed mathematical
producer, compactness theorem, or topological invariant still missing from
the cardinal-two argument.

## Export correction required

The current export should not retain the sentence

> Both `J`-entries are nonnegative.

without the solo-probe proof.  It should replace the signed component-index
sections by the finite-cap same-resolution computation above, or explicitly
present the latter as the proof selected for formalization.  Its source-facing
split and its nonclaims are otherwise correct.

## Files inspected

- `exports/FIN4_STRICT_MAXIMAL_RAY_CARDINAL_THREE_BINDING_REDUCTION.md`
- `FIN4_BINDING_PAIR_EXPLICIT_MOD_TWO_LOCAL_COUNT.md`
- `Research/Quitting/BindingCollisionGainPositivity.lean`
- `Research/Quitting/ForwardExactCapTailFlow.lean`
- `Research/Quitting/FinFourProducerAtlas/StrictRayTailNormalizedCapFlow.lean`
- `Research/Quitting/FinFourProducerAtlas/StrictRayBindingCardinality.lean`
- `Research/Quitting/Root/EndpointNashBoxComplementarity.lean`
- `Research/Topology/BoxComplementarityCubicalSperner.lean`
- `Research/Topology/BoxComplementaritySpernerApproximation.lean`
- `Research/Topology/BoxComplementaritySpernerLocalCount.lean`
- `Research/Topology/BoxComplementaritySpernerEventualLocalParity.lean`
- `Research/Topology/BoxComplementarityFaceSimplexPosition.lean`
- `Research/Topology/BoxComplementarityFaceLocalCountZero.lean`
- `Research/Topology/BoxComplementarityFaceLocalCountTwo.lean`

Focused builds of the last three generic face/sign modules completed without
errors during this audit.  This build evidence does not certify the still
missing source adapter.

## Post-repair export audit

I re-read the rewritten final export against the proof above.

The theorem statement, solo-probe formulas, finite/limit separation,
maximum-absorption localization, support-pattern split, explicit counts, and
source-facing trichotomy are transcribed correctly.  In particular:

- the probing player's comparison is correctly `-barDelta_j`, without the
  erroneous factor `1-t`;
- the two strict collision signs are proved at the limiting cap and only the
  fixed reward-table constants are transported to the finite cap;
- the both-positive and solo local counts are performed for one fixed late
  finite-cap problem and compared at one common sufficiently fine mesh; and
- the text no longer claims an abstract parity-spec inhabitant or general
  component-index theorem is required.

One scope sentence still needs correction.  Under **Cardinality-three and
full-binding survival**, the checked zero-minimum regressions do realize those
binding cardinalities, but each regression also carries a positive-absorption
exact root at its limiting cap.  They therefore do not show that cardinality
three or full binding survives inside the *unique-all-Continue* arm.  The
sentence

> Consequently neither remaining binding pattern can be eliminated from local
> root geometry alone

is stronger than those regressions establish unless it is explicitly limited
to the unrestricted source-facing classification.  A correct replacement is:

> These regressions also have a positive-absorption limiting root, so they do
> not witness the unique-all-Continue subbranch.  They show only that binding
> cardinality by itself cannot remove either label from the unrestricted
> source-facing trichotomy.

There is also a harmless quantifier shorthand in Section 1: `V` should have
closure contained in `R`, after which the `1/p` thickening of `V` lies in `R`
for every sufficiently fine mesh.  The later text uses exactly this order, so
this is not a mathematical defect, but that wording would be clearer than
choosing a mesh-dependent "one-mesh thickening" before `p` is fixed.

**Final gate verdict: HOLD for the single regression-scope correction above.**
After that local edit, PASS; I found no other transcription error or overclaim.

Post-correction confirmation: both the regression-scope qualification and the
mesh-thickening quantifier order now appear exactly as requested. **Final
verdict: PASS.**
