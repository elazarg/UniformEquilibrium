# Cross-face semantic-gap and paired-completion review

Reviewer: `CODEX_GAUSS`

Reviewed note:
[`../notes/CODEX_NOETHER__QUIT_TIME_COMPACTIFICATION.md`](../notes/CODEX_NOETHER__QUIT_TIME_COMPACTIFICATION.md)

Scope: Section 58, Propositions 56--57.  I independently reconstructed the
three cross-face semantic failures and the exact two-phase nonexistence proof
for `stationaryCompletionReward`.  This review is ordinary mathematics, not
Lean-checked, and it makes no universal source-matched-block or export claim.

## Verdict

**Propositions 56 and 57 are VALID ordinary mathematics.**  I found no
normalization, collision-law, reached-tail, endpoint-sign, or compact-box
counterexample.  The conclusions are scoped correctly: Proposition 56 kills
three direct static decoders, and Proposition 57 kills only the alternating
cross-pair support with four interior hazards for one completion.  Neither
result excludes longer, boundary, joint-support, or vanishing-defect blocks.

## 1. Static cross-face data do not supply a continuous direction

The artificial right-hand side is negative on `P` and zero off `P`.  A full
standard-LCP solution must put positive mass outside `P`, or its restriction
would solve the prohibited principal problem.  This algebra says nothing
about the actual reached boundary gap.  If that gap has zero set exactly `P`,
the checked field
`NonnegativeBoundaryDirection.supported_on_zero` forbids every positive
outside weight.  Thus `(N1)` is not a support-compatible continuous tangent;
no sign or orientation is reversed in this comparison.

## 2. Product-row and ordered-singleton failures

For `(N2)`, `Z=2`, so textbook-to-projective normalization gives

```text
c=1/3,
a=(1/9,2/9,1/9,2/9).
```

A product row with `c>0` and two positive singleton atoms necessarily gives
their pair coalition positive mass, so it cannot realize a packet supported
only on cemetery and singletons.  Matching singleton/cemetery odds gives

```text
p=(1/4,2/5,1/4,2/5),
c_product=81/400,
singleton mass=162/400,
multi mass=157/400.
```

These values recompute exactly.

For a collision-free ordered realization, the conditional hazard `(N6)`
does realize every displayed singleton mass and the final cemetery mass.  If
the first owner has mass `a_i`, the whole-packet pinning equation makes that
owner's reached tail equal its solo.  For the second owner `j`, direct
removal of the first singleton term gives

```text
tail_j-s_j = a_i(s_j-R^i_j)/(1-a_i).
```

Every off-diagonal entry of the paired matrix is nonzero, hence no choice of
first and second owners makes this vanish.  This proves failure of every
one-pass singleton ordering, not failure of recurrent or simultaneous-owner
implementation.

## 3. Exact two-phase equations for the `-2` completion

At the odd phase, mixer indifference gives

```text
x_0=-2v, y_0=-v/(1-v),
x_2=-2u, y_2=-u/(1-u),
```

and the even phase gives the analogous formulas for players `1,3`.  Substituting
these into the four inactive Bellman coordinates yields `(N12)`.  An inactive
deviator gets zero when the active pair both continue and `-2` otherwise, so
endpoint Nash is exactly `(N13)` with the displayed inequality orientation.

Let `T=max{u,v,a,b}`.  The matching inactive inequality implies

```text
T/(1-T) <= 2(2T-T^2),
T <= (3-sqrt(3))/2 < 3/4.
```

The equation belonging to the maximal hazard has the form `(N15)`.  Since
`3-4x>0`, it gives `T/(1-T)<2D`, while endpoint Nash gives
`T/(1-T)<=2(1-D)`.  Therefore `T<1/2`.  All strict inequalities use the
interior assumption in `(N10)` exactly where required.

Subtracting the paired equations gives `(N18)`.  On `(0,1/2)`,

```text
-1 < g_e'(t) < 4.
```

If the two coordinate differences have the same nonzero sign, the two MVT
identities imply each absolute difference is strictly smaller than the
other.  If their signs are opposite, they imply the mutually impossible
factor-four inequalities.  A zero difference forces both zero.  Hence
`a=b=r` and `u=v=s`.

The symmetric reduction `(N21)` is also exact.  When `r=s`, it gives
`1=2r^2(1-r)`, impossible since `r^2(1-r)<=4/27`.  Otherwise `(N22)` gives
`r+s-rs=1/2`; substituting

```text
s=(1-2r)/(2(1-r))
```

into the first cleared equation produces the strictly positive quantity
`6r(1-r)(1-2r)`, contradicting the equation.  This completes the interior
two-phase exclusion.

## 4. Surviving universal obligation

The Solan--Vieille completion of the same singleton matrix has the checked
period-two block, while the constant-`-2` completion lacks the same interior
support pattern and separately has a pure terminal equilibrium.  Hence
singleton standard-Q/cross-face data alone cannot choose the semantic block.
Any universal producer must use actual nonsingleton rows and may dispatch to
an already solved instant or stationarily generated branch.  The remaining
reviewable target is correctly normalized by total absorption: absolute
block defect can vanish trivially as all hazards vanish, so a useful source
theorem needs defect `o(A)` or an exact returned block.
