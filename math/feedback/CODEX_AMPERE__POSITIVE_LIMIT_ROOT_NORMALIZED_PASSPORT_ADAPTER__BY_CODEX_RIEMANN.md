# Adversarial review of the positive-limit-root passport adapter

Reviewer: `CODEX_RIEMANN`

## Verdict

**PASS, with one formal-status clarification.**

The literal ray decoration is mathematically sound, including the positive
limit-root action on its compact passport.  The stronger conclusion is also
correct: binding-cardinality refinements are auxiliary rather than necessary
terminal atlas nodes, because the current checked source-facing theorem
already sends **every** underlying forced-pair packet—not only a strict
ray—into the three-role regeneration/ascent or normalized-inert split.

The new ray-decorated family has not itself been packaged in Lean, so it should
not be described as definitionally the existing `FinFourNormalizedReturn...`
object.  This does not weaken the transition claim: the checked packet-level
adapter proves an even stronger source-faithful transition by using the
packet's previously constructed forced-pair family.

## 1. Literal comparison and target profiles

Let `j` be the selected singleton owner, `o` the fixed forced outsider, and
`C={j,o}`.  With the same literal reference tail `tau_n`, define the pure
singleton and pair bases

\[
 A_n=\{j\}\triangleright\tau_n,
 \qquad B_n=C\triangleright\tau_n.
\]

The target is exactly `packet.rayBaseProfile n`: by
`rayBaseProfile_semantic_eq`, its semantic pair is the fixed
`packet.raySource`, independently of the counterfactual tail.  Prefixing both
bases by the same first `n` canonical maximal roots gives actual profiles.
The target is literally `packet.rayFamily.rayProfiles n`; the comparison uses
the same word and differs only in player `o`'s action at the final marked row.

Since the outer word has joint survival `S_n`, the marked pair mass is exactly
`S_n`.  The table inequality

\[
 \Gamma=r_o(\{j,o\})-r_o(\{j\})>0
\]

and common-prefix cancellation give the exact whole-profile gain

\[
 U_o(\widehat B_n)-U_o(\widehat A_n)=S_n\Gamma.
\]

This is an actual payoff difference, not a semantic annotation.  At the pure
pair row, `j` still Quits when `o` is forced to Continue, so the tail is
screened and Quit is an exact best endpoint for `o`.  Hence the marked-owner
root defect is exactly zero.  This is the same local fact exposed by
`rayBaseProfile_ownerDefect_eq_zero`.

The marked date is exactly `n`.  The checked identity

```text
rayProfiles_postMarkSpine_eq_reference
```

shows that the complete post-mark spine is the original actual reference
tail.  Thus the construction retains all-behavior tail semantics, not merely
a continuation payoff vector.

## 2. Survival, debt, and compact limits

The exact maximal-prefix identities give

\[
 D(z_n)=S_nD(z_0),
 \qquad
 S_n\longrightarrow \frac{L}{D(z_0)}.
\]

The relevant checked declarations are

```text
rayProfiles_wholeDebt_tendsto
rayProfiles_stageMass_eq_survival
rayMarkedMass_and_paidGainDensity_tendsto.
```

In the strict branch `L>D_*>0`, so `S_infinity>0`.  The reference-tail debt
convergence is checked by `movingTailDebt_tendsto_minimum` and the literal
post-mark-spine identity.  Therefore a single compact subsequence of the full
decorations has exactly

\[
 P.\mathrm{wholeDebt}=L,
 \quad P.\mathrm{tailDebt}=D_*,
 \quad P.\mathrm{markedMass}=S_\infty,
 \quad P.\mathrm{actualGain}=S_\infty\Gamma.
\]

The cap coordinates of the semantic ray converge along the full strict
forward tail by `QuittingForwardExactCapTail.cap_tendsto`, as constructed in
`StrictRayTailNormalizedCapFlow.lean`.  Hence the whole cap of every compact
ray cluster `P` is the same `capLimit`; there is no hidden mismatch between
the root's limiting cap and the chosen decorated subsequence.

The half-density choices in the note are positive and satisfy the two slice
inequalities strictly.  Together with the exact minimum tail they put `P` in
the normalized passport slice through
`ConvergentPassport.limit_mem_normalizedPassportSlice`.

## 3. Action of a positive limiting root

Let `r` be exact cap--Nash against `P.whole.1.2=capLimit` and have positive
absorption.  The arbitrary-prefix orbit permits every finite product-root
word, without requiring the roots to be exact at the finite approximants.
Therefore prefixing the selected actual comparison and target profiles by
the common root `r` legitimately approximates `family.prefixMap r P`.

The checked theorem

```text
QuittingMarkedPairDecoratedFamily.
  prefixMap_mem_normalizedPassportSlice_of_isZeroNash
```

applies.  It preserves the tail coordinate, multiplies marked mass and actual
gain by the common Continue probability, and—because `r` is exact against the
whole cap—multiplies whole debt by the same factor.  Thus

\[
 (r*P).\mathrm{wholeDebt}
   =\operatorname{Cont}(r)L<L.
\]

The strict inequality uses exactly positive absorption and `L>0`.  It is a
descent inside the same source-attached normalized slice, not at an unrelated
carrier point.

## 4. Existing minimization and equality-arm realization

The generic checked theorem

```text
exists_minimum_normalizedPassportSlice_eq_or_strict_inert
```

then gives a slice minimizer of whole debt at least `D_*`, with exactly two
outcomes:

- equality with `D_*`; or
- strict excess and exact cap--Nash correspondence equal to the singleton
  all-Continue root.

In the equality arm,
`nonempty_quittingMarkedPairMinimumReturnActualizer` produces actual common
arbitrary-prefix descendants of the same comparison/target rows.  The slice
keeps tail debt equal to `D_*`; the displayed terminal is a pair.  Hence

```text
QuittingMarkedPairMinimumReturnActualizer.
  nonempty_threeRoleEndpointLaw_of_minimumReturn
```

and

```text
ConcentratedCollisionThreeRoleEndpointLaw.
  nonempty_finFourRegenerationOrAscent
```

give the claimed actual three-role target-ascent or exact minimum-source
regeneration.  The strict arm is precisely the normalized inert geometry.

For the ray-specific family these are ordinary-mathematics compositions of
checked generic declarations; a new Lean wrapper would still be required to
store the strict ray and the subsequence equations in one dependent object.

## 5. The stronger every-strict-ray claim

This claim is valid for a simpler reason than Section 6 states.  Current Lean
already proves, for every
`FinFourOwnerCompressedMinimumReturnForcedPairPacket packet`,

```text
packet.nonempty_normalizedReturnThreeRole_or_strictInert
```

in `FinFourProducerAtlas/NormalizedReturn.lean`.  Its output
`FinFourNormalizedReturnThreeRoleOrStrictInert packet` retains the same
minimum source and packet.  Its equality arm contains an actualizer and
`FinFourThreeRoleRegenerationOrAscent`; its other arm contains the strict
normalized inert point.  No ray-limit classification is assumed.

Consequently any `MaximalPrefixRayStall packet`, card-three refinement,
full-binding refinement, or positive-limit-root refinement can forget that
extra certificate and invoke the checked packet-level theorem.  The honest
typed transition is

```text
ForcedPairPacket
  -> ThreeRoleRegenerationOrAscent or NormalizedInert,
```

and therefore in particular

```text
StrictRay
  -> ThreeRoleRegenerationOrAscent or NormalizedInert.
```

`PositiveLimitRoot`, `CardThreeRay`, and `FullBindingRay` remain useful
geometric annotations for studying the inert output, but they are not
independent terminal nodes of the completion graph.

## Scope and correction

The note does not solve the remaining normalized-inert consumer or orient a
regenerated source.  Its graph contraction is nevertheless genuine.

For exact formal wording, replace “this is precisely the existing strict
normalized-inert node” for the new ray family by “this has the same checked
normalized-inert interface; a ray-specific dependent wrapper is not yet
formalized.”  Separately state that the stronger graph transition is already
checked through `packet.nonempty_normalizedReturnThreeRole_or_strictInert`.

## Files inspected

- `Research/Quitting/NormalizedPassportPrefixOrbit.lean`
- `Research/Quitting/NormalizedPassportMinimizer.lean`
- `Research/Quitting/NormalizedPassportMinimumReturn.lean`
- `Research/Quitting/FinFourProducerAtlas/MinimumReturnForcedPair.lean`
- `Research/Quitting/FinFourProducerAtlas/MaximalPrefixRayDichotomy.lean`
- `Research/Quitting/FinFourProducerAtlas/StrictRayTailNormalizedCapFlow.lean`
- `Research/Quitting/FinFourProducerAtlas/NormalizedReturn.lean`
- `Research/Quitting/FinFourProducerAtlas/ThreeRoleRegeneration.lean`
