Historical design record. Frozen source/review artifact; see Research/Pending/README.md.

# Exact midpoint third-derivative integral identity: draft 44

Status: frozen UNCOMPILED/UNAPPLIED draft, not a checked Lean theorem here.
Both exports were reread fully. The frozen 01–43 inventory and calculus owners
were inspected; all prior draft bytes remain unchanged. No shared edits,
Lean/Lake, Git, children, caches, worktrees, options, or inventory edits.

## Exact obligation and reuse

The reflection packet proof 4 and Lean handoff item 4 print an exact integral
identity in addition to its third-derivative lower bound. Frozen 05/06 already
prove the sharp quantitative bound and actual directional derivative using
Lagrange remainders, but deliberately omit this identity. No second bound,
directional chain rule, minimum, Hessian, or game adapter is introduced here.

Canonical Mathlib `taylor_integral_remainder` already owns integral Taylor/FTC
and integration by parts. This patch only specializes its two half-interval
remainders, connects within derivatives to ordinary derivatives at every
closed-segment point, and performs the packet algebra. It does not duplicate
an integration-by-parts or Taylor foundation.

To avoid copying 05's Taylor expansion, the first hunk exposes its existing
`Math.taylorWithinEval_two_eq` by removing only `private`. Its proof is untouched.
This changes the visibility of the original helper, not any frozen patch file.
Root must apply the original 05 before applying 44; 05 is not yet present in
the current checkout. The narrow update hunk matches its frozen declaration.

The new `MathUE.Analysis.MidpointThirdDerivativeIntegral` proves both literal
half identities, then the displayed midpoint identity with kernel
`(1 - |time - 1|)^2` and actual `iteratedDeriv 3`. Its weighted kernel is
nonnegative and has exact mass one sixth. The simple quadratic integral used
only for that mass is canonical FTC applied to a cubic primitive.

All hypotheses are C3 at EVERY point of [0,2], including both endpoints. They
are supplied by the source's open-neighborhood regularity; no global C3,
favorable endpoint/slope, global potential, minimizer, or spectral premise is
added. This is a reusable generic calculus identity in MathUE with no game
imports. The reflected-segment bound and game-facing consumer remain 05/06.

## Exact dependency/check order

1. Original frozen 05 MathUE.Analysis.MidpointThirdDerivative and its imports.
2. Apply 44's visibility hunk, silently recheck that module.
3. Apply 44's new module and silently check
   MathUE.Analysis.MidpointThirdDerivativeIntegral.
4. Optional separate informational AXIOM_HARNESS.lean.
5. Root alone wires appropriate umbrellas, regenerates the exhaustive axiom
   inventory, runs lexical/import/docs/telescope/duplicate checks and the final
   serialized integration gate when appropriate.

No compilation or repository audit ran here. Pinned Taylor integral remainder,
within-derivative equality, closed-interval unique differentiability, interval
concatenation/congruence/scalar linearity, continuity, and FTC signatures were
read. Ordinary elaboration risks are honest: simplification of the factorial
and scalar remainder, conditional within-derivative rewriting in interval
congruence, and cubic primitive normalization. No source mathematics gap was
identified. Non-import Lean lines have been statically checked ≤100 columns.

The printed coupled-polynomial/Hessian and boundary fixtures remain separate
next obligations; this handoff makes no claim that those are completed.
