Historical design record. Frozen source/review artifact; see Research/Pending/README.md.

# Rational rejection and exhaustive search: frozen draft 36–43

Status: static draft, NOT compiled, NOT applied, NOT integrated, and no axiom
output checked. Root alone owns checkout edits, compiler calls, integration,
and Git. No Lean/Lake, Git, shared edits, caches, worktrees, or children were
used for this unit. Frozen Hessian patches 31–35 remain untouched.

## Source and reuse

Both source exports were read fully. This unit covers Theorem 4 / proof 8 of
`QUITTING_POTENTIAL_SHAPE_EXCLUSIONS.md` and item 5 / proof 7 of
`REFLECTION_AND_MULTIAFFINE_POTENTIAL_EXCLUSIONS.md`.

Canonical owners inspected and reused:

- `RationalCubeGrid`: existing endpoint-preserving finite grid density; no
  copied rounding proof. Patch 36 adds only the needed literal arbitrary-index
  closed-box/zero-width-face interface using Mathlib product density and clipping.
- `RationalApproximateQuittingRoot`: existing rational approximate Nash at a
  fixed tail. It does not preserve an independently strict violating edge or
  absorption-relative regret, so 39 uses joint source/root continuity instead.
- `RationalFiniteWordSemantics`, `RationalReward`, and
  `RationalQuittingRootGridSelector`: actual reward/root/expected-payoff/regret
  rational cast interfaces; no duplicated product-game semantics.
- `NashDefectContinuity`, `ComplementarityClosed`, and `BoundedEndpoint`:
  joint continuity, exact successor, endpoint bounds, and zero-absorption
  identity via the existing displacement estimate.
- `CollisionAdjustedSingletonProbe`, `FullExactRootPotentialFaceDrift`, and
  `MathUE.Analysis.CollisionAdjustedDrift`: frozen-upper collision repair,
  exact source Nash, actual absorption equal to rate, actual affine successor,
  and canonical difference-quotient limit. No Nash proof is repeated.
- `RationalFiniteSourceCapThresholdScan`: existing executable solo root and
  probability/actual PMF identities.
- `RationalPolynomial`: syntax and actual real evaluation. Its normalized
  polynomial/evaluation interface is noncomputable; 37 adds a five-constructor
  exact rational syntax interpreter, proved equal to the SAME actual evaluation.
- Mathlib `Rat.Encodable`, finite-function encodings, `List.find?`, product
  dense ranges, and relative-neighborhood density; no custom coding system.

## Dependency and application order

Every patch adds one module; no inventory/umbrella/audit/shared-doc edit is
included. Apply/check each named module silently before the next consumer.

| Patch | New module | Required earlier future patches |
| --- | --- | --- |
| 36 | MathUE.Interval.RationalClosedBoxDensity | none |
| 37 | MathUE.Interval.RationalPolynomialRationalEvaluation | none |
| 38 | UniformEquilibrium.Quitting.Root.RationalBoxedEdge | 36 |
| 39 | UniformEquilibrium.Quitting.Projective.RationalRobustRejectionDensity | 38 |
| 40 | UniformEquilibrium.Quitting.Projective.ExcludedPolynomialRationalRejection | 04, 09, 12, 39 |
| 41 | UniformEquilibrium.Quitting.Projective.RationalPotentialRejectionSearch | 37, 40 |
| 42 | UniformEquilibrium.Quitting.Projective.RationalExactSoloRejection | 12, 25, 38 |
| 43 | UniformEquilibrium.Quitting.Projective.RationalExactSoloRejectionSearch | 41, 42 |

Patch 25 has its original 18–23/source dependencies; do not replace it with
the matrix-free full-root exclusion. The exact-solo branch may be checked
after 38 without waiting for 39–41; only its search join 43 needs 41.

After module checks and the draft axiom harness, root may wire narrow umbrella
imports, regenerate the exhaustive axiom audit, run trust/import/duplicate/
telescope/docs checks, and run the required serialized full gate. Those checks
have NOT been run here. Harness informational output is expected only in the
separate audit invocation, not in clean production module checks.

## Literal theorem and quantifier map

36 permits arbitrary index types and zero-width rational intervals. No
interior-point assumption or perturbed owner coordinate is hidden in density.

39 is a reusable continuity helper with an explicit real strict positive
exact rejecting edge. It produces the whole rational pair internally, keeps
both endpoints in the SAME rational closed box, uses the literal exact
successor (residual zero), and makes every ordinary SOURCE-based coordinate
regret STRICTLY less than tolerance times its actual positive absorption.
It does NOT claim rational exact Nash. The complete game producer 40 does
not take that favorable edge as an input: it obtains it from the actual
quadratic OR multi-affine exclusion and rules out zero absorption using the
canonical bounded displacement estimate.

40 retains n≥2, rational reward bound one, nonnegative own-singleton values,
the actual supplied rational expression, normalized totalDegree≤2 OR all
normalized degreeOf≤1, and a supplied positive rational tolerance. It produces
rational source/root/exact successor on the literal radius-three box. Neither
no-UE, standard Q, a minimizer, nor a favorable strategy is an extra premise.
The proof works for every positive tolerance; the packet's positive tolerance
≤1/4 is included without needing its upper bound.

41's finite-budget list decodes ALL natural codes ≤budget, not a chosen dense
subsequence. Every rational source/probability pair belongs for every budget
at least its canonical code. Its Boolean test uses exact rational arithmetic:
both endpoint boxes, valid probabilities, positive absorption, ordinary source
regret ≤tolerance·absorption, and actual potential drop <absorption. An accepted
pair produces a literal `IsQuittingFloorFreeRobustEdge`, positive charge, and
rejection for the same expression. The complete excluded-polynomial theorem
internally invokes 40 and eventually succeeds at every budget beyond a finite
threshold. There is NO computable uniform bound on that threshold claimed.

42 retains rational reward/M, actual textbook standard Q, and quasiconvexity
of the SAME actual rational polynomial on C=[singletons,M+1]. It internally
produces an offending lower face using the face-only S2 exclusion, approximates
on a rational closed face with owner coordinate FIXED (zero width), keeps drift
<1/2, and chooses a rational positive rate from the two actual neighborhoods.
Only that owner quits; the root is EXACT source Nash; absorption equals the
positive rate; actual rational potential drop is <3·rate/4. Both endpoints lie
in K=[−(M+2),M+2]. The existing frozen-upper probe actually keeps endpoints in
the smaller M+1 box, a valid strengthening of the packet's larger-K probe.
No rational Q/LCP witness, minimizer, or root is supplied. The theorem uses
nonempty indices; it includes the packet n≥2 class and does not assert any
standard-Q one-player example.

43 feeds that SAME exact solo witness to the exact test at radius M+2 and
EVERY supplied positive rational tolerance; exact source regret is zero and
3·rate/4<rate. No second polynomial/table/root selection is made.

All these are candidate rejection, not a UE strategy, a refutation of a reward
table, a denominator bound, tolerance lower bound, or complete decision
procedure. The exact-Nash and approximate-Nash producers remain separate.

## Static checks and expected compiler attention

All patch payload non-import Lean lines are at most 100 characters. A lexical
scan found no forbidden trust construct (a prose occurrence of “admits” is
not a declaration). No repository trust scan, compiler check, axiom audit,
or generated-document check was run on unapplied patches.

Pinned signatures were inspected for denseRange/relative neighborhoods,
Bernoulli PMF/simplex maps, cast interfaces, canonical probe limits, finite
encodings, and list search. Ordinary elaboration uncertainties remain honest:
closed-box subtype reductions; rewriting cast root interpretations after
unfolding; simplification of the actual rational successor versus its raw
Boolean-game formula; and exact field/cast simplification in probe transport.
No source mathematics gap was identified by this author. Independent static
review and root compilation are still required.

## Frozen patch SHA256

```text
36 b1c004e87b1ec88898acd12089d2ad598bf860b130fded45bf334986c74b1f12
37 9e27afc420d3c9645a6bb050d11ef071cd7bcbe650a8b621eb7d2552c85edaf3
38 6215031453395edaaa47bf3f296605658c90db8f06c80288b88b1f44fa954a99
39 3efda40ae095b4a2d49fae2e3b533d12cef24eade9f14a6e418a67a2348d7f18
40 2823f43d275aa6ff27f6bb4a258ee827529c17fc54ee89bda7964904db32f984
41 3e55ce72de55aca37307d1b71f262b9e9035be917dfcd426da2d03b0cdcba940
42 4c9dcee45a9b4c156af7443d08ea7aad6b069783bfa8ad9fd0f64bceb2838f02
43 72b8dbd0a55a8a7fbda5b2b25e657d994ba4a218ceb4484a83bea67fe04630ba
```
