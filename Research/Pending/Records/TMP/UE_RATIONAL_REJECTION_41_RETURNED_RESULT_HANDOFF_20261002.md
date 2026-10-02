Historical design record. Frozen source/review artifact; see Research/Pending/README.md.

# Returned-result soundness facade for rational potential rejection

Status: frozen static implementation overlay, not compiled, applied, integrated, or axiom-checked here. Root alone owns shared edits and compilation. Originals remain immutable. This overlay is authored by the same agent who independently reviewed original 37/39/40/41; the new overlay itself does not acquire an independent-review seal from that fact.

## Change and delegation

`rationalQuittingPotentialRejectionSearch_sound` is inserted in `UniformEquilibrium/Quitting/Projective/RationalPotentialRejectionSearch.lean`, after accepted-pair soundness and before source-facing eventual success. Given the literal result equation `search? … budget = some pair`, the pinned `List.find?_some` supplies acceptance of that SAME pair. The proof delegates immediately to `rationalQuittingPotentialRejects_sound`.

Its conclusion includes the returned pair's exact root probabilities, its literal source, exact rational successor, actual successor equality, floor-free robust edge, positive absorption and strict potential-drop rejection. No payoff, regret, density, or enumeration calculation is repeated. No favorable strategy or root is input. The result equation is a normal conditional verifier interface; the existing source-facing eventual-success theorem supplies success under the original source hypotheses.

The executable predicate, search algorithm, existing statements, and existing proofs are unchanged. In particular regret acceptance is still ≤ τA, not < τA. Only the existential producer 39/40 promises the latter. The facade does not advertise exact rational Nash, repeated-game equilibrium, a denominator bound, or a runtime bound.

Pinned theorem inspected: `List.find?_some`, in Lean 4.34.0 `Init/Data/List/Find.lean`, has result `find? p l = some a → p a`. Boolean-to-proposition coercion is exactly `p a = true`. The search definition unfolds to that `find?`; no auxiliary library theorem is invented.

## Exact application order

Existing actual quadratic/multi-affine exclusions and rational polynomial regularity are prerequisites. Then:

1. `/tmp/ue-rational-rejection-MLTrufnP/36_RATIONAL_CLOSED_BOX_DENSITY.patch`.
2. `/tmp/ue-rational-rejection-MLTrufnP/37_RATIONAL_POLYNOMIAL_EVALUATION.patch`.
3. `/tmp/ue-rational-rejection-MLTrufnP/38_RATIONAL_BOXED_ROOT_INTERFACES.patch`.
4. `/tmp/UE_RATIONAL_BOXED_ROOT_38_CANONICAL_BERNOULLI_REUSE_20261002.patch`.
5. `/tmp/ue-rational-rejection-MLTrufnP/39_RATIONAL_ROBUST_REJECTION_DENSITY.patch`.
6. `/tmp/ue-rational-rejection-MLTrufnP/40_ACTUAL_EXCLUDED_POLYNOMIAL_RATIONAL_REJECTION.patch`.
7. `/tmp/ue-rational-rejection-MLTrufnP/41_EXHAUSTIVE_RATIONAL_REJECTION_SEARCH.patch`.
8. `/tmp/UE_RATIONAL_REJECTION_41_RETURNED_RESULT_SOUNDNESS_20261002.patch`.

Skip prerequisites only if root has already applied their exact current approved forms. This does not require 42 or 43. The original all-eight-unit harness imports 43 and should not be used as a narrow group gate.

## Frozen bytes and static checks

Original 41 patch SHA256:
`3e55ce72de55aca37307d1b71f262b9e9035be917dfcd426da2d03b0cdcba940`.

Exact original 41 Lean payload base SHA256:
`acf9c5f689a22a7c0f513797144189ba82b6618ef4e385c5444eb16e04c05cdf`.

New overlay `/tmp/UE_RATIONAL_REJECTION_41_RETURNED_RESULT_SOUNDNESS_20261002.patch` SHA256:
`308a12c342f3995184b026bf0d6187bbb7f522e8a3bf47aafcc69e811ce88380`.

Resulting 41 Lean payload SHA256:
`54e5995b6dd323e9f864b4910648d8521d7f1eefbe532efe7fce031c167733e7`.

The original add-patch payload and overlay were reconstructed entirely in memory; the sole hunk context matches exactly once. Nothing was applied to the checkout or a duplicate checkout. Added production/harness non-import lines are within 100 characters.

Delegating group harness `/tmp/UE_RATIONAL_REJECTION_41_RETURNED_RESULT_AXIOMS_20261002.lean` SHA256:
`78d3461ef846a5e1fd1c7254b882b70703eeb852b7d51ee2f66ff3bfbcb0a449`.

The harness imports only 41, prints nine relevant axiom sets, and includes fully quantified examples delegating to (a) the new same-returned-pair facade and (b) the unchanged source-facing eventual-success theorem. Printing axioms is for the separate audit invocation, not a silent production check. The harness has not been executed.

Independent original-group review `/tmp/UE_REFLECTION_RATIONAL_REJECTION_37_39_40_41_STATIC_REVIEW_20261002.md` SHA256:
`2b614be19da87c4d0d02201284dbfb46f1f93ebba12f7904d20c9bd2cea1453f`.

That report records the complete source/dependency hash inventory and source limitations. This facade implements its explicit returned-result API recommendation without changing the accepted-edge mathematics.
