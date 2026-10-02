Historical design record. Frozen source/review artifact; see Research/Pending/README.md.

# Independent static review: rational screened-source selection 66–67

Verdict: PASS for mathematical/source scope and the displayed quantifiers.
No definite proof repair identified. These are frozen, unapplied drafts:
no compiler, axiom, integration, or whole-packet seal is claimed. Root alone
owns application and checks. No shared edits, Git, builds, caches, worktrees,
children, or math-note edits were used.

Both complete patches, the complete handoff and harness, and the complete
screened-source export were read. The dependency specification's P8 and
adjacent P6/P7 contracts were compared. Canonical scaling/robustness and
no-UE/positive-infimum declarations were inspected, as were the exact frozen
density62, strict-gap65 and literal chart bodies. Earlier independent reviews
of 61–62 and 63–65 remain dependency evidence, not compiler seals.

## Immutable byte verification

All advertised 66–67/harness/source and predecessor-handoff hashes match.
SHA256:

```text
6e8b02b20bf1f95d45c47230ffc9b9704f09fb34fe4951c17ce554053fee13da  66_POSITIVE_RATIONAL_SCREENED_FIBER_ENTRANCE.patch
796e94ee41afe255e168ed01e21fa055d8eb93b98015d3e2a030b50dc8b8d623  67_RATIONAL_SCREENED_SINGLETON_FIBER_SELECTION.patch
8c75826abbf456568f3163f868c8e2970169e05e406ad799eed3531c184bcf0f  AXIOM_HARNESS.lean
1d6d8a25770497bea9bb49f110a61c7e42b61ee9ce6736d49a8fbf5a8f5e32b6  HANDOFF.md
```

The four paths above are under `/tmp/ue-screened-rational-selection-sInZmW`.
Source and canonical fingerprints:

```text
c3004d986acc316a20b7c29a7cdc9c764235f843e4b006a7fc99e0cbe0e0f5d7  math/exports/GENERIC_SCREENED_ROOT_EXCLUSION_AND_SINGLETON_MASS_COLLAR.md
0f4412a92546f7036c1d850e96141275526cf18e9aa000bc48c1c079d8509a59  /tmp/three-source-packets-dependency-audit.xEpZYgxQ/DEPENDENCY_AND_THEOREM_SPECS.txt
6ec9f2a4ccc5c6fa94d52ae86e477025cfaec3102603427d51c09a473b939bd0  UniformEquilibrium/Quitting/Terminal/TerminalExploitabilityRewardRobustness.lean
d71b92d78fcd032dcc0055747abe2cc0227c79e42bb0a7bc36f71d6982b93d70  UniformEquilibrium/Quitting/Terminal/TerminalDebtPrefixDescent.lean
6cf88b0275721e0e933301951eab49a015316f75a3717df01e6e0f2a25c4ee06  /tmp/own-singleton-reward-chart.fIa1qX/OWN_SINGLETON_REWARD_CHART.patch
e470d528865baf2ebc20cfc19fa61a5d62e157a07f7a63791abad71a54126cbb  /tmp/ue-screened-polynomial-density-Z9NPbs/HANDOFF.md
cfbf2df77abe2f17d8396178f63283dbe580bcffc1dd72b6ab71afc506ff4254  /tmp/ue-screened-polynomial-density-Z9NPbs/61_MVPOLYNOMIAL_NONVANISHING.patch
5ff786b574db33957988c2203e44a27517ea6d127c3e8c0ee5b93ff408493faa  /tmp/ue-screened-polynomial-density-Z9NPbs/62_SCREENED_ROOT_POLYNOMIAL_DENSITY.patch
bedcc5a538d3513ed89c14c183922095b1668ac883a7b2bb971dcb6b7e6b6e07  /tmp/ue-screened-fiber-extrema-DhGLPM/HANDOFF.md
f1816c277e0db1d6ea696a0d6739479498f2fa52ab203c5bc9fb11fce5abb19c  /tmp/ue-screened-fiber-extrema-DhGLPM/63_OWN_SINGLETON_FIBER_MAXIMUM.patch
6cc75d542579b934155f309d6f13a096769371115034e39a9fe0a22ee6a38009  /tmp/ue-screened-fiber-extrema-DhGLPM/64_SCREENED_ROOT_COMPACT_MINIMUM.patch
fa436850afb00636522974ceec6671cfc2f30a8288e664bf358f0f7d621521dd  /tmp/ue-screened-fiber-extrema-DhGLPM/65_SCREENED_SINGLETON_FIBER_STRICT_GAP.patch
```

New files are additions, not edits against a stale shared-file base. Their
dependency chain still includes the earlier complete polynomial algebra,
degree, per-factor witnesses and chart integration/repairs listed in the
predecessor handoffs. This review does not replace that chain's checks.

## 66: common scaling and actual positive entrance

`exists_strictUnit_scaleQuittingReward` in proposed
`UniformEquilibrium/Quitting/Terminal/StrictUnitRewardScale.lean` chooses
one scalar 1/(M+1), with M the canonical sum reward bound. Existing
`quittingRewardBound_nonneg` and `abs_reward_le_quittingRewardBound` in
`UniformEquilibrium/Quitting/RewardBound.lean` give M≥0 and every entry ≤M
in absolute value. Hence scale>0 and every scaled literal entry is <1.
There is no recipient-specific scaling or affine shift. The helper works
for arbitrary finite player types, including the vacuous empty type.

`exists_positive_rational_screenedFiber_entrance` in proposed
`UniformEquilibrium/Diagnostics/Quitting/PositiveRationalScreenedFiberEntrance.lean`
starts with an arbitrary actual real Fin4 table and the sole substantive
premise η(original)>0. It uses
`quittingTerminalExploitabilityInf_scaleQuittingReward_pos_iff` to obtain
η(scaled)>0; it does not assume normalization preserves an unrelated objective.

Set radius=η(scaled)/4. The call to
`exists_rational_interior_screenedRootCoordinates_near` (62) internally
selects one rational b in the strict 56-coordinate cube with the SAME
literal `screenedRootExclusionPolynomial` nonzero. Its nonzero-polynomial
proof comes from the actual product and separate factor witnesses; no
favorable common witness is added to the incoming game assumptions.

The new table's four own-singleton entries are exactly those of the scaled
original. Every other terminal/recipient entry differs by <radius. The
proof splits on equality with that recipient's own singleton, using the
direct chart, not on whether the recipient merely belongs to the coalition.
Thus it handles all sixty literal entries and leaves live/Never payoff zero.

`abs_quittingTerminalExploitabilityInf_sub_le_of_reward_close` gives
|η(nearby)−η(scaled)|≤2radius. The lower half implies
η(nearby)≥η(scaled)/2>0. This is the actual full behavioral infimum: the
canonical robustness proof compares every full replacement payoff on the
same law before taking caps, player maximum and profile infimum. There is
no finite-menu or stationary approximation in this selection step.

The output retains scale, strict original scaled bound, selected rational b,
polynomial nonvanishing, and positive η at the unchanged scaled singletons.
It does not claim the final b was originally rational or transport an old
optimizer to the new table.

## 67: fresh extrema, rational gap and semantic equivalence

All declarations below belong to proposed
`UniformEquilibrium/Diagnostics/Quitting/RationalScreenedSingletonFiberSelection.lean`.

`IsRationalGenericScreenedSingletonFiber` is a transparent proposition, not
itself a producer. Its substantive seven fields faithfully represent B:
strict rational b; same polynomial nonzero; closed-cube real s*; rational
γ>0; η(r_b(s*))>0; actual maximality over every closed-cube singleton vector;
and full exploitability ≥η(r_b(s*))+γ for every such vector and every
screened product root. There is no rationality requirement on s* or roots.

`exists_rationalGenericScreenedSingletonFiber_of_positive_inf` actually
constructs all fields. After 66, its retained old singleton vector provides
an existential positive point in the NEW fiber. It then calls
`exists_strict_screenedSingletonFiber_gap` (65) afresh for the newly selected
b. That theorem internally produces an actual η maximizer s*, a screened
minimum root and the exact positive difference θ(b)−η(r_b(s*)).

The existential destructuring matches 65's output order: singleton bounds,
screened membership, positive gap, positive maximum, global fiber maximality,
screened minimality, exact gap identity, and uniform floor. Discarding the
minimizing root and exact gap identity in this final facade is harmless:
they are not later supplied as hypotheses or replaced by arbitrary points.

`exists_rat_btwn` then selects ONE rational γ with 0<γ<gap. The final
comparison is Ω+γ≤Ω+gap≤E for every allowed s and screened root. Both s*
and γ are selected after b but BEFORE these universal quantifiers. No
accuracy, root, or competing singleton vector causes reselection.

Closed singleton faces, optional probabilities 0 and 1, all six sure-pair
charts, and three/four sure quitters remain covered through 65/64. The
root-then-Never profile restricts prescribed play only: its exploitability
still uses every full behavioral deviation, including arbitrary late dates
and Never. The screened minimum is not a restricted-response cap.

`exists_rationalGenericScreenedSingletonFiber_of_no_uniformEquilibriumPayoff`
uses precisely `quittingTerminalExploitabilityInf_pos_of_no_uniformEquilibriumPayoff`
from `TerminalDebtPrefixDescent.lean`. It accepts any original real table
with no fixed uniform-equilibrium payoff, not a supplied selected source,
normal, optimizer, or determinant certificate.

`exists_finFour_no_uniformPayoff_iff_exists_rationalGenericScreenedSingletonFiber`
has a correct reverse implication: construct the literal r_b(s*) and use
its positive actual η in
`quittingGame_not_exists_uniformEquilibriumPayoff_of_quittingTerminalExploitabilityInf_pos`.
It does NOT infer no-UE from polynomial nonvanishing or positive screened
regret alone. This is existential counterexample preservation, not a claim
that the final table equals the incoming table or retains its original target.

## Reuse, proof risks, and source omissions

The generic reward bound, direct coordinate chart, positive scaling semantics,
full-cap robustness, rational nonvanishing density, compact extrema and
positive-minimum all-player ties are reused. No duplicate foundation or
favorable strategic source field was introduced. Repository name/content
search found no existing copy of the three new producer interfaces.

Pinned library names inspected: `div_mul_eq_mul_div₀` has the needed
CommGroupWithZero identity a/c*b=a*b/c; `exists_rat_btwn` supplies a rational
between two real endpoints. The new dependent-if reduction uses
`dite_eq_right`, not the deprecated `dif_neg` used in old frozen chart bytes.
Any earlier chart repair remains a separate dependency; this unit does not
silently incorporate it.

No definite elaboration failure is established statically. Root still needs
to check definitional unfolding of `scaled`/`nearby` and dependent coordinate
subtypes, rational-cast inference for `exists_rat_btwn`, nested conjunction
construction, import instances, unused-argument/linter policy, and transitive
axioms. The supplied harness covers all five new theorems and the predicate;
expected standard three axioms are an expectation, not observed output.

Coverage is source Theorem B/section5.1/P8 using P6/P7, not the complete export.
The optional sentence that the initial table may also be made rational in
all sixty coordinates is NOT implemented by these conclusions. This is
acknowledged in the handoff and is not a defect in the central B claim.
No rational maximizer, global sixty-coordinate maximum, membership-stretch
ancestry, singleton collar, common-calendar sequence, harmonic bound,
actual counterexample, or arbitrarily-low-regret producer is claimed.

Recommended next action: keep frozen originals unchanged; root checks the
full predecessor chain and then the three named new modules and harness,
before umbrella/axiom integration. Mathematical/source PASS here is not
permission to report the packet complete or the new declarations checked.
