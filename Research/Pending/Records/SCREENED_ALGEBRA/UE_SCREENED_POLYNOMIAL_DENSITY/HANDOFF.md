Historical design record. Frozen source/review artifact; see Research/Pending/README.md.

# Screened-root polynomial density: frozen known-proof unit

Status: static draft; not applied, compiled, axiom-checked or integrated here.
No Lean/Lake, shared edit, Git operation, cache/worktree or child agent was used.
The root agent remains the sole shared editor and compiler owner.

## Exact source and useful claim

Read the complete 1109-line export
`math/exports/GENERIC_SCREENED_ROOT_EXCLUSION_AND_SINGLETON_MASS_COLLAR.md`.
Its SHA256 is
`c3004d986acc316a20b7c29a7cdc9c764235f843e4b006a7fc99e0cbe0e0f5d7`.

This unit implements section 4.1's final paragraph: the same constructed
degree-144 polynomial has an open dense nonvanishing locus, its zero locus
has empty interior, and rational nonvanishing points are dense. It supplies
the topological rational-choice step used in section 5.1, NOT that section's
complete positive-exploitability/fiber-maximum producer. The dependency audit
calls this P7, not P6 (the latter is the compact-fiber strict-gap join).

The closed-box approximation is standard minor topology/order glue: intersect
each positive-width side with the radius interval around the old coordinate.
Its strict interior is nonempty even when the old point lies on a lower or
upper face. Apply the open-region rational nonvanishing theorem there.

## Frozen new bytes

61_MVPOLYNOMIAL_NONVANISHING.patch
  SHA256 cfbf2df77abe2f17d8396178f63283dbe580bcffc1dd72b6ab71afc506ff4254
  Adds MathUE.Polynomial.MvPolynomialNonvanishing; independently applicable.

62_SCREENED_ROOT_POLYNOMIAL_DENSITY.patch
  SHA256 5ff786b574db33957988c2203e44a27517ea6d127c3e8c0ee5b93ff408493faa
  Adds UniformEquilibrium.Diagnostics.Quitting.ScreenedRootPolynomialDensity.
  Depends on 61 and the complete old chart/algebra/witness chain below.

AXIOM_HARNESS.lean
  SHA256 012ce5cb1258ac37f19f4b00d296b1ffb610b775c5549f58bf81bdd91af7694c
  Prints all twelve new declarations' axioms after application. Expected policy
  is only propext, Quot.sound, Classical.choice; not checked here.

## Exact API and quantifier map

Generic MathUE declarations, all in namespace Math:

- isOpen_eval_ne_zero_mvPolynomial: arbitrary variable type, no nonzero premise.
- dense_eval_ne_zero_mvPolynomial: arbitrary finite variable type and nonzero
  real polynomial; no degree/rational-coefficient/nonempty-index restriction.
- exists_rational_mem_open_eval_ne_zero_mvPolynomial: one rational point in
  EVERY nonempty open real region, using the SAME supplied generic polynomial.
- dense_rational_eval_ne_zero_mvPolynomial: rational nonvanishing locus dense.
- exists_rational_box_eval_ne_zero_mvPolynomial: any closed positive-width box
  point, positive radius, internally chosen rational interior approximation.

Actual GameTheory declarations:

- screenedRootPolynomialEval_eq_real_eval: canonical integer eval2 equals eval
  of the SAME coefficient-cast polynomial; no replacement expression.
- screenedRootExclusionPolynomial_nonvanishing_isOpen
- screenedRootExclusionPolynomial_nonvanishing_dense
- screenedRootExclusionPolynomial_zero_locus_interior
- screenedRootExclusionPolynomial_rational_nonvanishing_dense
- exists_rational_screenedRootCoordinates_mem_open: exists ONE rational b in
  an arbitrary nonempty open region, Pi(b) != 0, THEN forall real singleton
  vectors, forall screened roots, no four equal strictly positive complete debts.
- exists_rational_interior_screenedRootCoordinates_near: forall original b in
  the CLOSED [-1,1]^56 cube and positive radius, exists ONE rational b' strictly
  inside that cube and coordinatewise radius-close, with Pi(b') != 0, THEN forall
  s in the CLOSED [-1,1]^4 cube, forall screened roots, the same exclusion.

The last theorem does not require an interior starting b, positive eta,
singleton sign, favorable root, nonvanishing point or witness certificate.
The selected free recipient/terminal coordinates remain LITERAL and FIXED
while s varies. No recipient-row translation, old-polynomial transport or
singleton-dependent reselection occurs. PMF roots include optional endpoints
and three/four sure quitters. Debts are the actual unrestricted behavioral
terminal debts of the root-then-Never profile, not one-stage response debts.
The unbounded-singleton open-region facade is stronger than the bounded
singleton use; the boxed facade prints the source's closed allowed fiber.

## Canonical discovery and nonduplication

MvPolynomial.funext_set in Mathlib.Algebra.MvPolynomial.Funext is the entire
polynomial identity theorem. A product open neighborhood supplies infinite
coordinate sides via IsOpen.exists_Ioo_subset and Set.Ioo_infinite. The wrapper
does not recreate univariate specialization or induction on polynomial degree.

MvPolynomial.continuous_eval supplies openness. DenseRange.piMap together with
Rat.denseRange_cast supplies rational coordinate density. dense_iff_inter_open
and Dense.exists_mem_open are the existing topological consumers. The pinned
Set.compl_ofPred is used instead of its deprecated compl_setOf alias.

MathUE.Polynomial.DensePolynomial concerns coefficient lists, not this density.
No existing project declaration providing this nonvanishing-density API was
found by declaration/topic searches. No copied project algebra proof is added.

Actual nonzero is consumed ONLY from
screenedRootExclusionPolynomial_map_real_ne_zero in the frozen witness owner.
That owner proves each factor nonzero from its OWN literal bounded rational
reward witness and uses integral-domain product nonzero. It does not claim or
assume a single common witness. The source-facing density theorems have NO
polynomial-nonzero premise. The final rational-choice facades delegate to the
existing actual all-singleton screened-debt exclusion using the SAME chosen b.

## Exact prerequisite/apply order

All ten old patches are independently reviewed but UNAPPLIED/UNCHECKED by this
agent. They remain immutable. Their original order is:

1. /tmp/own-singleton-reward-chart.fIa1qX/OWN_SINGLETON_REWARD_CHART.patch
   6cf88b0275721e0e933301951eab49a015316f75a3717df01e6e0f2a25c4ee06
2. /tmp/screened-root-source.xNVVKd/SCREENED_ROOT_DEBT_BRANCHES.patch
   46d69174893acfbcea517076790e9408007249e030f0dbe2ad0db131ba937e2a
3. /tmp/own-singleton-reward-chart.fIa1qX/SCREENED_ROOT_BRANCH_LABELS.patch
   ebaa9d7113b14e79bc3c12491f580a18c734ef76b9a68d8df21a1d28da25a7c2
4. /tmp/screened-root-four-corners.cIBcxx/SCREENED_ROOT_FOUR_CORNERS.patch
   47813f600a0ff663cf7b9ddbb16f958d55cc589a60f7844ac351a2f50a2a5a5a
5. /tmp/screened-root-four-corners.cIBcxx/SCREENED_ROOT_FOUR_CORNERS_REPAIR.patch
   bfdc3b0bc8706f0b3e3e56fcc7f3487af43a4d3e546b7ec8d6fa5c71abc3a22c
6. /tmp/rectangular-cofactor-kernel.akNW24/RECTANGULAR_COFACTOR_SEGRE.patch
   b07ca5fb697d2c34992ad6d96c593fa1f3447c7cfcd16a5099ac41231bcf0c29
7. /tmp/rectangular-cofactor-kernel.akNW24/RECTANGULAR_COFACTOR_SEGRE_REPAIR.patch
   fdecf5890b7892f339d0fb71f1285942b1fe7d98ec6e4c42cb1a543eb607904e
8. /tmp/screened-root-polynomial.qdx5Fg/SCREENED_ROOT_POLYNOMIAL.patch
   e3ddc227b55d3f48518ed5d60af28620026e95710bf31687e069dda4252e2440
9. /tmp/screened-polynomial-witness.4kdar9/SCREENED_POLYNOMIAL_DEGREES.patch
   9572c041d806a5fbfa8c293f85ca7c5b188492e141eb229a0c3fb91df753af3b
10. /tmp/screened-polynomial-witness.4kdar9/SCREENED_POLYNOMIAL_WITNESSES.patch
    dab5f8e14dc55cd8ef8d005a7d25948767b0060e773aac6542ecbc02b85acbdb
11. New 61 (may be applied/checked independently at any earlier point).
12. New 62.

Old chain source/hash records and exact APIs were read through the full
534-line dependency audit and complete independent review. The direct chart,
actual polynomial and witness patch bodies consumed here were also read fully;
all ten old patch hashes were verified against the records. The two old repairs
are retained, not silently absorbed or discarded.

The complete independent review is
/tmp/UE_SCREENED_SOURCE_STATIC_REVIEW_20261002.md
  b421e3a9a9163e90d5d63e0cf5196ea0dd4975a881832a7c00a6de36228dbcb8
The complete dependency specs are
/tmp/three-source-packets-dependency-audit.xEpZYgxQ/DEPENDENCY_AND_THEOREM_SPECS.txt
  0f4412a92546f7036c1d850e96141275526cf18e9aa000bc48c1c079d8509a59

## Root-owned check order

After the existing chain's own narrow checks, check one target at a time:

1. MathUE.Polynomial.MvPolynomialNonvanishing
2. UniformEquilibrium.Diagnostics.Quitting.ScreenedRootPolynomialDensity
3. This local AXIOM_HARNESS.lean after both source modules are available.
4. Root wires the appropriate MathUE/Diagnostics umbrellas and regenerates
   exhaustive AxiomAudit, then trust/import-graph checks and the scoped full gate.

No umbrella/inventory/shared documentation edits are in these patches.
Static line-length and forbidden-token inspections were clean. Compiler
elaboration, tactic imports, linter behavior and axiom sets remain unverified.

## Separate remaining compact-fiber/source steps and nonclaims

This natural unit closes audit P7 only. D1 metric/cube glue, D2 compact eta
extrema, D3 compact screened minima and P6 strict-gap join remain undrafted.
Suggested exact next API, NOT an existing declaration:

For any literal b, internally produce s in [-1,1]^4 such that every allowed
t has eta(quittingOwnSingletonReward t b) <= eta(quittingOwnSingletonReward s b).
Independently produce a screened PMF root minimizing the same actual E over
the union of SIX CLOSED squares; retain singleton invariance. Then Pi(b)!=0
and the internally selected eta>0 imply a strict theta-Omega_b gap, by the
canonical all-player-ties theorem and the already drafted actual exclusion.
Both extrema must be OUTPUTS of compactness, not favorable input certificates.

Only after that join can source P8 invoke reward robustness to preserve positive
eta under the rational b perturbation, produce the maximizing s and rational
gamma, and quantify the source floor over EVERY s/root. Existing eta robustness
and scaling owners were discovered; they are not re-proved or yet joined here.

The zero-singleton/Never contradiction C1, full joint-carrier graph C3, uniform
near-minimum singleton collar C4/C5, common-calendar selection, harmonic bound
and additional source regressions remain separate obligations. Existing SUM
debt collars do not establish the source's MAX-minimum TOTAL-law-mass collar.
No positive eta, screened minimum, actual Nash point, counterexample, collar
or Fin4 equilibrium resolution follows from density alone. No mathematical
source defect was found in the narrow construction implemented here.
