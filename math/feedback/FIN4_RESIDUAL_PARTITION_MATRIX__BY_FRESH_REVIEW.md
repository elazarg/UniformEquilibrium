# Fresh whole review of the Fin4 singleton-matrix partition

## Verdict and exact scope

Reviewer: all_positive_final_review. This is a fresh independent review of the
complete matrix partition in Sections 1--8 of
[the residual partition](../notes/CODEX_COORDINATOR__FIN4_RESIDUAL_PARTITION.md), including the full
unique-pivot/no-child classification, the signed active-set atlas, the affine
multiple-pivot refinement, all eight pivot patterns in its twelve-sign orbit,
and the favorable-coordinate-ray counts. Prior component review approvals are
not premises of this review.

**Verdict: PASS as an exact internal matrix repartition.** There is no unresolved
mathematical objection. The result does not eliminate a new UE counterexample
class, settle an arbitrary collision-reward branch, or close Fin4.

Byte boundary and hashes:

* Exact Sections 1--8 begin with `## 1. Scope and generic source` and end
  immediately before `## 9. Five actual-source cases and five inherited endpoint cases`.
  This UTF-8 byte segment has 29,728 bytes and SHA-256
  `0d69c9190bf8abb264e0eeb46e58b7cccedf3375ec4fffa317fcdfba7c3f6cc7`.
* The same prefix including the title and introductory front matter has
  30,834 bytes and SHA-256
  `255705a81b7e7f0c10e37aba1f94904cab60563ef0e9fe6d0914f4c7e58eea19`.
* The complete canonical stdlib checker
  `math/experiments/CODEX_PARTITION__FIN4_SINGLETON_CELLS_CHECK.py` has SHA-256
  `3e3586061c1bb7a555a7711c045b9d397a5d95a2ef236e8cba59b5c82e1646de`.
* Its matrix-only prefix, ending immediately before
  `# Raw necessary tests for a selected actual two-owner tail.`, has 10,369
  bytes and SHA-256
  `b9ae064da075fc88e0186422d616ca7961d1b255e851eb1b6b843220591c0ffd`.

The later actual-source and endpoint analysis in Sections 9--10 is outside
this review. I ran the complete checker, so its I2 controls also executed, but
that execution is not an independent semantic review of those later sections.
No repository file was edited and no Lean, Lake, build, or Git command was run.

## Source, genericity, and normalization audit

I read the mathematical instructions and export boundary, then the exact
relevant source declarations:

* `standardQMatrixSide_of_not_exists_uniformEquilibriumPayoff` in
  `UniformEquilibrium/Quitting/Classification/LCP/CounterexampleNecessary.lean`;
* `normalCore_eq_univ_of_fourPlayer_not_exists_uniformEquilibriumPayoff` in
  `UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/AmbientCarrierElimination.lean`;
* `singleton_r0Degree_eq_one_of_no_uniformPayoff` in
  `UniformEquilibrium/Quitting/Classification/LCP/SingletonDegreeCriterion.lean`;
* `exists_uniformEquilibriumPayoff_of_raw_nonnegativeInverse_triple` in
  `UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/RawPassiveRowInverseCriterion.lean`;
* `exists_uniformEquilibriumPayoff_of_arbitrarily_close_reward_tables` in
  `UniformEquilibrium/Quitting/Terminal/TerminalExploitabilityRewardRobustness.lean`.

I also read the coordinate-ray and sign arguments in Part IV, Sections 2--4,
of `FIN4_STRICT_INVERSE_COLUMN_AND_ALL_END_MINIMUM_REDUCTION.md`, and the raw
support/sign hypotheses and scale definitions in
`WEIGHTED_COLLISION_DOMINANCE_UNIFORM_EQUILIBRIUM.md`.

The note correctly distinguishes necessary matrix restrictions from sufficient
counterexample conditions. In particular it does not infer nonexistence of UE
for an own-zero native table from arbitrary terminal row subtraction. Its
existential original/native gap reduction and its statement that native
AllNever is exact Nash are consistent.

The genericity argument is valid. Counterexamples form an open reward region
by the contrapositive of reward-closure. All excluded singleton-entry,
principal-determinant and optional full-cofactor equalities are nonzero
polynomials on the zero-diagonal singleton space. The all-off-diagonal-one
matrix has the needed nonzero principal determinants and inverse entries.
Thus arbitrarily small off-own singleton perturbations can avoid them without
leaving a counterexample neighborhood. This is a route reduction, not a claim
that every original counterexample is already generic.

For v = Gamma^-1 e_p > 0, positive column scaling gives H1 = e0 and preserves
entry signs, principal determinant signs, complementary supports, R0 and
complementary degree. The latter can also be seen by homotopy through positive
diagonal scales without introducing a homogeneous nonzero solution. Passive
outside inverse weights are unchanged because the child diagonal scales
cancel. These are only algebraic invariances, as the note explicitly states.

The Schur formulas for H = [0,c;-r,B], r = B1 and c1 = 1 are exact:
its Schur scalar is 1, det H = det B, and the entire displayed inverse follows.
The least-original-pivot rule followed by finite observer-word minimization is
well-defined and disjoint on labeled data. It does not accidentally claim ten
unpointed full-matrix sign orbits. All ten witnesses have pivot 0 available,
so this canonical rule retains their ten distinct observer templates.

## Complete degree test and polygon membership

I checked the complete support enumeration at offset -e0. The full root is 1.
Supports omitting 0 of size at least two have zero active target and therefore
zero active vector. Observer singletons fail their negative column, whether
the negative entry occurs in row 0 or another observer. A support {0,i}
fails its observer equation because r_i != 0. Empty and singleton-0 supports
fail the pivot target. This leaves exactly the three possible triples {0,i,j}.

For each such triple, the displayed D_ij formula, root coordinates, inactive
slack and determinant agree. A positive omitted slack forces B_ij B_ji > 0;
its strictness follows from det B > 0. The eligibility and D_ij > 0 tests
are therefore necessary and sufficient, and every admitted proper root has
index -1. No unexamined weak root remains at this offset. The degree formula
1 minus the number of admitted triples follows from the actual degree sum.
The simpler R0 assertion also holds: nonsingular principal supports of size
at least two cannot carry a homogeneous nonzero solution, and a singleton
violates a negative column.

The passive-child reduction checks all four children, not a selected witness.
A generic zero-diagonal 3-by-3 nonnegative inverse is strictly positive because
all its cofactors are nonzero products. Positive inverse forces positive
determinant and cyclic opposite reciprocal signs. For a child containing the
pivot, block inversion makes its outside pivot weight strictly negative.
Thus only B's passive row remains to test. If B is positive-inverse and fails
that row test, any negative R_j produces a strict full pivot inside B by the
explicit block inverse. This pivot switch is valid.

For fixed B, the Section 6 conditions exactly recover negative columns,
mutual negativity, complete degree, passive-child failure, and generic
principal nonsingularity. None is omitted. All c-dependent conditions are
affine on sum c_j = 1. The alternative counts of at most 1, 3 or 9 basic
convex regions are correct. Cutting at equality lines and removing required
genericity lines yields the claimed relatively open polygonal cells, with
lower-dimensional and unbounded cells permitted. The six B magnitudes still
vary, so the note correctly avoids claiming a universal finite list of
sample matrices for the entire continuous problem.

## Sign classification and child-count split

The checker enumerates all 64 observer sign words and all 16 simultaneous
observer-permutation orbits. Its determinant-sign test is exact: a positive
determinant is possible precisely when at least one of the two cycle
monomials is positive. It obtains the stated 11 representatives. The one
all-positive B orbit is impossible because negative observer columns would
force all c_j < 0 while their sum is 1. The remaining ten printed templates,
determinant formulas and forced c-coordinate signs agree with the enumeration
and the direct reciprocal-pair classification.

Each of the ten exact witnesses has all nontrivial principal blocks
nonsingular, negative entries in every column, a mutually negative pair,
positive determinant and strict inverse pivot, exactly its unique full root
at offset -e0, and failure of every positive-inverse child's passive test.
This establishes nonemptiness under the complete Section 1 restrictions,
not merely nonemptiness of a sign word.

A mutually negative pair forbids the positive inverse on its two containing
triples, so at most two good children remain. I independently checked the
child {0,i,j} adjugate and determinant symbolically; their six sign tests are
exactly criterion (8). The checker supplies all child counts 0, 1 and 2.
The small no-child witness has determinant 11, the stated inverse, unique
strict column 2, the stated pointed B,c,r, and empty eligible-pair set E.
Its degree certificate and no-child claim both hold.

## Entire unique-pivot/no-child branch

The large negative coordinate-ray argument applies to every nonpositive full
inverse column under full-cofactor genericity. At -(M e_h+1), omitted-axis
supports are bounded and eventually fail the h inequality; pairs fail an
outside negative entry in their fast column; singleton and empty supports
are impossible; and the full support fails a negative inverse coordinate.
The finitely many surviving triple roots are strict for large M because
both active inverse coordinates and outside leading weights are nonzero.
Degree +1 forces a positive-determinant triple with positive column and
positive exterior weight. Thus every nonpivot axis is covered.

I checked the analytic sign argument identifying the unique orbit, including
its relabeling steps. A positive-determinant 3-by-3 inverse with two positive
columns has all three positive, so no-child prohibits two covered axes on one
triple. If a negative-pair endpoint were the unique uncovered axis, the other
three covered axes lead through the epsilon/delta alternatives to either a
positive-inverse child or an impossible remaining covered column. Four
covered axes are ruled out by the same argument. With the uncovered axis
labeled 2 and a negative pair 01, the remaining assignments force exactly
(013,axis0), (123,axis1), (023,axis3) and the displayed twelve signs (9).

Their exterior weights are respectively -U/R, -V/D123 and -W/D023.
Positive determinant and exterior slack give precisely R > 0 and
U,V,W < 0. Conversely those inequalities imply D > 0 through the exact
Jacobi identity, yield strict full column 2, and put a negative coordinate
in each other full column. The opposite-pair graph is a path, excluding
positive-inverse triples. The complete offset -e2 support census leaves
only the full root of index +1. Together with principal nonsingularity and
negative columns, this proves all Section 1 conditions. This is an iff
classification within the stated additional genericity, not just a necessary
sign list.

The nonzero E,T conditions supply exactly the remaining genericity tests:
V < 0 forces ch > ai, fixing the signs of N03, N21 and N23; every other
cofactor except E and T is already fixed strictly. The four exact integer
witnesses cover all four (sign E, sign T) cases.

I also checked the claimed COMPLETE ten-choice signed active-set atlas.
On 013, the three uniform column signs are (+,-,-), with outside row
(-U,-N21,-N23)/R. Multiplying each by its corresponding sign makes both the
active direction and exterior image strictly positive. Its seven nonempty
recipient subsets are therefore eligible. The only other eligible choices
are row1+ on 123, row3+ on 023 and row2+ on the full set. All 012 columns and
unlisted 023/123 columns are mixed; all unselected full columns are mixed;
pair inverse columns have a zero coordinate. This verifies exactly ten
choices for all four E,T subcases.

## Multiple-pivot refinement and all eight patterns

For fixed B, the condition R_j < min(0,V_1j,V_2j,V_3j) is equivalent to
strict positivity of full observer inverse column j. Under inverse-entry
genericity the equality boundary cannot occur. The three independent affine
cuts give at most eight convex pieces of each prior polygon. The note does
not incorrectly assert that every abstract piece is nonempty.

Inside the particular twelve-sign orbit, I independently expanded the full
symbolic adjugate in all twelve magnitudes. Every entry agrees with the
checker, and all five identities (16) vanish identically. These identities
prove the exact full-pivot set

    {2} union {0:U>0} union {1:V>0} union {3:W>0}

under R > 0 and D > 0, with no hidden U,V,W sign assumptions. In particular,
U > 0 forces N10 > 0; N21 > 0 follows from the second identity; and W > 0
forces all remaining column-3 entries positive by the final three identities.

Sufficiency of R > 0,D > 0 uses the same complete offset -e2 support census
without sign restrictions on U,V,W. For necessity, if R < 0 then U < 0,
so a strict pivot must be 1 or 3. The corresponding column of the 013
inverse is positive because its adjugate column is negative and R < 0.
Its exterior weight is strictly positive by the full-pivot block identity,
so it contributes index -1. Every other admitted proper triple at that
pivot also has negative determinant. All smaller supports fail. The total
degree therefore cannot be +1. Genericity excludes R = 0. This proves the
stated iff reduction to R > 0,D > 0 on the whole sign orbit.

I verified all eight listed integer rows, including their printed R and D
values, full cofactor nonvanishing, every principal determinant, complete
strict-pivot sets and the unique offset -e2 root. All eight U/V/W orthants
occur. No connectedness of these sign regions is used or claimed.

## Favorable directions, attempted falsifiers, and reproducibility

The Section 8 direction theorem is a consequence of the prior coordinate-ray
argument and the weighted collision theorem. A strict full pivot supplies
full support; every other recipient gets a positive triple direction with
strict outside image. With m full pivots, the distinct ray counts are
3m+2(4-m)=8+m, 3m+(4-m)=4+2m, 3m+(4-m)=4+2m, m, and m, respectively.
Recipient rows distinguish these coordinates, so there is no double counting
across recipients. Holding every other reward fixed keeps the adverse scale
bounded while the selected favorable scale diverges. This does not say that
competing large rewards or arbitrary collision completions are covered.

The principal attempted falsifiers were:

* missing singleton, pair or weak triple roots at the special offsets;
* a hidden positive-inverse child containing the selected pivot;
* a unique pivot lying in the negative reciprocal pair;
* four covered axes without a positive-inverse triple;
* a mixed-sign full column becoming positive contrary to (15);
* a degree-one matrix with R < 0 in the same sign orbit;
* an extra signed active-set choice outside the ten-choice atlas;
* loss of one of the eight pivot orthants through genericity conditions;
* an implicit use of column scaling as a game-equilibrium invariance.

The support formulas, adjugate signs, degree sum and exact symbolic checks
resolve all of them. None yields a surviving counterexample to the matrix
claims.

I inspected the stdlib checker in full and ran
`python math/experiments/CODEX_PARTITION__FIN4_SINGLETON_CELLS_CHECK.py`.
All printed checks passed: 64 words/16 orbits/11 determinant-positive-possible
classes; ten generic normal-form witnesses and complete child failure;
child counts 0/1/2 and the exact no-child witness; the conservative 4096-word
covered-axis census with 48 signatures in one orbit; and all eight complete
pivot patterns. The independent symbolic checks and complete signed-atlas
checks are in `/tmp/FIN4_MATRIX_PARTITION_INDEPENDENT_CHECK.py`; all passed.
The canonical checker itself requires only Python's standard library.

This consolidated review covers the complete stated matrix result at the
pinned bytes. It can serve as the coherent review record without retaining
fragmented component approvals. No further UE class is excluded merely by
this repartition, and arbitrary Fin4 remains open.
