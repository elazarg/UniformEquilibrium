# Independent review: nonnegative-weight social chamber

Reviewer: `PAIRED_HULL_REVIEW`  
Date: 2026-08-31  
Verdict: **PASS.**

I found no mathematical defect in the global-minimum inequality, its
positive-support outcome form, the fixed-support cone alternative, the
Caratheodory support bound, or the separating Fin4 example.  The note should
be combined with the sparse-law/product-barrier result for export, rather
than exported as two overlapping packets.

## 1. Claim checked

At an ordinary global minimum (z_*=(U,B)) of total semantic debt, write

\[
 d_i=B_i-U_i,
 \qquad D_*=\sum_i d_i>0.
\]

For a nonnegative costate θ with at least two positive coordinates, put

\[
 T=\sum_i\theta_i,
 \qquad M=\max_i\theta_i,
 \qquad A=\theta\cdot s,
\]

where (s_i=r_i(\{i\})).  The note claims

\[
 A+(T-M)D_*\leq\theta\cdot U\leq
 \max\bigl(0,\max_{S\ne\varnothing}\theta\cdot r(S)\bigr).
\tag{1.1}
\]

It also claims a positive-mass common outcome attaining the corresponding
surplus lower bound, and for every fixed support (J) an exact alternative
between a positive costate on (J) and a (J)-projected Pareto law supported
on at most |J| outcomes.

## 2. Global-minimum inequality

The proof is exact.  The checked singleton margin gives

\[
 D_*\leq B_i-s_i
\tag{2.1}
\]

for every player.  Multiplication by θ_i≥0 and summation gives

\[
 TD_*\leq\theta\cdot(B-s)
 =\theta\cdot(U-s)+\sum_i\theta_i d_i.
\]

Carrier debt nonnegativity and θ_i≤M imply

\[
 \sum_i\theta_i d_i\leq M\sum_i d_i=MD_*.
\]

Subtracting proves the left side of (1.1).  Nothing here inserts zero
coordinates into the strictly-positive weighted-minimum theorem; this is a
different and valid argument at the ordinary total-debt minimum.

The right side uses only the checked reward-moment membership of the
prescribed coordinate.  Never has reward zero, so the outer maximum with zero
is necessary and sufficient.  No actual profile attaining the minimum is
assumed.

If at least two coordinates of θ are positive, then (T-M>0).  Thus the
division and positive-part bound in the note are valid.  The chamber condition

\[
 \theta\cdot s\geq0,
 \qquad
 \theta\cdot(r(S)-s)\leq0
\]

for every nonempty (S) contradicts (D_*>0), and the checked zero-minimum
consumer applies.

## 3. Positive-mass common outcome

Let μ be a reward-moment law for (U), including Never.  Equation (1.1)
gives

\[
 (T-M)D_*\leq
 \sum_\omega\mu(\omega)
   \theta\cdot(\bar r(\omega)-s).
\]

Because the outcome space is finite, at least one outcome of positive
μ-mass has surplus at least this average.  This proves the support-sensitive
claim exactly.  The selected outcome may be Never; the note states this.

## 4. Fixed-support dual and support bound

For a fixed (J), the generator cone

\[
 C_J=\operatorname{cone}
 \bigl(\{-s|_J\}\cup
 \{(r(S)-s)|_J:S\ne\varnothing\}\bigr)
\]

is finitely generated and closed.  Its disjointness from the nonnegative
simplex is equivalent to (C_J\cap
(\mathbb R^J_{\geq0}\setminus\{0\})=\varnothing).  Strong separation from that
compact simplex gives a functional nonpositive on (C_J) and strictly
positive on every simplex vertex.  Hence its coordinate vector is strictly
positive on (J), with exactly the claimed signs.

Conversely, a nonzero vector in the nonnegative orthant generated as

\[
 -\lambda_0s|_J+
 \sum_S\lambda_S(r(S)-s)|_J
\tag{4.1}
\]

is incompatible with any such positive functional.  Normalizing by

\[
 L=\lambda_0+\sum_S\lambda_S
\]

is correct: λ_0/L becomes Never mass and

\[
 \mathbb E_\nu\bar r|_J-s|_J=(4.1)/L.
\]

Conic Caratheodory in ℝ^J replaces (4.1) by a representation using at most
|J| generators while retaining the same nonzero nonnegative vector.  After
normalization, this is a law supported on at most |J| terminal outcomes.
There is no missing affine (+1): the argument is conic, not ordinary convex
Caratheodory.

The quantifier over all nonnegative costates with support cardinality at
least two is also handled correctly.  It is the finite union over fixed
supports (J), on each of which the restricted costate is strictly positive.

## 5. Separating Fin4 example

The example with θ=(1,2,3,4) is correct.  On every nonsingleton coalition
(S), if ℓ and (h) are its least- and greatest-weight members, the only
nonzero rewards are

\[
 r_\ell(S)=\theta_h,
 \qquad
 r_h(S)=-\theta_\ell.
\]

Therefore

\[
 \theta\cdot r(S)
 =\theta_\ell\theta_h-
   \theta_h\theta_\ell=0.
\]

All singleton reward vectors are zero, so the arbitrary-weight chamber holds
with equality.  For every subset (J) of cardinality at least two, using the
coalition (S=J) gives unweighted (J)-surplus

\[
 \theta_{h(J)}-\theta_{\ell(J)}>0.
\]

Thus every subset-indicator chamber fails.  This genuinely separates the
arbitrary nonnegative costate theorem from the complete family of indicator
tests, not just from the all-player indicator.

## 6. Export organization

The primary chamber note and
`CODEX_SOCIAL_DUAL__SPARSE_PARETO_LAW_AND_PRODUCT_BARRIER.md` should become
**one mathematical export**, not two.

The reasons are structural:

1. the supportwise sparse law is the exact dual arm of the primary chamber;
2. both notes currently repeat the same Gordan normalization and
   Caratheodory argument;
3. the sharp Fin4 support example and product/behavioral nonrealizability
   results are the necessary boundary preventing the dual arm from being
   misread as a strategy; and
4. a single packet can state the complete static result:

   \[
   \text{a closing nonnegative social costate}
   \quad\lor\quad
   \text{fixed-support sparse Pareto laws, generally nonexecutable}.
   \]

The export should use the global-minimum theorem and fixed-support dual from
the primary note as its main statement, then take the sharp support and
product/behavioral barrier sections from the sparse-law note.  Lean
formalization may naturally split these into separate declarations; that is
not a reason to duplicate the mathematical export.

The newer pairwise exploration
`CODEX_SOCIAL_PAIR__SOURCE_SUPPORTED_TWO_OUTCOME_CERTIFICATES.md` should
remain a research note for now.  It adds the useful fact that the selected
outcomes can be chosen inside one minimum law's positive support, but its
conclusion is presently a boundary result rather than a consumer.

## Sources inspected

- `minimumTerminalSemantic_singletonMargin` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticAuxiliaryNashBudget.lean`;
- `quittingTerminalSemanticCarrier_prescribed_mem_rewardMomentSet` in
  `UniformEquilibrium/Quitting/Root/TerminalSemanticMoment.lean`;
- `exists_uniformEquilibriumPayoff_of_hasZeroMinimumTerminalSemanticDebt` in
  `UniformEquilibrium/Quitting/Terminal/PositiveMinimumSemanticDebt.lean`;
- `notes/CODEX_WEIGHT_GLOBAL__NONNEGATIVE_WEIGHT_SOCIAL_CHAMBER.md`; and
- `notes/CODEX_SOCIAL_DUAL__SPARSE_PARETO_LAW_AND_PRODUCT_BARRIER.md`.

