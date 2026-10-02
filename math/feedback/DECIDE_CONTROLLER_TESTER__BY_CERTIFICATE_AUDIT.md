# Audit of `DECIDE_CONTROLLER_TESTER`

## Claim audited

The note claims that escape-aware finite-clock shells and exact rational
interval trees give:

1. a sound and complete finite certificate system for positivity of the Fin4
   terminal exploitability infimum;
2. a terminating two-sided resolver at every positive rational accuracy;
3. uniform computability of that infimum on rational reward tables; and
4. a recursively enumerable rational-open cover of the positive-value locus.

I audited the shell bracket, the finite rational presentation, the interval
tree argument, and the passage from strict shell bounds to the positivity
semidecision. I inspected the following checked interfaces:

- `finFourSingleShell_quantitative_bracket` and
  `finFourSingleShellLower_le_exploitabilityInf` in
  `Research/Quitting/FinFourSingleShellOuter.lean`;
- `finFourRationalSingleShellProblemValue_eq_finFourSingleShellLower`,
  `finFourRationalSingleShellTree_sound`, and
  `exists_finFourRationalSingleShellSearch_of_lt_lower` in
  `Research/Quitting/FinFourRationalSingleShellLower.lean`;
- `RationalLowerBoxProblem.verifies_sound` and
  `RationalLowerBoxProblem.exists_search_verifies_of_feasible_objective_gt`
  in `MathUE/Interval/RationalLowerBoxTree.lean` and
  `MathUE/Interval/RationalLowerBoxSearch.lean`;
- `exists_finFourExactScaleStep`, its upper/lower soundness theorems, and
  `finFourExactScale_infimum_zero_or_lower_event` in
  `Research/Quitting/FinFourExactScaleResolution.lean`; and
- `exists_finFourCounterexampleStep_iff_exists_real_infimum_pos` in
  `Research/Quitting/FinFourCounterexampleSemidecision.lean`.

## Verdict

The normalized-rational core is mathematically sound and is substantially
already checked. The certificate and approximation conclusions survive, but
the note needs two explicit repairs before its headline arbitrary-rational
theorem is literally correct as written.

The first repair is a genuine definition mismatch. The second is a missing
normalization wrapper. Neither damages the intended result.

## Required repair 1: use the truncated objective on the whole shell

Section 1 defines

\[
E(u,b)=\max_i(b_i-u_i).
\]

Section 3 instead encodes

\[
E_+(u,b)=\max\{0,b_0-u_0,\ldots,b_3-u_3\}.
\]

These coincide on actual semantic pairs because prescribed play is an
admissible response, so every debt is nonnegative. They need not coincide on
the ambient outer shell: a shell point is merely close to a semantic center
and may have all four displayed differences negative. Therefore the quantity
called `A_N` in Section 2 is not literally the value of the executable problem
unless the same truncated objective is used there.

Repair the first definition to

\[
E(u,b):=\max\{0,\max_i(b_i-u_i)\}
\]

everywhere. The carrier identity is unchanged, the Lipschitz constant remains
two, and the shell bracket then agrees exactly with
`finFourSingleShellObjectiveExpression` and
`quittingTerminalSemanticExploitability`.

## Required repair 2: define the arbitrary-rational verifier

The checked single-shell verifier is for a normalized rational reward code.
Its semantic soundness theorem also consumes normalization. The note begins
instead with an arbitrary rational table and postulates a relation
`Verify(r,N,a,T)` whose soundness has no normalization premise. Scaling is
discussed, but the verifier itself is never defined through that scaling.

There are two honest presentations.

### Normalized version

State the main theorem for rational tables satisfying
\(\lVert r\rVert_\infty\le 1\), and include the normalization check in the
Boolean certificate relation. This version is directly represented by the
current shell and exact-scale declarations.

### Arbitrary-rational wrapper

For arbitrary rational `r`, compute

\[
M(r)=\max\bigl(1,\max_{S,i}|r_i(S)|\bigr),
\qquad \bar r=r/M(r).
\]

Define

\[
\operatorname{Verify}(r,N,a,T)
\quad:\Longleftrightarrow\quad
\operatorname{Verify}_{\rm norm}
  \bigl(\bar r,N,a/M(r),T\bigr).
\]

Then homogeneity gives

\[
a/M(r)\le\eta(\bar r)
\quad\Longrightarrow\quad a\le\eta(r),
\]

and strict-margin completeness transfers in the same way. All data remain
rational and decidable. The tree type depends only on `N`, so no additional
payload is needed.

Without one of these changes, the displayed arbitrary-table soundness theorem
is not the theorem currently proved by the cited checker. In particular,
`exists_finFourCounterexampleStep_iff_exists_real_infimum_pos` is a global
existential enumeration theorem; it is not a direct fixed-table verifier for
an arbitrary unnormalized rational input.

The same wrapper is needed in the proof of the open-cover formula. Restricting
certificate centers to normalized tables would not cover positive tables far
outside the normalized cube, whereas the proof chooses a rational center close
to the supplied real table.

## Shell bracket

After the objective repair, the bracket is correct.

For level `N > 0`, the checked center clock is

\[
T_N=8N+1,
\]

and the semantic radius is `12/N`. Every actual semantic pair lies in the
closed radius shell, while every center is the semantic pair of an actual
finite-clock product profile. The objective is two-Lipschitz in the semantic
sup metric. Hence, writing `A_N` for the one-shell lower value and `V_N` for
the center upper value,

\[
A_N\le\eta\le V_N,
\qquad V_N-A_N\le 24/N.
\]

The statement that a distance-shell point has a center within the radius is
legitimate here because the center set is nonempty and compact, so the
infimum distance is attained.

The all-Never point is retained, and the auxiliary date correctly represents
all finite stopping times at or after the last active clock date against
finite-clock opponents. Never remains a distinct response. Thus the cap in
the center problem is the unrestricted behavioral cap, not a bounded-tester
surrogate.

## Finite rational presentation

The dimension and row counts in the note are correct:

\[
8N+3\text{ atoms per marginal},
\qquad 32N+28\text{ real variables},
\]

\[
16\text{ equalities},
\qquad 64N+40\text{ required-nonnegative rows}.
\]

The auxiliary mass is constrained to zero but its coordinate remains among
the pure-deviation candidates. The cap-upper inequalities together with the
product-zero tightness equation force the displayed cap to equal one member
of the finite candidate menu and dominate every member, hence to equal its
maximum. Over the real numbers there is no missing disjunct in this encoding.

The rational root box contains every feasible semantic/mass assignment under
the normalized reward bound. With the repaired truncated objective, the
feasible objective image is exactly the analytic one-shell image.

## Interval-tree proof system

The three leaf rules are sound. A real feasible point cannot lie in a leaf
whose equality interval omits zero or whose required-nonnegative interval has
negative upper endpoint. An objective leaf directly gives the requested lower
bound. Because child boxes are reconstructed from the split path, induction
over an accepted tree proves the lower bound on the entire root box.

Strict-margin completeness is also correct. If `a < A_N`, every root-box point
has one of three strict witnesses:

- a nonzero equality;
- a negative required-nonnegative row; or
- a feasible objective strictly above `a`.

Rational max-expression interval extensions converge as all coordinate widths
shrink, and the full-coordinate dyadic schedule is fair. Compactness then
forces a finite accepted refinement. This is exactly the hypothesis and
conclusion of
`exists_search_verifies_of_feasible_objective_gt`; no general CAD or
quantifier-elimination claim is needed.

## Positivity semidecision

For normalized rational tables, the main equivalence is valid:

\[
\eta(r)>0
\quad\Longleftrightarrow\quad
\exists N\ge1\ \exists a\in\mathbb Q_{>0}\ \exists T,
\quad \operatorname{Verify}_{\rm norm}(r,N,a,T).
\]

Soundness is non-strict: an accepted tree proves `a <= A_N <= eta(r)`.
Completeness uses `A_N >= eta(r)-24/N`; for every rational `a < eta(r)`, a
sufficiently large `N` makes `a < A_N`, after which strict tree completeness
applies.

The note correctly reduces a non-strict cap lower bound before claiming an
attained behavioral deviation. A certificate at scale `epsilon` proves a
literal terminal gap at every strictly smaller level, and `epsilon/8` is a
valid uniform choice below the certified `epsilon/4` cap bound.

The fixed-scale total resolver is also correct. Use the natural-number floor
notation appearing in the checked source,

\[
N(\varepsilon)=\lfloor 96/\varepsilon\rfloor_{\mathbb N}+1,
\]

to avoid ambiguity. At that level either strict lower search terminates, or
the shell upper value is below `epsilon/2`; density of rational finite-clock
profiles then produces an exactly checkable upper witness below
`3 epsilon/4`. This is a terminating scale resolver, not a terminating test of
whether `eta` is zero.

## Derived consequences

The computable-real argument is sound for normalized rational tables. The
explicit normalization wrapper above extends it uniformly to arbitrary
rational tables. At fixed `N`, dovetailing strict lower trees and rational
upper profiles eventually gives rational bounds

\[
a\le\eta(r)<b,
\qquad b-a<\delta.
\]

This does not decide exact zero.

The `2`-Lipschitz reward robustness estimate and the radius `a/4` in the open
cover are correct. Once arbitrary-rational `Verify` is explicitly defined,

\[
\{r:\eta(r)>0\}
=
\bigcup_{\operatorname{Verify}(q,N,a,T)}
B_\infty(q,a/4)
\]

is valid. For a noncomputable real table this is a topological coverage
statement. For a computable real table with certified approximations, entry
into one displayed rational ball is finite positive evidence.

## Strongest valid theorem

After the two repairs, the strongest justified statement is:

> For every rational Fin4 reward table, there is a decidable finite-tree
> certificate relation, obtained by explicit rational normalization, such
> that accepted level-`a` certificates prove `a <= eta(r)`, and every rational
> `a < eta(r)` has a certificate at some finite shell level. Consequently
> `eta(r) > 0` is semidecidable for each fixed rational table; `eta(r)` is a
> uniformly computable nonnegative real; and the positive locus in the full
> finite-dimensional real reward space is an effectively enumerable union of
> rational open balls.

This theorem does not decide the Fin4 conjecture, decide whether a supplied
table has zero value, or provide a positive table. It is nevertheless a
complete finite certificate theory for every positive Fin4 value, rather than
only a numerical heuristic.

## Re-audit of the revised note

The revised definition

\[
E(u,b)=\max\{0,\max_i(b_i-u_i)\}
\]

correctly repairs the ambient-shell objective mismatch. The displayed
arbitrary-rational wrapper

\[
\operatorname{Verify}(r,N,a,T)=
\operatorname{Verify}_{\rm norm}
  \bigl(r/M(r),N,a/M(r),T\bigr)
\]

is also mathematically correct, and the note now honestly labels that wrapper,
uniform computability, and the open-cover theorem as ordinary mathematics not
yet present under named checked declarations.

One local scoping inconsistency remains in the written proof. Section 2 begins
with the arbitrary table `r` from the headline and assigns it the normalized
radius `12/N` and bracket `24/N`. Those constants apply to `bar r`, not to an
unnormalized table. Correspondingly, under the wrapper, an accepted tree proves

\[
a/M(r)\le A_N(\bar r),
\]

not the currently displayed intermediate statement `a <= A_N(r)` in (17).
The latter is not defined compatibly with the wrapper.

This needs only a presentational repair: say at the start of Sections 2--4
that `r` is normalized and use `Verify_norm` throughout (17)--(19). Then return
to arbitrary `r` by applying those statements to `bar r` at threshold `a/M`
and multiplying by `M`. Alternatively define scaled shell quantities
`A_N(r) := M A_N(bar r)` and `V_N(r) := M V_N(bar r)`, in which case the shell
width is `24 M/N` rather than `24/N`.

After that scoping repair, I find no remaining mathematical overclaim. The
fixed-scale resolver is explicitly limited to normalized rational tables; the
arbitrary-table computability paragraph rescales its accuracy correctly; the
open-cover calculation uses the repaired arbitrary-rational verifier; and the
note continues to distinguish positivity semidecision from zero-decision and
from production of a positive table.
