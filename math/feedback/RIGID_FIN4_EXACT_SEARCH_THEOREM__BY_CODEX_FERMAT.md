# Independent strengthening and falsification review of rigid Fin4 exact search

Reviewer: `CODEX_FERMAT`

## Verdict

**PASS for the corrected maximal export statement in this review; REVISE the
supplied theorem document before using it as the export packet.**

The mathematical core is sound and strictly closes a named algorithmic gap in
[`ESCAPE_AWARE_FIN4_CERTIFICATE_SEARCH.md`](../questions/ESCAPE_AWARE_FIN4_CERTIFICATE_SEARCH.md):
there is now a complete elementary exact generator, an exact finite proof
language, and an independently recomputing verifier for every fixed-accuracy
Fin4 query.  It also proves that falsity of the Fin4 conjecture is
semidecidable by exhaustive rational-table search.

The supplied document overstates the relation to the strict inert chamber.  Its
algorithm is generic in the reward table and does not encode, eliminate, or
consume the inert source.  The statement that it is Output 4 of
[`FIN4_INERT_MACHINE_CERTIFICATE_SEARCH.md`](../questions/FIN4_INERT_MACHINE_CERTIFICATE_SEARCH.md)
must be removed.  The corrected theorem below is nevertheless export-worthy as
a strict narrowing of the general escape-aware certificate-search obligation.

## Corrected maximal statement

Let `r` be a rational Fin4 quitting reward table with every reward coordinate
in `[-1,1]`.  For every positive rational `epsilon`, there is an explicit exact
algorithm which terminates and returns one of:

1. a finite rational interval-tree certificate, independently checkable by
   rational arithmetic, proving

   \[
   \frac{\varepsilon}{4}\le
   \inf_\sigma\max_{i<4}(B_i^r(\sigma)-U_i^r(\sigma)),
   \]

   where `sigma` and every deviation defining `B_i` range over the complete
   behavioral strategy class; or
2. a rational product stopping-law profile with finite clock support and a
   separate Never atom whose unrestricted terminal exploitability is strictly
   below `3 epsilon / 4`.

The first certificate is sound against all behavioral profiles.  The second
object is a literal executable behavioral profile, not an outer semantic
point.

Running these resolvers sequentially at `epsilon_k=2^{-k}` has the following
productive semantics:

- if the exploitability infimum is positive, the process halts after finitely
  many scales with a lower certificate;
- if the infimum is zero, it never emits a lower certificate and instead emits
  actual profiles of exploitability tending to zero.  Those profiles satisfy
  the checked all-errors terminal hypothesis and therefore imply existence of
  a uniform-equilibrium payoff.

This is a productive fork, not a terminating decision procedure on the
zero-gap side.  In particular, no finite initial string of upper profiles
certifies that the process will remain in that branch.

There is a further exact corollary which should be included in the export:

> If any normalized real Fin4 reward table has positive terminal
> exploitability infimum, then a normalized rational Fin4 table does too, and
> an exhaustive dovetailing over rational tables and scales eventually emits
> such a rational table together with a finite all-behavior lower certificate.

Indeed the exploitability infimum is `2`-Lipschitz in the reward sup norm, so a
real positive-gap table has a rational positive-gap neighbor in the normalized
box.  Rational tables and dyadic scales are effectively enumerable, and the
per-scale resolvers can be dovetailed.  Conversely every emitted lower
certificate is sound.  Thus a negative answer to the Fin4 conjecture is
recursively enumerable.  Nontermination does not prove the conjecture.

## Mathematical audit

### 1. Single-shell outer problem

At level `N`, the implementation uses finite support

\[
T_N=8N+1
\]

and semantic radius

\[
\rho_N=12/N.
\]

These are literally the checked declarations `quantileClockSupport_fin4` and
`quantileClockRadius_fin4` in
`Research/Quitting/EscapeAwareQuantileClockHierarchy.lean`.  The checked
common-quantile compression in
`Research/Quitting/EscapeAwareQuantileClockTransport.lean` maps every actual
behavioral profile to an actual independent finite-clock product profile at
that support, retains Never, and controls both prescribed payoff and the
unrestricted cap coordinatewise by `rho_N`.

Let `C_N` be the actual finite-clock semantic image and let `O_N` be its closed
coordinatewise `rho_N`-tube.  Every actual semantic pair lies in `O_N`, while
every center of `O_N` is actual.  For

\[
E(U,B)=\max(0,B_0-U_0,\ldots,B_3-U_3),
\]

the coordinate sup-norm Lipschitz constant is `2`.  If `A_N` is the minimum of
`E` on `O_N` and `eta(r)` is the actual exploitability infimum, then

\[
\eta(r)-24/N\le A_N\le\eta(r).
\]

The inequality directions are correct.  In particular, a certified positive
lower bound for `A_N` is a lower bound for the actual all-behavior infimum.
The cumulative intersection used by the existing hierarchy is unnecessary for
this per-level estimate; replacing it by the final shell does not weaken this
soundness direction or the `24/N` modulus.

### 2. Finite-clock expression system

I independently checked the formulas in `rigid_fin4_exact_search.py`.
For each player they retain masses at every represented date, a separate Never
mass, a simplex equation, and a zero-mass auxiliary after-support date.  Every
joint event probability is regenerated as a product of the four marginals.

The earliest-coalition payoff formula is exact.  For one deviator, the finite
menu

\[
0,1,\ldots,T_N,\mathsf{Never}
\]

is payoff-complete against opponents supported before `T_N`: all still later
finite dates have the same payoff as the auxiliary date, whereas Never can
differ on the all-opponents-Never event.  The checked pure-time extremality
bridge makes the maximum of this menu the cap against every behavioral
deviation, not merely stationary or bounded-memory deviations.

The direct cap is represented by a finite `max` expression rather than a
separately constrained cap variable.  This is an exact alternative to the
max-graph presentation in `FiniteClockPolynomialCenter.lean`.

### 3. Lower interval certificates

Each leaf has one of three sound meanings:

- an equality interval excludes zero, so the box has no feasible point;
- an inequality interval has upper endpoint below zero, so the box has no
  feasible point; or
- the objective interval has lower endpoint at least `gamma`.

Induction over the binary splits proves that a verified tree covers the root
box and establishes the lower bound at every feasible point.  All operations
use exact `Fraction` arithmetic.

The strict-margin completeness proof is valid.  If `A_N>gamma`, every point
of the compact root box has a neighborhood certified by a nonzero equality, a
strictly violated inequality, or objective strictly above `gamma`.  Factored
interval evaluation, including finite maximum nodes, converges to point
evaluation as the box diameter tends to zero.  The implementation always
bisects a coordinate of maximal width normalized by its root width.  Because
there are finitely many coordinates, every coordinate width tends to zero on
every infinite branch.  A Lebesgue-number argument therefore gives a finite
depth at which every surviving box classifies, and breadth-first search finds
a finite tree.

The normalized-longest-side fairness sentence in the preceding paragraph
should be added to the export proof.  Compactness alone does not prove
termination for an arbitrary unfair splitting rule.

### 4. Upper enumeration and scale resolution

The upper generator enumerates clock bounds and common denominators
diagonally, then all four marginal simplex points.  Every rational finite-clock
profile appears, and rational profiles are dense in every fixed finite product
simplex.  Exact finite-clock exploitability is continuous, so every strict
upper allowance has a rational witness.

For

\[
N=\lfloor96/\varepsilon\rfloor+1,
\qquad a=\varepsilon/4,
\qquad b=3\varepsilon/4,
\]

one has `24/N < epsilon/4`.  If `A_N>a`, lower-tree completeness terminates.
If `A_N<=a`, a witnessing actual center has exploitability below

\[
a+24/N<\varepsilon/2<b,
\]

so upper enumeration terminates.  The equality case `A_N=a` is correctly sent
to the upper branch and still has strict rational-approximation room.  This
establishes total termination of every supplied-accuracy resolver without an
oracle for `eta(r)`.

### 5. Productive global fork

If `eta(r)>0`, choose a dyadic `epsilon` with
`3 epsilon / 4 < eta(r)`.  The upper branch is then impossible, so that scale
returns a lower certificate.  If `eta(r)=0`, soundness excludes every positive
lower certificate, and every scale returns an upper profile.  Selecting a
dyadic scale below a requested error gives terminal approximate Nash profiles
at every error.  The checked consumer is
`quittingGame_exists_uniformEquilibriumPayoff_of_terminalNash_all_errors` (and
the equivalence version) in
`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`.

There is no claim that consecutive upper profiles share a source, tail, law,
or Bellman chronology.  The all-errors consumer requires none of those.

## Explicit falsification and implementation checks

I attempted to falsify the result at the following boundaries.

1. **After-support deviation.**  The auxiliary finite date detects a player
   who profits only by tying an opponent at the last represented date; Never
   does not replace this check.
2. **All-Never and local inertness.**  On the checked cyclic-plateau
   transcription, the all-Never profile has exact exploitability zero and is
   accepted as an upper certificate.  Thus local all-Continue rigidity cannot
   create a false global lower result.
3. **Unattained semantic points.**  A payload carrying only a semantic pair is
   rejected by the upper-certificate schema.  An upper result must contain the
   four literal marginal laws.
4. **Product provenance.**  A joint-law-only payload is rejected; coalition
   terms are reconstructed from marginals.
5. **False lower certificate.**  A root goal leaf claiming a positive lower
   bound on the zero reward table is rejected.
6. **Direct/formula agreement.**  In addition to the supplied nontrivial
   exact regression, I generated 25 deterministic-seed random normalized
   rational reward tables and product laws at level one.  In every case the
   outer expression equalities, radius inequalities, and objective agreed
   exactly with the independently evaluated finite-clock payoff and cap.

The module compiles with `py_compile`.  The environment has no `pytest`, so I
invoked all nine supplied test functions directly (providing a temporary path
to the one fixture); all nine passed.

One implementation qualification should be recorded.  `ScaleSearch.run` is a
real dovetailed API, but the command-line program currently exposes only
`scale` and `verify`, not the end-to-end search.  Also, tree assembly, JSON
decoding, and verification are recursively implemented and therefore inherit
Python's default recursion-depth limit.  A realistic certificate is likely
to be much deeper than that limit.  Either replace these traversals by
iterative versions or describe this Python package as a reference generator
and verifier for the mathematical certificate language, rather than claiming
that the unmodified CLI robustly checks every finite certificate.  This does
not affect the ordinary mathematical algorithm or a future Lean checker.

## Exact novelty and conjecture-facing change

The checked/exported escape-aware hierarchy already supplies:

- common-quantile compression with exact Never and product provenance;
- finite rational polynomial outer queries;
- the `24/N` Fin4 bracket and convergence;
- actual small finite-clock profiles conditional on zero infimum; and
- a sound Lean verifier for a *supplied* restricted polynomial identity.

The internal note
`CODEX_EULER__QUANTILE_CLOCK_PRODUCTIVE_CERTIFICATE_OR_ALL_ERRORS_FORK.md`
also observed abstractly that real-closed-field decidability gives a productive
fork.  Its independent reviews correctly declined a separate export because
it mostly repackaged the hierarchy and supplied no concrete generator or proof
trace.

The genuinely new content here is narrower and operational:

1. the cumulative hierarchy is replaced, for this purpose, by one explicit
   final-shell expression system;
2. a finite rational interval-tree proof language is defined;
3. sound verification and strict-margin completeness of that language are
   proved;
4. the lower generator is dovetailed with a complete exact rational upper
   enumerator, producing a total resolver at every accuracy; and
5. the resulting positive-gap semidecision and exhaustive rational-table
   counterexample search are proved.

These points remove the items “complete certificate generator,” “certificate-
search completeness theorem,” “proof-trace checker,” and “positive-gap
semidecision procedure” from the list of missing algorithmic layers in
`ESCAPE_AWARE_FIN4_CERTIFICATE_SEARCH.md`.  They do not solve any current
structural Fin4 component.  This is the precise strict boundary change which
supports export.

## Mandatory corrections to the export packet

1. Retitle the result around **exact per-accuracy Fin4 resolution** or
   **positive-gap semidecision**, not the rigid inert input.
2. Remove “This is Output 4” and every assertion that the theorem answers
   `FIN4_INERT_MACHINE_CERTIFICATE_SEARCH.md`.
3. State explicitly that termination is per supplied accuracy.  The global
   zero-gap behavior is productive and infinite, not a terminating zero test.
4. Treat the strict inert object only as a corollary: if such a rational-table
   source with positive minimum is supplied, positivity implies that a later
   scale emits a lower certificate.  The certificate does not encode the
   source and does not consume or contradict it.  “Carried unchanged” means at
   most that the caller may pair its unchanged input with the generic output.
5. Distinguish the ordinary mathematical algorithm from current Python CLI
   ergonomics and recursion limits.
6. Include the exhaustive rational-table semidecision corollary, which is the
   strongest new conjecture-facing conclusion.
7. State that this is a strict narrowing of the general certificate-search
   question, not one of its full terminal Outputs 1--3: no positive table is
   presently exhibited, the zero branch is not decided in finite time, and no
   inert chamber is eliminated.

With those changes, I have no unresolved mathematical objection.

## Lean handoff

The narrow formalization should introduce:

1. a single-shell Fin4 outer predicate using the existing finite-clock center
   presentation;
2. the sandwich
   `eta - 24/N <= singleShellLower N <= eta`;
3. a finite expression syntax with rational constants, variables, addition,
   negation, multiplication, and maximum;
4. rational interval evaluation and its enclosure theorem;
5. binary box trees, exact leaf verification, coverage soundness, and the
   lower-bound theorem;
6. strict-margin completeness under normalized-longest-side dyadic splitting;
7. enumeration of rational finite-clock product laws and density/continuity of
   their exact unrestricted exploitability;
8. the per-epsilon dovetail termination theorem; and
9. the productive dyadic process and rational-table semidecision corollary.

Likely source declarations are:

- `quantileClockSupport_fin4`, `quantileClockRadius_fin4`, and
  `escapeAwareQuantileClock_fin4_normalized_quantitative_bracket` in
  `Research/Quitting/EscapeAwareQuantileClockHierarchy.lean`;
- the forward and reverse cap-transport results in
  `Research/Quitting/EscapeAwareQuantileClockTransport.lean`;
- `finiteClockPolynomialSemanticImage_eq_reachable` and the finite cap graph
  in `Research/Quitting/FiniteClockPolynomialCenter.lean`;
- `quittingTerminalSemanticPair_eq_stoppingLawProfile` in
  `Research/Quitting/FiniteClockTerminalSemantics.lean`; and
- the terminal all-errors consumer in
  `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`.

The export earns ordinary mathematical evidence only.  It should not carry
Lean, adapter, or consumer seals until the corresponding new declarations are
checked.
