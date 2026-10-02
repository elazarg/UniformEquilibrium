# Algorithmic audit of `DECIDE_CONTROLLER_TESTER`

Reviewer: `ALGORITHM_AUDIT`

## Claim audited

The note claims that the escape-aware Fin4 shell construction yields:

1. a decidable finite rational certificate relation, complete for every
   positive terminal-exploitability value of a rational Fin4 table;
2. a terminating exact lower-or-upper search at every requested positive
   rational scale;
3. uniform computability of the value `eta(r)` for rational tables; and
4. a recursively enumerable rational-open cover of the positive-value locus.

I concentrated on computability, quantifiers, strict versus non-strict
boundaries, reward scaling, and the open-cover assertion.

## Verdict

**PASS the normalized per-scale resolver and its fixed-table consequences.
REVISE the arbitrary-scale verifier and open-cover statements before treating
this file as a final theorem statement.**

The central result is sound and already has the right effective content.  For
every normalized rational Fin4 table and every rational `epsilon > 0`, the
explicit stage-by-stage search eventually emits either

\[
 \epsilon/4\leq\eta(r)
\]

with a finite rational interval-tree proof, or an actual rational
finite-clock product profile of unrestricted exploitability below
`3 epsilon / 4`.  This is a genuine algorithm: each stage is computable, the
output relation is decidable, and a theorem proves that sequential stage
enumeration eventually stops.  No oracle comparison with `eta(r)` occurs in
the computation.

The dyadic fixed-table process therefore semidecides `eta(r) > 0`; if
`eta(r)=0`, it produces actual profiles at every accuracy but never produces a
finite certificate of that global zero assertion.  This does not decide the
zero predicate.

## Sources inspected

- `Research/Quitting/FinFourExactScaleResolution.lean`:
  `finFourExactScaleStep`, `exists_finFourExactScaleStep`, and the upper and
  lower soundness theorems;
- `Research/Quitting/FinFourCounterexampleSemidecision.lean`:
  `finFourCounterexampleStep` and
  `exists_finFourCounterexampleStep_iff_exists_real_infimum_pos`;
- `Research/Quitting/FinFourRationalSingleShellLower.lean` and
  `MathUE/Interval/RationalLowerBoxSearch.lean`: exact lower-tree soundness
  and strict-margin completeness;
- `Research/Quitting/FinFourRationalFiniteClockProfile.lean` and
  `Research/Quitting/FinFourRationalFiniteClockProfileCompleteness.lean`:
  upper verification and rational enumeration completeness; and
- `Research/Quitting/TerminalExploitabilityRewardRobustness.lean` and the two
  rational-reward approximation modules: positive homogeneity and the
  `2`-Lipschitz reward bound.

## Points that survive adversarial checking

### 1. The shell inequalities have the correct direction

If `A_N` is the minimum on the radius-`12/N` shell and `V_N` the minimum on
its actual finite-clock centers, then

\[
 A_N\leq\eta(r)\leq V_N,
 \qquad V_N-A_N\leq 24/N.
\]

Thus a lower certificate for `A_N` is a lower certificate against every
behavioral profile.  The auxiliary late date and separate Never coordinate
make the finite menu the true unrestricted cap at a finite-clock center.

### 2. The scale resolver handles equality correctly

For

\[
 N=\lfloor96/\epsilon\rfloor+1,
 \quad a=\epsilon/4,
 \quad b=3\epsilon/4,
\]

one has `24/N < epsilon/4`.

- If `A_N > a`, strict-margin lower completeness closes a finite tree.
- If `A_N <= a`, including `A_N = a`, an actual center has
  exploitability below `a+24/N < epsilon/2 < b`, leaving strict room for
  rational upper approximation.

No equality case is omitted.  A lower tree may incidentally verify at
equality, but its completeness is not needed there.

### 3. The positive-gap quantifiers are correct

If `eta(r)>0`, a sufficiently small dyadic scale has upper threshold below
`eta(r)`, so upper output is impossible and lower output must occur.  If
`eta(r)=0`, soundness excludes every positive lower output.  The latter arm
is productive and infinite, not a finite proof of zero.

A certified non-strict lower bound `epsilon/4 <= eta(r)` does not imply that a
best deviation attains gain exactly `epsilon/4`.  It does imply, for every
profile, an actual deviation of gain strictly above any smaller number, such
as `epsilon/8`.  The note states this correctly.

### 4. Uniform computability of `eta` is a valid derived theorem

At a fixed shell, dovetailing rational lower thresholds and lower trees with
rational upper profiles eventually gives rationals `a < b` satisfying

\[
 a\leq A_N\leq\eta(r)\leq
 \operatorname{Expl}_r(\sigma)<b,
 \qquad b-a<\delta.
\]

The existence proof also works when `A_N=0`: the lower rational `a` may be
negative, or may be replaced afterward by `max(a,0)`.  Therefore `eta(r)` is
a computable nonnegative real uniformly in a normalized rational table.  By
canonical positive rational normalization the conclusion extends to every
rational table.

This is an ordinary mathematical consequence of the checked generators; it
should not be described as a named checked Lean theorem unless such a wrapper
is added.

## Required repairs

### A. The opening verifier changes normalization without defining the wrapper

The note begins with an arbitrary rational table and a relation

\[
 \operatorname{Verify}(r,N,a,\mathcal T),
\]

but the displayed shell radius `12/N`, the `24/N` bracket, and the checked
lower verifier apply to tables bounded by one.  Later prose observes that one
can divide by

\[
 M=\max(1,\lVert r\rVert_\infty),
\]

but it never defines how `N`, `a`, and the tree are transformed in the
opening relation.

There are two clean repairs.

1. State the main verifier theorem only for normalized rational tables, then
   state arbitrary rational tables as a scaling corollary; or
2. define the arbitrary-table verifier to regenerate the normalized problem
   for `r/M` at threshold `a/M`, and conclude `a <= eta(r)` by homogeneity.

Without one of these repairs, a reader could incorrectly apply the normalized
`12/N` shell directly to an unbounded table.

### B. Equation (29) needs the same normalization repair

The checked certificates currently enumerate normalized rational centers.
Balls around only those centers cannot cover the positive locus in the whole
unbounded reward space.  For example, a positive table of very large norm is
not near the normalized cube.

Either write the normalized statement

\[
 \{r:\lVert r\rVert_\infty\leq1,\ \eta(r)>0\}
 =\{r:\lVert r\rVert_\infty\leq1\}\cap
   \bigcup B_\infty(q,a/4),
\]

where `q` ranges over normalized rational certified tables, or first define
the scaled arbitrary-rational certificate wrapper from repair A and let `q`
range over those arbitrary rational tables.

With that wrapper, the global open-cover proof is sound.  In fact the radius
can be strengthened from `a/4` to any strict radius below `a/2`, because

\[
 \eta(r)\geq\eta(q)-2\lVert r-q\rVert_infty
           \geq a-2\lVert r-q\rVert_infty>0.
\]

The conservative radius `a/4` is nevertheless correct.

### C. Distinguish a terminating search from a total Lean return function

`finFourExactScaleStep` is a total computable **stage** function, and
`exists_finFourExactScaleStep` proves classically that some stage emits a
certificate.  Sequentially testing stages is therefore a total algorithm in
the ordinary recursion-theoretic sense.  The repository does not expose a
proof-free total Lean function which returns the first certificate; doing so
by `Classical.choose` would not be executable.

Use wording such as “the explicit sequential stage search terminates” rather
than suggesting that the current API already contains a total executable
resolver value.

### D. The title must not suggest exact zero-decision

The result computes `eta(r)` to arbitrary certified accuracy and
semidecides strict positivity.  It does not decide whether `eta(r)=0` in
finite time.  Therefore it does not answer the direct Fin4 decision question,
although it completely settles the previously missing positive
semidecision/proof-generator layer.

## Final maximal statement

After the normalization wrapper is made explicit, the maximal valid result is:

> The Fin4 terminal-exploitability value is uniformly computable on rational
> reward tables.  Strict positivity is recursively enumerable by finite exact
> all-behavior certificates.  The positive locus is effectively open and is
> covered by recursively enumerable rational certificate balls.  Exact
> equality to zero remains undecided, and no positive table is produced.

I found no endpoint or equality counterexample to this corrected statement.

## Re-audit of the revised note

The revision fixes the principal defect:

\[
\operatorname{Verify}(r,N,a,T)
=
\operatorname{Verify}_{\rm norm}
  (r/M(r),N,a/M(r),T)
\]

is decidable for arbitrary rational `r`, and homogeneity gives both soundness
and strict completeness.  The arbitrary-rational computability argument is
also correct: request normalized accuracy `delta/M(r)` and multiply the
certified interval by `M(r)`.  Equation (29) now quantifies over arbitrary
rational centers carrying these rescaled certificates, so its open-cover and
recursive-enumerability claims are sound.  The status paragraph correctly
separates checked declarations from the three ordinary-mathematics wrappers.

One presentation repair remains in the proof body.  Sections 2--4 reuse the
letter `r` and write

\[
 24/N<\eta(r)-a,
 \qquad
 \operatorname{Verify}(r,N,a,T)\Rightarrow a\le A_N(r),
\]

although those shell formulas have normalized radius `12/N`.  For an
arbitrary table the corresponding normalized statements are

\[
 24/N<\frac{\eta(r)-a}{M(r)},
 \qquad
 \frac a{M(r)}\le A_N(\bar r),
\]

followed by multiplication by `M(r)`.  The simplest correction is to insert
at the start of Section 2: “Until the arbitrary-rational corollaries below,
assume `r` is normalized,” and let the paragraph following (5) discharge the
opening arbitrary-rational theorem by scaling.  Alternatively define
`A_N^{sc}(r)=M(r)A_N(r/M(r))` throughout.

This is residual notation/scope leakage rather than a counterexample to the
result.  After that sentence and the corresponding reference in the
completeness conclusion, I have no remaining mathematical objection.
