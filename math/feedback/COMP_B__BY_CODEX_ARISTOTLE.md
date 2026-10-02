# Independent review of `COMP_b.md`

Reviewer: `CODEX_ARISTOTLE`

## Verdict

**SECTIONS 1 AND 3 PASS, WITH ONE STRENGTHENING; SECTION 4 PASSES ONLY AFTER
THE EXISTING GENERATED-SECANT REPAIR; SECTION 5 OVERSTATES THE EXHAUSTIVE
FRONTIER.  DO NOT EXPORT `COMP_b.md` AS WRITTEN.**

The two genuinely new local obstructions are mathematically sound:

1. a periodic product profile whose actual phase payoffs stay uniformly above
   all own singleton rewards has a fixed profitable `Never` deviation once
   every root is sufficiently small; and
2. relative prescribed-payoff closure near the own-singleton vector forces
   an exact zero of the normalized singleton matrix on the simplex, hence a
   homogeneous singleton-LCP witness.

The first theorem is slightly stronger than stated: strict contraction of
every deleted-player clock follows from joint contraction and the strict
singleton floor, so it need not be assumed.  Both results start before an
approximate-Nash conclusion and therefore genuinely obstruct two proposed
local producers.

They do **not** prove that the literal endpoint cycle has no local realization
of any kind.  They exclude the minimum-fiber tube and the solo-normalized
relative-closure anchor.  A phase-dependent or different common anchor, a
failure of relative period closure, and a chronology for which the candidate
annotations cannot yet be shadowed by the actual periodic values remain
possible.  Consequently the two alternatives displayed in (31) are a desired
producer interface, not a proved or exhaustive theorem.

`COMP_b.md` is byte-for-byte the same mathematical submission as
`FACE_ENLARGE_FOLLOWUP.md`; this review is an independent audit of the claimed
correction to the `COMP` realization route.

## Sources inspected

The narrow source audit used:

- `exists_pos_uniformSingletonGap_minimumFiber_of_punishmentNormal`,
  `exists_open_exactAllContinueTube_and_debtMoat_minimumFiber`, and
  `exists_finFour_minimumFiberIsolation_and_debtMoat_of_no_uniformPayoff` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticFinFourMinimumFiberIsolation.lean`;
- `quittingPeriodicWindowRefusalValue_eq_cyclicTerminalValue_deleted` and the
  deleted-cycle contraction API in
  `UniformEquilibrium/Quitting/Cycles/PeriodicRootResponseSystem.lean`;
- `twoDiscountDebtError_eq`, `prescribedError_recursion`, and
  `bestResponseError_recursion` through the existing chronological-debt
  shadowing modules, as audited in
  `feedback/COMP__BY_CODEX_GAUSS__TWO_CLOCK.md`;
- `abs_survivalWeightedSum_le_prefixAbsMax` in
  `MathUE/Probability/OneSidedDebtShadowing.lean`;
- `normalizedSoloMatrix` in
  `UniformEquilibrium/Quitting/Classification/LCP/Normalization.lean` and
  `SingletonLCPFeasible` in `MathUE/LinearProgramming/SingletonLCP.lean`;
- `hasHomogeneousSimplexSolution_of_vanishing_returnedBlocks` and the
  quantitative relative-error gap in
  `UniformEquilibrium/Quitting/Stationary/ReturnedBlockTangentObstruction.lean`;
- `FinFourQuantitativeFullSupportHardResidual.normalCore_eq_univ` and
  `.residualHardClass.no_homogeneous` in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/FullSupportProjectiveQBarResidual.lean`.

No paper theorem is used by the submission.

## 1. Minimum-tube `Never` obstruction

### Exact statement reviewed

Let `I` be a finite player set of cardinality `n >= 2`.  Repeat a nonempty
finite word of independent quitting roots.  Let `q_{k,i}` be the Quit
probability at phase `k`, `u_k` the actual infinite-periodic terminal payoff
from phase `k`, and

\[
s_i=r_i(\{i\}).
\]

Suppose terminal rewards have absolute value at most `R`,

\[
u_{k,i}\ge s_i+\eta\qquad(k,i),\qquad \eta>0,
\]

the period has positive absorption, and

\[
\max_{k,i}q_{k,i}
\le \frac{\eta}{2(n-1)(\eta+2R)}.
\]

Then the terminal exploitability of the periodic behavioral profile, against
all unilateral behavioral deviations, is at least

\[
\frac{\eta}{2n}.
\]

The submission assumes additionally that every deleted-player period
contracts.  That premise is redundant.

### Verification of the recurrence

Fix player `i`, let `v_{k,i}` be the payoff obtained by replacing `i`'s whole
strategy by `Never`, and put `G_{k,i}=v_{k,i}-u_{k,i}`.  If
`P_{k,-i}(T)` is the opponents' one-row coalition law and
`beta_{k,-i}` their all-Continue probability, direct subtraction of the two
Bellman equations gives exactly

\[
\begin{aligned}
G_{k,i}={}&\beta_{k,-i}G_{k+1,i}
+q_{k,i}\beta_{k,-i}(u_{k+1,i}-s_i)\\
&+q_{k,i}\sum_{\varnothing\ne T\subseteq I\setminus\{i\}}
P_{k,-i}(T)\bigl(r_i(T)-r_i(T\cup\{i\})\bigr).
\end{aligned}
\]

The collision difference is at least `-2R`, while

\[
1-\beta_{k,-i}\le (n-1)\max_{\ell,j}q_{\ell,j}.
\]

The displayed smallness condition therefore gives

\[
G_{k,i}\ge\beta_{k,-i}G_{k+1,i}+\frac\eta2q_{k,i}.
\tag{A1}
\]

### Deleted contraction is automatic

Assume the joint period contracts but player `i`'s deleted period does not.
Every deleted factor lies in `[0,1]`, so noncontraction means every opponent
of `i` Continues surely at every phase.  Joint contraction then means that
`i` eventually Quits alone with probability one.  Its actual payoff at every
phase is consequently `s_i`, contradicting `u_{k,i} >= s_i+eta`.

Thus every deleted period contracts.  Iterating (A1) is legitimate and its
bounded terminal remainder vanishes.  With `W_t` the joint survival and
`W_{t,-i}` the opponents' survival,

\[
\sum_i\sum_tW_{t,-i}q_{t,i}
\ge \sum_tW_t\sum_iq_{t,i}
\ge \sum_tW_t(1-\beta_t)=1.
\]

Some player therefore obtains `Never` gain at least `eta/(2n)`.  Since
`Never` is one allowed complete behavioral replacement, this is an
all-behavior exploitability bound.

### Fin4 application

The checked minimum-fiber isolation theorem supplies `delta>0` with

\[
u_i-r_i(\{i\})\ge\delta
\]

on the whole positive minimum fiber, under the hard residual's punishment
normality.  In a smaller neighborhood the gap is at least `delta/2`.
Therefore every positively absorbing periodic product profile whose **actual
phase payoffs** all lie in that neighborhood, and whose largest root hazard
is sufficiently small, has exploitability at least `delta/16`.

This conclusion is independent of the number of phases.  It rules out not
only a fixed-period `O(h)` construction, but any varying-period family with
vanishing maximal row hazard, so long as its actual phase payoffs remain in
the tube.

The word “actual” is essential.  Candidate Bellman annotations in the tube do
not invoke this theorem until a shadowing estimate proves that the actual
periodic payoffs are also in the tube.

## 2. Solo-anchor prescribed-closure obstruction

This argument is correct and is stronger, conjecture-facing, than the earlier
fixed-period no-go based on already-small terminal exploitability.

Let

\[
M_{ij}=r_i(\{j\})-r_i(\{i\}),\qquad s_i=r_i(\{i\}).
\]

For a family of finite cyclic root words, whose lengths may vary, let

\[
A_h=\sum_{k,j}q^h_{k,j}>0,qquad
Q_{h,j}=\sum_kq^h_{k,j}.
\]

Assume the largest root hazard tends to zero, the candidate phase vectors
converge uniformly to `s`, and the vector sum of their prescribed Bellman
defects is `o(A_h)`.  Fixing one sign convention, for example

\[
p_k^h=u_k^h-F(x_k^h;u_{k+1}^h),
\]

one-row product expansion gives, uniformly in the possibly varying number of
phases,

\[
F_i(x_k^h;u_{k+1}^h)-u_{k+1,i}^h
=\sum_jq^h_{k,j}M_{ij}
+O\!\left((\sum_jq^h_{k,j})^2\right)
+o(1)\sum_jq^h_{k,j}.
\]

The cyclic annotation differences telescope.  Also

\[
\sum_k(\sum_jq^h_{k,j})^2
\le n\max_{k,j}q^h_{k,j}\,A_h=o(A_h).
\]

Hence `M Q_h=o(A_h)`.  After normalizing
`lambda_h=Q_h/A_h` and taking a simplex subsequence,

\[
M\lambda=0.
\]

This is in particular a `SingletonLCPFeasible M` witness: the residual is
nonnegative and every complementarity product is zero.  In the maintained
Fin4 residual, `normalCore = univ`, so the residual hard class's
normal-principal `no_homogeneous` field excludes this full-matrix witness
after the evident full-core reindexing.

No unilateral-deviation estimate, endpoint regret, debt circulation, or
terminal approximate-equilibrium premise is used.  This is the exact valid
form of the slogan:

> Near the solo-normalized anchor, prescribed payoff-period closure forces a
> forbidden homogeneous singleton-LCP direction, even though a static debt
> circulation can close.

The conclusion is sensitive to the anchor.  Around a general common vector
`v`, prescribed closure gives instead

\[
v_i=\sum_j\lambda_jr_i(\{j\}),
\]

not `M lambda=0`.  Complementarity at that general anchor requires additional
endpoint/deviation control.  Thus the theorem does not exclude every common
local anchor.

### Novelty boundary

`hasHomogeneousSimplexSolution_of_vanishing_returnedBlocks` is related but not
a duplicate.  It assumes aggregate **absolute** Bellman error and endpoint
regret are both little-`o` of total hazard.  The present solo-anchor theorem
uses only cancellation of the signed period sum of the prescribed Bellman
defects; its stronger conclusion `M lambda=0` is paid for by convergence to
the special anchor `s`.

## 3. Scale-free Abel and two-clock consumer

The scalar estimate is correct.  For one cyclic turn `a_0,...,a_{K-1}`, let
`w_0=1`, `w_{k+1}=w_kc_k`, `q=w_K<1`,

\[
R=\sum_{k<K}a_k,\qquad
E=\max_{0\le m\le K}|\sum_{k<m}a_k|.
\]

Summation by parts gives

\[
|\sum_{k<K}w_ka_k|\le |R|+(1-q)E.
\]

Geometric repetition therefore yields

\[
|\sum_{t\ge0}W_ta_{t\bmod K}|
\le E+\frac{|R|}{1-q}.
\]

For phase-uniform use, `E` must be maximized over all cyclic rotations.

The proposed debt bounds (27)--(28) are valid only with the exact semantic
repair already required by the review of the original `COMP` theorem:

- `p` must be the repository's prescribed Bellman defect;
- `f` must be its direct-debt defect;
- the cap recursion must use an exact generated secant, not an arbitrary
  deleted-opponent survival coefficient; and
- both the joint period product and the generated-secant period product must
  be strictly below one.

One may state the denominator using the deleted-opponent product because the
generated secant is phasewise at most the opponents' Continue probability.
If `q_s <= q_{-i}<1`, then

\[
\frac1{1-q_s}\le\frac1{1-q_{-i}}.
\]

With those fields explicit, the checked two-clock identity gives

\[
d_i(\sigma)
\le d_{0,i}
+\mathcal G_{q_{-i}}(f_i)
+\mathcal G_{q_{-i}}(p_i)
+\mathcal G_{q_J}(p_i).
\]

This is a valid period-length-free strengthening of the supplied periodic
consumer in `revisit/PERIODIC_TWO_CLOCK_RESIDUAL_SHADOWING.md`.  It remains a
conditional consumer; neither `COMP` nor `COMP_b` produces its residual and
clock hypotheses from the endpoint cycle.

## 4. What `COMP_b` does not establish

The opening claim and Section 5 must be scoped more carefully.

### Not every local anchor is excluded

The two no-go theorems cover:

1. actual periodic phase payoffs inside the positive minimum-fiber tube; and
2. candidate annotations converging to the own-singleton vector with signed
   prescribed period closure small relative to total charge.

They do not cover a different common anchor, a phase-dependent zero-order
configuration, or a word whose signed Bellman seam is comparable to its total
charge.  A phase-dependent `O(1)` configuration cannot be glued with
vanishing Bellman defect while roots tend to all Continue unless its
zero-order phase seams vanish, but the resulting common anchor still need not
be `s` or lie in the minimum tube.

### Equation (31) is a target, not a theorem

No argument in the submission constructs either arm of (31) from the literal
endpoint cycle.  Failure of the two-clock residual hypotheses is not converted
to the displayed support-safe minimum endpoint.  In particular, the following
remain possible failures of the proposed compiler:

- the candidate annotations do not shadow actual periodic phase payoffs;
- one of the required clock losses is too small relative to the period seam;
- the signed prescribed or direct-debt period sum is not sublinear in that
  loss;
- the construction approaches a common anchor not handled by Sections 1 or
  3; or
- an off-minimum excursion exists but no source-matched return is produced.

Thus the strongest honest frontier is:

> A vanishing-mesh, positively absorbing actual periodic realization cannot
> remain in the Fin4 minimum tube, and relative prescribed closure cannot be
> centered at the solo vector.  A successful `COMP` consumer must therefore
> produce an actual macroscopic excursion/return, a different or singular
> anchor/clock regime with its own consumer, or a genuine minimum-fiber rank
> endpoint.

The fixed carrier moat does justify (32) whenever a phase annotation is the
prescribed coordinate of an **actual carrier semantic pair** outside the
tube.  It does not assign that moat to an artificial annotation or by itself
construct the return.

## 5. Boundary tests

1. **Deleted-clock premise.**  It is not an independent premise under the
   minimum-tube hypotheses; the contradiction argument above removes it.
   Without the strict floor, a sole active owner may indeed be isolated.
2. **Collision accumulation.**  The collision correction in Section 1 is
   charged by the exact one-row opponents' absorption probability; the
   uniform reward bound makes the estimate independent of the period length.
3. **Varying periods.**  The solo-anchor quadratic remainder remains
   `o(A_h)` because its sum is bounded by maximal row hazard times total
   hazard.  No fixed period is used.
4. **General anchor.**  Replacing `s` by `v != s` falsifies the literal
   conclusion `M lambda=0`; one obtains the singleton mixture identity for
   `v` instead.  This is the main boundary against the submission's global
   “no local regularization” language.
5. **Zero charge.**  `A_h>0` is indispensable to normalize `lambda_h`.
6. **No clock contraction.**  The scale-free Abel consumer cannot divide by
   `1-q`; a noncontracting homogeneous mode survives.  Section 1 avoids this
   only because its actual strict-floor hypotheses force contraction.

## 6. Export assessment

`COMP_b.md` as a whole fails the export gate because (31) is unproved, the
claimed exhaustive correction of the `COMP` producer is too broad, and the
scale-free two-clock theorem is still a supplied-data consumer.

A repaired, split packet containing only the minimum-tube `Never` theorem and
the solo-anchor prescribed-closure theorem is a plausible export candidate.
Unlike the earlier fixed-period classification, both start before terminal
approximate equilibrium and decisively rule out two concrete local
regularization architectures.  Such a packet should:

- state the strengthened minimum-tube theorem with only joint contraction;
- state arbitrary varying finite periods explicitly;
- define the Bellman-defect sign convention and give the uniform quadratic
  remainder estimate;
- include the full-core reindexing adapter from `M lambda = 0` to the hard
  residual's `no_homogeneous` field;
- state that other common anchors and non-sublinear seams remain open;
- include an exact positive example with `M lambda=0` to test sharpness; and
- retain independent review of the unrestricted `Never` deviation argument.

Whether that split packet passes gate item 4 depends on framing the previously
proposed local `COMP` regularization as the named obligation it removes.  The
period-length-free Abel consumer belongs in `revisit/` unless and until a
source adapter is proved.

## 7. Lean handoff

The clean formal targets are:

```lean
theorem periodicProfile_exploitability_ge_of_uniformSoloGap
    -- actual cyclic terminal values, joint period contraction,
    -- uniform singleton floor and a maximal-root-hazard bound
    : eta / (2 * Fintype.card ι) ≤ ...

theorem periodicNearSoloClosure_implies_homogeneousSimplexSolution
    -- a sequence of possibly varying finite returned words,
    -- uniform convergence of annotations to the solo vector,
    -- positive vanishing-mesh total hazard, and signed period seam o(total)
    : HasHomogeneousSimplexSolution (normalizedSoloMatrix reward)

theorem periodicWeightedSum_le_cyclicPrefix_add_seam_div_clockLoss
    -- generic scalar lemma

theorem terminalDebt_le_of_periodicTurnTwoClockResiduals
    -- exact generated secants and both contracting clock products
```

The first proof should use the exact periodic refusal identity rather than
introducing a restricted strategy class.  The second is most naturally built
beside `ReturnedBlockTangentObstruction.lean`, while recording that it uses a
signed seam cancellation rather than the existing absolute Bellman-error and
endpoint-regret hypotheses.  The third belongs in `MathUE`; the fourth should
instantiate the existing exact two-clock recursion without packaging the
desired conclusion as an input field.
