# Independent review of `FACE_ENLARGE_FOLLOWUP.md`

Reviewer: Codex Archimedes

Reviewed derivation:
[`../FACE_ENLARGE_FOLLOWUP.md`](../FACE_ENLARGE_FOLLOWUP.md)

Distilled note:
[`../notes/CODEX_ROOT__FACE_ENLARGE_FOLLOWUP_LOCAL_PERIODIC_OBSTRUCTIONS.md`](../notes/CODEX_ROOT__FACE_ENLARGE_FOLLOWUP_LOCAL_PERIODIC_OBSTRUCTIONS.md)

## Verdict by separable result

1. **Minimum-tube Never barrier: mathematically approve after small statement
   repairs.**  The proof covers an unrestricted behavioral deviation because
   `Never` is one literal complete strategy replacement.  Periodicity is not
   actually needed.  The result is a useful local obstruction, but it is not
   independently export-worthy: in a maintained counterexample the terminal
   witness already excludes every terminal approximating family.  It is a
   good `Research` theorem and a useful boundary test for proposed producers.

2. **Solo-anchor prescribed-closure obstruction: approve after explicit
   formal hypotheses.**  This is the important new result.  It assumes no
   Nash or small-exploitability property.  A cyclic prescribed Bellman seam
   which is little-o of total root hazard, with annotations converging to the
   own-singleton vector, forces `M lambda = 0`.  On the Fin4 hard residual,
   whose normal core is all players, this contradicts the checked absence of
   a homogeneous simplex solution.  This repairs the decisive gate failure
   in the earlier regular-clock no-go: it obstructs the chronology producer
   *before* assuming the terminal semantic endpoint.  I regard this result as
   eligible for an export packet after the repairs and boundary tests below,
   provided the packet is framed as the precise no-go for the local
   solo-anchor realization of the `COMP` obligation rather than as a producer
   from `COMP` data.

3. **Scale-free periodic Abel estimate: approve.**  The constant and the lack
   of an explicit period-length factor are correct.  It is a reusable scalar
   lemma, not a standalone export.

4. **Two-clock application: repair the clock statement, then approve.**  The
   exact cap recursion is discounted by the generated Snell secant, not by
   the deleted-opponent Continue mass.  The displayed bound remains valid
   because each generated secant is bounded by that mass, but this comparison
   must be stated.  Periodicity of the chosen generated secants must also be
   an explicit hypothesis or obtained from a canonical periodic selection.
   After this repair, equations (27)--(30) give the advertised all-behavior
   terminal-debt consumer.  Like the earlier fixed-period consumer, it lacks
   an arbitrary-game producer and should not be exported alone.

Section 5's “corrected last-mile theorem” is **not a theorem**.  The preceding
no-go results do not prove the exhaustive alternative (31), do not produce a
macroscopic excursion, and do not route failure to support descent.  It must
remain a requested producer, with the singular deleted-clock regime also
listed as an unresolved possibility.

## 1. Minimum-tube Never barrier

### Exact claim checked

Let `I` have cardinality `n >= 2`.  Let an infinite executable product-root
sequence have Quit probabilities `q_{t,i}`, actual tail payoff `u_t`, joint
Continue mass `beta_t`, and deleted-player Continue mass `beta_{t,-i}`.  Let

\[
s_i=r_i(\{i\}),\qquad |r_i(S)|\le R,
\]

with `R >= 0`.  Assume

\[
u_{t,i}\ge s_i+\eta\quad(t,i),\qquad \eta>0,
\]

\[
\max_{t,i}q_{t,i}
\le {\eta\over2(n-1)(\eta+2R)},
\]

joint survival tends to zero, and every player-deleted survival product tends
to zero.  Then the terminal exploitability of the profile from time zero is
at least

\[
{\eta\over2n}.
\]

The periodic theorem in the derivation is the specialization in which strict
one-period contraction yields both limiting survival hypotheses.

### Recurrence and constants

Let `v_{t,i}` be the payoff after player `i` replaces its whole behavioral
strategy by `Never`, and put `G_{t,i}=v_{t,i}-u_{t,i}`.  Direct subtraction of
the two Bellman equations gives exactly

\[
\begin{aligned}
G_{t,i}={}&\beta_{t,-i}G_{t+1,i}
+q_{t,i}\beta_{t,-i}(u_{t+1,i}-s_i)\\
&+q_{t,i}\sum_{\varnothing\ne T\subseteq I\setminus\{i\}}
 P_{t,-i}(T)[r_i(T)-r_i(T\cup\{i\})].
\end{aligned}
\]

The collision line is at least `-2 R q_{t,i}(1-beta_{t,-i})`.  Also

\[
1-\beta_{t,-i}\le\sum_{j\ne i}q_{t,j}\le(n-1)m.
\]

Thus the stated smallness assumption gives

\[
G_{t,i}\ge\beta_{t,-i}G_{t+1,i}+{\eta\over2}q_{t,i}.
\]

Iteration is legitimate even though `G` need not be nonnegative at the
finite cutoff: terminal payoffs are reward-bounded, and deleted survival
tends to zero, so the bounded remainder vanishes.  Therefore

\[
G_{0,i}\ge {\eta\over2}\sum_{t\ge0}W_{t,-i}q_{t,i}.
\]

With joint survival `W_t`,

\[
\sum_i\sum_tW_{t,-i}q_{t,i}
\ge\sum_tW_t\sum_iq_{t,i}
\ge\sum_tW_t(1-\beta_t)=1.
\]

Some player consequently has Never gain at least `eta/(2n)`.  Since Never is
one admissible complete behavioral replacement, the same lower bound holds
for the unrestricted cap.  No best-response attainment or restriction to
stationary deviations is used.

### Repairs and strengthening

* State `n >= 2` (or split off the one-player case), because the displayed
  hazard threshold contains `n-1` in its denominator.
* State `eta > 0` and `R >= 0` explicitly.
* Say “actual tail payoffs” rather than generic phase annotations.
* The proof works for an arbitrary root sequence; periodicity is only one way
  to supply the two survival limits.
* Deleted contraction is only used for players carrying positive own hazard
  mass.  The all-player formulation is simpler and safe, but is not sharp.
* In the Fin4 application, taking the checked minimum-fiber gap `delta` and
  `eta=delta/2` gives `delta/16`, exactly as claimed.

The deleted-clock boundary is real.  If exactly one owner has the persistent
clock, its opponents' survival need not decay, and the remainder in the
Never recursion need not vanish.  This is the same exceptional-owner seam
isolated elsewhere in the project.

## 2. Solo-anchor prescribed-closure obstruction

### Correct statement

Let `I` be nonempty and finite, and define

\[
M_{ij}=r_i(\{j\})-r_i(\{i\}).
\]

For every index `h`, let `K_h >= 1`, let `x^h_k` be product roots for
`k in Z/K_h Z`, and let `u^h_k` be cyclic payoff annotations.  Write
`q^h_{k,j}` for the Quit hazards and

\[
A_h=\sum_{k<K_h}\sum_jq^h_{k,j}>0,
\qquad Q_{h,j}=\sum_{k<K_h}q^h_{k,j}.
\]

Assume

\[
m_h:=\max_{k,j}q^h_{k,j}\to0,
\qquad
\epsilon_h:=\max_k\|u^h_k-s\|_\infty\to0,
\]

where `s_i=r_i({i})`.  With the sign convention

\[
p^h_{k,i}=u^h_{k,i}-F_i(x^h_k,u^h_{k+1}),
\]

assume

\[
\left\|\sum_{k<K_h}p^h_k\right\|_\infty=o(A_h).
\]

Then, after taking a subsequence,

\[
\lambda_{h,j}:={Q_{h,j}\over A_h}\to\lambda_j,
\qquad \lambda\in\Delta(I),
\]

and

\[
M\lambda=0.
\]

No Nash inequality, debt complementarity, joint-survival assumption, or
behavioral-cap assertion occurs in this theorem.

### Expansion audit

For `a^h_k=sum_j q^h_{k,j}`, the product Bellman map obeys, uniformly in
`k,i`,

\[
F_i(x^h_k,u^h_{k+1})-u^h_{k+1,i}
=\sum_jq^h_{k,j}[r_i(\{j\})-s_i]+e^h_{k,i},
\]

where, for a constant depending only on the finite reward table and an
eventual bound on the annotations,

\[
|e^h_{k,i}|\le
 a^h_k\epsilon_h+C(a^h_k)^2.
\]

This follows by separating singleton terminal coalitions from coalitions of
size at least two.  Singleton product masses differ from the raw hazards by
`O((a_k^h)^2)`, and all collision mass is `O((a_k^h)^2)`.
Furthermore,

\[
\sum_k(a^h_k)^2
\le |I|m_hA_h=o(A_h).
\]

Because the annotations close cyclically,

\[
\sum_k(u^h_k-u^h_{k+1})=0.
\]

Summing the preceding expansion and the definition of `p` therefore gives

\[
MQ_h=-\sum_kp^h_k+o(A_h)
\]

for the stated sign convention.  Division by `A_h` and compactness of the
simplex prove the result.  The opposite convention for `p` merely reverses
the displayed harmless sign before the little-o term.

Since `M lambda=0`, `lambda` is a homogeneous simplex-LCP witness.  In the
Fin4 hard residual, use
`FinFourQuantitativeFullSupportHardResidual.normalCore_eq_univ` to identify
the normal-player matrix in
`ResidualHardClass.no_homogeneous` with the full normalized solo matrix.
Without this equality, the full-matrix conclusion does not directly
contradict a no-homogeneous assertion only on the normal core.

### Boundary tests required in an export packet

1. **The solo anchor is essential.**  Small exact periodic product profiles
   generally converge to a singleton-mixture payoff `v`, not to the vector
   of own singleton rewards.  Exact Bellman closure away from `s` need not
   imply `M lambda=0`.
2. **The relative seam is essential.**  An `O(A_h)` signed period seam can
   cancel a nonzero `M Q_h`; little-o relative closure cannot be weakened to
   an unnormalized seam tending to zero.
3. **Vanishing mesh is essential.**  At nonvanishing hazards, nonsingleton
   coalition rewards enter prescribed payoff at first order and the
   singleton matrix alone does not govern closure.
4. **Sharp positive chamber.**  If all singleton rewards for each recipient
   equal that recipient's own singleton reward, then `M=0`; taking compatible
   nonsingleton rewards gives exact small-hazard cyclic closures, consistent
   with the theorem.

## 3. Scale-free periodic Abel estimate

Let `a_0,...,a_{K-1}` be real, `K>=1`, and let `c_k in [0,1]`.  Set

\[
w_0=1,\quad w_{k+1}=w_kc_k,\quad q=w_K<1,
\]

\[
R=\sum_{k<K}a_k,
\qquad E=\max_{0\le m\le K}\left|\sum_{k<m}a_k\right|.
\]

For the periodic extensions and their survival weights,

\[
\left|\sum_{t\ge0}W_ta_{t\bmod K}\right|
\le E+{|R|\over1-q}.
\]

Indeed, Abel summation on one turn gives

\[
\sum_{k<K}w_ka_k
=w_{K-1}R+
\sum_{m=1}^{K-1}(w_{m-1}-w_m)\sum_{k<m}a_k.
\]

The absolute value is at most

\[
|R|+(1-w_{K-1})E
\le |R|+(1-q)E.
\]

Successive turns are multiplied by `q^r`; division by `1-q` proves the
claim.  Taking the maximum of `E` over cyclic rotations gives a bound valid
from every phase.

This is compatible with, but not already stated by,
`abs_survivalWeightedSum_le_prefixAbsMax` in
`MathUE/Probability/OneSidedDebtShadowing.lean`.  That checked theorem is the
finite Abel engine; the periodic seam-versus-clock-loss specialization is the
new wrapper.

Boundary tests: constant forcing shows the `|R|/(1-q)` term is necessary;
zero-sum forcing concentrated before a clock drop shows the `E` term is
necessary; and `q<1` is indispensable unless both the period sum and the
weighted one-turn sum vanish.

## 4. Correct two-clock application

Use periodic `QuittingChronologicalDebtData` and a periodic generated secant
selection.  For player `i`, write

\[
q_J=\prod_{k<K}\beta_k,
\quad q^s_i=\prod_{k<K}s_{k,i},
\quad q^{-i}=\prod_{k<K}\beta_{k,-i}.
\]

Here `beta` is joint Continue mass, `s` is the generated secant in
`exists_quittingTerminalSemanticPrefix_secant`, and `beta_{-i}` is deleted
Continue mass.  The checked inequality gives

\[
0\le s_{k,i}\le\beta_{k,-i},
\qquad q^s_i\le q^{-i}.
\]

Let `p_{k,i}` be the prescribed defect and `f_{k,i}` the direct debt defect.
The exact recursions in `ChronologicalDebtShadowing.lean` yield

\[
d_i(\sigma)-d_{0,i}
=-\sum_tW^s_{t,i}f_{t,i}
+\sum_t(W^J_t-W^s_{t,i})p_{t,i}.
\]

If `q_J<1` and `q^{-i}<1`, the terminal remainders vanish.  Applying the
scale-free estimate gives the sharp statement

\[
d_i(\sigma)\le d_{0,i}
+\mathcal G_{q^s_i}(f_i)
+\mathcal G_{q^s_i}(p_i)
+\mathcal G_{q_J}(p_i).
\]

Since `q^s_i <= q^{-i}` and
`E+|R|/(1-q)` is increasing in `q`, the convenient deleted-clock version is

\[
\boxed{
d_i(\sigma)\le d_{0,i}
+\mathcal G_{q^{-i}}(f_i)
+\mathcal G_{q^{-i}}(p_i)
+\mathcal G_{q_J}(p_i).}
\]

The prescribed-payoff error separately satisfies

\[
|U_i(\sigma)-u_{0,i}|\le\mathcal G_{q_J}(p_i).
\]

Thus (29)--(30) are sufficient for all terminal debts to vanish, provided
each period has `q_J<1`, `q^{-i}<1`, the candidate initial debts vanish, and
the roots, annotations, defects, and selected secants are genuinely periodic.
The cap is the unrestricted behavioral cap; no periodicity is imposed on the
deviator.

The original prose must not identify the secant clock with the deleted clock.
The latter only supplies an upper bound on the former.

## Source and novelty audit

Declarations inspected:

* `exists_pos_uniformSingletonGap_minimumFiber_of_punishmentNormal` and
  `exists_open_exactAllContinueTube_and_debtMoat_minimumFiber` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticFinFourMinimumFiberIsolation.lean`;
* `normalizedSoloMatrix` in
  `UniformEquilibrium/Quitting/Classification/LCP/Normalization.lean`;
* `HasHomogeneousSimplexSolution` in
  `UniformEquilibrium/Quitting/Classification/LCP/MatrixClasses.lean`;
* `ResidualHardClass.no_homogeneous` and the full-normal-core field of
  `FinFourQuantitativeFullSupportHardResidual`;
* `hasHomogeneousSimplexSolution_principal_of_vanishing_returnedBlocks` in
  `UniformEquilibrium/Quitting/Classification/LCP/ReturnedBlockTangentGap.lean`;
* `exists_quittingTerminalSemanticPrefix_secant`,
  `prescribedError_recursion`, and `bestResponseError_recursion` in
  `UniformEquilibrium/Quitting/Debt/Dynamic/ChronologicalDebtShadowing.lean`;
* `twoDiscountDebtError_eq` and
  `abs_survivalWeightedSum_le_prefixAbsMax` in
  `MathUE/Probability/OneSidedDebtShadowing.lean`.

The closest checked homogeneous-LCP theorem is the returned-block tangent
result.  It assumes vanishing *nonnegative Bellman error plus endpoint
regret*, normalized by total hazard.  The solo-anchor theorem here instead
uses a signed prescribed period seam and the special limiting anchor `s`; it
does not assume endpoint Nash or terminal exploitability.  It is therefore
not a restatement of the checked returned-block theorem.

No paper theorem was invoked.  The arguments are elementary Bellman
expansion and Abel summation.

## Exact repair list

1. Add `n>=2`, `eta>0`, and `R>=0` to the first theorem.
2. Make clear that the first theorem uses actual tail payoffs, not arbitrary
   annotations, and that the cap lower bound is witnessed by the complete
   `Never` deviation.
3. State cyclic indexing and the varying periods `K_h>=1` explicitly in the
   solo-anchor theorem.
4. Define the sign of `p`, the norm, and both little-o hypotheses precisely.
5. Include the summed collision bound
   `sum_k (sum_j q_{k,j})^2 <= |I| m_h A_h` in the proof.
6. In the Fin4 corollary, use `normalCore_eq_univ` before invoking
   `ResidualHardClass.no_homogeneous`.
7. In the two-clock theorem, distinguish `q_i^s` from `q^{-i}` and explicitly
   assume or canonically construct a periodic generated-secant selection.
8. State `q_J<1` and `q^{-i}<1` before using the seam-over-clock-loss ratios.
9. Relabel (31) as the remaining requested producer, not as a consequence or
   exhaustive theorem.  Retain the singular deleted-clock branch explicitly.

## Export-gate recommendation

* **Solo-anchor prescribed-closure no-go:** approve for export after repair,
  preferably as a compact packet tied explicitly to the local realization
  arm left open by `SAME_STAGE_ENDPOINT_MONODROMY_REDUCTION.md`.  Its adapter
  is any proposed cyclic Bellman word satisfying the exact small-mesh,
  solo-anchor, and relative-seam hypotheses; its output is immediately
  contradicted by the checked Fin4 hard-residual `no_homogeneous` field.  Its
  gain over the previously rejected regular-clock no-go is that no terminal
  approximation or Nash premise is assumed.
* **Minimum-tube Never barrier:** retain as a supporting boundary theorem or
  `Research` formalization target; do not export by itself.
* **Scale-free Abel/two-clock consumer:** retain in `revisit/` or formalize in
  `Research`; do not export without a producer from actual conjecture-facing
  data.
* **Alternative (31):** not proved and not exportable.

