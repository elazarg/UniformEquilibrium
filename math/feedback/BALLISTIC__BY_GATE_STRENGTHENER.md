# Independent strengthening review of BALLISTIC

## Verdict

**FAIL for export in its current role.**  The cocycle averaging argument is a
correct and useful normalized compactness theorem after two small statement
repairs:

1. the two displayed outputs are not mutually exclusive, so “exactly one”
   must be replaced by “either,” or by an implication from failure of the
   boundary arm; and
2. failure of a boundary subsequence yields a uniform interior lower bound
   only after deleting a finite prefix, not necessarily at every original
   index.

With those repairs, the sharp theorem is dimension-free and stronger than the
document states: it has finite approximate certificates, the effective ratio
is a weighted average of the ratios in the selected block, and the fixed
ratio may be confined to the asymptotic range of the original ratios.

The existing Research atlas also supplies a genuine conditional actual-source
adapter: a full-binding strict Fin4 ray with eventually positive current
hazards produces the source-compatible normalized omega chain to which this
theorem applies.  What is not supplied is a consumer.  The boundary arm is
only vanishing normalized current along a subsequence, not literal player
omission or debt-support descent.  The interior arm is only a kernel of
`M+rJ`; it has no absolute hazard scale, cap/payoff pair, exact product root,
Bellman seam, or behavioral chronology.  A checked matrix-level regression
already shows that such an augmented fixed state is compatible with a hard
solo matrix having no homogeneous simplex kernel.

Accordingly, this result compresses the normalized omega-chain scaffold, but
it is precisely the kind of unconsumed ballistic split excluded as an answer
by `questions/FIN4_STRICT_NORMALIZED_INERT_IMPOSSIBILITY_OR_MODEL.md`.

## 1. Corrected sharp theorem

Let `I` be finite.  Let `M,J : I -> I -> R`, let `0 < eta <= 1`, and let

\[
(\lambda_n,\Lambda_n,\rho_n)
 \in\Delta(I)\times\Delta(I)\times[\eta,1]
\]

satisfy

\[
\Lambda_n
=\rho_n\lambda_n+(1-\rho_n)\Lambda_{n+1}
\tag{R}
\]

and

\[
\lambda_{n,i}
\bigl(M\Lambda_n+\rho_nJ\lambda_n\bigr)_i=0
\qquad(n\in\mathbb N, i\in I).
\tag{C}
\]

The inequality

\[
M\Lambda_n+\rho_nJ\lambda_n\le0
\]

is part of the ballistic relation but is not used in the collapse theorem.
Complementarity (C) is the operative hypothesis.

Then

\[
\boxed{
\liminf_{n\to\infty}\min_i\lambda_{n,i}=0
\quad\text{or}\quad
\exists r,y\;[
r\in[\eta,1],\ y\in\Delta(I),\ y_i>0,\ (M+rJ)y=0].}
\tag{1}
\]

Equivalently, if no fixed coordinate tends to zero along a strict
subsequence, then the second arm holds.  Because `I` is finite, the first arm
is equivalent to the existence of a player `i` and strict subsequence `n_k`
with

\[
\lambda_{n_k,i}\longrightarrow0.
\]

The word “or” in (1) is inclusive.  It cannot be strengthened to an exclusive
dichotomy.

If the second arm is obtained, `r` may moreover be chosen in the closed
asymptotic range

\[
r\in[\liminf_n\rho_n,\limsup_n\rho_n].
\tag{2}
\]

For the normalized ballistic relation, `(y,y,r)` is then an exact stationary
state: renewal is tautological and its work vector is zero.

### Minimal hypotheses

The sign inequality on work is unnecessary for (1).  The simplex
normalizations, renewal identity, complementarity equality, finite player
set, and positive ratio floor are sufficient.  The ratio floor is used twice:
it keeps the constructed `r` away from zero and turns a current interior
floor into an interior tail-average floor.

## 2. Finite cocycle certificate

The limiting theorem follows from a stronger finite statement.

Assume, after shifting the sequence if necessary, that

\[
\lambda_{n,i}\ge\delta>0
\qquad(n\ge0, i\in I).
\tag{3}
\]

Then complementarity gives

\[
M\Lambda_n+\rho_nJ\lambda_n=0,
\tag{4}
\]

and renewal gives

\[
\Lambda_{n,i}\ge\eta\delta.
\tag{5}
\]

For every cutoff `N` and `epsilon>0`, compact recurrence supplies
`N <= a < b` with

\[
\|\Lambda_a-\Lambda_b\|\le\varepsilon.
\tag{6}
\]

If some `rho_n=1` after the cutoff, (R) gives
`Lambda_n=lambda_n`, and (4) directly yields the fixed state with `r=1`.
Otherwise put

\[
g_n=1-\rho_n,
\quad
q=\left(\prod_{n=a}^{b-1}g_n\right)^{1/(b-a)},
\quad
r=1-q,
\tag{7}
\]

and define

\[
\alpha_a=1,
\qquad
\alpha_{n+1}=\frac{\alpha_ng_n}{q}.
\tag{8}
\]

Then `alpha_b=1`.  With

\[
A=\sum_{n=a}^{b-1}\alpha_n\Lambda_n,
\quad
B=\sum_{n=a}^{b-1}\alpha_n\rho_n\lambda_n,
\quad
Z=\sum_{n=a}^{b-1}\alpha_n,
\tag{9}
\]

the exact telescopes are

\[
B=rA+q(\Lambda_a-\Lambda_b),
\qquad
MA+JB=0.
\tag{10}
\]

Put

\[
y=A/Z,
\qquad
e=\frac qZ(\Lambda_a-\Lambda_b).
\tag{11}
\]

Then

\[
y\in\Delta(I),
\qquad
y_i\ge\eta\delta,
\tag{12}
\]

and

\[
\boxed{(M+rJ)y=-Je.}
\tag{13}
\]

For any fixed norm and its induced operator norm,

\[
\boxed{
\|(M+rJ)y\|
\le\|J\|\,\|\Lambda_a-\Lambda_b\|
\le\|J\|\varepsilon.}
\tag{14}
\]

There is also an exact provenance identity omitted from the packet.  Summing
the coordinates in the first equality of (10) gives

\[
\boxed{
r=\frac{\sum_{n=a}^{b-1}\alpha_n\rho_n}
        {\sum_{n=a}^{b-1}\alpha_n}.}
\tag{15}
\]

Thus `r` is a positive-weighted average of the actual ratios in the block;
in particular it lies between their minimum and maximum.  If

\[
z=\frac{B}{rZ}\in\Delta(I),
\]

then

\[
z-y=e/r,
\qquad
\|z-y\|\le\varepsilon/\eta.
\tag{16}
\]

So the certificate says more than approximate kernel membership: one
weighted average of actual current directions and one weighted average of
actual tail directions coalesce quantitatively.

Choose recurrent blocks with `a -> infinity` and endpoint error tending to
zero.  Compactness of `[eta,1] x Delta(I)` and (12)--(15) gives a limit
`(r,y)` satisfying (1) and (2).

## 3. Corrections to the stated proof

### The alternatives are not exclusive

Take two players, `M=J=0`, `rho_n=1`, and

\[
\lambda_n=\Lambda_n=
\left(\frac1{n+2},1-\frac1{n+2}\right).
\]

All hypotheses hold.  The first coordinate tends to zero, while every
positive simplex vector `y` and every `r` give an ambient fixed state.  Both
outputs hold simultaneously.  Therefore “exactly one” is false.

The proof establishes the correct asymmetric statement: **if the boundary
arm fails, then an interior fixed state exists**.

### The interior floor is eventual

Failure of a strict subsequence tending to zero does not rule out an isolated
zero or very small coordinate at an early index.  It yields

\[
\exists N,\delta>0\quad
\forall n\ge N,\forall i,\quad\lambda_{n,i}\ge\delta.
\]

Shift to `N` before applying the proof.  This is sufficient because the
construction uses arbitrarily late recurrent blocks.

### Recurrence blocks must be cofinal

Compactness gives pairs of close tail states in every sufficiently late
tail, so the blocks can and should be chosen with `a_k -> infinity`.  This is
what justifies the asymptotic-range refinement (2) and preserves tail-source
provenance.

## 4. Source adapter

The theorem is not source-free in the current project, but its actual adapter
is conditional on a named strict-ray branch.

From one
`FinFourStrictRayForwardExactCapTail`, assume:

* full limiting binding; and
* eventual positivity of all four finite current normalized hazards.

`eventually_renewalRatio_ge_pos_of_fullBinding_of_eventually_all_currentHazard_pos`
in
`Research/Quitting/FinFourProducerAtlas/FullBindingPointwiseSupportBallistic.lean`
produces `eta>0` and an eventual ratio floor on that same ray.

`nonempty_ballisticNormalizedOmegaChain_of_fullBinding_of_eventually_all_currentHazard_pos`
in
`Research/Quitting/FinFourProducerAtlas/BallisticNormalizedOmegaChain.lean`
then produces one source-compatible omega chain.  Its forward half has

\[
\lambda_n=\text{current normalized hazard},
\quad
\Lambda_n=\text{tail hazard average},
\quad
\rho_n=\text{renewal ratio},
\]

with

\[
M=\operatorname{normalizedSoloMatrix}(r),
\qquad
J=\operatorname{quittingCollisionMatrix}(r).
\]

The checked declarations `renewal`, `work_nonpos`, and
`current_work_eq_zero` give (R) and (C).  Thus the corrected theorem gives the
source-attached normalized alternative

\[
\boxed{
\text{one omega-current coordinate approaches zero}
\quad\text{or}\quad
\exists r,y>0\;(M+rJ)y=0.}
\tag{17}
\]

This source attachment is real but limited.  In the first arm, diagonal use
of `source_current_tendsto` recovers actual ray dates at which one normalized
current coordinate tends to zero.  It does not make that coordinate exactly
zero.  In the second arm, `sourceFiniteWindow_tendsto` lets each fixed finite
cocycle block be approximated by literal consecutive windows of the same
actual ray.  The resulting `r,y` is nevertheless a weighted limit, not an
actual ray state.

The atlas theorem
`eventually_renewalRatio_ge_pos_or_exists_frequently_currentHazard_eq_zero`
has a distinct second arm: one player has **exactly zero** current hazard
infinitely often.  The boundary arm in (17) is weaker and must not be
identified with it.

## 5. What the fixed state does and does not imply

The fixed certificate is the finite semialgebraic system

\[
r\in[\eta,1],
\qquad
y_i>0,
\qquad
\sum_i y_i=1,
\qquad
(M+rJ)y=0.
\tag{18}

For Fin4, a necessary scalar condition is

\[
\det(M+rJ)=0,
\tag{19}
\]

a polynomial equation in `r` of degree at most four, together with positivity
of a kernel vector.  Therefore (18) is finitely and exactly screenable from a
reward table.

This screen gives two valid conditional consequences:

* if (18) has no solution, a uniformly interior ballistic normalized chain is
  impossible, so the boundary arm must occur; and
* if additionally `Jy=0` for every candidate produced by (18), then `My=0`,
  contradicting the hard residual's absence of a homogeneous simplex kernel.

Neither condition follows from the current hard residual.

The checked regression in
`Research/Quitting/BallisticNormalizedSelectedChainRegression.lean` is the
decisive boundary test.  Its solo matrix has no homogeneous simplex solution
and retains the paired-singleton hard matrix properties, while the explicit
collision matrix satisfies

\[
(M+\tfrac12J)y=0
\]

at the uniform positive vector.  The same normalized relation also carries a
uniformly interior aperiodic selected chain.  Hence neither hard solo-matrix
geometry nor aperiodicity excludes (18).

Even an exact solution of (18) is not:

* an absolute product hazard vector;
* an exact root against one cap vector;
* an attained semantic pair;
* a Bellman return block; or
* a terminal approximate equilibrium.

Choosing a small absolute hazard scale from `y` only cancels the first-order
endpoint equations.  The exact product residual is quadratic, and no
nondegeneracy, implicit-function, cap matching, or source-return theorem is
present to remove it.

## 6. Boundary tests and necessity

### Uniform current interior is essential

Let `I={1,2}`, take a constant state

\[
\lambda_n=\Lambda_n=(1,0),
\qquad \rho_n=\eta,
\]

put `J=0`, and choose

\[
M=\begin{pmatrix}0&0\\0&1\end{pmatrix}.
\]

Renewal and complementarity hold, but no strictly positive simplex vector is
in the kernel of `M`.  This is exactly the boundary arm.

### Complementarity is essential

With any constant interior simplex state, take `M=-I` and `J=0`.  Work is
strictly negative, so feasibility alone holds, but no positive vector solves
`My=0`.  The equality `lambda_i W_i=0`, not merely `W<=0`, drives the proof.

### The positive ratio floor controls the output

The cocycle argument without a positive floor can at best return `r=0` or a
boundary `y`; it does not yield the collision-corrected interior certificate
needed in the ballistic branch.  Quantitatively, (5), (12), and (16) all use
`rho_n>=eta>0`.

### A normalized fixed state is not an absolute lift

The selected-chain regression above supplies an exact fixed normalized state
but explicitly no actual quitting ray or Bellman realization.  The
zero-minimum maximal-ray regressions in
`Research/Quitting/FinFourMaximalRayZeroMinimumRegressions.lean` further show
that actual ballistic/full-binding local geometry does not itself contradict
existence of an equilibrium.  Positive-minimum source provenance must enter
any terminal consumer.

## 7. Downstream consumer audit

### What is complete

The corrected theorem eliminates the need to retain an arbitrary aperiodic
omega-chain as terminal normalized data.  Under uniform interiority, it
compresses the chain to the finite system (18), with the stronger finite
certificates (13)--(16).  This is a complete normalized algebraic reduction.

### What remains open

For the boundary output, one still needs a theorem that converts asymptotic
vanishing of one normalized current coordinate into one of:

* literal omission with source preservation;
* a regenerated support/rank decrease; or
* a charged/terminal consumer.

For the fixed-state output, one needs either:

* an exact source-faithful absolute lift to a product-root Nash--Bellman
  return;
* a hard-residual theorem excluding every positive solution of (18); or
* a new finite-rank transition generated directly from the augmented kernel.

No such theorem is currently present.  In particular, the existing
homogeneous-kernel obstruction applies to `My=0`, not to `(M+rJ)y=0`.

Therefore the result does not eliminate the strict normalized inert SCC,
construct terminal approximants, produce a uniform-equilibrium payoff, or
realize a positive-gap counterexample.

## 8. Lean handoff

The reusable generic statement should not be tied to quitting games.  A
possible interface is:

```text
ballisticRenewal_exists_boundarySubseq_or_interiorAugmentedKernel
  (lambda tail : Nat -> stdSimplex R I)
  (rho : Nat -> Icc eta 1)
  (renewal : ...)
  (complementarity : ...)
  :
  (exists i subseq, StrictMono subseq /\
     Tendsto (lambda (subseq n) i) atTop (nhds 0))
  \/
  exists r : Icc eta 1, exists y : stdSimplex R I,
    (forall i, 0 < y i) /\
    forall i, matrixApply (M + r • J) y i = 0
```

Do not state this as `Xor`.

Separate the finite calculation:

```text
ballisticCocycleBlock_identity
ballisticCocycleBlock_ratio_eq_weightedAverage
ballisticCocycleBlock_residual_le_endpointDistance
```

The Fin4 adapter should live at the normalized-chain level:

```text
FinFourBallisticNormalizedOmegaChain.nonempty_boundaryCurrent_or_fixedState
```

and return a structure storing either the source-coordinate subsequence or
the ratio, positive simplex kernel, block approximants, and source finite
windows.  It must not claim `HasAbsoluteNashBellmanLift`.

Useful exact tests are:

* the zero-matrix example above, showing the alternatives overlap;
* the boundary `diag(0,1)` example;
* the checked aperiodic selected-chain regression, which should return its
  uniform fixed state with `r=1/2`; and
* a constant fixed chain, for which a one-date `rho=1` shortcut should avoid
  geometric-weight division by zero.

## 9. Export gate

### PASS conditions

The packet could pass the named strict-inert question only if the source
adapter is followed by at least one of:

1. consumption of both outputs into terminal approximants, a uniform payoff,
   or a positive admissible return;
2. a source-preserving renewable finite-rank transition for both outputs;
3. a proof that the complete positive-minimum hard residual excludes both
   outputs; or
4. an actual four-player positive-gap realization.

Alternatively, a separate question would have to explicitly accept
compression of a supplied normalized omega-chain to (18) as its completed
answer.  The current question expressly rejects another unconsumed ballistic
split.

### Current FAIL conditions

* “Exactly one” is false as written.
* The proof's interior floor is only eventual until the sequence is shifted.
* The boundary output is asymptotic vanishing, not literal omission or rank
  descent.
* The fixed output is normalized and averaged, with no absolute cap/root or
  Bellman lift.
* The collision correction `rJy` is not removed by the hard residual.
* The checked hard-matrix regression realizes the augmented fixed state, so
  the normalized algebra alone cannot be a contradiction.
* No downstream consumer closes either branch.

The right disposition is to retain this as a strong normalized reduction,
formalize it in Research if useful, and ask separately for the absolute lift
or finite augmented-kernel exclusion.  It should not enter `exports/` as a
conjecture-facing completion.
