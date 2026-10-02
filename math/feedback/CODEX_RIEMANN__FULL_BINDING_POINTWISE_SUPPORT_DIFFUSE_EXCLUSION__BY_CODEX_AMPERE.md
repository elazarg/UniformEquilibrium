# Review of full-binding pointwise-support diffuse exclusion

Reviewer: `CODEX_AMPERE`

## Verdict: PASS

The finite-level complementarity argument, the homogeneous normalized-solo
limit, and the source-level uniform-ballistic corollary are mathematically
correct.  The compact vector is not a carrier-only semantic artifact: it is a
dependent cluster of one actual `QuittingForwardExactCapTail`, which retains
the strict ray, forced-pair packet, and positive-minimum source.

The essential order of operations is valid:

1. finite current positivity gives finite endpoint slack exactly zero;
2. only then is the diffuse compact limit taken;
3. the resulting tail-hazard barycenter is a literal simplex vector; and
4. the hard residual's source-indexed no-homogeneous theorem applies to that
   vector.

I found no lost source field, exchanged quantifier, or strategy-class issue.

## Claim checked

Let an actual source-attached strict Fin4 forward exact-cap tail have full
binding.  Suppose that along a strict subsequence

\[
\rho_{k_n}\to0
\]

and every finite current hazard is positive at every player eventually along
that same subsequence:

\[
\forall i\;\forall^\infty n,\qquad\lambda_{k_n}(i)>0.
\]

Then the remaining-tail hazard limit `Lambda` solves

\[
M\Lambda=0,qquad \Lambda\ge0,qquad\sum_i\Lambda_i=1,
\]

for the table's full normalized solo matrix `M`.  This contradicts the hard
residual.  Consequently eventual finite full current support forces an
eventual positive lower bound on the renewal ratio.

## 1. Exact finite complementarity

The checked normalized-flow certificate has, at every actual date and player,

\[
E_k(i)\ge0,
\qquad
\lambda_k(i)E_k(i)=0.
\]

Finite positivity `lambda_(k_n)(i)>0` therefore gives

\[
E_{k_n}(i)=0
\tag{1}
\]

exactly for all sufficiently large `n`.  No positivity of the limiting
current direction is needed.  This is the substantive strengthening over the
already checked `subseq_diffuse_positiveCurrent_solo_eq_zero`, whose public
hypothesis is positivity after taking the limit.

## 2. Diffuse endpoint equation

Write

\[
A_k(i)=
\frac{b_\infty(i)-b_k(i)}{T_k}
\]

for the normalized cap gap, and let `C_k(i)` be the collision expression.  The
checked endpoint decomposition is

\[
\rho_kE_k(i)=-A_k(i)-\rho_kC_k(i)+e_k(i).
\tag{2}
\]

The current directions lie in the compact simplex and the collision matrix
is fixed, so `C_(k_n)(i)` is bounded.  Along the selected diffuse subsequence,

\[
\rho_{k_n}C_{k_n}(i)\to0,
\qquad e_{k_n}(i)\to0.
\]

Using the finite equality (1) in (2) gives

\[
A_{k_n}(i)\to0.
\tag{3}
\]

The checked tail-normalized cap-flow identity says

\[
A_{k_n}(i)-\sum_jM_{ij}\Lambda_{k_n}(j)\to0.
\tag{4}
\]

Compact convergence of the tail averages, together with (3)--(4), yields

\[
\sum_jM_{ij}\Lambda(j)=0
\qquad\text{for every }i.
\tag{5}
\]

Full binding is used to make (2)--(4) available in every row and to identify
the solo matrix with the hard residual's full normalized solo matrix.

## 3. The limit is a literal forbidden simplex vector

`CompactHazardCluster` stores its tail coordinate in `stdSimplex`.  Hence,
without a separate realization or closure assertion,

\[
\Lambda(j)\ge0,
\qquad
\sum_j\Lambda(j)=1.
\tag{6}
\]

Equations (5)--(6) produce the forbidden homogeneous simplex solution.
The checked source theorem
`FinFourMinimumAtomProducer.not_hasHomogeneous_fullNormalizedSoloMatrix`
uses the same retained minimum source and the literal full-core reindexing.
Thus this is not an independently selected matrix or a supplied external
simplex vector.

## 4. Source-level uniformity

If the renewal ratios had no eventual positive lower bound, recursively
choose actual dates `k_n` with

\[
\rho_{k_n}<1/(n+1).
\]

Eventual full finite current support remains valid on this subsequence.
Compactness of the actual normalized states supplies a dependent further
cluster with ratio limit zero.  Sections 1--3 give a contradiction.  Therefore

\[
\exists\eta>0\;\forall^\infty k,\qquad\rho_k\ge\eta.
\]

All subsequences are selected from the one incoming ray.  The flow stores
`pair_eq`, `root_eq`, and `source_eq`, so no source-faithful adapter is missing
at this step.

## 5. Scope

The conclusion is ballisticity only.  It does not turn normalized hazards
into literal positive product roots, construct a stationary or periodic
Nash--Bellman block, or consume the partial finite-current-support branch.
Those limitations in the author note are necessary.

The Lean implementation at the time of this review already contains the
dependent compact-cluster and positive-**limit**-support reduction in
`Research/Quitting/FinFourProducerAtlas/StrictRayFullBindingDiffuseReduction.lean`.
The incremental formal target is the finite-positive-support use of
`current_complementarity` before passing to the limit, followed by the source-
level contradiction selection above.
