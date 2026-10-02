# Review of full-binding pointwise-support diffuse exclusion

Reviewer: `CODEX_ROOT`

## Claim reviewed

For one source-attached Fin4 strict exact-cap ray, assume that the limiting
binding set is all four players and that every normalized current hazard is
strictly positive at all sufficiently late finite dates.  Then no compact
cluster of the current direction, tail-average direction, and renewal ratio
has renewal-ratio limit zero.  Consequently the actual renewal ratios have a
uniform positive eventual lower bound.

## Verdict

**PASS.**  The strengthening is valid and source-faithful.  Its decisive step
is correctly taken before passage to the limit: finite positivity and exact
complementarity make every finite endpoint slack literally zero.  Therefore a
diffuse cluster forces the full normalized-solo matrix equation in all four
rows even if some coordinates of the current-direction limit vanish.

The result strictly strengthens the checked limit-support theorem.  It does
not consume ballistic flow or partial finite support, and the author does not
claim that it does.

## Exact audit

Write `lambda_k`, `Lambda_k`, and `rho_k` for current direction, tail-average
direction, and renewal ratio.  Let `E_k(i)` be the normalized endpoint slack.
The checked certificate gives

\[
E_k(i)\ge0,
\qquad
\lambda_k(i)E_k(i)=0.
\]

Along an arbitrary jointly convergent strict subsequence, eventual finite
full support implies `E_(k_n)(i)=0` for every player and every sufficiently
large rank.  No uniform lower bound on `lambda_(k_n)(i)` is used.

For every binding row, the checked endpoint decomposition has the form

\[
\rho_kE_k(i)
=-G_k(i)-\rho_kC_k(i)+e_k(i),
\]

where `e_k(i)->0`, the collision term `C_k(i)` is bounded under current-state
compactness, and tail-normalized cap flow identifies the limit of `G_k(i)`
with

\[
\sum_j M_{ij}\Lambda(j).
\]

If `rho_(k_n)->0`, the left side is eventually identically zero and
`rho_(k_n) C_(k_n)(i)->0`.  Hence

\[
\sum_jM_{ij}\Lambda(j)=0
\]

for every one of the four rows.  The tail limit is a standard-simplex point,
so it is a homogeneous simplex-LCP solution of the full normalized solo
matrix.  This contradicts the source's checked
`not_hasHomogeneous_fullNormalizedSoloMatrix` theorem.  Full binding is used
exactly where claimed: it supplies the analytic equations on every row and
identifies the matrix with the hard residual's full matrix.

For the source-level corollary, if no positive eventual lower bound on
`rho_k` existed, one could choose a strict subsequence with
`rho_(k_n)<1/(n+1)`.  Compactness supplies a jointly convergent further
subsequence whose ratio limit remains zero, while eventual finite positivity
is inherited.  This contradicts the local result.  The quantifier order is
therefore correct:

\[
\text{fixed source and flow}
\to\text{eventual finite support}
\to\exists\eta>0\text{ eventually }\rho_k\ge\eta.
\]

## Boundary and source checks

- Finite full support does not imply that the limiting current direction has
  full support; the author's explicit simplex sequence correctly separates
  the two hypotheses.
- If a player is absent at infinitely many selected finite dates, its endpoint
  slack need not vanish there, so the proof correctly stops.
- The argument uses actual finite exact-root complementarity before taking a
  limit.  It does not infer complementarity from positivity of a limiting
  coordinate.
- It does not identify a positive ratio limit with a stationary equilibrium;
  the fixed-point payoff identity remains absent.
- It does not use the conditional parity or binding-cardinality certificate.

## Source correspondence

I checked the proof against:

- `QuittingTailNormalizedCapFlow.current_complementarity`,
  `endpoint_decomposition`, `collisionError_tendsto_zero`, and
  `tailNormalized_capFlow` in
  `Research/Quitting/ForwardExactCapTailFlow.lean`;
- the source construction in
  `Research/Quitting/FinFourProducerAtlas/StrictRayTailNormalizedCapFlow.lean`;
- `CompactHazardCluster` and
  `FinFourMinimumAtomProducer.not_hasHomogeneous_fullNormalizedSoloMatrix` in
  `Research/Quitting/FinFourProducerAtlas/StrictRayFullBindingDiffuseReduction.lean`.

The checked compact theorem currently requires positivity of every coordinate
of the **limit** current direction.  The finite-complementarity strengthening
reviewed here is not a restatement of that theorem.

## Lean handoff check

The proposed local theorem should accept eventual positivity along the
selected subsequence, derive eventual slack-zero coordinatewise, and replay
the endpoint-decomposition/tail-flow convergence without multiplying by the
current limit.  The source wrapper then uses a contradiction subsequence to
obtain the positive eventual renewal floor.  No new topological or parity
infrastructure is required.
