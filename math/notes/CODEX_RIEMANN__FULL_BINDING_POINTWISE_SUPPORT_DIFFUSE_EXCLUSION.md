# Full binding plus pointwise full current support excludes diffuse strict flow

Author: `CODEX_RIEMANN`

## Status

This note proves an ordinary-mathematics strengthening of the checked compact
full-binding reduction.  It is not checked in Lean.

The existing theorem excludes a diffuse compact cluster when the **limiting**
current-hazard direction is positive at every player.  The limit-positivity
hypothesis is stronger than necessary.  Positivity at every selected finite
date already makes the exact endpoint slack zero before passage to the limit.
Consequently a full-binding hard-residual ray with eventually full current
support cannot have any diffuse compact cluster, even when its normalized
current hazards converge to the boundary of the simplex.

Equivalently, such a ray has an eventual positive lower bound on its renewal
ratio and is ballistic.  This is a genuine reduction, not a terminal
consumer: ballistic full binding, positive exact limit roots, and cardinality-
three binding remain unconsumed.

## Question

Let an actual Fin4 canonical strict ray lie over a quantitative full-support
hard residual.  Suppose its limiting binding set is all four players and its
selected normalized current-hazard vector has all four coordinates positive
at every sufficiently late date.  Can the renewal ratio tend to zero, or even
have a subsequence tending to zero?

The answer is no.

## Sources inspected

- `QuittingForwardExactCapTail`, `QuittingTailNormalizedCapFlow`,
  `subseq_collision_nonpos`, `subseq_collision_complementarity`, and
  `subseq_diffuse_positiveCurrent_solo_eq_zero` in
  `Research/Quitting/ForwardExactCapTailFlow.lean`;
- `tailNormalizedCapFlow` in
  `Research/Quitting/ForwardExactCapTailFirstOrder.lean`;
- `FinFourStrictRayForwardExactCapTail` and its `analysis` in
  `Research/Quitting/FinFourProducerAtlas/StrictRayTailNormalizedCapFlow.lean`;
- `CompactHazardCluster`, `nonempty_compactHazardCluster`,
  `not_ratioLimit_eq_zero_and_all_currentLimit_pos_of_fullBinding`, and
  `FinFourMinimumAtomProducer.not_hasHomogeneous_fullNormalizedSoloMatrix` in
  `Research/Quitting/FinFourProducerAtlas/StrictRayFullBindingDiffuseReduction.lean`;
- `FinFourQuantitativeFullSupportHardResidual` in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/FullSupportProjectiveQBarResidual.lean`.

The present proof uses only these named interfaces.  It does not use the
conditional binding-cardinality/parity certificate.

## 1. Exact hypotheses and quantifier order

Fix a source-attached flow

\[
\mathcal F:
\texttt{FinFourStrictRayForwardExactCapTail(packet)}
\]

and write

\[
\lambda_k(i)=\mathcal F.\mathrm{currentHazard}(k,i),
\quad
\Lambda_k(i)=\mathcal F.\mathrm{tailAverage}(k,i),
\quad
\rho_k=\mathcal F.\mathrm{renewalRatio}(k).
\]

Let

\[
M_{ij}=r_i(\{j\})-r_i(\{i\})
\]

be the checked normalized solo matrix.  Assume:

1. the limiting binding set is full:

   \[
   \mathcal F.\mathrm{bindingFinset}=\operatorname{Fin}4;
   \tag{H1}
   \]

2. finite current support is eventually full:

   \[
   \exists K\;\forall k\ge K\;\forall i,
   \quad \lambda_k(i)>0.
   \tag{H2}
   \]

Now choose a strict subsequence `k_n` and one joint compact cluster

\[
\lambda_{k_n}\to\lambda,qquad
\Lambda_{k_n}\to\Lambda,qquad
\rho_{k_n}\to\rho.
\tag{H3}
\]

The conclusion is

\[
\boxed{\rho>0.}
\tag{T1}
\]

The order is important.  The flow and its source are fixed first; the
eventual positivity is a statement about the actual finite roots; then an
arbitrary jointly convergent strict subsequence is selected.  No positive
lower bound on the coordinates of `lambda_k` is assumed.  In particular,
some or all coordinates may converge to zero.

The minimal subsequence-level hypothesis is even weaker than (H2): it is
enough that

\[
\forall^\infty n\;\forall i,\quad \lambda_{k_n}(i)>0.
\tag{H2'}
\]

## 2. Finite positivity kills the slack before the limit

Let `E_k(i)` be the exact normalized endpoint slack in the checked
`QuittingTailNormalizedCapFlow`.  At every date and player, exact root
complementarity says

\[
\lambda_k(i)E_k(i)=0,
\qquad E_k(i)\ge0.
\tag{1}
\]

Under (H2'), this gives the literal finite-level identity

\[
\boxed{E_{k_n}(i)=0}
\tag{2}
\]

for every player and every sufficiently large `n`.

This is the step missed by a limit-only use of complementarity.  Passing
first to

\[
\lambda(i)\,E(i)=0
\]

loses (2) whenever `lambda(i)=0`.  The finite exact identity does not.

## 3. Diffuse clustering forces the full homogeneous equation

For a binding player `i`, the checked endpoint decomposition is

\[
\rho_kE_k(i)
=-G_k(i)-\rho_k C_k(i)+e_k(i),
\tag{3}
\]

where

\[
G_k(i)=
\frac{\bar b_i-b_{k,i}}{T_k},
\qquad
C_k(i)=\sum_jJ_{ij}\lambda_k(j),
\]

and the collision error satisfies `e_k(i) -> 0`.  The checked normalized cap
flow gives

\[
G_k(i)-\sum_jM_{ij}\Lambda_k(j)\longrightarrow0.
\tag{4}
\]

Assume for contradiction that the selected cluster is diffuse, `rho=0`.
Along `k_n`, equation (2) makes the left side of (3) identically zero.  The
current directions converge in the compact cluster, so `C_(k_n)(i)` is
bounded and indeed convergent.  Hence

\[
\rho_{k_n}C_{k_n}(i)\longrightarrow0.
\]

Equations (3)--(4), the tail convergence in (H3), and `e_(k_n)(i)->0` now
give

\[
\boxed{\sum_jM_{ij}\Lambda(j)=0}
\qquad(i\in\operatorname{Fin}4).
\tag{5}
\]

Full binding is used here twice: it makes (3)--(4) available for every row of
the full matrix, and it identifies that matrix with the hard residual's full
normalized solo matrix.

The tail limit is a literal simplex point:

\[
\Lambda(j)\ge0,qquad \sum_j\Lambda(j)=1.
\tag{6}
\]

Equations (5)--(6) make `Lambda` a homogeneous simplex-LCP solution of `M`:
every row is zero, hence both nonnegativity and complementarity hold.  This
contradicts

```text
FinFourMinimumAtomProducer.not_hasHomogeneous_fullNormalizedSoloMatrix
```

obtained from the retained hard residual.  Therefore `rho` cannot be zero.
Since every renewal ratio is nonnegative, (T1) follows.

Notice that the proof never assumes `lambda(i)>0`.  It works even for a
boundary current limit.

## 4. Source-level ballistic corollary

Under (H1)--(H2), every compact cluster has positive ratio limit.  Compactness
then gives the stronger sequential conclusion

\[
\boxed{
\exists\eta>0\;\exists K'\;\forall k\ge K',
\quad \rho_k\ge\eta.}
\tag{7}
\]

Indeed, if no such `eta` existed, recursively choose a strict subsequence
`k_n` with `rho_(k_n)<1/(n+1)`.  Compactness of the current/tail/ratio state
gives a further jointly convergent strict subsequence.  Its ratio limit is
zero, while (H2) remains eventual along it, contradicting Section 3.

Thus the exact source-facing split is

\[
\boxed{
\begin{array}{c}
\text{full limiting binding}\
+\ \text{eventually full finite current support}
\end{array}
\Longrightarrow
\text{uniformly ballistic renewal ratio}.}
\tag{8}
\]

This does not consume the ballistic branch.  It only proves that the diffuse
full-support branch is impossible.

## 5. Why this is stronger than limit-positive support

Finite full support does not imply a full-support cluster.  For example, let

\[
\varepsilon_k=\frac1{(k+1)^2},
\qquad
\lambda_k=(1-3\delta_k,\delta_k,\delta_k,\delta_k),
\qquad
\delta_k=\frac1{4(k+2)}.
\tag{9}
\]

Every coordinate of every `lambda_k` is strictly positive,
`sum epsilon_k<infinity`, and

\[
\rho_k=\frac{\varepsilon_k}{\sum_{h\ge k}\varepsilon_h}\longrightarrow0.
\]

Nevertheless `lambda_k -> e_0`, and its weighted tail averages also converge
to `e_0`.  Thus no compactness argument may replace (H2) by positivity of the
cluster limit.

The new proof succeeds because (H2) is used at the finite exact
complementarity equation (1), before the vanishing coordinates are lost.
This example is only a normalized-sequence regression, not an actual quitting
ray or a positive-gap table.

## 6. Lean-facing target

The local lemma should avoid requiring a positive current limit:

```lean
theorem not_ratioLimit_eq_zero_of_fullBinding_of_eventually_subseq_current_pos
    (cluster :
      QuittingForwardExactCapTail.CompactHazardCluster flow.forward)
    (hbinding : flow.forward.bindingFinset = Finset.univ)
    (hpositive : ∀ᶠ rank in atTop, ∀ who : Fin 4,
      0 < flow.forward.currentHazard (cluster.subseq rank) who) :
    cluster.ratioLimit ≠ 0
```

Its proof should use:

- `analysis.normalized.current_complementarity` to obtain finite slack zero;
- `analysis.normalized.endpoint_decomposition`;
- `analysis.normalized.tailNormalized_capFlow`;
- `cluster.current_tendsto`, `cluster.tail_tendsto`, and
  `cluster.ratio_tendsto`;
- `analysis.normalized.collisionError_tendsto_zero`; and
- `source.not_hasHomogeneous_fullNormalizedSoloMatrix`.

The source wrapper is then:

```lean
theorem eventually_renewalRatio_ge_pos_of_fullBinding_of_eventually_current_pos
    (flow : FinFourStrictRayForwardExactCapTail packet)
    (hbinding : flow.forward.bindingFinset = Finset.univ)
    (hpositive : ∀ᶠ time in atTop, ∀ who : Fin 4,
      0 < flow.forward.currentHazard time who) :
    ∃ eta > 0, ∀ᶠ time in atTop,
      eta ≤ flow.forward.renewalRatio time
```

The first theorem is the essential mathematical adapter.  The second is a
compactness/strict-subsequence corollary and must preserve the order
`flow -> eventual support -> eta -> eventual dates`.

## 7. Scope and remaining boundary

This result does not consume:

- a positive-absorption exact root at the limiting cap;
- a proper binding face of cardinality three;
- full binding with partial finite current support; or
- the ballistic branch produced by (7).

It proves no terminal approximants, chronological return, renewable finite
rank, uniform-equilibrium payoff, or positive-gap counterexample.  Its exact
conjecture-facing change is narrower: **diffuse full binding can survive only
by losing at least one current player at infinitely many sufficiently late
finite roots; merely converging toward a boundary is not enough when every
finite root remains fully supported.**

## Next question

In the remaining full-binding branch, can maximum absorption force eventual
full current support, or can a fixed omitted current player be converted into
a source-faithful codimension-one handoff?  Either implication would connect
the present diffuse exclusion to an existing finite branch; neither follows
from the normalized-flow interface alone.
