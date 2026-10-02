# Full Fin4 binding with eventual finite full support forces ballistic renewal

Author: `CODEX_RIEMANN`

Independent review:

- [`CODEX_ROOT`](../feedback/CODEX_RIEMANN__FULL_BINDING_POINTWISE_SUPPORT_DIFFUSE_EXCLUSION__BY_CODEX_ROOT.md)
- [`CODEX_AMPERE`](../feedback/CODEX_RIEMANN__FULL_BINDING_POINTWISE_SUPPORT_DIFFUSE_EXCLUSION__BY_CODEX_AMPERE.md)

## Exact statement

Fix an actual source-attached Fin4 canonical strict exact-cap ray over a
`FinFourMinimumAtomProducer`.  Let

\[
\lambda_k(i)=\text{normalized current marginal hazard},
\]

\[
\Lambda_k(i)=\text{remaining-tail hazard barycenter},
\qquad
\rho_k=\text{renewal ratio}.
\]

Assume:

1. the limiting binding set is all of `Fin 4`; and
2. the finite current roots are eventually fully supported:

   \[
   \exists K\;\forall k\ge K\;\forall i,\qquad\lambda_k(i)>0.
   \tag{1}
   \]

Then the ray is uniformly ballistic:

\[
\boxed{
\exists\eta>0\;\exists K'\;\forall k\ge K',
\qquad \rho_k\ge\eta.}
\tag{2}
\]

More locally, take any strict subsequence and any one joint compact cluster

\[
\lambda_{k_n}\longrightarrow\lambda,
\qquad
\Lambda_{k_n}\longrightarrow\Lambda,
\qquad
\rho_{k_n}\longrightarrow\rho.
\tag{3}
\]

It is enough to assume finite full support eventually along this subsequence.
Then

\[
\boxed{\rho>0.}
\tag{4}
\]

No positive lower bound on the individual finite hazards is assumed.  In
particular, the limiting current direction `lambda` may lie on the boundary
of the simplex.

## Proof

Let `E_k(i)` be the normalized endpoint slack supplied by the checked
tail-normalized cap-flow certificate.  At every finite date, exact root
complementarity gives

\[
E_k(i)\ge0,
\qquad
\lambda_k(i)E_k(i)=0.
\tag{5}
\]

Under eventual finite full support, (5) gives the literal finite identity

\[
\boxed{E_{k_n}(i)=0}
\tag{6}
\]

for every player and every sufficiently large subsequence rank.  This is the
essential strengthening: complementarity is used before any coordinate of
the current direction can vanish in the limit.

Let

\[
M_{ij}=r_i(\{j\})-r_i(\{i\})
\tag{7}
\]

be the normalized solo matrix.  On a binding row, the checked endpoint
decomposition has the form

\[
\rho_kE_k(i)
=-G_k(i)-\rho_kC_k(i)+e_k(i),
\tag{8}
\]

where `C_k(i)` is the collision-matrix expression in the current direction,
`e_k(i)->0`, and the checked tail-normalized cap-flow identity gives

\[
G_{k_n}(i)\longrightarrow
\sum_jM_{ij}\Lambda(j).
\tag{9}
\]

Suppose for contradiction that the selected cluster is diffuse, `rho=0`.
The current directions live in a compact simplex, so `C_(k_n)(i)` is bounded.
Equations (6) and (8) then have an eventually zero left side, while

\[
\rho_{k_n}C_{k_n}(i)\longrightarrow0,
\qquad e_{k_n}(i)\longrightarrow0.
\]

Together with (9), this yields

\[
\boxed{\sum_jM_{ij}\Lambda(j)=0}
\qquad(i\in\operatorname{Fin}4).
\tag{10}
\]

Full binding makes (8)--(9) available in every row and identifies `M` with
the hard residual's full normalized solo matrix.  The tail limit is a literal
simplex point:

\[
\Lambda(j)\ge0,
\qquad
\sum_j\Lambda(j)=1.
\tag{11}
\]

Thus (10)--(11) give a homogeneous simplex-LCP solution of the full normalized
solo matrix.  This contradicts the retained hard residual's checked
`not_hasHomogeneous_fullNormalizedSoloMatrix`.  Hence `rho` is nonzero; its
nonnegativity gives (4).

To prove (2), suppose no positive eventual lower bound existed.  Recursively
choose a strict subsequence with

\[
\rho_{k_n}<\frac1{n+1}.
\]

Compactness gives a jointly convergent further subsequence.  Its ratio limit
is zero, and eventual finite full support remains true along it, contradicting
(4).

## Conjecture-facing change

The checked compact full-binding reduction only excludes a diffuse cluster
whose **limiting** current direction is positive at all four players.  That
condition can fail even when every finite exact root is fully supported.

The present theorem removes that gap.  Diffuse full binding can survive only
if at least one player is literally absent from infinitely many sufficiently
late finite current roots.  Merely letting finite positive hazards tend to
zero is not enough.  Equivalently, eventual finite full support places the ray
in the uniformly ballistic branch.

This is a strict reduction of the full-binding ray obligation.  It does not
consume the surviving ballistic branch or the partial-finite-support branch.

## Probability and strategy-class audit

The ray consists of actual finite product roots chosen exact against the full
behavioral terminal caps of their successor semantic pairs.  Equation (5) is
finite exact endpoint complementarity, not complementarity inferred from a
limit.  The cap-flow and collision identities retain the actual ray and its
minimum source.  No stationary profile, bounded stopping-time deviation, or
cap attainment is inserted.

The conclusion is only a statement about the renewal ratios of that actual
ray.  A positive ratio limit is not called a stationary equilibrium because
the required fixed-point payoff identity is not supplied.

## Source correspondence

The proof uses:

- `QuittingTailNormalizedCapFlow.current_complementarity`,
  `endpoint_decomposition`, `collisionError_tendsto_zero`, and
  `tailNormalized_capFlow` in
  `Research/Quitting/ForwardExactCapTailFlow.lean`;
- `FinFourStrictRayForwardExactCapTail` and its `analysis` in
  `Research/Quitting/FinFourProducerAtlas/StrictRayTailNormalizedCapFlow.lean`;
- `CompactHazardCluster`, `nonempty_compactHazardCluster`, and
  `FinFourMinimumAtomProducer.not_hasHomogeneous_fullNormalizedSoloMatrix` in
  `Research/Quitting/FinFourProducerAtlas/StrictRayFullBindingDiffuseReduction.lean`.

The existing checked theorem proves only

```text
diffuse cluster + full limiting current support + full binding -> False.
```

The new content is the finite-level complementarity upgrade and the uniform
source-level ballistic corollary (2).

## Boundary tests

Finite full support need not survive in the limiting current direction.  For
example, with

\[
\varepsilon_k=\frac1{(k+1)^2},
\qquad
\delta_k=\frac1{4(k+2)},
\]

put

\[
\lambda_k=(1-3\delta_k,\delta_k,\delta_k,\delta_k).
\]

Every finite vector has four positive coordinates, while
`lambda_k -> e_0`.  The associated scalar renewal ratios may tend to zero.
This normalized-sequence example is not asserted to satisfy the exact cap-flow
equations; it shows exactly why the old limit-support hypothesis is stronger
than (1).

If one player is absent at infinitely many selected finite dates, (6) is no
longer available for that row.  The proof correctly gives no conclusion in
that branch.

## Adapter and consumer

The actual-data adapter is the checked
`FinFourStrictRayForwardExactCapTail` produced from the strict positive-hazard
maximal ray, together with its checked `analysis` and the hard residual stored
by the incoming `FinFourMinimumAtomProducer`.

The output is a strict source-retaining dispatch:

\[
\text{eventually full finite support}
\Longrightarrow
\text{uniformly ballistic flow}.
\]

It permanently removes diffuse fully supported flow.  The next consumer must
handle either uniformly ballistic full binding or a subsequence with a fixed
omitted finite current player.

## Lean handoff

1. For a supplied compact cluster and eventual subsequence positivity, use
   `analysis.normalized.current_complementarity` to derive eventual
   coordinatewise endpoint-slack zero.
2. Combine `endpoint_decomposition`, `collisionError_tendsto_zero`, and
   `tailNormalized_capFlow` to obtain (10) without multiplying by the current
   limit.
3. Reindex the resulting full matrix equation through the already checked
   `not_hasHomogeneous_fullNormalizedSoloMatrix` adapter.
4. Prove the source wrapper by contradiction: a failure of an eventual
   positive lower bound selects ratios tending to zero, then compactness gives
   the forbidden cluster.

No parity, component-index, stationary, or new compactness infrastructure is
needed.

## Scope and nonclaims

- No terminal approximants or uniform-equilibrium payoff are produced.
- No positive-gap reward table is constructed.
- Ballistic flow is not consumed.
- A positive exact root at a cap limit is not identified with a stationary
  return.
- Binding cardinality three is not treated as player deletion.
- Partial finite current support remains open.

## Formalization record

This packet is formalized in
`Research/Quitting/FinFourProducerAtlas/FullBindingPointwiseSupportBallistic.lean`.

The generic declarations
`QuittingTailNormalizedCapFlow.subseq_scaledEndpointSlack_tendsto` and
`subseq_diffuse_eventually_currentHazard_pos_solo_eq_zero` combine the exact
finite endpoint decomposition with complementarity before taking a limit.
For any binding coordinate whose finite current hazard is eventually positive
along a supplied strict convergent subsequence, zero renewal-ratio limit forces
the corresponding homogeneous solo-flow row to vanish.  No positivity of the
limiting current coordinate is required.

For a source-attached `FinFourStrictRayForwardExactCapTail`,
`FinFourOwnerCompressedMinimumReturnForcedPairPacket.compactCluster_ratioLimit_pos_of_eventually_all_currentHazard_pos`
applies that row identity simultaneously to every player under full binding.
The hard residual's checked
`FinFourMinimumAtomProducer.not_hasHomogeneous_fullNormalizedSoloMatrix`
then proves that every compact cluster with eventual finite full support has
strictly positive ratio limit.

`FinFourOwnerCompressedMinimumReturnForcedPairPacket.eventually_renewalRatio_ge_pos_of_fullBinding_of_eventually_all_currentHazard_pos`
is the same-flow global theorem.  It turns failure of an eventual positive
renewal-ratio floor into a strict subsequence tending to zero, compactifies a
further refinement, and contradicts the universal cluster theorem.  Finally,
`eventually_renewalRatio_ge_pos_or_exists_frequently_currentHazard_eq_zero`
gives the literal source-level dispatch: under full binding, the same actual
strict ray is uniformly ballistic or one fixed player has zero current hazard
infinitely often.

Evidence seals:

- **M:** PASS.  Exact finite complementarity is used before the limit, so the
  proof retains the packet's stronger pointwise-support quantifier and does
  not assume a positive limiting current direction.
- **L:** PASS.  The generic subsequence lemmas, arbitrary-cluster Fin4 theorem,
  same-flow eventual lower bound, and source-level ballistic-or-omitted-player
  dispatch are checked Lean declarations.
- **A:** PASS relative to the packet's explicit branch hypotheses.  The Fin4
  theorems retain the actual `FinFourStrictRayForwardExactCapTail`, its packet,
  minimum source, normalized analysis, and full binding.  Neither full binding
  nor eventual finite full support is manufactured.
- **C:** Not present.  Uniformly ballistic renewal and recurrent omission of a
  finite current player remain unconsumed branches.

The module is reachable through
`Research/Quitting/FinFourExhaustiveProducerAtlas.lean` and the `Research`
reader umbrella.  It proves no positive exact root at the limiting cap,
stationary return, player deletion, terminal approximation, rank decrease,
uniform-equilibrium payoff, or counterexample.  Partial finite support remains
open, and no lower bound on any individual positive finite hazard is asserted.
