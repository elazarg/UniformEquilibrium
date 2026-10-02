# Tail-normalized cap flow of a summable exact quitting ray

Author: `CODEX_BOREL`

Independent review:
[CODEX_STOKES](../feedback/CODEX_BOREL__STRICT_RAY_TAIL_NORMALIZATION__BY_CODEX_STOKES.md)

The source-derived normalized-flow core is checked in Lean.
`QuittingForwardExactCapTail.tailNormalizedCapFlow` in
`Research/Quitting/ForwardExactCapTailFirstOrder.lean` constructs the exact
first-order certificate, and
`FinFourOwnerCompressedMinimumReturnForcedPairPacket.eventualAllContinue_or_nonempty_strictRayForwardExactCapTail`
plus `FinFourStrictRayForwardExactCapTail.analysis` in
`Research/Quitting/FinFourProducerAtlas/StrictRayTailNormalizedCapFlow.lean`
attach it to the actual source-selected Fin4 ray.  These declarations give
the cap convergence, eventual binding support, renewal identity, normalized
solo/collision limits, and complementarity with `M`, `L`, and `A`.

The positive limiting-root arm now also has branch-local `C` in
`Research/Quitting/FinFourProducerAtlas/StrictRayPositiveRootReturn.lean`.
`FinFourStrictRayCapLimitJointLaw.nonempty` selects a compact joint-law point
from the same executable ray with cap exactly `capLimit`, and
`FinFourStrictRayPositiveRootReturn.nonempty_minimumLawHandoff_or_offMinimumDescent`
returns either a fresh same-residual minimum source at the exact prefixed point
or a strict off-minimum point whose debt lies between `D_*` and the ray limit.

The packet is not fully formalized as written.  Its separately displayed pure
remote-coalition and all-Never formulas (6)--(7) are not exposed by the
integrated theorem surface, and there is no quantitative or renewable consumer
for the strict off-minimum descent.  The cardinal-three, ballistic, and
omitted-player outputs also remain open.  Revisit this packet when those
literal identities or one of those source-retaining consumers is needed; the
checked normalized-flow and positive-root-return layers need no repair.

## Exact statement

Let `I` be a nonempty finite player set and

\[
 r:\{C\subseteq I:C\ne\varnothing\}\longrightarrow\mathbb R^I
\]

a quitting reward table.  Write

\[
 s_i=r_i(\{i\}).
\]

Let

\[
 z_k=(u_k,b_k),\qquad z_{k+1}=T_{q_k}z_k
\]

be the canonical maximal semantic prefix orbit.  Thus each `q_k` is a
maximum-absorption product root among the roots which are exact Nash against
the unrestricted behavioral cap vector `b_k`.
For its marginal Quit probabilities put

\[
 x_{k,i}=\Pr_{q_k}(i\text{ Quits}),
 \quad
 \varepsilon_k=\sum_i x_{k,i},
 \quad
 a_k=1-\prod_i(1-x_{k,i}).
\]

Assume

\[
 \sum_ka_k<\infty
\]

and that the orbit is not eventually all Continue.  After deleting a finite
initial segment, `epsilon_k>0` and every `x_(k,i)<1`.  Define

\[
 \lambda_{k,i}=x_{k,i}/\varepsilon_k.
\]

Then:

1. the cap vector converges to some `bar b`, and

   \[
   \bar b_i\ge s_i;
   \]

2. if

   \[
   A=\{i:\bar b_i=s_i\},
   \]

   then every sufficiently late root hazard is supported on `A`;

3. for the zero-diagonal matrices

   \[
   M_{ij}=r_i(\{j\})-s_i,
   \qquad
   J_{ij}=r_i(\{i,j\})-r_i(\{j\})
   \quad(i\ne j),
   \]

   define

   \[
   T_k=\sum_{h\ge k}\varepsilon_h,
   \quad
   \rho_k=\varepsilon_k/T_k,
   \quad
   \Lambda_k=\frac1{T_k}
      \sum_{h\ge k}\varepsilon_h\lambda_h.
   \]

   Then, for every `i in A`,

   \[
   \boxed{
   \frac{\bar b_i-b_{k,i}}{T_k}
      =(M\Lambda_k)_i+o(1).}
   \tag{1}
   \]

4. along every subsequence on which

   \[
   \lambda_k\to\lambda,
   \qquad
   \Lambda_k\to\Lambda,
   \qquad
   \rho_k\to\rho,
   \]

   one has, on `A`,

   \[
   \boxed{-M\Lambda-\rho J\lambda\ge0,}
   \tag{2}
   \]

   \[
   \boxed{
   \lambda_i(M\Lambda+\rho J\lambda)_i=0,}
   \tag{3}
   \]

   and the exact finite-level renewal identity

   \[
   \boxed{
   \Lambda_k=\rho_k\lambda_k+(1-\rho_k)\Lambda_{k+1}.}
   \tag{4}
   \]

In the diffuse case `rho=0`, if `lambda_i>0` for every `i in A`, then

\[
 (M\Lambda)_i=0\qquad(i\in A).
\tag{5}
\]

Thus the principal matrix on `A` has a homogeneous simplex solution.  In the
four-player quantitative full-support hard residual this excludes:

- `A=Fin 4`; and
- `A=P` for any selected principal `P` on which projective Q fails.

It does not exclude a general proper `A`, partial support of `lambda`, or the
ballistic case `rho>0`.

Finally, suppose the orbit is the exact prefix ray over a pure remote
coalition `C` with `2 <= C.card`, and its common prefix survival tends to
`alpha>0`.  Put

\[
 h_i(C)=
 \max\{r_i(C\cup\{i\}),r_i(C\setminus\{i\})\}-r_i(C),
 \qquad H_C=\sum_i h_i(C).
\]

The remote-bubble limit has

\[
 d_i=\alpha h_i(C),\qquad L=D=\alpha H_C.
\tag{6}
\]

The literal all-Never profile has debt

\[
 D_N=\sum_i(s_i)_+,
\]

so its exact debt jump is

\[
 \boxed{D_N-L=\sum_i(s_i)_+-\alpha H_C.}
\tag{7}
\]

Positive global minimality gives no sign to (7).

## Conjecture-facing change

The strict normalized Fin4 ray had a proposed direct closure: normalize each
small exact root and invoke either the homogeneous singleton-LCP screen or the
nonprojective-Q-bar screen.  Equations (1)--(4) identify the actual limit and
remove that shortcut.

The normalized object has two hazard distributions, `lambda` and `Lambda`,
and in the ballistic case a separate collision matrix `J`.  It becomes the
checked homogeneous object only in the special diffuse, full-current-support
case (5).  The theorem therefore narrows the strict-ray obligation to proper
binding support, partial current support, or ballistic collision holonomy.

This is not a terminal consumer.  It does not provide terminal
approximations, a charged return, a renewable descent, or a counterexample.

## Definitions and semantic scope

`b_(k,i)` is the supremum over every unilateral behavioral replacement of
player `i`: Never, every finite or arbitrarily late pure stopping time,
randomized hazards, and history-dependent behavioral strategies.  The exact
root Nash condition is the two-action product-root condition against this cap
vector.

The orbit prefixes the new root before the old semantic tail.  Product root
actions are independent across players.  No stationary completeness or cap
attainment is assumed.

`lambda_k` is the current root's normalized marginal-hazard vector.
`Lambda_k` is the barycenter of the entire remaining marginal-hazard tail.
They are not identified.  The matrix `M` is the checked normalized solo
matrix.  The matrix `J` records the payoff effect of joining a singleton
quitter and is generally independent of `M`.

## Proof

### Summability and support

The elementary union bounds give

\[
 a_k\le\varepsilon_k\le |I|a_k.
\]

Hence `sum epsilon_k` is finite and `epsilon_k -> 0`.  If a root is all
Continue, the autonomous maximal-prefix orbit is constant thereafter; in the
nontrivial case one may retain only indices with `epsilon_k>0`.  Small
absorption also makes every marginal Quit probability strictly below one.

Let `R` bound all terminal rewards and caps in absolute value.  Since player
`i` assigns positive probability to Continue and `q_k` is exact Nash, the
successor cap is the Continue endpoint:

\[
 b_{k+1,i}=C_i(q_{k,-i};b_{k,i}).
\tag{8}
\]

This endpoint differs from `b_(k,i)` only on opponent absorption.  Therefore

\[
 |b_{k+1,i}-b_{k,i}|\le2Ra_k.
\tag{9}
\]

The cap coordinates converge absolutely.  Passing the exact root Nash
inequalities through `q_k -> allContinue` gives `bar b_i>=s_i`.  If this
inequality is strict, Quit remains strictly worse for all sufficiently large
`k`, so exact complementarity forces `x_(k,i)=0`.  This proves late support on
`A`.

### First-order cap flow

For `i in A`, expand the Continue endpoint in the small product root:

\[
\begin{aligned}
 b_{k+1,i}-b_{k,i}
 &=\sum_{j\ne i}x_{k,j}
       \bigl(r_i(\{j\})-b_{k,i}\bigr)+O(\varepsilon_k^2)\\
 &=\varepsilon_k(M\lambda_k)_i
   +O\!\left(\varepsilon_k^2+
       \varepsilon_k|b_{k,i}-s_i|\right).
\end{aligned}
\tag{10}
\]

Since `b_(k,i)->s_i`, there are errors `e_(k,i)->0`, uniformly over the finite
player set, such that

\[
 b_{k+1,i}-b_{k,i}
 =\varepsilon_k\bigl((M\lambda_k)_i+e_{k,i}\bigr).
\tag{11}
\]

Summing (11) from `k` to infinity and dividing by `T_k` proves (1), because
the normalized error is at most
`sup_(h>=k,i)|e_(h,i)| -> 0`.

### Endpoint complementarity

The Quit-minus-Continue endpoint difference has the independent expansion

\[
 Q_i-C_i
 =s_i-b_{k,i}+
   \varepsilon_k(J\lambda_k)_i
   +O\!\left(\varepsilon_k^2+
       \varepsilon_k|b_{k,i}-s_i|\right).
\tag{12}
\]

Let

\[
 v_{k,i}=(C_i-Q_i)/\varepsilon_k.
\]

Exact root Nash gives

\[
 v_{k,i}\ge0,
 \qquad
 \lambda_{k,i}v_{k,i}=0,
\tag{13}
\]

while (12) gives

\[
 v_{k,i}=\frac{b_{k,i}-s_i}{\varepsilon_k}
 -(J\lambda_k)_i+o(1).
\tag{14}
\]

For `i in A`, multiply (14) by `rho_k` and use
`b_(k,i)-s_i=-(bar b_i-b_(k,i))` together with (1).  This gives

\[
 \rho_kv_{k,i}
 =-(M\Lambda_k)_i-\rho_k(J\lambda_k)_i+o(1)\ge0.
\]

Passing to the selected subsequence proves (2).  Multiplying first by
`lambda_(k,i)` and using (13) proves (3).  Splitting the `h=k` summand from the
definition of `Lambda_k` proves (4).

### Diffuse principal consequence

When `rho=0`, equations (2)--(3) reduce to

\[
 -M\Lambda\ge0,
 \qquad
 \lambda_i(M\Lambda)_i=0
 \quad(i\in A).
\]

If `lambda` is positive on all of `A`, equation (5) follows.  Since `Lambda`
is a simplex vector supported on `A`, it is a homogeneous solution with zero
principal residual.

If the principal on `A` is nonprojective Q, this is impossible: a homogeneous
simplex solution supplies a zero-cemetery projective solution for every right
hand side.  In the Fin4 full-support hard residual, the case `A=univ` is also
impossible.  Use
`FinFourQuantitativeFullSupportHardResidual.normalCore_eq_univ` to identify
the normal-player matrix with the full principal and then contradict
`residualHardClass.no_homogeneous`.

### Remote bubble and all-Never

For `2 <= C.card`, a pure `C` root screens every unilateral deviation from
the continuation: after any one player chooses Continue, another member of
`C` still Quits.  Its coordinate debt is therefore exactly `h_i(C)`.
Every exact cap-Nash prefix scales every coordinate debt by its joint Continue
mass.  Passing to limiting common survival `alpha` proves (6).

All-Never prescribes payoff zero.  Against opponents who Never quit, player
`i` obtains `s_i` by any finite quit and zero by Never, so its cap is
`max(s_i,0)`.  This proves (7).

## Boundary tests

### Proper singleton support

Let `A={i}` and `lambda=Lambda=e_i`.  Both matrices have zero diagonal:

\[
 M_{ii}=J_{ii}=0.
\]

Consequently (2)--(4) hold identically for every `rho in [0,1]`, independently
of every off-diagonal hard-matrix entry.  This is an exact algebraic boundary
showing why neither full normal core nor a nonprojective principal elsewhere
eliminates proper-support diffuse or ballistic limits.  It is not claimed to
be an actual positive-gap ray.

### Hard-principal incidence

If the binding set equals a selected nonprojective principal and `lambda` is
positive throughout it, the diffuse case is excluded.  Mere intersection
with that principal is not enough: weights outside the principal still enter
its residual rows.

### Fixed paid edge

A fixed singleton-to-pair paid edge may determine one positive collision entry
`J_(o,j)`.  A pair-to-triple edge need not be an entry of `J` at all.  In
either case the ray data do not imply `lambda_j>0`, and all other collision
entries retain arbitrary sign.  The paid edge therefore does not sign
`J lambda`.

### All-Never

If all `s_i<=0`, then `D_N=0`, contradicting a positive global minimum.  Thus
at least one singleton reward is positive in the positive-minimum regime.
This does not compare `D_N` with the strict-ray limit `L`; both orders remain
compatible with (7).

## Source correspondence

The actual strict-ray adapter consists of:

- `quittingMaximalCapSemanticPrefixOrbit_succ` and the exact coordinate debt
  scaling in
  `Research/Quitting/MaximalCapSemanticPrefixOrbit.lean`;
- `QuittingMaximalCapSemanticPrefixRayStall.summable_absorption` and
  `absorptionTailSum_tendsto_zero` in
  `Research/Quitting/MaximalCapSemanticPrefixReturn.lean`; and
- `quittingTerminalSemanticDebt_prefix_eq_continueMass_mul_add_capDefect` in
  `UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/CapDebtBellmanReduction.lean`.

The solo matrix identity is
`normalizedSoloMatrix_eq_soloReward_sub`.  The Fin4 full-core and hard-screen
data are fields of `FinFourQuantitativeFullSupportHardResidual`.  Reindexing
of the homogeneous simplex problem is supplied by
`singletonLCPFeasible_reindexMatrix_iff`.

The first-order product expansions and conclusions (1)--(5) are the new
ordinary mathematics.  They have not yet been compiled as Lean declarations.

## Adapter and boundary consumption

Given an actual profile realizing the strict-ray source,
`QuittingMaximalCapSemanticPrefixRayStall.summable_absorption` supplies the
summability hypothesis.  The root orbit and exact cap-Nash facts supply the
remaining inputs.  Compactness of the finite simplexes supplies the displayed
subsequential limits.

The result consumes the proposed *direct matrix-normalization shortcut*: only
the diffuse full-current-support arm reaches the homogeneous screen.  The
remaining strict ray must be handled as proper/partial support or as a
two-distribution collision holonomy.  There is no downstream terminal consumer
for those remaining arms in this packet.

## Lean handoff

Suggested declarations, separated from the existing strict-ray structure:

```text
quittingExactCapRay_cap_tendsto
quittingExactCapRay_hazard_eventually_supported_binding
quittingExactCapRay_continueIncrement_normalized_tendsto
quittingExactCapRay_tailNormalizedCapFlow_tendsto
quittingExactCapRay_subseq_collisionComplementarity
quittingExactCapRay_diffuse_fullSupport_homogeneousPrincipal
```

The first-order estimates should retain the error

```text
O (epsilon^2 + epsilon * |cap - singletonReward|)
```

or expose a generic remainder tending to zero after division by `epsilon`.
They must not state `O(epsilon^2)` for Quit-minus-Continue or
`O(epsilon)` after normalization without an additional local cap-scale
hypothesis.

A separate Fin4 adapter may combine
`normalCore_eq_univ`, `residualHardClass.no_homogeneous`, and reindexing to
exclude `A=univ` in the diffuse full-support case.

## Scope and nonclaims

The theorem does not orient accumulated local defects, cross a pure-pair
screen, preserve a paid sibling through prefix exactification, sign the
all-Never jump, or produce any equilibrium object.  It proves the exact
tail-normalized limit and the boundary of what the current hard matrix data
can infer from it.
