# Review of strict maximal-prefix ray tail normalization

Reviewer: `CODEX_STOKES`

## Verdict

The tail-normalized cap-flow theorem is sound after two substantive scope
repairs:

1. the one-step remainders in (11)--(13) are little-oh remainders, not the
   displayed `O(epsilon_k)` and `O(epsilon_k^2)` remainders, unless an
   additional estimate
   `|b_(k,i)-bar b_i| = O(epsilon_k)` is supplied; and
2. the diffuse full-binding/full-support contradiction uses both
   `normalCore_eq_univ` and the hard class's `no_homogeneous` field.  The
   latter is stated on the normal-core principal matrix, not directly on the
   ambient matrix.

The repaired errors are still uniform little-oh errors, so tail averaging
proves the same displayed limit equations (15)--(20).  The proper-support,
ballistic, and all-Never limitations are correct.  They can be sharpened as
follows:

- a diffuse limit whose current-root direction is positive on every binding
  coordinate makes the binding principal matrix homogeneous; hence the
  binding set cannot equal any selected nonprojective hard principal;
- mere incidence with that principal is insufficient; and
- a singleton binding support makes both the solo and collision terms
  identically diagonal-zero, so the limiting equations are compatible with
  every hard matrix screen.

The fixed pre-mark paid edge does not remove this last obstruction.  It gives
at most one oriented terminal membership comparison; the ray data do not put
positive limiting hazard on its other label, and the remaining entries of the
collision matrix are unrestricted.

No terminal consumer follows.  The result is nevertheless a decisive no-go
for the proposed direct normalization shortcut.

## Claim reviewed

For a nontrivial canonical maximum-absorption exact cap-prefix ray with
summable absorption, let

\[
 z_{k+1}=T_{q_k}z_k,
 \qquad
 \varepsilon_k=\sum_i x_{k,i},
 \qquad
 \lambda_{k,i}=x_{k,i}/\varepsilon_k,
\]

where `x_(k,i)` is player `i`'s Quit probability in the exact product root.
Let `b_k` be the cap coordinate of `z_k`, `bar b` its limit, and

\[
 A=\{i:\bar b_i=r_i(\{i\})\}.
\]

Writing

\[
 M_{ij}=r_i(\{j\})-r_i(\{i\}),
 \qquad
 J_{ij}=r_i(\{i,j\})-r_i(\{j\})
\]

off the diagonal and zero on it, define the remaining hazard and its
barycenter by

\[
 T_k=\sum_{h\ge k}\varepsilon_h,
 \quad
 \rho_k=\varepsilon_k/T_k,
 \quad
 \Lambda_k=T_k^{-1}\sum_{h\ge k}\varepsilon_h\lambda_h.
\]

Then along a convergent subsequence

\[
 \frac{\bar b_i-b_{k,i}}{T_k}=(M\Lambda_k)_i+o(1)
 \qquad(i\in A),
\]

and if

\[
 \lambda_k\to\lambda,
 \quad \Lambda_k\to\Lambda,
 \quad \rho_k\to\rho,
\]

then

\[
 -M\Lambda-\rho J\lambda\ge0,
 \qquad
 \lambda_i(M\Lambda+\rho J\lambda)_i=0
 \quad(i\in A).
\]

This is not in general a homogeneous or projective LCP for `M`.

## Independent derivation

### 1. Summable hazard and cap convergence

For root absorption `a_k`, the finite union bounds give

\[
 a_k\le\varepsilon_k\le |I|a_k.
\]

Thus summable absorption implies summable `epsilon_k` and
`epsilon_k -> 0`.  Once absorption is small, every root coordinate is below
one.

Let `R` bound both terminal rewards and terminal caps in absolute value.
Because `q_k` is exact Nash against `b_k` and player `i` puts positive mass
on Continue, the successor cap is its Continue endpoint:

\[
 b_{k+1,i}=C_i(q_{k,-i};b_{k,i}).
\]

This endpoint differs from `b_(k,i)` only on opponent absorption, so

\[
 |b_{k+1,i}-b_{k,i}|\le2Ra_k.
\]

The cap coordinates therefore converge absolutely to `bar b`.  Closedness of
the root Nash inequalities at all Continue gives

\[
 \bar b_i\ge s_i:=r_i(\{i\}).
\]

If the inequality is strict, the Quit endpoint remains strictly below the
Continue endpoint for all large `k`, hence `x_(k,i)=0` eventually.  All late
hazard is supported on `A`.

### 2. Correct one-step expansions and signs

For `i in A`, product expansion of the Continue endpoint gives

\[
\begin{aligned}
 b_{k+1,i}-b_{k,i}
 &=\sum_{j\ne i}x_{k,j}
     \bigl(r_i(\{j\})-b_{k,i}\bigr)+O(\varepsilon_k^2)\\
 &=\varepsilon_k(M\lambda_k)_i
   +O\!\left(\varepsilon_k^2+
      \varepsilon_k|b_{k,i}-s_i|\right).
\end{aligned}
\]

Since `b_(k,i)->s_i`, division by `epsilon_k` yields

\[
 \frac{b_{k+1,i}-b_{k,i}}{\varepsilon_k}
 =(M\lambda_k)_i+o(1).
\tag{R1}
\]

This is the exact repair of the note's (11).  The stronger remainder
`O(epsilon_k)` would require the unproved local comparison
`|b_(k,i)-s_i|=O(epsilon_k)`.

Similarly,

\[
 Q_i-C_i
 =s_i-b_{k,i}+
   \varepsilon_k(J\lambda_k)_i
   +O\!\left(\varepsilon_k^2+
      \varepsilon_k|b_{k,i}-s_i|\right).
\tag{R2}
\]

Define the exact normalized Continue advantage

\[
 v_{k,i}:=\frac{C_i-Q_i}{\varepsilon_k}.
\]

Exact root Nash gives

\[
 v_{k,i}\ge0,
 \qquad
 \lambda_{k,i}v_{k,i}=0,
\]

and (R2) gives

\[
 v_{k,i}
 =\frac{b_{k,i}-s_i}{\varepsilon_k}
   -(J\lambda_k)_i+o(1).
\tag{R3}
\]

This verifies both signs.  The collision term is `-J lambda` in the
Continue advantage and hence `-rho J lambda` in the limiting nonnegative
residual.

### 3. Tail normalization

Write (R1) as

\[
 b_{h+1,i}-b_{h,i}
 =\varepsilon_h\bigl((M\lambda_h)_i+e_{h,i}\bigr),
 \qquad
 \sup_i|e_{h,i}|\to0.
\]

Summing from `h=k` to infinity and dividing by `T_k` gives

\[
 \frac{\bar b_i-b_{k,i}}{T_k}
 =(M\Lambda_k)_i+o(1).
\tag{R4}
\]

The error is bounded by `sup_(h>=k,i)|e_(h,i)|`; no square-summability
estimate is needed.

On `A`, `bar b_i=s_i`.  Multiplying (R3) by `rho_k` and using (R4) yields

\[
 \rho_kv_{k,i}
 =-(M\Lambda_k)_i-\rho_k(J\lambda_k)_i+o(1)\ge0.
\]

Passing to the chosen subsequence proves

\[
 -M\Lambda-\rho J\lambda\ge0.
\]

Since `lambda_(k,i) rho_k v_(k,i)=0` exactly, passage to the limit also gives

\[
 \lambda_i(M\Lambda+\rho J\lambda)_i=0.
\]

Finally, splitting the first term of the tail sum gives the exact renewal
identity

\[
 \Lambda_k=\rho_k\lambda_k+(1-\rho_k)\Lambda_{k+1}.
\]

### 4. Diffuse case and the exact hard-screen adapter

If `rho=0`, then

\[
 -M\Lambda\ge0,
 \qquad
 \lambda_i(M\Lambda)_i=0
 \quad(i\in A).
\]

If `lambda_i>0` for every `i in A`, then

\[
 (M\Lambda)_i=0\qquad(i\in A).
\]

Because `Lambda` is a simplex vector supported on `A`, this is a homogeneous
simplex solution of the principal matrix `principalMatrix M A`.  Therefore:

- `A` cannot equal a selected principal on which projective Q fails, since a
  homogeneous solution makes that principal projective Q; and
- in the Fin4 hard residual, `A=univ` is impossible.  For the latter, use
  `FinFourQuantitativeFullSupportHardResidual.normalCore_eq_univ`, transport
  the ambient full-principal solution along the normal-core equivalence, and
  contradict
  `residualHardClass.no_homogeneous`.

The full-core field is essential to this second bullet.  The hard
`no_homogeneous` declaration by itself concerns
`normalizedNormalPlayerMatrix`, not the literal ambient matrix.

Mere intersection with the selected hard principal is insufficient.  Entries
from `A` outside that principal continue to contribute to the displayed rows,
so restriction does not preserve the zero residual.

### 5. Proper-support and ballistic boundary tests

The smallest exact algebraic boundary is a singleton binding set
`A={i}` with

\[
 \lambda=\Lambda=e_i.
\]

Both matrices have zero diagonal:

\[
 M_{ii}=J_{ii}=0.
\]

Therefore for every `rho in [0,1]`,

\[
 -M\Lambda-\rho J\lambda=0
\]

on `A`, and the renewal identity is also satisfied.  Thus neither the full
normal-core screen nor any nonprojective principal elsewhere can exclude the
normalized object.  This validates both the proper-support diffuse limitation
and the ballistic limitation without constructing a positive-gap game.

The fixed pre-mark paid edge does not force a different conclusion.  In the
special singleton-to-pair orientation it yields one positive entry
`J_(o,j)>0`; in the general pair/triple orientation it is not an entry of `J`
at all.  The ray supplies neither `lambda_j>0` nor a sign on the remaining
entries of the relevant row.  Consequently the signed term `J lambda` remains
uncontrolled.  Static full support of the hard residual's singleton packet is
not support of the maximal cap-prefix roots.

### 6. Remote pure coalition and all-Never jump

Assume explicitly that the remote pure coalition `C` has cardinality at least
two.  Then its complete terminal debt is tail-independent and equals

\[
 h_i(C)=
 \max\{r_i(C\cup\{i\}),r_i(C\setminus\{i\})\}-r_i(C).
\]

If the infinite exact prefix has limiting common survival `alpha>0`, exact
coordinate debt scaling gives

\[
 d_i(\bar z)=\alpha h_i(C),
 \qquad
 L=D(\bar z)=\alpha\sum_i h_i(C).
\]

The literal all-Never profile has debt

\[
 D_N=\sum_i(r_i(\{i\}))_+,
\]

so

\[
 D_N-L=\sum_i(r_i(\{i\}))_+-
   \alpha\sum_i h_i(C).
\]

There is no forced sign.  Global positive minimality only gives
`D_N>=D_*` and `L>D_*` in the strict arm.  It also implies that at least one
own singleton reward is positive—otherwise `D_N=0`—but this still does not
compare `D_N` with `L`.

The cardinality hypothesis is necessary: for a singleton `C={i}`, player
`i` can expose the continuation by choosing Continue, so its debt is not the
tail-independent toggle formula above.

## Source correspondence

The exact ray, summability, and scalar debt scaling are supplied by:

- `quittingMaximalCapSemanticPrefixOrbit_succ` and the coordinate-scaling
  declarations in
  `Research/Quitting/MaximalCapSemanticPrefixOrbit.lean`;
- `QuittingMaximalCapSemanticPrefixRayStall.summable_absorption` and
  `absorptionTailSum_tendsto_zero` in
  `Research/Quitting/MaximalCapSemanticPrefixReturn.lean`; and
- the exact root debt formula
  `quittingTerminalSemanticDebt_prefix_eq_continueMass_mul_add_capDefect` in
  `UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/CapDebtBellmanReduction.lean`.

The matrix identification is
`normalizedSoloMatrix_eq_soloReward_sub` in
`UniformEquilibrium/Quitting/Classification/PreemptionGateDictionary.lean`.
The full-core and hard-screen fields are in
`FinFourQuantitativeFullSupportHardResidual`.

The first-order expansions and the tail-normalized theorem are not presently
named Lean declarations.  The review makes no compilation claim for them.

## Remaining scope

The repaired theorem rules out only the direct identification of the strict
ray with the existing homogeneous or projective-Q-bar packets.  It does not
produce a returned block, a chronological payoff charge, a minimum-fiber
source transition, terminal approximants, or a counterexample.
