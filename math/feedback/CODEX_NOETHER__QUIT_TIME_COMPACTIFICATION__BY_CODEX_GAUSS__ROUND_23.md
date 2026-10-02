# Subcompatible tangent-row compiler and normal-core support review

Reviewer: `CODEX_GAUSS`

Reviewed note:
[`../notes/CODEX_NOETHER__QUIT_TIME_COMPACTIFICATION.md`](../notes/CODEX_NOETHER__QUIT_TIME_COMPACTIFICATION.md)

Scope: Section 58.6--58.7, Propositions 61--62.  I independently checked the
blow-up orientation, tight/slack endpoint cases, absorption scale, recursive
normal-layer induction, restriction to the principal matrix, and exceptional
vertex signs.  This is ordinary mathematics, not Lean-checked.

## Verdict

**Propositions 61--62 are VALID ordinary mathematics as stated.**  Proposition
61 is a literal local product-row compiler with quadratic Bellman and standard
probability-weighted endpoint errors under one-sided tight-coordinate
compatibility.  Proposition 62 proves that a nonvertex full homogeneous
witness is supported in the recursive normal core.  No local-to-global
reprojection, ambient abnormal-vertex dispatch, or full-conjecture conclusion
follows from either theorem.

## 1. Bellman orientation in Proposition 61

The chosen coordinates are

```text
a=scale*mu,
u=-scale*z,
h(t)=t*a,
y(t)=b+t*u=b-scale*t*z.
```

This orientation agrees with the checked exceptional-divisor equation.
`QuittingChargeTangentPacket.bellmanFirstOrderResidual_eq_zero` makes the
Bellman blow-up residual vanish at `t=0`, while
`t_mul_quittingBellmanBlowupResidual` says exactly

```text
t B_i(t)=T_i(y(t),h(t))-b_i.
```

The residual is a finite polynomial.  Hence `B_i(0)=0` gives a common local
bound `|B_i(t)|<=L t` for `t>=0`, and the Bellman error is at most `L t^2`.
There is no reversed current/tail sign.

Hazard feasibility is also exact: `scale>0`, simplex nonnegativity, and
`t>0` give `h_i(t)>=0`, while finiteness lets one shrink `t_0` until every
hazard is below one.

## 2. Tight and slack endpoint coordinates

At a singleton-tight coordinate `b_i=s_i`, the factorization
`t_mul_quittingMixingBlowupResidual` applies and its right side is the checked
Quit-minus-Continue gain.  The identities at the exceptional divisor give

```text
D_i(t)=t M_i(t),
M_i(0)=scale*R_i<=0.
```

Polynomial local boundedness supplies both `M_i(t)<=L t` and
`|M_i(t)|<=L` after using `M_i(0)<=0`.  Therefore

```text
(1-h_i(t))D_i(t)<=L t^2,
-h_i(t)D_i(t)<=h_i(t)|D_i(t)|=O(t^2).
```

These are precisely the two weighted inequalities in
`IsεQuittingRootEndpointNash`; the cheap negative raw gap is handled with the
correct owner-hazard factor.

If `b_i>s_i`, positive-mass pinning and `mu_i>=0` force `mu_i=0`, so
`h_i(t)=0`.  At `t=0`, forced Quit minus forced Continue is `s_i-b_i<0`; it
remains nonpositive locally.  The Quit-deviation inequality then has zero
upper error and the Continue-deviation regret is identically zero because the
prescribed hazard is zero.  Thus the proof correctly includes inactive tight
coordinates in `(N51)` and treats inactive slack coordinates separately.

## 3. Absorption scale

The product absorption `q(t)` is a polynomial with

```text
q(0)=0,
q'(0)=sum_i a_i=scale.
```

Taylor's formula gives `(N53)` after enlarging the common finite constant.
Since `scale>0`, a further reduction of `t_0` gives `q(t)>=scale*t/2`; hence
the `O(t^2)` row errors are genuinely `O(q(t)^2)=o(q(t))`.

This validates the proposed local scaling but not iteration: the tail is
`b-scale*t*z`, so the same frozen packet is no longer based at the reached
payoff unless a separate reprojection theorem is supplied.

## 4. Normal-core support reduction

Let `S={i:mu_i>0}` and assume it has at least two members.  For `i in S`,
homogeneous complementarity gives `(M mu)_i=0`.  The diagonal term is zero.
If every `M_i,j` with `j in S\{i}` were strictly positive, the residual would
be strictly positive because all corresponding weights are positive.  Hence
there is a distinct supported `j` with `M_i,j<=0`.

This witness propagates the entire support through the recursive normal
layers.  The support begins in layer zero; if it lies in layer `n`, the same
supported witness lies in layer `n` and proves membership of each `i` in
layer `n+1`.  Thus `S` lies in every layer and hence in `normalCore M`.

Restriction preserves total mass, residuals, and complementarity because all
weights outside `S` vanish.  Therefore it gives a homogeneous solution of
`normalPlayerMatrix M`.  If that principal matrix has no homogeneous solution,
every full witness must consequently be a vertex outside the core.

For a vertex `e_j`, the full residual is column `j`, so every entry in that
column is nonnegative.  If some distinct `k` had `M_j,k<=0`, the hypotheses of
`exists_uniformEquilibriumPayoff_of_nonnegative_column`
(`UniformEquilibrium/Quitting/Classification/LCP/LaterLayerAbnormal.lean`)
would hold with owner `j` and blocker `k`.  Under a no-uniform-payoff
hypothesis this is impossible, proving `M_j,k>0` for every `k!=j`.  This also
excludes `j` from `normalLayer M 1` exactly as claimed.

## 5. Scope for the returned-block obstruction

The elementary reward restriction to the alpha normal-core subtype is sound:
map each subtype coalition into the ambient player set and restrict payoff
coordinates.  Singleton normalization is literally
`normalizedNormalPlayerMatrix reward`, and an ambient product block with zero
hazards off the core has the same normal-coordinate Bellman and endpoint laws.
Thus Gauss Propositions 46--47 and Corollary 48 apply to core-supported blocks
under `ResidualHardClass.no_homogeneous`.

Proposition 62 sharpens, but does not erase, the ambient qualification.  An
arbitrary ambient vanishing returned block can only escape through normalized
cumulative owner mass converging to one pure vertex outside the core.  Under a
hypothetical counterexample its exact surviving sign pattern is `(N58)`.
Until that vertex is dispatched, the uniform small-charge modulus cannot be
claimed for every ambient block from the residual-hard gate alone.

## Concrete next question

The two results meet at one precise producer seam.  Proposition 61 supplies
quadratically accurate rows for collision-subcompatible packets; the returned
telescope says such cheap rows must accumulate nonvanishing hazard/payoff
motion unless a homogeneous witness appears.  The next theorem must re-extract
a packet at the displaced tail while preserving floors, or show that the only
ambient pure vertex `(N58)` is stationarily generated/instant.  Neither result
currently supplies that step.
