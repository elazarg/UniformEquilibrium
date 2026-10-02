# Hard Cross-Face Positive-Exit Review

Reviewer: `CODEX_NOETHER`

Reviewed note:
[`../notes/CODEX_GAUSS__CURL_FREE_TOGGLE_POTENTIAL.md`](../notes/CODEX_GAUSS__CURL_FREE_TOGGLE_POTENTIAL.md)

Scope: Section 39, Proposition 53, including its use of Proposition 52 and its
application to `CODEX_NOETHER` Proposition 74(b).  I independently checked
the production-normal/abnormal floor split, the singleton-mixture consumer,
the averaged-control kernel, and the strict endpoint sign.  This is ordinary
mathematics; I did not produce a new Lean declaration or integration seal.

## Verdict

**Proposition 53 is VALID ordinary mathematics as stated.**  The local
two-sign examples in `CODEX_NOETHER` Proposition 75 do not survive the global
no-uniform and production-normal hypotheses: a cross-face principal kernel
must have a strictly negative omitted production-normal residual, hence a
strictly positive coordinate of the radial endpoint.  The conclusion remains
a directed restart obligation, not a clock/support-entry producer.

## 1. The Proposition 52 dispatch is exact

Write `M` for the normalized singleton matrix, so

```text
(M nu)_i = quittingSingletonMixture reward nu i - solo_i.
```

Extend the probability vector on `A` by zero to all players.  For `i in A`,
`M_A nu=0` pins the mixture to `solo_i`; production normality gives
`solo_i>=punishment_i`.  For an omitted production-normal player,
`(M nu)_i>=0` makes the mixture at least `solo_i`, again at least the
punishment value.

For an abnormal player, extend the same weights by zero to the full subtype
of production-normal players.  The hypotheses of
`abnormal_punishmentFloor_chain_punishmentNormal_singletonMixture`
(`UniformEquilibrium/Quitting/Classification/LCP/NormalPrincipalReward.lean`)
hold: weights are nonnegative and sum to one.  Its conclusion is exactly

```text
solo_i < punishment_i <= singletonMixture_i.
```

Thus, with `floor_i=max(solo_i,punishment_i)`, the mixture dominates the
floor at every coordinate and every positive-mass owner is solo-pinned.
The remaining two floor inequalities are tautological.  These are literally
the hypotheses of
`exists_uniformEquilibriumPayoff_of_complementarySingletonMixture`
(`UniformEquilibrium/Quitting/Classification/ThreePlayer/SingletonMixtureCompiler.lean`),
whose conclusion covers unrestricted behavioral deviations.  Therefore, if
no uniform-equilibrium payoff exists, not all omitted production-normal
residuals can be nonnegative.  This remains true when `A` already exhausts
the production-normal set: the universal omitted-row condition is then
vacuous and the same compiler gives the contradiction, so that boundary case
cannot occur under the proposition's premises.

## 2. Strict residual and drift sign

Finiteness converts failure of the universal nonnegative-row condition into
an omitted production-normal `i` with `(M nu)_i<0`.  Since `b>=solo`,
`c_i=b_i-solo_i>=0`, and hence

```text
d_i=c_i-(M nu)_i>c_i>=0.
```

No strictness is lost when `c_i=0`; the negative residual itself supplies it.
No assertion is made about the sign of other omitted coordinates.

## 3. Proposition 74(b) supplies the required kernel

Let `nu(s)` be the simplex control in the unit escape arc and define its
coordinatewise average

```text
barNu_j=integral_(0 to 1) nu_j(s) ds.
```

Finite dimensionality and the almost-everywhere simplex/support clauses give
`barNu>=0`, `sum_j barNu_j=1`, and support contained in `A`.  In arm (b),
`u_i(1)=u_i(0)=0` for each `i in A`.  Integrating

```text
u'=lambda(c-M nu(s))
```

and using `lambda>0` and `c_i=0` on `A` yields
`(M barNu)_i=0` for every `i in A`.  Proposition 53 therefore applies to
`barNu` literally.  For its selected omitted normal player,

```text
u_i(1)=lambda[c_i-(M barNu)_i]>0.
```

The averaging step does not require pointwise convergence of controls or a
support representative on null sets.

## 4. Exact surviving gap

The result finds one strategically relevant positive coordinate, but the
control remains supported on `A`.  Positive payoff displacement is not the
same as positive quit hazard, and by itself supplies neither the next
source-matched Bellman arc nor an exact returned block.  A proof still has to
turn permanent omission of this negative-residual normal row into a checked
dispatch, or construct a compatible support-entry/reset chronology.  I found
no mathematical objection to Proposition 53 and no broader claim in the note.

## 5. Residual-hard strengthening for nonvertex averages

I also checked the subsequent strengthening communicated by the author.  Add
the residual-hard hypothesis, and suppose the support `S={j | nu_j>0}` has at
least two elements.  For every `i in S`, the equality `(M nu)_i=0`, the zero
diagonal, and positivity of the weights imply that some distinct `j in S`
has `M_ij<=0`; otherwise the weighted row sum would be strictly positive.
Induction through
`mem_normalLayer_succ` in
`UniformEquilibrium/Quitting/Classification/LCP/NormalCore.lean` then gives

```text
S subset normalLayer M n    for every n,
```

so `S subset normalCore M`.

View `nu` as a simplex vector on `normalCore M`, extended by zero away from
`S`.  If every recursively normal row outside `A` had nonnegative residual,
then every normal-core residual would be nonnegative: rows in `A` have zero
residual by `(CF1)`.  Positive weights lie in `S subset A`, where the residual
is zero, so complementarity also holds.  This would be a
`HasHomogeneousSimplexSolution (normalPlayerMatrix M)`, contradicting the
`ResidualHardClass.no_homogeneous` field.  Hence in the nonvertex case the
strict negative row, and therefore the strict positive exit, may be chosen in

```text
normalCore M \ A.
```

This strengthening is valid.  The support-cardinality hypothesis is
essential to this particular recursive-normality argument: a vertex owner
need not have a distinct supported nonpositive witness.  Thus the vertex case
retains only Proposition 53's production-normal conclusion.
