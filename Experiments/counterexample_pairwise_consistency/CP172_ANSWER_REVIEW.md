# Review of the proposed answer to Question 172

## Decision

The answer does not solve the compatibility problem, and correctly refuses to
claim that it does.  Its useful mathematical contribution is a prospective
occupation bridge from a summable tail to its canonical periodic windows.  It
also identifies the normalized window scale at which unnormalized convergence
loses information.

The final diagnosis needs one correction: the missing condition is not always
“funding the ghost packet.”  The stabilized periodic evaluator has two branches,
and they fail different packet clauses.

This review concerns the mathematical deductions.  Its literature-status
paragraph is not used as evidence here and requires an independent source
audit before citation.

## Claims that survive review

### Tail exploitability

If `rho_T = sum_(t>=T) q(a_t)`, then every honest suffix payoff is bounded by
`M rho_T`.  A deterministic unilateral stop at a late date differs from the
solo reward by at most a constant times `M rho_T`, while Never differs from
zero by the same order.  Hence

```text
BR_i(a^(T)) = max(0,r_i({i})) + O(M rho_T),
E(a^(T)) -> max_i max(0,r_i({i})) = K.
```

The constants `4` and `5` in the proposed answer are conservative and should
be replaced by explicit inequalities before formal promotion.  The conclusion
is sound: the selected tail is itself highly exploitable, so no contradiction
comes from tail exploitability alone.

### Ghost target and support pinning

Under the genuine exact Nash--Bellman tail equations,

```text
|v_t-v_(t+1)| <= 2 M q(a_t),
```

so the whole annotation vector converges.  Vanishing opponent hazards give
`z_i >= r_i({i})`, and any player using positive own hazard infinitely often
is pinned at `z_i = r_i({i})`.  Therefore every limit of normalized late
hazard occupations is supported on pinned coordinates.

This produces the solo and support-complementarity portions of a singleton
packet.  It does not by itself produce both the mixture-funding inequality and
the punishment-floor inequality.

### Periodic occupation approximation

For a late finite word whose total hazard is small, within-word survival
weights equal one up to the tail hazard, and total multi-quitter mass is the
same relative order.  Consequently its periodically repeated terminal law,
conditional on singleton absorption, is close to the normalized owner-hazard
measure.  The prescribed delivery and refusal evaluator approach the
corresponding singleton mixture and conditional refusal value.

This is a useful theorem candidate, but the proposed `O(rho)` statements are
not yet a proof object.  Promotion requires explicit denominator hypotheses,
uniform constants, and separate zero-total-hazard and zero-opponent-hazard
branches.

## Necessary correction: phase and refusal fail different clauses

Let `lambda` be a limiting normalized hazard occupation and `z` the limiting
annotation.  For a stabilized player `i`, write

```text
m_i = sum_j lambda_j r_i({j}),
R_i = [sum_(j != i) lambda_j r_i({j})]/(1-lambda_i).
```

When `lambda_i > 0`, support pinning gives `z_i = r_i({i})`, and

```text
R_i-m_i = lambda_i (R_i-r_i({i})).
```

The two evaluator branches therefore behave as follows.

1. **Phase-stop branch.** If
   `r_i({i}) >= m_i + eta/2`, then
   `z_i >= m_i + eta/2`.  The ghost pair fails packet funding
   `z_i <= m_i` quantitatively.
2. **Refusal branch.** If
   `R_i >= m_i + eta/2`, then `lambda_i` is bounded away from zero and
   `R_i > r_i({i}) = z_i`.  Hence
   `m_i = lambda_i z_i + (1-lambda_i)R_i > z_i`:
   packet funding is recovered rather than lost.  What can still be missing is
   `chi_i <= z_i`, and the stabilized refusal player need not be the positive-
   debt owner for whom a floor theorem is available.

Thus the proposed answer's later statements that all routes reduce to funding
are not correct in the refusal branch.  The missing bridge is:

> produce, from one tail/window subsequence, a normalized occupation packet
> that is simultaneously funded, punishment-rational, and tied to the same
> source/cap data.

Equivalently, one must either fund the phase branch or prove the punishment
floor (with the required provenance) in the refusal branch.  Aligning the
periodic witness with the selected debt owner would be one sufficient route,
but is not currently known.

## Relation to the pair experiments

The exact `P × W` witness independently confirms that an occupation bridge can
make the packet refusal defect converge to the periodic refusal defect.  This
reinforces obstruction and does not identify packet target with delivery.

The exact `T × W` witness independently confirms that debt conservation,
summable absorption, and the logarithmic opponent clock do not improve the
window endpoint difference from `O(m)` to `o(m)`.  The normalized drift can
converge to a nonzero constant.

The answer's all-Continue plateau is a valid local regression for phantom
annotation and cap self-loop compatibility.  It does not establish the global
finite capacity of every punishment-floor chain, so it is not by itself a
`T × C` consistency witness under this program's full `C` cluster.

## Useful extraction tasks

The following statements merit isolated experimental formalization:

1. explicit suffix best-response bounds converging to the maximal positive
   solo reward;
2. full-vector annotation convergence and occupation-support pinning;
3. a quantitative periodic singleton-occupation approximation, including
   refusal and phase values;
4. the exact phase-underfunded/refusal-floor-missing alternative above; and
5. a conditional theorem that a punishment-floor bound for the stabilized
   refusal player turns the ghost coordinates into a genuine normalized
   packet.

Only after those statements are exact should the remaining bridge be treated
as one inequality or sent to the production pipeline.
