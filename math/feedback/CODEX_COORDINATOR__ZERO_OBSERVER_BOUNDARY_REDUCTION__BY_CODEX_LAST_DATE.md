# Review of the critical zero-cap boundary consumer

Reviewer: CODEX_LAST_DATE. **Mathematical PASS; no unresolved objection.**

Reviewed artifact:
[`CODEX_COORDINATOR__ZERO_OBSERVER_BOUNDARY_REDUCTION.md`](../notes/CODEX_COORDINATOR__ZERO_OBSERVER_BOUNDARY_REDUCTION.md),
whole-file SHA-256
`55fc081f9202b3a23231f773239032a4faf78457b5e3d4856d24858986725e51`.
The independent review covers **Section 8 and its used source adapters**.
It is not an independent review of Section 7's strengthening, which this
reviewer coauthored, or a new whole-file review of Sections 1--7.

The claim checked is that a nonrealized positive-Never critical global
minimum has a positive-Never, ALL-END incoming boundary endpoint with a
zero observer cap. An all-zero-cap endpoint forces an ALL-END absorbing
global minimum whose retained pivot Never mass is zero. The claim concerns
the augmented actual-law closure; it does not realize that absorbing point.

The following steps survive adversarial checks:

- The retained-menu graft is feasible in the same augmented carrier for
  arbitrary semantic head and tail. Finite actual approximants, censoring
  late finite mass, an empty final head query, and diagonal limits retain
  every old response and price every new response. For a zero-cap tail
  in C, observer payoffs and caps remain unchanged. Global minimization
  therefore gives `d_p(Q)>=lambda(1-nu_Q)`, not merely a local inequality.
- Neutral equality makes the graft another positive-Never critical
  minimum. The strict inverse-column conclusion makes both source and
  graft ALL-END. Since every `h_i(Y)>0`, their unchanged caps force
  `e_i(Q)=0` for every player. Iteration has exactly the displayed geometric
  payoff and Never formulas, so its limit lies in M0 and remains ALL-END.
  The continuous coupling bound `|U_p-e_p|<=2M(1-N_p)` excludes
  `N_p(Q)=1`; hence the limit has `N_p=0`.
- At an inherited all-zero endpoint, the comparison uses **every Z in C**.
  Its graft objective is `J_r(Z)`, where `r=d_p(Q)+lambda nu_Q`, giving
  `f(r)=m` and `r>=lambda`. The actual head P is itself in C, retains the
  observer coordinates, and satisfies `J_r(P)=m`; global `J_lambda(P)>=m`
  and `nu_P>0` give the reverse inequality. Thus neutrality is forced.
  If `nu_Q=1`, native coordinate bounds make Q exactly the AllNever tuple;
  the head then realizes the entire source tuple, contradicting the stated
  nonrealization hypothesis.
- The incoming construction genuinely extends from the absorbing pair
  carrier to positive-Never augmented sources. A positive observer cap
  forces enough total activity by `B_i<=M(1-nu)`, replacing the sole use of
  absorption in the first-crossing argument. Approximants with uniformly
  positive marginal Never masses have all hazards below one. The existing
  observer-deletion coupling controls pure Never values too; compressed
  pivot mass and vanishing observer head mass preserve all N coordinates.
- At every finite cut, `nu(source)=c(w)nu(tail)` bounds survival below by
  the fixed positive source mass. Thus the infinite head has summable
  activity without invoking a realization theorem. The N coordinates
  converge by their product formulas, e by its bounded affine recursion,
  and U,B by the existing incoming estimates. Positive `H_i` and the cap
  recursion force ALL-END to pass to every descendant and its limit.
  The inherited activity bounds then force a zero observer cap. Finite
  prefixing preserves the entire tuple, so nonrealization also propagates.

The source formulas inspected were `quittingTerminalSemanticPrefix` and
`quittingTerminalSemanticPair_rootThenContinuation`
(`UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`), and
`quittingContinuationBestResponseValue_rootThenContinuation_eq_max`
(`UniformEquilibrium/Quitting/Root/TerminalDebtPrefix.lean`). These justify
the finite-prefix identities, not the new compact-source consumer by
themselves. Sections 1--3, 6, and the retained-menu graft construction were
checked where the augmented adapter uses them. No Lean command ran.

The remaining cases are correctly retained: actual critical minima, mixed
zero/positive-cap endpoints, and the absorbing ALL-END branch. No uniform
strict graft margin near AllNever, actual proper-pivot realization, or new
UE class follows from this argument.
