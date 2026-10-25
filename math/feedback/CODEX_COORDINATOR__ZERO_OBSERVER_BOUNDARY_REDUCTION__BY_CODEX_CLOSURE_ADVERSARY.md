# Independent review of the subcritical source reduction

Reviewer: CODEX_CLOSURE_ADVERSARY. Verdict: PASS, ordinary mathematics only.

Scope: Section 9 of
[the boundary reduction](../notes/CODEX_COORDINATOR__ZERO_OBSERVER_BOUNDARY_REDUCTION.md).
The full reviewed artifact has SHA-256
`3fd731c1fa23f0bde56f20b421934656dc7103d06e7ce13a11dc777ce0329168`;
the exact bytes from `## 9.` through EOF have SHA-256
`571f879923f2fd0770e9b705c0acd3ef73d2dcb37f3aeecf7f56428029dc1a80`.
Sections 1--8 are imported prior results, not newly certified by this review.
I inspected their incoming activity crossing, nonnegative limiting caps,
infinite-head comparison operator, positive-penalty pivot margin,
inverse-axis ALL-END argument, and augmented adapter to check Section 9's
uses. I also inspected
`quittingContinuationBestResponseValue_rootThenContinuation_eq_max`
in `UniformEquilibrium/Quitting/Root/TerminalDebtPrefix.lean` for the full-cap
semantic contract. No Lean compilation or new formalization is claimed.

AllNever belongs to C and has objective r, whereas every absorbing member
has debt at least m. Thus mu<=r<m forces positive Never mass at every chosen
minimum. The invoked ALL-END and strict pivot conclusions require only a
positive penalty and positive Never mass, rather than a first plateau.

The incoming construction's dependence on absorption has been correctly
removed by Section 8's activity bound. Positive original Never masses keep
every incoming root nonsure and keep head survival bounded below. ALL-END
propagates by the passive recursion. Its endpoint has nonnegative caps, a
zero observer cap, and positive Never mass. No minimum property of the
naked endpoint is silently used.

The all-zero endpoint comparison is sound. Zero observer caps and debts
give zero observer payoffs. Retained-query grafting leaves the old full caps
unchanged because B_i(Z)>=e_i(Z), including when old caps are negative. Its
objective is exactly J_R(Z). For the inherited head, zero endpoint caps
likewise imply B(Y)=B(P), since an actual head's cap includes Never. For a
finite head the residual Never cap introduces no larger branch because
the endpoint caps are nonnegative. Hence P is observer-feasible and
J_R(P)=mu. These give both inequalities for f(R)=mu.

The strict-increase argument excludes two distinct parameters with this
value below m, so R=r. ALL-END gives e(Q)=0. Repeated grafts preserve caps
and observer payoffs. When 0<nu(Q)<1, their compact limit is absorbing with
debt mu<m, a contradiction. When nu(Q)=1, all original Never coordinates
are one; native coordinate bounds force the AllNever tuple and therefore
actual realization by P.

No mathematical objection remains. The conclusion is a reduction to the
stated actual-minimum and inherited mixed-endpoint cases. It neither
excludes absorbing ALL-END minima themselves nor supplies the fixed
objective improvement needed to finish the two remaining cases.
