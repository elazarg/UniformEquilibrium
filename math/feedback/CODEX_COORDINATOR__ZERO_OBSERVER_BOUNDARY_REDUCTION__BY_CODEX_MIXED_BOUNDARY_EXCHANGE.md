# Review of the subcritical source reduction

Reviewer: CODEX_MIXED_BOUNDARY_EXCHANGE.

Reviewed artifact:
[canonical boundary note](../notes/CODEX_COORDINATOR__ZERO_OBSERVER_BOUNDARY_REDUCTION.md),
Section 9 only. Whole-file SHA-256:
`3fd731c1fa23f0bde56f20b421934656dc7103d06e7ce13a11dc777ce0329168`.
The exact bytes beginning with `## 9. One subcritical` through end of file
have SHA-256
`571f879923f2fd0770e9b705c0acd3ef73d2dcb37f3aeecf7f56428029dc1a80`.

Verdict: the reduction and all-zero exclusion are correct under the stated
augmented-carrier source hypotheses. They do not eliminate actual minima or
mixed endpoints. Ordinary mathematics only; no Lean command ran.

Subcriticality forces every minimum to have positive joint Never mass, so
Section 7's positive-penalty strict margin and inverse-axis argument apply.
Comparison with a minimum at the larger parameter proves strict increase
where the value is below m. The incoming adapter in Section 8 uses the same
positive Never mass, ALL-END and positive observer caps, without needing
the first-plateau identity. I checked that parameter substitution and its
augmented coordinates, rather than reproving the entire root extraction.

At an all-zero endpoint Q, the complete head-cap formula gives
`B_i(Y)=max(B_i(P),e_i(P))=B_i(P)`. Observer payoffs likewise equal those
of P, so P belongs to C. The pivot identity is
`d_p(Y)=d_p(P)+nu(P)d_p(Q)`, which proves `J_R(P)=mu`. No minimizer status
for Q is used.

Grafting Q with the retained query after any Z in C keeps every cap
unchanged because `B(Q)=0` and `B(Z)>=e(Z)`. Its observer debts stay zero
and its exact objective is `J_R(Z)`. These two comparisons force
`f(R)=f(r)=mu<m`, hence `R=r`. ALL-END has already propagated to Q,
so `e(Q)=0` follows directly. Repeated grafts therefore retain all e
coordinates and caps, while their compact limit has zero joint Never and
debt mu<m, the stated contradiction.

When nu(Q)=1, native coordinate bounds force Q to be the complete AllNever
tuple. The head map then yields the actual tuple of P. This argument does
not assume that a general actual Q can be played after an infinite actual
head. The final approximate-repair criterion correctly requires a fixed
positive improvement with full-cap observer errors tending to zero.

No unresolved objection in this scope. Earlier sections and any subsequent
additions are outside this review's approval.
