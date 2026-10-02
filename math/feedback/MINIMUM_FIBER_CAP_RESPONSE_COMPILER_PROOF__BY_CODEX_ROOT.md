# Review of the minimum-fibre cap/response compiler

## Verdict

The mathematical claim is valid. It is a substantive horizontal-seam
compiler, although it is not a consumer of the renewable trace and does not
control arbitrary externally supplied responses.

This claim appeared in the PR 76 material under
`StoppingLawMinimumFiberCommonResponseCompiler`, but the earlier
`CODEX_ROOT` triage recorded only a plausibility assessment. The argument is
checked here directly.

## Claim reviewed

Let `S_n` be a tangent source profile and `T_n` its literal full replacement
of mover `m`, along a subsequence on which both semantic endpoints converge to
the global minimum-debt fibre. Let `H_n` replace `m` by the half mixture of its
laws in `S_n` and `T_n`.

For every nonmover `i`, the claim selects one actual behavioral response
`rho_(i,n)` such that its regret at both `S_n` and `T_n` tends to zero.
Consequently the difference between the true cap displacement and the payoff
displacement of this same response tends to zero. The mover's cap is unchanged
exactly.

## Verification

For a fixed nonmover `i`, put

```text
g_n = (B_i(S_n) + B_i(T_n))/2 - B_i(H_n).
```

For every fixed response of `i`, payoff is affine in `m`'s stopping law.
Therefore `B_i`, a supremum of those affine functions, is convex and
`g_n >= 0`.

Prescribed payoff is affine on the same chord. Hence `g_n` is the coordinate
debt chord defect. Summing the nonnegative coordinate chord defects and using
global minimality at the actual half profile gives

```text
g_n <= ((D(S_n)-D_*) + (D(T_n)-D_*))/2.
```

Both endpoint excesses tend to zero by source convergence, endpoint
convergence, and the minimum-fibre hypothesis. Thus `g_n -> 0`.

Choose an actual `tau_n`-best response `rho_(i,n)` at `H_n`, with
`tau_n -> 0`. Since `i != m`, updating `i` commutes with mixing `m`, so the
payoff of this fixed response is exactly affine:

```text
U_i(H_n[i <- rho])
  = (U_i(S_n[i <- rho]) + U_i(T_n[i <- rho]))/2.
```

Writing the endpoint regrets as `r_S,n` and `r_T,n`, both are nonnegative and

```text
(r_S,n + r_T,n)/2 <= g_n + tau_n.
```

Therefore each regret is at most `2(g_n+tau_n) -> 0`. Finally,

```text
(B_i(T_n)-B_i(S_n))
  - (U_i(T_n[i <- rho])-U_i(S_n[i <- rho]))
  = r_T,n-r_S,n,
```

whose absolute value has the same vanishing bound. For `m`, the opponents are
identical at the two endpoints, so its unrestricted cap is exactly invariant.

No hidden attainment assumption is used: an arbitrarily accurate actual
behavioral response at the half profile suffices.

## Exact scope

The compiler proves more than source-faithful causalization alone: it bridges
one horizontal minimum-fibre full-replacement seam and represents the actual
cap displacement by one common response.

It does **not** prove:

- that the cap displacement itself tends to zero;
- that every supplied response transports across the seam;
- a uniform estimate over all responses;
- small horizontal deviation leakage;
- a chronological Nash--Bellman edge;
- or consumption of any renewable-trace exit.

Thus “the fourth requested item is provable” is correct if that item means the
existence of this selected common-response cap compiler. It would be too strong
if the item meant the older arbitrary-response leakage predicate.

## Formal status

The supplied corrected Lean source follows the valid proof above, but its own
validation record says Lean elaboration was not rerun after the repair. This
review assigns no Lean-checked status.

Files inspected:

- `MINIMUM_FIBER_CAP_RESPONSE_COMPILER_PROOF.md`;
- `StoppingLawMinimumFiberCommonResponseCompiler.corrected.lean`;
- `CanonicalPairMinimumEndpointRenewal.corrected.lean`; and
- the prior PR 76 triage and renewable-handoff feedback.
