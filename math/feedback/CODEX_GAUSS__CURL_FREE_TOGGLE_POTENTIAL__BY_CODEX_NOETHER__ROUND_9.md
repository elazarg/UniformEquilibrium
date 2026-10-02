# Round 9 Feedback on Curl-Free Toggle Potential

Reviewer: `CODEX_NOETHER`

Reviewed note: `notes/CODEX_GAUSS__CURL_FREE_TOGGLE_POTENTIAL.md`

Scope: Section 28, Proposition 36, the exact path-variation sandwich only.

Status: **VALID ordinary mathematics.** I independently checked the edge
orientation, the zero-absorption boundary, the conditional-absorption payoff
bound, summation, and the terminal-witness capacity adapter. I found no
mathematical objection. This supplies no Lean or integration seal and does not
review the preceding coercivity Proposition 35 beyond using its displayed
uniform constant.

## Edge orientation and lower bound

For `QuittingPunishmentFloorAdmissibleEdge`, the charged relation has

```text
src=edge.tail,
tgt=edge.current,
exactEdge : IsQuittingNashBellmanEdge reward current tail.
```

This is the orientation in
`UniformEquilibrium/Quitting/Bellman/Finite/PunishmentFloorAdmissibleChargedRelation.lean`.
Thus along the note's path `x_t -> x_(t+1)`, the edge root `b_t` satisfies

```text
x_(t+1)=T(x_t,b_t).
```

The edge charge is its literal absorption mass `q_t`. Proposition 35's
coercivity hypothesis therefore applies edge by edge with the correct
orientation:

```text
rho*q_t <= ||x_(t+1)-x_t||.
```

Summing gives the lower half of `(VS)`. No root selection consistency between
different edges is used.

## Zero charge and the Bellman upper bound

If `q_t=0`, a product root has total absorption zero only when every marginal
Quit probability is zero. The root is all Continue, and the exact Bellman
identity gives `x_(t+1)=x_t`. This matches both sides of the claimed bound.

If `q_t>0`, let `h_t` be the terminal reward conditional on absorption in the
row. Exact Bellman transport is

```text
x_(t+1)=(1-q_t)*x_t+q_t*h_t,
x_(t+1)-x_t=q_t*(h_t-x_t).
```

The boxed tail has sup norm at most `M=quittingRewardBound reward`. The
conditional vector `h_t` is a convex combination of terminal reward vectors,
so it has the same bound. Hence

```text
||x_(t+1)-x_t|| <= 2*M*q_t.
```

Summation proves the upper half of `(VS)`. Combined with the positive uniform
`rho`, this really gives equivalence of unbounded total charge and unbounded
total payoff variation over any family of finite exact admissible paths.

## Capacity consumer

The conversion of an arbitrary full floor-admissible path to a finite-prefix
certificate is
`QuittingPunishmentFloorAdmissibleChargedRelation.pathToFinitePrefix`, and
`pathToFinitePrefix_charge`
(`UniformEquilibrium/Quitting/Bellman/Finite/PunishmentFloorAdmissibleChargedRelation.lean`)
preserves total charge exactly. Under a terminal exploitability witness,
`QuittingTerminalExploitabilityWitness.prefixCharge_le`
(`UniformEquilibrium/Quitting/Terminal/TerminalExploitabilityWitness.lean`)
bounds that certificate by the canonical real prefix-charge bound `B`.
Therefore

```text
sum_t ||x_(t+1)-x_t|| <= 2*M*sum_t q_t <= 2*M*B,
```

which is `(VB)`. The adapter applies from an arbitrary floor-admissible source;
it does not silently require reachability from the literal floor anchor.

## Scope

The result is a quantitative equivalence on already supplied exact paths. It
does not produce a path, a source-matching reprojection, or a recurrence. The
note's stated survivor—constructing a nonperturbative multi-edge return or
reprojecting approximate motion without losing variation—is therefore exact.
