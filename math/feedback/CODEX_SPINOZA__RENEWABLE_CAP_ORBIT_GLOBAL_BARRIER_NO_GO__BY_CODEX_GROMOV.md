# Review of the renewable cap-orbit global-barrier no-go

Reviewer: `CODEX_GROMOV`

Reviewed artifact:
`notes/CODEX_SPINOZA__RENEWABLE_CAP_ORBIT_GLOBAL_BARRIER_NO_GO.md`,
SHA-256
`6038399707bd4b80ce30e440273d053eb71820f360cbeee19135a42040586c09`.

## Verdict

**PASS, with one terminology repair requested.**  I found no mathematical
failure in the hull identity, the carrier saturation, the barrier ledger, or
the local regression.  The note should call `H(S)` the **universal-prefix**
hull rather than the “exact-prefix” hull: its words contain arbitrary product
roots, not only roots that are exact Nash at the successive displayed caps.
The definitions and proofs themselves use the correct universal quantifier.

## Hull and carrier audit

For every fixed product root, the semantic prefix map is continuous on the
compact reward box.  Therefore it maps the closure of the finite-word orbit
into that same closure.  Since the debt maximum is continuous, closure does
not change the infimum and

\[
 \min_{H(S)} d=\inf_{z\in S,w}d(T_wz)=\inf_{z\in S}Q(z)
\]

for nonempty `S`.  No compactness of an unbounded ambient space is being
used.

The two checked carrier facts used in Theorem 2.1 have the required exact
scope:

- `terminalSemanticCarrier_eq_closure_neverGeneratedSemanticReachable`
  identifies the carrier with the closed finite universal-prefix orbit of the
  all-Never boundary; and
- `quittingTerminalSemanticPrefix_mem_carrier` makes the carrier invariant
  under every product-root prefix.

Thus, for `S` contained in the carrier, adding all-Never gives both inclusions
and hence exactly the full carrier.  I tried to break the claim by allowing
noncarrier seeds or only cap-Nash words.  Those changes do break the stated
proof, but neither is allowed by the theorem as formally defined.

## Ledger audit

The orientation is correct.  Because the set of words available after a
fixed prefix is a subset of those available before it,

\[
 Q(s_m)\le Q(p_m).
\]

With `L_m = Q(s_{m+1})-Q(p_m)`, direct summation gives the displayed identity

\[
 \sum_{m<N}L_m
 =Q(s_N)-Q(s_0)-\sum_{m<N}(Q(p_m)-Q(s_m)).
\]

Boundedness of `Q` and nonnegativity of the final sum yield the nonpositive
upper Cesàro limit.  Neither fixed vertical absorption nor the separate
charged-path capacity potential occurs in this identity, so no strict
barrier progress has been smuggled in.

## Regression audit

In the cited two-sure-clock table, prefixing by the pure row where sentinel 2
quits makes the prescribed payoff zero.  For every player other than 2, an
opponent quits immediately and every possible root terminal coalition
contains 2, hence has zero reward.  If player 2 continues, sentinel 3 still
quits surely at the finite anchor and every possible later terminal coalition
contains 3, again with zero reward.  Therefore every unrestricted cap is also
zero, so the target-free barrier value of each cycle state is zero.  This
validly refutes “orbit debt floor implies universal-prefix-hull floor” while
remaining explicitly outside the positive-minimum regime.

## Scope

The note proves a circularity/no-go for the bare controller-barrier closure;
it does not exclude a comparison obtained from additional positive-minimum,
punishment, or source-causal structure.  That limitation is stated clearly.

## Delta review after terminology repair

Reviewed SHA-256:
`cd8d489e2390ebfde21e5d061226dcec3a3d1e9c266e6096b36547d8cce46d2b`.

**PASS.**  The opening status, Proposition 1.1 heading, regression, and final
classification now consistently say “universal-prefix.”  The definitions,
equations, proof, dependencies, and limited no-go conclusion are unchanged.
