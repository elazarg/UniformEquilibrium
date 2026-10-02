# Review of renewable cap-orbit global barrier no-go

Reviewer: `CODEX_HAHN`

Originally reviewed SHA-256:
`6038399707bd4b80ce30e440273d053eb71820f360cbeee19135a42040586c09`.

Delta-reviewed terminology-only repair SHA-256:
`cd8d489e2390ebfde21e5d061226dcec3a3d1e9c266e6096b36547d8cce46d2b`.

## Verdict

**PASS.**  I found no mathematical error in the hull identity, the global
saturation collapse, the signed barrier ledger, or the local regression.

## Claims checked

The note proves four precise statements.

1. If
   \(Q(z)=\inf_w d(T_wz)\), then the minimum of \(d\) on the closed
   arbitrary-product-prefix hull of a nonempty seed set \(S\) is exactly
   \(\inf_{z\in S}Q(z)\).
2. If \(S\) lies in the terminal-semantic carrier and the all-Never boundary
   is added, the resulting closed arbitrary-product-prefix hull is the whole
   carrier.
3. Along an alternating vertical-prefix/horizontal-response sequence, the
   horizontal barrier displacements satisfy the exact signed telescope (10),
   and hence have nonpositive upper Cesaro average.
4. The reviewed two-sure-clock response-cycle table has displayed maximum
   debt one at all four cycle states but has \(Q=0\) at each state.

## Audit

For Proposition 1.1, continuity of each semantic prefix map gives prefix
invariance of the closure.  Since \(d\) is continuous, closure does not
change the infimum, and the two nested infima are definitionally the infimum
over all seed/word pairs.  Compactness turns this into a minimum.  The proof
correctly assumes the seed set is nonempty when asserting existence of the
minimum.

For Theorem 2.1, I checked the named carrier theorem
`terminalSemanticCarrier_eq_closure_neverGeneratedSemanticReachable` in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticGlobalDebtBarrierCertificate.lean`.
It gives exactly the inclusion from the all-Never-generated hull to the whole
carrier.  Prefix closure and closedness of the carrier give the reverse
inclusion once all additional seeds lie in the carrier.  Thus adding
\(e_\infty\) really does collapse the proposed local saturation to the whole
carrier; there is no missing reachability direction.

For the ledger, \(p_m=T_{w_m}s_m\) implies \(Q(s_m)\le Q(p_m)\), because
the words starting with \(w_m\) are a subset of all words available in the
infimum defining \(Q(s_m)\).  Expanding
\(Q(s_{m+1})-Q(p_m)\) through \(Q(s_m)\) gives (10) with the displayed
sign.  Boundedness of \(Q\) and nonnegativity of every vertical increment
then give (11).  No absorption-dependent strictness is smuggled into this
argument.

For the regression, the reward table in
`CODEX_GROMOV__TWO_SURE_CLOCK_FINITE_RESPONSE_CYCLE_NOGO` makes every reward
vector on a coalition containing player 2 equal to zero.  Prefixing any of
the four cycle states by the pure root where only player 2 Quits therefore
sets prescribed payoff and every unrestricted cap to zero: an outsider is
screened at the root, while player 2's continuation/cap is also identically
zero in this table.  Hence the claimed \(Q(z_X)=0\) follows.  Directly
checking the four cycle states gives maximum debt one, as stated.

## Delta review

The author replaced the potentially ambiguous phrase “exact-prefix hull” by
“universal-prefix hull” and made no mathematical change.  The repaired term
now advertises correctly that definition (3) ranges over arbitrary product
roots, not only Nash roots.  **PASS** on the repaired exact SHA above.

The no-go is scoped correctly.  It does not exclude a future comparison
using positive-minimum Fin4 structure on the specific cap-child seam, and it
does not infer a negative certificate from a local response orbit.
