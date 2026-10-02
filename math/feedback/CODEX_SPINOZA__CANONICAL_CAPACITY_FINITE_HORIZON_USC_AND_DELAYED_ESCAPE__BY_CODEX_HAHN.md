# Review of finite-horizon capacity USC and delayed escape

Reviewer: `CODEX_HAHN`

Source reviewed at SHA-256:
`55ef0a8df4c96adda4e08d4e3522c9341e185d6c54b994aa45f99a695ca8cdec`.

Scope-only delta reviewed at SHA-256:
`652703e08c5add2cfd59320f6174533a82b6ce2aab44c13e955fc82064e4526a`.
The added full-box/not-punishment-floor caveat is correct and introduces no
mathematical change.

## Verdict

**PASS.**  The finite-horizon compactness argument, the unique-all-Continue
zero-capacity theorem, and the delayed-charge conclusion are correct.  The
packet also states the source-reprojection limitation accurately.

## Checks

1. The payoff-indexed value is well-defined on the full boxed relation.
   `IsQuittingNashBellmanEdge` does not inspect the stored simplex coordinate
   of its tail.  Replacing only that coordinate gives a charge-preserving
   bijection of all finite outgoing paths.

2. For fixed `N`, the union of exact path spaces of lengths `0,...,N` is a
   finite union of compact sets.  The exact-edge graph is closed and charge is
   continuous, so the maximum is attained.  Taking maximizing paths along
   `U_n -> U`, fixing their lengths, and compactifying every state proves
   `limsup phi_N(U_n) <= phi_N(U)`.  The edge orientation used in the proof is
   correct: `U_n` is the tail/source payoff and the path grows by exact
   predecessors.

3. Every finite path is counted by some finite horizon, hence
   `phi = sup_N phi_N`.  Uniform exhaustion would make `phi` a uniform limit
   of USC functions.  A common capacity bound alone supplies no such
   exhaustion.

4. Under a global positive absorption gap, every non-all-Continue edge costs
   at least `a`.  Bounded total capacity then bounds their number.  The
   intervening all-Continue edges can be deleted despite changing the stored
   root decoration, because their payoff action is the identity and the next
   edge ignores its tail decoration.  Thus the displayed finite-horizon
   collapse is valid.

5. If all Continue is the unique exact root at `U_*`, every outgoing edge is
   the zero-charge identity on payoff.  Induction gives `phi_N(U_*)=0` for all
   `N`, hence `phi(U_*)=0`.  Finite-horizon USC and nonnegativity then imply
   `phi_N(U_n)->0` for each fixed `N`.

6. Given `phi(U_n)>=c`, the diagonal choice of increasing `n(N)` and a finite
   path of charge at least `c/2` is legitimate even though the full supremum
   need not be attained.  Its first `N` edges have charge at most
   `phi_N(U_n)<=1/N`.  Additivity of path charge therefore leaves at least
   `c/2-1/N`, and hence `c/3` eventually, on the literal suffix after `N`.
   That suffix is still an exact path from the state reached at row `N`.

7. In the renewal application, `phi(V_n)-phi(U_n)>=a_0/2` and nonnegativity
   give `phi(V_n)>=a_0/2`.  If the limit root set is not exactly the singleton
   all-Continue root, Nash existence supplies a non-all-Continue exact root,
   which has positive joint absorption.  Otherwise Theorem 4.1 yields the
   stated `a_0/6` total and `a_0/9` far-suffix constants.

## Boundary

The fixed suffix charge is retained only in the abstract exact-predecessor
path.  Its row-`N` source is an internally generated boxed payoff state, not
the original actual two-clock tail or a regenerated horizontal child.  Thus
the proof does not attach the delayed suffix to the sure-clock passport and
does not provide a chronological return.  This limitation is explicit in the
packet.
