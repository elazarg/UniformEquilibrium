# Review of two-sided singleton wall and unique-root capacity shift

Reviewer: `CODEX_HAHN`

Source reviewed at SHA-256:
`43d71ec684bb8e014c0114f988d2fe253aeea6f1b6c40136b08eb88fce160d81`.

## Verdict

**PASS.** I found no mathematical defect or claim-strength drift. The result is
a valid strict reduction, with the outward-versus-chronological boundary stated
correctly.

## Checks

1. Full terminal-semantic convergence transfers both the named cap pin and the
   named debt floor. With `gamma = delta/2`, the fixed-cap-pin theorem gives
   the stated uniform debt expenditure
   `min(delta/4, delta^2/(64M))` on both sibling sequences.
2. If the opponents of the named player absorb with probability at least
   `delta/(32M)`, joint absorption has that floor. Otherwise endpoint
   stability makes the named player's Quit endpoint strictly preferable, so
   exact complementarity forces that player to Quit surely. This proves the
   advertised all-root absorption floor.
3. Closedness of the exact-root graph plus compactness proves uniform collapse
   of both nearby root correspondences when the limiting root set is a
   singleton. No continuous selector is being assumed.
4. For the capacity shift, deleting the first edge of the nearly maximizing
   high path and prepending the arbitrary exact low root give the two correctly
   oriented dynamic-programming inequalities. Their subtraction yields the
   surviving gap because the two root absorptions converge to one another.
5. Fixed-depth iteration is legitimate after successive subsequence
   extraction. If no multi-root face appears, every finite initial segment of
   the limiting outward chain is an admissible exact predecessor path. The
   uniform finite-block capacity bound therefore makes its total absorption
   summable, and product-root absorption tending to zero forces the roots to
   all Continue.
6. The note does not reverse that outward infinite chain into a chronological
   tail. It explicitly withholds source ancestry, punishment-floor use, and a
   terminal consumer, which is the necessary qualification.

## Boundary retained

Only the first limiting face retains the quantitative singleton wall. After a
capacity-gap shift the wall can be lost, so neither later multi-root branching
nor the all-summable outward chain is consumed by this theorem.

## Delta check

The added summable per-depth error budget is valid. At stage `k`, the
asymptotic `o(1)` loss can be made at most `kappa/2^(k+2)` by a further
cofinal subsequence. These nested refinements define every fixed finite depth,
and the total loss is below `kappa/2`, so the two approximating successor
sequences retain the advertised capacity gap at every finite depth. If no
multi-root limiting face occurs, the unique limiting roots and their Bellman
successors form a correctly typed infinite **outward-prefix** chain. Each
finite initial portion is a finite exact predecessor path and hence is covered
by the global finite-block capacity bound. The new text still does not turn
that outward chain into a chronological tail.
