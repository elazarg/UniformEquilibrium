# Review of capacity-gap root matching and the persistent inner mark

Reviewer: `CODEX_HAHN`

Exact source reviewed: `notes/CODEX_SPINOZA__CAPACITY_GAP_ROOT_MATCHING_OR_PERSISTENT_INNER_MARK.md`

SHA-256: `1c8a4f9441f959ad4f3d1e72518d7124a33554effe6eaaf547909ab54aff8008`

Verdict: **PASS** as an ordinary-mathematics reduction, with the stated
nonconsumer boundary.

## Claim checked

The note proves a one-step alternative for two convergent payoff sources
whose bounded exact predecessor capacities differ by a fixed amount.  A
capacity-near first root is either separated from every exact root on the
other source, or it has a convergent exact mate and the capacity gap passes to
the two Bellman predecessors.  Iterating the matched branch retains the first
positive-absorption root as an inner literal mark.  Bounded Fin4 exact-block
hazard capacity then makes the later outer absorption summable.  Unless a
later sure root screens the mark, one fixed coalition at the moving inner
date keeps a positive terminal-mass floor, and each of its members' stopping
laws has no total-variation-convergent cofinal subsequence.

## Mathematical audit

The root-matching split is valid.  Compactness and closedness of the exact-root
graph put both root limits in the same limiting root set.  If the distance to
the low-side root set does not tend to zero, a subsequence has a positive
separation; otherwise an almost-nearest exact mate gives root convergence.

The capacity shift has the correct orientation.  Removing the first root
from a near-maximizing high path gives

```text
phi(high predecessor) >= phi(high source) - absorption(high root) - error,
```

whereas prepending the low root gives

```text
phi(low source) >= absorption(low root) + phi(low predecessor).
```

Subtracting and using convergence of the two roots preserves the gap up to a
vanishing loss.  Here `phi` is the absorption-charge version of the bounded
full-box capacity.  The checked bound on total marginal-hazard capacity is
strong enough for the later use because stage absorption is at most total
marginal hazard.

The fixed first-root absorption floor is inherited from the reviewed
two-sided singleton wall.  Later roots need not retain that wall, and the note
correctly does not claim that they do.  Diagonal compactification keeps every
finite predecessor word literal; it does not manufacture an infinite
chronological profile.

The finite/limit word orientation is correct: at depth `K` the chronology is
read from the newest outer root back to the original inner marked root.  If
all later absorption probabilities are strictly below one, summability gives
a positive product of their Continue probabilities.  Pigeonholing among the
fifteen nonempty Fin4 coalitions gives the stated `alpha/15` inner coalition,
and diagonal approximation justifies the conservative `R_infty*alpha/30`
actual finite-word floor.

The total-variation noncompactness argument is also valid.  A member of the
fixed coalition has a fixed positive mass of finite stopping times beyond
every fixed cutoff.  Total-variation convergence to one probability law
would transfer that lower bound to every finite tail of the limit law,
contradicting continuity from above.

The terminal screens are correctly limited.  Two sure quitters screen every
player's continuation cap.  For a pure singleton root, the unique quitter is
also screened only when its limiting cap is pinned to its singleton reward.
A single sure outsider without that pin is left as a handoff boundary.

## Scope and exact boundary

No issue was found with the `1/30` mass constant, the fixed-coalition
selection, or the no-total-variation-subsequence conclusion.  The result is
not a terminal consumer: positive projective reach belongs to a diagonal
family of finite words whose marked date escapes, not to one actual infinite
profile.  The note states this explicitly and makes no stationarization,
source reprojection, punishment-floor return, or uniform-payoff claim.

