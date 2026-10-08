# FTV1996 Example 1 and the Section 4 cross-reference

## Primary source

J. Flesch, F. Thuijsman and O. J. Vrieze, *Recursive repeated games with
absorbing states*, Mathematics of Operations Research 21 (1996), 1016–1022,
DOI `10.1287/moor.21.4.1016`.
The [author-hosted scanned paper](https://dke.maastrichtuniversity.nl/f.thuijsman/recursive%20repeated.pdf)
was inspected visually. Example 1's table is on journal page 1018; its printed
proper-family conclusion continues on page 1019. Section 4's opening paragraph
on page 1021 cites Example 1 for nonexistence of exact stationary equilibria.

## Checked correction

The literal Example 1 table has two actions per player. Only the first-row,
first-column entry remains live, with zero payoff. The other entries absorb
with probability one and have rewards `(2, −2)`, `(1, −1)` and `(0, 0)` in
row-major order. The stationary pair with row weights `(1/2, 1/2)` and pure
first-column play is an exact equilibrium; its live-state payoff is `(1, −1)`.
Consequently, Example 1 does not witness the nonexistence cited in Section 4.
This does not refute that nonexistence phenomenon for recursive absorbing games
in general or the printed small-error exclusion for the delta-proper family.

The declarations `example1_halfFirst_payoff`, `example1_halfFirst_equilibrium`
and `example1_section4_crossReference_refuted` in
`Literature/future/FleschThuijsmanAndVrieze1996.lean` are proved in Lean under
that file's imports. Their separate axiom checks use only `propext`,
`Classical.choice` and `Quot.sound`. The named proposition
`Example1StationaryExclusionClaim` records the nonexistence assertion suggested
by the cross-reference, not a separately numbered theorem printed for Example 1.

## Semantic scope and remaining obligations

The witness uses `canonicalGame example1Data` and the literal expected pathwise
liminf payoff `canonicalPayoff` under its actual infinite-play measure. One
stationary pair satisfies `IsεAsymptoticNash` at error zero at every initial
state, against every unilateral behavioral deviation. The proof delegates
the checked arbitrary-action recursive-absorption behavioral payoff caps,
including the negative column payoff, and the actual constant-payoff identity
at absorbing initial states.

This canonical model has literal action-independent absorbing rewards. The
result does not establish the paper's general reduction from absorbing stage
games with state-dependent legal actions, nor a fixed-target uniform-equilibrium
payoff theorem. The printed delta-family's proper limit and small-error
exclusions are separately proved in the same paper file; they do not follow
from the cross-reference witness alone. The remaining examples and remarks
and the original-model reduction are separate paper-coverage obligations.
The paper remains in the partial Literature lane.
