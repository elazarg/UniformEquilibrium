# Quiet-extension classes: primary-source scope

This is a bounded comparison of the original papers with the two quiet-extension
claims. It establishes attribution and hypothesis distinctions, not worldwide
priority or a new proof of the cited papers.

## Three-player existence

Eilon Solan, *Three-Player Absorbing Games*, Mathematics of Operations Research
24 (1999), 669–698, [author-hosted original](https://www.math.tau.ac.il/~eilons/three.pdf).
Printed pages 673–674 were read directly as page images.

Definition 3.1 permits behavioral strategies. Definition 3.2 fixes the payoff
target before the accuracy and requires both prescribed payoff delivery and
unilateral payoff bounds for every sufficiently large finite-average horizon.
It additionally imposes infinite-play liminf/limsup inequalities. Theorem 3.3
covers every three-player absorbing game without a reward-sign assumption.

Consequently the unrestricted three-player child theorem is an existing
dependency, not an increment supplied by either quiet-extension packet.
The project declaration
`quittingGame_exists_uniformEquilibriumPayoff_threePlayer`
(`UniformEquilibrium/Quitting/Classification/ThreePlayer/Existence.lean`)
provides the needed quitting-game existence input independently. Neither the
paper's theorem nor its definition alone supplies an ambient outsider adapter.

## A payoff-restricted multiplayer theorem

Eilon Solan and Nicolas Vieille, *Quitting Games*, Mathematics of Operations
Research 26 (2001), 265–285,
[author-hosted original](https://www.math.tau.ac.il/~eilons/quitting19.pdf).
Theorem 1.2 and its assumptions on printed page 267, together with the
root-condition refinement in Proposition 2.2 on printed page 270, were inspected.

Theorem 1.2 normalizes every own singleton to one and bounds each quitter's
payoff at coalitions containing that player by one. The capped-clock fixture
violates this bound at coalition {0,2}, whose active players receive two.
The passive-row class also allows collision completions violating the bound.
Proposition 2.2 uses an additional one-shot root condition; its applicability
cannot be inferred merely from the table's membership in either new class.

Thus the explicit hypotheses of this named payoff-restricted theorem do not
subsume the two proposed families. This comparison does not rule out other
existing methods for particular tables in those families.

## Proof obligations unaffected by the comparison

The capped-clock theorem must prove its full unilateral response comparison
from the finite raw inequalities. The passive-row theorem must construct
the ambient continuation floors and retain the complete-response bound.
Their independent reviews check these respective adapters. Citing a solved
three-player game does not replace either obligation.
