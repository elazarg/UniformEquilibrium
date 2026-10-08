# FTV1996 restricted-optimizer ranking specification

The primary source is Flesch, Thuijsman and Vrieze, *Recursive repeated games
with absorbing states*, Remark 1, journal page 1022, DOI
`10.1287/moor.21.4.1016`. The scanned primary source is available from the
[author's copy](https://dke.maastrichtuniversity.nl/f.thuijsman/recursive%20repeated.pdf).

The paper states that equilibria for its linearized rewards have properties
similar to delta-proper pairs and that the limiting approximate-equilibrium
argument follows analogously. This note specifies the remaining formalization
dependency; it does not supply that proof, assert a mathematical gap, or infer
the ranking property from compact Nash existence alone.

## Literal domain and objective

For a finite action type A of cardinality m, the domain D(A, delta) consists of
real probability vectors x satisfying

- sum over U of x(a) >= delta^(m - card U), for EVERY nonempty proper subset U;
- ordinary simplex nonnegativity and total mass one.

For an arbitrary signed value vector v, the objective is sum_a x(a) * v(a).
An optimizer maximizes this objective against every alternative in this SAME
domain. This is not optimization on the weaker coordinate-floor simplex, nor
optimization of the original nonlinear stationary payoff.

`remark1RestrictedStrategies` and the linearized auxiliary-game construction
are in `Literature/future/FleschThuijsmanAndVrieze1996.lean`. The printed full
delta range is already refuted by its empty two-action domain at delta 3/4.
The ranking task must therefore use a justified sufficiently-small range.

## Required uniform-modulus contract

For each finite nonempty A, seek a positive cutoff eta and a function r_A of
delta, chosen BEFORE the value vector and optimizer, such that:

- eta is at most both 1/2 and the inverse of m;
- r_A(delta) is positive and less than one for 0 < delta <= eta;
- r_A(delta) tends to zero as delta tends to zero from above;
- for every such delta, EVERY signed v and EVERY optimizer x on D(A, delta),
  simultaneously for all actions i,e, v(e) < v(i) implies
  x(e) <= r_A(delta) * x(i).

No particular formula for r_A is asserted here. A proof may first establish a
uniform quantitative bound and then choose a suitable modulus and cutoff.
The modulus must not depend on the payoff gaps, optimizer, or chosen action
pair. Equal-value actions impose no strict-ranking inequality; arbitrary
optimizer choices inside tied value classes remain covered. For a singleton
action type, the simplex has one point and strict ranking is vacuous. An empty
action type has no simplex strategy and is not a nonempty-game case; positive
delta bounded by inverse cardinality already excludes it in the current API.

## Existing consumers and the precise missing bridge

`IsDeltaProperPair` (`MathUE/Probability/RatioProperPair.lean`) requires both
strict-ranking inequalities with one positive parameter below one, full
support, and actual simplex membership. Applying the optimizer contract to
each auxiliary-game player would provide those inequalities at a common
vanishing parameter, for example by taking the maximum of the two moduli.
Full support follows from the literal singleton constraints, with the
singleton-action case handled by simplex mass one. Compact subsequence
selection then gives a proper-pair sequence without changing its domain or
replacing its source with `exists_properPair`.

`eventually_row_maximal_of_limit_pos`, its column companion, and the actual
bad-absorption-mass estimates are in
`UniformEquilibrium/ProofView/Concepts/Stochastic/Models/RecursiveAbsorption/ProperPairApproximation.lean`.
`eventually_isAsymptoticNash_of_absorbing_proper_limit` and
`isAsymptoticNash_of_pure_gaps` are public consumers in the sibling
`ProperPairLimit.lean`. The profitable recurrent-row and recurrent-column
limit arguments are checked private declarations there; using an externally
produced auxiliary sequence may require a reviewed extraction of those
consumers, not copied proofs or a call to an unrelated existence producer.
`BestReplyMassEstimate.lean` also exposes the arbitrary-sequence row and column
payoff floors from vanishing conditional bad-reply ratios.

All these actual-game consumers retain signed rewards, zero-hazard branches,
and unrestricted behavioral deviations. None proves the missing literal
polytope optimizer property. Searches of project, GameTheory, and Mathlib
found no reusable cardinality-base-polytope greedy or exchange theorem.
The familiar finite-optimization route is a tight lower-value-subset or
feasible improving coordinate-exchange lemma for these exact constraints,
followed by finite subset inequalities giving the uniform ranking modulus.
That source-sketch formalization needs a reviewed proof plan before code.
The nonlinear restricted-game assertion and original absorbing-stage
reduction remain separate obligations.
