# Review of Proposition 6BB

## Claim checked

I checked the current component-pair smoothing construction in Proposition
6BB: smooth every source and full-replacement stopping law by the same
full-support zero-Never law, rebuild the frozen radial mixtures with the same
outer weights and inner scale, and then apply the reviewed periodic kernels
6AZ/6BA.

## Verdict

**PASS in the stated conditional nearby-source scope.**  The affine component
identity, product-coupling constants, zero-Never and finite-reach fields, and
the prescribed/rectangle periodic handoffs are correct.  The proposition
does not produce its componentwise zero-Never premise and does not preserve
equality with an independently supplied source port.

For the rectangle sentence, `aligned` must retain its established meaning
from Proposition 6V: `first` is the atom mover and `second` is the observer.
With that convention no statement repair is needed; without the surrounding
definition, this should be restated explicitly before invoking 6BA.

## Algebra and provenance

For an active coordinate, smoothing both components by the same law `G`
commutes exactly with the radial mixture:

```text
(1-w h)[(1-epsilon)A+epsilon G]
  +w h[(1-epsilon)R+epsilon G]
= (1-epsilon)[(1-w h)A+w h R]+epsilon G.
```

Thus `(6BB.4)` is exact, not an approximation.  Replacing `first` in the
rebuilt source by `Smooth_epsilon(R_first)` is literally the full-replacement
endpoint of the rebuilt component chart.  The old source and replacement
laws have changed, but their labels, outer coefficients, inner coefficient,
and reset orientation survive inside the new chart.  This is the precise
component provenance claimed by the proposition; it is not source-only
relocation.

For `0<w_j h<1`, affinity of the Never atom gives

```text
Never(P_h(j))=(1-w_j h)Never(A_j)+w_j h Never(R_j).
```

Both coefficients are positive, so zero Never of the executed marginal is
equivalent to zero Never of both named components.  Smoothing with a
zero-Never `G` preserves zero Never under the displayed premise.  Since `G`
has positive survival through every finite cutoff, every rebuilt coordinate,
including coordinates whose original Never mass was positive, has positive
finite-cutoff survival.  In particular both the rebuilt source word and the
rebuilt full-endpoint word are literally reachable at every finite cutoff.

## Coupling constants

Couple each original marginal to its smoothed marginal by keeping the old
law with probability `1-epsilon`.  A union bound gives mismatch at most
`n epsilon` for both the source product and the full-endpoint product.  With
rewards in `[-M,M]`, prescribed payoffs move by at most
`2 M n epsilon`.  The same coupling is uniform in a fixed player's behavioral
deviation because only the opponent environment matters; the stated
`2 M n epsilon` unrestricted-cap bound is therefore valid (and slightly
loose).  Adding payoff and cap errors gives the debt bound
`4 M n epsilon`.

A reward-weighted source-minus-endpoint terminal atom has two probability
terms.  Each changes by at most `n epsilon`, so its magnitude changes by at
most `2 M n epsilon`, exactly `(6BB.7)`.  Rectangle comparisons use the same
pure-time observer override on both sides; only the remaining coordinates
are smoothed, so the same displayed bound remains valid.  Consequently a
fixed signed atom, its orientation, and any strict pure-time comparison
survive after choosing `epsilon` sufficiently small.  If an endpoint-debt
field is `O(h^2)`, taking `epsilon=o(h^2)` preserves it; taking
`epsilon=o(h)` preserves any already quantified `kappa h` inequality after
a fixed reduction of `kappa`.

## Periodic handoff and boundary

The rebuilt source has two actual zero-Never labels and positive finite word
reach, so reviewed Proposition 6AZ applies in the prescribed arm.  In the
rectangle arm, the aligned observer is `second`, and the rebuilt endpoint
mover law `Smooth_epsilon(R_first)` also has zero Never; these are precisely
the extra hypotheses of reviewed Corollary 6BA.  Periodicization then gives
the literal self-loop, two persistent deleted clocks, and the required
source/endpoint tail forgetting.  The same fixed word can answer smaller
declared scales only because the current packet interface lower-bounds
progress and imposes no root-mesh upper bound; the note states this
qualification.

The conditional boundary is exact.  Proposition 6BB assumes

```text
Never(A_first)=Never(R_first)=Never(A_second)=Never(R_second)=0.
```

Neither the tangent family nor the checked packet supplies these four facts.
The construction also replaces the actual source by a nearby smoothed source,
so it does not enter an arbitrary reached port or solve the separate
candidate-anchor problem.  What it proves is that, once the componentwise
zero-Never premise is supplied, smoothing and periodic restart introduce no
additional algebraic, atom, cap, or provenance obstruction.

## Sources inspected

- `notes/CODEX_RAMSEY__POSITIVE_ATOM_ROOT_REPAIR_FLOOR.md`, current
  Proposition 6BB and the reviewed Proposition 6AZ/Corollary 6BA on which it
  depends.
- `feedback/CODEX_RAMSEY__POSITIVE_ATOM_ROOT_REPAIR_FLOOR__BY_CODEX_CEDAR__PROPOSITIONS_6AY_6AZ.md`.
- `feedback/CODEX_RAMSEY__POSITIVE_ATOM_ROOT_REPAIR_FLOOR__BY_CODEX_CEDAR__COROLLARY_6BA.md`.
