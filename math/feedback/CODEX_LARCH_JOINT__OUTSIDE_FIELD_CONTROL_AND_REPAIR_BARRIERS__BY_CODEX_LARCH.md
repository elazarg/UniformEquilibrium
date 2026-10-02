# Review of control translation and repair barriers

Reviewer: CODEX_LARCH, 2026-09-07. Ordinary mathematical review only.

The [control sketch](../notes/CODEX_LARCH_JOINT__OUTSIDE_FIELD_CONTROL_AND_REPAIR_BARRIERS.md)
passes its stated finite-switching and counterexample claims. No Lean check
or verification of a general control theorem was needed: the claims follow
from the displayed finite product-space construction.

Fixed coordinate reset fields depend on disjoint variables and commute.
The scalar mixed term −ab therefore cannot be interpreted as a nonzero
commutator displacement. The note correctly leaves open only a substantially
different construction involving state-dependent selectors and constrained
motions.

Full payoff and response-cap discrepancies are each at most 2M times the
sum of marginal total variation distances; hence E is 4M-Lipschitz. Every
partially completed coordinate sweep lies within D(p(s),p(s+h)) of its start.
The chosen h gives the stated exploitability budget and a strictly positive
minimum step before clipping, so finitely many sweeps reach the endpoint.
This argument also controls interpolation along each coordinate chord.

The dyadic-band count is correct. Below r=(η/c)^(1/k), O(r/η) sweeps
suffice. Above r, the bound per band is proportional to
η^(-(k−1)/k) 2^(-j(k−1)), plus one crossing step. Thus quadratic descent
costs O(η^(-1/2)) and linear descent costs O(log(1/η)), with constants
depending on the supplied curve and finite player count.

In the exact two-coordinate example, before the maximum reaches √η any
single-coordinate increase in that maximum is at most 8η/3. The bound also
applies to the final crossing step and does not assume coordinate monotonicity.
Therefore the Ω(η^(-1/2)) lower bound is valid on that specified face.

The affine-coordinate barrier example correctly rules out replacing a whole
low-sublevel path by an endpoint-only hypothesis. Its continuous barrier also
rules out finite coordinate jumps with both endpoints below the barrier,
because this particular objective is affine on every such chord.

Usefulness judgment: this is a valid small consumer of supplied common
curvature and distinguishes exact monotone repair from vanishing-overrun
repair. It does not generate a joint descent path. More critically, its
strategy-construction sequence is not a chronology of reached histories in
the quitting game. These limitations are explicit in the note and justify
ranking it below the quantitative law-to-cap and quadratic-compatibility
candidates for the immediate UE search.
