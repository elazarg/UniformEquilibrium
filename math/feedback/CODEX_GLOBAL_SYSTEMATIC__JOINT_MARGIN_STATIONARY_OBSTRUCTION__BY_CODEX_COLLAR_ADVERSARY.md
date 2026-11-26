# Independent review: joint observer margins and stationary obstruction

Reviewer: CODEX_COLLAR_ADVERSARY. **Mathematical verdict: PASS.**
Internal obstruction only; no export-gate or Lean claim.

Reviewed the complete
[note](../notes/CODEX_GLOBAL_SYSTEMATIC__JOINT_MARGIN_STATIONARY_OBSTRUCTION.md),
SHA256 `fb707a2927478e418f567ae8b817e2ed747854a712719e6fe660b7cd8b1f8855`,
and its complete
[exact checker](../experiments/CODEX_GLOBAL_SYSTEMATIC__JOINT_MARGIN_STATIONARY_CHECK.py),
SHA256 `e8b81ccf9b6073bbbe09b1067547f72fc09cb4fabef2af5d0ff6c2af661969a3`.
No other review was used as evidence.

## Claim and original-game semantics

The specified original own-singleton-one game has all four raw observer
margin capacities positive, a strictly positive regret floor over ALL
stationary profiles, and no absorbing finite-calendar exact terminal Nash profile.
Its period-three strategy is nevertheless an absorbing exact terminal
Nash profile and a uniform equilibrium. This refutes the suggested
implication from joint margin positivity to stationary approximate equilibria
or exact finite-calendar equilibria. It does not exclude approximate
finite-calendar families, refute UE existence, or show that every
hypothetical-counterexample condition holds.

The sixty native coordinates are unambiguous. Adding one to terminal
rewards leaves live and AllNever rewards zero. The proof never globally
shifts Never payoffs: its stationary and periodic response comparisons use
proper opponents; its root comparison uses the explicit continuation-cap
identity. Solo stationary hazards are treated separately.

## Table, singleton screens, and raw capacities

I independently reconstructed all sixty coordinates and verified by exact
symbolic arithmetic the singleton matrix, determinant `1344/25`, inverse
pivot column `(1600,1,1,1)/3`, and positive test direction `(800,1,1,1)`.
The R0 argument is exhaustive: a positive core coordinate forces `z0=0`;
core supports of sizes one, two, and three fail respectively by a negative
outsider, nonzero reciprocal entries, and invertibility. A pivot-only
support fails its negative outsider entries.

Independent enumeration gives `C=(5/4,-1,-1,-1)`. For pivot0 all observer
A entries are one. For a core pivot they are `(-1,1,1)`, with player0 first.
Thus `Lambda0=1` and every other capacity is `1/17`, attained at `x=8/17`.
These differences are unchanged in the original game.

## Sure roots and finite calendars

I rederived all four Quit-minus-Continue polynomials from the table.
For original continuation cap B the native continuation is exactly `B-1`.
Every actual original cap `B0>=1`, so the sole continuation restriction
needed in the sure-root census, `v0>=0`, always holds.

At `q0=1`, the complete core Nash census is the three types printed in the
note; all give a strictly negative player0 gap even at `v0=0`. With a sure
core player, `q0=0` forces all core hazards one and a profitable player0
entry. For `0<q0<1`, player0 indifference forces `ab=4/9`. The two additional
sure-hazard cases fail by the negative `-5/18` gap; the remaining interior
case gives `36a^2-51a+20=0`, discriminant `-279`.

An absorbing finite-calendar product law has a reached sure hazard, since
some private clock is proper with finite support. Exact full-response Nash
implies a Nash root against actual child caps there, including a root with
zero all-Continue probability. The census therefore applies to arbitrary
complete behavioral profiles with finite calendars, not just pure schedules.

## Complete stationary exclusion and rational certificate

The stationary gain is `(1-H)Q-P`, as obtained by eliminating the stationary
value from its Bellman equality. Its boundary sign conditions are correct.
Solo owners admit the explicit improving observer; sure hazards are already
excluded. At `q0=0`, a missing core hazard creates a positive gain. With all
three core hazards interior, the symmetric strictly increasing function T
forces equality of their hazards. The common solution exceeds `4/5`, giving
player0 a strictly profitable Quit offer.

The remaining case has all four hazards interior and core product `4/9`.
I independently expanded the gain and verified every coefficient of
`F=C+v B-v^2 D`. Its three cyclic evaluations match exactly the three core
rows. Every remaining profile maps into the checker's closed domain.

I inspected every interval operation and branch. All endpoints and operations
are exact Fractions; reciprocal denominators stay positive. Intersecting the
derived c interval with `c<=1` is sound. Each discarded box is infeasible or
has a gain interval excluding zero. Closed bisections cover their parent;
small unresolved boxes raise failure. Thus completed exhaustion is a finite
exact proof, not a numerical search heuristic. Independent execution returned
`EXACT RATIONAL PASS: no simultaneous zero; boxes 9589`.

## Positive stationary regret floor

I separately audited the final compactness extension. At a limit with at
least two active owners, all opponents' absorption denominators stay
positive, so prescribed values and both endpoint offers are continuous.
Every deadline offer lies between Quit0 and Never; endpoint inequalities
therefore give an excluded exact stationary Nash profile. At a nonzero solo
limit, the outsider's limiting Quit0 gain is `16-15s>=1` for a core owner,
or `1/100+(99/100)s>=1/100` for owner0, with `s` its positive hazard.

At a zero-hazard limit, normalize by the total hazard. The first-order
absorption numerator has singleton coefficient `1+Gamma alpha`, so the
prescribed original limit is exactly the value printed in the note.
Quit0 forces `Gamma alpha>=0`. For `alpha_i<1`, the Never expansion has
positive opponent denominator `1-alpha_i`; its comparison gives
`alpha_i(Gamma alpha)_i=0`. If `alpha_i=1`, the diagonal-zero identity
already gives that equality. The nonzero normalized alpha contradicts R0.
Thus every possible limit of a vanishing-regret sequence is excluded.
Fixed profitable terminal deviations persist at long finite horizons by
bounded convergence, validating the stated stationary uniform-equilibrium
consequence. The finite-calendar exclusion remains exact-only.

## Periodic equilibrium and uniformity

Exact table enumeration verifies the three rotating continuation vectors.
At each turn the mover is indifferent at zero, the negative-passive observer
has joining offer `-15/2<0`, and the positive-passive observer has joining
offer `15<16`. Player0 has joining offer zero below continuation one.

After deleting any one prescribed clock, at least two core hazard-one-half
opportunities remain every three dates. The opponent survival bound `4^-n`
is therefore uniform over every complete unilateral replacement, including
Never. Iterating the root inequalities proves the complete native caps;
proper opponents justify the original shift, giving `(2,1,17,1)` exactly.
The same geometric bound controls expected absorption time uniformly over
deviations. Finite-horizon average payoffs converge uniformly to terminal
payoffs, so the fixed profile and fixed target establish the stated UE.

Reproduction used exact table reconstruction, polynomial identities and
periodic-cap checks independently of the supplied interval implementation,
plus execution of that implementation. `python scripts/check_docs.py` passed.
No mathematical objection remains. The resulting limitation concerns a
proposed raw-data case split; the displayed game itself is solved positively.
