# Delta whole-packet gate: interval-passive odd core

Reviewer: `CODEX_EULER`

Verdict: **PASS**.  The packet amendment contains exactly the twice-reviewed
odd interval-passive theorem and satisfies every applicable
`exports/README.md` criterion.  I found no required repair.  The later
unreviewed even-cycle parity corollary is explicitly excluded and does not
appear in the statement or proof.

## Statement and finite source predicate

The amended source is literal finite reward-table data.  For an odd cyclic
core `K` of cardinality at least three, it computes continuation extrema
`C_i^-,C_i^+`, blocker-absent Quit minimum `H_i^-`, and blocker-present Quit
maximum `L_i^+`, and assumes precisely

```text
L_i^+ < C_i^- <= C_i^+ < H_i^-.
```

No equilibrium, continuation value, or calibrator payoff condition is hidden
in this predicate.  Every calibrator reward coordinate remains arbitrary.
The old passive theorem is correctly identified as the special case
`C_i^-=C_i^+=z_i`.

## Producer and odd-limit proof

On `[epsilon,1]^K x [0,1]^(I\K)`, every player has a positive-rate core
opponent, so all deleted absorption denominators are positive and the
stationary payoff is continuous.  With fixed opponents it is fractional
linear in the own rate, with derivative of constant sign `Q_i-N_i`; its
argmax is an endpoint or the entire interval.  The resulting product
best-response correspondence has nonempty compact convex values and closed
graph, so constrained Kakutani applies.

For a core continuer, `N_i` is a convex combination of literal nonempty rows
omitting `i`, hence `C_i^- <= N_i <= C_i^+`.  If the blocker rate tends to
zero, conditioning the forced-Quit endpoint on the blocker action gives
`liminf Q_i >= H_i^-`; the bounded blocker-present part has vanishing weight.
If the blocker rate tends to one, it gives `limsup Q_i <= L_i^+`.  The strict
band separation therefore supplies the two eventual endpoint signs uniformly
while calibrator rates vary arbitrarily.

A limiting core zero forces its predecessor to rate one and the next
predecessor to the lower constrained rate, hence back to zero.  Backward
alternation cannot close around an odd cycle.  A limiting one forces a
predecessor zero and is likewise excluded.  Thus every limiting core rate is
strictly interior.  For all sufficiently late constrained equilibria it is
also interior relative to `[epsilon_m,1]`, so exact optimality yields
`Q_i=N_i`; the arbitrary calibrator best-response inequalities pass to the
limit because the interior core uniformly bounds every relevant denominator
away from zero.

At the limit, a core player's Continue endpoint is
`delta_i N_i+beta_i N_i=N_i`, equal to its Quit endpoint.  The calibrator
endpoint inequalities follow from its unrestricted stationary best response.
This gives the exact fixed-point endpoint certificate.  Every player has a
positive-rate core opponent, so joint and all player-deleted Continue products
contract.  The named endpoint compilers therefore upgrade the certificate to
exact terminal Nash against every unilateral behavioral strategy and to a
uniform-equilibrium payoff.  Nothing in this handoff restricts calibrator
deviations.

## Tests, sources, and scope

The strict rational extension test is exact: with one surely quitting
calibrator and all three core rates `1/3`, the continuation endpoint is `1`
and the Quit endpoint is `2*(2/3)-1*(1/3)=1`, while
`(C_i^-,C_i^+,H_i^-,L_i^+)=(0,1,2,-1)`.  Hence no constant passive baseline
exists.  The likelihood-ratio regression also computes exactly
`Q_i=1+8 epsilon` and `N_i=10/(1+epsilon-epsilon^2)`, demonstrating that
same-background toggle signs alone do not imply the required face
orientation.  The even two-cycle example correctly marks the parity boundary
without asserting nonexistence there.

The source audit distinguishes the new partial-core band theorem from the
checked all-player blocker/face results, the positive-cycle signed-influence
theorem, and `Literature.SolanAndVieille2001.theorem1_2`.  The actual-data
adapter, named endpoint consumers, proof outline, regression list, and Lean
handoff are all explicit.  Two independent falsification reviews of the
interval amendment are linked.

The nonclaims match the mathematics: the theorem does not cover weak or
overlapping bands, arbitrary negative cycles, or even cores; it does not
produce the requested pair-mass gadget or settle general quitting-game
existence.  The amendment is therefore export-ready at exactly its stated odd
interval-passive, arbitrary-calibrator, unrestricted-behavior scope.
