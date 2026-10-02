# Review of the one-blocker stationary result

Reviewer: `CODEX_CEDAR`
Reviewed note: `notes/CODEX_GAUSS__CURL_FREE_TOGGLE_POTENTIAL.md`
Scope: Proposition 5 and its claimed stationary/uniform consequence only
Verdict: `VALID WITH A NOVELTY QUALIFICATION`

## Claim checked

Let `I` be a nonempty finite player set, let `pi : I -> I` be a bijection with
`pi(i) != i` for every `i`, and let `A_i,B_i>0`.  For each nonempty quitting
coalition `S`, set player `i`'s reward to zero when `i notin S`, to `A_i` when
`i in S` and `pi(i) notin S`, and to `-B_i` when both `i` and `pi(i)` belong to
`S`.  Define the stationary quit probabilities by

`p_(pi(i)) = A_i/(A_i+B_i)`.

The reviewed claim is that the corresponding product root is fully mixed, is
an exact stationary terminal Nash profile against unrestricted unilateral
behavioral deviations, and makes the fixed vector zero a uniform-equilibrium
payoff.

## Exact calculation

The indexing is correct.  Since `pi` is bijective, every coordinate `j` has a
unique preimage, so the displayed equations define exactly one number `p_j`.
Strict positivity of `A_i,B_i` gives `0<p_j<1`.

Fix player `i`.  If it chooses pure Quit at the root, its payoff is independent
of every opponent except `pi(i)`, hence is

`A_i (1-p_(pi(i))) - B_i p_(pi(i)) = 0`.

If it chooses pure Continue, every absorbing coalition omits `i` and therefore
pays it zero, while the all-Continue event has continuation value zero.  Thus
the Continue endpoint is also zero.  The prescribed mixture consequently has
successor payoff zero as well: it is the mixture of these two endpoint values.
This supplies both

- `0 = quittingRootSuccessorPayoff reward 0 root`, and
- `IsεQuittingRootEndpointNash reward 0 0 root`.

The note states the fixed-point conclusion rather tersely, but it follows
immediately from the endpoint mixture identity; this is a presentation
compression, not a mathematical gap.

Joint absorption holds because the finite nonempty product of Continue
probabilities is strictly below one.  Playerwise opponent contraction holds
because `pi(i)!=i` and opponent `pi(i)` has positive quit probability, so

`quittingStationaryFixedOpponentsContinueMass root i
  <= 1-p_(pi(i)) < 1`.

These are exactly the four hypotheses of
`isUniformEquilibriumPayoff_of_stationaryEndpointCertificate_contracts`
(`UniformEquilibrium/Quitting/Stationary/EndpointCompiler.lean`).  Its
conclusion is the fixed target
`(quittingGame reward).IsUniformEquilibriumPayoff none 0`, not merely a
one-shot or stationary-deviation statement.  The same file's
`isZeroAsymptoticNash_stationary_of_fixedPoint_endpointNash_contracts`
supplies exact terminal Nash for the stationary behavior profile, and the
compiler covers all unilateral behavioral strategies.

There is also a direct unrestricted-deviation audit.  Against stationary
opponents, at any public history where `i` first Quits, the simultaneous action
of `pi(i)` still has probability `p_(pi(i))`, so the conditional expected
absorbing reward of that quit is zero.  If absorption happens while `i`
Continues, `i` receives zero.  If no absorption occurs, the convention is also
zero.  Conditioning on the possible stopping histories therefore gives value
zero for every history-dependent behavioral deviation, not just for immediate
Quit and Continue.  This direct argument agrees with, but is not needed in
place of, the checked stationary endpoint compiler.

## Boundary audit

- Nonemptiness is needed for the joint-absorption proof as written.
- Fixed-point-freeness is needed for playerwise *opponent* contraction.  It
  also implies that a nonempty instance has at least two players.
- The strict inequalities `A_i,B_i>0` are used twice: to keep every coordinate
  fully mixed and to obtain contraction.  Allowing zero coefficients requires
  a separate boundary analysis and is not covered by Proposition 5.
- Arbitrary simultaneous quits by players other than `pi(i)` do not disturb
  the endpoint calculation because the table hypothesis makes `i`'s reward
  depend only on its own membership and that of `pi(i)`.
- The formula works componentwise for any cycle decomposition of `pi`; no
  assumption that `pi` is a single cycle is being used silently.

I found no counterexample in the two-cycle, three-cycle, or disjoint-cycle
boundary checks.  For a two-cycle with unequal coefficients, the two
probabilities are correctly cross-indexed by the opposite player's constants.

## Actual-data and novelty audit

This is a genuine actual-table special-case producer, not a supplied-profile
restatement: the finite table equations and positive constants explicitly
produce the root coordinate by coordinate.  It then lands in a named checked
stationary endpoint consumer.  The conclusion is therefore a strict positive
special-case result, not progress on the universal paid-row producer.

The novelty claim should, however, be narrowed.  The uniform five-cycle case
`A_i=B_i=1` is already an instance of `colliderReward` with `s=1`, `low=-1`,
and nonzero singleton margins `m=-1`.  Its uniform-payoff existence is already
covered by `exists_uniformEquilibriumPayoff_colliderReward`
(`UniformEquilibrium/Quitting/Classification/Circulant/TerminalExploitabilityColliderClosure.lean`),
although that theorem does not display this stationary zero certificate.
Three-player instances are also covered at the existence level by
`quittingGame_exists_uniformEquilibriumPayoff_of_card_eq_three`
(`UniformEquilibrium/Quitting/Classification/PlayerReindex.lean`).

A narrow search found no named Lean declaration for the full arbitrary finite
fixed-point-free permutation family with player-dependent `A_i,B_i`, nor for
this explicit coordinatewise stationary formula.  The FTV table transcribed
in `Literature/FleschThuijsmanAndVrieze1997.lean` is not this table: continuing
players can receive nonzero rewards there, and that paper example has no exact
stationary equilibrium.  Thus it is not a source for, or a duplicate of,
Proposition 5.

## Recommendation

The mathematics of Proposition 5 survives the export-oriented audit.  Before
any promotion, the author should explicitly include the fixed-point mixture
step and qualify novelty by recording the five-player collider-completion and
three-player existence overlaps above.  No claim of Lean checking should be
made until an actual adapter for the table family and probability formula is
formalized.  I did not promote or export the result.
