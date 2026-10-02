# Independent review: finite punishment-floor burn-in

Reviewer: CODEX_HILBERT.

Complete reviewed author note:
`notes/CODEX_RENY__FINITE_FORWARD_PUNISHMENT_FLOOR_BURN_IN.md`,
SHA-256 `8b88941767cc9278725140d1e02e3dc14771e95ac75b942b65efd2178876066f`.

Verdict: **PASS, ordinary mathematics.** No mathematical repair required.
This checks the finite, approximate, free-start adapter independently; its
infinite-spine antecedent is my earlier deficit argument. No source or
export edits and no Lean build were made.

## 1. Finite claim checked

There are finitely many nonempty players, independent root choices, rewards
bounded in absolute value by M>0, Never payoff zero, and semantic punishment
values P_i≤s_i. Fix B≥M and τ>0. Suppose a finite word with annotations in
[−B,B]^I obeys, for every row and coordinate,

    Q_i(q_t) ≤ v_(t+1)(i)+ζ,
    C_i(q_t,v_t) ≤ v_(t+1)(i)+ζ,

where 0≤ζ≤min(τ/2,τ²/(8M)). For κ=τ²/(8M) and any integer L≥1
with Lκ>M+B, every endpoint of index at least L satisfies v_j≥P−τ.
This is valid without any initial floor, positive singleton, actual suffix
payoff realization, or absorption lower bound.

The simultaneous endpoints are essential. A bound on the supported action
alone, without the approximate-Nash comparison to the other action, would
not give this theorem.

## 2. Full deficit calculation

Fix a violating coordinate with d_j=P_i−v_j(i)>τ. For row j−1 let α
be that player's opponents' all-Continue mass. On that event its Quit
reward is s_i; the remaining outcomes give the exact estimate

    Q_i ≥ s_i−2M(1−α) ≥ P_i−2M(1−α).

Combining with the displayed Quit upper bound gives

    1−α ≥ (d_j−ζ)/(2M) > τ/(4M).

In particular α<1 and Q_i<P_i. Against the opponents repeating this
same row, the complete behavioral cap is max(Q_i,L_i/(1−α)), where L_i
is their absorbing Continue contribution. This cap is at least P_i by
the definition of punishment. Therefore L_i≥(1−α)P_i. The displayed
Continue upper bound now implies

    α d_(j−1) ≥ d_j−ζ > 0.

This separately rules out α=0 before dividing. As 0<α≤1,

    d_(j−1)−d_j
      ≥ ((1−α)d_j−ζ)/α
      > τ²/(4M)−ζ
      ≥ τ²/(8M)=κ.

The numerator is positive, which justifies dropping division by α in the
middle comparison. The same coordinate remains a strict violator and the
argument iterates toward index zero. Thus d_0>d_j+jκ>jκ, whereas
d_0≤P_i+B≤M+B. This proves the stated L and all endpoint quantifiers.

For one player α=1 identically; the first strict inequality is already a
contradiction. Thus the finite-player statement includes the one-player
boundary correctly. Neither α=0 nor α=1 is hidden inside an invalid
division. Signed rewards and possibly negative punishment values cause no
sign change in the argument.

## 3. Error sums, retained semantics, and charge

If Bellman error is at most b_t and ordinary root regret at most n_t, each
pure endpoint is at most F_i+n_t≤v_(t+1)(i)+b_t+n_t. Therefore ζ bounds
the **sum** of the two errors. There is no horizon-sized accumulated error.

For exact Bellman/support-e input, ordinary root regret is at most e.
Choosing e≤min(δ,δ/2,δ²/(8M)) and τ=δ supplies the burn-in lemma.
For weighted input, the two errors are each at most e a_t, so the pure
endpoint discrepancy is at most 2e a_t≤2e. Choosing
e≤min(δ,δ/4,δ²/(16M)) supplies the same lemma with ζ=2e. These are the
author's constants and orientations.

Choose L from the target accuracy and the fixed bounds before requesting
a word of charge Q+L. Since every a_t≤1, its horizon H is at least L.
Retain annotations v_L,…,v_H and roots q_L,…,q_(H−1). The removed
charge is at most L; the retained charge is at least Q. The retained
initial endpoint v_L and final endpoint v_H both satisfy the desired
floor. All retained edges are literal old edges with the same annotations,
roots, and error bounds, and the box is unchanged. If Q=0 and H=L the
remaining length-zero word still has its required endpoint floor.

The first L construction rows are the last chronological block when the
word is read as a play prescription. The proof does not delete an earliest
chronological prefix and then attach its roots to a different tail.

It follows that the floor-free exact-support producer and the floor-bearing
one are equivalent in the same fixed box. The corresponding weighted
producers are also equivalent in that same box. The converse implications
simply forget floors. These are all-accuracy/all-requested-charge
equivalences, not a claim that every original word already has its floors.
The box cannot depend on the requested charge or accuracy.

## 4. Falsification boundaries

The zero-reward, two-sure-quitter example is valid: from a negative initial
annotation, every pure root endpoint is zero and the next value is zero.
It defeats a floor assertion at index zero while satisfying exact root
Nash and Bellman transport.

For the stated two-player negative-membership table, P_i=0 exactly: Never
guarantees a nonnegative payoff against any opponent law, and all-Never
opponents give cap zero. The own singleton is −1, so normality fails. At
q=0 and v=(−1/2,−1/2), Quit pays −1, Continue and the displayed value
are −1/2. This is an arbitrarily repeatable exact Nash--Bellman row with
zero charge violating the τ=1/4 floor. It disproves the finite floor
lemma without normality, but does **not** disprove a producer equivalence
whose premise demands unbounded charge. The author maintains this scope.

## 5. Source overlap and actual input reduction

The inspected production definitions and declarations are:

- `quittingBestReplyValue`, `quittingPunishmentValue`,
  `quittingBestReplyValue_stationary`,
  `quittingStationaryUnilateralCap_eq_max_div`, and
  `quittingPunishmentValue_le_stationaryUnilateralCap` in
  `UniformEquilibrium/Quitting/Stationary/MinMax.lean`. The comparison used
  above controls all complete behavioral responses, not a finite menu.
- `quittingPunishmentValue_sub_le_continueMass_mul_of_nashBellmanEdge` in
  `Quitting/Debt/Dynamic/PunishmentFloorViolation.lean`: the existing exact
  one-edge deficit propagation. The present result adds approximate
  endpoint error, a uniform finite burn-in, and all-word input removal.
- `QuittingPunishmentFloorFinitePrefix` and
  `quittingPunishmentValue_le_finitePrefixValue` in
  `Quitting/Bellman/Finite/PunishmentFloorFinitePrefix.lean`: the old exact
  forward floor propagation explicitly assumes an anchor floor.
- `QuittingAbsorptionWeightedForwardPacket`,
  `HasExactFiniteForwardPackets`,
  `HasAbsorptionWeightedFiniteForwardPackets`, and
  `exists_exactFiniteForwardPacketBox_iff_exists_absorptionWeightedBox` in
  the current `Quitting/Projective/AbsorptionWeightedForwardPacket*` files:
  the floor-bearing endpoints, fixed-box producer quantifiers, and checked
  repair/consumer agree with the retained data.

The narrow lookup found no existing free-start approximate finite burn-in
declaration. The argument is a genuine removal of the every-endpoint floor
input under normality, not merely a renamed supplied-floor verifier. It
still does not construct words with unbounded charge; that global producer
obligation remains. No positive-gap table or new equilibrium existence
claim follows without such a producer.
