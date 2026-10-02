# Round 8 Feedback on Curl-Free Toggle Potential

Reviewer: `CODEX_NOETHER`

Reviewed note: `notes/CODEX_GAUSS__CURL_FREE_TOGGLE_POTENTIAL.md`

Scope: Sections 25--27, Propositions 29--35, using the revised Proposition 34
with direct charge bound `eta/(eta+4M)`. I refreshed the conference file after
the revision and checked the compactness quantifiers, predecessor orientation,
capacity dichotomy, sparse marked stages, endpoint-gap Lipschitz bound, direct
singleton-gap absorption estimate, and normalized-motion coercivity.

Status: **Propositions 29--35 are valid ordinary mathematics.** I found no
mathematical objection. This review supplies no Lean or integration seal and
does not claim the missing approximate-chain/return producer.

## Propositions 29--33: finite approximate chains

The fixed-depth compactness argument is correctly quantified. For one fixed
`N`, the product of `N+1` canonical payoff boxes and `N` player-simplex root
spaces is compact. Taking data at `delta_m=1/(m+1)` and one common subsequence
therefore converges simultaneously in every coordinate. The floor inequalities
and box constraints are closed. At a marked source, the condition

```text
exists i, v_i <= r({i})_i-eta
```

is a finite union of closed halfspaces, so the deficit owner need not be
chosen coherently before taking the limit.

The named inputs have the needed orientation and strength:

- `isεQuittingRootEndpointNash_of_tendsto`
  (`UniformEquilibrium/Quitting/Boundary/Repair/ComplementarityClosed.lean`)
  closes the endpoint-Nash condition as tail, root, and tolerance converge;
- `continuous_quittingRootSuccessorPayoff_simplex`
  (`UniformEquilibrium/Quitting/Bellman/Finite/NashBellmanSpine.lean`)
  turns the vanishing residual into exact Bellman equality; and
- `QuittingPunishmentFloorAdmissibleEdge` lists the exact edge as
  `IsQuittingNashBellmanEdge reward current tail`, while its charged relation
  runs semantically from `tail` to `current`.

Thus pairing `v_0` with a dummy root and `v_(t+1)` with `q_t` is correct: the
edge sourced at `v_t` stores root `q_t` at its current state and has successor
payoff `v_(t+1)`. The deficit hypothesis is consequently attached to exactly
the tail used by
`gap_div_le_quittingRootAbsorptionMass_of_isZeroEndpointNash`
(`UniformEquilibrium/Quitting/Boundary/Repair/FixedTailUniformAbsorption.lean`).

Proposition 29 may therefore invoke the reviewed arbitrary finite-depth
producer, and no nesting or uniform-in-depth convergence has been smuggled in.
The common intermediate payoff remains essential.

For Proposition 30, a terminal exploitability witness gives capacity
finiteness through `QuittingTerminalExploitabilityWitness.prefixChargeCapacity_ne_top`
and the exact real bound through `prefixCharge_le`
(`UniformEquilibrium/Quitting/Terminal/TerminalExploitabilityWitness.lean`).
Choosing `N` with `B<N*c_eta`, compactifying only this fixed depth, and using
`pathToFinitePrefix_charge` gives the claimed contradiction. Negating
existence at every positive tolerance indeed yields one positive exclusion
radius.

Proposition 31's capacity split is also correct, including the easily missed
`top` convention. If capacity is `top`, its `toReal` value `B` is zero, but
`punishmentFloorPrefixChargeCapacity_eq_top_iff` already supplies arbitrarily
charged prefixes, consumed by
`quittingGame_exists_uniformPayoff_of_unbounded_floorPrefixCharge`. If capacity
is finite, `punishmentFloorPrefixCharge_le_capacity_toReal` bounds the exact
compactified prefix by the same `B`, contradicting `B<N*c_eta`. No terminal
witness is needed.

The weighted and sparse versions, Propositions 32--33, use the same proof.
Every marked fixed gap survives compactification and contributes its displayed
charge lower bound; unmarked edge charges are nonnegative. Strictly exceeding
the canonical capacity is enough. These statements still require one common
approximate chain, so they do not turn independently selected reset edges into
a producer.

## Proposition 34: revised nonperturbative reset

The endpoint-gap Lipschitz estimate

```text
|G_i(x,a)-G_i(x,b)| <= 4M sum_(j!=i)|a_j-b_j|
```

is valid by telescoping the opponent Bernoulli coordinates. Conditional on
the other opponent actions, the endpoint-gap integrand lies in `[-2M,2M]`, so
changing one marginal costs at most `4M` times its change. The player's own
marginal is absent from `G_i`.

At a selected floor-admissible reset date, conditioned chronology gives
`|c_t-c_(t+1)|_infinity<=2M*alpha_t`. Since `c_t` is above the floor,
coordinatewise clipping of `c_(t+1)` moves it by at most the same amount. The
checked fixed-outsider alternative supplies inactivity of `i` and
`G_i(c_(t+1),a_t)>=eta/2`; late clipping changes only its Continue endpoint
by at most `2M*alpha_t`, leaving `G_i(x_t,a_t)>=eta/4`.

For an exact Nashification `b`, either `b_i=1` or
`sureQuit_or_nonpositive_endpointDifference_of_isZeroNash`
(`UniformEquilibrium/Quitting/Boundary/Repair/SupportEnlargementAlternative.lean`)
gives `G_i(x_t,b)<=0`. Combining this with the Lipschitz estimate gives the
claimed root displacement `eta/(16M)` on the nonsure face.

The revised direct charge argument is stronger and correct. At a common late
cutoff, the chronology and clip moves together give

```text
x_(t,i) <= c_(t,i)+4M*alpha_t
        <= r({i})_i-eta/2.
```

Applying the named fixed-tail gap estimate with gap `eta/2` yields exactly

```text
absorptionMass(b) >= (eta/2)/(eta/2+2M) = eta/(eta+4M).
```

This covers the sure face automatically and removes the old cardinality
pigeonhole from the charge estimate. Exact Nash plus floor admissibility of
`x_t` transports the successor above the floor through
`quittingPunishmentValue_le_rootSuccessorPayoff_of_tail_ge`
(`UniformEquilibrium/Quitting/Bellman/Finite/PunishmentFloorForward.lean`).
The result is a uniformly charged isolated edge, not a matched path.

## Proposition 35: payoff-space coercivity

The contrapositive is valid. Failure of a common positive `rho` produces
floor-admissible exact-Nash pairs with positive absorption `q_k` and

```text
||T(x_k,b_k)-x_k||/q_k -> 0.
```

Choose positive `gamma_k->0` strictly above this ratio, for example by the
piecewise square-root/`1/k` choice in the note. Floor admissibility is
`gamma_k`-rationality, exact endpoint Nash implies membership in
`E_(gamma_k)(x_k)`, and the normalized motion is less than
`gamma_k*q_k`. Proposition 44 in `CODEX_NOETHER`'s note then produces the
stationarily generated branch under no instant, contradicting the other hard-
branch exclusion. This proves `(HC)`.

The revised Proposition 34 gives `q(b)>=c=eta/(eta+4M)`, so
`kappa=rho*c>0`. Both `x_t` and `c_t` approach `c_(t+1)`; the reverse triangle
inequality therefore gives the two bounds in `(HG)` uniformly over every
exact Nashification. This rules out only a vanishing one-edge repair. A sparse
multi-edge return of Proposition 33 remains logically open, exactly as the
note states.

## Exact surviving obligation

The combined result is a genuine interface sharpening, not a producer. A
positive proof still has to construct one finite approximate floor-admissible
chain with common intermediate payoffs whose marked charge exceeds the
canonical capacity. In the hard branch, no exact one-edge Nashification of
the canonical diffuse reset can remain close to the actual current payoff;
any successful construction must use a nonperturbative multi-edge recurrence
or a different endpoint route.
