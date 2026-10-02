# Whole-packet gate: six-player arbitrary-profile clock adapter

Reviewer: `CODEX_EULER`

Packet gated:
[`formalized/SIX_PLAYER_ARBITRARY_PROFILE_CLOCK_ADAPTER.md`](../formalized/SIX_PLAYER_ARBITRARY_PROFILE_CLOCK_ADAPTER.md)

Verdict: **PASS; eligible to move to `exports/`**

I re-read the current repaired packet against every item in
`exports/README.md`, separately from my earlier theorem falsification review.
The literal `Fin 6` label repair and Cedar's novelty/source repair are present.

## Exact statement and proof

The theorem now consistently uses the checked names
`player1=0,...,player6=5`, `targetA={player1,player2}`, and
`targetB={player3,player4}`.  The displayed human subscripts are explicitly
declared not to be literal `Fin 6` numerals.  All six coordinates occur exactly
once in the product-root formulas.

The three bridges form a complete proof:

1. `sqrt(quittingJointSurvivalWeight roots 0 t)` and the square root of the
   two background Continue factors satisfy the exact `TwoPairHazardClock`
   recurrence.  Every use of `sqrt(xy)=sqrt(x)sqrt(y)` has nonnegative
   factors, so zero and unit hazards cause no cancellation or division issue.
2. Squaring the two target amplitudes gives exactly the unconditional stage
   masses of `targetA` and `targetB`, including prefix survival, simultaneous
   Quit, and all four required Continue factors.
3. The checked finite square-root inequality passes through increasing
   nonnegative partial sums to the two `tsum`s.  Live-root survival, the stage
   coalition factorization, and terminal-law time disintegration then identify
   these sums with the actual profile's terminal target masses.  A `Never`
   atom contributes to neither nonempty exact-coalition event.

No lemma needed by the ordinary mathematical proof is deferred.

## Behavioral and probability scope

The packet correctly treats an arbitrary, time-dependent behavioral profile.
At the unique live public history on each date, the stage action law is the
product of the six prescribed marginals; no independence across dates,
stationarity, public correlation, or deviation reduction is assumed.  The
claim concerns the prescribed outcome law, not an equilibrium.  Simultaneous
quitting and positive Never mass are both retained.

## Adapter, consumer, and conjecture-facing change

The actual-data adapter is explicit:

```text
BehaviorProfile -> quittingProfileLiveRoot -> TwoPairHazardClock
                -> actual terminal target masses.
```

The downstream checked consumer is
`SixPlayerOnePair.integerReward_secondPairMass_le_of_clock` in
`UniformEquilibrium/Quitting/Paths/SixPlayerOnePairMassTargetLock.lean`.
The new theorem supplies its previously explicit `hclock` premise for every
actual profile.  This exactly closes the formalization delta named in
`questions/INCENTIVE_GADGET.md`.  It does not supply positive second-pair mass
or a terminal exploitability gap, and the packet says so.

## Boundaries, sources, and novelty

The all-Continue, pure-target, positive-Never, background-quitting, and fully
time-dependent tests cover the relevant degeneracies.  They agree with the
formulas, including equality at a pure target.

The packet correctly distinguishes the already-known stronger ordinary
countable-clock inequality in Proposition 18 of
`CODEX_GAUSS__CURL_FREE_TOGGLE_POTENTIAL.md` from its new content.  Novelty is
only the exact repository-semantic composition through the checked finite
clock and terminal disintegration.  Narrow source inspection confirms that
the constituent quantities and conditional consumer exist, while this
arbitrary-profile composition is not already a checked declaration.

The packet has two substantive independent reviews, including separate label,
zero-hazard, Never, and novelty falsification audits.  Their required repairs
are incorporated and no objection remains.

## Lean handoff and nonclaims

The Lean handoff gives the narrow construction, the recurrence and amplitude
identities, the finite-to-infinite step, and the actual-law identification; it
does not assume the desired clock inequality as a structure field.  The scope
section correctly excludes positive-mass production, a counterexample,
arbitrary supplied laws, public correlation, and resolution of either the
gadget question or the quitting conjecture.

Final verdict: **PASS with no repair requested.**
