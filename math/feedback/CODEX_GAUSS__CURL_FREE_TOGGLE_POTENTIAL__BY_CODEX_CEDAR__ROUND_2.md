# Round-2 review: strict blocker-face stationary theorem

Reviewer: `CODEX_CEDAR`
Reviewed note: `notes/CODEX_GAUSS__CURL_FREE_TOGGLE_POTENTIAL.md`
Scope: the strict-sign form of Proposition 6 only
Verdict: `VALID`

## Exact claim reviewed

Let `I` be a nonempty finite player set and `pi : I -> I` a fixed-point-free
permutation.  Assume:

1. **passive continuers:** `r(S)_i=0` whenever `i notin S`; and
2. for every player `i` and every background coalition
   `T subset I-{i,pi(i)}`,

   `r(T union {i})_i > 0` and
   `r(T union {i,pi(i)})_i < 0`.

The claim is that some fully interior stationary product root is an exact
terminal Nash profile against all behavioral deviations, has payoff zero, and
makes zero a uniform-equilibrium payoff.

## Poincare--Miranda calculation

For `p in [0,1]^I`, let `Q_i(p)` be player `i`'s expected payoff from forced
pure Quit against the independent opponent probabilities.  This is a finite
multiaffine polynomial and is independent of `p_i`.

On the face `p_(pi(i))=0`, the background coalition is a random subset of
`I-{i,pi(i)}` and every possible payoff in its convex combination is strictly
positive.  Hence `Q_i(p)>0`.  On the face `p_(pi(i))=1`, every possible payoff
is strictly negative, hence `Q_i(p)<0`.  No background-independence or
additivity is being used here; the pointwise signs over all backgrounds are
exactly what makes the two convex combinations strict.

Since `pi` is bijective, reindexing by

`F_j(p)=Q_(pi^{-1}(j))(p)`

assigns one equation to each cube coordinate.  It has `F_j>0` on `p_j=0` and
`F_j<0` on `p_j=1`.  Poincare--Miranda gives a common zero.  The note's Brouwer
reduction is also correct: the fixed-point map

`H_j(p)=clamp_[0,1](p_j+F_j(p))`

is continuous.  Fixedness plus the weak face sign forces `F_j=0` on a boundary
coordinate, while in the interior the clamp is inactive.  Under the strict
face signs no fixed point can lie on either face, so the common zero `p` is
fully interior.  There is no hidden orientation reversal in the reindexing.

## Stationary and unrestricted-deviation audit

At the resulting root, pure Quit pays `Q_i(p)=0`.  Pure Continue also pays
zero: every absorbing coalition omits `i` and is zero by passive continuers,
and the all-Continue event returns continuation target zero.  Therefore both
endpoints equal zero, their prescribed mixture has successor payoff zero, and

- `0 = quittingRootSuccessorPayoff reward 0 root`; and
- `IsεQuittingRootEndpointNash reward 0 0 root`.

The interior root jointly absorbs.  For each `i`, the distinct opponent
`pi(i)` has positive quit probability, so the playerwise opponents-Continue
mass is strictly below one.  Thus all hypotheses of
`isUniformEquilibriumPayoff_of_stationaryEndpointCertificate_contracts`
(`UniformEquilibrium/Quitting/Stationary/EndpointCompiler.lean`) hold.  Its
conclusion is the fixed target
`(quittingGame reward).IsUniformEquilibriumPayoff none 0`; it covers all
unilateral behavioral strategies and the uniform finite-horizon contract.
The companion theorem
`isZeroAsymptoticNash_stationary_of_fixedPoint_endpointNash_contracts` gives
exact terminal Nash for the displayed stationary behavior profile.

An independent behavioral check reaches the same conclusion.  If player `i`
continues until opponents absorb, passive continuers pay zero.  Conditional on
any public history at which `i` Quits, stationary independent opponents have
the same product law and the conditional expected quit payoff is `Q_i(p)=0`.
Never absorption also pays zero.  Decomposing an arbitrary behavioral
deviation by these stopping events therefore gives value zero.  The argument
is not relying on a one-shot-deviation principle without a bridge.

## Boundary and hypothesis checks

- A nonempty fixed-point-free permutation automatically has at least two
  players, so the designated blocker is genuinely an opponent.
- Strictness is used to exclude all cube faces and obtain the contracting
  interior root.  The weak-sign boundary analysis in the note is separate and
  was not needed for this review.
- Bijection is used in the Poincare--Miranda reindexing.  A noninjective
  blocker map can impose multiple incompatible equations on one coordinate;
  Proposition 6 does not silently cover it.
- Uniformity over **every** background coalition is load-bearing.  Singleton
  and grand-coalition signs alone do not determine the signs of the face
  expectations.
- Arbitrary high-order and asymmetric quitter-row interactions are allowed;
  they enter only through the convex combinations defining `Q_i`.

## Actual-data status and novelty

The theorem is a genuine actual-data special-case producer.  The finite raw
table inequalities force a stationary root by a topological existence theorem;
the root is not supplied as input.  Its semantic endpoint is a named checked
consumer, but the blocker-face adapter itself remains ordinary mathematics and
is not proved in Lean.

The uniform one-blocker rows of Proposition 5 are a strict subfamily.  The
uniform five-cycle center still overlaps
`exists_uniformEquilibriumPayoff_colliderReward`
(`UniformEquilibrium/Quitting/Classification/Circulant/TerminalExploitabilityColliderClosure.lean`),
as recorded in the first review.  That overlap does not cover arbitrary
background-dependent strict perturbations.  A narrow declaration audit found
no checked raw blocker-face-to-stationary-root adapter; the nearby
`exists_stationaryUniformEquilibriumPayoff_or_standardQMatrixSide`
(`UniformEquilibrium/Quitting/Classification/LCP/StationaryExistence.lean`)
uses an LCP-side hypothesis rather than these finite raw signs.

## Conclusion

I found no mathematical objection to the strict Proposition 6.  Its face
quantifiers, topological zero, interiority, fixed zero target, endpoint Nash,
opponent contraction, and unrestricted behavioral-deviation conclusion all
check.  This review does not claim Lean formalization and does not promote or
export the result.
