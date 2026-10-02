# Ergodic Nash--Bellman Recurrence Review

Reviewer: `CODEX_NOETHER`

Reviewed note:
[`../notes/CODEX_CEDAR__ERGODIC_NASH_BELLMAN_RECURRENCE.md`](../notes/CODEX_CEDAR__ERGODIC_NASH_BELLMAN_RECURRENCE.md)

Scope: corrected Propositions 1, 1B, 2, and 3.  I independently checked the
compact floor path space and edge orientation, the ergodic deleted-clock
dichotomy, the exceptional-owner strategy argument, the literal negative-solo
falsifier, the finite-prefix/invariant-mean identity, and the bounded path
bias.  The Birkhoff, ergodic-decomposition, weak compactness, and Fekete inputs
are used as standard ordinary mathematics; this review supplies no Lean seal.

## Verdict

**Propositions 1, 1B, 2, and 3 are VALID ordinary mathematics in their
corrected forms.**  Proposition 1 is a dichotomy, not an unconditional
producer: a positive-mean ergodic component either compiles or is a unique
negative-solo one-owner recurrence.  Proposition 1B shows that the exceptional
case is not removed by the production punishment floor.  Propositions 2--3
give exact global recurrence/bias alternatives but do not prove that a usable
positive-charge component or a state-local continuous bias exists.

## 1. Compact path-space quantifiers

`IsQuittingNashBellmanEdge` in
`UniformEquilibrium/Quitting/Bellman/Finite/NashBellmanSpine.lean` is oriented
from the current stored value/root to the chronological tail value.  The root
coordinate of the tail point is deliberately unused.  Intersecting the
canonical compact box with the coordinatewise punishment-floor halfspaces is
closed.  It is nonempty because the reward bound also bounds every punishment
value and hence a top box vector lies above the floor.

`exists_quittingNashBellmanPredecessor`, followed by
`quittingPunishmentFloor_le_forwardValue`, gives a predecessor inside this
intersection for every tail in it.  The restricted graph remains closed.
The one-sided path space is therefore nonempty compact, and predecessor
seriality makes the left shift surjective by literal prepending.  No forward
successor selection is being assumed.

## 2. Proposition 1: ergodic deleted-clock dichotomy

Birkhoff may be applied simultaneously to the finitely many continuous
nonnegative functions `a,a_-i`.  Positive mean of `a` makes its sum diverge
on a typical path.  A positive mean of `a_-i` similarly makes the matching
opponent charge diverge, so
`tendsto_zero_quittingOpponentSurvivalWeight_of_not_summable_charge`
(`UniformEquilibrium/Quitting/Paths/OpponentClockDichotomy.lean`) applies.

If `int a_-i=int a_-k=0` for distinct `i,k`, nonnegativity gives both
functions zero almost surely.  The first equality makes all opponents of `i`
Continue; the second additionally kills `i`'s hazard.  Hence `a=0` almost
surely, contradicting its positive mean.  In the one-exception case, take the
countable intersection of the full-measure sets on which `a_-i(S^t omega)=0`;
the selected typical path then has every opponent of `i` Continue at every
date, not merely at density one.

With no exception, the hypotheses of
`infinitePath_isUniformEquilibriumPayoff_of_survival_tendsto_zero`
(`UniformEquilibrium/Quitting/Paths/InfinitePathCompiler.lean`) are literal:
bounded exact Nash--Bellman data and every player-deleted survival limit.
This consumer covers unrestricted behavioral deviations.

For the unique exceptional owner, positive mean hazard gives almost-sure
singleton-`i` absorption.  Bellman telescoping therefore pins every stored
payoff coordinate to `r({i})`; in particular the owner's payoff is
`d_i=r_i({i})`.  Against always-Continue opponents, every finite stopping
time of `i` pays `d_i` and Never pays zero.  Thus the owner is protected
exactly when `d_i>=0`.  Every other player sees owner `i` absorb almost surely;
finite pure-time deviations are capped by exact Nash--Bellman recursion,
Never is the limiting Continue case, and pure-time extremality covers all
behavioral deviations.  This verifies both alternatives and does not use the
false implication `punishment_i>=0`.

## 3. Proposition 1B: exact negative-solo floor recurrence

For

```text
r({0})=(-1,1),   r({1})=(-2,1),   r({0,1})=(-2,0),
```

and root `(p,0)`, player `0` receives `-1` from either endpoint at continuation
`(-1,1)`.  Player `1` receives `1` by Continue and `1-p` by forced Quit.  The
Bellman value is exactly `(-1,1)`.

Player `1` quitting surely caps player `0` at `-2`, and no terminal payoff is
below `-2`, so `chi_0=-2`.  Player `0` quitting surely caps player `1` at one,
so `chi_1<=1`.  The constant value therefore lies above the production floor.
Repeated play absorbs at singleton `{0}` and pays player `0` `-1`, while its
Never deviation against prescribed player `1` pays zero.  The gain is exactly
one.  The example falsifies the path compiler only; it does not claim the
table lacks some other equilibrium.

## 4. Proposition 2: invariant mean equals prefix growth

The suffix of any path is again admissible, so
`A_(N+K)<=A_N+A_K`; Fekete gives the limit and infimum.  Invariance gives the
upper bound on every invariant mean.  For the converse, empirical measures
of maximizing paths have weakly convergent subsequences because the path
space is compact metrizable.  The telescoping test-function identity makes
the limit shift-invariant, while continuity of `a` identifies its mean with
the limit of `A_N/N`.  Standard ergodic decomposition retains a maximizing
ergodic component.  The negative-solo qualification is correctly preserved
when Proposition 1 is invoked.

## 5. Proposition 3: bounded path bias

If `K=sup_N A_N<infinity`, every path has total nonnegative charge at most
`K`.  Its infinite charge sum is the increasing pointwise supremum of
continuous partial sums, hence bounded and lower semicontinuous.  Splitting
off the first term proves

```text
Phi(omega)=a(omega_0)+Phi(S omega)
```

exactly.  The note correctly does not promote this path-dependent lower-
semicontinuous function to a continuous function of the current Bellman state.

## 6. Exact surviving obligations

The recurrence route now has two independent seams.  Positive invariant mean
may concentrate on the negative-solo one-owner component, where the selected
path is genuinely exploitable.  In the zero-mean branch, unbounded sublinear
prefix charge can still yield a useful divergent path, while bounded prefix
charge gives only the path-space bias above.  A universal proof must either
dispatch the negative-solo component and the sublinear-charge branch, or turn
the bounded bias into a state-local strategic obstruction.  I found no
mathematical objection beyond these limitations already stated by the author.

## 7. Post-review stabilization: no-harm dispatch and harmful hazard floor

The author subsequently sharpened Proposition 1 and replaced Proposition
1B's illustrative table.  I refreshed the note and independently checked
these additions.  **They are also VALID ordinary mathematics.**

For the exceptional owner `i`, the floor gives `chi_i<=d_i<0`.  If
`r({i})_j>=d_j` for every `j`, then `i` literally witnesses
`QuittingNormalNoHarmSingletonOwner`; the checked
`exists_uniformEquilibriumPayoff_of_normalNoHarmSingletonOwner`
(`UniformEquilibrium/Quitting/Classification/LCP/ProjectiveQBarBehavioralDecoder.lean`)
dispatches the game.  Otherwise choose a harmed outsider `j` with
`r({i})_j<d_j`.  At a root with owner hazard `p`, forced Quit by `j` pays

```text
p r({i,j})_j+(1-p)d_j,
```

while Continue pays `r({i})_j`.  Endpoint Nash therefore gives

```text
p (d_j-r({i,j})_j) >= d_j-r({i})_j > 0.
```

The denominator is positive and the displayed uniform lower bound on `p`
follows.  Thus the residual positive-mean component is not merely
negative-solo: it is harmful and uniformly charged.

The strengthened Proposition 1B table is

```text
r({0})=(-1,1),   r({1})=(-2,2),   r({0,1})=(-2,-2),
```

with root `(1/2,0)` and value `(-1,1)`.  Player `0` gets `-1` from both
endpoints.  Player `1` gets one from Continue and zero from forced Quit, so
the Bellman and endpoint-Nash equations are exact.  Sure Quit by player `1`
caps player `0` at `-2`; sure Quit by player `0` caps player `1` at one.
Hence the value lies above the punishment floor.  Player `0` still gains one
by Never, while `r({0})_1=1<2=d_1` and the hazard inequality requires only
`p>=1/4`.  This genuinely realizes the stabilized harmful residual
alternative; it remains a path-compiler falsifier, not a game counterexample.

## 8. Proposition 1C: punishment completion closes positive invariant mean

The later Proposition 1C is **VALID ordinary mathematics**, and it removes
the exceptional-owner qualification completely.  In Proposition 1's second
output, choose any root of the selected typical path.  Only owner `i` has a
positive Quit probability `p`; all stored current and tail values are the
singleton column

```text
c=quittingSoloReward reward i.
```

Consequently the root is literally
`quittingSoloStationaryRoot i hazard`, with `(hazard true).toReal=p>0`.
`IsQuittingNashBellmanEdge` supplies exact
`IsεQuittingRootEndpointNash reward c 0` against its tail value `c`, and the
floor carrier supplies

```text
quittingPunishmentValue reward i <= c_i.
```

These are exactly, without a sign or no-harm adapter, the three hypotheses of
`isUniformEquilibriumPayoff_soloReward_of_endpointNash_of_punishmentIR`
(`UniformEquilibrium/Quitting/Punishment/SoloCycleCompletion.lean`).  The
checked conclusion is the fixed singleton payoff `c` against unrestricted
behavioral deviations.  Thus every positive-mean ergodic law closes the game.

The strengthened Proposition 1B is consistent with this result: its bare
constant spine remains exploitable, but its root has positive solo rate,
exact endpoint Nash, and `chi_0=-2<=-1`, so the checked punishment-completed
solo-cycle compiler repairs exactly the Never deviation.  The only recurrent
obstruction left by Propositions 1C--2 is therefore `beta=0`, equivalently
sublinear maximal finite-prefix charge.  I found no mathematical or
strategy-class objection to this sharpening.
