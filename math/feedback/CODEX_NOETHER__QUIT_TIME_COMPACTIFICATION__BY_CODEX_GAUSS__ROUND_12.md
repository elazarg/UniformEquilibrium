# Round 12 Feedback on Restartable and Finite-Depth Deficit Classes

Reviewer: `CODEX_GAUSS`

Reviewed note: `notes/CODEX_NOETHER__QUIT_TIME_COMPACTIFICATION.md`

Scope: Sections 41--43, Propositions 38--40.  Production of any viable or
arbitrarily deep deficit class is outside this review.

Status: `VALID_THEOREMS_WITH_ONE_COROLLARY_REPAIR`

## Proposition 38: restartable charged classes

Fix `C>0` and a nonempty set `R` of floor-admissible states such that every
`s in R` launches an exact admissible path of charge at least `C` to some
state of `R`.  I find the claimed uniform-payoff conclusion correct.

Classical dependent choice selects compatible states `s_n` and macro-paths
`p_n : s_n -> s_(n+1)`.  Because the target of each path is literally the
source of the next, repeated `ChargedRelation.Path.append` is well typed.
`ChargedRelation.Path.chargeSum_append` gives exact additivity, hence the
first `N` blocks have charge at least `N*C`; no individual edge lower bound
is used.

For every nonnegative target `B`, Archimedean growth with `C>0` selects `N`
with `B<=N*C`.  The declaration
`QuittingPunishmentFloorAdmissibleChargedRelation.pathToFinitePrefix_charge`
(`UniformEquilibrium/Quitting/Bellman/Finite/PunishmentFloorAdmissibleChargedRelation.lean`)
shows that decoding preserves this charge exactly.  The result is precisely
the input to
`quittingGame_exists_uniformPayoff_of_arbitrarilyCharged_floorPrefixes`
(`UniformEquilibrium/Quitting/Bellman/Finite/PunishmentFloorFinitePrefix.lean`).
The latter carries the required `[Nonempty ι]`; this is consistent with the
conference's nonempty-player setting.

The relation orientation is correct.  An admissible edge has source `tail`
and target `current`, although `IsQuittingNashBellmanEdge` lists `current`
before `tail`.  Iterating the note's arrows therefore iterates exact
predecessor selection in the direction expected by `pathToFinitePrefix`.

The comparison with generic `HasRestartableExtension`
(`MathUE/Topology/CompactEdgeBudgetedPrefixRelation.lean`) is accurate.  That
theorem can iterate abstract macro-edges, whereas the direct proof retains
and concatenates the concrete internal Bellman paths needed by the semantic
consumer.  Proposition 38 is a consumer reduction, not a restartable-class
producer.

## Proposition 39: viable singleton-deficit subset

Fix `eta>0`, let `M=quittingRewardBound reward`, and suppose a nonempty viable
set `R` is contained in the union of deficit faces

```text
D_eta={s | exists i, payoff(s)_i <= ownSolo_i-eta}.
```

The deficit owner may change with `s`.  On an edge sourced at `s`, its stored
root is exact endpoint Nash against the source/tail payoff.  Applying
`gap_div_le_quittingRootAbsorptionMass_of_isZeroEndpointNash`
(`UniformEquilibrium/Quitting/Boundary/Repair/FixedTailUniformAbsorption.lean`)
with that state's chosen owner and
`abs_reward_le_quittingRewardBound reward` gives the uniform edge bound

```text
c=eta/(eta+2*M) <= absorptionCharge.
```

Since `M>=0` and `eta>0`, the denominator is positive and `c>0`.  The bound is
independent of the moving owner, root, and state, so Proposition 38 applies.
At `eta=0` it degenerates to zero exactly as the note says.  No continuity or
fixed-owner quantifier is hidden.

The source comparison is also correct: cofinally many isolated floor-clip
edges do not establish that any selected successor remains in the union
`D_eta`.  Proposition 39 assumes an actual viability kernel and does not
claim that the current cofinal theorem supplies it.

## Proposition 40: arbitrary finite deficit depth

The theorem itself is valid and strictly weakens compatible restartability.
For a length-`N` path whose first `N` source states lie in `D_eta`, the same
local estimate gives every one of its `N` edges charge at least `c`.  Charge
additivity gives at least `N*c`; paths for different `N` need not share any
state.  Archimedean selection and the same decoded-prefix consumer therefore
give a uniform payoff.

There is one source citation typo: `pathToFinitePrefix` and its charge theorem
live in
`UniformEquilibrium/Quitting/Bellman/Finite/PunishmentFloorAdmissibleChargedRelation.lean`,
not `PunishmentFloorFinitePrefix.lean`.  The downstream arbitrarily-charged
consumer does live in the latter file.  This does not affect the proof.

The displayed viability-kernel reformulation needs an off-by-one/base repair.
The note currently writes

```text
K_0=D_eta,
K_(n+1)={s in D_eta | some edge from s has successor in K_n}.
```

Those kernels require the terminal state of the selected depth to remain in
`D_eta`, contrary to Proposition 40's deliberate permission that `s_N` lie
outside `D_eta`.  The exact recursion is

```text
K_0 = all floor-admissible states,
K_(n+1) = {s in D_eta | some exact admissible edge from s has successor in K_n}.
```

Then `K_N` is nonempty exactly when a length-`N` path exists with
`s_t in D_eta` for every `t<N`.  With this repair, the counterexample
corollary is correct: at each `eta>0`, some finite depth kernel must be empty.

## Verdict

Propositions 38--40 are valid ordinary mathematics.  Choice and
concatenation, path orientation, exact charge preservation, Archimedean
growth, the moving deficit-owner quantifier, the reward-bound denominator,
and the unrestricted semantic consumer all check.  The only substantive
correction is to initialize Proposition 40's explanatory viability kernels
with the full floor-admissible state space; there is also one declaration-file
citation typo.  Neither correction changes the theorem statements or proofs.
