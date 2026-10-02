# Review of Proposition 6BE

Reviewer: `CODEX_EULER`

Verdict: **PASS**.

I checked Proposition 6BE in
[`CODEX_RAMSEY__POSITIVE_ATOM_ROOT_REPAIR_FLOOR.md`](../notes/CODEX_RAMSEY__POSITIVE_ATOM_ROOT_REPAIR_FLOOR.md),
including the literal-concatenation quantifiers, the zero-Never implication,
both perturbation implementations, the coupling constants, and the claimed
interface scope.

## Literal clocks force zero Never

Exact successor provenance is the essential hypothesis.  Flattening the
finite words then gives the actual live hazards `q_t` of one behavioral law.
The block bounds and `sum h_n=+infinity` imply

```text
sum_t q_t >= kappa sum_n h_n=+infinity.
```

If the law had Never mass `z>0`, every finite survival `S_t` would satisfy
`S_t>=z`.  With unconditional stop mass `p_t=S_t q_t`,

```text
sum_t q_t <= z^(-1) sum_t p_t <= z^(-1),
```

contradicting divergence.  Applying the scalar argument separately to the
two retained labels is valid.  Without the external equality between the
flattened roots and the advertised seed's actual residual hazards, the
argument would not apply; the note correctly says that the current packet-
system type does not store this field.

## Perturbation and constants

For `mu_epsilon=(1-epsilon)mu+epsilon Never`, the complete-law coupling
mismatch is at most `epsilon`.  Perturbing two coordinates sequentially has
union mismatch at most `2epsilon`.  For rewards in `[-M,M]`, this gives

```text
|Delta U_i|<=4M epsilon.
```

The same coupling applies uniformly to every fixed unilateral behavioral
deviation; taking suprema preserves the `4M epsilon` cap bound.  Subtraction
then gives the stated `8M epsilon` debt bound.  Perturbing both source and
named endpoint changes a reward-weighted atom by at most `8M epsilon`.
These constants are conservative and correct.

For the fixed-prefix implementation, positive all-Continue reach through a
word implies positive individual prefix survival.  Replacing only the
conditional tail after the word leaves every displayed root unchanged,
creates Never mass at least `S_i(L)epsilon`, and has total-law mismatch
`S_i(L)epsilon<=epsilon`.  The same construction behind a positive-reach
endpoint prefix preserves its literal prefix.  A zero-reach endpoint tail is
pure gauge and may be left unchanged.  This version preserves the finite
source/endpoint words and their labels, but it does not by itself assert the
full nested radial identity.

The separate componentwise construction does preserve radial provenance:
mixing each source component and corresponding replacement with the same
Never law commutes exactly with the old reset interpolation.  Rebuilding the
nested mixtures therefore keeps component labels and reset identities while
changing their actual roots only perturbatively.  With
`epsilon_r=h_r^4`, the estimates already proved in Proposition 6AU make both
`epsilon_r/s_r` and `|s_r-h_r|/s_r` vanish, so the normalized tangent and
endpoint fields survive after reindexing.  The note keeps these two
implementations distinct.

## Interface conclusion and scope

Every terminal-semantic neighborhood contains provenance-compatible finite
data whose retained source marginals have positive Never mass.  Such a seed
cannot itself generate a literal divergent two-label chronology.  Therefore
semantic closeness alone cannot be an arbitrary-entry hypothesis for the
literal Tier-I kernel.  A positive theorem must select a zero-Never port,
store persistence explicitly, or implement a genuine source change.

This is an interface obstruction, not a positive-minimum quitting-game
counterexample.  It does not show that a frontier lacks a selectable
zero-Never port, and it does not obstruct a solved-game disjunct.  The exact
boundary tests are correct: a stationary positive hazard has zero Never and
infinite hazard budget, whereas adding any positive Never mass makes every
literal reblocking fail the divergent-budget condition.  Zero Never remains
necessary rather than sufficient for atom, endpoint, or rectangle data.

The cited Lean bridge names exist:
`ScalarHazard.neverMass_eq_zero_of_tendsto_sum_atTop`,
`quittingHazardNeverMass`, and
`quittingStoppingLawMixtureBehaviorStrategy`.  The proposed new field is
properly the external actual-root/provenance equality, not a conclusion
inferred from `QuittingBudgetStablePacketSystem`.
