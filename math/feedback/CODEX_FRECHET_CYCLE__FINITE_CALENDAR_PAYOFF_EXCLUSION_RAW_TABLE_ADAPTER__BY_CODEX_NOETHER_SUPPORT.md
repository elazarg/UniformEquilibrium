# Independent review of finite-calendar payoff-exclusion recognition

Reviewer: CODEX_NOETHER_SUPPORT.

Reviewed manuscript:
[finite-calendar raw-table adapter](../notes/CODEX_FRECHET_CYCLE__FINITE_CALENDAR_PAYOFF_EXCLUSION_RAW_TABLE_ADAPTER.md).
Reviewed SHA256:
`35f330143fef16c3c040161327c40d39097e2a649f0f1608047874ae8bc96e91`.

Verdict: PASS as ordinary mathematics, with no unresolved mathematical
objection or requested proof repair. This review includes an independent
derivation and explicit falsification attempts at the new interfaces.
It does not assert a Lean implementation or authorize export by itself.

## 1. Precisely what was checked

For four independent private stopping laws on natural dates and Never,
with a fixed finite reward table and zero Never payoff, the manuscript
proves that the entire actual prescribed-payoff image, and its closure,
equal the payoff image of one twenty-date product simplex. It then gives
equivalent finite real-algebraic tests for the already specified strict
deficit PD, nonconcentrated group exclusion GE, and signed-outsider weak
subset exclusion WE_J. Accepted rational tables have computable positive
rational parameters where those consumers need them. The frozen actual-law
selectors then produce arbitrary-accuracy finite words, whose lengths are
not bounded by twenty.

The checked result is a raw-table recognition adapter. It is not a
twenty-date equilibrium theorem, payoff/cap compression theorem, new
existence class beyond its listed hypotheses, or strategy-class completeness
claim for finite-menu equilibria.

## 2. Independent check of the realization proof

For each original marginal, the probability of a changed draw under finite
censoring is its finite tail mass, not its existing Never mass. These tails
tend to zero. Independent coupling therefore changes each bounded payoff
coordinate by at most 2M times the sum of the marginal tail masses. Given a
sequence approaching a payoff closure point, choose a separate cutoff for
each sequence member. No uniform tightness assertion is required.

For one finite profile and one player, fixing the other CURRENT marginals
makes the WHOLE prescribed payoff vector an affine function of that player's
law. If more than n+1 actions have positive mass, their payoff vectors
augmented by a final coordinate one are linearly dependent. The coefficients
of a nonzero dependence sum to zero, so they have both signs. Moving the
weights in one direction until the first vanishes preserves nonnegativity,
the total mass, and all n payoff coordinates. Iterate. The player uses only
actions in its old support.

Applying this operation successively to all players is valid. Later
operations may change the pure-response vectors seen by an earlier player,
but they do not need to preserve those vectors: they preserve the CURRENT
whole prescribed payoff and never enlarge the earlier marginal's support.
There remains exactly one independent product profile at every step.

At most n(n+1) finite dates remain in the union of the supports. One common
increasing rank map preserves all finite orders and equalities; fixing
Never also preserves finite-versus-Never comparisons. Thus the prescribed
first quitting coalition is unchanged on every support tuple, including
simultaneous full quitting and all-Never. Transforming each marginal by the
same deterministic map retains independence.

The compressed profiles lie on one fixed finite product simplex. Marginal
support size at most n+1 defines a finite union of closed faces, so it is
compact. The finite prescribed-payoff map is polynomial and continuous.
A convergent subsequence consequently realizes every requested closure
point, with the support bound retained. This is the only compact-limit
step; it does not appeal to continuity of terminal outcome under arbitrary
weak clock convergence. The reverse inclusion is immediate actual play.

Thus the exact image equality and its compactness conclusion pass, both
for n players with n(n+1) dates and for n=4 with twenty dates.

I additionally read the matching payoff proofs in TARSKI's
[prescribed-outcome note](../notes/CODEX_TARSKI_PREMIUM__FINITE_CALENDAR_PRESCRIBED_OUTCOME_REALIZATION.md)
and FRECHET's earlier
[payoff-carrier note](../notes/CODEX_FRECHET_CYCLE__ACTUAL_PAYOFF_CARRIER_POTENTIAL_LOCALIZATION.md).
The present review does not import either note's stronger outcomes or
potential claims; the manuscript's displayed proof is sufficient.

## 3. Polynomial map and the three exact tests

The first-coalition formula is correct. For each finite date t, every
member of S must choose exactly t and every other player must choose a
later finite date or Never. Multiplying those independent events and
summing over t produces P_S. Together with the product Never mass these
are disjoint and exhaustive events. In particular the outer sum must NOT
include Never as a finite full-coalition tie. The manuscript keeps them
separate.

The hazard denominator is the marginal survival mass at t. When it is
zero, all later finite and Never masses of that marginal are already zero;
the proposed zero-hazard convention is harmless on the unreachable own
tail. Thus every point in the product simplex is an executable finite word.

For PD, forbidding an all-nonnegative surplus vector says that the
continuous minimum coordinate is strictly negative everywhere on the
compact simplex. Its maximum is attained and remains strictly negative,
providing one positive UNIFORM κ. Conversely PD directly forbids that
vector. Replacing nonnegative by strictly positive would lose the margin;
the text correctly does not do so.

For WE_J, the negation of some surplus coordinate being nonpositive is
that every coordinate in J is strictly positive. The stated strict forbidden
system is therefore exact, including the equality boundary. The singleton
sign conditions belong to the consumer and are explicitly retained.
Enlarging J preserves the disjunction, so the largest admissible set J_+
correctly recognizes existence of a witnessing subset when nonempty.

For GE, enlarge a valid maximum weight bound to β'≥1/2 while keeping
β'<1. If a_i is the smallest surplus and a_j is the smallest outside i,
then any weight in the capped simplex satisfies

    Σ_k w_k a_k ≥ a_j+w_i(a_i−a_j)
                  ≥ a_j+β'(a_i−a_j).

The last inequality has the correct direction because a_i−a_j≤0.
Equality is attained at β'e_i+(1−β')e_j; this is admissible precisely
because β'≥1/2 and i,j are distinct. Thus the minimum capped weighted
surplus is the minimum of the displayed twelve ordered-pair expressions.
One λ=1−β' works uniformly over profiles. Conversely any pair witnessing
the formula supplies a legal capped probability weight. Ties between
smallest coordinates do not alter the proof.

The order ∃λ∀x and its negation ∀λ∃x are correctly retained. The manuscript
does not infer a single profile witnessing failure for every λ. Neither
the capped-weight reduction nor its rational weakening has a gap.

## 4. Effective parameters and downstream scope

The finite predicates use polynomial equalities and strict or weak
inequalities with rational coefficients for rational tables. Their truth
sets in the reward variables are semialgebraic by real quantifier
elimination. This gives an in-principle exact recognition procedure for
rational and real-algebraic encoded tables, not for arbitrary unencoded
real data. The manuscript states this limitation.

After PD has been recognized, some 1/k lies below its positive margin,
so exact tests for supplied κ=1/k eventually succeed. For GE, after sorting
the surplus coordinates, the minimum pair expression is
a_(1)+λ(a_(2)−a_(1)), nondecreasing in λ. Therefore any smaller positive
λ remains valid simultaneously for all x. Testing λ=1/k for k≥2 likewise
terminates after GE recognition. No strict-margin assumption is improperly
added to WE_J. Positive rational reward bounds and error tolerances can be
supplied independently.

I checked the actual frozen source
[payoff-exclusion selectors](../exports/PAYOFF_EXCLUSION_ACTUAL_SELECTORS_AND_EXACT_SUFFIX_LIMITS.md):
its hypotheses are exactly PD, GE and WE_J as stated here. It computes
complete caps of its own literal words, selects approximate auxiliary
Boolean roots with rational error budgets, and controls TOTAL complete
debt. Applying it at any smaller requested tolerance gives the displayed
strict target inequality. Its exact every-suffix conclusion needs PD AND
nonnegative own singletons for every player; the adapter retains both.
Finite PD and GE selection have no such singleton sign premise. WE needs
only signs on J. The fixed uniform-payoff and all-behavior conclusions
are inherited from that packet, not inferred from finite payoff realization.

The optional cap-threshold consumer is correctly restricted to its
all-player nonnegative WE entrance. The broader qualitative signed-subset
implication uses only the existing strict-minimum plateau and a payoff
projection. No caps are transported to the finite realization.

## 5. Falsification attempts and small boundaries

I checked the following minimal hazards to the argument.

- A finite tail converging to Never: only finite tail mass is censored, so
  genuine Never mass does not obstruct the approximation step.
- A full-coalition tie versus all-Never: the former appears in P_I at a
  finite date and the latter only in P_∅. They cannot be confused.
- Sequential compression interpreted as a public mixture: the proof
  changes one private marginal at a time, so no correlation is introduced.
- A cap transported through equal payoff: the two-player example in
  Section 6.7 indeed has equal prescribed payoff zero and caps one versus
  zero. The adapter makes no use of that false implication.
- Strict/weak collapse: the identically zero table fails PD while satisfying
  GE and admissible WE_J. This confirms that the strict signs are necessary.
- WE implying GE: the stated pure-{0} surplus (0,1,1,1) gives every capped
  weighted surplus at least 1−β>0, while coordinate 0 never exceeds its
  own singleton. The separation is exact.
- Group exclusion mistaken for reward-convex-hull separation: in Section
  6.4, the independent-clock bound √x+√y≤1 is valid. If x≤y, then
  3x+y≤3t²+(1−t)²≤1 for t=√x∈[0,1/2], proving the claimed group surplus
  inequality even with positive Never mass. The correlated half-A/half-B
  lottery has every surplus 1/2, so it defeats every nonzero nonnegative
  fixed weight. That correlated lottery is not passed off as actual play.
- Recognition mistaken for exhaustive UE decision: the full-coalition
  example fails all three tests yet is a literal exact pure equilibrium.

The remaining examples, including PD⇒GE with the displayed positive λ,
also check by direct substitution. These attempts found no counterexample
to the stated claims.

## 6. Named declarations independently inspected

- `quittingTerminalPayoff_update_eq_expect_stoppingLaw_pureTime` in
  `UniformEquilibrium/Quitting/Paths/BehaviorStoppingPayoff.lean`.
- `quittingBehaviorStoppingLaw_finiteStoppingLawMixture` and
  `quittingTerminalPayoff_update_finiteStoppingLawMixture_eq_expect` in
  `UniformEquilibrium/Quitting/Paths/FiniteStoppingLawMixture.lean`.
  The latter has a separate observer argument, as required for whole-vector
  rather than owner-only affine replacement.
- `quittingTerminalSemanticCarrier` and
  `exists_terminalProfile_sequence_tendsto_semanticPair` in
  `UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`.
- `exists_finFour_strictMinimum_allContinuePlateau_of_no_uniformPayoff` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticFinFourStrictMinimumPlateauIsolation.lean`.
  Its actual declaration provides a carrier point strictly above every
  singleton coordinate, with no sign premise being silently added.
- `exists_uniformEquilibriumPayoff_of_nonnegativeWeightChamber` in
  `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticNonnegativeWeightChamber.lean`.
  The nonnegative weight has two positive coordinates and explicitly
  includes the Never comparison through its weighted-singleton premise.

No Lean files, shared indexes or exports were edited. The proposed adapter's
new connection is sound: fixed-calendar actual payoff realization converts
these universal finite-word hypotheses into finite raw-table recognition,
while the existing consumers construct and test the equilibrium words
separately. I recommend retaining exactly that narrow statement.

## Final-byte acceptance

I compared the reviewed source with
[the named candidate](../exports/FINITE_CALENDAR_PAYOFF_EXCLUSION_RAW_TABLE_TESTS.md)
and accept SHA256
`55db4eb51e4b309de13498bdbabfa1e808b5e3fde35a5fb3a31dc4483e5bb99f`.
The only changes are review/status provenance, relocation-safe links to the
two supporting notes, and removal of the requested-check paragraph. All
proofs, predicates, scope statements and boundary tests are unchanged.
There is no unresolved mathematical objection to these exact bytes.
