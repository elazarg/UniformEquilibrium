# CODEX_NOETHER independent review of the mixed-sign paired producer

## Frozen claim and verdict

Reviewed the section headed “A mixed-sign paired producer on the
nonbijective two-cycle-plus-leaves branch” through EOF in
`notes/CODEX_BROUWER__NONBIJECTIVE_SINGLETON_SOURCE.md`, section SHA256
`a59c1f3a57e4ba35c4dee353d257766dd9ab4cc544496c67b0d908bff0448aa7`.
This review concerns that original MP1–MP6 version, not a subsequently
suggested modification of its unused reward entries.

SOUNDNESS: PASS as complete ordinary mathematics. The four-hazard IFT
producer, arbitrary signed own-row translations with zero Never payoff,
all behavioral deviations, and fixed-profile/fixed-target uniform
quantifiers are valid. No Lean implementation or build is asserted.

EXPORT SIGNIFICANCE: FAIL for this original local class. The complete
implemented empty-premium-core existence producer, combined with the
implemented no-UE single-pivot normalization source, already covers
every signed Fin4 empty-core table. Every sufficiently small centered
neighborhood of this MP center is empty-core. Thus arbitrary signed
own translations do not recover a new counterexample exclusion.
The stronger exact-profile conclusion remains useful internal
mathematics but is not a new UE existence class under exports/README.

## Exact claim checked

The data are a complete four-player table with independent private
behavioral randomization, one public live history at each date, absorbing
payoffs on the first nonempty quitting coalition, and Never payoff zero.
MP produces proper period-two rates for its explicit centered table z,
and then for every arbitrary centered table in one open neighborhood
of z. It translates the construction back to every possible own vector
s∈ℝ⁴. The conclusion is exact terminal Nash against every complete
unilateral behavioral replacement, followed by a uniform-payoff
conclusion for one literal profile and one target fixed before accuracy.
This is an actual-data producer, not a supplied-certificate verifier.

The strategic inputs are all produced: the initial root a is supplied
by IVT; b is its explicit rational function; all phase values are
explicit; all four nearby hazards are supplied by parameterized IFT;
properness and the passive Quit margins persist by continuity. No
strategic input remains assumed. The radius is existential, as stated.

## Independent exact soundness checks

I ran the complete standard-library Fraction verifier printed in MP4.
It passed the two exact endpoint values of P, both cleared substitution
identities, all six rational interval bounds, and both determinant
bounds. Separately, I rebuilt every phase Quit and Continue endpoint
from the complete 15-coalition table, rather than using the claimed
reduced equations. Exact symbolic simplification verified every active
identity, every printed passive Quit formula, the complete 4×4
Jacobian, and its symmetric/antisymmetric determinant factorization.
These are exact ordinary checks, not floating-point or Lean evidence.

Specific valid steps are as follows.

1. P changes sign at the two rational endpoints. D=1−a³ is positive,
   and the convex lower-bound polynomial and the shifted upper-bound
   polynomial give 3/16<b<1/5. Uniqueness of a is unnecessary.
2. Each active owner faces its mate only. The supplied X and W make
   both active actions indifferent at the actual X, not merely at an
   arbitrary annotation. The passive Continue equations clear exactly
   to the two displayed polynomials. The root substitution therefore
   realizes every prescribed phase value.
3. Passive Quit includes all nonempty opponent coalitions, including
   the simultaneous pair. For bad owners its value is below −1/3 while
   W is above −1/8; for good owners Quit is negative while W>1/4.
   The four margins are genuinely strict.
4. All four hazard coordinates, rather than two symmetry coordinates,
   are solved in MP4–MP5. For the independently differentiated field,
   the printed matrix J is correct. Its two block determinants satisfy
   Δ₊≤−281/640 and Δ₋≥69/50. The parameterized IFT therefore applies
   to arbitrary centered reward perturbations, not only symmetric ones.
5. F=0 is exactly the passive Continue identity because 1−q_m>0.
   Active identities follow from the arbitrary-table X,W formulas at
   every proper q. Continuity of the finite list of passive Quit tests
   permits a common neighborhood shrinkage. Perturbed unused entries
   do not create a missing prescribed or unilateral coalition test.

The existing semantic consumer is
`GameTheory.PairedCycle.twoPair_exact_terminal_and_fixedProfile` in
`UniformEquilibrium/Quitting/Cycles/TwoPairExactCertificate.lean`.
Its proper-rate, passive Continue, and passive Quit hypotheses match
the produced data exactly, with no hidden singleton-floor or premium
sign assumption. I also inspected the arbitrary-table identity
`GameTheory.PairedCycle.TwoPairOdds.passiveEquation_eq_scaled_post_sub_continue`
in `UniformEquilibrium/Quitting/Cycles/TwoPairOddsValues.lean`.
These consumers do not produce MP's new rates by themselves.

## Explicit attempts to falsify the semantic chain

The principal attempted falsifier was own-row translation with Never
fixed at zero. Such a translation is NOT an invariance of arbitrary
quitting profiles. Here it is valid for the stated reason: after any
one player is replaced by any behavioral deviation, the three unchanged
players still have deterministic proper phase hazards. Their two-date
survival probability is at most κ=169/384<1. Thus every unilateral
profile absorbs almost surely, including when the replacement itself
plays literal Never. Every prescribed and deviation terminal payoff
really gains s_i; no residual Never event contributes a different
offset. This falsification attempt did not expose a gap.

I also tested the likely missing-cap failure: a passive player's Quit
can add a third quitter to the two scheduled opponents. The actual
triple entries were included in the independent complete-table endpoint
calculation, and the margins above survived. A grand coalition cannot
occur against a unilateral replacement, since at most two unchanged
owners are active in a phase; this is a genuine agency restriction,
not an omitted response. No arbitrary simultaneous deviation is needed
for Nash. A perturbation of a used triple is controlled by the strict
margin and the neighborhood shrinkage. No finite selected-response
ledger is being mistaken for the entire behavioral cap.

Finally, the finite-horizon quantifiers are not interchanged. For any
fixed table the rates, profile, and phase target are fixed first.
The opponent-deleted geometric tail gives E[τ+1]≤768/215 for the native
rates. At a nearby table some finite analogous constant is enough.
The exact terminal-to-average error is at most M E[τ+1]/H, uniformly
over the replacement. This yields delivery error of that order and
regret at most twice it. Only the horizon threshold depends on the
requested accuracy. Arbitrarily large signed translations merely
change the finite reward bound M; they do not invalidate the argument.

Positive boundary: s=(1,1,1,1) indeed makes AllNever fail by a profitable
solo Quit, while MP's absorbing exact profile remains valid. This
boundary excludes the trivial native AllNever proof, but does not
exclude the implemented nontrivial empty-core producer below.

## Decisive complete-producer overlap

For every player i and every coalition S containing i with |S|≥2,
the printed center has

    z_i(S)≤−1/2,       z_i({i})=0.

This is a complete participant comparison across all coalitions, not a
few favorable singleton screens. If a centered table z′ is within
supnorm 1/4 of z, then every such participant premium is below −1/4.
Singleton premiums are identically zero. Thus there is no positive
participant-premium witness at any coalition, hence no premium trap
on any nonempty support, hence its premium core is empty. Row
translation does not change any of these comparisons.

The exact relevant definitions are `GameTheory.HasPositiveOwnQuittingPremium`
in `UniformEquilibrium/Quitting/Classification/QuittingPremiumSupportPeelingOrder.lean`,
`GameTheory.IsQuittingPremiumTrap` and `GameTheory.quittingPremiumCore`
in `UniformEquilibrium/Quitting/Classification/QuittingPremiumCore.lean`,
and `MathUE.IsFiniteCoalitionPremiumTrap` and
`MathUE.finiteCoalitionPremiumCore` in `MathUE/FiniteCoalitionPremiumCore.lean`.
An empty core is not being inferred from just one failing trap witness.
The complete trap selection set is empty by the uniform participant
inequality.

For nonnegative own singletons the named implemented producer is

    GameTheory.exists_uniformEquilibriumPayoff_of_empty_quittingPremiumCore

in `UniformEquilibrium/Quitting/Classification/Existence/SignedPairCoreUniformPayoff.lean`.
Its hypotheses are exactly nonnegative own singletons and empty core;
it does NOT require nonnegative participant premiums. Its proof
internally supplies supportwise balance from weak premium peeling.
The empty branch of
`GameTheory.exists_uniformEquilibriumPayoff_of_empty_or_signed_pair_core_weakSameSign`
in `UniformEquilibrium/Quitting/Classification/Existence/SignedPairCoreRewardClosure.lean`
calls this producer directly.

There is also COMPLETE overlap for arbitrary signed own singletons,
not merely for the positive-own translates. Here is the full short
ordinary corollary of the implemented sources.

Let r be any Fin4 table with empty core, without any own-sign hypothesis.
Suppose for contradiction that r has no UE payoff. A finite reward
bound exists. The declaration

    GameTheory.nonempty_finFourSinglePivotNormalization_of_no_uniformPayoff

in `UniformEquilibrium/Diagnostics/Quitting/FinFourSinglePivotNormalization.lean`
produces a pivot p with s_p>0 and the literal normalized table

    r′_i(S)=(r_i(S)−o_i)/s_p,
    o_p=0,       o_i=s_i for i≠p.

Its output record supplies BOTH no UE for that same r′ and canonical
own vector (1,0,0,0), with the pivot position permuted as appropriate.
This is an actual no-UE source, not an assumed normalization witness.
The definitions `GameTheory.quittingSinglePivotOffset` and
`GameTheory.quittingSinglePivotNormalizedReward`, and the theorem
`GameTheory.quittingSoloReward_singlePivotNormalized`, are in
`UniformEquilibrium/Quitting/Root/SinglePivotNormalization.lean`.
The canonical singleton predicate is
`GameTheory.IsSinglePivotSingletonTable` in
`UniformEquilibrium/Quitting/Terminal/SinglePivotFiniteMenuSource.lean`.

For every row and every coalition, direct subtraction gives

    r′_i(S)−r′_i({i})=(r_i(S)−r_i({i}))/s_p.

Since s_p>0, the ENTIRE strict premium relation is unchanged. The
trap family and its union/core are unchanged as well. Thus r′ has
empty core and nonnegative own singletons. The implemented empty-core
producer gives it a UE payoff, contradicting the normalized no-UE
field. Therefore every signed Fin4 empty-core table already has UE.

This argument does not assert a general affine UE invariance with
Never=0. It uses exactly the no-UE normalization source, whose output
includes the requisite normalized no-UE claim. Confusing these two
statements would be an error; the actual source avoids it.

The accepted packet `exports/MIXED_PREMIUM_TRAPS_UNIFORM_EQUILIBRIUM.md`
also contains the nonnegative-own empty-trap case: all pair and larger
trap conditions have empty selection sets and are vacuous. Its
existence proof is not excluded by MP6's paired and quotient screens.
The same normalization contradiction extends that already accepted
empty-trap coverage to the signed-own input. No new enumeration of
quiet-child or punishment witnesses is needed to reject this MP
existence-class claim, because this complete producer already covers
every table in a sufficiently small claimed neighborhood.

More precisely, MP's IFT proof may choose its radius no larger than
1/4. The entire produced class at that radius is covered above. A
larger quantitative neighborhood could conceivably include a table
with nonempty core, but MP supplies neither such a radius nor such a
table. A bare existential local radius does not certify that stronger
coverage. The exact paired witness can be stronger than a prior UE
existence witness without eliminating another counterexample.

## Gate disposition and useful continuation

MP1–MP5 are a sound, reusable internal actual-data exact-profile
construction. MP6's stated named-interface exclusions do not establish
new conjecture coverage, and the complete empty-core overlap prevents
promotion of this original section. No unresolved soundness objection
is left; the unresolved export requirement is significance, not a
missing cap, missing root, or insufficient uniform quantifier.

A material extension must leave the empty-core class and exhibit an
actual raw table outside the applicable complete existential producers
and accepted existence packets. Changing unused grand/triple rewards
may preserve this exact profile, but that is a new claim requiring
complete data and a separate overlap preflight. This review neither
accepts nor rejects that unsubmitted extension. No constant refinement
or further audit of the original empty-core neighborhood is needed.
