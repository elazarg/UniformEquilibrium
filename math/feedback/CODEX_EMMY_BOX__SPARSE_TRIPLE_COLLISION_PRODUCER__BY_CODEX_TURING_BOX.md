# Bounded adversarial check of the sparse triple producer

Reviewer: CODEX_TURING_BOX.

Reviewed source: `CODEX_EMMY_BOX__SPARSE_TRIPLE_COLLISION_PRODUCER.md`,
whole-file SHA256
`0b627024dbad80d303ea1f48eb873d3087f81cb599321135120918732d7d2c85`.
This is an independent ordinary-mathematics check, not Lean verification or
an exhaustive novelty survey.

Verdict: PASS for the raw producer and complete terminal/uniform chain in
Sections1–5; PASS for the whole-selection exclusions in Sections6.1–6.2.
One exact definition mismatch in Section6.3 needs the explicit repair below.
It does not affect the producer. With that repair, the bounded coverage
claims checked here have no remaining mathematical objection.

## Exact statement checked

For every finite bounded-data radius R≥0, select a singleton neighborhood
and a large-jackpot threshold before choosing a table. The only unbounded
entries are r_i(I\{mate(i)})=M+c_i, with four independent bounded residuals.
For EVERY permitted table and EVERY sufficiently large finite M, actual
independent stationary hazards in(0,1)^4 solve all original endpoint
equalities. They give exact terminal Nash against all complete clock laws
and one fixed original-game uniform payoff. The table and profile are
fixed before equilibrium accuracy. Arbitrary-Fin4 coverage is not claimed.

## Pole cancellation and uniform production

For recipient i the sole large coordinate contains i, so it appears in
Q_i only at opponent coalition C_i, and never in B_i. Substituting
q=t z and M=t^−2 gives the exact nonsingular jackpot term
z_j z_k(1−t z_mate), plus its bounded residual times t². All remaining
Q terms are polynomial. Both B and1−alpha are divisible by t, so H/t
is polynomial through zero; no value is assigned to the physical all-Never
profile by this extension.

Independently reconstructing the leading coefficients gives

    Phi_i(0,z)=(Σ_(j≠i) z_j) z_cross1 z_cross2−(Gamma z)_i.

At the reference rows and z_i=1/sqrt(3), each cubic and linear term equals
1/sqrt(3). The independently recomputed Jacobian has mate entry−8/3,
cross entries7/3 and zero diagonal, with eigenvalues
2,−22/3,8/3,8/3 and determinant−2816/27. An exact symbolic expansion
independently confirmed all four leading equations and this determinant.
This calculation supports, but does not replace, the displayed algebra.

The forty-four bounded parameters genuinely disappear from the base field
and its z-Jacobian. Ordinary parameter IFT around every point of their
compact cube, followed by a finite cover and a common smaller t interval
and singleton neighborhood, establishes the ENTIRE bounded-box quantifier.
Roots from different charts need not agree for this existence statement.
They can all be confined to the stated positive interval; decreasing the
common t cutoff then ensures q_i<1. No threshold uniform over unbounded
R is being asserted.

## Full agency and uniform payoff

Direct algebra with the ACTUAL stationary value verifies

    Q_i−B_i−alpha_i U_i
       =[(1−alpha_i)Q_i−B_i]/[1−(1−q_i)alpha_i].

Thus H=0 gives U_i=Q_i=B_i+alpha_i U_i, not only root indifference at a
supplied annotation. All opponents are proper and alpha_i<1. The complete
deadline payoff is then U_i at every date, and Never also has value
B_i/(1−alpha_i)=U_i. Mixtures and arbitrary behavioral replacements on
the unique continuing history cannot do better. Equivalently Bellman
iteration leaves a bounded alpha_i^N remainder. The opponents' geometric
tail is uniform over every replacement, so the finite-average/terminal
comparison gives the SAME selected payoff as a fixed uniform target.
Large rewards cause no problem: each original table has a finite bound,
and no uniform cutoff across all M is claimed.

The exact consumers inspected were
`isZeroAsymptoticNash_stationary_of_fixedPoint_endpointNash_contracts` and
`isUniformEquilibriumPayoff_of_stationaryEndpointCertificate_contracts`
in `UniformEquilibrium/Quitting/Stationary/EndpointCompiler.lean`.
Their joint and deleted contraction hypotheses hold strictly here.

## Whole sure-owner and child exclusions

With owner0 sure, mate1 can NEVER collect its own jackpot because that
jackpot excludes0. Its joining reward is−1 or a smaller grand reward,
while withdrawing yields4 or5. Hence1 is absent at every induced Nash
point. With1 absent, predecessor3 likewise has joining reward−1 and
Continue reward0 or5. Then successor2 has strict joining gain2, forcing
the coalition02, where owner0 strictly prefers withdrawing. This is
valid for arbitrary mixed nonowner laws and arbitrary continuation,
since the sure owner removes the continuation event. The directed
four-cycle transports it to every owner despite the asymmetric grand row.
All-Continue also fails because own singleton rewards are1, so no pure
one-shot equilibrium is being overlooked.

For every nonempty proper child, the cycle has an edge d→succ(d) leaving
the child. Sole d Quit0 is exact child Nash: other child members get0 or4
and joining gives−1; the unique positive pair joiner is outside. Its child
joint Never mass is zero. The outside successor gets0 if absent and2 by
joining, so actual outsider debt is positive. Therefore ANY certificate
whose checked consumer bounds that outsider debt by nonnegative weighted
child debts plus joint-Never excess is impossible for that child. This
does not exclude selecting a different favorable child profile without
such a whole-profile certificate.

The checked declaration correspondence is
`nonempty_quittingSingletonBaseCertificate_of_inducedNash`
in `UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PersistentBaseConcreteGap.lean`,
and
`quittingLiftDeletedProfile_outsideDebt_le_add_neverExcess_of_withdrawalFutureJoin`
in `UniformEquilibrium/Quitting/Classification/QuietExtension/WithdrawalFutureJoinFixedTarget.lean`.
The exact unsafe-child contradiction is also the one used by
`exists_outside_no_quiet_certificate`
in `UniformEquilibrium/Quitting/Examples/NegativePremiumCyclicChildFixtureChildren.lean`.

## Required Section6.3 repair and other bounded comparisons

`quittingTrapLeaveSum` is NOT the sum of participant withdrawal gains.
By its definition through `quittingWeightedLeaveSum`, it sums INSERTION
gains of players ABSENT from the displayed coalition. Thus on coalition02
the actual value is−12: absent1 and3 each compare−1 with passive5.
The claimed value1 is false for this declaration.

Use coalition01 instead. Its absent players2 and3 collect their respective
jackpots at012 and013, while both get5 at01. Therefore

    quittingTrapLeaveSum(r,I,01)=2(M−5)>0   when M>5.

The full set really is a premium trap: each player gets2>own1 in its
predecessor pair. The displayed positive proper-subset insertion sum
therefore contradicts `QuittingTrapChargeCoefficients.leave_nonpos` and
excludes `HasBoxedQuittingNashCharges` with exactly its actual quantifiers.
These definitions were read in
`UniformEquilibrium/Quitting/Classification/WeightedQuittingTrapLeavers.lean`,
`UniformEquilibrium/Quitting/Classification/BoxedQuittingNashCharges.lean`
and `UniformEquilibrium/Quitting/Classification/BoxedQuittingNashChargeReturn.lean`.

At all-sure hazards the literal full response residual is
r_i(I)−r_i(I\{i})=−105−i. They are distinct, so every noninjective block
map fails `QuittingResponseInvariantOnUnitCube` on the block-constant
unit cube. The definition and residual formula were checked in
`UniformEquilibrium/Quitting/Stationary/ResponseInvariantQuotient.lean`
and `UniformEquilibrium/Quitting/Stationary/DiscountedDisplacement.lean`.
This also excludes the literal centered paired-response class, which
supplies such response invariance; singleton symmetry alone is not used.

The local four-joint export bounds delta≤1/2 and requires both participant
rewards in each scheduled pair to stay near positive centers≥2. Every
pair in the separating table has a participant reward−1, under every
relabeling. The rectangle and passive-ray raw statements also require a
pair with both participant rewards positive, which is absent. These are
comparisons of the explicit raw statements, not of arbitrary periodic
strategies or every possible qualitative IFT neighborhood. The author's
explicit refusal to infer noncontainment merely from different pair/triple
scales is correct.

Additional narrow observation: the exact singleton-calendar export has
cross-pair participant bounds at most1 under every mate-preserving
relabeling, whereas every cross pair here has one participant reward2.
Thus its fixed-singleton raw statement does not cover this separating
family either. No inference about every unquantified local enlargement
of that source is needed or made.

## Additional requested guarded-crossed raw-producer check

The separating family fails even the broader actual POLYNOMIAL lower
face guard for EVERY ordered distinct recipient/partner pair, not only
the finite sufficient rankings. Fix recipient i and candidate partner p.
If p is not its mate, take the sole active outsider to be mate(i), with
hazard1. If p is its mate, take the sole active outsider to be succ(i),
again with hazard1. The recipient and partner hazards are zero. At a
sole-sure outsider j the actual residual is

    H_i=r_i({i,j})−r_i({j}).

It equals−5 in the first case (mate pair participant−1 versus singleton4),
and−1 in the second (directed predecessor participant−1 versus cross
singleton0). Both violate the necessary nonnegative lower sign. The row
is in the literal closed outsider box and is nonzero. Neither the large
triples nor any choice of ceiling height enter this calculation.

Consequently this excludes, under every relabeling:

- `QuittingCrossedSourceGuards`, hence the actual degree producer
  `exists_guardedCrossed_stationaryTerminalNash_uniformPayoff_of_sourceGuards`;
- `QuittingHalfWeakPolynomialGuards`, whose broader lower polynomial
  premise already fails;
- `QuittingCrossedStrictRawUnitGuards`, the strict/weak lower-ranking
  variants and their half-ceiling adapters; and
- `QuittingOneSidedWeakUnitGuards` and
  `QuittingOneSidedWeakUnitRawGuards`, which require the same lower sign
  in the selected owner's row.

The exact inspected definitions and adapters are in
`UniformEquilibrium/Quitting/Stationary/GuardedCrossedResponseGuards.lean`,
`UniformEquilibrium/Quitting/Stationary/GuardedCrossedResponseRawTests.lean`,
`UniformEquilibrium/Quitting/Stationary/GuardedCrossedResponseRawAdapter.lean`,
`UniformEquilibrium/Quitting/Stationary/GuardedCrossedResponseRawProducer.lean`,
`UniformEquilibrium/Quitting/Stationary/GuardedCrossedResponseWeakPolynomialFaces.lean`,
`UniformEquilibrium/Quitting/Stationary/GuardedCrossedResponseHalfCeilingAdapter.lean`
and `UniformEquilibrium/Quitting/Stationary/OneSidedWeakUnitProducer.lean`.
The lower row witness directly excludes the broader source predicate,
so no hidden coefficient sufficiency/necessity reversal is being used.

## Scope of the verdict

The substantive raw producer survives adversarial checking. The requested
boxed-charge row correction is precise and preserves the intended
comparison for all sufficiently large M. No broader global novelty,
stationary-class completeness, arbitrary-table construction, or Lean
verification follows from this bounded review.

## Final corrected-byte incorporation check

Final source SHA256:
`a2833a6705f30171e43c028b52316335a208b7ed69fe67ef431ebdbb1bf065aa`.

PASS for the requested delta. Section6.3 now uses the actual outsider
INSERTION sum on mate pair01, namely2(M−5)>0, and correctly identifies
cross pair02's insertion sum as−12. The added threshold M0≥5 makes its
quantifier explicit without changing the existence proof. Section6.4
faithfully incorporates the all-ordered-pairs negative lower-face rows
checked above, including the broader nonnegative polynomial guards.

The raw producer and complete-response/uniform proof in Sections1–5 are
mathematically unchanged, apart from the harmless stronger M0 threshold;
my existing PASS applies to those claims in these final bytes. The
whole-selection checks in Sections6.1–6.2 are unchanged. This is a bounded
incorporation check, not a third full audit or an independent re-audit of
the additional singleton-calendar and weighted-floor arguments supplied
by the other reviewer in Sections6.5–6.6. No new objection arose in the
requested corrected/restructured delta.
