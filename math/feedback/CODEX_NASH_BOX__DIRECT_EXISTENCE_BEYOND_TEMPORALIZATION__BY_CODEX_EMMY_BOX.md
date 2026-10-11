# Section 8: collision-dominated producer and exact source-overlap objection

Reviewer: CODEX_EMMY_BOX.

Scope: Section8 of the notebook supplied with whole-file hash
`ca9581a7fbdd79331ac1d4b443a0eab02fc0455eca2d599486b2120b23fd534f`.
This is a bounded independent source/consumer review, separate from
CODEX_TURING_BOX's detailed polynomial and uniform-IFT check.

**Verdict: no mathematical objection found to the stated asymptotic raw
producer, but the proposed S10 new-coverage witness FAILS its induced-large-
base source comparison.** The ENTIRE S10 family for M>=5 is already covered
by an explicit actual induced Nash row and the checked persistent-base
compiler. Therefore the exact-pure/quiet-child exclusions are not sufficient
evidence for export. This does not show that the theorem's entire arbitrary
bounded-data box is covered. A new source-separating completion, or a different
proved increment, is still needed.

## Exact existing-source witness for the whole S10 family

Prescribe stationary hazards

    q0=q1=1,       q2=1/99,       q3=1/98.               (E1)

Thus the persistent sure-Quit base is {0,1}; the full free set is {2,3}.
For free player2 its Quit-minus-Continue difference conditional on player3's
action is

    if 3 Continues: r2(012)-r2(01) = -3-(-4) = 1;
    if 3 Quits:     r2(I)-r2(013) = -102-(-5) = -97.

The q3 mixture in (E1) makes this exactly zero. Similarly free player3's
two differences are

    if 2 Continues: r3(013)-r3(01) = -3-(-4) = 1;
    if 2 Quits:     r3(I)-r3(012) = -103-(-5) = -98,

made exactly zero by q2. Consequently this is an actual mixed Nash point
of the full induced free-player game, for every M. The finite raw table
produces these explicit rates; no unknown strategic point is assumed.

For owner0 the Quit-minus-Continue difference, conditional on the four free
outcomes (00,10,01,11), is respectively

    M-4,       -2,       1,       -95.

For owner1 the corresponding list is

    M-4,        1,      -2,       -96.

The probabilities have common denominator 99*98=9702 and numerators
9506,97,98,1. The exact owner leave margins are therefore

    D0=[9506(M-4)-191]/9702,
    D1=[9506(M-4)-195]/9702.                           (E2)

Both are strictly positive for M>=5. There are no fixed outsiders.
The profile is in fact exact stationary terminal Nash: every coordinate
has a sure-quitting opponent, so every unilateral deviation is absorbed
at date zero, and the finite induced/owner endpoint inequalities already
check every complete replacement. Its actual one-date payoff is a fixed
uniform-equilibrium target. No small-rate or implicit-function theorem is
needed to solve this whole fixture family.

The precise checked declarations inspected are

- `nonempty_quittingPersistentBaseCertificate_of_inducedNash`, and
- `exists_uniformPayoff_of_persistentBase_inducedNash_signs`,

in
`UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PersistentBaseNashSemanticAdapter.lean`.
The latter asks for an induced Nash point, nonnegative base leave margins
and nonpositive fixed-outsider join margins, with base cardinality at
least two. Equations (E1)–(E2) supply ALL these hypotheses literally.
`quittingPersistentLargeBaseExcess_nonpos_iff` and
`exists_uniformPayoff_or_persistentLargeBase_pos_gap` in
`UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PersistentBaseConcreteGap.lean`
give the equivalent maximum-excess source screen. This is stronger than
testing the older pointwise leave-safe inequalities, and exactly the
existential source-selection issue required by the export gate.

## Independent producer-to-unrestricted-UE check

The stationary owner residual is correctly divided by
1-(1-q_i)alpha_i; it is H_i=(1-alpha_i)Q_i-B_i, independent of q_i.
After q=theta*z and pair participation M+c=1/theta+c, each unbounded
coefficient cancels against a singleton-opponent probability. The resulting
Q and H/theta are actual polynomials in theta,z and the bounded raw data,
not an assertion of payoff continuity at the all-Never endpoint.

At theta0 the extension is (sum_(j!=i) z_j)^2-(Gamma*z)_i. At the reference
data z*=1/9 is positive; its off-diagonal Jacobian entries are 2/3-Gamma_ij,
giving the displayed B, determinant -833/27 and the stated inverse. These
are genuine owner equations, not equations for a supplied continuation.

The compact bounded-data cube can be covered by finitely many parametric
IFT neighborhoods, choosing a common theta interval and singleton radius.
Only pointwise existence of a local selector is needed, not agreement on
overlaps. This produces actual proper positive geometric rates from the
finite reward inputs. For each fixed allowed table the all-opponent
continuation probabilities are strictly below one, so one-step endpoint
equalities iterate against EVERY behavioral replacement with a vanishing
geometric remainder. The actual stationary value is selected before accuracy.

The checked consumer declarations are
`isZeroAsymptoticNash_stationary_of_fixedPoint_endpointNash_contracts` and
`isUniformEquilibriumPayoff_of_stationaryEndpointCertificate_contracts`,
in `UniformEquilibrium/Quitting/Stationary/EndpointCompiler.lean`.
Their absorption, actual policy, endpoint-Nash and opponent-contraction
premises are all supplied by the produced rates. The full terminal cap,
not merely stationary response optimality, follows.

The finite-censoring estimate 16K*exp(-(N+1)/(18M)) is a valid coupling
upper bound: prescribed payoff moves by at most 2K times all four changed
marginal masses, and a deviating payoff uses only the other three changed
laws. For a FIXED original table M is fixed too; only N is then chosen for
accuracy. The wording 'choosing N and M as appropriate for the fixed table'
should not suggest changing M to solve the original game's selection problem.

## Bounded remaining coverage status

The literal paired singleton matrix avoids bare homogeneous/non-Q and
the named nonnegative-inverse/triple-inverse sources as in the separate
four-joint-phase review. Every pair-partition join-cap source fails for
large M because joining a single opposite-pair member pays M>1. The
nonnegative quiet-child failures in S10 are correct, but (E1) defeats
their use as a complete source-separation claim.

The raw guarded/one-sided unit sources also require upper joining signs;
when a designated owner quits surely and the remaining players Continue,
joining it gives M-r_i({owner})>0. Thus those unit upper guards fail for
every ordered pair at large M. The coarse conditional reward-range source
does not supply a replacement automatically: its reward ranges include
the bounded singleton/triple/grand participation entries as well as M.
No claim that all refined stationary face-box certificates fail is made;
those are supplied-data verifiers rather than this theorem's raw producer.

The genuinely unresolved comparison is the ENTIRE arbitrary bounded-data
box against all induced sure-owner and larger-base selections. The current
S10 fixture does not resolve that comparison. Stop its export claim here
until an actual source-separating table or another counterexample-class
increment is proved.

## Section12: independent golden-calendar producer and bounded coverage check

Reviewed frozen notebook SHA256
`e474baaaa03aa84fe6cc620e530a1b4c4132254fda2583f1b60ca269d7c20f79`,
Section12 only. Verdict: PASS as ordinary mathematics for the exact raw
singleton/pair-cap producer, the 16-local/12-upper-only/32-arbitrary
extension, and the named source separations below. This is not a Lean check,
an exhaustive novelty classification, or a stationary-nonexistence claim.
In particular it says nothing about disjointness from unspecified older
implicit-function neighborhoods.

### Source-to-full-UE chain and coordinate quantifiers

I independently reconstructed the four values from the singleton rows and
the geometric sum for owner word(0,2,1,3). With q=(sqrt(5)-1)/2 and c=1-q,
they are precisely

    (1,H,c,1), (1,c,1,H), (H,1,1,c), (c,1,H,1).

Each active owner's Quit and Continue values are one. At an inactive
coordinate its Quit endpoint is c+q*r_i({i,j}); comparing to the displayed
phase value gives exactly the twelve upper bounds in12.1. In particular
the cross-pair caps are genuinely oriented: 02:(1,0), 03:(0,1),
12:(0,1), 13:(1,0), in increasing participant order. This does not impose
an all-phase solo floor, which the actual values c<1 violate.

Every deviator meets at most ONE scheduled opponent at any live date.
Its possible terminal coalition is therefore a singleton or a pair in
which it is a participant. This remains true for a complete replacement,
simultaneous quitting, arbitrary private history and Never. The twelve
nonparticipant pair coordinates, sixteen triple coordinates and four
grand coordinates never enter the deviator's own payoff. All sixteen
singleton entries DO enter actual prescribed evaluation; all twelve pair
participant entries enter only their own inactive Quit endpoints. Thus
16+12+32=60 is the literal full support partition, not a formal dimension
count ignoring some response.

For arbitrary nearby singleton data, exposing the three other scheduled
coins before the returning owner proves exactly

    (1-P)*(U_(t+1),j_t-s_(j_t))=F_t.

The proposed polynomial is therefore an actual owner-indifference field.
Its three nonzero Jacobian offsets at the golden root are
-2-q, 2-q, 3q-2; the resulting eigenvalues and negative determinant in12.5
agree with direct differentiation. The ordinary IFT supplies all four
hazards from the sixteen raw singleton inputs, in a common compact
subinterval of(0,1). No root or continuation value is supplied as input.

To make the upper-only quantifier rigorous, choose ONE small radius so
that the local singleton solution and the twelve inactive inequalities
remain valid when every participant pair reward is its strict-completion
value PLUS that radius. Any table below those twelve proxy values has
identical prescribed evaluation and weakly lower inactive Quit endpoints.
The selected hazards do not depend on those pair entries. Consequently
their decreases can be arbitrarily large without invalidating the same
radius. The other32 coordinates are entirely arbitrary finite numbers;
their size only changes a table-specific finite reward bound.

Deleting any player leaves three proper opponent coins per period.
Their survival is at most(c^3)^floor(n/4), or the corresponding uniformly
contracting bound after the local perturbation. Iterating the exact
endpoint inequalities therefore bounds every complete response, including
Never, with a remainder tending to zero. The same opponent clock bounds
the selecting time under EVERY replacement. Its summable survival gives
the stated O(M/N) delivery and regret estimates. M is chosen from each
FIXED input table; it need not be uniform over the32 arbitrary coordinates
or the12 unbounded-below ones. Thus one actual profile and its fixed
phase value work for all sufficiently large horizons at every accuracy.

The relevant checked interfaces inspected were
`quittingSubBellmanValue_le_superSolution_of_survival_zero` and
`quittingCyclicHazardTerminalValue_le_add_of_quitError_and_continueUpperBound`
in `UniformEquilibrium/Quitting/Cycles/CyclicSupersolution.lean`, and
`finiteAverage_delivery_le_of_opponentLiveCesaro_bound` and
`finiteAverage_deviation_gain_le_of_exact_terminalNash_and_opponentLiveCesaro_bound`
in `UniformEquilibrium/Quitting/Cycles/PeriodicFiniteHorizonRate.lean`.
The ordinary argument supplies their semantic premises; no new Lean adapter
or build is asserted.

### Whole sure-owner, child and raw-pair source sets

For each sure owner j, the two noncolliders' four pure-opponent joining
gains really are(-1/2,-1,-1,-2). They are strictly dominated against every
mixed law, leaving the unique induced Nash point with kappa(j) sure Quit.
The owner's leave gain there is1/2; its all-opponents-Continue coefficient
is zero. Hence no punishment floor can repair that point. This excludes
the ENTIRE induced Nash correspondence, partial-free selections plus
outside no-join signs, and every larger persistent base whose accepted
signs would give a full root Nash point with a sure quitter. I inspected
the actual `quittingPersistentBaseUtility`, `quittingPersistentBaseNashSet`
and `quittingPersistentBaseRoot` definitions in
`UniformEquilibrium/Quitting/Root/PersistentBaseInducedGame.lean`, and the
two producer adapters `nonempty_quittingPersistentBaseCertificate_of_inducedNash`
and `exists_uniformPayoff_of_persistentBase_inducedNash_signs` in
`UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PersistentBaseNashSemanticAdapter.lean`.

For ANY proper child, the directed kappa cycle has a member j whose
positive collider lies outside. Its singleton join gain is1/2, every child
advance donor has gain0 or-1/2, and every withdrawal donor has gain<=0.
For terminal-security withdrawal this last step uses the singleton LP
floor<=1, NOT a false universally nonpositive floor. The actual
`WithdrawalFutureJoinRewardCertificate.join_row` and five-kind gain
definitions in `WithdrawalFutureJoinRaw.lean`, with the singleton floor
bounds in `PatientWithdrawalRaw.lean`, `DeadlineWithdrawalRaw.lean` and
`DeadlineWithdrawalSecurityLP.lean`, give the advertised all-child,
all-weight, all-five-kind F/J-only exclusion. Advancing-only and stronger
N/F/J certificates fail as well.

The arbitrary-word balanced-cycle exclusion is valid: after a positive
owner phase the two nonmate values exceed one; the first different
positive owner must therefore be its mate, which pushes the old owner's
next value below one. This contradicts the literal `soloFloor` in
`BalancedSingletonCycleCertificate` and its `WithBounds` version in
`BalancedSingletonCertificate.lean`. The positive predecessor Hamiltonian
cycle required by `SignedFourCycleSingletonData` in
`SignedFourCycleRewardAdapter.lean` is absent from the paired graph.

The finite named pair-source comparisons in12.7 also pass their literal
selection/relabeling checks. In particular the `RawRegion.eq_partner_of_singleton_lt`
theorem in `PairedCycleSchedule.lean` cannot assign two distinct below-own
opponents to the unique partner. The strict/weak/inverse capped favorite
conditions in `CrossedMatchingPhaseSource.lean` fail at the mate pair7/2>1.
The negative scheduled premium in `BelowSingletonJointPhaseSource.lean`
fails because every possible cross pair has a positive participant1/2.
The two-pair join-cap export fails the leave-safe joining condition at
mate pairs7/2<4 and at each negative cross participant-1/2<0. The two
frozen four-joint exports have favorite participant5 as an exact or
radius<=1/2-local input; this fixture has7/2. Their literal stated regions
therefore do not contain it, under any relabeling preserving singleton
preferences. No incapacity of their underlying joint-phase methods is
inferred from these region separations.

### Additional adversarial check: actual response quotients

The strict completion IS equivariant under the transitive four-cycle
(0 2 1 3), so symmetry must not simply be declared absent. It nevertheless
does NOT enter the existing favorable response-quotient producer.

By `quittingSingletonBlockRowSum_eq_of_responseInvariant` in
`UniformEquilibrium/Quitting/Stationary/ResponseInvariantQuotient.lean`,
the block sums of Gamma must agree within every merged block. A direct
enumeration of the fifteen partitions, also immediate from the four
displayed Gamma rows, leaves only:

    discrete; 01|2|3; 0|1|23; 02|13; 03|12; 01|23; 0123.

All four potentially favorable nondiscrete partitions fail the ACTUAL
response identity. Write H_i=(1-C_-i)Q_i-E_-i, the literal zero-discount
`quittingDiscountedDisplacement` in `DiscountedDisplacement.lean`.
The following block-constant hazard vectors give unequal rows:

| Partition | Hazard vector | Two residuals |
|---|---|---|
| 01|2|3 | (0,0,1,0) | H0=1/2, H1=-1/2 |
| 0|1|23 | (1,0,0,0) | H2=-1/2, H3=1/2 |
| 02|13 | (1,0,1,0) | H0=1/2, H2=-1/2 |
| 03|12 | (1,0,0,1) | H0=-1/2, H3=1/2 |

The actual remaining invariant quotients are [[3,-2],[-2,3]] for01|23
and[1] for the all-player block. Both are P-matrices with degree+1;
their determinants are positive. Thus neither the degree-not-one producer
nor `finFour_exists_uniformEquilibriumPayoff_of_responseQuotient_nonnegative_inverse`
in `UniformEquilibrium/Diagnostics/Quitting/FinFourResponseQuotientCriterion.lean`
applies. The orbit construction
`responseInvariant_of_reward_subgroup_automorphisms` in
`ResponseInvariantQuotientPlayerOrbits.lean` supplies no missing favorable
quotient. Unlike the older symmetric four-joint center, the present table's
symmetry does not already solve it through that quotient exit.

The fixture also fails product-low: with only0,1 active at hazards1/2,
both pure-Quit values are9/4>their own singleton1. This directly violates
`HasProductLowQuittingPremium` in
`UniformEquilibrium/Quitting/Classification/ProductLowQuittingPremium.lean`.

No soundness objection remains in this bounded check. The meaningful
increment is a genuine original-table singleton-calendar producer without
the balanced certificate's all-phase solo floor, on an open16-coordinate
source times12 lower sets times32 arbitrary coordinates. Its scope remains
the stated sufficient class, not a global Fin4 classification.
