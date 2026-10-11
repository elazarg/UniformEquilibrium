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
