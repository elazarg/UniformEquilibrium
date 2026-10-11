# Independent bounded check of the sparse triple producer

Reviewer: CODEX_NASH_BOX.

Reviewed source: `notes/CODEX_EMMY_BOX__SPARSE_TRIPLE_COLLISION_PRODUCER.md`,
SHA256 `0b627024dbad80d303ea1f48eb873d3087f81cb599321135120918732d7d2c85`.
Scope: Sections 1--5 soundness and the explicit Section 6 family's named
source comparisons. Ordinary mathematical review, not Lean checking and
not an exhaustive survey of arbitrary supplied-object verifiers.

Verdict: no objection to the raw producer or full-response consumer.
Section 6.3 contains one incorrect boxed-charge calculation. The claimed
exclusion survives the exact repair below. The four-singleton source also
fails on this family, including its existential-radius strengthening;
that comparison should be stated explicitly rather than inferred from
the triple scale alone.

## 1. Raw construction and complete unilateral agency

For recipient i the only unbounded reward in Q_i is at opponent coalition
C_i, and its mass is exactly

    t^2 z_j z_k (1-t z_mate(i)).

Multiplication by M=t^(-2) cancels the pole. Its bounded residual c_i
contributes t^2 z_j z_k(1-t z_mate(i))c_i. No unbounded coordinate occurs
in B_i: i's unique jackpot coalition contains i, whereas B_i samples only
coalitions excluding i. Other recipients' jackpots do not make i's
coordinate unbounded. Thus H_i/t really has a polynomial extension and

    Phi_i(0,z)=sum_(l!=i) z_l * z_j z_k - (Gamma z)_i.

Independently differentiating gives zero diagonal, mate entry -8/3 and
cross entries 7/3. The eigenvalues are 2, -22/3, 8/3, 8/3, and the
determinant is -2816/27. Exact symbolic arithmetic reproduces these
identities. No numeric root is used.

The compact-parameter IFT argument is valid. At every bounded-data point
the limiting root and derivative are identical; a finite cover yields
one positive t-interval and singleton neighborhood for the entire closed
44-coordinate cube. Overlap compatibility of local selectors is not
required for existence. The stated positive z-box keeps all four hazards
strictly between zero and one after shrinking t. For each fixed original
table, M is fixed before accuracy or horizon varies.

The identity

    Q_i-(B_i+alpha_i U_i)
      = ((1-alpha_i)Q_i-B_i)/(1-(1-q_i)alpha_i)

is exact. At its common zero both pure endpoints equal the ACTUAL
stationary policy value. Every deleted-opponent system contracts because
all hazards are positive. Iterating the bounded Bellman equality/inequality
therefore covers every complete behavioral replacement, including Never.
The same geometric opponent bound gives uniform finite-horizon convergence
to the one fixed actual payoff vector. Large but finite jackpot and grand
entries affect the bound, not the conclusion.

The exact inspected tracked consumers are
`isZeroAsymptoticNash_stationary_of_fixedPoint_endpointNash_contracts` and
`isUniformEquilibriumPayoff_of_stationaryEndpointCertificate_contracts` in
`UniformEquilibrium/Quitting/Stationary/EndpointCompiler.lean`. Their
fixed-point, endpoint and playerwise contraction hypotheses are supplied
by the calculation. The new raw IFT producer is ordinary mathematics.

## 2. Whole sure-owner and proper-child comparisons

The sure-owner argument is exhaustive, including mixed opponents and
arbitrary continuation annotations. With owner 0 sure, mate 1 has joining
reward at most -1 and Continue reward at least 4. Once 1 Continues,
predecessor 3 has joining reward -1 and nonnegative Continue reward.
Then successor 2 strictly joins for 2 rather than 0. Owner 0 withdraws
for 0 instead of -1. No continuation event survives any comparison in
which it is needed. The directed-cycle rotations preserve these strict
comparisons despite the asymmetric negative grand entries. Hence there
is no exact root with ANY sure coordinate. This covers the whole nonempty
persistent-base/free selection, not merely pure free-player completions.

For every nonempty proper child, a vertex d whose successor lies outside
exists because successor is one four-cycle. The pure-d child profile is
exact against all complete child replacements: the other surviving
players' pair joining rewards are -1, while their prescribed singleton
rewards are 0 or 4. The omitted successor's original joining gain is 2,
all child debts vanish, and child joint Never mass is zero. This contradicts
every claimed outsider-debt bound by weighted child debts plus finite
Never slack. The actual inspected certificate
`WithdrawalFutureJoinRewardCertificate` in
`UniformEquilibrium/Quitting/Classification/QuietExtension/WithdrawalFutureJoinRaw.lean`
has nonnegative advance and withdrawal weights and all five operation
kinds. The contradiction is exactly the consumer pattern used by
`exists_outside_no_quiet_certificate` in
`UniformEquilibrium/Quitting/Examples/NegativePremiumCyclicChildFixtureChildren.lean`.
This does not exclude joint original-game strategies or selected-child
methods outside that certificate family.

## 3. Required boxed-charge correction

In the inspected definition `quittingWeightedLeaveSum` in
`UniformEquilibrium/Quitting/Classification/WeightedQuittingTrapLeavers.lean`,
the sum is over players OUTSIDE the tested coalition, and each term is
the reward from INSERTING that outside player minus its passive reward.
It is not the sum of the coalition's participants' withdrawal gaps.

Consequently the tested cross pair {0,2} has actual unit-weight leave sum

    [r_1(012)-r_1(02)] + [r_3(023)-r_3(02)]
      = (-1-5)+(-1-5) = -12,

not +1. Replace that test by the mate pair {0,1}:

    [r_2(012)-r_2(01)] + [r_3(013)-r_3(01)]
      = (M-5)+(M-5) = 2(M-5)>0  when M>5.

The entire player set IS an actual premium trap: each player has its
predecessor pair with own reward 2>1. Thus the corrected proper-pair test
contradicts `QuittingTrapChargeCoefficients.leave_nonpos` in
`UniformEquilibrium/Quitting/Classification/BoxedQuittingNashCharges.lean`.
By the literal universal-trap quantifier in `HasBoxedQuittingNashCharges`
in `UniformEquilibrium/Quitting/Classification/BoxedQuittingNashChargeReturn.lean`,
the raw boxed-charge producer cannot apply for M>5. Increasing the
producer's qualitative M0 to at least 5 is harmless.

## 4. Other bounded raw-source comparisons

At the all-sure point the exact raw displacement from
`quittingDiscountedDisplacement` in
`UniformEquilibrium/Quitting/Stationary/DiscountedDisplacement.lean` is

    H_i = r_i(I)-r_i(I minus i) = -105-i.

These four numbers are distinct. This point is block-constant for EVERY
partition, so the literal equality required by
`QuittingResponseInvariantOnUnitCube` in
`UniformEquilibrium/Quitting/Stationary/ResponseInvariantQuotient.lean`
fails for every noninjective block map. No inference from asymmetry alone
is being made.

The reference singleton matrix is exactly the same paired hard matrix
as in the four-singleton export, not a newly favorable singleton matrix.
Every prescribed pair in `FOUR_JOINT_PHASE_UNIFORM_EQUILIBRIUM.md` has
both participant center coordinates at least 2, and its radius is at most
1/2. Every actual fixture pair has a participant -1. This excludes that
raw P-coordinate premise under EVERY relabeling, independently of any
triple or grand entry. The rectangle and passive-ray named sources require
a scheduled/favorite pair with both participants positive, also absent.

There is an additional important comparison with
`FOUR_SINGLETON_PHASE_UNIFORM_EQUILIBRIUM.md`. Its arbitrary-triple freedom
alone does not cover this family. For exact reference singleton rows,
every all-positive solution of its named singleton word's owner equations
is golden: in chronological Continue variables, opposite differences of

    u_i(4-4u_next+u_next*u_nextnext)-1=0

force u_0=u_2 and u_1=u_3 by the positive two-by-two determinant;
the remaining difference forces all four equal, with
u=(3-sqrt(5))/2. Thus every cross-pair participant bound for that
architecture is at most 1, for either orientation and every relabeling
preserving the singleton mate pattern. The fixture has a cross-pair
participant reward 2 on each directed edge. Hence it cannot have that
named word's full Nash profile. This also excludes the export's Theorem 2
on this exact-singleton family; it does not depend on knowing its
existential IFT radius. It is not an exclusion of all possible calendars.

As further bounded checks, the crossed-matching raw cap (C) cannot hold.
For the true-mate scheduled matching every jackpot violates its recipient's
triple cap M<=1 for M>1. For either cross scheduled matching, the two
recipients whose scheduled partner is their successor have their predecessor
in the other scheduled pair. Their predecessor-pair participant reward 2
violates the corresponding cross cap r_i({i,predecessor})<=s_i=1.
The opposite-sign matching source's paired singleton identities force
H=3, b_i=1, s_i=1. Choosing the true mate as scheduled partner cannot
satisfy its required negative complementary singleton; choosing a cross
matching makes a directed cross cycle's one participant -1 and the other
2 in each scheduled pair, incompatible with its common participant
coefficient within that pair. These checks concern those literal raw
criteria only.

The remaining relevant live raw criteria have the following direct
failures, without a tree-wide survey.

- The six strict pair joins in the triple--singleton collision-box source
  cannot hold for ANY selected triple. Every three-element set contains a
  true mate pair, and each ordered mate joining gap is -1-4=-5.
- The signed inverse-column criterion also fails for EVERY matching.
  The exact inverse of Gamma has rows (2,7,3,3)/15, (7,2,3,3)/15,
  (3,3,2,7)/15, (3,3,7,2)/15. Its strict column signs force every sigma_i
  to be +1. Every selected pair contains a participant with premium
  Pi_i=-2, contradicting the required sigma_i Pi_i>=0.
- The full guarded crossed stationary-response source requires positive
  reciprocal singleton comparisons. This forces the selected pair to
  be true mates. In `QuittingCrossedSourceGuards` in
  `UniformEquilibrium/Quitting/Stationary/GuardedCrossedResponseGuards.lean`,
  take partner rate zero and the pure successor outsider rate one.
  The selected recipient's lower-face displacement is -1-0=-1,
  violating strict lower positivity at EVERY height. The same strictly
  negative witness also fails weak lower-guard variants. Choosing a
  cross partner fails the reciprocal premise instead.
- The protected-leaver class has P_max empty, since every player's grand
  reward is below its own singleton. The greatest premium core is all
  four players, so the size-at-most-two and size-three core classes do
  not apply. A nonzero nonnegative global forced-Quit floor is impossible:
  its grand-coalition test is sum_i w_i(-101-i)>=0.
- The mixed supportwise-upper-or-charge raw class fails on the FULL trap.
  Its boxed-charge arm is excluded in Section 3 above. For its upper-average
  arm, let X=w_0+w_1 and Y=w_2+w_3. Testing the mate pairs 01 and 23
  gives (M-1)Y<=2X and (M-1)X<=2Y. For M>3 these force X=Y=0,
  contradicting its required nonzero weight. This also rules out a
  support-local upper average, not only the global floor condition.

These tests use the literal statements of
`TRIPLE_SINGLETON_COLLISION_BOX_UNIFORM_EQUILIBRIUM.md`,
`SIGNED_INVERSE_COLUMN_UNIFORM_EQUILIBRIUM.md`,
`CROSSED_MATCHING_UNIFORM_EQUILIBRIUM.md`,
`OPPOSITE_SIGN_MATCHING_PHASE_UNIFORM_EQUILIBRIUM.md`,
`SUPPORT_SPECIFIC_LEAVERS_WITH_SIGNED_PREMIUMS.md`,
`MIXED_SUPPORT_UPPER_OR_CHARGE_UNIFORM_EQUILIBRIUM.md`, and
`MIXED_PREMIUM_TRAPS_UNIFORM_EQUILIBRIUM.md`, together with the named
tracked guard and charge definitions. All are direct whole-selection
failures for sufficiently large M, not failed trial selectors.

No whole-quantifier exclusion of the common-large-PAIR IFT class is
inferred from its different scale alone. No claim is made about all
stationary-root, collision-box, or supplied-face verifiers. Such a verifier
can of course consume the root newly produced here without supplying the
raw-data producer proved in this note.

## Final scope

The complete raw theorem survives this adversarial check. Its explicit
family survives the named whole sure-owner, all-proper-child certificate,
literal response-quotient, boxed-charge (after correction), and the named
four-phase/matching raw comparisons above. This is meaningful finite-data
coverage, not an arbitrary-Fin4 theorem or a claim of exhaustive novelty.
