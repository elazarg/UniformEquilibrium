# Raw endpoint producer: bounded whole-source comparison

Reviewer: CODEX_NASH_BOX. Ordinary independent mathematics, not Lean checked.
Reviewed Section13 at whole-file SHA256
`4033a7d23312c0781f9c7474de09f4ad352e58e57069d9bdf18d128bd4c3fd3b`.
The generic enumeration, ratio lemma and IFT are the other reviewer's
producer scope; this review checks the actual complete-cap consumer and
whether the full raw class is already explained by relevant named sources.

## Verdict and precise scope

Bounded PASS: no consumer objection or applicable whole-class containment
was found. The eight guards do not imply the compared singleton, child,
sure-owner, trap/weight, pair-joining or crossed-guard source hypotheses.
The explicit family below certifies their failure over the WHOLE stated
finite selection sets. This is not an exhaustive theorem about every
conditional verifier, every unnamed mechanism, or every pointwise use of
an existential local radius or scale-thick threshold.

In particular, the det-63 fixture from the separate two-pole notebook was
covered by a selective passive-row lift despite unsafe child Nash
witnesses. That missed-source inference is NOT reused here: the actual
inverse AND outside-weight conjunction is checked for all four deletions.
The determinant-sign convention is also checked directly; the degree is
really +1, not the +1 obtained by incorrectly inserting a support-parity
factor into a local index.

## Claim being compared

The input is an arbitrary finite Fin4 reward table except for the three
passive coordinates

    r1(02)=-beta1*M+e1, r2(13)=-beta2*M+e2, r3(01)=a*M+e3,

with beta1,beta2>0, a>=0, bounded e, and all other57 coordinates fixed.
The eight raw guards are A0>0>B0, A2<0, B2<0, L0<0, L1<0,
F(0)>0>F(1), with exactly the definitions of Section13. No singleton
matrix condition or own-singleton sign restriction is supplied. For all
sufficiently large M, the produced hazards have scale

    q=(x,t*y,c',1-t*z), t=1/M,

with x,c' interior and y,z positive. Thus this is an actual macroscopic
stationary producer, not a claim that every table has a diffuse root.

## Exact admissible family

For any M>0 and a>=0 take the singleton rows

    r(0)=(10,9,8,13), r(1)=(12,10,17,7),
    r(2)=(4,14,10,17), r(3)=(7,14,4,10).

The pair rows are

    r(01)=(-1,40,1,a*M), r(12)=(1,-1,40,1),
    r(23)=(1,1,-1,40), r(03)=(40,1,1,-1),
    r(02)=(-1,-M,-1,1), r(13)=(1,-1,-M,-1).

Every triple gives -1 to its participants and1 to its outsider. The grand
row is(-10,-11,-12,-13). Independent exact substitution gives

    A0=33, B0=-2, c=33/35, A2=-5, B2=-2,
    L0=-96/35, L1=-80/7,
    F(x)=(4917-5025*x-550*x^2)/245,
    F(0)=4917/245>0, F(1)=-94/35<0.

Thus this ENTIRE ray for each fixed a is an admissible subfamily, not a
numerical stationary solution offered in lieu of the producer. All the
following tests hold for every M>0 and a>=0 unless explicitly restricted.

## Singleton matrix, degree, all selective children and quotients

Direct reconstruction gives

    Gamma=[0,2,-6,-3; -1,0,4,4; -2,7,0,-6; 3,-3,7,0],
    det Gamma=265,
    Gamma^-1=(1/265)*[268,171,-20,132;
                       170,150,15,60;
                       -42,-9,15,7;
                       109,118,-20,26].

The six two-dimensional principal determinants, in lexicographic support
order, are(2,-12,9,-28,12,42); the four triple determinants are
(26,15,150,268). All are nonzero. Every singleton column has a negative
off-diagonal entry. An R0 solution with at least two positive coordinates
would be annihilated by an invertible active principal block; an axis
solution fails the nonnegative-residual test. Hence Gamma is R0.

Exact enumeration at offset ones gives precisely the roots

    support empty: z=0, residual=(1,1,1,1), index+1;
    support02: z=(1/2,0,1/6,0), residual=(0,7/6,0,11/3), index-1;
    support012: z=(31/13,7/13,9/26,0), residual=(0,0,0,233/26), index+1.

All are strictly complementary. The local index is the sign of the ACTIVE
PRINCIPAL DETERMINANT, by
`IsStandardLCPSolution.exists_box_localDegree_eq_sign_det` in
`MathUE/LinearProgramming/LocalDegree.lean`; the complete sum is given by
`exists_finset_r0Degree_eq_sum_sign_det` in
`MathUE/LinearProgramming/R0DegreeSum.lean`. Thus the actual degree is1.
The degree-not-one UE exit in
`UniformEquilibrium/Quitting/Classification/LCP/SingletonDegreeCriterion.lean`
does not apply. Each row has a distinct negative blocker, so the actual
`normalLayer` recursion in `Classification/LCP/NormalCore.lean` retains
all4. Nonzero degree makes this full core standard-Q by
`isStandardQ_of_r0Degree_ne_zero` in
`MathUE/LinearProgramming/R0Degree.lean`. R0 excludes the homogeneous
simplex branch, and the ordinary non-Q core exit is unavailable. The03
principal block is[0,-3;3,0], which fails Q at offset(-1,-1).

For the ACTUAL raw passive-row producer, deleting0 has inverse entry
-6/67, deleting1 has inverse entry-7/50, and deleting3 has inverse
entry-14/13. Deleting2 has entrywise positive inverse, but its actual
outside row times that inverse is(14/5,3/5,-7/15). Hence every choice
fails the conjunction in
`PassiveRowInverseCriterion.exists_uniformEquilibriumPayoff_of_raw_nonnegativeInverse_triple`
in `Classification/LCP/ThreeCore/RawPassiveRowInverseCriterion.lean`.
This declaration was reopened; it has no collision restriction that could
substitute for one of these failed singleton tests.

The all-sure actual Quit-minus-Continue residuals are
(-11,-12,-13,-14), pairwise distinct. Under
`QuittingResponseInvariantOnUnitCube`, players in a common block must have
equal responses at this block-constant point. Thus no noninjective raw
response quotient exists. The actual criterion in
`Diagnostics/Quitting/FinFourResponseQuotientCriterion.lean` requires the
response invariance, a NEGATIVE determinant and nonnegative inverse; it
is not a theorem based on superficial table symmetry.

For `SignedFourCycleSingletonData` in
`Quitting/Cycles/SignedFourCycleRewardAdapter.lean`, all six cyclic orders
starting with0 fail successor negativity or predecessor positivity.
Witnesses for0123,0132,0213,0231,0312,0321 are respectively successor0,
successor0, predecessor0, predecessor2, predecessor0, successor3.
Multiple positive entries in rows1 and3 exclude the weak matching pattern.
No singleton column is negative at all its other recipients, excluding
the literal negative-pivot cyclic-child pattern. These are whole labeling
tests, not failure of one chosen ordering.

## All sure-owner and persistent-base selections

Suppose ANY player i quits surely at a root, with ANY continuation vector
and arbitrary independent mixing by the other three. Its opposite player
i+2 gets at most-1 whenever joining and at least0 whenever continuing.
Neither selected negative passive pole can enter this comparison: its
opponent coalition contains i. The additional positive pole a*M can only
raise a Continue payoff. Thus i+2 strictly Continues.

Both negative opposite-pair coalitions are now impossible. The remaining
nonsuccessor i-1 also strictly Continues: all its joining rewards are
negative and all its reachable passive rewards are nonnegative. The
successor i+1 strictly Joins for40 rather than its passive singleton,
which is at most17. Owner i consequently gets-1 and improves by
withdrawing to its passive singleton at i+1, which is at least4.
This contradicts root Nash. The all-Continue annotation never enters
these comparisons because the owner is sure.

This excludes the ENTIRE accepted induced-Nash/free-set correspondence
of every nonempty persistent base, including partial or empty free sets,
not just pure witnesses. The actual adapter
`exists_uniformPayoff_of_persistentBase_inducedNash_signs` in
`Diagnostics/Quitting/Collision/Toggles/PersistentBaseNashSemanticAdapter.lean`
combines induced free Nash with the base-leave and quiet-outsider signs
to make precisely such a full sure root.

## Whole quiet-child and withdrawal selections

For every nonempty proper child C choose d in C with d+1 outside C.
Only d Quits0; all other child clocks Never. This is exact full child
Nash: d receives10 rather than Never0; another member receives a passive
singleton at least4, while joining pays-1. Later deadlines cannot change
the already absorbed singleton. All child debts and child joint-Never
mass are zero. Outside successor d+1 gains at least40-17=23 by joining.
Thus a universal bound of ALL outsider debts by child debts plus finite
Never-slack fails for every proper child. For a one-player deletion this
is the particular omitted player's own obstruction.

The F/J-only certificates can also be tested literally, without an N row.
In `WithdrawalFutureJoinRewardCertificate.join_row`, at A={d}, each
nonowner child advancing coefficient is -1-r_i(d)<=-5; the owner's is0.
Nonmembers have withdrawal coefficient0. The owner's withdrawal floor
minus10 is nonpositive for ALL five kinds: patient floor<=max(10,0),
deadline/cancellation floor<=0, evaluated-security floor<=0, and terminal
security floor<=10. Hence every nonnegative-weight right side is
nonpositive, against the successor's strictly positive left side.

These facts use the actual `WithdrawalFutureJoinKind.gain` and
`WithdrawalFutureJoinRewardCertificate.join_row` in
`Classification/QuietExtension/WithdrawalFutureJoinRaw.lean`, with
`patientWithdrawalFloor_le_ownNeverAlternative`,
`deadlineWithdrawalZeroFloor_le_zero`,
`deadlineSecurityGainFloor_singleton`,
`deadlineSecurityGainFloor_singletonWithRestart`, and
`deadlineWithdrawalSecurityValue_le_singleton` in the respective
`PatientWithdrawalRaw.lean`, `DeadlineWithdrawalRaw.lean`,
`DeadlineWithdrawalSecurityMixedPointwise.lean`,
`DeadlineWithdrawalRestartPointwiseCore.lean` and
`DeadlineWithdrawalSecurityLP.lean` files in that same directory.

## Entire weight, trap, pair and crossed-guard choices

The only premium trap is all4: each player's only above-own participant
row is its incoming40 pair, so a trap must contain every predecessor.
For arbitrary w>=0, w!=0, independent exact sums give

    sum_d sum_i w_i[r_i({d,i})-s_i]=8*sum_i w_i>0,
    sum_d sum_(i!=d)w_i[r_i({d,i})-r_i(d)]
                                 =15*w0+w1+9*w2+w3>0.

Thus ALL upper-average weights and ALL nonnegative weighted
leave-nonpositive selections fail, including zero-weight coordinates.
The unweighted singleton leave sums are(8,2,3,13), contradicting the
required singleton boxed-charge signs BEFORE their quantitative threshold.
This is the literal `QuittingTrapChargeCoefficients.leave_nonpos` in
`Classification/BoxedQuittingNashCharges.lean`, not a sum of participant
premiums confused with a sum of outsider insertions.

At background012 the global forced-Quit premium vector is
(-11,-11,-11,-23), excluding every nonzero nonnegative global floor
weighting. These exact tests cover the full selections in
`MIXED_SUPPORT_UPPER_OR_CHARGE_UNIFORM_EQUILIBRIUM.md`,
`BOXED_NASH_CHARGES_UNIFORM_EQUILIBRIUM.md`,
`MIXED_PREMIUM_TRAPS_UNIFORM_EQUILIBRIUM.md` and
`WEIGHTED_FLOOR_RETURN_UNIFORM_EQUILIBRIUM.md`.

Every player has an incoming40 participant premium and an outgoing-1
deficit. Hence neither participant-at-most-own protection nor
participant-at-least-own common/support-specific protection is available.
The greatest premium core has size4, not2 or3. Every pair has a participant
whose joining reward-1 is below its passive singleton, so EVERY partition
fails the scheduled-pair join condition of
`TWO_PAIR_JOIN_CAP_UNIFORM_EQUILIBRIUM.md`. Every triple contains such a
negative ordered joining gap, defeating the six-positive-join condition of
`TRIPLE_SINGLETON_COLLISION_BOX_UNIFORM_EQUILIBRIUM.md` over ALL triples.

For ANY selected owner i and partner p, choose j in{i+1,i+2} distinct
from p. At the sole-sure outsider j, with the partner hazard zero, the
owner's actual residual is -1-r_i(j)<=-5. Thus even the weak lower guard
fails over every pair/height, using the actual definitions
`QuittingCrossedSourceGuards` in `Stationary/GuardedCrossedResponseGuards.lean`
and `QuittingOneSidedWeakUnitGuards` in
`Stationary/OneSidedWeakUnitProducer.lean`.

## Jackpot architecture comparison and nonclaims

The carrying directions of the two negative passive poles are +e1,+e2.
Both inverse images have mixed signs. The carrying direction of the
positive passive pole is -e3, whose inverse image is strictly negative.
None is a positive carrying direction. Therefore the literal hypotheses
of the one-signed-column and selected-signed-column-cone producers fail
at EVERY growing coordinate. The full signed-inverse criterion fails
because columns1 and2 are mixed. The positive-inverse coalition jackpot
export fails both its inverse and its participatory-pole requirements.
These are tests of complete raw hypotheses, not an objection to their
producer mathematics.

The exact paired-singleton calendar/rectangle/ray sources do not have
these singleton identities, even under positive row rescaling and terminal
row translation: their two equal negative off-diagonal entries in every
row are absent here. The explicit four-joint local box has delta<=1/2
and own levels near1, whereas these own levels are10. No exclusion of
an unspecified larger local radius is inferred. The scalar singular
circuit's strict Section5 constant guards also fail over all relabelings.
Its two solo favorite inequalities force three consecutive vertices
label0 -> label3 -> label1 along the ONLY above-own participant cycle;
its A2>0 condition forces label2 to be the next successor of label1.
The additional singleton inequalities require negative incoming Gamma
entries at ALL three receivers label3,label1,label2. In this family the
incoming Gamma entries at receivers0,1,2,3 are(-3,-1,7,7): only TWO are
negative. Thus no three consecutive receivers can supply those guards.
This uses the source's actual asymmetric pair ladder, not a fictitious
both-above-own pair condition.

For a>=1/4, the all-small leading scale q=M^-1*w, w>0, is impossible
by the exact equation(32): its left bracket is negative while its right
side is positive. This is a useful scale discriminator, NOT nonexistence
of stationary Nash and NOT exclusion of unknown pointwise thick bounds.
The macroscopic branch is expressly allowed and is the new construction.

The full57-coordinate endpoint class is not being replaced by a local
center theorem. All its singleton data can vary; the center merely
certifies failure of the compared WHOLE selections. Fixed terminal row
translations preserve all eight guards (in F the added constant cancels
between its two terms), so raw bounded-coordinate local boxes cannot
explain the whole endpoint class just by containing this one center.
This does not license an unrestricted affine-equivalence claim at Never.

## Actual complete-cap and uniform consumer

At every produced finite M all four q_i lie in(0,1), so each player's
opponents have stationary survival alpha_i<1. Let Q_i be its Quit payoff
and B_i its nonempty-opponent absorption reward. The exact equation
H_i=(1-alpha_i)Q_i-B_i=0 makes the actual policy value equal Q_i.
Every deadline h earns

    B_i*(1-alpha_i^h)/(1-alpha_i)+alpha_i^h*Q_i=Q_i,

and Never earns B_i/(1-alpha_i)=Q_i. Independent mixtures of these
complete stopping clocks exhaust all unilateral behavioral replacements
on the unique live history. Thus FULL terminal Nash follows, including
off-policy and arbitrarily late deviations, with no sign hypothesis.

For each FIXED table the geometric first-opponent stopping time has finite
expectation uniformly over the replacing player's strategy. The expected
finite-horizon average/terminal discrepancy is bounded by that expectation
times the finite reward bound divided by horizon. Therefore the SAME
profile delivers its actual fixed payoff as a UE target. M and the table
are fixed before accuracy; no M-uniform horizon estimate is claimed.

Current remaining admission boundary: this bounded review establishes
noncontainment in the explicitly compared raw predicates, not a census
of all possible conditional policy verifiers or unquantified pointwise
neighborhoods. No further producer interface is required for its own
full-response conclusion.
