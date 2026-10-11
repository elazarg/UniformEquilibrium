# Sparse recipient-specific triple rewards produce stationary equilibrium

Status: ordinary mathematical theorem and proof, not Lean-checked.
This is a raw-table existence producer for an unbounded four-player
reward region, not an arbitrary-four-player theorem or a stationary
strategy-class completeness claim.

## 1. Self-contained question and theorem

Let I={0,1,2,3}, m=(0 1)(2 3), and let C_i=I\{i,m(i)} be the two
cross-pair players of recipient i. Put J_i=I\{m(i)}, a triple containing i.
There are FOUR jackpot coordinates, namely

    (023,0), (123,1), (012,2), (013,3).

At each live date every player privately and independently chooses
Continue or Quit. The first nonempty coalition S quits simultaneously
and pays the finite original reward vector r(S); live payoff and Never
are zero. All unilateral replacements are unrestricted behavioral laws,
including arbitrary finite deadlines and Never. Claims are in expectation.

The reference singleton table is

    r^0(0)=(1,4,0,0),   r^0(1)=(4,1,0,0),
    r^0(2)=(0,0,1,4),   r^0(3)=(0,0,4,1).

The question is whether ONLY the four recipient-specific triple rewards
can offset this hard singleton matrix, without making every triple
leave-safe or invoking an already supplied strategic witness.

Theorem. For every real R>=0 there are delta>0 and M0>0 such
that for EVERY M>M0 and EVERY finite original reward table satisfying

1. All sixteen singleton coordinates differ from r^0 by less than delta.
2. r_i(J_i)=M+c_i, where |c_i|<=R, for each i.
3. Every other nonsingleton coordinate has absolute value at most R,

there is an exact stationary terminal Nash profile against ALL complete
unilateral behavioral replacements. Its actual payoff is one fixed
original-game uniform-equilibrium payoff; the same profile works for
every positive accuracy and all sufficiently long finite horizons.

The produced hazards have q_i=z_i/sqrt(M), where z_i tends to1/sqrt(3)
uniformly over the bounded nonsingleton data as the singleton table tends
to the reference and M tends to infinity. More precisely they can all be
kept in a fixed positive interval around1/sqrt(3). No public correlation,
normalization of Never, supplied Nash row, or reward transport is used.
For an interior bounded box this is a raw sixty-coordinate open tube:
sixteen local singleton coordinates, four jackpot residuals and forty
other bounded coordinates. The theorem concerns each original table at
its chosen finite M; M is NOT varied with the equilibrium accuracy.

## 2. Exact stationary equations before scaling

Fix q in(0,1)^4. For a recipient i and A subset I\{i}, let

    p_i(A)=product_(j in A) q_j product_(j notin A+i)(1-q_j),
    alpha_i=p_i(empty),
    Q_i=sum_A p_i(A) r_i(A+i),
    B_i=sum_(A nonempty) p_i(A) r_i(A).

Q_i is the one-date pure-Quit value, B_i the Continue stopping
contribution, and alpha_i the opponent continuation probability. The
actual stationary policy value is

    U_i=[q_i Q_i+(1-q_i)B_i]/[1-(1-q_i)alpha_i].        (1)

Every denominator is positive. Quit-minus-Continue, against actual
continuation U_i, equals

    Q_i-(B_i+alpha_i U_i)
      =H_i/[1-(1-q_i)alpha_i],
    H_i=(1-alpha_i)Q_i-B_i.                            (2)

Hence a common zero H=0 yields U_i=Q_i=B_i+alpha_i U_i for every i.
The four equations H_i=0 do not depend on q_i itself, but must be
solved JOINTLY in all four coordinates.

## 3. The pole-cancelled raw-data producer

Put t=1/sqrt(M) and q_i=t z_i. Let d denote all forty-four bounded
nonsingleton parameters: c_i at the four jackpot coordinates and the
other forty entries. They range independently over [-R,R]^44.

The ONLY unbounded entry in recipient i's own Q_i is its jackpot,
at opponent coalition A=C_i. Its contribution is exactly

    p_i(C_i)*(M+c_i)
      = z_j z_k (1-t z_(m(i)))
          +t^2 z_j z_k (1-t z_(m(i))) c_i,
          where C_i={j,k}.                             (3)

Thus Q_i extends POLYNOMIALLY in t,z,singleton-data,d through t=0.
Recipient i's B_i has NO jackpot pole: B_i samples only coalitions not
containing i, whereas its sole jackpot J_i contains i. Every term of
B_i is divisible by t, as is 1-alpha_i. Consequently

    Phi_i(t,z,data)=H_i/t                              (4)

has a polynomial extension through t=0. This is an algebraic extension,
not a terminal payoff evaluation at the all-Never zero-hazard law.

Write s_i=r_i({i}), a_i=sum_(j!=i)z_j and
Gamma_ij=r_i({j})-s_i for j!=i, Gamma_ii=0. Then (3) gives

    Phi_i(0,z,data)=a_i z_j z_k-(Gamma z)_i,
                      {j,k}=C_i.                       (5)

Indeed Q_i(0)=s_i+z_j z_k, (1-alpha_i)/t tends to a_i and
B_i/t tends to sum_(j!=i)z_j r_i({j}). All forty-four bounded
nonsingleton data disappear from (5).

At the reference singletons,

    Gamma=[ 0, 3,-1,-1;
            3, 0,-1,-1;
           -1,-1, 0, 3;
           -1,-1, 3, 0 ].

Every row sums to1. Therefore the constant positive vector
z*= (1/sqrt(3),1/sqrt(3),1/sqrt(3),1/sqrt(3)) solves (5):
a_i z_j z_k=3*(1/sqrt(3))^3=1/sqrt(3).

The z-Jacobian at z* has zero diagonal, entry-8/3 in the mate position
and entries7/3 in the two cross positions. To verify this directly,
differentiate a_i z_j z_k: its mate derivative is z_j z_k=1/3;
each cross derivative is z_j z_k+a_i z_k=1/3+1=4/3.
Subtract the corresponding Gamma entries. The invariant subspaces are
the constant line, the difference of the two mate-pair sums, and the
two within-mate-pair differences, with eigenvalues respectively

    2,       -22/3,       8/3,       8/3.

In particular det D_z Phi=-2816/27 is nonzero.

## 4. Uniformity over the ENTIRE bounded data box

For every d in the compact cube [-R,R]^44, the base equation
Phi(0,z*,reference-singletons,d)=0 and the SAME nonsingular Jacobian
hold. Apply the ordinary finite-dimensional implicit function theorem
there, treating t, all sixteen singleton coordinates and all d coordinates
as parameters. Its resulting root z can be kept in, for example,

    (1/(2sqrt(3)),3/(2sqrt(3)))^4.

Choose finitely many of the d-neighborhoods covering the compact cube.
Intersect their t-intervals and singleton neighborhoods. A common
positive t0 and singleton radius delta then give a positive root for
EVERY d in the cube, every permitted singleton table and every0<t<t0.
No local root selector is required to agree on overlaps; existence for
each original table is sufficient. Shrink t0 so all q_i=t z_i<1.
Set M0=max(5,t0^-2). This proves the raw all-parameters producer in
Section1. The extra lower threshold5 is used only in the separating
family below.

## 5. Complete terminal agency, Never, and fixed uniform target

For each produced positive t, H=t Phi=0, so (1)--(2) give
U_i=Q_i=B_i+alpha_i U_i. All opponents have positive stationary hazards,
and alpha_i<1. Under ANY unilateral replacement, the one-stage expected
stopping reward plus alpha_i times U_i on continuation is at most U_i;
indeed both pure endpoints equal U_i. Iterating the inequality leaves
a remainder bounded by a fixed original-table constant times alpha_i^N.
It tends to zero uniformly over the replacing law, including Never.
Thus EVERY complete behavioral deviation earns at most U_i. The
prescribed law realizes U_i, giving exact terminal Nash.

The same independent stationary profile supplies the fixed uniform target
U. Against any deviator, the opponents alone bound the absorption tail
by alpha_i^N. The original finite-horizon average/terminal discrepancy
therefore tends uniformly to0, as does prescribed-profile discrepancy.
Rewards remain finite and fixed; no accuracy-dependent table is used.

The exact already-checked semantic endpoints inspected in
`UniformEquilibrium/Quitting/Stationary/EndpointCompiler.lean` are
`isZeroAsymptoticNash_stationary_of_fixedPoint_endpointNash_contracts`
and `isUniformEquilibriumPayoff_of_stationaryEndpointCertificate_contracts`.
Their inputs here are the ACTUAL value (1), fixed point (2), endpoint
equalities and alpha_i<1. They are consumers, not the new raw producer;
no Lean implementation of Sections3--4 is claimed.

## 6. Exact separating family, not an all-triple-positive class

At the reference singletons define the directed cross-cycle

    succ: 0->2->1->3->0.

Every pair has passive rewards5. Mate pairs pay-1 to both participants.
Each cross pair has one directed edge i->succ(i), and pays-1 to i and2
to succ(i). Every triple J_i pays M to its unique jackpot recipient i,
-1 to its other two participants and5 to its outsider. The grand row is
(-100,-101,-102,-103). These rules specify all fifteen rows completely.
They lie in Section1's class with R=103 and c_i=0, for all sufficiently
large M. Each triple has only ONE large participant.

### 6.1. No root Nash with any sure quitter, over the whole selection set

Suppose owner0 quits surely at any root, with ANY continuation vector.
Its mate1's joining payoff is always-1 or its still smaller grand
coordinate, whereas Continue yields4 or5. Thus1 surely Continues.
Given that, predecessor3's joining payoff is always-1, whereas Continue
gives0 or5. Thus3 surely Continues. Successor2 now strictly prefers
joining for2 to Continue0, so2 surely Quits. Owner0 then gets-1 by
Quitting but0 by withdrawing, a contradiction. No unpriced continuation
event remains in this last comparison.

Rotate by the directed four-cycle to get the identical argument for
EVERY sure owner; the asymmetric grand entries remain negative and do
not affect the comparisons. This excludes EVERY stationary root with
a sure quitter, not merely pointwise leave-safe bases or a chosen
induced free-player Nash. Hence no nonempty persistent-base/free-set
producer can supply a Nash profile for this family. The inspected actual
adapter surface is in
`UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PersistentBaseConcreteGap.lean`:
`nonempty_quittingSingletonBaseCertificate_of_inducedNash` and its
large-base induced-Nash semantic consumer retain sure base coordinates.

### 6.2. Every proper child has an unsafe EXACT child equilibrium

For EVERY nonempty proper child C choose d in C with succ(d) outside C;
such a d exists because succ is a single four-cycle. In the child let
d Quit surely at0 and every other child member be Never. This is exact
child terminal Nash against all complete deviations: d gets1 rather
than Never0; a different child member k gets4 if it is d's mate and0
otherwise, whereas joining gives-1. The only profitable pair joiner is
succ(d), deliberately outside the child. The child joint Never mass is0.

In the original game, that outside successor gains EXACTLY2 by joining
at0. Thus every proper child has a witness with zero child debts and
zero joint Never slack but positive outsider debt. This rules out all
raw withdrawal/future-join reward certificates that bound outsider debt
by a nonnegative weighted child debt plus Never excess, not only the
advancing-only CappedClock subcone. The relevant inspected general
consumer is
`quittingLiftDeletedProfile_outsideDebt_le_add_neverExcess_of_withdrawalFutureJoin`;
the same contradiction pattern is implemented as
`exists_outside_no_quiet_certificate` in
`UniformEquilibrium/Quitting/Examples/NegativePremiumCyclicChildFixtureChildren.lean`.
No claim is made that unsafe child lifting excludes arbitrary joint play.

### 6.3. Response quotients and actual insertion charges

- The normalized singleton matrix is the hard paired Gamma above,
  unchanged by M. All four labels survive singleton normality. This is
  not a homogeneous/non-Q singleton-matrix construction.
- There is no noninjective full stationary response-invariant quotient:
  at the all-sure hazard vector its residual coordinates are
  r_i(I)-r_i(I\{i})=-105-i, all distinct. A block-constant response
  invariance would equate these for two labels in the same block.
  The actual definition inspected is `QuittingResponseInvariantOnUnitCube`
  in `UniformEquilibrium/Quitting/Stationary/ResponseInvariantQuotient.lean`.
- The entire player set is a premium trap, since every player receives2>1
  in the pair with its predecessor. The actual proper-coalition leave
  comparison sums INSERTION gains of players OUTSIDE that coalition.
  On the mate pair{0,1} it is

      [r_2(012)-r_2(01)]+[r_3(013)-r_3(01)]
         =(M-5)+(M-5)=2(M-5)>0.

  Thus `QuittingTrapChargeCoefficients.leave_nonpos` fails on that
  actual trap, excluding `HasBoxedQuittingNashCharges`. The relevant
  definitions are `quittingWeightedLeaveSum` in
  `UniformEquilibrium/Quitting/Classification/WeightedQuittingTrapLeavers.lean`,
  `QuittingTrapChargeCoefficients` in
  `UniformEquilibrium/Quitting/Classification/BoxedQuittingNashCharges.lean`
  and `HasBoxedQuittingNashCharges` in
  `UniformEquilibrium/Quitting/Classification/BoxedQuittingNashChargeReturn.lean`.
  This is not a participant-withdrawal sum: on cross pair02 the actual
  insertion sum is-12, so that pair is not the witness.

### 6.4. Every ordered pair fails the broader crossed lower face

Fix any recipient i and distinct candidate partner p. At the face where
their two hazards are zero, put hazard1 on one outsider j and zero on
the remaining outsider. The actual residual from Section2 is then

    H_i=r_i({i,j})-r_i({j}).

If p is not mate(i), choose j=mate(i), giving H_i=-1-4=-5.
If p is mate(i), choose j=succ(i), giving H_i=-1-0=-1.
Thus EVERY ordered pair has a strictly negative point on its literal
closed lower outsider box, independently of the ceiling height and M.
This violates even a necessary NONNEGATIVE lower face condition, not
merely one sufficient coefficient ranking.

In particular it excludes `QuittingCrossedSourceGuards` in
`UniformEquilibrium/Quitting/Stationary/GuardedCrossedResponseGuards.lean`,
whose lower face must be strictly positive for every nonzero outsider
row, and `QuittingOneSidedWeakUnitGuards` in
`UniformEquilibrium/Quitting/Stationary/OneSidedWeakUnitProducer.lean`,
whose lower face must be nonnegative. The same point excludes the
broader weak polynomial lower premise of `QuittingHalfWeakPolynomialGuards`
in `UniformEquilibrium/Quitting/Stationary/GuardedCrossedResponseWeakPolynomialFaces.lean`.
Strict/weak raw-ranking adapters cannot bypass a failure of their actual
polynomial conclusion.

### 6.5. Two concrete calendar restrictions fail

Any raw calendar premise requiring a prescribed pair with BOTH
participant rewards positive fails here, under every relabeling: every
pair has at least one participant reward-1. This includes a local pair
premise with both center rewards at least2 and radius at most1/2.
It does not exclude all possible calendars.

There is also a whole-architecture exclusion for the positive singleton
word0,2,1,3 and its mate-preserving relabelings, not just its symmetric
hazard choice. Each owner's mate occurs two phases later. Let u_l in(0,1)
be the four Continue probabilities in chronological order. Owner
indifference, with own singleton1, is exactly

    E_l=u_l[4-4u_(l+1)+u_(l+1)u_(l+2)]-1=0,

with cyclic indices. Put a=u_0-u_2, b=u_1-u_3. Opposite differences give

    E_0-E_2=4(1-u_1)a-u_2(4-u_0)b,
    E_1-E_3=u_3(4-u_1)a+4(1-u_2)b.

The determinant is

    16(1-u_1)(1-u_2)+u_2u_3(4-u_0)(4-u_1)>0.

Hence a=b=0. Writing u_0=u_2=x, u_1=u_3=y, the remaining difference
is (4+xy)(x-y)=0. The common equation factors as

    (u-1)(u^2-3u+1)=0,

so the UNIQUE positive proper owner solution has
u=(3-sqrt(5))/2 and p=1-u. At a root of one owner, the next nonmate's
prescribed value is u and the preceding nonmate's prescribed value is1;
these follow by evaluating their singleton continuation paths, using
u(4p+u^2)=1. Either nonmate's immediate-Quit value is
u+p*r_i({i,owner}). Thus their necessary pair-participant caps are
respectively0 and1. Each actual cross pair here has one participant
reward2, so some inactive endpoint inequality fails, for either
orientation. This excludes the ENTIRE named positive singleton-word
architecture at the reference singleton rows, including any positive
branch selected by a local implicit-function theorem. No unspecified
neighborhood radius or all-calendar uniqueness is assumed.

### 6.6. Further exact raw-data boundaries

The grand row rules out every nonzero nonnegative global inserted-premium
floor: its necessary test is sum_i w_i(-101-i)>=0. The supportwise
upper-average alternative on the full premium trap fails as well.
For nonnegative weights put X=w_0+w_1 and Y=w_2+w_3. Testing mate pairs01
and23 gives respectively

    (M-1)Y<=2X,       (M-1)X<=2Y.

For M>3 these force X=Y=0. Thus no nonzero such weight exists, and it
cannot rescue the failed insertion-charge arm. Every three-element set
also contains a mate pair whose two ordered joining gaps are-1-4=-5;
any source requiring six positive joins within one triple fails for
EVERY triple.

The common-large-PAIR family has a different scale premise: all twelve
pair participant entries grow together, whereas here four triple entries
grow and pair entries stay fixed. This observation alone is not a
whole-quantifier noncontainment proof for an earlier theorem with an
unquantified threshold depending on its bounded-data radius. No such
inference is used. A supplied stationary-root or face-box verifier can
of course consume the actual root produced here; that is not an earlier
raw-data producer for this class.

## 7. Boundary tests and precise implementation target

- R=0 is permitted: the forty-four bounded parameters are then zero,
  and the same nonsingular base point supplies a root. R=103 is sufficient
  for the entire explicit separating family. No threshold uniform over
  unbounded R is asserted.
- The polynomial value at t=0 is NOT a physical all-Never payoff. At the
  actual all-Never law the payoff is0 and each singleton deviation earns1
  at the reference table. All produced profiles have strictly positive
  t and every player's deleted-opponent system contracts.
- The jackpot indices are substantive: i's sole unbounded reward contains
  i and occurs with exactly TWO opponent quits. This is why it enters Q_i
  at order M*q^2 but never enters B_i. An arbitrary large passive-recipient
  entry cannot be included in the bounded box without changing the proof.
- Grand rewards and all other bounded coordinates can have either sign;
  every unilateral deviation, including a simultaneous grand-coalition
  quit and Never, is retained in Sections2--5. No coalition is discarded
  because its equilibrium probability is small.
- The separating insertion test requires M>5, already ensured by M0.
  No claim at the threshold or at small jackpots is needed.

The new implementation target is the raw polynomial construction in
Sections3--4: its extension, exact base Jacobian, positive local root
and uniform compact-parameter quantifiers. Sections2 and5 identify the
actual stationary value and supply the fixed-point, endpoint and deleted
contraction hypotheses of the two named checked semantic consumers.
Implementing those algebraic steps would give an actual-data adapter;
the present proof does not itself claim a checked Lean producer.

The result is a raw-table existence theorem with explicit whole-selection
comparisons. It neither settles arbitrary four-player quitting games nor
claims that its stationary architecture represents every uniform payoff.
