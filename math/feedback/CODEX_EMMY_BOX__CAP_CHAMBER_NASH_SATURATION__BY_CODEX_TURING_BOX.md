# Independent full-cap chamber review

Reviewer: CODEX_TURING_BOX. Verdict: PASS for the ordinary mathematical
proof, including the final unbounded asymmetric family below. This is not
a Lean verification, an exact-terminal-Nash theorem, or an arbitrary-Fin4
theorem. The author file was not edited.

Checked versions:

* Base `notes/CODEX_EMMY_BOX__CAP_CHAMBER_NASH_SATURATION.md`, SHA256
  `9dc27819b96e8d881ae46107b5480349474f1512c8468a17839e2de95056f3da`.
* Separate interval delta, Section7 of
  `notes/CODEX_EMMY_BOX__OPPONENT_COINCIDENCE_BARRIER.md`, whole SHA256
  `946f5e2072da56c90bca6694ea6b0c28e168995c25534fbe7f3ea1e163c9a4a7`.
* ENTIRE final family
  `notes/CODEX_EMMY_BOX__PASSIVE_TRIPLE_CAP_CHAMBER_RAW_FAMILY.md`, SHA256
  `bb20cbe7d9078b51df89df7716085441cc90f31763a8f12e61247b7c8ea10c16`.

The companion checker was read, but its success was not a mathematical
premise. I reconstructed the literal coalition rows independently,
symbolically checked the endpoint and total-reward identities, and
separately enumerated all singleton LCP supports and all15 response
partitions. The soundness verdict and these computations preceded reading
the other independent review.

## 1. Exact claim and legal semantic source

The final input fixes the printed singleton/pair rows and all triple
participant rewards at-1. The four passive triple coordinates are arbitrary
finite K_i>=7, and each finite grand coordinate satisfies ONLY G_i<K_i.
In particular there is no upper bound on K_i or |G_i|, no lower bound on
G_i, and no common-K assumption. The conclusion is a fixed uniform payoff
obtained from actual independent complete private clocks with ALL unilateral
behavioral caps tending to the same target. No public correlation is added.

The compact domain is the closure of ACTUAL pairs(U,B), where B is the full
unilateral supremum. It is not an arbitrary annotation box, a convexification,
or a closure of an exact-root spine. Never guarantees B_i>=0 because every
passive reward is0,1,4, or K_i. Negative grand rewards do not affect this
fact. Every fixed table has a finite reward bound, sufficient for compactness.

For a fixed product root q, let alpha_i be opponent Continue probability
and c joint Continue probability. The exact prefix equations are

    U_i'=q_i Q_i+(1-q_i)(b_i+alpha_i U_i),
    B_i'=max(Q_i,b_i+alpha_i B_i).

At ANY Nash root of the finite binary game with continuation B,

    d_i'=c d_i,             D'=c D.

This remains true for a nonattained response supremum. For a fixed chosen
q, prefixing is continuous, so a root selected at a carrier limit gives a
legal point of the same closed actual carrier. The approximating actual
profiles do not need to have this root as their own Nash root. No continuous
Nash selection or inherited chronology between accuracies is being assumed.

I opened the actual statements and relevant definitions of:

* `quittingTerminalSemanticPair`, `quittingTerminalSemanticPrefix`,
  `quittingTerminalSemanticCarrier`,
  `exists_terminalProfile_sequence_tendsto_semanticPair`,
  `quittingTerminalSemanticCarrier_isCompact`,
  `continuous_quittingTerminalSemanticPrefix`, and
  `quittingTerminalSemanticPrefix_mem_carrier` in
  `UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`;
* `exists_isZeroQuittingRootNash` in
  `UniformEquilibrium/Quitting/Root/NashExistence.lean`;
* `quittingTerminalSemanticDebt_prefix_eq_continueMass_mul_of_capNash`
  and
  `quittingTerminalSemanticPrefix_envelope_eq_rootSuccessorPayoff_of_capNash`
  in `UniformEquilibrium/Quitting/Root/CapNashRootStack.lean`;
* `isUniformEquilibriumPayoff_of_diagonal_mem_terminalSemanticCarrier` in
  `UniformEquilibrium/Quitting/Classification/Existence/UniformPayoffTerminalSemanticCarrier.lean`.

Their hypotheses match the use here. The last consumer retains ALL complete
behavioral replacements, Never, and one fixed payoff target. It does not
require an actual strategy representing the limiting semantic pair.

## 2. Adversarial support and boundary checks

A sure quitter i makes opposite i+2 strictly prefer Continue, with
joining differences-4,-2,G_(i+2)-K_(i+2). Once opposite Continues,
predecessor i-1 has differences-1,-2 and also Continues. Successor joins
strictly, after which i can withdraw from-1 to0. This excludes EVERY sure
Nash root for EVERY continuation, not just a selected root. Thus all active
rates are interior and all active endpoint equalities are legitimate.

For full support, opponent odds x,y,w give

    P_i=1+2x-w-(xy+xw+yw)+G_i xyw,
    N_i=4y+(xy+xw+yw)+K_i xyw.

Active indifference implies B_i=P_i-N_i. Consequently

    sum B=4-3Z-4E2+sum_i(G_i-K_i)V_i<4.

A positive-debt chamber point instead has sum B>4. This contradiction
excludes full support at EVERY such point. It is precisely what permits
arbitrary finite grand rewards below the corresponding K_i. No claim of
full-support invariance at zero debt is needed.

All surviving nonzero supports were independently checked:

* Singleton: the owner's output cap is1.
* Adjacent pair(a,b): B0=(1-2b)/(1-b), B1=(1+a)/(1-a).
  Nonnegative B0 gives b<=1/2 and output Q0=1-2b<1.
* Opposite pair(a,b): B0=(1-5b)/(1-b) and its rotated counterpart.
  Thus a,b<=1/5 and output Q0=1-b<1.
* Triple(a,b,e,0):

      Q0=1-2b-e+be,       b0=(4-3b)e,
      Q2=1-a+b-2ab,       b2=(4-3b)a.

  Nonnegative active caps give

      1-2b-5e+4be>=0,     1-5a+b+ab>=0,
      b<=1/2, a<=1/3, e<=(1-2b)/3,
      a+b+e<=5/6,          Q0<1.

The varied passive-triple/grand coordinates are absent from these ACTIVE
endpoints. The inactive player's full Nash inequality is not discarded:
the calculation is a necessary consequence of an already full-game Nash
root and does not propose solving only the active subsystem.

The total-cap ledger on supports<=3 is exactly

    sum B'-4=c(sum B-4)+H,
    H=P1-P_adj-2P_opp+sum_i(K_i-7)P_(3,i).

The Poisson-binomial inequality has the correct direction. With odds z,
Cauchy gives sum z/(1+z)>=Z^2/(Z+sum z^2); hence sum q<=1 implies
2E2<=Z and therefore P1>=2P2. Opposite and triple supports meet the premise.
Adjacent support instead gives H=a+b-3ab>=0 for b<=1/2. Singleton and empty
supports have no exception. Thus H>=0 follows from K_i>=7, including equality.
This is entire-correspondence preservation at positive debt, not a selected
favorable-root assertion. No grand-probability term remains because support4
was excluded before this ledger was used.

## 3. Actual seed, compact minimum, and endpoint

For the stated seed I independently evaluated every pure response class:

    player0/2: Quit0=1/4, finite date>0=1/2, Never=1/4;
    player1/3: Quit0=1/2, finite date>0=5/2, Never=2.

Mixtures add no larger value. Thus U=(1/4,5/4,1/4,5/4),
B=(1/2,5/2,1/2,5/2), D=5/4, and sum B-4=2 are exact FULL-cap data.
The old base sentence excluding every triple encounter was too broad:
an outsider Quit0 can form a triple and receive the FIXED member reward-1.
The final family states the accurate fact: no VARIABLE passive triple or
grand coordinate enters a seed response. This prose repair changes no cap.

The chamber min B<=1, sum B-4>=(8/5)D is compact and contains this seed.
At a positive minimizing debt, min B<1 makes all-Continue non-Nash, so
finite Nash existence supplies a nonzero root. If min B=1, sum B>4 gives
a directed cycle edge from B_i=1 to B_(i+1)>1. The printed one-owner
p<(B_(i+1)-1)/(B_(i+1)+1) root is exact Nash: successor strictly Continues;
predecessor and opposite have the printed nonnegative margins; owner is
indifferent. This includes all equality/boundary cap cases.

No sure rate and a nonzero root imply0<c<1. Entire-correspondence chamber
preservation plus D'=cD contradicts a positive chamber minimum. Therefore
the chamber contains a diagonal actual-carrier point. The named consumer
then supplies actual independent approximate profiles and a fixed uniform
payoff. No semantic closure point has been silently called an actual clock.

The earlier K in[7,30] delta also passes, including both endpoints. It is
strictly subsumed by the final family, whose proof no longer needs the
full-support low-output-cap estimate or any upper-grand bound.

## 4. Exact K10 structural hard-class membership

These are ordinary exact calculations about K10, NOT a positive-gap witness.
Its normalized singleton matrix is

    Gamma=[ 0,-1, 3,-1;
           -1, 0,-1, 3;
            3,-1, 0,-1;
           -1, 3,-1, 0].

Every row has a negative adjacent neighbor, so the recursive normal core
retains all four players at every layer. Actual punishment values are
exactly0: Never guarantees>=0, and a sure successor singleton makes the
player's entire best-response value0. All own singletons1 are therefore
punishment-normal as well.

Gamma is R0. Singleton supports violate an inactive negative neighbor;
two-player active equations have nonzero off-diagonal coefficients;
every three-principal determinant is6 and det Gamma=45. At offset ones
the ENTIRE strict complementary root set consists of:

    empty, index+1;
    four adjacent supports with active entries(1,1), index-1 each;
    four triple supports with rotated entries(1/2,5/2,1/2), index+1 each.

All inactive inequalities are strict. The actual degree is1-4+4=1, with
the active determinant sign and NO extra support-parity factor. Thus Gamma
is standard Q by the R0 nonzero-degree theorem, but the degree-not-one
producer does not apply.

It is NOT projective-Q-bar. An adjacent principal is [[0,-1],[-1,0]].
At offset(-1,-1), every nonnegative standard candidate has a negative
residual. Its homogeneous simplex problem also has no solution: any
positive coordinate makes the other residual negative. Therefore even
the projective problem at that offset is unsolvable. This is an explicit
hard-principal obstruction, not a failure of one chosen full-matrix root.

Consequently K10 satisfies the ordinary predicate `ResidualHardClass`
defined in `UniformEquilibrium/Quitting/Classification/LCP/Gate.lean`:
nonempty full normal core, no homogeneous solution, normal standard Q,
and failure of full projective Q-bar. I also opened `NormalCore.lean`,
`MatrixClasses.lean`, `Normalization.lean`, `NormalPrincipalQBar.lean`,
and `PunishmentNormalR0.lean` in that LCP subtree. The degree interpretation
was checked against `isStandardQ_of_r0Degree_ne_zero` in
`MathUE/LinearProgramming/R0Degree.lean` and
`IsStandardLCPSolution.exists_box_localDegree_eq_sign_det` in
`MathUE/LinearProgramming/LocalDegree.lean`.

This does NOT certify `FinFourQuantitativeFullSupportHardResidual` in
`UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/FullSupportProjectiveQBarResidual.lean`:
that structure includes an ACTUAL positive terminal-gap witness. The new
UE proof rules such a witness out. Nor is literal K10 already the existential
single-pivot normalization with own singletons(1,0,0,0). That normalization
is a counterexample reduction, not a required equality for every original
raw table. Subtracting1 from finite rewards while leaving Never unchanged
would not preserve the original full game.

## 5. Bounded whole-source coverage checks at K10

These provide a separating witness inside the new family. They are not a
claim that every family member avoids every older result, or that every
unquantified qualitative IFT neighborhood is disjoint.

### Entire induced-base and punishment-tail selections

The continuation-independent no-sure proof excludes EVERY full one-shot
Nash root with a sure player. Thus any persistent-base induced Nash
selection with all omitted-player joins and all base-player leaves accepted
is impossible, since it would be such a root. This covers all selections,
not only their pure witnesses. Directly, the full induced-complement Nash
sets at K10 are: singleton base has only its successor sure and the other
two Continue; adjacent/opposite bases have all outsiders Continue; triple
base has its outsider Continue. Singleton owner payoff-1 versus withdrawal0,
adjacent donor gap-1, opposite gaps-4, triple member gaps-2, and grand gaps-1
reject their corresponding accepted base rows. Singleton punishment0 cannot
repair its owner-floor inequality. I checked the actual induced-game
definitions in `UniformEquilibrium/Quitting/Root/PersistentBaseInducedGame.lean`.

### Every child, including full-behavior quiet transports

For ANY nonempty proper child C, choose j in C with successor j+1 outside C.
In the child, sole j Quit0 and everybody else Never is exact Nash: a
predecessor join gives-1 instead of0, an opposite join gives0 instead of4,
and the successor is absent. Joint Never mass is0. In the full quiet lift,
missing successor j+1 can Quit0 for2 instead of0. Thus all child debts and
Never residual are0 but an outsider's complete debt is2.

This rules out any universal raw child certificate whose checked consumer
bounds that outsider by nonnegative weighted child debts plus a finite
joint-Never residual. I opened the actual full-behavior transport declarations
`quittingLiftDeletedProfile_outsideDebt_le_add_neverExcess_of_withdrawalFutureJoin`,
`quittingLiftDeletedProfile_outsideDebt_le_of_withdrawalFutureJoin`, and
`isεAsymptoticNash_quietLift_of_withdrawalFutureJoinFamily` in
`UniformEquilibrium/Quitting/Classification/QuietExtension/WithdrawalFutureJoinFixedTarget.lean`,
as well as the five-kind raw premise in `WithdrawalFutureJoinRaw.lean`.
I also checked `quietLift_outsideBehaviorDeviationDebt_le_weighted_childDebt_add_slack`
and `quietLift_outsideBehaviorDeviationDebt_le_weighted_childDebt` in
`CappedClockChildDeletionAdapter.lean`, and the Never-residual variant in
`CappedClockPositiveSingletonQuietExtension.lean` in the same directory.
The universal profile witness excludes every child and every certificate
weight choice in those premises. It does not exclude a hypothetical new
consumer restricted to a selected favorable child equilibrium.

### Entire response partitions and degree/inverse screens

Independent symbolic enumeration of ALL15 partitions using the literal
residual H_i=(1-alpha_i)Q_i-b_i leaves only discrete, opposite02|13, and
all-four blocks. Their quotient matrices are Gamma, [[3,-2],[-2,3]], and
[1], respectively, each R0 of degree1 and positive determinant. Some
other partitions preserve singleton block sums but fail actual higher-order
response equality. For example 01|23 at q=(0,0,1/2,1/2) has
H0=-7/8 versus H1=-23/16; 02|1|3 at q=(0,0,0,1/2) has H0=3/4 versus H2=0.

The exact response condition and polynomial interpretation were opened in
`UniformEquilibrium/Quitting/Stationary/ResponseInvariantQuotient.lean` and
`ResponseInvariantQuotientPolynomial.lean`. I also opened
`finFour_responseQuotient_r0Degree_eq_one_of_no_uniformPayoff` and
`finFour_exists_uniformEquilibriumPayoff_of_responseQuotient_nonnegative_inverse`
in `UniformEquilibrium/Diagnostics/Quitting/FinFourResponseQuotientCriterion.lean`.
Thus no partition invokes the whole degree-not-one or
negative-determinant/nonnegative-inverse quotient exit. Gamma itself has a
POSITIVE inverse, not a mixed inverse:

    Gamma^-1=(1/15)[2,3,7,3;3,2,3,7;7,3,2,3;3,7,3,2].

The failed inverse exit is its positive determinant/degree1. Every deleted
triple inverse has a negative diagonal entry, excluding the raw nonnegative
child-inverse criterion as well.

### Boxed, weighted, joins, and accepted finite phase classes

The only premium trap is the full set, because a trap must be closed under
the directed positive incoming participant premiums. Summing its singleton
weighted floor tests gives-2 sum weights, excluding all nonzero nonnegative
weights. The grand coalition gives upper-average premium8 sum weights,
excluding all such upper-average weights. For boxed charges the actual
singleton, pair, triple coefficient pairs are(-2,-3),(-4,-4),(8,-1).
Every allowed coefficient choice has delta<=2, gap<=3, loss<=1, tau>=8,
so its threshold is at most13/2, below the required4+4M with M>=10.
These premises were checked in `WeightedQuittingTrapLeavers.lean`,
`BoxedQuittingNashCharges.lean`, `BoxedQuittingNashChargeOdds.lean`, and
`BoxedQuittingNashChargeReturn.lean` under
`UniformEquilibrium/Quitting/Classification/`.

Every pair partition fails a weak member join: adjacent donor join-1<0,
or opposite join0<4. Every triple fails its six-strict-join source. The
paired singleton favorite relation forces opposite mates, and an incoming
participant reward2 violates the corresponding cross threshold<=1 in the
named proper golden singleton-calendar architecture. The earlier four-joint
local/rectangle/passive-ray raw hypotheses likewise fail their literal
scheduled pair requirements: K10 pairs have a nonpositive member rather
than the required positive scheduled member values. These are bounded
named-source comparisons, not a statement about unknown larger qualitative
IFT neighborhoods or arbitrary longer calendars.

The base exact all-stationary exclusion was also reconstructed. Supports0
and1 give an immediate profitable Quit; adjacent support2 has one active
player with Never0 and positive Quit, while opposite support2 has Never4
and Quit<=1. For support3(a,b,e,0), stationarity of player0 gives b<1/2,
then e<1/4, whereas player1 has Quit>1/2 but stationary continuation<=e.
For the bound on e one uses

    (1-2b)(b+e-be)<=(1+e)/2,
    (1+e)-2(1-2b)(b+e-be)
                 =(1-e)(1-2b+4b^2)+4be>=0.

In full support set A_i=x+y+w+T+V and
F_i=N_i(1+A_i)-P_i A_i. Stationarity requires every F_i=0, but literal-row
expansion gives

    sum F=sum z+Qquad
          +sum_i[9V+3T(2y+w)+2T^2
                         +V(-x+5y+2w)+3TV+V^2],
    Qquad=2 sum z_i^2+(z0-z2)^2+(z1-z3)^2
                                      +7 sum_adjacent z_i z_j.

All terms are nonnegative after grouping2T^2-xV, whose coefficients are
positive, and sum z>0. Thus sum F>0. The polynomial identity was checked
independently from literal rows, not numerical root searches. This excludes
applicability of sound sources concluding an exact stationary Nash profile,
not stationary approximation or arbitrary nonstationary sources.

## 6. Significance and the genuinely missing general step

This is a complete producer on an unbounded raw family, with K10 an ordinary
hard-matrix witness not caught by the bounded named screens above. The generic
compact minimum argument was already available; the substantial new math is
the table-specific nonconvex chamber, its seed, and its entire-correspondence
support inequalities. It is not merely a conditional endpoint for supplied
low-regret profiles.

The proof demonstrates that chronological temporalization between accuracies
is unnecessary for this endpoint. It globally minimizes over a closed ACTUAL
semantic chamber rather than following a fixed root spine. A newly available
root at the minimizing limit is enough; intermediate payoff targets and
calendars are free to change. It neither asserts universal root contraction
nor promotes arbitrary semantic annotations to actual states.

For arbitrary hard residual data the missing assertion is substantive: find
an actual nonempty compact region or another global operation that prevents
stalling at positive debt, while guaranteeing a nonzero exact cap-Nash root
and preserving the required region. Finite Nash existence alone can return
only all-Continue when all caps lie above own singletons. Here low-minimum
cap plus surplus rules out that stall, and surplus also excludes full support
exactly where it is needed. No argument currently produces comparable
geometry for every arbitrary hard residual table.
