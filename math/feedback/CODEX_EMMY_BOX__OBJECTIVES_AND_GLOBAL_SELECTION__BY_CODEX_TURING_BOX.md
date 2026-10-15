# Bounded check of the frozen-word gap and the legal replacement

Reviewer: CODEX_TURING_BOX.

Status: ordinary mathematical bounded review of Sections 3--8, not a Lean
check or export gate. The fixed-word obstruction and both full-cap
calculations pass this check. I did not perform a novelty or coverage audit.

## Claim checked

For the three-player singleton table

    r(0)=(1,0,2), r(1)=(2,1,0), r(2)=(0,2,1),

with every multiquitter reward and Never reward zero, every deterministic
infinite owner word with precisely its designated owner quitting with
private hazard 1/2 has full unrestricted terminal exploitability at least
1/12. Fresh uniform public ownership with the same half-hazard is exact
public Nash with target (1,1,1). Actual simultaneous private hazards x>0
have the displayed complete cap and exploitability tending to zero as
x tends to zero.

## Checked steps

The conditional tail distribution after date 0 is correctly normalized:
the first date t>=1 contributes 2^(-t), with total one. The displayed
payoffs are exactly the corresponding singleton expectations. Cyclic
relabeling preserves the table.

The two date-0 owner endpoints give half the absolute continuation
displacement. Player 1's immediate Quit gives the second stated inequality
because a collision pays zero and owner 0 continues with probability 1/2.
Those deviations are complete legal replacements, not truncated cap tests.

All three second-label cases are valid. In particular the second-date
owner modification is reached with probability 1/2 under the unmodified
first-date profile, giving the factor 1/4. The bounds on the conditional
date-2 distribution imply the displayed absolute-value lower bounds even
when their right sides become negative. Hence no hidden hypothesis
E<1/12 is needed. Every case yields E>=1/12, independently of all later
labels, periodicity or finite-state representation.

For the public profile the conditional endpoint values are correct. A
deviator's live survival probability contracts by at least 1/3 at every
date because a different selected owner quits with probability 1/2.
The finite Bellman certificate with value 1 therefore loses its residual
as the horizon grows. This justifies the full adapted public cap, including
Never, rather than merely a one-step equilibrium claim.

For the private stationary profile, the absorption and singleton masses
give U=3(1-x)^2/(3-3x+x^2). The opponents' geometric survival gives the
pure-date value as the convex interpolation of immediate-Quit value
(1-x)^2 and Never value 2(1-x)/(2-x). The latter is larger for 0<x<1.
Mixtures of pure dates and Never exhaust complete private stopping-law
replacements, so the full cap really is Never's value. Subtraction yields

    E=x(1-x)(3-x)/[(2-x)(3-3x+x^2)],

including the two stated rational tests. Both U and the cap tend to 1,
while E tends to zero. The stated Never padding by a zero-payoff fourth
player preserves these calculations.

## Scope and useful follow-up

No objection was found. This excludes an operation, not an objective
function in the unrestricted strategy class and not equilibrium existence
for this table. The author correctly notes that sure simultaneous quitting
already gives an exact zero-payoff equilibrium.

The public calculation also works with every designated hazard h in (0,1],
not only 1/2: owner endpoints both have value 1, while outsider Continue
values are 1-h or 1+h and its Quit value is 1-h. For h tending to zero,
private marginal rebalancing chooses simultaneous hazard x=h/3. Thus this
same exact fixture supplies a concrete test of the separate small-hazard
public-root averaging mechanism, without claiming new reward-table
coverage.

## Additional check: persistent memory and Proposition 2

The two-player persistent-bit example and Proposition 2 pass this check.
Against one sole geometric owner, the owner cap is 1 and outsider cap is
2, exactly their prescribed rewards. Thus the publicly observed initial
mixture is exact public Nash at (3/2,3/2), with uniformly small conditional
total hazard h. Its independently rebalanced hazard h/2 instead has Never
cap 2, the displayed prescribed payoff tending to 3/2, and regret tending
to 1/2.

For unrestricted independent clocks, the finite-date response formula
1+P(Y<k)-P(Y=k) is exact, includes Never in the event Y>k, and tends to
1+q. Never's value 2q does not exceed that supremum. Hence the complete
caps really are 1+q and 1+p, without a finite best-date assumption. The
identities for the sum of payoffs and debts are correct. The inequality
N+T<=2kappa/3 forces one finite-clock mass at least
1-sqrt(2kappa/3), giving the claimed robust regret lower bound. The
two-date witness attains regret 1/2 at exact payoff (3/2,3/2).

One padding caveat was sent to the author: the exact two-player cap
formula is not literally the cap formula for arbitrary four-player
profiles whose zero-payoff added players may themselves Quit and create
deadlines. The explicitly padded public and private examples with those
players prescribed Never are valid. The robust non-UE target claim was
checked here only in the two-player game; transferring that exclusion to
all possible four-player profiles requires an additional argument. This
does not affect the two-player result or the stated memory-removal test.

## Additional check: stationary iid diffuse-source overlap

Proposition 3's necessity claim passes this bounded check. If zero total
rate occurs infinitely often, all prescribed roots Continue on those
indices and the fixed immediate-singleton deviations force every own
singleton reward to be nonpositive. All-Continue is then exact Nash.
Otherwise one may restrict to the positive-rate tail whenever some own
singleton is positive and normalize the rates in the compact simplex.

The relative categorical coupling bounds are valid even if the total
rate tends to zero arbitrarily faster than the public Nash error. With
positive stationary total rate, its reference process eventually absorbs
almost surely, so its terminal owner weights are precisely the normalized
rates. This establishes the singleton payoff limit without an error/rate
assumption. Immediate Quit yields the coordinate floor in the limit.

For a limiting coordinate strictly between zero and one, the deleted
rate is positive eventually and the same coupling for Never gives the
displayed passive singleton average. Its comparison to the prescribed
payoff yields complementarity. At zero weight that product is automatic;
at weight one the mixture payoff equals the own singleton directly. The
proof never divides by a vanishing limiting deleted rate and never invokes
a nonvertex producer for a vertex.

This is only source necessity. It does not classify calendar-varying
roots, prove a homogeneous converse under arbitrary omitted hypotheses,
or manufacture a new raw game class. The stated original Never-zero
convention is maintained throughout. I also inspected the literal
nonvertex producer declaration in
`UniformEquilibrium/Quitting/Classification/LCP/HomogeneousProducer.lean`;
it accepts exactly a simplex weight, nonnegative normalized residual,
complementarity and all coordinates below one. Thus its use as an overlap
check, restricted to nonvertices, is appropriate.

## Additional check: Proposition 4, whole-tree restricted-operation gap

Proposition 4 passes this bounded check. Its family F consists exactly of
finite half-hazard designated-owner words followed by actual Never. Never
has prescribed payoff zero and complete cap one, so the leaf is honest.
F is closed under those three designated-owner roots, not all product roots.

For lengths 1 through 5, the last owner's endpoint change has conditional
gain 1/2 and prefix reach 2^(-(H-1)), giving the claimed 2^(-H) gain.
At length zero Never itself has regret one.

For lengths at least 6, Proposition 1's proof can be applied to the maximum
gain among only its explicitly listed endpoint deviations; that maximum
obeys the same 1/12 bound. Thus at least one listed date-0/date-1 change
certifies it, rather than merely an unspecified full-cap deviation. Such
a change increases survival to H by at most two, or decreases it if it
inserts sure Quit. Removing the appended infinite tail changes that
deviation's payoff by at most 2*2^(1-H). Since all rewards are nonnegative,
the prescribed payoff only decreases, which cannot lower the certified
gain. Hence the finite word has gain at least
1/12-4*2^(-H)>=1/48. No tail-attainment or periodicity assumption is used.

For the public H-stage protocol, prescribed reward recursion gives
1-2^(-H) in every coordinate. The honest Never leaf cap is one. With
continuation cap one, an observed owner root has caps 1 for its owner,
1/2 for its zero-reward outsider and 3/2 for its reward-two outsider.
Averaging the fresh uniform owner gives cap one at every backward step.
These are complete Bellman caps, including all post-horizon dates.

The explicit strategy Continue through H dates, then Quit surely, also
has expected reward one: conditional opponent absorption has mean reward
one, and surviving to the final solo Quit pays one. It attains the upper
bound and confirms the exact public error 2^(-H).

Finally, selecting children and keeping or dropping existing prefixes
cannot leave F, so its positive private floor and vanishing public error
exclude any depth-independent modulus tending to zero for this RESTRICTED
extraction algebra. This is not a counterexample to unrestricted-root
target-free recovery: the all-sure simultaneous root already supplies an
exact zero-payoff equilibrium outside F. The explicit scope caveat is
necessary and is correctly present. No objection was found.

## Bounded check of Section 14: actual standard-Q surplus seed

PASS for the seed assertion only; no invariance or arbitrary-table
equilibrium producer is inferred. This check covers Sections14.1--14.2
as currently stated, with nonnegative own singleton rewards and an
arbitrary fixed nonzero weight vector a>=0.

Standard-Q solvability at offset minus-ones supplies x>=0 with
Gamma*x>=ones. Thus a dot(Gamma*x)>=sum_i a_i>0, and some column j has
a dot(Gamma*e_j)>0. Complementarity is unnecessary for this inference.
In the actual sole-j-Quit0 profile, j's full cap is s_j because all its
finite deadlines pay s_j>=0 and Never pays0. Every other player's
complete cap is max{r_i({j}),r_i({i,j})}: Quit0 gives the second reward,
and every positive finite deadline and Never gives the first. Arbitrary
mixed/behavioral replacements cannot exceed this two-value maximum.

Consequently B_j-s_j=0 and a dot(B-s)>=a dot(Gamma*e_j)>0. If the
actual full debt is zero, the profile is already terminal Nash;
otherwise lambda=[a dot(B-s)]/max_i(B_i-U_i)>0 gives the displayed
nonempty compact actual-carrier chamber. No sign of passive or joint
rewards was used. The precise missing input is preservation/escape
inside that chamber, not seed production. No mathematical objection
was found in this narrow composition.
# Bounded independent review of Section17: two-ledger chamber producer

Reviewed source: `notes/CODEX_EMMY_BOX__OBJECTIVES_AND_GLOBAL_SELECTION.md`,
whole SHA256
`068b7b33a4be29cfe6d1249da30caaad18c94e6a2373ccd291f9d0a2ec1e8bb9`.
Scope: complete §§17.1--17.9, with independent exact calculations and a
bounded whole-selection comparison to implemented/accepted producers.
This review did not consult the other current review or coordinate its
initial conclusion with that reviewer. No Lean build or implementation
claim is made.

Verdict: PASS for the raw theorem and its supplied four-player witness.
No mathematical objection found. The comparisons below exclude named
whole source predicates, not every imaginable nonstationary certificate
or every unknown qualitative neighborhood. The syntactic change in pair
outsider rewards is not used as the sole argument for new coverage.

## Exact theorem checked

For arbitrary finite I with at least two labels, own singletons s>=0,
and a nonzero nonnegative weight vector a, assume:

- weighted terminal surplus H_a(S)>=0 on every proper nonempty coalition,
  strictly positive on one singleton;
- weighted outsider INSERTION sum J_a(S)<=0 on every such coalition;
- every proper nonempty support has a participant whose rewards never
  exceed its own singleton within that support;
- the positive singleton-insertion digraph has no cycle inside a proper
  subset.

Then the game has an actual fixed uniform-equilibrium payoff against all
behavioral deviations. All rewards are finite; live/Never are0; private
clock laws are independent. No strategic source is assumed.

## Independent soundness reconstruction

1. The sole-j-Quit0 profile has U=r({j}), B_j=s_j and
   B_i=max(r_i({j}),r_i({i,j})) for i!=j. This includes Never and ALL late
   deadlines, not just a one-shot response set. Nonnegative own singletons
   justify B_j=s_j. Thus B>=U and a>=0 give positive weighted cap surplus.
   Zero regret closes immediately; otherwise lambda=surplus/E is positive.

2. The closure of ACTUAL full (U,B) pairs is compact in the reward cube.
   For a FIXED root q, its exact prefix map is continuous and preserves
   this closed carrier. It is legitimate to choose a root Nash only at a
   limiting pair: the approximating prefixes need not themselves be Nash.
   No semantic closure point is identified with an actual law profile.

3. At a cap-Nash root the larger endpoint equals the player's own mixed
   root payoff. Therefore B' is the usual expected root payoff at tail B,
   and d_i'=c d_i, E'=cE. Sure roots have c=0 and already close the proof.
   The identities are precisely the statements in
   `quittingTerminalSemanticDebt_prefix_eq_continueMass_mul_of_capNash` and
   `quittingTerminalSemanticPrefix_envelope_eq_rootSuccessorPayoff_of_capNash`
   in `UniformEquilibrium/Quitting/Root/CapNashRootStack.lean`, reopened here.

4. If all q_i are strictly between0 and1, active indifference gives

       B_i-s_i=sum_(empty!=A subset I\{i}) z_A
                         [r_i(A+i)-r_i(A)], z_i=q_i/(1-q_i).

   Summing with weights and grouping by the SAME opponent set A gives
   sum_i a_i(B_i-s_i)=sum_A z_A J_a(A)<=0. This uses outsider insertion,
   not participant withdrawal. It contradicts positive chamber surplus.
   I also reconstructed81 exact rational full-support examples at the
   witness, allowing negative input B; every identity agreed and its
   surplus was strictly negative. These finite tests supplement the proof.

5. Every remaining nonempty root support A is proper. The flat participant
   supplied by guard3 has Q_i<=s_i; supported Nash gives B_i'=Q_i<=s_i.
   Expected terminal-surplus expansion gives
   L_a(B')=c L_a(B)+sum_(nonempty S) p_q(S)H_a(S)>=cL_a(B).
   No grand-row H guard is used, because the proper root support makes
   grand probability zero. All Continue fixes the original pair.

6. At a positive chamber minimum, a strictly low cap already rules out
   all Continue, so finite Nash supplies a contracting nonzero root. In
   the remaining boundary case B>=s, the equality set L is nonempty and
   proper: if it were all I, its weighted surplus would be0, even with
   some zero weights. A sink i in its positive-insertion digraph has no
   positive insertion gain toward another label of L. The sole-i root
   with rate p gives each other player's Continue-minus-Quit difference

       (1-p)(B_j-s_j)+p[r_j({i})-r_j({i,j})].

   It is nonnegative on L, and remains nonnegative off L for sufficiently
   small p>0 by the strict initial cap gaps and finiteness. Owner i is
   indifferent. Thus this is a FULL root Nash, including every inactive
   endpoint, and E'=(1-p)E contradicts the positive minimum.

7. A zero-debt carrier pair is a diagonal. The actual sequence and one
   fixed target follow from carrier membership, not a maintained root
   spine or a correlation relaxation. I reopened
   `isUniformEquilibriumPayoff_of_diagonal_mem_terminalSemanticCarrier`
   in `UniformEquilibrium/Quitting/Classification/Existence/UniformPayoffTerminalSemanticCarrier.lean`.
   Its consumer retains ALL behavioral deviations and fixes the payoff
   before accuracy. The result is not exact terminal-Nash existence.

The argument handles weak H/J inequalities, arbitrary signed unprotected
rewards, zero weights, nonsure boundary supports, and either kind of
low-cap boundary. No global B>=0 hypothesis has crept into the theorem.

## Independent witness and stationary falsification

The raw table was reconstructed from the prose with exact Fractions.
Its (H,J) values are (1,-3) on singletons, (0,-5) on adjacent pairs,
(0,-6) on opposite pairs, and (3,-1) on triples. Its ONLY premium trap
is the full set. Its positive insertion graph is the directed4-cycle.
The actual sole-owner0 seed is exactly
U=(1,0,4,0), B=(1,2,4,0), E=2, L_a=3, lambda=3/2.

I independently checked the entire stationary exclusion, including the
boundary cases. A sure i forces its opposite to Continue because its
four pure endpoint differences are -4,-5/2,-5/2,-1. Its predecessor
then Continues (differences -1,-5/2), its successor Joins, and i strictly
withdraws. This excludes ANY sure root for ANY real continuation vector.

With no sure player, supports0/1 fail immediately. Adjacent support2
has a successor with Never0 and Quit1+a>0. Opposite support2 has Never4
and Quit1-b<1. Full support gives weighted terminal surplus>0 from its
positive singleton probabilities, whereas its odds identity is strictly
negative. For support012, active indifference and nonnegative B0 give

    1-2b-5c+(7/2)bc>=0,
    b<1/2, c<=(1-2b)/(5-(7/2)b)<=1/5.

Player1 has Q1=1-2c+a(1-c)>=3/5, but its stationary Never value is
2ac/(a+c-ac)<=2c<=2/5. Its positive hazard requires equality, impossible.
All cyclic rotations are included. Thus no exact stationary product Nash
exists, with arbitrary support/hazard choices; this does NOT exclude
stationary approximations or nonstationary sources.

## Bounded IMPLEMENTED/ACCEPTED whole-source comparison

### Entire persistent-base/free and punishment-tail sets

This is stronger than stationary exclusion. I reopened the actual finite
binary utilities and Nash-set definition in
`UniformEquilibrium/Quitting/Root/PersistentBaseInducedGame.lean`.
Every accepted base of size>=2, free induced Nash point, and omitted-player
join choice would give a FULL one-shot Nash with a sure label, which the
continuation-independent proof above excludes. This covers every mixed
selection, not just a chosen pure induced point.

For singleton bases the actual punishment values are0: Never sees only
nonnegative passive rewards, and opponents can set the successor to
Quit0 surely, giving the owner Quit=-1 and all positive deadlines/Never=0.
The FULL-complement induced Nash set for owner i is the UNIQUE point with
successor sure and opposite/predecessor Continue. Its owner payoff is-1,
its Continue value is0, and its empty-opponent probability is0. Hence its
punishment-floor excess is1, regardless of any installed punishment tail.
The exact singleton floor-excess semantics was reopened in
`singletonBase_inducedNash_floorExcess_semantics`,
`UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/LargeBaseStationarySemanticHandoff.lean`.
Punishment cannot repair the owner inequality. Arbitrary omitted-player
choices accepted by their joins again yield the already-impossible sure
root at continuation0.

For calibration, full-complement adjacent/opposite/triple bases all have
their outsiders strictly Continue. An adjacent donor has withdrawal gap-1;
opposite owners have gap-4; triple owners have gap-5/2 or-3, depending on
the remaining pair; grand owners have gap-1. Thus no larger-base exit was
missed by only inspecting singleton induced sets.

### Every universal quiet-child certificate

For ANY nonempty proper child C there is j in C with successor j+1 outside
C. Its actual sole-j-Quit0 profile is exact child Nash: predecessor joining
gives-1 instead of0, opposite joining gives0 instead of4, and the favorable
successor is absent. Every child debt is0 and child joint-Never mass is0.
In its full quiet lift the omitted successor gains2 by Quit0 instead of0.

Thus EVERY child/weight/kind choice fails a universal raw certificate whose
consumer bounds outside debt by nonnegative weighted child debts plus any
finite joint-Never residual. This includes the five-kind withdrawal F/J
families through the actual declarations
`quittingLiftDeletedProfile_outsideDebt_le_add_neverExcess_of_withdrawalFutureJoin`,
`quittingLiftDeletedProfile_outsideDebt_le_of_withdrawalFutureJoin`, and
`isεAsymptoticNash_quietLift_of_withdrawalFutureJoinFamily` in
`UniformEquilibrium/Quitting/Classification/QuietExtension/WithdrawalFutureJoinFixedTarget.lean`,
which I reopened. The same zero/zero witness applies to the capped-clock
weighted-child-debt/slack consumer. This is a WHOLE raw-certificate
exclusion, not an exclusion of a new source selecting only a favorable
particular child equilibrium.

### Whole weights, boxed charges, and stationary raw sources

The only trap is full. Summing its four singleton weighted-floor
inequalities yields -2sum weights, excluding EVERY nonzero nonnegative
floor weight. Its grand upper-average premium is8sum weights, excluding
EVERY corresponding nonzero nonnegative upper-average weight. The actual
floor and insertion/leave definitions were reopened in
`UniformEquilibrium/Quitting/Classification/WeightedQuittingTrapLeavers.lean`.

The boxed coefficient restrictions are delta<=2, tau>=8, gap<=3, loss<=1.
With the ACTUAL four-player threshold
4sqrt(delta/tau)(gap+loss*delta/tau), every choice gives at most13/2,
whereas the required singleton-plus-box charge is at least4+4*10=44.
I reopened `QuittingTrapChargeCoefficients`,
`QuittingTrapChargeCoefficients.threshold_of_cardinality_four`, and
`HasBoxedQuittingNashCharges` in `BoxedQuittingNashCharges.lean`,
`BoxedQuittingNashChargeOdds.lean`, and `BoxedQuittingNashChargeReturn.lean`
under `UniformEquilibrium/Quitting/Classification/`. There is no remaining
coefficient-selection loophole in this predicate.

The stationary exclusion rules out EVERY sound source concluding exact
stationary Nash, including any parameter selection in stationary collision
chambers. It is not being used to exclude nonstationary punishment or
calendar sources; those comparisons are separate above/below.

### Singleton, quotient, core, and named finite-calendar classes

The singleton matrix is unchanged from the paired-hard K10 matrix:
Gamma=circ(0,-1,3,-1), determinant45 and positive inverse with entries
(2,3,7,3)/15 in cyclic order. The earlier exact degree/R0 check depends
ONLY on these singleton rows: its degree is1, all deleted triple inverse
tests fail a negative diagonal, and its adjacent2x2 principal block is
not standard-Q. There is no non-Q/homogeneous singleton exit.

I recomputed the ACTUAL response polynomials H_i=(1-L_i)Q_i-b_i and tested
ALL15 partitions by exact symbolic coefficient equality, as defined by
`QuittingResponseInvariantOnUnitCube` in
`UniformEquilibrium/Quitting/Stationary/ResponseInvariantQuotient.lean`.
Only the discrete partition, opposite02|13, and all-four partition survive.
Their matrices are Gamma, [[3,-2],[-2,3]], and [1], with degree1 and
positive determinants. Thus the actual quotient favorable-degree and
negative-determinant/inverse exits do not apply; singleton block sums
alone were NOT substituted for actual response equality.

Full premium core excludes pair/triple-core hypotheses. Each participant
has a negative premium somewhere, excluding the protected nonnegative-
participant leaver assumptions; adjacent/opposite pairs fail a required
weak member join, and each triple fails the all-strict-joins premise.

Under the exact paired singleton rows the named positive proper singleton
word has uniquely golden hazards, by the independently checked difference
determinant proof printed in Section12 of
`exports/FOUR_PHASE_PASSIVE_REWARD_RAY_UNIFORM_EQUILIBRIUM.md`.
Each directed recipient premium2 exceeds the required incoming cross
bound1 in that named calendar. This rules out its entire positive proper
owner solution set, not only a chosen IFT branch. Arbitrary longer words
or boundary hazards are NOT excluded.

The earlier four-joint local/rectangle/passive-ray raw regions require
scheduled member values that these pairs do not possess: every adjacent
pair has one member-1 and every opposite pair has both members0. The
favorite singleton relation fixes the mate permutation under relabeling.
In particular the first local packet has explicit radius<=1/2 about
scheduled member values5 and9/2; the literal rectangle and passive-ray
bounds also fail. This is not a claim about unknown larger neighborhoods
of OTHER implicit-function constructions.

Finally the preexisting passive-triple cap-chamber export fixes all pair
outsider values at1. Its singleton pattern forces identity scaling and
zero translation under any recipient-affine relabeling that could preserve
the literal singleton data; the new values3/2 and2 cannot be obtained in
that way or as a limit within that fixed-row class. This syntactic fact is
only ONE comparison, supplemented above by the whole base, quiet-child,
weighted/boxed and actual stationary source exclusions.

## Scope and significance

The proof supplies a raw finite class, not merely a conditional chamber
interface. Its two raw ledgers have different jobs: H preserves the
weighted-surplus region; J excludes full-support roots at positive
surplus. Proper-subset flatness preserves a low cap, while proper-subset
acyclicity gives escape ONLY at the attained minimum. The compact invariant
minimization argument is generic; these verified raw guards and actual
seed are the producer content. No chronological return word is required.

The bounded whole-selection comparisons found no containment in the named
implemented/accepted classes above. This is evidence of additional raw
coverage, not an exhaustive theorem census or an assertion that all
nonstationary or arbitrarily long calendars fail on the witness. In fact
the new theorem proves UE there. No arbitrary-table implication is claimed:
standard-Q supplies the seed but does not supply either higher-coalition
ledger, the flatness guard, or the acyclicity guard.

## Bounded Section18.7 complete-law check

Checked source SHA256
`8a671efd1dcbfef987982703979815184cfc1856b75e3dc41daa3964bb1c5d15`.
Scope: the vulnerable cumulative-budget/complete-response step in
Section18.7, together with its running-maximum inequalities and initial
seams. This is not a full notebook or export audit.

No objection found. At the end T_(i,n) of player i's nth own phase,
the fixed opponents have survival P^(2n+i). Thus the shared constraint
forces every feasible replacement's own survival to be at most P^(n+1),
exactly the prescribed survival there. The prescribed quantile layer n
lies wholly in its own phase, where every deadline has the same payoff
w_(i,n). The replacement draw in that layer is no later than T_(i,n),
so the proved running maximum bounds its payoff by w_(i,n). This
argument checks an arbitrary COMPLETE replacement law; it does not infer
source optimality from one-stage roots. The phase-end bounds also force
replacement Never mass to zero.

The scalar estimates used here are consistent: minimality of L gives
P>=(1-delta)R>=1/2+delta, while P<=R<7/10, hence
F(P)-1=(2P-1)(1-P)>=3delta/5>=e*delta. The successor-phase identity
and predecessor-phase monotonic bound cover the intermediate deadlines.
The initial predecessor-only seam for player1 and successor/predecessor
seam for player2 have the stated first-own-phase maxima.

This supports the claimed positive shared-budget calibration on the
literal three-player table, not an arbitrary-table selector. In
particular, earlier fixed-owner or unconditional all-proper selector
falsifiers do not transfer to the whole shared-budget correspondence.

## Scoped initial Section18.19 math and producer-overlap check

This is an INDEPENDENT INITIAL check of Section18.19 only, not a full
export/novelty gate or an audit of the whole notebook. I reconstructed its
four-variable equations from the printed proper rows before comparing
the named existing paired/phase producers. No Lean command or author-note
edit was performed. The conclusions below are ordinary mathematics.

Verdict: no mathematical gap found in the local cylinder producer at
this stage. The four-variable IFT, actual-value realization, unrestricted
cap proof and arbitrary-grand assertion pass this check. Existing generic
CONSUMERS already realize this two-pair architecture once its hazards
and passive endpoints are supplied, but they do not themselves produce
those hazards throughout this cylinder. The bounded RAW producer check
did not find whole-cylinder redundancy. There IS a concrete coverage
correction: the printed two-entry perturbation witness is already covered
by the existing crossed-matching raw producer.

### Independent four-variable and cap calculation

At the literal center all participant pair entries equal own1. Thus the
four active Quit endpoints equal1, and direct evaluation gives

    V^B_0=1-u+3v-2uv,       V^B_2=u(4-3v),
    V^A_1=1-x+3y-2xy,       V^A_3=x(4-3y).

These give precisely the four printed equations18.56. I independently
computed their full Jacobian in variable order(x,y,u,v) and equation
order(Phi_0,Phi_2,Phi_1,Phi_3). At(a,b,a,b), subtraction of rows2 and4
gives3a^2(dy-dv); subtraction of rows1 and3 gives

    b(1+2b)(dx-du)+(1-a)(dy-dv).

So every kernel vector is symmetric. The remaining two-variable
Jacobian is D(f,g), where f=b(1-a+3b-2ab)-1 and
g=a^2(4-3b)-1. Direct algebra gives BOTH identities

    f(a,(4a^2-1)/(3a^2))=(1-a)P(a)/(9a^4),
    det D_4 Phi=3a^2 b(1+2b) det D(f,g).

Since P(a)=0 and the source's exact isolating interval has P'(a)>0,
det D(f,g)=-(1-a)P'(a)/(3a^2)<0. The full determinant is nonzero,
with precisely the printed positive multiplicative factor. This is a
four-variable check, not an inference from a symmetric slice alone.

For arbitrary nearby proper rows, the displayed eight candidate value
coordinates and four active equations are polynomial. The active
equations make the four remaining Bellman coordinates hold; the inactive
ones are definitions. The full two-phase recursion has unique bounded
solution because xyuv<1, so these are actual values, not independently
supplied continuations. Ordinary IFT therefore selects all four coins
smoothly for all fifty-six independent proper-row parameters, even though
some coordinates are unused by the equations. Shrinking one common box
retains the proper coins and all strict inactive inequalities.

The center's inactive forced-Quit expectations at phase A are exactly
x+y-xy for player1 and1 for player3, giving the printed gaps against
1/b and1/a; phase B has the analogous two values. Thus all eight root
inequalities, not only the active equations, persist.

Under an arbitrary complete one-player replacement, at most three
players can Quit at any date: only two opponents can be prescribed
active at a phase. The grand coalition is consequently absent from
EVERY prescribed and deviating endpoint, not merely absent from the four
equations. Each deleted opponent set has a positive prescribed hazard
at every phase and its survival contracts by at least7/8 per date.
Finite Bellman iteration therefore controls an arbitrary entire
behavioral replacement with a residual tending to0 geometrically,
including Never. The selected prescribed values equal the full caps.
This justifies exact terminal Nash at both phases and the same-profile
fixed-target uniform conclusion; local root Nash alone would not do so.

The N_delta membership also checks: each date has joint survival at
most49/64, so its cumulative survival meets the original shared budget
for every0<delta<=15/64. Full Nash implies optimality in the smaller
budget-feasible replacement set. No new global minimum selection follows.

### Actual overlap: the two-entry witness is already a raw source

Let only r_0(02)=r_2(02)=1+epsilon change, with epsilon>0, as printed
in Section18.19. For the existing schedule02|13, the favorite involution
is(0 1)(2 3), scheduled partners are(0 2)(1 3), and the other partners
are(0 3)(1 2). All singleton favorite rewards are4>own1, scheduled and
other singleton rewards are0<1. Every scheduled pair reward exceeds
its scheduled singleton0. Every off-schedule participant pair reward
is still1, and every off-schedule joining triple reward is0 or1.

These are EXACTLY every field of
`PairedCycle.CrossedMatching.RawSource` in
`UniformEquilibrium/Quitting/Cycles/CrossedMatchingPhaseSource.lean`.
Its `exists_uniformEquilibriumPayoff` therefore already covers that whole
two-entry family, for EVERY grand row. This example loses proper-flatness
but is not a new UE coverage witness. Nor would replacing its producer
proof by a four-variable IFT change that fact.

### Bounded whole-cylinder comparisons and a corrected test direction

The following checks are against complete named producer selections,
not against one numerical root or distance from a theorem's center.

1. `PairedCycle.RawRegion`, including all schedules and positive
   recipient-affine images, does NOT contain the center. Every recipient
   has TWO below-own singleton quitters, whereas
   `RawRegion.eq_partner_of_singleton_lt` permits only its unique partner.
   These strict signs persist under the proposed small proper-row changes.
   Consequently `exists_exact_allSuffix_uniformPayoff_of_rawRegion`,
   its open-region/affine entrances, and the generic paired cleared-field
   interval construction do not already give the whole cylinder.

2. The crossed-matching sources do cover the center and the preceding
   two-entry direction, but NOT a full open cylinder. For an explicit
   improved test, change only

       r_0(02)=1+epsilon, r_2(02)=1+epsilon,
       r_0(03)=1+epsilon,

   keep EVERY other entry equal to the boundary table, and take epsilon
   arbitrarily small and positive. Player0 now has TWO participant pair
   rewards above own1. Every pair partition leaves one of these pairs
   off-schedule, violating its necessary own-singleton joining cap.
   This excludes ALL `RawSource`, `WeakRawSource`, `InverseRawSource`
   and `ScheduledPairCapSource` choices, and the stricter off-schedule
   caps in `PairedCycle.BelowSingleton.RawFamily`. The strict surplus
   obstruction is invariant under positive recipient-affine membership
   transport and relabeling. The IFT producer still supplies the actual
   exact equilibrium for this three-entry perturbation. Its pair02 also
   has no flat participant.

3. The below-singleton full-table neighborhood is not merely at a
   different numerical center: its conclusion
   `HasBelowSingletonExactProfile` requires every phase coordinate to be
   STRICTLY below its own singleton. On the boundary AND the three-entry
   perturbation, all participant pair rewards are at least own1.
   In any proper two-pair schedule each active Quit endpoint is therefore
   at least1. Active indifference makes its actual active-phase value
   at least1 as well. Hence NO such below-singleton profile exists there,
   regardless of that neighborhood's unquantified radius or relabeling.
   This rejects the conclusion of `exists_reward_supnorm_radius` itself,
   not merely literal membership in its special raw family.

4. `PairedCubicStationaryExample.exists_local_stationary_branch` and
   any other entrance concluding an exact stationary product Nash cannot
   cover the boundary's fixed stationary-gap point. For the preceding
   three-entry perturbation with original grand(-1,-1,-1,-1), choose
   epsilon below a quarter of that gap. Uniform reward robustness leaves
   a positive gap for EVERY stationary profile. Thus the same exact
   nonstationary witness lies outside those entire stationary selections;
   no assumption about their numerical neighborhood radii is needed.

5. `PairedCollisionReward.exists_uniformEquilibriumPayoff` covers the
   existing one-parameter table, but not this three-entry direction.
   Its literal family has the SAME parameter c in ALL twelve participant
   pair entries. The perturbed row0 has participant pair entries
   1,1+epsilon,1+epsilon, which cannot be made constant by relabeling.
   For positive recipient-affine images, the unchanged singleton lows0
   and owns1 force each shift0 and scale1; favorite4 forces the same
   favorite matching. Thus such images cannot repair the discrepancy.

The conditional `twoPair_exact_terminal_and_fixedProfile` is a sound
existing consumer for supplied proper hazards and passive endpoint tests.
It is not, without an existence theorem supplying those hazards, a raw
producer of the whole cylinder. The Section18.19 IFT calculation supplies
precisely that missing local synthesis. No arbitrary-table or all-calendar
completeness is being claimed.

### Named source scope and disposition

The bounded source route was the maintained paired/phase entries in
docs/TOOLKIT.md, followed by these actual files/declarations:

- `periodTwoPolynomial_strictMonoOn`,
  `exists_periodTwoParameter_mem_isolatingInterval` and the endpoint/profile
  declarations in
  `UniformEquilibrium/Quitting/Examples/BlockPair/FourPlayerPairedSingletonPeriodTwo.lean`;
  `boundaryReward` and the fixed stationary exclusion in
  `UniformEquilibrium/Quitting/Examples/SolanVieilleBoundaryTable.lean` and
  `UniformEquilibrium/Quitting/Examples/SolanVieilleBoundaryNonstationarity.lean`.
- `RawRegion.eq_partner_of_singleton_lt` in
  `UniformEquilibrium/Quitting/Cycles/PairedCycleSchedule.lean`;
  the literal `OwnBounds`/`PassiveBounds` in
  `MathUE/PairedAffineIntervalEstimates.lean`;
  `centerReward` and the raw/open/affine entrances in
  `UniformEquilibrium/Quitting/Cycles/PairedCycleRegionCenter.lean`,
  `PairedCycleOpenRegion.lean` and `PairedCycleAffineEquilibrium.lean`.
- The four crossed/matching raw source structures in
  `UniformEquilibrium/Quitting/Cycles/CrossedMatchingPhaseSource.lean`,
  and `RawFamily` in `BelowSingletonJointPhaseSource.lean`.
- `twoPairActiveValue`, `twoPairPostValue`, `twoPair_policy_and_nash`
  and `twoPair_exact_terminal_and_fixedProfile` in
  `UniformEquilibrium/Quitting/Cycles/TwoPairExactCertificate.lean`.
- `exists_local_odds_branch`, `HasBelowSingletonExactProfile` and
  `exists_reward_supnorm_radius` in
  `UniformEquilibrium/Quitting/Examples/BelowSingletonJointPhaseLocalPersistence.lean`;
  `exists_local_stationary_branch` in
  `UniformEquilibrium/Quitting/Examples/BlockPair/PairedCubicLocalPersistenceStrategic.lean`.
- `reward` in
  `UniformEquilibrium/Quitting/Examples/BlockPair/PairedCollisionRewardTable.lean`,
  its scalar `PeriodicRates` producer in `PairedCollisionRewardPeriodic.lean`,
  and its all-parameter existence theorem in `PairedCollisionRewardExistence.lean`.

A narrow local-persistence/implicit-function search in the chosen Cycles
and BlockPair subtrees found the fixture-specific below-singleton and
stationary neighborhoods, not an already generic center-parametrized
theorem that supplies this boundary cylinder. This is a bounded finding,
not proof of noncoverage by every accepted packet, unknown large implicit
neighborhood, longer phase producer or other verifier. No full export
gate was attempted. The existing two-entry witness should be relabeled
as calibration, and the three-entry direction is available if a later
focused complete coverage gate is requested.
