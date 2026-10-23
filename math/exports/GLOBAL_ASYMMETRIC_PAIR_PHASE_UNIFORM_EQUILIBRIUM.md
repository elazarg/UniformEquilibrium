# A global alternating-pair producer with asymmetric joining premiums

## 1. Exact statement

There are four players I={0,1,2,3}, with indices read modulo four.
At every live date each player independently chooses Continue or Quit.
The first nonempty quitting coalition S absorbs at the finite reward
vector r(S). Live stages and perpetual continuation pay zero. A unilateral
deviation may replace the player's entire behavioral strategy, including
any finite stopping date, Never, and arbitrary private mixtures. No public
randomization or correlated device is available.

Partition I into A={0,1} and B={2,3}. Write m(i) for i's other member
of its pair, and O(i) for the other pair. Choose finite real parameters

    a>2b>0,       0<=e<c<=a/2,       M in R.

Define a normalized reward table Z on nonempty coalitions by the following
finite equalities and inequalities:

    Z_i({i})=0,
    Z_i({m(i)})=a,
    Z_i({j})=-b                         (j in O(i)),

    Z(01)=(a+c,a+e,M,M),
    Z(23)=(M,M,a+c,a+e),

    Z_i({i,j})<=-b+c*1[j=i+1]           (j in O(i)),
    Z_i({i} union O(i))<=M-2c           (i=0,2),
    Z_i({i} union O(i))<=M+c            (i=1,3).

Here 01 denotes {0,1}, and similarly for other displayed coalitions.
The last three lines impose twelve caps: eight pair coordinates and
four triple coordinates. Every other nonsingleton coordinate is an
arbitrary finite real number. There are twenty-four such free coordinates,
since there are forty-four nonsingleton coordinates, eight exact
scheduled-pair entries and twelve capped coordinates. In particular,
grand-coalition and passive-triple rewards are unrestricted.

Finally choose arbitrary finite offsets mu_i in R and positive scales
lambda_i, and set

    r_i(S)=mu_i+lambda_i Z_i(S)         (S nonempty).

Live and Never still pay zero. The theorem concerns this original table r.

**Theorem.** Every table in this raw class has an exact terminal Nash
profile against all complete unilateral behavioral replacements. The
profile is proper and period two: players 0,1 act at one phase, players
2,3 at the other, and all coins are independent. Every deleted-opponent
family has a geometric absorption tail. One fixed actual terminal value
is a uniform-equilibrium payoff of r; the same profile supplies every
positive accuracy at all sufficiently long finite horizons.

The inputs are the finite reward comparisons above. No strategy, selected
nonlinear zero, hazard, continuation value or payoff target is assumed.
All conclusions are ordinary mathematics; no new Lean theorem is claimed.

There is also a full-dimensional conclusion, proved in Section 8. Let R
be the complete table (11) with a=3, b=3/5, c=9/26 and M=3/20,
and put Rplus_i(S)=1+R_i(S) for every nonempty coalition. Every raw
table r with

    max_(i,S nonempty)|r_i(S)-Rplus_i(S)|<=1/1000000

has the same exact-terminal and fixed-uniform conclusions. All sixty
coordinates, including the own singletons near one, vary independently.
Its four hazards are produced within distance 1/1000 of
(1/4,1/2,1/4,1/2). This second theorem assumes none of the exact
singleton or scheduled-row equalities of the first class.

## 2. Strategic inputs and probability mode

Before absorption the only public live history is repeated all Continue.
A behavioral strategy therefore induces a private law on natural stopping
dates plus Never. Independent private seeds induce independent clocks.
A complete unilateral replacement is an arbitrary replacement of one
clock law. Its terminal payoff is affine in that law, so it suffices to
bound every finite pure deadline and literal Never. The proof below does
this without assuming that a response supremum is attained.

The two phases are deterministic calendar dates. The choice of their
hazards uses only the raw reward parameters and occurs before accuracy
is chosen. The construction supplies all four hazards, both phase-value
vectors, all root incentives and all absorption bounds. There is no
recursive call requiring another strategic witness.

## 3. A global producer for every passive pair reward

Put d=a/c>=2 and g=e/c in [0,1). For each k in (0,1), put
B=1-k and D=(1-g)k. There is a unique rho in (0,1) satisfying

    H_g(rho)=rho^2(1-k+k rho)^2[d(1-k)+1-gk]
                    -[(1-k)+(1-g)k rho]=0.                    (1)

Indeed H_g(0)=-B<0 and H_g(1)=dB>0. The function

    rho^2(1-k+k rho)^2/(B+D rho)

is strictly increasing on (0,1): its logarithmic derivative is

    2/rho+2k/(1-k+k rho)-D/(B+D rho)>0,

because D/(B+D rho)<1/rho. Equation (1) therefore has exactly one
root, with nonzero derivative. The ordinary implicit function theorem,
or uniqueness and compactness of roots, gives continuous dependence on k.
Define

    y=1-rho,       x=k y,
    C=(1-x)(1-y)=rho(1-k+k rho).

Then 0<x<y<1. Dividing (1) by positive factors and substituting these
definitions gives exactly

    C[(a+c)y-(a+e)x]
                    =c y/(1-y)-e x/(1-x).                    (2)

For clarity, after division by c y equation (2) reads

    C[d(1-k)+1-gk]=1/rho-gk/(1-k+k rho).

Multiplication by rho(1-k+k rho)=C is precisely (1).

We next obtain a lower bound that holds throughout this whole branch.
Let m=1/sqrt(1+d). Evaluate the same expression at g=1, retaining the
actual rho and k. Its algebraic form is

    H_1=(1-k)[(d+1)C^2-1].

At a root of H_g,

    H_1-H_g=(1-g)k(rho-C^2)>0,                              (3)

since C=rho(1-k+k rho)<rho<1. Consequently

    C>m>1/d=c/a>=c/(a+e).                                   (4)

The middle strict inequality follows from d>=2, hence d^2>d+1.

Consider the continuous raw parameter map

    M(k)=[b(k+1)+e k/(1-ky)-(a+e)k C]/(k y)-2b.              (5)

As k tends to zero, (1) gives rho tending to m. Thus y has a positive
limit and the numerator in (5) tends to b>0: M(k) tends to +infinity.
As k tends to one, (4) keeps rho bounded away from zero. Every limit
of (1) satisfies (1-g)(rho^4-rho)=0. Because g<1 and rho>0, necessarily
rho tends to one. Hence y tends to zero, C tends to one, and the
numerator in (5) tends to

    2b+e-(a+e)=2b-a<0.

Thus M(k) tends to -infinity. The intermediate value theorem supplies
a k for the given finite M. Choose one such k once, and retain its x,y.
No monotonicity or uniqueness of this final k selection is required.
Equation (5) is equivalent to

    P=-b(x+y)+(M+2b)xy
      =e x/(1-x)-C(a+e)x.                                   (6)

This proves a global producer on the entire real M axis, including
positive, zero and negative passive pair rewards.

## 4. Every phase endpoint, including simultaneous deviations

At phase A, players 0 and 1 independently Quit with probabilities x,y;
players 2 and 3 Continue. At phase B, players 2 and 3 use x,y and
players 0 and 1 Continue. Repeat after all Continue. Define

    vA=((a+c)y,(a+e)x,c y/(1-y),e x/(1-x)),
    vB=(c y/(1-y),e x/(1-x),(a+c)y,(a+e)x).

We verify the two pure action endpoints of every player at each phase,
with continuation vB after A and vA after B.

In phase A, player 0's Quit value is (a+c)y. Its Continue value is

    a y+(1-y)vB_0=a y+c y=(a+c)y.

Player 1's Quit value is (a+e)x. Its Continue value is

    a x+(1-x)vB_1=a x+e x=(a+e)x.

Thus both active players are indifferent at the displayed values.

Each inactive player's immediate passive payoff is P from (6), with
the term Mxy retaining the event that both scheduled opponents Quit.
Their Continue endpoints are

    P+C vB_2
       =e x/(1-x)+C[(a+c)y-(a+e)x]=vA_2,
    P+C vB_3=e x/(1-x)=vA_3,                              (7)

by (2) and (6). Player 2's Quit endpoint is at most P-2cxy:
its two singleton-opponent outcomes have no favorite bonus, while
the triple reward is at most M-2c. Its Quit-minus-Continue gap is at most

    -2cxy-C(a+c)y<0.                                      (8)

Player 3's Quit endpoint is at most P+cx. Its favorite is player 0;
the pair cap adds at most c when only 0 quits, and the triple cap adds
at most c when both quit. Their total probability is x. Its gap is at most

    x[c-(a+e)C]<0                                         (9)

by (4). Rotation by two labels proves the four corresponding comparisons
in phase B. These are all sixteen pure endpoints. Every prescribed
mixture uses maximizing actions and gives the exact policy recursion.

No unspecified coordinate has been discarded in this calculation.
An active deviator faces at most one possible quitter. An inactive
deviator faces exactly the scheduled pair, whose joint event is included
in (7)--(9). A unilateral replacement cannot create a grand coalition,
and the deviator's own reward is never a passive triple. Thus all
twenty-four free coordinates really are unused under every unilateral
replacement from this support schedule.

## 5. Actual values and unrestricted behavioral caps

The joint survival probability per period is C^2<1. Iterating the
policy recursion for n periods leaves a bounded continuation multiplied
by C^(2n), which tends to zero. Hence vA,vB are the actual terminal
policy values, not arbitrary continuation vectors.

Deleting player 0 or 2 leaves opponent survival per period (1-y)C<1;
deleting player 1 or 3 leaves (1-x)C<1. These contractions are independent
of the deviator's entire replacement law.

Fix a pure finite deadline. At every earlier date the Continue equation
preserves the relevant phase value, and at the final date the Quit
endpoint is at most that phase value. Iteration proves its terminal
payoff is at most the initial value. For literal Never, iterate Continue
forever. The bounded remainder is multiplied by the deleted-opponent
survival product and vanishes, so Never earns exactly the initial value.
The prescribed finite atoms occur only at active maximizing phases and
its clock is almost surely finite. Its payoff is exactly the same value.
Affinity now bounds every mixed law and therefore every complete
behavioral deviation. In normalized coordinates U_i=B_i=v_i.

Every unilateral replacement still absorbs almost surely because its
opponents do. Therefore transforming normalized rewards by mu_i+lambda_i
times the normalized reward transforms every actual response payoff and
prescribed payoff by that same affine formula. There is no contribution
from a residual joint-Never event. Since lambda_i>0, all Nash comparisons
are preserved for arbitrary signed offsets mu_i. The original table's
actual values are

    uA_i=mu_i+lambda_i vA_i,
    uB_i=mu_i+lambda_i vB_i.                               (10)

This argument does not translate the live payoff or assert affine
invariance for profiles with positive joint-Never probability.

For the finite-horizon claim, let R bound the absolute original rewards.
Under any unilateral replacement, absorption occurs no later than the
first opponent Quit. Its mean time is uniformly finite by the relevant
geometric contraction. The difference between the terminal payoff and
the N-stage average payoff is bounded by R times this mean, with an
inessential date-index constant, divided by N. This bound is uniform
over all unilateral behavioral deviations and also applies to the
prescribed profile. Exact terminal Nash implies finite-horizon gains
are O(1/N), while prescribed averages converge to (10). The single target
uA is fixed before accuracy, and the same profile works at every accuracy.

## 6. A literal completion with no absorbing one-date equilibrium

The following complete table is a useful global test of the producer.
Take e=0 and the same a,b,c,M. For each recipient i, first define its
passive reward on opponents' coalitions by

    F_i(empty)=0,
    F_i({m(i)})=a,
    F_i({j})=-b                      (j in O(i)),
    F_i(T)=M                        (T subset I\{i}, |T|>=2).

For any nonempty opponent coalition T put Z_i(T)=F_i(T). For any
coalition containing i, including the own singleton, set

    Z_i({i} union T)
      =F_i(T)+c[1[i+1 in T]-2*1[{i+2,i+3} subset T]].       (11)

This specifies all sixty entries. Its scheduled rows and twelve caps
are exactly those in Section 1, with equality at the caps. For instance,
an even recipient's opposite pair gives increment -2c, while an odd
recipient's opposite pair gives increment +c. The grand reward is M-c
in each row. The theorem thus provides an actual absorbing equilibrium
for every such completion and every real M.

We classify all one-date root/Never equilibria directly. With root Quit
probabilities q_i and continuation payoff zero, player i's immediate
Quit-minus-Continue difference is

    c N_i(q),      N_i(q)=q_(i+1)-2q_(i+2)q_(i+3).          (12)

At equilibrium, q_i=0 requires N_i<=0, q_i=1 requires N_i>=0,
and 0<q_i<1 requires N_i=0. If zeros and positive coordinates coexist,
there is a cyclic transition q_j>0, q_(j-1)=0. The inactive predecessor
has N_(j-1)=q_j-2q_(j+1)q_(j+2)<=0, so q_(j+1),q_(j+2)>0.
The active player j+2 has next coordinate q_(j+3)=q_(j-1)=0,
and its other two opponents j,j+1 are positive. Thus

    N_(j+2)=-2q_j q_(j+1)<0,

contradicting q_(j+2)>0. Every nonzero equilibrium has all coordinates
positive.

There can be no unit coordinate. Rotate labels to q_0=1. Since every
player is active, all four N_i are nonnegative. The inequalities N_1>=0
and N_2>=0 give q_2>=2q_3>=4q_1. The inequality N_0>=0, together
with q_3>=2q_1>0, gives q_2<=1/4. Hence q_3<=1/8 and q_1<=1/16.
Players 1,2,3 are proper, so N_3=0. However

    N_3=1-2q_1q_2>=1-1/32>0,

a contradiction. Thus a nonzero equilibrium is entirely proper, and
N_i=0 for every i. Put z_i=log(2q_i). The equations become
z_(i+1)=z_(i+2)+z_(i+3). Their sum gives sum_i z_i=0, whence
2z_(i+1)=-z_i. Iterating four times gives z_i=z_i/16, so every z_i=0.
Consequently the only root/Never Nash profiles are AllNever and
q=(1/2,1/2,1/2,1/2). The latter has joint Never probability 1/16
and value M/2+(a-2b)/8 in each row. Neither profile absorbs surely.
In particular, the completion has no absorbing one-date mixed equilibrium.

It also has no exact sole-owner geometric equilibrium, at any hazard
z in (0,1]. Such an equilibrium with owner k and all others Never
would require, for every observer h,

    z Z_h({h,k})<=Z_h({k}).                                (13)

This follows directly from the observer's date-zero Quit comparison;
the converse follows by summing the same geometric replies. If the
favorite predecessor h=k-1 is a cross recipient, its passive reward is
-b and joining reward -b+c. Condition (13) is impossible for z<=1:
if -b+c>=0 the left side is nonnegative, and otherwise it exceeds -b.
If that predecessor is the positive mate, (13) requires
z<=a/(a+c)<1. A cross recipient has joining reward equal to its passive
reward -b and instead requires z>=1. These cases cover all four k.

The period-two producer therefore gives a global consumer after every
absorbing one-date and sole-owner geometric exit has been removed.
This is not a claim that the table has no general stationary equilibrium.

The positive-own table r_i(S)=1+Z_i(S) also has no absorbing one-date
full Nash profile. To see this, suppose a root q followed by Never
absorbs surely. In each row compare Quit now with Continue and then
forced Quit at the next date. Both of these pure responses absorb
surely, and their difference is exactly c N_i(q): the constant offset
one cancels. The prescribed root action, on its positive-probability
support, must maximize these two options at a full Nash profile. Since
the prescribed play absorbs surely, its Continue branch has no residual
Never contribution. Thus the same conditions on N_i used above are
necessary. The classification rules out any absorbing root. AllNever
itself is not an equilibrium in this positive-own table, because an
immediate lone quitter earns one. The normalized own-zero table has
the trivial nonabsorbing AllNever equilibrium; its stronger absorbing
construction alone is not evidence of a new UE existence class.

## 7. Exact source correspondence and complete selection comparisons

The new mathematical content is the raw producer (1)--(6), its global
survival bound and its twelve-cap adapter. The exact periodic consumer
already exists as
`isZeroAsymptoticNash_quittingCyclicBehaviorProfile_of_certificate` and
`isUniformEquilibriumPayoff_quittingCyclicTerminalValue_of_certificate`
in `UniformEquilibrium/Quitting/Cycles/PeriodicCompiler.lean`.
Their inputs are exact policy recursion, exact root Nash at every phase,
and a strictly contracting opponent-cycle product for every player.
Sections 4--5 supply all three for the actual raw table. The second
declaration supplies one fixed uniform target. No new producer instance
or theorem is asserted to have been checked in Lean.

The following comparisons concern full selection sets of the named
criteria. A permutation of players merely permutes the calculations.
Positive recipient scaling preserves every indicated sign or ordering,
and recipient offsets cancel in differences from the own singleton.
Thus the exclusions also hold under canonical positive row-affine maps.

### 7.1. Full inverse positivity does not invoke a general producer

The normalized singleton matrix is

    Gamma=[[0,a,-b,-b],
           [a,0,-b,-b],
           [-b,-b,0,a],
           [-b,-b,a,0]].

Its determinant is a^2(a^2-4b^2)>0. Its inverse has diagonal,
mate and cross entries respectively

    2b^2/[a(a^2-4b^2)],
    (a^2-2b^2)/[a(a^2-4b^2)],
    b/(a^2-4b^2),

all strictly positive. Existing standard-Q, R0 and degree consequences
of positive inverse matrices do not by themselves produce an equilibrium
for arbitrary higher rewards. For example,
`r0Degree_eq_sign_det_of_nonnegative_inverse`
in `MathUE/LinearProgramming/NonnegativeInverseDegree.lean` supplies
the minimum-map degree, rather than an arbitrary-table strategy.
The positive-inverse reward producers require additional higher-reward
guards, which must still be checked.

### 7.2. All proper triples fail the passive-row inverse test

Every proper triple, after permutation, has matrix

    T=[[0,a,-b],[a,0,-b],[-b,-b,0]],
    T^-1=[[-1/(2a),1/(2a),-1/(2b)],
           [1/(2a),-1/(2a),-1/(2b)],
           [-1/(2b),-1/(2b),-a/(2b^2)]].

Thus no triple inverse is entrywise nonnegative. Its outside row is
(-b,-b,a), and the inverse weight equals

    (-a/(2b),-a/(2b),1-a^2/(2b^2)),

which is strictly negative in every coordinate. This rejects all four
child selections in
`exists_labeledCycle_uniformPayoff_of_raw_strictInverse_triple` and
`exists_uniformEquilibriumPayoff_of_raw_nonnegativeInverse_triple`
in `UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/RawPassiveRowInverseCriterion.lean`.
These are raw sufficient conditions; their failure is not a general
nonexistence result for all proper-child strategies.

### 7.3. All ordered-pair raw regions fail

`RawRegion.eq_partner_of_singleton_lt`
in `UniformEquilibrium/Quitting/Cycles/PairedCycleSchedule.lean`
shows that in its implemented ordered-pair raw region every singleton
strictly below a recipient's own singleton must belong to that
recipient's one partner. Our table has two such singleton columns in
every recipient row. Consequently no pairing, ordering, relabeling or
positive row-affine map puts this class in that raw region. This
comparison does not reject the general periodic compiler, whose inputs
we explicitly produce.

### 7.4. Signed inverse columns: all signs and all three partitions

The signed-inverse two-phase raw criterion requires signs sigma_i
such that Gamma^-1 diag(sigma)>0, strictly signed joining increments
sigma_i[r_i({i,m(i)})-r_i({m(i)})]>0, and nonpositive signed passive
pair rewards sigma_i[r_i(O(i))-r_i({i})]<=0. Strict inverse positivity
forces every sigma_i=+1, under every permutation and positive row scale.

In the positive scheduled partition 01|23, the four joining increments
are c,e,c,e. At e=0 strictness fails. At e>0 and M>0 the passive pair
condition fails in all rows. In either cross partition, recipient 0's
scheduled mate is 2 or 3 and its joining increment is at most zero:
its favorite is 1, so its cap is -b, equal to the passive singleton.
Hence strictness fails there for every e,M and completion. Thus the
entire M>0 class fails this criterion over all three partitions and all
sign choices, not just at the displayed schedule.

### 7.5. Proper-flat and own-level joining criteria

A graph-free H/J-flat existence criterion requires that every nonempty
proper player set A have a participant i such that every coalition
inside A containing i pays that participant at most its own singleton.
For A={0,1}, both participants have strictly positive scheduled-pair
premiums a+c and a+e. Thus this guard fails, independently of any
choice of nonnegative H/J weights and for every completion in our class.

The two-pair own-level joining criterion requires, for some partition,
every inactive pair and triple reward to be at most the own singleton.
Some low completions of our upper-cap class can satisfy this condition;
no disjointness of the whole class is claimed. However the literal
completion (11) with M>0 fails it in every partition. At 01|23 an odd
recipient's inactive triple is M+c>0. At either cross partition the
opposite-pair joining tests for recipient 0 include Z_0(01)=a+c>0.
The crossed-matching criterion shares these own-level caps, so it also
fails on the same literal completion in every partition.

### 7.6. Whole sure-owner faces and stationary raw guards

The following tests concern the literal completion (11). Its exact
joining difference on an opponent set T is the displayed cyclic vertex
expression c[1[i+1 in T]-2*1[{i+2,i+3} subset T]]. This makes whole
upper-face tests particularly transparent.

`QuittingWeakUnitJoining`
in `UniformEquilibrium/Quitting/Stationary/OneSidedWeakUnitRawGuards.lean`
requires, for one ordered recipient i and partner j, that adding i never
raises i's reward on any opponent coalition containing j. It fails for
every one of the twelve ordered selections. If j=i+1, choose opponent
set {j}; its joining difference is c>0. Otherwise choose {j,i+1};
its joining difference is again c>0. These are legitimate outsider
subsets of the required sure-partner face. Thus
`exists_uniformPayoff_of_oneSidedWeakUnitRawGuards`
in `UniformEquilibrium/Quitting/Stationary/OneSidedWeakUnitProducer.lean`
cannot use any ordered selection on this completion. This does not
assert failure of all stationary equilibria.

Likewise `IsQuittingInstantNoJoin`
in `UniformEquilibrium/Quitting/Punishment/InstantPunishment.lean`
requires that no observer gains by joining the selected sure quitter.
For each candidate quitter j, its cyclic predecessor i=j-1 has joining
difference c>0. Hence every selected owner fails this necessary root
comparison, regardless of the off-path punishment tail. The exact
sole-owner geometric criterion in
`isεAsymptoticNash_soloStationary_exact_iff`
in `UniformEquilibrium/Quitting/Punishment/OwnerSoloCertification.lean`
is independently excluded by (13). These tests cover every owner and
every punishment law for these particular root mechanisms.

For another endpoint raw guard, a positive singleton joining difference
followed by a negative two-opponent joining difference on a set containing
that singleton cannot occur: positivity forces singleton i+1, and every
two-opponent set containing i+1 still has difference +c. A scalar endpoint
guard requiring an above-own passive singleton and a negative joining
difference there also fails: the only above-own singleton is the paired
mate, and its joining difference is c or zero. These are entire finite
selection exclusions, independent of M and of the recipient offsets.

### 7.7. Weighted, support and fixed-phase comparisons

Several finite raw guards are ruled out by short complete computations
on (11). For any nonnegative recipient weights w, the singleton insertion
sum at S={j} is exactly

    sum_(i!=j) w_i[Z_i({i,j})-Z_i({j})]=c w_(j-1).

Thus requiring all four such sums to be nonpositive forces every weight
to vanish. In particular no nonzero nonnegative weighting passes a
guard imposing nonpositive insertion on every proper coalition. The
unweighted full-support singleton insertion sum is c>0.

Every recipient has some negative participant premium: its nonfavorite
cross pair pays -b below own. Both disjoint mate pairs are premium traps,
meaning that every participant in each pair has a coalition inside that
pair paying it strictly above own. The union is therefore a full
four-player premium trap. A guard requiring a nonpositive weighted
participant upper bound on either mate pair cannot use nonzero
nonnegative weights, because its two participant premiums are both
strictly positive. A guard requiring a proper residual premium core
also cannot use this completion. Within any proper triple, the strictly
positive singleton-joining graph is only the induced part of a directed
four-cycle. It is never the complete directed graph; thus no selection
has all six ordered pair-joining increments strictly positive.

Fixed phase families also have literal sign and ordering tests. The
canonical affine chart sending own to one and both negative passive
singletons to zero is unique: u_i=1+Z_i/b. Its positive mate singleton
is 1+a/b. A family requiring that singleton to be four can therefore
match only a/b=3. In that case the even mate participant reward is
4+c/b>4. Consequently a fixed mate-participant reward bounded by
(5+sqrt(5))/2, or required strictly below four, cannot match any
canonical chart. Any phase family requiring a strictly negative
singleton joining increment at a scheduled cross pair also fails:
every literal cross increment is zero or +c. At every cross pair
one member is a nonfavorite recipient whose participant premium is
-b<0, ruling out a raw cross-pair row that puts both members strictly
above own. Equal-member mate rows fail because c>e. Finally the positive
singleton graph is exactly two disjoint transpositions, and cannot be
relabelled into a directed positive four-cycle or a positive tournament.

All these calculations are invariant under arbitrary recipient offsets
and positive scales when stated as signs of own/passive differences.
They exclude the complete indicated finite selections; they do not
assume that an arbitrary completion under the twelve caps has the
cyclic joining differences of (11).

### 7.8. Bounded meaning of the comparisons

The preceding exact exclusions show why neither a supplied periodic
verifier nor full inverse positivity alone provides the new raw result.
They are comparisons with the complete indicated selection sets. They
do not assert absence of every stationary equilibrium, every punishment
tail, or every other raw sufficient condition. In particular, sparse
large-jackpot existence theorems have additional higher-reward size
conditions and thresholds; no pointwise failure of their entire
existential scale choices follows merely from a different reward shape.
No such pointwise noncoverage claim is used in the proof.

## 8. An explicit open box in all sixty reward coordinates

Let R be the full table (11) with a=3, b=3/5, c=9/26 and M=3/20,
and put Rplus_i(S)=1+R_i(S) for every nonempty S. No center entry is
left free. Suppose the actual raw input r obeys

    max_(i,S nonempty)|r_i(S)-Rplus_i(S)|<=eta=1/1000000.    (B2)

The producer below constructs four hazards in the closed cube

    |q-q*|_infinity<=rho=1/1000,
    q*=(1/4,1/2,1/4,1/2).                                 (B3)

All sixty entries, including own singletons near one, vary independently.
There is no assumed strategic root or nonquantitative neighborhood size.
The same proof also holds around R itself or after any fixed real
recipient offsets, because the displayed coefficient differences cancel
those offsets and all prescribed/deviating profiles absorb surely.

### 8.1. Four-hazard equations from the actual table


For each i put s_i=r_i({i}), let m=i xor 1, and let {j,k} be the opposite
scheduled pair. Normalize only the absorbing coordinates by subtracting
s_i. Define from the actual input

    Gamma_il=r_i({l})-s_i,
    Pi_i=r_i({i,m})-s_i,
    K_i=r_i({j,k})-s_i,
    c_i=Pi_i-Gamma_im=r_i({i,m})-r_i({m}).

For q in (0,1)^4 set C_i=(1-q_j)(1-q_k) and

    F_i(r,q)=c_i*q_m/(1-q_m)
       -Gamma_ij*q_j*(1-q_k)-Gamma_ik*q_k*(1-q_j)
       -K_i*q_j*q_k-C_i*Pi_i*q_m.                          (B4)

No continuation value is an input. Given a zero of F, define the values
before i's active phase and its inactive phase respectively by

    U_i=s_i+Pi_i*q_m,
    W_i=s_i+c_i*q_m/(1-q_m).                               (B5)

Active Quit has value U_i. Active Continue has value

    q_m*(s_i+Gamma_im)+(1-q_m)*W_i=U_i.

Inactive Continue has value

    s_i+Gamma_ij*q_j*(1-q_k)+Gamma_ik*q_k*(1-q_j)
       +K_i*q_j*q_k+C_i*Pi_i*q_m=W_i,                     (B6)

where the equality is exactly F_i=0. Inactive Quit must still be checked;
Section 8.4 gives a strictly positive margin, uniformly over (B2)--(B3).

The row subtraction is an algebraic convenience. It is legitimate for
the original terminal comparison only after opponents' sure absorption
is proved, as done in Section 8.5. No AllNever reward is changed in the
original game.

### 8.2. Exact center root and nonsingular Jacobian

At Rplus, Pi=(87/26,3,87/26,3), c=(9/26,0,9/26,0), K_i=3/20,
Gamma_i,m=3 and Gamma_i,j=Gamma_i,k=-3/5. Substitution in (B4) gives
F(Rplus,q*)=0. More explicitly C_i=3/8 for every i, and

    P=-(3/5)(1/4+1/2)+(3/20+6/5)(1/8)=-9/32.

For even i, C_i*Pi_i*q_m=261/416 and c_i*q_m/(1-q_m)=9/26;
their difference is P. For odd i, C_i*Pi_i*q_m=9/32 and c_i=0.

The exact Jacobian J=partial_q F(Rplus,q*) in owner order is

    [[0,27/208,99/130,789/520],
     [-9/8,0,3/10,33/40],
     [99/130,789/520,0,27/208],
     [3/10,33/40,-9/8,0]].                                 (B7)

It has determinant -185549859/69222400 and inverse A

    [[106912/208249,-2127512/2290739,-61360/624747,686240/6872217],
     [-66768/208249,98688/208249,459680/624747,-18880/208249],
     [-61360/624747,686240/6872217,106912/208249,-2127512/2290739],
     [459680/624747,-18880/208249,-66768/208249,98688/208249]].   (B8)

Direct rational multiplication gives AJ=I. The maximum absolute row
sum of A is 6136/3741<2, and in particular ||A||_infinity<4. These
displayed rational matrices make the bound independently reproducible.

### 8.3. A uniform contraction produces the zero from every raw input

All q in (B3) lie in [0.249,0.501]^4, and every 1-q_l is at least 0.499,
so using the looser denominator bound 0.49 is valid. At the center
|c_i|<0.4 and |Pi_i|<4. The only nonzero second partials of F_i(Rplus,q) are:

    partial_(m,m) F_i=2*c_i/(1-q_m)^3,
    partial_(m,j) F_i=Pi_i*(1-q_k),
    partial_(m,k) F_i=Pi_i*(1-q_j),
    partial_(j,k) F_i=Gamma_ij+Gamma_ik-K_i-Pi_i*q_m,

and their symmetric counterparts. Their total absolute sum is less than
64: the first term is less than 7, the four mate/cross terms total less
than 16, and the two cross/cross terms total less than 14. Consequently

    ||partial_q F(Rplus,q)-J||_infinity <=64*rho.                (B9)

Changing raw entries by at most eta changes each Gamma, Pi, K and c
coefficient by at most 2eta. In particular c is a difference of TWO raw
entries, not an independent sum of four errors. Formula (B4) gives,
uniformly on (B3),

    ||F(r,q)-F(Rplus,q)||_infinity <=12eta,
    ||partial_q F(r,q)-partial_q F(Rplus,q)||_infinity <=24eta.  (B10)

For the first bound use q_m/(1-q_m)<2, total nonempty opposite-pair
probability at most one, and C_i*q_m<=1. For the derivative bound the
mate derivative changes by less than 12eta; each cross derivative
changes by less than 6eta; the own derivative is zero. This proves both
bounds directly from the raw perturbations.

Define T_r(q)=q-A*F(r,q) on the closed cube (B3). Since AJ=I, (B9)--(B10)
and ||A||<4 give

    Lip(T_r) <= L=4*(64rho+24eta)=0.256096 <1/2.

At the center ||T_r(q*)-q*||<=48eta. Therefore

    ||T_r(q)-q*|| <=48eta+L*rho
                    =0.000304096 <rho.                    (B11)

Thus T_r maps the whole closed cube strictly into itself and is a
contraction there. Its iterates from q* converge to its unique fixed
point in this cube. Since A is invertible, that fixed point solves F=0.
This is a uniform, actual-data production of all four hazards. Neither
an implicit smallness threshold nor a supplied strategic root is used.

### 8.4. Every inactive endpoint remains strictly suboptimal

At the center, the scheduled pair values in (B5) are

    (U_even,U_odd)=(1+87/52,1+3/4),
    (W_even,W_odd)=(1+9/26,1).

In the opposite phase an even i's normalized Quit endpoint is
P-2c*q_j*q_k, whereas an odd i's endpoint is P+c*x with x=1/4.
Here P=-9/32 and y=1/2. The exact Continue-minus-Quit margins are

    even: 2cxy+C*(a+c)y=297/416,
    odd:  x*(a*C-c)=81/416.                               (B12)

These include singleton and simultaneous-opponent exits, including the
queried triple containing the deviator. They follow immediately from
the difference rule (11), which is unchanged by adding one.

For clarity the same margin at any actual input is the explicit function

    G_i(r,q)=c_i*q_m/(1-q_m)
        -L_ij*q_j*(1-q_k)-L_ik*q_k*(1-q_j)-L_ijk*q_j*q_k,
    L_iT=r_i({i} union T)-s_i.                            (B13)

All center participant coefficients appearing here have absolute value
less than 4. On (B3), the derivative of the first term is less than 2;
each cross derivative of the remaining polynomial is less than 8.
Thus its total absolute first derivative sum is less than 64. Raw
perturbation changes its first coefficient and each L by at most 2eta;
using q_m/(1-q_m)<2 and total mixture weight at most one bounds its
change by 16eta. Hence

    |G_i(r,q)-G_i(Rplus,q*)| <=64rho+16eta
                         =0.064016 <81/416.               (B14)

Every inactive Quit endpoint is strictly below W_i throughout the full
raw box and hazard cube. Every active endpoint equals U_i, by (B5)--(B6).
All sixteen Bellman endpoint comparisons are therefore established.

### 8.5. Entire behavioral replacements and one fixed uniform target

Alternate the scheduled pairs, drawing each active owner's independent
Quit coin with the produced probability q_i and otherwise Continuing.
Every owner has a strictly positive hazard every second date. Against
any replacement of owner i, its three opponents' cycle survival is

    rho_i=product_(l!=i)(1-q_l)<1.

It is in fact less than 0.3 uniformly on (B3). The opponents' private
coins do not depend on the deviator, on the unique all-Continue history.
Thus every unilateral replacement, including literal Never, faces sure
opponent absorption with a uniformly bounded geometric expected time.

Iterate the endpoint inequalities (B5)--(B6),(B14) along any finite response
deadline. The residual continuation term after n cycles is bounded by
a fixed value bound times rho_i^n, so tends to zero. Every finite and
Never response is bounded above by the initial phase value. Under the
prescription the endpoint equalities give exactly that value. Arbitrary
private mixtures of deadlines add no larger value. The unique live
history also identifies every behavioral replacement with such a law.

Consequently these are actual terminal Nash profiles of the ORIGINAL
table. The earlier row subtraction translates every prescribed and
deviating payoff by the same s_i, since each is surely absorbing; live
and AllNever rewards remain zero throughout the game.

Let H bound the geometric expected time until one of an owner's
opponents quits, uniformly over owners and replacements. With
B=max_(i,S)|r_i(S)|, a conservative endpoint-convention independent
bound on the difference between expected terminal payoff and expected
N-stage average payoff is 2BH/N. This holds uniformly over every
replacement and for the prescription. Exact terminal Nash therefore
caps every finite-horizon gain by 4BH/N. The prescribed averages tend
to the fixed initial phase payoff from (B5). This proves one fixed
uniform-equilibrium target, chosen before accuracy, using the same
profile for every accuracy.

## 9. Exact positive and negative boundary tests

First, an entirely rational e=0 example has

    a=3, b=3/5, c=9/26, e=0, M=3/20,
    x=1/4, y=1/2, C=3/8.

Equation (2) gives

    (3/8)[87/52-3/4]=9/26,

and (6) gives P=-9/32. Thus its phase-A payoff is exactly
(87/52,3/4,9/26,0). Taking the literal completion (11) specifies
all sixty raw coordinates without an auxiliary certificate. It has
neither an absorbing one-date equilibrium nor a sole-owner geometric
equilibrium by Section 6, and its native center payoff is 3/10.

The asymmetric-premium extension also contains a rational proper example:

    a=3, b=3/5, c=54/133, e=27/133, M=717/1330,
    x=1/4, y=1/2, C=3/8.

Here (2) is the identity 78c-23e=9a, and (6) gives
P=(23e-9a)/96. Its phase-A payoff is
(453/266,213/266,54/133,9/133). Assign the twelve capped coordinates
their upper bounds and assign every free coordinate zero. This is a
complete explicit e>0 table in the theorem.

The endpoint assumptions have a concrete role. If e=c, the factor
1-g in the k-to-one limit vanishes and the limiting polynomial becomes
identically zero; the proof no longer forces y to zero or M(k) to
-infinity. If a=2b, the same numerator limit is zero and the negative
infinity conclusion is not supplied. These observations do not claim
nonexistence at either boundary. The theorem retains its stated strict
inequalities.

The triple caps are genuine all-response hypotheses. If an inactive
recipient's triple coordinate is raised without bound while holding
all other data fixed, the both-opponents-Quit event has positive
probability xy, so its inactive Quit endpoint eventually exceeds the
displayed Continue value. Thus singleton and pair comparisons alone
cannot prove this profile's Nash property. By contrast, arbitrary
grand and passive-triple coordinates do not affect any unilateral test.

Finally, row offsets cannot be moved through a profile with positive
joint-Never probability in general. For AllNever, adding mu_i to every
nonempty reward still leaves prescribed payoff zero. The affine step
in Section 5 is valid because all prescribed profiles and unilateral
replacements absorb almost surely.

## 10. Adapter, consumer and Lean handoff

An actual-data adapter takes a finite table r, a labeling of the two
pairs, positive recipient scales and offsets satisfying Section 1.
It centers and scales the finite rewards to Z, forms d,g, produces
rho(k) by (1), then uses (5) and the intermediate value theorem to
choose k for the actual M. Equations (2), (4) and (6) produce proper
x,y and certify every endpoint from the raw caps. Sections 4--5 then
give a genuine original-game profile and the fixed target (10).
Every strategic input of the periodic consumer is thus supplied.

The natural implementation separates three ordinary lemmas: uniqueness
and continuity of the interior rho root; the global bound (4) and
surjective parameter map (5); and the finite endpoint calculation.
The resulting theorem should quantify over raw tables satisfying the
displayed finite conditions, and conclude existence of the proper
period-two profile and its uniform target. A structure whose fields
already assume hazards, equilibrium values or an indifference root
would omit the producer established here.

The existing cyclic behavior profile and the two declarations cited in
Section 7 supply the semantic consumer. An implementation may invoke
them after constructing the two Bernoulli root distributions and the
phase vectors. The four opponent-cycle products are explicitly
(1-y)C,(1-x)C,(1-y)C,(1-x)C, all strictly below one. No public
randomization extension, external payoff closure or strategy-class
restriction is needed. The rational fixtures in Section 9 test both
the zero-premium boundary and the strict asymmetric-premium interior.

The open-box adapter instead forms the actual coefficients (B4),
iterates T_r from q*, and uses the uniform self-map and contraction
bounds to produce all four hazards. The strict margins (B12)--(B14)
then certify every inactive action. A Lean implementation must retain
the independent sixty-coordinate input bound, rather than assume a
nearby certificate or a nonsingular zero. Exact rational matrix
multiplication, finite-dimensional derivative bounds and the contraction
mapping theorem suffice for this additional raw producer.

## 11. Conjecture-facing scope

This is a complete raw-family existence producer for every finite real
M, with twelve one-sided caps, twenty-four free nonsingleton coordinates,
arbitrary signed recipient offsets and positive scales. It gives actual
absorbing terminal Nash profiles and fixed uniform-equilibrium payoffs.
The literal completion (11) demonstrates a finite-amplitude global exit
after all absorbing one-date and sole-owner geometric choices disappear.

Section 8 additionally proves existence throughout an explicit full-dimensional
sixty-coordinate box with positive own rewards, without retaining those
equalities. This is a particular open raw region, not a normalization of
every four-player table. No assertion of completeness of two-phase
profiles, exhaustive failure of all older existence criteria, or solution
of the arbitrary signed four-player conjecture is made. No new Lean
theorem, implementation or build check is claimed.
