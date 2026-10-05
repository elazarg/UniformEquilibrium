# Quitting-table coverage

Author: CODEX_BROUWER

## Current status

No exhaustive arbitrary-Fin4 producer has been obtained. A later exact
source audit below shows that the Klein-four and one-involution EXISTENCE
classes are already consumed by the implemented response-quotient machinery.

The final **A solo-0 bridge pays a positive outsider cap** section is a
new complete ordinary construction undergoing independent falsification.
It inserts a diffuse solo phase into a
joint/solo cycle, gives an all-real-parameter raw producer and an exact
four-player-premium-core fixture, and proves fixed-target safety against
unrestricted behavioral deviations. The final bounded source audit also
excludes the latest switched-pair family and universal quiet-debt gates.
This is not an export or Lean claim.

A separate unreviewed result at the end, **Canonical premium-core
reduction**, extends the reviewed two-player strict-leave mechanism to
tables whose positive-premium supports peel down to a pair. It supplies
a finite raw reduction and a three-premium-recipient exact example, not
an arbitrary-game theorem. No export or Lean-check claim is made for it.

The subsequent **Three-player premium core** section gives an exact
unique-full-root falsifier with strictly interior successor and local
index +1. Its complete rational proof and concrete next question are
recorded below. This rules out a direct root-return/index extension,
not uniform-equilibrium existence. It is not yet independently reviewed.

The symmetry proofs remain correct, but neither is new uniform-payoff coverage.
The complete signed Klein-four theorem has passed
independent falsification reviews by CODEX_KREIN and CODEX_MORSE, with no
unresolved mathematical objection. That section remains unchanged. The
self-contained alternative proof is retained internally at
[`CODEX_BROUWER__KLEIN_FOUR_EQUIVARIANT_QUITTING_GAMES.md`](CODEX_BROUWER__KLEIN_FOUR_EQUIVARIANT_QUITTING_GAMES.md)
after removal from the export queue for source overlap. It is not yet
Lean-checked. The theorem places no
restrictions on nonsingleton rewards beyond the stated group symmetry. Its
earlier periodic and two-sure sufficient regions are retained as discovery
history, not final scope. Everything here is ordinary mathematics, source
checks, or labeled experiment; none is a new Lean theorem.

A separate unreviewed extension below weakens Klein-four equivariance to
one within-pair involution and seven linear inequalities between raw reward
sums. It proves an exact stationary all-behavior equilibrium for every
table in that class, and includes the Klein-four theorem's hard branch. The
extension has not been independently
reviewed. Its extra raw inequalities are unnecessary for bare UE existence,
as the response-quotient overlap calculation below proves.

An earlier completed review concerns the zero-singleton child selection in
[`CODEX_KREIN__INDEPENDENT_STOPPING_LAW_SELECTION.md`](CODEX_KREIN__INDEPENDENT_STOPPING_LAW_SELECTION.md).
The review, including an exact all-five-kind reward-closure comparison, is in
[`CODEX_KREIN__ZERO_SINGLETON_CHILD_SELECTION__BY_CODEX_BROUWER.md`](../feedback/CODEX_KREIN__ZERO_SINGLETON_CHILD_SELECTION__BY_CODEX_BROUWER.md).
It approves a modest missing boundary corollary, not a new exhaustive route.

## Question and bounded source audit

For a finite player set I, every nonempty coalition S has a real payoff
vector r(S). Players independently choose complete stopping laws on the
nonnegative integers and Never. First finite quitting pays its coalition;
joint Never pays zero. A deviation replaces one player's entire law. The
question is to produce unrestricted terminal approximate Nash profiles for
every accuracy from a reward-table class, then select one fixed uniform
payoff before the accuracy quantifier.

The initial attempted route was to make the complement of existing
stationary, collision, and quiet-child producers strategically productive,
using the nonsingleton coordinates as well as the singleton matrix.

Inspected source declarations include:

- `quittingUniformEquilibriumPayoffConjecture`, in
  `UniformEquilibrium/Quitting/Conjecture/Basic.lean`;
- `quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors`
  and the retained-family selection theorem, in
  `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`;
- `quittingFaceNumerator`, in
  `UniformEquilibrium/Quitting/Stationary/FaceNumerator.lean`;
- `exists_heterogeneousStationaryFaceNash`, in
  `UniformEquilibrium/Quitting/Stationary/HeterogeneousConstrainedFaceNash.lean`;
- `stationaryTerminalNash_or_instantNoJoin_of_oneSidedWeakUnitGuards`, in
  `UniformEquilibrium/Quitting/Stationary/OneSidedWeakUnitProducer.lean`;
- `quittingGame_exists_uniformPayoff_of_toggleOrdinalPotential`, in
  `UniformEquilibrium/Quitting/Stationary/TogglePotential.lean`;
- `PairedCollisionReward.exists_uniformEquilibriumPayoff`, in
  `UniformEquilibrium/Quitting/Examples/BlockPair/PairedCollisionRewardExistence.lean`,
  together with its literal table and stationary/periodic producers;
- `hasProductLowQuittingPremium_iff_supportwiseBalance_of_nonnegative`, in
  `UniformEquilibrium/Quitting/Classification/NonnegativeProductLowSupportPeelingConverse.lean`;
- `quittingPunishmentValue_eq_singleton_of_nonnegativePremium`, in
  `UniformEquilibrium/Quitting/Classification/NonnegativePremiumPunishment.lean`;
- `exists_periodic_quittingPerfectAbsorbingRootSequence_of_lowActiveQuitPayoff`,
  in `UniformEquilibrium/Quitting/Classification/Existence/PerfectAbsorbingRootSequence.lean`,
  and its actual one-row producer in `PerfectAbsorbingRow.lean`;
- the reward/projection/payoff comparisons in
  `UniformEquilibrium/Quitting/Terminal/PassivePlayerPadding.lean`.

These were source inspections, not new builds. The toolkit already records
signed sole-owner and punishment-normality completions; those boundaries
must not be treated as absent.

## A discarded broad reduction: zero-sum balancing observer

This is an elementary universal reduction, not a Fin4 advance. It is retained
because it explains why a proposed conservation-law route was abandoned.

For any nonempty finite I choose H_i greater than both zero and every
r_i(S), and put L_i=min(0,min_S r_i(S)). Add one player o. At an
old-containing coalition T, let S=T intersect I, copy r(S) on old players,
and pay o minus the sum of these old rewards. At the coalition {o}, pay
the old players H and pay o minus the sum of H. Every outcome is zero sum.

Let p be any profile of the enlarged game, Pp its literal old-law
projection, and s the probability that o strictly preempts every old clock.
Put

    a = sum_i H_i - max(0, max_S sum_i r_i(S)) > 0,
    W = max_i (H_i-L_i).

Coupling the same independent clocks gives

    0 <= U_i(p)-U_i(Pp) <= W s

for each old player. Lifting an arbitrary old deviation never lowers its
deviating payoff, since new-player preemption replaces an old outcome by
the coordinatewise upper bound H. The observer's deviation to Never gains
at least a s: only its strict-preemption event changes, and its new eventual
payoff is at least minus max(0,max_S sum_i r_i(S)). Thus, for full maximum
terminal exploitability E,

    E(p) >= max(a s, E(Pp)-W s),
    E(Pp) <= (1+W/a) E(p).

Conversely, adjoining literal Never for o preserves every old deviation
payoff. Any observer deviation can only replace its eventual payoff by the
worse value minus sum H on strict preemption, so it is unprofitable.
Consequently the exact uniform-payoff sets satisfy

    UE(r_plus) = { (v, -sum_i v_i) : v belongs to UE(r) }.

For the reverse target direction use the displayed O(E) payoff comparison;
for the observer coordinate use the exact zero-sum identity. The result uses
all behavioral laws and does not supply extra correlation. It raises the
player count and therefore neither solves nor narrows the Fin4 problem. It
is not queued for review/export.

## Nonnegative own premiums: a surviving question, not a theorem

The independently stated cone is

    r_i(S) >= r_i({i}) whenever i belongs to S.

This implies exact punishment normality for nonnegative own singletons;
it does not imply the product-low condition. Within this cone, the checked
product-low/supportwise-balance theorem is exactly the support-peeling
restriction, so that theorem does not cover its complement.

As an early falsification test, keep the paired singleton rows

    r(1)=(1,4,0,0), r(2)=(4,1,0,0),
    r(3)=(0,0,1,4), r(4)=(0,0,4,1).

Set every nonsingleton participant reward to 101/100. For each passive
coordinate r_i(S), with |S|>=2, compare its two adjacent entries in the
literal `PairedCollisionReward.reward 1` table. Set the new passive entry
to 2 if the old passive entry exceeds the old joining entry, to 0 if it is
smaller, and to 101/100 if equal. This completely specifies a rational
table and preserves every strict nonempty membership-toggle orientation
of the source table. It has no pure sure-exit coalition.

A floating Newton search through stationary support/boundary patterns found
no nonzero stationary complementary root. This is only a discarded
discovery experiment: it is not an exact stationary exclusion, a durable
computational certificate, or evidence of equilibrium nonexistence. The
experiment did not justify spending a full review cycle on another local
stationary obstruction.

The source check also distinguishes this cone from positive recursive
quitting games: nonnegative terminal rewards are a different condition.
The public abstract of Solan--Solan's
[positive recursive general quitting-game result](https://arxiv.org/abs/1803.00878)
promises sunspot equilibria. It does not supply the independent-strategy
producer needed here. Solan--Vieille's
[Quitting Games](https://www.math.tau.ac.il/~eilons/quitting19.pdf), its
introductory assumptions and main capped-payoff theorem, use the opposite
participant inequality. No published closure of the entire nonnegative
premium cone is asserted.

## A raw Klein-four class and its unconsumed complement

Status: ordinary proof draft, not independently reviewed. This is a positive
class, not a completeness theorem or a new periodic mechanism.

Let I be the additive group with four elements, and impose translation
equivariance r_(i+k)(S+k)=r_i(S). Normalize every own singleton to 1.
For the three nonzero group elements t, all of the remaining raw data are:

    r_i({j}) = a_(i-j)                         (i != j),
    r_i({j,j+t}) = p_t                         (i in the pair),
    r_i({j,j+t}) = f_t                         (i outside the pair),
    r_i(I minus {m}) = h_(i-m)                 (i != m),
    r_m(I minus {m}) = h0,
    r_i(I) = g.

Thus there are fourteen free real coordinates after the normalization. In
particular triple and full-coalition rewards are not inferred from singleton
symmetry. Write D=sum_t a_t-3 and d_t=p_t-a_t.

### Raw alternating-pair producer

Suppose D>0 and some type t, with the other two types denoted s,u, obeys

    d_t>0,
    p_s+p_u <= 2+d_t,
    h_t <= 1+2d_t.                                         (K)

Then the table has an exact terminal Nash profile at every live suffix,
against unrestricted independent behavioral deviations, and hence a uniform
equilibrium payoff. The profile alternates the two complementary pairs of
type t. At its scheduled phase each member of the active pair independently
quits with the same internally selected hazard x in (0,1); all other players
Continue. No restriction is placed on f_t, on the other two f coordinates,
on h_s,h_u,h0, or on g. The remaining singleton coordinates enter only D.

Here is the selection and full incentive calculation. Put a=a_t, p=p_t,
f=f_t, d=p-a, and z=a_s+a_u. For a trial hazard x let c=(1-x)^2. A player's
one-root terminal contributions at its active and inactive phases are

    A=x(1-x)(1+a)+x^2 p,
    B=x(1-x)z+x^2 f.

Consequently its actual alternating values are

    V=(A+c B)/(1-c^2),        W=(B+c A)/(1-c^2).

Active Quit and Continue are respectively (1-x)+xp and xa+(1-x)W.
Multiplying their difference by 1-c^2 gives x times the polynomial

    P(x)=(p-1)x^3+(-3p+f-z+4)x^2
         +(3p-f+2z-6)x+3-a-z.

Its endpoint values are P(0)=-D<0 and P(1)=p-a=d>0. The intermediate
value theorem selects an interior x with P(x)=0 from the reward data.
There is no supplied-root hypothesis. At this x, writing l=x/(1-x),

    W=1+l d,
    V=1+x(p-1).

At an inactive phase, immediate Quit has payoff

    Qquiet=((1-x)^2)+x(1-x)(p_s+p_u)+x^2 h_t.

Continue has payoff W. The exact cleared difference is

    (1+l)^2 (W-Qquiet)
      =l[(2+d-p_s-p_u)+l(1+2d-h_t)+l^2 d] >= 0,

by (K). Thus active players are indifferent and inactive players prefer
Continue at both actual phases. No unlisted coalition coordinate occurs in
these prescribed or one-player-deviation rows.

This checks arbitrary behavioral deviations, not merely periodic responses:
each opponent has one independent quit trial of hazard x in every two-date
cycle. Under any replacement of one player's law, unchanged opponents have
cycle survival (1-x)^3<1. Iterating the displayed endpoint inequalities
therefore kills the terminal remainder and bounds every response by V or W
at the corresponding initial phase. Prescribed Bellman recursion has the
same vanishing remainder. Their equality proves exact terminal Nash. The
same geometric opponent-absorption bound gives a finite expected duration
uniform over deviations, so terminal and long finite-average comparisons
converge uniformly to the one fixed actual initial payoff. This supplies the
uniform-payoff conclusion without changing its target with accuracy.

The stronger root-dependent inactive condition is the nonnegativity of the
displayed quadratic at the selected l. It is NOT the raw theorem being
claimed: (K) deliberately replaces it by reward inequalities before root
selection. For a<=1, the equation selecting l can also be written

    f=d l+2d+1+(p-1)/(l+1)-D/l.

Its right side has positive derivative: if p>=1 use p-1<=d, and if p<1
all three derivative terms are positive. It rises from minus infinity to
plus infinity. This is a useful uniqueness fact for this scalar ansatz,
not additional game coverage.

### Exact adjacent alternatives

Within this same whole symmetry class, the following finite-table tests
produce pure sure-exit terminal Nash profiles:

    singleton:  d_t<=0 for every t;
    pair t:     d_t>=0 and h_t<=f_t;
    triple:     h_t>=f_t for every t, and g<=h0;
    all four:   g>=h0.

These conditions are also necessary for the indicated pure coalition. For
the singleton the owner compares 1 with Never's zero; for every other
membership toggle, the relevant payoff pair is exactly one of
(p_t,a_t), (h_t,f_t), or (g,h0). Dates later than zero cannot improve a
deviation once another sure quitter is retained. All-Never is not Nash
because own singletons are 1.

The entire region sum_t a_t<=3 also has a uniform equilibrium by a symmetric
stationary argument, with no restrictions on nonsingleton coordinates. If
g>=h0 use the full sure-exit profile. Otherwise, at a common trial hazard y,
write z0=1-y and

    Q(y)=z0^3+y z0^2 sum_t p_t+y^2 z0 sum_t h_t+y^3 g,
    L(y)=(3-3y+y^2)Q(y)
         -[z0^2 sum_t a_t+y z0 sum_t f_t+y^2 h0].

The stationary face numerator is y L(y). If sum a_t<3, then L(0)>0 and
L(1)=g-h0<0, so an interior common hazard makes every player indifferent.
At sum a_t=3, common hazards tending to zero have payoff and both complete
response endpoints tending to 1. Hence their full terminal exploitability
tends to zero and their target is the fixed all-ones vector. This boundary
argument does not assert a positive stationary root.

Consequently a counterexample in this symmetry class would necessarily have

    D>0,  g<h0,  some h_t<f_t,  some d_t>0,
    d_t>=0 implies h_t>f_t,

and for every t with d_t>0 at least one of the two nontrivial raw bounds in
(K) must fail. These are actual restrictions on a surviving table, but they
are not a contradiction. A failed scalar sufficient bound alone does not
force a different pairing or a pure equilibrium.

There is one further exact stationary alternative that consumes an entire
tail of the remaining full-coalition coordinate. Put e_t=h_t-f_t and
J=h0-g. In the no-pure branch J>0, and every type with d_t>=0 has e_t>0.
Fix a type with d_t>0. Make both members of a pair of this type sure
quitters at every date, and give each of the other two players the hazard

    y=e_t/(e_t+J),             0<y<1.

For each nonsure player, Quit minus Continue is

    (1-y)e_t-y J=0.

For either sure player the same difference is

    (1-y)^2 d_t+y(1-y)(e_s+e_u)-y^2 J
      =(1-y)^2 [d_t+(e_t/J)(e_s+e_u-e_t)].

Hence this actual stationary profile is full behavioral terminal Nash if

    d_t J+e_t(e_s+e_u-e_t)>=0.                             (S)

Every unilateral deviation leaves at least one sure opponent, so there is
no tail or sole-owner boundary issue. This is a finite raw inequality, not
a supplied stationary-root condition. In particular, for fixed proper
coalition rewards in the no-pure branch, every sufficiently negative g
is solved: choose any t with d_t>0, and increase J until (S) holds.

Thus a surviving Klein-four table must also satisfy, for every t with
d_t>0,

    e_t>e_s+e_u,
    0<J<e_t(e_t-e_s-e_u)/d_t.

This confines the only unresolved full-coalition coordinate to a bounded
interval once the proper coalition rewards are fixed. It does not prove
that the interval is covered by the common-hazard or alternating-pair
producer. The two-sure calculation is an elementary specialization of the
existing finite-game/stationary complementarity mechanism, not a claim of
a new general equilibrium theorem.

### Novelty calibration and comparison

The current exact sources for the strategy mechanism are
`PairedCollisionReward.PeriodicRates.profile_isExactTerminalNash` and its
uniform-payoff theorem in
`UniformEquilibrium/Quitting/Examples/BlockPair/PairedCollisionRewardPeriodic.lean`,
and `GameTheory.PairedCycle.exists_exact_allSuffix_uniformPayoff_of_rawRegion`
in `UniformEquilibrium/Quitting/Cycles/PairedCycleEquilibrium.lean`.
`PairedCycleSchedule.lean` was also inspected for its literal raw-region
hypotheses. No claim of a new periodic compiler is made.

The broad existing ordinary-math region in
[`CODEX_TARSKI_PREMIUM__ASYMMETRIC_PAIRED_CYCLE_EXACT_CAP_SELECTOR.md`](CODEX_TARSKI_PREMIUM__ASYMMETRIC_PAIRED_CYCLE_EXACT_CAP_SELECTOR.md)
requires each recipient's two external singleton rewards to be above its
own singleton, and bounds the joining rows close to the own singleton.
The raw class (K) does not require either. For example fix a=(4,0,0),
p=(101/100,101/100,101/100), and choose a type with a_t=0. Then d_t=101/100,
p_s+p_u=202/100<301/100; any h_t<=302/100 passes. Every f coordinate and
the other listed unused coordinates remain arbitrary. No pairing of these
singleton rows fits the Tarski region, even after positive playerwise
affine changes: each recipient has only one external singleton above its
own, whereas that region needs two. This is a source-class separation,
not an exclusion from all known UE producers.

For p_t>1 the actual periodic values V,W are both strictly above 1. Thus
the constructed profile itself rules out weak singleton-payoff exclusion,
and activating its pair alone rules out product-low premiums. The
four-neighborhood construction in
[`CODEX_DESCENDANT__TRACKED_CORPUS_ALTERNATING_PAIR_EQUILIBRIA.md`](CODEX_DESCENDANT__TRACKED_CORPUS_ALTERNATING_PAIR_EQUILIBRIA.md)
is another existing alternating-pair mechanism, not a source of the present
unbounded scalar raw class. No complete separation from quiet-child or
general stationary producers has been established.

## Complete Klein-four coverage: frozen candidate for independent review

Status: proof draft, not independently reviewed or Lean-checked. This section
is frozen on 2026-10-05 for falsification; no export is requested yet. Unlike
the preceding sufficient regions, this statement consumes the ENTIRE
specified symmetry class.

### Full statement, probability mode, and desired conclusion

Let I be the four-element group (Z/2Z)^2. For every nonempty coalition S,
let r(S) be an arbitrary finite real payoff vector indexed by I. Assume only
translation equivariance:

    r_(i+k)(S+k)=r_i(S)              for all i,k and nonempty S.       (E)

All-Never pays zero. Players use independent behavioral strategies, or
equivalently independent complete stopping laws on the nonnegative integers
and Never. A deviation may replace one player's ENTIRE law; it need not be
stationary, periodic, bounded, or proper.

Claim: every such reward table has a uniform-equilibrium payoff. More
precisely, the construction below produces either one exact stationary
terminal Nash profile with all opponent-deleted absorption probabilities
positive, the exact all-Never profile, or a stationary approximation family
with one fixed payoff target and full terminal regret tending to zero.
The strategies use no public correlation, common random clock, or observation
of another player's future private stopping choice.

Equivariance makes the own singleton s=r_i({i}) independent of i. If s<=0,
all-Never is exact Nash for every finite average and terminal evaluation:
a unilateral deviation can only realize its own singleton or Never, both
nonpositive. This gives the fixed zero uniform payoff. Hence assume s>0
and divide every reward by s. This positive scalar normalization preserves
all comparisons; restore the scale at the end. Own singletons are now 1.

Use the complete fourteen-coordinate data a_t,p_t,f_t,h_t,h0,g from the
earlier Klein-four section, but impose NONE of its periodic row inequalities.
Put D=sum_t a_t-3. The exhaustive alternatives are:

1. D<0: a common-hazard exact stationary equilibrium or the full sure exit.
2. D=0: common hazards tending to zero, with fixed target (1,1,1,1).
3. D>0 and a_t>=1 for all three t: one rare solo owner, with its fixed
   singleton payoff vector as target.
4. D>0 and a_t<1 for some t: the triangle argument below produces an
   exact stationary equilibrium, with a common hazard on each t-pair.

These conditions concern only singleton rows, but the constructed exact
field in case 4 contains every nonsingleton reward. Its global values are
not replaced by a singleton approximation.

### The exact face field and complete-response bridge

For any hazard vector c in [0,1]^I, fix i and let

    alpha_i=product_(j!=i)(1-c_j),
    Q_i=E[r_i(A union {i})],
    A_i=E[1_(A nonempty) r_i(A)],

where A is the independently sampled opponent quitter set at one date.
Define

    F_i(c)=(1-alpha_i) Q_i-A_i.                              (F)

This is the literal polynomial `quittingFaceNumerator` in
`UniformEquilibrium/Quitting/Stationary/FaceNumerator.lean`, with its
continuity and endpoint identity. Its independence of c_i is checked in
`heterogeneousFaceNumerator_update_self` in
`UniformEquilibrium/Quitting/Stationary/HeterogeneousConstrainedFaceNash.lean`.
No approximation error enters this definition.

Suppose every player has at least one positive-hazard opponent and

    c_i=0       implies F_i<=0,
    0<c_i<1     implies F_i=0,
    c_i=1       implies F_i>=0.                              (C)

Let b_i=1-(1-c_i)alpha_i>0. The actual stationary payoff is

    U_i=[c_i Q_i+(1-c_i)A_i]/b_i.

At continuation value U_i, Quit minus Continue equals F_i/b_i; prescribed
mixing has value U_i. Conditions (C) therefore make BOTH pure action
endpoints at most U_i. Every arbitrary behavioral deviation still faces
the unchanged opponents' geometric survival alpha_i^N. Iterating the
endpoint inequalities and letting N tend to infinity proves that its full
terminal payoff is at most U_i. Thus (C) gives exact unrestricted terminal
Nash, not merely a stationary best-response test.

Moreover the expected absorption time under any unilateral deviation is
bounded by the unchanged opponents' geometric waiting time. Rewards are
bounded because the table is finite. Terminal and H-stage average payoffs
therefore differ uniformly over deviations by a constant times 1/H. The
same one profile is a uniform-equilibrium witness at its one actual payoff
U, for every accuracy after increasing the horizon threshold.

### The two-dimensional symmetric field in case 4

Fix t with a_t<1, and write the other two nonzero elements as u,v. Partition
I into B0={0,t} and its complementary coset B1={u,v}. Give both B0 players
hazard x and both B1 players hazard y. Translation by t interchanges the
members within each coset, so their respective exact face numerators agree.
Translation by u interchanges the cosets, so the resulting two-coordinate
field has the exact form

    F(x,y)=(F0(x,y),F1(x,y)),       F1(x,y)=F0(y,x).          (Sym)

This holds for the whole square, not just at first order.

Set A=1-a_t>0 and B=a_u+a_v-2. Since D>0, B-A=D>0. Directly expanding
(F) at (0,0), where Q_i=1 and A_i=0, gives

    F0(x,y)=A x-B y+O((x+y)^2),
    F1(x,y)=A y-B x+O((x+y)^2).                              (L)

Indeed opponent absorption is x+2y+O((x+y)^2), and the passive contribution
is a_t x+(a_u+a_v)y+O((x+y)^2). Since the exact field is polynomial,
the remainder bound is uniform in a small square. Thus choose 0<delta<1
so that throughout 0<=y<=x<=delta, x>0,

    F1(x,y)<0,                 F0(x,0)>0.                  (N)

For example the first follows from A y-B x<=-(B-A)x and a quadratic
remainder bounded by a constant times x^2. The second follows from its
positive linear coefficient A. On the diagonal, (Sym) and (N) also give
F0(x,x)=F1(x,x)<0.

### Projected-field construction and all triangle faces

Let T={(x,y):0<=y<=x<=1}, a compact convex triangle, and choose any
continuous function phi:[0,1]->[0,infinity) that is positive at zero and
vanishes for x>=delta. For example phi(x)=max(delta-x,0). Define

    Ftilde(x,y)=(F0(x,y)+phi(x), F1(x,y)).

The map z |-> P_T(z+Ftilde(z)) is a continuous self-map of T, where P_T
is Euclidean metric projection. Brouwer gives a fixed point z. The exact
projection convention is

    Ftilde(z) dot (w-z)<=0       for every w in T.            (VI)

First exclude the WHOLE cutoff neighborhood x<=delta, including its edge:

* At (0,0), the field is (phi(0),0), so a positive horizontal feasible
  direction violates (VI).
* If 0<y<x<=delta, the point is interior to the triangle because delta<1.
  Its vertical coordinate admits both signs of perturbation, so (VI)
  requires F1=0, contradicting (N).
* If y=0 and 0<x<=delta, both horizontal signs are feasible. Hence (VI)
  requires F0+phi=0, whereas F0>0 and phi>=0.
* If x=y in (0,delta], a positive phi makes
  Ftilde_0-Ftilde_1=phi>0. The feasible direction (1,-1) contradicts
  (VI). If phi=0, both coordinates equal the same negative value, and
  the feasible direction (-1,-1) contradicts (VI).

These arguments also cover x=delta, where phi vanishes: that line is not
an additional boundary of T. Therefore the fixed point has x>delta, and
Ftilde(z)=F(z) is the unmodified exact reward-table field.

Now read (VI) on each remaining genuine face of T:

* 0<y<x<1: both field coordinates are zero.
* y=0 and 0<x<1: F0=0 and F1<=0.
* x=1 and 0<y<1: F0>=0 and F1=0.
* (x,y)=(1,0): F0>=0 and F1<=0.
* x=y in (0,1): both diagonal tangent directions give F0+F1=0;
  (Sym) gives F0=F1, so both are zero.
* (x,y)=(1,1): (Sym) gives F0=F1. Testing the feasible direction
  (-1,-1) gives F0=F1>=0.

These are exactly (C) for the four individual hazards (x,x,y,y). Since
x>delta>0, both B0 players have positive hazards. Each of the four players
therefore retains a positive-hazard opponent even under an arbitrary own
deviation. The complete-response bridge proves exact stationary terminal
Nash and its fixed uniform payoff. No inference from a grouped-player
equilibrium is used: the two field coordinates are the actual INDIVIDUAL
face numerators, and their symmetry is what turns a triangular VI solution
into all four individual complementary inequalities.

### Verification of the other three exhaustive cases

For D<0, use the common-hazard polynomial L from the preceding section.
It has L(0)=-D>0. If g>=h0, everybody quitting surely is already exact
Nash. Otherwise L(1)=g-h0<0, and the intermediate value theorem gives a
root in (0,1). All players have positive-hazard opponents; apply (C).

For D=0, give every player the same hazard q>0 and send q to zero. At every
q, unchanged opponents absorb almost surely. The full response cap is

    max(Q_i(q), A_i(q)/(1-alpha_i(q))):

a pure finite date gives the corresponding convex interpolation between
these endpoints, and Never gives the second endpoint. Both endpoints tend
to 1 because Q_i(q)->1 and A_i(q)/(1-alpha_i(q))->sum_t a_t/3=1.
The prescribed payoff also tends to 1. Thus the maximum unrestricted
terminal regret tends to zero and the target is the fixed all-ones vector.
For each requested accuracy first choose q, then use the geometric
opponent-absorption bound to obtain one sufficiently large finite-average
threshold for that same profile. This is the correct fixed-target uniform
quantifier order.

For D>0 with every a_t>=1, choose any owner o. Let only o use a stationary
hazard q>0, all others literal Never. The prescribed terminal payoff is
EXACTLY r({o}) for every q, so the target never varies. The owner has no
profitable deviation: its own singleton is 1 and Never pays zero. For an
outsider i, write a=r_i({o})>=1 and p=r_i({o,i}). Against o, quitting at
any finite date, conditional on reaching it, yields

    (1-q)*1+q*p,

whereas Never yields a. Its complete deviation gain is therefore at most
q*max(p-1,0); earlier opponent absorption only attenuates this difference.
This bound also covers arbitrary mixtures of finite times and Never.
Hence full terminal regret tends to zero. For outsiders, geometric owner
absorption bounds expected duration under all deviations. For the owner,
every finite-average deviating payoff is at most 1, while its prescribed
average tends to 1. Thus this same family supplies uniform witnesses at
the fixed singleton target. No unjustified translation across positive
Never mass is used.

Scaling back by s completes all cases. Every source-data choice (including
the pairing, delta, cutoff, and exact root) is made from the table before
the relevant profile is used. No response solution, finite-law limit, or
correlated randomization is assumed as input.

### Comparison and requested independent attack

The new mathematical step is the triangular projected-field producer with
local coefficients B>A>0 and exact coordinate-swap symmetry. It is an
application of Brouwer, not a new fixed-point theorem. The whole symmetry
class is not claimed to be stationary-complete: the zero-average and rare
solo branches deliberately provide approximations rather than an asserted
exact stationary equilibrium.

A narrow source search for Klein symmetry, equivariant stationary roots,
triangle Nash fields, and involution stationary producers found no named
production theorem supplying this full reward class. Existing constrained
stationary Nash gives box-boundary inequalities, not the triangle/origin
exclusion above. Existing paired periodic regions and specific collision
tables do not quantify over all fourteen remaining reward coordinates.
No assertion about external literature priority is made.

Requested falsification: check the exact individual-field symmetry; the
linear coefficients and uniform triangle signs; the projection sign in
(VI); every diagonal, outer, and cutoff-boundary case; and the full-response
and fixed-target bridges in all four singleton alternatives. In particular,
do not replace individual complementary conditions by group best responses.

## One involution and raw diagonal order: a larger class

Status: ordinary mathematical proof, awaiting independent falsification.
This section is separate from the frozen Klein-four theorem and export.
It requires no source strategy, stationary root, continuation value, or
certificate. The raw conditions below are a finite list of linear reward
inequalities, together with one table symmetry.

### Exact data and conclusion

There are four players 0,1,2,3. Every nonempty S has an arbitrary finite
real reward vector r(S), Never pays zero, and every behavioral profile
uses independent private randomization. A deviator may replace its complete
behavioral strategy. Let tau=(0 1)(2 3), and assume only

    r_(tau(i))(tau(S))=r_i(S)             for all i and nonempty S.   (I)

Write E0={0,1}, E1={2,3}, choose representatives i0=0,i1=2, and put

    s0=r_0({0}),                   s1=r_2({2}),
    A0=s0-r_0({1}),                A1=s1-r_2({3}),
    B1=r_2({0})+r_2({1})-2s1.

Require the strict singleton conditions

    A0>0,                 B1>max(A1,0).                           (O)

For ell=0,1 and m in its stated range define raw cardinal sums

    P_(ell,m)=sum_(S contains iell, |S|=m) r_iell(S),    1<=m<=4,
    C_(ell,m)=sum_(S excludes iell, |S|=m) r_iell(S),    1<=m<=3.

The seven weak inequalities are

    P_(0,m)>=P_(1,m)          (m=1,2,3,4),
    C_(0,m)<=C_(1,m)          (m=1,2,3).                            (R)

**Theorem.** Every table satisfying (I),(O),(R) admits an exact stationary
terminal Nash profile against arbitrary full behavioral deviations, with
two positive hazards. Its actual terminal payoff is one fixed uniform
equilibrium payoff. All rewards may be signed; no additive normalization
of the zero Never payoff is used.

### Producing the field inequalities from these raw data

Use the exact face numerator F_i from the earlier reviewed section. At
the hazard row (x,x,y,y), (I) makes F_0=F_1 within the first pair and
F_2=F_3 within the second. Denote those two individual numerator values
by f0(x,y),f1(x,y). No symmetry exchanging the two pairs is assumed.

At the diagonal x=y=q, all three opponent hazards equal q, so for ell=0,1

    Q_ell(q)=sum_(m=1..4) q^(m-1)(1-q)^(4-m) P_(ell,m),
    H_ell(q)=sum_(m=1..3) q^m(1-q)^(3-m) C_(ell,m),
    f_ell(q,q)=[1-(1-q)^3]Q_ell(q)-H_ell(q).

Every weight is nonnegative on [0,1]. Thus (R) gives Q0>=Q1 and H0<=H1,
and hence the exact global diagonal ordering

    f0(q,q)>=f1(q,q)                  for every q in [0,1].        (D)

At the origin direct singleton expansion gives

    f0(x,0)=A0*x+O(x^2),
    f1(x,y)=A1*y-B1*x+O((x+y)^2).

On 0<=y<=x, the latter linear term is at most
-[B1-max(A1,0)]x. The polynomial remainder is bounded by a fixed multiple
of x^2. Therefore there is 0<delta<1, selected from the literal table,
such that whenever 0<=y<=x<=delta and x>0,

    f0(x,0)>0,                         f1(x,y)<0.                 (L)

These signs need no condition on the other first-order coefficient of f0.

### The triangular selection and individual decoding

On T={0<=y<=x<=1}, put phi(x)=max(delta-x,0) and
ftilde=(f0+phi,f1). Brouwer applied to Euclidean projection of z+ftilde(z)
onto T gives a point with

    ftilde(z) dot (w-z)<=0              for every w in T.          (V)

The origin is impossible because ftilde(0,0)=(delta,0). At 0<y<x<=delta,
both vertical perturbations are feasible, contradicting f1<0. At y=0,
0<x<=delta, both horizontal perturbations are feasible, contradicting
f0+phi>0. At x=y in (0,delta], direction (1,-1) is feasible, so (V)
requires f0+phi<=f1. Together with (D) and phi>=0, this forces phi=0 and
f0=f1. But then both are negative by (L), and direction (-1,-1)
contradicts (V). Thus the entire cutoff region, including its boundary,
is excluded. The selected x is greater than delta and its field is the
unaltered exact field f.

The non-diagonal faces decode exactly as in the earlier triangle proof:
interior coordinates have zero numerator, the y=0 face has f1<=0, and
the x=1 face has f0>=0. At an interior diagonal point, its two tangent
directions imply f0+f1=0, while the feasible direction (1,-1) implies
f0<=f1. Combining with (D) gives f0=f1=0. At (1,1), the feasible
direction (0,-1) implies f1>=0; (D) then gives f0>=f1>=0. At (1,0),
the ordinary inward coordinate directions give f0>=0 and f1<=0.

Therefore every one of the four INDIVIDUAL hazards satisfies the cube
complementarity signs. Both first-pair players have hazard x>delta, so
deleting any own strategy leaves positive opponent absorption. The exact
stationary/full-response proof above applies literally, yielding the
actual payoff and its fixed-target finite-horizon conclusion. This is an
actual-data producer for every table in (I),(O),(R).

### Strict enlargement and exact tests

For the positive-surplus Klein-four branch, choose its subunit direction
as the within-pair involution. Then A0=A1=A>0, B1=B>A, and all seven
cardinal-sum comparisons hold with equality. Thus this result contains
the complete previously difficult branch and drops pair-exchange symmetry.

It also contains a relatively open set of nonsymmetric tables in the
linear space defined by the one involution. For an exact example, start
with the exported boundary example, whose coordinates in XOR labels are

    s=1, (a1,a2,a3)=(4,0,0), (p1,p2,p3)=(2,1,1),
    (f1,f2,f3)=(1,0,0), (h1,h2,h3)=(0,1,1), h0=0, g=-1.

Reorder its players as old labels (0,2,1,3), so that tau=(0 1)(2 3)
is XOR translation by 2. For any lambda,mu>0, change ONLY the coordinates
of players 0 and 1: add lambda to each reward where that player belongs
to S, and subtract mu when that player is outside S. Keep the Never payoff
zero and keep both other players' coordinates unchanged. This preserves
(I) but breaks full Klein-four symmetry already at own singleton rewards.
The strict raw comparisons are

    P_(0,m)-P_(1,m)=binomial(3,m-1)*lambda>0,
    C_(1,m)-C_(0,m)=binomial(3,m)*mu>0.

The singleton conditions are A0=1+lambda+mu>0, A1=1, B1=2>1.
Every inequality remains valid in a sufficiently small neighborhood within
the one-involution space. Thus the extension is not only an equality
reformulation of the earlier symmetry class. This example still violates
product-low at the root supported on new players 0 and 2 with hazards 1/2:
both participant premiums are 1/2. Increasing one player's own singleton
and all its participant rewards by lambda cancels from that premium.

The example alone is not asserted to avoid every implemented producer;
the new coverage statement quantifies over ALL tables satisfying the
finite raw conditions. Dropping (D) would invalidate the diagonal decoder:
at an interior diagonal point, the values f0=-1,f1=1 satisfy the triangle
normal inequalities but fail both individual mixed-action conditions.
Thus the global diagonal hypothesis does real strategic work.

### Source and review boundary

This extension uses the same inspected `quittingFaceNumerator` and
`heterogeneousFaceNumerator_update_self` declarations in
`UniformEquilibrium/Quitting/Stationary/FaceNumerator.lean` and
`UniformEquilibrium/Quitting/Stationary/HeterogeneousConstrainedFaceNash.lean`.
The actual semantic endpoint is
`quittingGame_isUniformEquilibriumPayoff_of_terminalNash_tendsto` in
`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`,
or the direct geometric finite-average estimate already proved here.
A bounded search in the classification and stationary subtrees found no
named involution/ordered-diagonal raw producer. Rectangular constrained
Nash by itself still leaves the zero hazard row. No new Lean result,
external publication priority, or exhaustive source non-overlap is claimed.

## Full equal-hazard ordering already gives a pure exit

This exact overlap observation retires the attempted four-dimensional
ordered-simplex route; it is not new existence coverage. Suppose the own
singleton of player 0 is nonnegative. On the ordered cube chamber
1>=c0>=c1>=c2>=c3>=0, assume that the actual individual numerators obey
F_i>=F_(i+1) whenever c_i=c_(i+1). Then a pure sure-exit coalition exists.

Start with the sure coalition S={0}. Its only participant can secure its
nonnegative own singleton against Never. At any prefix S={0,...,k-1},
all outsiders have hazard zero, so their fields are ordered. If the first
outside field F_k is nonpositive, every outsider is join-safe and stop.
Otherwise add player k. The field F_k is independent of its own hazard,
so its strictly positive value persists after addition. All participants
now lie in the common hazard-one block, where the assumed field order
gives F_i>=F_k>0 for i<k. Every participant is therefore leave-safe.
This argument repeats at most three times, terminating at an exact pure
coalition Nash profile. With at least two sure players, every deviation
absorbs at once; for the one-owner case, its nonnegative singleton also
controls Never. Thus the conclusion already has the ordinary sure-exit
consumer.

An exploratory integer singleton matrix had passed the linearized seam
tests with ambient R0 degree one. That observation did not avoid this
pure-exit construction, which uses the full table's global face order.
No matrix search output or numerical evidence is needed for the overlap
proof. The proposed full-order raw class is retired rather than polished
into another existence packet.

## Exact response-quotient overlap correction

Status: source audit and ordinary 2 by 2 calculation. This section
supersedes every earlier suggestion that the triangle's EXISTENCE class
was absent from the implementation. The standalone triangle proof has
not been falsified; the error was the earlier incomplete source search.

### Named inspected source chain

The relevant maintained toolkit route is stationary response-invariant
quotients. Its exact declarations, read under their imports, are:

- `QuittingResponseInvariantOnUnitCube`,
  `quittingSingletonBlockRowSum`, and `quittingResponseQuotientMatrix`, in
  `UniformEquilibrium/Quitting/Stationary/ResponseInvariantQuotient.lean`;
- `responseInvariant_of_reward_subgroup_automorphisms`, in
  `UniformEquilibrium/Quitting/Stationary/ResponseInvariantQuotientPlayerOrbits.lean`;
- `finFour_exists_uniformEquilibriumPayoff_of_responseQuotient_nonnegative_inverse`
  and `finFour_responseQuotient_r0Degree_eq_one_of_no_uniformPayoff`, in
  `UniformEquilibrium/Diagnostics/Quitting/FinFourResponseQuotientCriterion.lean`;
- `exists_uniformEquilibriumPayoff_of_responseInvariant_noSingletonBlocks`, in
  `UniformEquilibrium/Quitting/Stationary/ResponseInvariantQuotientStrategic.lean`;
- `exists_stationaryTerminalNash_sameProfileUniform_of_responseInvariant_singletonSign`,
  in `UniformEquilibrium/Quitting/Stationary/ResponseInvariantQuotientSameProfile.lean`;
- `exists_finset_r0Degree_eq_sum_sign_det`, in
  `MathUE/LinearProgramming/R0DegreeSum.lean`.

The automorphism theorem takes literal covariance of every coalition row
under a subgroup of player permutations and produces response invariance
on its orbit blocks. Thus the table involution used here supplies its raw
hypothesis directly. The blocks each have two players, so no singleton-block
sign, normality, or Never-boundary strategic witness is needed. The
quotient entries are SUMS of singleton margins over blocks, including the
nonzero diagonal block sum. The quotient is not a smaller quitting game.

### The complete Klein-four hard branch

With the earlier notation A=1-a_t>0 and B=a_u+a_v-2>A, the orbit quotient
is exactly

    M=[[-A,B],[B,-A]],
    det M=A^2-B^2<0,
    M^(-1)=[[-A,-B],[-B,-A]]/(A^2-B^2)>0 entrywise.

All literal hypotheses of
`finFour_exists_uniformEquilibriumPayoff_of_responseQuotient_nonnegative_inverse`
are supplied by these raw calculations and the automorphism adapter.
It produces original-game UE without assuming R0, a root, or a strategy.
For the stronger stationary conclusion, this matrix is directly R0:
neither singleton support can solve zero-offset complementarity because
its diagonal is nonzero, and its full block is invertible. Its positive
inverse and negative determinant give degree -1; the inspected
same-profile theorem produces an exact stationary terminal Nash profile
and its own fixed uniform target, since both blocks have size two.

Therefore even the exact-stationary part of the formerly claimed new
branch is already covered. The other signed/circulant/rare-owner branches
were already recognized as existing consumers. The complete signed theorem
is a correct alternative proof and class corollary, not missing existence
scope suitable for the export gate.

### The one-involution extension needs no diagonal-order restriction for UE

For its two orbit blocks put a=A0>0, c=B1>0, d=A1, and
b=r_0({2})+r_0({3})-2s0. Its actual quotient is

    M=[[-a,b],[c,-d]].

I now show that NO such response-invariant Fin4 table can fail UE,
independently of the seven cardinal-sum inequalities and even without the
extra condition c>max(d,0). Suppose it failed. The named same-table
criterion would produce R0 for this quotient and require its R0 degree
to equal one.

Choose a positive offset q=(q0,q1). If d>0, choose it so
T=d*q0+b*q1 is nonzero, which excludes at most one positive ratio.
Enumerate every standard complementary support:

1. Empty: the zero vector is a root with two strict positive residuals,
   contributing +1.
2. First coordinate only: x0=q0/a>0 and the other residual is
   q1+c*q0/a>0. Its active determinant is -a<0, contributing -1.
3. Second coordinate only: possible exactly when d>0 and T>0. Its
   coordinate is q1/d and its remaining residual is T/d. Its active
   determinant is -d<0, contributing -1.
4. Full support: if d<=0, the second residual q1+c*x0-d*x1 cannot
   vanish for nonnegative x, so this support is impossible. If d>0,
   R0 forces Delta=ad-bc to be nonzero: Delta=0 would have b=ad/c>0
   and a strictly positive zero-residual vector (d,c). For Delta!=0,
   the unique full-support candidate is

       x=(T,c*q0+a*q1)/Delta.

   It is positive exactly when Delta>0 and T>0. In that case its
   determinant is positive and its contribution is +1.

These roots all have strict inactive residuals and nonzero active
determinants. The exact root-sum theorem applies. For d<=0 its sum is
1-1=0. For d>0 and Delta>0, the last two roots are simultaneously present
or absent, so the sum is zero. For d>0 and Delta<0 one has b>ad/c>0,
therefore T>0; the second singleton root is present and the full root is
absent, so the sum is -1. In every case the degree is zero or minus one,
contradicting the required one.

This supplies a stronger UE existence class through already implemented
quotient machinery: one strict within-pair own-singleton advantage and
one positive opposite-block singleton surplus suffice. The triangle's
raw diagonal-order constraints are unnecessary for existence, although
its independently selected exact stationary profile may carry additional
information in degenerate quotients. No missing-class export is justified
by those constraints.

## Canonical premium-core reduction

**Status: complete ordinary proof, not independently reviewed or
Lean-checked.** This is separate from the retired reward-symmetry and
equal-hazard-ordering paths above. It uses the reviewed full-root argument
in Section 10 of
[`CODEX_MORSE__GLOBAL_QUITTING_OBSTRUCTION.md`](CODEX_MORSE__GLOBAL_QUITTING_OBSTRUCTION.md),
but weakens its constant-outsider premise by an exact finite reduction of
the positive-premium relation. It does not delete players from the actual
strategic game and requires no quiet child equilibrium.

### Self-contained raw question and finite reduction

Let I be finite. Every nonempty coalition S has finite reward vector r(S),
and write s_k=r_k({k}). Assume nonnegative participant premiums:
`r_k(S)>=s_k` whenever k belongs to S. Product roots are independent
Quit/Continue marginals; annotations are arbitrary vectors. For the UE
conclusion below the original game has four players, s is nonnegative,
live and Never rewards are zero, and deviations are unrestricted complete
behavioral strategies. The target payoff precedes the accuracy quantifier.

Call a nonempty set A a **premium trap** if, for every k in A, there is
a nonempty S contained in A with k in S and `r_k(S)>s_k`. Thus every
member of A can get a positive participant premium somewhere inside A.
The witnessing coalition may depend on k. Let C be the union of all
premium traps, with C empty when there are none.

The following elementary facts make C canonical and computable from the
finite reward table.

1. The union of two premium traps is a premium trap: each player retains
   its original witnessing coalition. Since I is finite, C is itself a
   premium trap whenever nonempty.
2. A singleton is never a premium trap, because its only participant
   coalition is its singleton. Therefore C is either empty or has at
   least two players.
3. Begin with A=I. If some k in A satisfies `r_k(S)=s_k` for every
   participant coalition S contained in A, remove k and repeat. No
   premium trap can lose a member: a removed member of a surviving trap
   would have a positive-premium witness contradicting its flatness.
   Every terminal nonempty residual is itself a premium trap, since no
   remaining member is flat. Consequently every removal order terminates
   at precisely C. This is a finite raw-data calculation, not a choice
   of strategies, chronological quitting order, or selected response root.
4. Every nonempty A not contained in C fails to be a premium trap, so
   it has some k whose participant reward is s_k on EVERY coalition
   contained in A containing k. More generally this same conclusion
   holds for every A which is not a premium trap.

These statements use nonnegative premiums when translating “no positive
premium” into exact equality. The union fact and removal argument are
otherwise purely finite combinatorics.

### The pair-core strict-leave theorem

Suppose C={i,j} and

    r_i({i,j}) < r_i({j}).

Then the full-root smooth-potential exclusion of MORSE Section 10 holds
for this ORIGINAL table, even if players outside C have positive premiums
on other coalitions. In particular, for four players with nonnegative
singletons the original game has a uniform-equilibrium payoff.

Here is the complete change to the analytic proof. Fix a bound M on all
reward magnitudes, B>M, the box K=[-B,B]^I, and its singleton lower
boundary L as in that proof. Consider any exact product root q at v in
K with the core source inequalities `v_i>=s_i`, `v_j>=s_j`, and positive
absorption. Let A={k:q_k>0} be its actual active support. Every successor
is above s and stays in K by the same endpoint and convexity arguments.

If A is not the pair C, it cannot be a premium trap: every trap is
contained in C, and neither singleton subset of C is a trap. Therefore
some k in A is flat on every participant coalition contained in A.
Under the actual opponents' product distribution, k's forced-Quit
coalition is always contained in A. Thus its Quit endpoint is exactly
s_k. Supported Quit pins its successor coordinate at s_k, returning the
full successor to L. This retains all hazards; no low-probability or
zero-probability coalition is incorrectly kept in the expectation.

If A=C, all other hazards are zero. The designated player's endpoint
gap is

    (1-q_j)(s_i-v_i)+q_j[r_i({i,j})-r_i({j})] < 0,

contradicting q_i>0. This exhausts every support. Hence the same full-root
return property to the SAME L holds on the original core-floor region.

The remaining proof does not use global outsider flatness at all. The
singleton-face derivative inequality uses only actual small sole-owner
Nash roots and smoothness. A minimizer of a putative potential on L
cannot have a single binding coordinate. If only i,j bind, the face
inequality with owner j contradicts `r_i({j})>s_i` and the feasible
gradient signs. Thus some binding coordinate lies outside C. Lower all
such binding coordinates by epsilon and leave the two core coordinates
unchanged. All-Continue is no longer Nash. Every selected finite-game
Nash root absorbs positively and returns to the original L by the support
argument just proved. Its upward motion in a lowered coordinate is at
least epsilon, so its absorption is at least epsilon/(M+B). Potential
minimality forces the directional potential quotient to be at least
1/(M+B), but differentiability makes its limit the negative sum of
nonnegative binding gradients. This contradiction excludes every smooth
full-root potential.

Nonnegative singletons still identify punishment with s. In four players,
the exact existing no-UE polynomial producer contradicts this analytic
exclusion, with the all-zero-singleton case handled directly by all-Never.
Neither the removed layers nor their premiums are dropped from the
strategic game or from the no-UE producer. The UE conclusion retains
all complete behavioral deviations and one fixed payoff target.

### A strict raw enlargement with exact old-gate falsifiers

Start with the complete fifteen-row R=4 table in KREIN's independent
review, also independently checked in
[`CODEX_MORSE__GLOBAL_QUITTING_OBSTRUCTION__BY_CODEX_BROUWER.md`](../feedback/CODEX_MORSE__GLOBAL_QUITTING_OBSTRUCTION__BY_CODEX_BROUWER.md).
Its only positive participant premiums are

    r_0({0,3})-s_0=1,       r_3({0,3})-s_3=1,
    s=(1,0,0,0).

Make just one further change:

    r_1({0,1,2})=1/2.                                   (P)

All other entries remain unchanged. Player 2 is globally flat. After
removing 2, player 1 is flat on the remaining subtable, since its sole
positive premium (P) required 2. The residual pair {0,3} is a premium
trap, and `r_0({0,3})=2<4=r_0({3})`. The new theorem therefore applies.
Three distinct players 0,1,3 now receive positive participant premiums,
so no designation of two players satisfies the old constant-outsider
hypothesis. This is a strict raw-class extension, not a relabeling.

The prior matrix, degree, inverse, response-quotient, and product-low
falsifiers are unchanged. The singleton matrix is literally unchanged,
and the only first-order quotient survivor remains `{0}|{1,2,3}`. At
hazards `(x,0,0,0)`, modification (P) is invisible to every forced-Quit
endpoint, so the exact residuals remain `x,x,x+x*x`. The root supported
on {0,3} still has two positive expected active premiums. The no-pure-exit
proof is unchanged: a coalition with 0 but not 3 still invites 3;
with both 0 and 3 the pivot prefers leaving; without 0 the child-cycle
argument is untouched.

All fourteen proper-child five-kind F/J falsifiers remain valid, not
merely close to valid. The periodic {1,2,3} child never involves player
0, even in any child deviation, so (P) cannot affect its exact Nash
inequalities. Every sure-quit child containing 0 but not 3 remains
exact Nash: (P) only increases a prescribed participant's Quit payoff.
The favorable-solo-child and sure-owner-3 witnesses never see (P) in
their child best-response comparisons. On the delicate child {0,2,3},
the entire child table and hence its exact first-date root are unchanged.
Only the omitted player 1's joining payoff increases: it is now 1/4,
because the other players form {0,2} with probability 1/2 and its new
reward there is 1/2. Its passive payoff remains -5/6. Thus its strict
outside debt increases. All these laws still have zero child debt and
zero joint-Never probability, excluding every weight choice in the
five-kind universal bound. This comparison is restricted to those named
gates, not to every possible selected-child argument.

### Exact source overlap and surviving raw class

The bounded source audit inspected:

- `HasWeakQuittingPremiumSupportPeeling`,
  `hasWeakQuittingPremiumSupportPeeling_iff`, and
  `weakQuittingPremiumSupportPeeling_iff_playerRanking` in
  `UniformEquilibrium/Quitting/Classification/QuittingPremiumSupportPeelingOrder.lean`;
- `hasProductLowQuittingPremium_iff_weakSupportPeeling_of_nonnegative`
  in `UniformEquilibrium/Quitting/Classification/NonnegativeProductLowSupportPeelingConverse.lean`;
- `HasFiniteCoalitionSupportPeeling` and
  `finiteCoalitionSupportPeeling_iff_playerRanking` in
  `MathUE/FiniteCoalitionSupportPeelingOrder.lean`;
- the full-root, punishment, and polynomial declarations already recorded
  in the independent MORSE feedback linked above.

The existing peeling predicate requires a flat participant in EVERY
nonempty support; equivalently C is empty. It does not allow the residual
premium pair. The source product-low theorem therefore does not already
give the pair-core conclusion. The canonical removal process is useful
only because the strict-leave analytic mechanism now treats that residual
pair in the ORIGINAL game, without a quiet-lift premise.

Consequently any four-player counterexample with nonnegative singletons
and nonnegative participant premiums must have either:

1. a canonical premium core of at least three players; or
2. a canonical premium core {i,j} with BOTH
   `r_i({i,j})>=r_i({j})` and `r_j({i,j})>=r_j({i})`.

The empty core is already handled by the existing product-low theorem;
a one-player core is impossible; a pair with either strict leave
preference is handled above. This is a raw surviving-class reduction,
not a claim that either surviving alternative actually lacks equilibrium.

### Compatibility with the completed mutual-stay index mechanism

MORSE Section 12 now supplies the mutual-strict-stay root-index mechanism
for globally constant outsiders; my independent review of that section
passes. It has two outsider-flatness uses, both supplied by the canonical
pair core in the original table:

1. A root support other than the residual pair has a flat active
   participant, so its successor belongs to L as proved above.
2. For any outsider k and any T contained in the residual pair,
   `r_k(T union {k})=s_k`. Otherwise the residual pair union {k} would
   be a premium trap: each core member retains its positive pair witness,
   while k has the alleged new witness. This contradicts maximality.
   Thus every outsider forced-Quit endpoint against a core-only root is
   exactly s_k, as needed both for the harmed-outsider test and for the
   affine annotation tie removal.

The full clipped-root map, unique mixed core candidate, negative local
index, and total degree +1 then operate on the unchanged full table.
The weak-leave closure changes only a passive reward and therefore does
not change the premium core. This gives the same full two-player-core
conclusion through the completed index proof, subject to independent
review of this peeling transfer. It does not cover three-player cores.

## Three-player premium core: an exact unique-root obstruction

**Status: complete ordinary falsifier, not independently reviewed or
Lean-checked.** This is a failure of a proposed root-return/index
extension, NOT a game without a uniform equilibrium and NOT a smooth
potential for the game. It identifies a concrete larger-core boundary
before trying to generalize the two-core argument.

### The exact table and question

On I={0,1,2,3}, let the child cycle be 1 to 2 to 3 to 1. For every
nonempty S, begin with

    r_0(S)=1 if 0 belongs to S, otherwise 4*1_(3 belongs to S);
    r_j(S)=0 if child j belongs to S,
           -1 if j is absent and 0 belongs to S,
           2*1_(pred(j) belongs to S)-1_(succ(j) belongs to S) otherwise.

Change exactly the following three participant coordinates:

    r_0({0,3})=2,       r_3({0,3})=1,       r_1({0,1})=1/2.       (Q)

This starts again from the R=4 base table, NOT from the preceding
triple-premium modification (P). The singleton vector is (1,0,0,0),
every participant premium is nonnegative, and player 2 is globally flat.
The greatest premium trap is {0,1,3}: players 0 and 3 have their pair
witness, and player 1 has {0,1}. No trap can contain globally flat 2.

The question tested is whether a below-floor annotation always has some
exact Nash root returning to the singleton lower boundary, or whether
the global degree +1 of the actual clipped Nash map forces such a root
once only one three-player-supported root can avoid that boundary.
Both implications fail on this literal table.

Set

    v=(9/10,-1/10,1,253/725),
    p=(11/156,11/71,0,1/10).                            (R)

The full simultaneous game at v has EXACTLY ONE Nash root, namely p.
Its successor is

    T_p(v)=(77/71,33/1040,18419/22152,55/923),           (S)

strictly above every singleton. Its absorption is positive, and
all-Continue is not Nash since two annotations are below their own
singletons. The full clipped ambient root has local index +1, not -1.

### Literal endpoint polynomials

Write q=(x,y,z,t), h=253/725, and A=(1-y)(1-z). For this exact source
the four Quit-minus-Continue gaps, including all collision rewards, are

    g_0=1-(9/10)A-t[4-(19/10)A],
    g_1=(1/2)x(1-z)(1-t)+x
              -(1-x)[2t-z-(1/10)(1-z)(1-t)],
    g_2=x-(1-x)[1+y-2t+yt],
    g_3=x(1+A)-(1-x)[2z-y+hA].                         (T)

The own hazard is absent from its own gap, as required. Exact Nash means
g_k<=0 at hazard zero, g_k>=0 at hazard one, and g_k=0 in the interior.
Substitution of (R) gives gaps

    (0,0,-18419/22152,0),

so p is exact Nash and the outsider strictly Continues. The three active
successor coordinates are their forced-Quit endpoints; the inactive
coordinate is its Continue endpoint. This gives (S) exactly.

### No exact root can activate player 2

Suppose z>0. Then g_2>=0. If x=1, g_2=1 forces z=1, after which
g_3=1 forces t=1; but then g_0=-3, contradicting x=1.

If x=0, put B=1+y-2t+yt. The inequality g_2>=0 gives B<=0 and
hence t>=1/2. Now

    g_1=z-2t+(1/10)(1-z)(1-t)
        <=-(19/20)(1-z)<=0.

If y>0, its supported Quit would force equality throughout, in particular
z=1 and t=1/2. But B then equals 3y/2>0, impossible. Hence y=0.
The gap g_3 becomes `-[2z+h(1-z)]<0`, forcing t=0 and contradicting
t>=1/2. Therefore x is strictly between zero and one.

Now g_0=0 gives

    t=[1-(9/10)A]/[4-(19/10)A] in [1/21,1/4].

Consequently B>=1/2>0, and g_2>=0 gives x>=B/(1+B). We have

    x-(1-x)2t >= (B-2t)/(1+B) >=0,

because `B-2t=1+y-4t+yt>=0`. Expanding g_1 as this nonnegative
quantity plus

    (1/2)x(1-z)(1-t)+(1-x)[z+(1/10)(1-z)(1-t)]

shows g_1>0, using z>0 and x<1. Hence y=1. Then A=0, t=1/4,
B=7/4, and x>=7/11. But

    g_3=x-(1-x)(2z-1)>=2x-1>0,

forcing t=1, a contradiction. This exhausts all possibilities with z>0.

### Unique root on the remaining three-player face

We now have z=0. The case x=1 again gives g_3=2-y>0, t=1,
and g_0=-2-y<0, impossible. If x=0, then
`g_1=1/10-(21/10)t`. For y=0 the Nash inequality forces t>=1/21,
but g_3=-h<0 forces t=0. For y=1 it forces t<=1/21, but then
g_0=1-4t>0 contradicts x=0. For 0<y<1 it gives t=1/21 and
g_0=(17/21)y>0, again impossible. Thus 0<x<1.

The equation g_0=0 now yields

    t=(1+9y)/(21+19y),                                 (U)

so 0<t<1. At y=0, (U) gives t=1/21 and the gap g_1 is strictly
positive because x>0. At y=1, the gap g_3=1 forces t=1, contradicting
(U). Therefore 0<y<1 as well, and all three active gaps must vanish.

Solving g_1=0 after (U) gives

    x=17y/(31+41y).

The remaining equation g_3=0 is exactly

    h = y(65+7y)/[(31+24y)(1-y)].                       (V)

The right side is strictly increasing on (0,1): after clearing the
positive squared denominator, its derivative numerator is

    2015+434y+1511y*y>0.

Substitution of y=11/71 gives h=253/725. Thus (V) has this unique
solution, and (U) then gives t=1/10 and x=11/156. Together with the
exclusion of z>0, this proves uniqueness for the FULL four-player game,
not merely uniqueness on a selected support face.

### Why the two-core index mechanism cannot supply another root

At p the outsider gap is strictly negative, so its row in the ambient
clipped map `F(q)=clip(q+g(q))` is locally constant zero. In the coordinate
order (0,1,3), the active gap Jacobian is exactly

    J=[[0,71/100,-170/71],
       [39/25,0,-155/78],
       [20436/10295,71/60,0]].

The inactive coordinate contributes an identity block to the derivative
of q-F(q). Therefore

    det(I-DF(p))=det(-J)=1047/145>0.

The local fixed-point index is +1, consistently with its being the only
fixed point of a cube-valued ambient map. Its sign pattern already
explains the difference from the pair case: a zero-diagonal 3 by 3
matrix with rows `(0,+,-)`, `(+,0,-)`, `(+,+,0)` has negative
determinant, hence its negative has positive determinant.

The degree facts and explicit clipped-map interpretation are the same
ones inspected in my Section 12 MORSE review. No Nash-index axiom or
generic-root assumption is needed for this exact nonsingular example.
The rational endpoint, successor, and determinant identities were also
checked independently by symbolic arithmetic; the displayed algebra is
the proof rather than a floating-point root enumeration.

### Coverage and exact limitation

The centered singleton matrix and all matrix-degree/inverse failures are
unchanged from the independently reviewed R=4 fixture. Its sole candidate
nondiscrete response partition still fails: at `(u,0,0,0)` the three
child residuals are now `u+u*u/2`, `u`, `u+u*u`, not equal. The no-pure
coalition argument is unchanged. The proper-child F/J witnesses also
remain exact: the only child collision changed is {0,1}, where the
prescribed participant 1's Quit reward increases; the periodic {1,2,3}
child contains no 0, and the delicate {0,2,3} child's omitted-1 joins
always involve sure player 2, so never use the changed pair. Hence the
same all-fourteen-child zero-debt/positive-outsider-debt contradiction
survives.

Nevertheless, no claim is made that this game lacks a UE. The annotation
v need not be realizable as a continuation payoff. This example refutes
universal boundary-return and the automatic negative-index extension to
three premium-core players. It does not assert that v is a particular
smooth potential's minimizing-face perturbation, nor construct such a
potential on all sources. A new size-three-core proof must use information
beyond the mere count of exceptional roots and total degree +1.

## Current next question

For the explicit size-three-core table (Q), what global payoff or
continuation mechanism bypasses its unique interior-successor root? A
useful positive construction must handle the unchanged positive-debt
quiet-child witnesses and unrestricted behavioral deviations. Do not
weaken the now-exact local root-return falsifier into a conjecture, or
interpret it as a uniform-equilibrium counterexample.

## A solo-0 bridge pays a positive outsider cap

**Status: complete ordinary candidate proof, not independently reviewed
or Lean-checked.** This construction uses global continuation values,
not a second-root assertion at the preceding falsifier. The explicit
four-core example below is not that three-core table. The final source
audit records precise exclusions of the latest named families, without
claiming an exhaustive classification of every conditional consumer.

### Self-contained raw class

There are four players, independent Continue/Quit choices at every
nonabsorbed date, publicly observed past actions, and no external
correlation. First nonempty quitting coalition S pays r(S) forever;
perpetual continuation pays zero. All unspecified entries below are
arbitrary finite real numbers. The desired conclusion is one fixed
uniform-equilibrium payoff for the original table against complete
behavioral deviations.

Let a,b,c,h1,h2,h3,eta be strictly positive, with abc>1, and let
u<=1, v<1, R real. Prescribe the five complete vectors

    r(0)  = (1,-h1,-h2,-h3),
    r(1)  = (u,0,b,-1),
    r(2)  = (v,-1,0,c),
    r(3)  = (R,a,-1,0),
    r(01) = (1,eta,-h2,-h3).

Thus s=(1,0,0,0). Impose only the following six outsider bounds:

    r2(02), r2(12), r2(012) <= 0,
    r3(03) <= lambda,  r3(13), r3(013) <= 0,

where lambda>=0. Suppose there exists a real theta such that

    0 < theta < eta/h1,       lambda <= h3*theta.       (B1)

Equivalently, the potentially positive cap may be any lambda with
0<=lambda<h3*eta/h1. No assumption is made on pair-23 participant
premiums, on the pivot's participant reward at 03, or on any omitted
higher-coalition entries. Condition (B1) deliberately keeps the
effective premium below strictly positive; the equality limit is not
needed for this candidate.

**Claim.** Every such raw table, for every real R, has a uniform-
equilibrium payoff. The middle parameter interval has the explicit
four-phase producer below; the complementary intervals are consumed
by the same original-singleton-matrix exits as the reviewed cyclic
producer, without changing any reward.

### A scalar selector with zero pivot pair premium

Put D=abc-1, L=ac+a+1, Y=D/(b*L), and

    A = [[0,-1,a],[b,0,-1],[-1,c,0]],
    nu = A^(-1)*(h1,h2,h3),
    eta_eff = (eta-h1*theta)/(1+theta) > 0,
    Rlow = 1+((1-u)*nu1+(1-v)*nu2)/nu3,
    Rtop = 1+ac*(1-u)+a*(1-v).

All components of nu are positive since

    A^(-1) = [[c,ac,1],[1,a,ab],[bc,1,b]]/D.

Moreover Rtop>Rlow, because

    nu3*(Rtop-Rlow)
      = (1-u)*(c*h1+h3)+(1-v)*h1 > 0.

For each y in (0,Y), define K as the unique root in

    0 < K < min(b*y/h2, (c-(c+1)*y)/h3)

of the equation

    z = (h3*K+y)/(c*(1-y)),
    w = (b*y-h2*K)/(1+b*y+(1-h2)*K),
    0 = h1*K+z-a*w*(1-z)
        +eta_eff*K*(1-(1-z)*(1-w)/(1+K)).             (B2)

Here K,y,z,w depend on y. To verify existence, uniqueness, and
continuity directly, set C=c*(1-y), E=c-(c+1)*y,
d0=1+b*y, d1=1-h2. Multiplying the last equation by
C*(d0+d1*K) gives the quadratic alpha*K^2+beta*K+gamma, where

    alpha = h1*C*d1+h3*d1-a*h2*h3
              +eta_eff*(C*d1+h3),
    beta  = h1*C*d0+h3*(d0+a*b*y)+y
              +h2*(a*E-y)+eta_eff*y*(C*b+1),
    gamma = y*(b*L*y-D).

The denominators are positive throughout the closed cap interval:
d0+d1*K>=1+K and C>0. Also beta>0 because
a*E-y=ac-L*y>=1/b on [0,Y]. The polynomial is negative at K=0
for interior y, and positive at the cap: there either w=0 or z=1,
making the right side of (B2) strictly positive. A quadratic with
positive linear coefficient has exactly one crossing from negative to
positive on this interval. Its selected root is

    K = -2*gamma/(beta+sqrt(beta^2-4*alpha*gamma)),

valid also at alpha=0. This root is continuous and tends to zero
at both endpoints. Expanding (B2) at zero gives
K/y->1/nu1, z/y->nu2/nu1, w/y->nu3/nu1.

Define the pivot selector

    P(y) = 1 + [ (1-u)*y/(1-y)+(1-v)*z ]/[(1-z)*w].  (B3)

It is continuous on (0,Y), tends to Rlow at zero, and tends to
Rtop at Y. At the upper endpoint K=0 and (B2) says
z=a*w*(1-z); combined with z=y/(c*(1-y)), these give the stated
upper limit directly. Thus for every R in (Rlow,Rtop), the
intermediate value theorem supplies y with P(y)=R. No monotonicity
or unique y is claimed or needed.

This selector is the zero-pivot-premium specialization of the reviewed
quadratic mechanism in
[`CYCLIC_CHILD_WITH_ONE_JOINT_PHASE.md`](../exports/CYCLIC_CHILD_WITH_ONE_JOINT_PHASE.md).
That packet states a strictly positive pivot premium, so it cannot be
invoked as a black box here. The explicit calculation above supplies
the necessary extension: its nonpivot quadratic is independent of that
premium, and u<=1 supplies the now-weak pivot floor.

### Four exact phase values

Set

    k=K/(1+theta),  x=k/(1+k),  rho=theta*x/(1+theta*x).

Use four successive stages, repeating after nonabsorption:

    A: joint hazards x for player0 and y for player1;
    B: solo player2 with hazard z;
    C: solo player3 with hazard w;
    D: solo player0 with hazard rho.

The phases B,C,D will subsequently be diffused. Write d for the
value before D and t for the value before A. They are

    d = (1, eta_eff*K/(1+K), w/(1-w), 0),
    t = (1, eta*x,
         h2*theta*x+(1+theta*x)*w/(1-w),
         h3*theta*x).

The intervening vectors are

    V_C = ( (1-w)+R*w, (1-w)*d1+a*w, 0, 0 ),
    V_B = ( v*z+(1-z)*V_C0, (1-z)*V_C1-z, 0, c*z ).

These are exact Bellman values for every coordinate. At phase D,
d=(1-rho)*t+rho*r(0). The identity for d1 uses
eta_eff=(eta-h1*theta)/(1+theta). The identity for d2 follows from
the definition of t2; d3=0 is the purpose of the bridge.

At A, the player-0 Quit and Continue endpoints both equal 1 by (B3).
Player1's Quit endpoint is eta*x. Its Continue endpoint agrees because

    V_B1=K*(h1+eta_eff)=k*(h1+eta).

For player2, the literal passive average is

    -h2*x+(1-x)*b*y = t2.

For player3 it is

    -h3*x+(1-x)*[-y+(1-y)*c*z] = h3*theta*x = t3.

The latter equality uses K=(1+theta)*k. Thus the added phase has
converted an old zero value at the undiffused joint stage into a
positive value, while leaving the effective source d at the old
three-phase value.

At B the solo owner2 has both endpoints zero; at C owner3 has both
endpoints zero; at D owner0 has both endpoints one. Every player at
every phase has a value at least its singleton. For the pivot this
uses V_B0=(1-u*y)/(1-y)>=1 and R>Rlow>1; the other floors follow
from the displayed positive quantities. All pure-Continue endpoints
equal the current phase value, not only its prescribed mixed average.

At the undiffused phase A the only outsider tests are players2 and3.
The three player2 caps give Q2<=0<=t2. The player3 caps give

    Q3 <= lambda*x*(1-y) <= h3*theta*x = t3.           (B4)

This is the genuine new accounting step: r3(03) can be strictly
positive even when both other player3 caps are zero. It is paid by a
continuation value, not by a cancellation with a negative collision
reward. All active endpoints and all four full-response tests at A
have now been checked.

### Diffusion, a fixed target, and complete behavioral deviations

Replace each solo stage of rate q in {z,w,rho} by n stages of rate
q_n=1-(1-q)^(1/n). Keep A unchanged. The product survival over each
block remains 1-q, so t is the same exact prescribed payoff for all n.
Within a solo block of owner j, values are convex interpolants between
its two endpoint vectors; the j coordinate is identically s_j.
Thus all singleton floors, prescribed-policy equalities, and pure-
Continue equalities hold at every refined row.

Let

    Cjoin=max(0, r_i({i,j})-s_i : j in {0,2,3}, i!=j),
    e_n=Cjoin*max(z_n,w_n,rho_n).

Then e_n tends to zero. At any refined row the forced-Quit endpoint
of a nonowner is at most s_i+Cjoin*q_n, hence at most V_i+e_n.
The owner is exact. Together with (B4), EVERY row's Quit endpoint is
at most its value plus e_n, and every Continue endpoint is exactly its
value. Adding the same e_n to each continuation value therefore gives
a supersolution for both unilateral actions. The error is charged once
at eventual quitting, not once per date or period.

This proves unrestricted behavioral safety directly: after any history
that has not absorbed, the public date identifies the current row and
the opponents still use their prescribed independent coins. Their
probability of all continuing over one full period is a fixed rho_i<1
for every deviating player i, since each of the other three players
has positive total hazard. Hence absorption under any complete
behavioral deviation is almost sure, uniformly in the deviator's
stopping rule; bounded supersolution remainders vanish. Its terminal
payoff is at most t_i+e_n. The prescribed profile delivers exactly t.

For a direct finite-horizon bound, put m_n=1+3n and
Ctime=max_i m_n/(1-rho_i). Pre-sample the opponents' independent
coins. Under any deviation actual absorption occurs no later than
the first prescribed opponent quit, whose expected date is at most
Ctime (with the harmless usual date-index adjustment). With M bounding
all terminal payoffs, terminal versus N-stage-average expected payoff
differs by at most 2*M*Ctime/N, uniformly over the deviator. Thus

    regret_N <= e_n+4*M*Ctime/N,
    |prescribed average_N-t| <= 2*M*Ctime/N.

Choose n for the requested accuracy, then one horizon threshold for
all larger N. The target t is fixed before that choice. This is also
exactly the quit-error/Continue-equality hypothesis of the inspected
`QuittingInfinitePathQuitErrorCertificate` and
`isUniformEquilibriumPayoff_of_arbitrarily_small_infinitePath_quitError`
in `UniformEquilibrium/Quitting/Paths/InfinitePathSupersolution.lean`.
The direct argument shows why no bounded-controller or finite-number-
of-periods restriction on the deviator is being used.

### Original-table exits for all other real R

The only data used by these exits are the four prescribed singleton
vectors, so the bridge parameters and arbitrary unused entries do not
alter them. For R<Rlow the centered full singleton matrix is R0 and
has degree zero, by the two-root active-determinant calculation in the
reviewed quadratic packet. At R=Rlow, (1,nu) is a nonzero homogeneous
complementarity solution; the Fin4 no-UE degree criterion therefore
excludes this case too. For R>=Rtop the child A has nonnegative inverse,
and its passive pivot weights are

    [bc*(R-T1), R-T2, b*(R-T3)]/D,
    T1=1+[c*(1-u)+(1-v)]/(bc),
    T2=Rtop,
    T3=1+[(1-u)+ab*(1-v)]/b.

Here T2>=T3>T1 because u<=1 and v<1. The weights are nonnegative,
including equality R=Rtop. The actual original-table declarations
previously inspected for these exits are
`exists_uniformEquilibriumPayoff_of_r0Degree_ne_one` in
`UniformEquilibrium/Quitting/Classification/LCP/SingletonDegreeCriterion.lean`,
`finFour_singleton_r0Degree_eq_one_of_no_uniformPayoff` in
`UniformEquilibrium/Diagnostics/Quitting/FinFourSingletonDegreeCriterion.lean`,
and `exists_uniformEquilibriumPayoff_of_raw_nonnegativeInverse_triple` in
`UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/RawPassiveRowInverseCriterion.lean`.
None adds a condition on the unspecified nonsingleton entries.

### Exact full-core fixture and honest remaining overlap boundary

Take a=b=c=2, h1=h2=h3=1, u=v=0, eta=31/11,
lambda=theta=1/2, R=347/92. Then eta_eff=17/11 and

    K=1/10, y=1/4, z=7/30, w=4/15,
    x=1/16, rho=1/33.

The four value vectors are exactly

    t   = (1,31/176,13/32,1/32),
    V_B = (4/3,14/55,0,7/15),
    V_C = (40/23,7/11,0,0),
    d   = (1,17/121,4/11,0).

Complete the unprescribed rows as follows:

| S | r(S) |
|---|---|
| 02 | (1,-1,0,-1) |
| 03 | (2,-1,-1,1/2) |
| 12 | (0,0,0,1) |
| 13 | (347/92,0,1,0) |
| 23 | (347/92,1,1/2,1/2) |
| 012 | (1,0,0,-1) |
| 013 | (1,0,-1,0) |
| 023 | (1,-1,0,0) |
| 123 | (347/92,0,0,0) |
| 0123 | (1,0,0,0) |

Exact symbolic evaluation checked all sixteen policy identities and
all sixteen pure-Continue identities. At A the endpoint pairs are
(1,1), (31/176,31/176), (13/32,0), (1/32,3/128), so the formerly
problematic outsider3 is strictly safe. In the unrefined profile,
player2 has a positive Quit gain 2/15 at C and player3 has gain 1/66
at D. Thus diffusion is genuinely required for this completion; those
gains are not being discarded.

The complete positive-premium trap list is 03,013,23,023,0123. The
greatest premium core is all four players. The only common member of
all traps is 3, and player3 strictly prefers joining 0:
r3(03)=1/2>r3(0)=-1. Consequently neither the core-at-most-two class
nor MORSE's common weak/strict trap-leaver criterion admits this table.
Every pure quitting coalition has a strict toggle improvement, checked
directly in the complete table. The old one-joint-phase caps also fail
at r3(03)>0; selecting pair03 instead violates the pivot comparison
r0(03)>=r0(3).

### Completed bounded source audit for the full-core fixture

The switched-joint-pair theorem requires two of the pivot's passive
singleton rewards to be at least its own singleton. This fixture has
only one: r0(3)=347/92, while r0(1)=r0(2)=0<1. The unique
player with positive own singleton is 0, so relabeling the nonpivot
cycle cannot meet that raw requirement. This is a comparison with
the exact switched-family hypotheses, independently reviewed in my
KREIN feedback, not with all possible phase laws.

Its centered singleton matrix is

    Gamma=[[0,-1,-1,255/92],
           [-1,0,-1,2],[-1,2,0,-1],[-1,-1,2,0]].

The 123 child has positive inverse A^(-1) and uniquely solves
Az>=t*1, z>=0, z_i(Az-t*1)_i=0 by z=t*1 for t>0;
its homogeneous problem has only zero. Therefore the full matrix is
R0: a positive homogeneous pivot h would force child h*1 and
pivot residual (71/92)*h>0. At offset (1,-1,-1,-1), the unique
root is (0,1,1,1), its inactive residual is 163/92, and the active
determinant is 7. Its degree is +1. The only nonnegative-inverse
triple is 123, whose passive row is

    (186/161,-297/644,25/322).

The other triples have negative inverse entries: -2 for 012,
-255/439 for 013, and -92/301 for 023. The full inverse has
entry -744/497 in row0,column1. No pair has two positive
off-diagonal entries. Principal02 is R0 but non-Q, by its matrix
[[0,-1],[-1,0]] and the infeasible offset (-1,-1).

Exact enumeration of all fifteen response partitions leaves only the
discrete partition and 0|123 at first order. The latter fails at
the actual root (t,0,0,0), where the three child response residuals
are t+(31/11)*t^2, t, and t+t^2/2. These are unequal for t>0.
Thus the full response-quotient hypothesis also fails. The degree,
inverse, and response criteria are the same named declarations
independently inspected in the preceding reviews, including
`quittingSingletonBlockRowSum_eq_of_responseInvariant` in
`UniformEquilibrium/Quitting/Stationary/ResponseInvariantQuotient.lean`.

There are exact zero-regret/positive-outside-gain witnesses for thirteen
of the fourteen proper children. For singletons use their sure exit.
For children01,02,012, let every child member quit surely. For
03,13,013 use sure3; for12 use sure1; for23 use sure2.
Every chosen child profile is exact terminal Nash, and a missing
nonpivot currently receiving -1 can join for at least zero. All these
claims were checked directly in the complete table, including the
case where the sole quitting player instead delays forever.

For child023, use one date with hazards

    (q0,q2,q3)=(3/5,1,92/347),

then Never. The endpoint pairs for its players are exactly

    (1,1), (-245/347,92/1735), (1/5,1/5).

The profile absorbs surely. Player2's only possible post-deviation
survival leaves opponents at Never and has maximal continuation zero,
already included in the displayed Continue value. Hence these are
full behavioral comparisons. Omitted player1 has Continue payoff
-1367/1735 and Quit payoff zero.

The formerly useful EXACT child123 cycle is genuinely broken by the
positive pair23 premiums. At its player3 phase, player2 can join
profitably. This exact failure is retained; no old witness is reused.
Instead, take the child cycle of aggregate hazards 1/2 in order1,2,3,
and refine EACH solo phase into n equal microhazards

    alpha_n=1-2^(-1/n).

The three child phase vectors remain (0,1,0),(0,0,1),(1,0,0).
All their refined values are nonnegative, pure-Continue is exact, and
the only positive pair surpluses are the two 1/2 values at23. The
standard single-error supersolution therefore bounds every child's
full terminal regret by alpha_n/2. Prescribed joint Never has mass
zero. The quiet pivot's payoff is fixed at R/7=347/644, since
refinement does not change any aggregate singleton-exit probability.
Immediate Quit at the first microstage of player1 pays exactly one:
r0(0)=r0(01)=1. Its gain is thus the fixed 297/644 for EVERY n.

This limiting witness is sufficient to exclude universal debt bounds.
Indeed, any finite nonnegative weight vector would bound that fixed
outside gain by at most (sum weights)*alpha_n/2, plus a zero
joint-Never term, which tends to zero. I re-read the exact source
`withdrawalFutureJoin_quietLift_outsideDebt_le_add_neverExcess` in
`UniformEquilibrium/Quitting/Classification/QuietExtension/WithdrawalFutureJoinDebt.lean`.
Its quantifier is over EVERY child profile and its debt weights and
Never coefficient are fixed by the reward certificate. Consequently
all five such certificate kinds fail here too. An exact child
equilibrium is convenient but not necessary for this contradiction.
This excludes the specified universal quiet-debt families, not every
possible selected-child construction.

Concrete next question: independently falsify the complete bridge
producer, then seek an exhaustive global continuation-value mechanism
which chooses among joint phases or accounts rather than another
scalar refinement of this one fixed chronological grammar. The exact
three-core unique-root obstruction remains a valid stress test, not
a request to find a forced second root.
