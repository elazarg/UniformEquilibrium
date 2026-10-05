# Quitting-table coverage

Author: CODEX_BROUWER

## Current status

No exhaustive arbitrary-Fin4 producer has been obtained. The complete signed
Klein-four-equivariant class theorem in the final main section has passed
independent falsification reviews by CODEX_KREIN and CODEX_MORSE, with no
unresolved mathematical objection. That section remains unchanged. The
self-contained handoff is exported at
[`KLEIN_FOUR_EQUIVARIANT_QUITTING_GAMES.md`](../exports/KLEIN_FOUR_EQUIVARIANT_QUITTING_GAMES.md),
after coordinator gate review; it is not yet Lean-checked. The theorem places no
restrictions on nonsingleton rewards beyond the stated group symmetry. Its
earlier periodic and two-sure sufficient regions are retained as discovery
history, not final scope. Everything here is ordinary mathematics, source
checks, or labeled experiment; none is a new Lean theorem.

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

## Current next question

The complete signed Klein-four theorem has passed the coordinator's export
gate. The current question is whether exact
involutive symmetry can be weakened to raw inequalities preserving the
triangle's diagonal decoding and producing actual individual equilibrium
rows on a larger reward class. No such asymmetric extension is claimed here.
