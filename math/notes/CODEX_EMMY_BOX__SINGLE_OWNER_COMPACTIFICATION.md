# Single-owner compactification and global record selection

Author: CODEX_EMMY_BOX.

Status: ACTIVE ORDINARY PROOF DRAFT, not Lean
implemented and not an export candidate. This is a distinct mechanism from
the closed portfolio/quiet-lift route. An unconditional compact constrained-
Nash producer is available, with exact exits when a proper clock is bounded
or when the owner is the only proper clock. The genuinely missing step is
a GLOBAL selection or joint-law operation in the remaining case of at least
two unbounded proper clocks. No arbitrary-Fin4 UE theorem is claimed.
The bounded-support exit in Section4 has a bounded independent ordinary
check in `../feedback/CODEX_EMMY_BOX__SINGLE_OWNER_COMPACTIFICATION__BY_CODEX_NASH_BOX.md`;
that check does not cover the producer or the missing global selection.

## 1. Self-contained end-to-end question

Let I be a finite player set, in particular Fin4. Each nonempty coalition
S pays a finite vector r(S). The first finite quitting date pays its entire
simultaneous coalition; infinite all-Continue pays zero. All clocks and
private randomization are independent. Every unilateral date-or-Never law,
equivalently every complete behavioral replacement on the unique continuing
public history, is in the full response cap. Let |r_i(S)|<=R, s_i=r_i({i}),
U_i be terminal payoff, B_i the complete cap and D_i=B_i-U_i.

Choose one owner a and 0<delta<1; put c=1-delta. Restrict ONLY that owner's
law to the compact convex set

    K_delta={p: Pr_p(T>=t, including Never)<=c^t for every t>=0}.   (1)

All nonowners retain their unrestricted independent clock laws, including
arbitrary positive Never mass. The owner is uniformly proper but need NOT
be diffuse: immediate sure Quit belongs to K_delta. Thus this does not
impose the fixed-pivot small-atom hypothesis falsified elsewhere.

Let N_(a,delta) be the complete Nash correspondence of this constrained
normal-form law game. It is produced from the original finite table, not
supplied as a premise. At every p in it, D_i(p)=0 for i!=a; only the owner's
constraint loss can remain. The end-to-end source question is:

    If all s_i>=0 and some s_i>0, does there exist a sequence delta->0,
    owners a and p in N_(a,delta) with D_a(p)->0?              (Q)

One fixed uniform-equilibrium target would then follow from actual terminal
approximate Nash at all errors and the inspected bounded-target subsequence
consumer. A fixed owner, a fixed equilibrium branch or inter-accuracy nesting
is NOT required. This is a global selection question, not a scalar objective
on the old frozen root alphabet.

## 2. Unconditional actual constrained-Nash producer

Every K_delta is nonempty (it contains Geom(delta)), convex and weakly
compact in the laws on the one-point compactification of Nat. Each finite
tail in (1) is clopen, so its inequality is weakly closed. Letting t grow
forces literal Never mass zero.

On K_delta times the unrestricted nonowner-law product, ALL original
prescribed payoff functions are jointly continuous. To see this without
assuming continuity of the stopping payoff at all-Never, move the owner's
mass beyond N to the finite date N. The resulting game always absorbs by
N and depends on finitely many clopen cylinders. Its payoff functions are
continuous. The uniform payoff error is at most 2R*c^(N+1), which tends
to zero independently of all nonowner laws. Thus the original functions
are uniform limits of continuous finite-cylinder functions.

There is an exact Nash point on this domain. An elementary proof avoids
any extra discontinuous-game existence theorem. At cutoff N, let the owner
use laws in K_delta supported on0,...,N and let nonowners use
0,...,N,Never. The owner domain is a nonempty compact finite-dimensional
polytope. Treating its finitely many extreme points as pure actions, ordinary
finite mixed Nash gives a constrained equilibrium. Extract a weakly convergent
subsequence of these products as N grows. Uniform continuity above passes
every finite-date and Never nonowner response inequality to the limit.
For an arbitrary owner competitor in K_delta, move its mass after N to N;
this speeds up its law, remains in the finite constrained set, and converges
weakly to the original competitor. Its inequality also passes to the limit.
Linearity in each player's independent law covers all complete replacements.

This is an actual producer of p in N_(a,delta) for every finite table and
every owner/rate. It is not an actual unconstrained Nash producer.

## 3. The exact owner objective is a private-record envelope

Fix opponents and let f(t) be the owner's payoff from pure Quit at finite
date t. Let G have law Pr(G=g)=delta*c^g. Then

    max_(p in K_delta) E_p f(T)
      = E[ max_(0<=t<=G) f(t) ]
      = delta*sum_(g>=0) c^g max_(0<=t<=g) f(t).           (2)

For the upper bound, couple any p in K_delta with G by common quantiles;
its stochastic dominance gives T<=G pathwise. Conversely choose, after
privately sampling G, the first maximizer of f over0,...,G. This is an
actual owner clock with T<=G, hence belongs to K_delta and attains the
right side. There is no public seed, correlated opponent law or convexity
assumption on the attainable JOINT independent-law set.

If s_a>=0, the complete cap is sup_t f(t): the Never value does not exceed
the late finite-date limit, including arbitrary opponent Never masses.
Thus at constrained Nash the exact remaining loss is

    D_a = sup_t f(t) - E[max_(0<=u<=G) f(u)].             (3)

For fixed opponents this vanishes as delta->0, but the opponents in
N_(a,delta) vary with delta. Abstract bounded functions can postpone their
first high record to dates of order1/delta, so (3) has no uniform bound from
compactness alone. That observation is NOT a realized-game counterexample
to (Q). The required global information must control moving record times
or change the jointly selected laws.

## 4. Exact exit when ANY proper clock has finite support

Claim (ordinary proof draft): assume s_a>=0. If p in N_(a,delta) has any
bounded proper clock, some actually reached tail of p has

    max_i D_i <= 2R*delta.                              (4)

Let H be the earliest last support date among bounded proper clocks.
Every clock has positive survival through date H, so the joint all-Continue
history before H has positive reach. Condition all clocks on surviving to
H. Independence is preserved. Every nonowner's resulting tail debt is zero:
following its prescribed prefix and changing only the remaining clock is a
legal full deviation, and any positive tail gain would multiply a positive
joint reach to contradict original optimality.

At least one conditional clock quits surely at date H. If it is the owner,
the owner's remaining clock is pure immediate Quit. Moving a small positive
amount of its last atom from H to ANY later finite date is legal in K_delta:
the earlier constraints are unchanged, and after H the original tail is zero,
so an amount at most c^t can be placed at a chosen finite t. Hence no later
finite deadline improves on H. The assumption s_a>=0 also covers Never by
the late-limit cap identity. Thus this tail is exact full Nash.

Otherwise a nonowner quits surely at H, and every owner response is absorbed
at that same date. Let Q,C be its conditional immediate Quit/Continue
endpoints and m=Pr(T_a>=H)>0. The owner's conditional hazard is h.
If Q>C, moving all later owner mass to H speeds up the law and is legal;
optimality requires h=1. If Q<C, moving an atom from H to H+1 changes only
the constraint at H+1, so optimality forces

    h=max(0,1-c^(H+1)/m) <= delta,

using m<=c^H. Therefore its full tail loss is at most
h*(C-Q)<=2R*delta. If Q=C it is zero. All other players' tail losses
are zero as established above. This proves (4) without a bound on H,
an atom-dispersion assumption or a terminal cap-attainment premise.

## 5. Exact exit when the owner is the ONLY proper clock

Assume s_a>=0 and every nonowner has positive Never mass. If the owner has
bounded support, Section4 applies. Otherwise every finite tail is reached.
At arbitrary late dates condition all clocks on survival. Every nonowner
again has zero full tail debt. Its conditional probability of finite quitting
later tends to zero, because its fixed positive Never mass remains in the
denominator. Thus all nonowners' conditional laws tend in total variation
to Never. The owner's conditional clock remains proper.

Against all-Never opponents, any proper owner law earns s_a and its complete
cap is s_a (since s_a>=0). Coupling the actual opponents to Never bounds
the owner's prescribed payoff and every deviation payoff uniformly, giving
tail debt at most 4R times the sum of opponents' conditional finite masses.
This tends to zero. Hence these actually reached tails produce full actual
terminal approximate Nash at all errors and a fixed uniform payoff.

Together Sections4–5 localize the genuinely missing case of this source:
at least TWO proper clocks, ALL proper clocks unbounded. Each unbounded
proper NONOWNER must then regard Never as a full best reply: it uses
arbitrarily late finite best-reply dates, whose payoffs converge to its
Never value because the opponent owner is proper. This is a global
best-response plateau, not a positive-gap certificate.

## 6. Exact early tests and a failed shortcut

### Single proper owner is allowed and can be essential

On the canonical table from
`CODEX_TARSKI_PREMIUM__PERIODIC_QUOTA_NASH_AND_PROPER_CLOCK_FORMAT_BOUNDARY.md`,
proper nonempty S pays r0=1 to participant0 and3 if0 is outside, while
other recipients get0 if participating and2 outside; grand rewards are
(2,1,1,1). Owner0 Geom(delta), everyone else Never, is exact full Nash.
This compactification permits that source; forcing two proper clocks
would incur the known full exploitability floor1/2 on this same table.

On the canonical fixed-pivot dispersion falsifier in Turing's Section12,
r0(S)=1_{0 in S} and ri(S)=-1_{S={0}} for nonowners. Owner0 and player1
sure Quit at date0, others Never, is exact full Nash and belongs to this
owner domain. Thus the compactification does not inherit the forbidden
fixed small-atom format.

### A complete correspondence falsifier for a NEGATIVE fixed owner

Two players with zero Never have rows

    r(0)=(1,-2),   r(1)=(2,-1),   r(01)=(0,0).          (5)

If owner1 alone is constrained to K_delta, EVERY constrained equilibrium
has player0=Never. Indeed player0's full maximum2 is attained only when
player1 quits strictly earlier almost surely. If player0 had a first finite
atom at h, independence would force player1 to be supported strictly before
h. Move a small portion of player1's last atom to h, legally in K_delta;
it improves from -1 to -1+Pr(T0=h). This contradicts optimality. Thus owner1
always receives -1 and its full Never deviation gives0: the entire fixed-
owner correspondence has remaining debt1.

With POSITIVE owner0, however, T0=Geom(delta), T1=0 is constrained Nash.
Owner0 must put at least delta at0, so its constrained value2(1-delta)
is optimal. Player1's finite deadline payoff is

    f1(t)=-2+(1+delta)c^t,

maximized at0; its Never value is-2. The exact original full debts are
(2delta,0). This both tests the bounded-proper exit and shows why selecting
the owner matters. The negative-owner falsifier does not refute canonical
nonnegative-singleton (Q), which explicitly has different hypotheses.

### Planned-Never bonuses do NOT immediately remove the remaining case

A tempting shortcut adds a small private bonus for a nonowner's planned
Never action, to exclude unbounded proper best replies. But conditioning
an auxiliary equilibrium at date H scales that bonus by the inverse of
opponents' survival to H, whereas original terminal gains scale by joint
reach. The resulting tail bonus can be arbitrarily large. Thus one cannot
insert that shortcut into Sections4–5 with the same small full-debt bound.
This is a failed proof step, not a refutation of global bonus selection.

### Exact bad branch even with positive own singletons

The following is an exact two-player calibration, NOT a counterexample to
the full correspondence question (Q). Set

    r(0)=(1,2), r(1)=(2,1), r(01)=(3,3), Never=(0,0).

For each integer L>=1 choose c=2^(-1/L), delta=1-c, and let both clocks
use only dates0,L,2L,... . Owner0 quits with conditional grid hazard1/2;
player1 quits with conditional grid hazard1/4. Both are proper unbounded.

Against player1, owner's finite deadline values are

    f0(nL)=2-(1/2)(3/4)^n,
    f0(t)=2-(3/4)^(n+1)  for nL<t<(n+1)L.

Every grid date is a strict new record and all intervening dates are below
the preceding record. Hence the private-record optimizer from Section3 is
T0=L*floor(G/L), where G is Geom(delta). Since c^L=1/2 this is exactly
the prescribed owner law. Against owner0, player1's values are

    f1(nL)=2, f1(t)=2-(1/2)^(n+1) for nL<t<(n+1)L,
    f1(Never)=2.

Thus this is an EXACT constrained Nash point. Its values and full caps are

    U=(8/5,2), B=(2,2), D=(2/5,0).

Indeed owner value is
[(1/2)(3/2)+(1/2)(1/4)*2]/[1-(1/2)(3/4)]=8/5.
For every actually reached tail, conditioning merely gives an initial wait
to the next grid point followed by the same memoryless grid laws. The full
owner cap remains2, achieved by Never, and its payoff remains8/5. Therefore
NEITHER delta->0 NOR choosing a later reached tail removes this branch's
loss2/5.

The ENTIRE correspondence nevertheless contains good points: owner0
Geom(delta), player1 Never is exact FULL Nash for delta<=1/2. Owner value
and cap are1; player1's finite deadline values are

    2-(1-2*delta)c^t <= 2,

and its Never value is2. Thus this fixture forbids automatic removal of
the constraint at arbitrary constrained equilibria, not global selection,
owner reselection, unrestricted UE, or any claim about all Fin4 tables.
No new class coverage is claimed for this solved two-player fixture.

## 7. Narrow source audit and concrete next question

Inspected actual declarations/files:

- `CompactStoppingLaw`, `compactStoppingLawEquivPMF` and finite barycentre
  construction in `MathUE/ProbabilityMassFunction/CompactStoppingLaw.lean`;
- `quittingTerminalPayoff_update_finiteTime_tendsto_never_add_opponentNever_mul_singleton`
  and `quittingCompactStoppingLawProfile_cap_le_finiteBound_add_opponentNeverProduct_mul_negPart`
  in `UniformEquilibrium/Quitting/Terminal/CompactStoppingLawCapUpperBound.lean`;
- `QuittingJointTightLawSequence.of_properLimit`,
  `quittingTerminalSemanticPair_partial_eq_of_proper_lawLimit` and
  `oneProper_minimum_negativeSingletonJump_of_notAttained_lawLimit` in
  `UniformEquilibrium/Quitting/Terminal/OpponentTightTerminalSemanticRealization.lean`;
- the all-errors/fixed-target consumer in
  `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`.

The existing one-proper LAW-LIMIT realization theorem makes no continuity
claim for that proper player's own full cap. The present constrained game
instead obtains continuity of prescribed payoffs by a UNIFORM owner envelope
and leaves its complete cap as the explicit record deficiency (3). These are
different statements; no novelty claim for the compact PMF or cap identities.

Next concrete question: can one select, among the FULL constrained Nash
correspondence and owners, a point with a bounded proper clock or with only
one proper clock, or legally rebalance the unbounded-proper Never-indifferent
players so that the exact source supplies one of these exits? A mere choice
of a supported debt vector, or replacing one indifferent player by Never
without checking the other players' response caps, does not answer it.

The finite Nash producer and both exit proofs need independent checking
before being treated as established ordinary results. No export is requested:
the remaining global selection operation has not been supplied, and no new
raw reward class or unrestricted positive-gap table has been obtained.

## 8. The actual whole-correspondence minimum and a sharper remaining face

Ordinary proof draft, not independently checked. At FIXED owner a and
delta>0, N_(a,delta) is a nonempty COMPACT set. The continuity from Section2
makes every response inequality closed, including arbitrary owner responses
in K_delta and every unrestricted nonowner response. Their intersection
inside the compact law product is closed.

For s_a>=0, B_a is the supremum of finite-deadline payoffs. Each such
payoff is a finite-cylinder continuous function of the opponents' laws.
Consequently B_a, and hence D_a=B_a-U_a, is lower semicontinuous on the
constrained domain. Therefore the actual minimum

    eta_(a,delta)=min_(p in N_(a,delta)) D_a(p),
    eta_delta=min_(a with s_a>=0) eta_(a,delta)             (6)

is attained. This is an ordinary attained independent-profile minimum,
not a convexification or supplied favorable equilibrium. The unsettled
source question is liminf_(delta->0) eta_delta=0. No monotonicity of
eta_delta follows merely from inclusion of the owner strategy sets.
Nor has this assertion been proved EQUIVALENT to ordinary UE existence;
only its sufficient direction is established here.

The record formula gives a sharper fact about Section5's remaining face.
Whenever the owner is unbounded proper and at least one opponent is proper,
its finite-deadline values converge to its Never value v. If B_a>v, the
sequence f attains its strict global maximum B_a at a finite date and all
its maximizers lie before some H. Couple an optimal owner T<=G as in
Section3. Optimality makes

    f(T)=max_(0<=u<=G) f(u) almost surely.

On T>H, also G>H, so the right side is B_a while f(T)<B_a, a contradiction.
Thus an unbounded optimal owner must have B_a=v, and Never is its full
best reply. The same reasoning shows that if ANY finite deadline attains
B_a and all maximizers are bounded, its law cannot be unbounded. In
particular the still-unresolved positive-loss face is genuinely a
Never-best-reply plateau for EVERY proper player, including the owner.
This does not justify replacing any such player's law by Never while
retaining the other players' Nash inequalities.

## 9. Exact nonstationary calibration and valid Fin4 padding

This is an application of an EXISTING checked equilibrium, not a new
three-player producer or new table coverage. The literal FTV Example3 is

    r(0)=(1,3,0), r(1)=(0,1,3), r(2)=(3,0,1),
    r(01)=(1,0,1), r(02)=(0,1,1), r(12)=(1,1,0),
    r(012)=(0,0,0), Never=0.

Actual declarations `example3Reward`, all seven absorbing
`example3TerminalReward_*` row identities,
`example3_no_stationary_equilibrium` and `example3_corrected` in
`Literature/future/FleschThuijsmanAndVrieze1996.lean` identify the table
and exclude stationary equilibria even at all sufficiently small positive
errors. I inspected `phaseRoot`, `standardPromise_recursion`,
`endpointDifference_phaseRoot`, `isZeroEndpointNash_phaseRoot` and the
named-target construction in
`UniformEquilibrium/Quitting/Examples/Cyclic/ThreePlayer/AdmissibleCycle.lean`.
They supply the exact private three-phase cycle: at successive dates only
players0,1,2 respectively may quit, each with hazard1/2. Its actual phase
values are

    (1,2,1) -> (1,1,2) -> (2,1,1) -> (1,2,1).

The active player's endpoints are equal; the next player's Continue
margin is3/2 and the third player's endpoints are equal. Deleted-opponent
survival contracts by1/4 per three dates, so this is exact terminal Nash
against complete replacements, not merely a stationary or cycle-restricted
Nash point.

At the phase0 origin, owner0's clock is supported on0,3,6,... and

    Pr(T0>=t)=2^(-ceil(t/3)) <= 2^(-t/3) for every integer t>=0.

Hence the ACTUAL full equilibrium belongs to K_delta whenever
0<delta<=1-2^(-1/3). Its owner loss is zero, proving
eta_(0,delta)=eta_delta=0 throughout that rate interval. Thus the
compactification does not silently impose stationarity and survives this
nonstationary test without an approximate-to-exact reselection argument.

For a valid Fin4 embedding, add player3 with r_3(S)=1 for EVERY nonempty
S. For active recipients i=0,1,2 put r_i(S) equal to the three-player
reward at A=S intersect {0,1,2} when A is nonempty, and zero when A is
empty. Prescribe player3 Never. Under any active player's replacement,
player3 still Never, so its whole game is the original three-player one.
Under player3's replacement its own terminal payoff is always1 because
the three active opponent clocks are proper; no coalition can pay it
more than1. Therefore its actual full value/cap are1. This is exact full
Fin4 terminal Nash, all four own singletons equal1, and the same owner
envelope calculation applies. The claim concerns this prescribed passive
embedding, not arbitrary profiles involving the added player.

Current next question: an operation improving the ATTAINED minimum (6),
or a whole-correspondence obstruction, rather than another arbitrary bad
equilibrium branch. The exact nonstationary calibration above is evidence
for this source, not a proof of arbitrary-table completeness.

## 10. Global penalty selection: a genuine truncation, but no relative error control

Status: ordinary proof draft. This is a selection over the WHOLE constrained
strategy domain, not over a supplied equilibrium branch. It does not prove(Q).
Fix a,delta as above and let E_a be the owner's CONSTRAINED response debt;
for i!=a let E_i=D_i be its unrestricted debt. On the compact constrained
domain every E_i is continuous. Indeed the prescribed payoff functions are
uniform limits of finite-cylinder functions by Section2. The same estimate
holds uniformly over every legal replacement: when the owner is the
deviator its replacements still belong to K_delta, and otherwise its
prescribed clock still belongs to K_delta. Taking a maximum over the fixed
compact replacement-law set therefore preserves continuity.

For Lambda>0 maximize

    J_Lambda(p)=sum_(b!=a) p_b(Never)-Lambda sum_i E_i(p).

The Never atoms are upper semicontinuous on the compactified law space,
so a maximum exists. An exact constrained Nash point gives J_Lambda>=0.
Consequently every maximizer satisfies

    sum_i E_i <= (|I|-1)/Lambda.                              (7)

There is an actual global tail-deletion property. Fix b!=a and let
m=Pr(H<=T_b<Never). Move all this finite tail mass to Never. Its Never
bonus increases by m. Against any legal response of any recipient, the
outcome can change only when this tail event occurs and the owner's clock
survives H. These events are independent, and the owner's prescribed or
legally replaced law has survival at most c^H. Thus every relevant payoff
changes by at most 2R m c^H. The constrained cap of b is unchanged (b's
opponents did not change); every other relevant cap changes by at most
the same bound. It is enough to bound the total debt change by

    4R |I| m c^H.

If 4R |I| Lambda c^H<1, any m>0 would strictly increase J_Lambda.
Therefore EVERY maximizer has all nonowner finite clock supports below
such an H; the nonowners may retain positive Never mass. In particular
H can be chosen of order log(Lambda)/delta.

This gives bounded-tail APPROXIMATE constrained Nash profiles, not exact
ones. Section4's final-clock exit needs exact nonowner response
inequalities. Here the error bound(7) is of order 1/Lambda, while the
owner survival near the selected cutoff can itself be of that order.
After conditioning, error/reach need not vanish. Taking Lambda to infinity
recovers exact constrained Nash but also sends H to infinity. There is no
proved interchange of these operations, and no resulting UE producer.

### An exact falsifier of an abstract linear repair principle

The following FINITE response game is only a test of generic equilibrium
repair, not a quitting-game counterexample or a falsifier of(Q). Three
players choose A or N, with independent N probabilities x,y,z. Give A
payoff zero and let the N-minus-A expected advantages be

    d_1=y-2z-yz,  d_2=z-2x-xz,  d_3=x-2y-xy.

These multilinear formulas define an ordinary finite game. Its UNIQUE
Nash point is x=y=z=0. If x>0, best response requires y>=2z+yz.
If y=0 this forces z=0, but then d_3=x>0 contradicts z=0. Cycling the
argument makes all three coordinates positive. Their best-response
inequalities y>=2z, z>=2x, x>=2y then contradict each other. At the
all-zero point all three unused N actions are weak best replies.

At x=y=z=t>0, each advantage is -t-t^2 and each debt is t^2+t^3.
Thus

    (x+y+z)-Lambda sum_i D_i = 3t-3Lambda(t^2+t^3)>0

for all sufficiently small positive t, whereas its value at the unique
Nash point is zero. A Never-bonus/linear-debt penalty need not maximize
at an exact equilibrium, however large its coefficient is. Weakly best
unused actions also cannot automatically be activated while preserving
equilibrium. This invalidates those ABSTRACT repair steps; the special
quitting-clock structure might still permit a different joint operation.

Current next question: control the NORMALIZED continuation debt globally,
or reorganize tails so that the final-clock exit does not divide an
unconditioned approximation error by a vanishing reach probability.
