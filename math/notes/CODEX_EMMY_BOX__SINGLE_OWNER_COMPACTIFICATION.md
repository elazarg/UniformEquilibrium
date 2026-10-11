# Single-owner compactification and global record selection

Author: CODEX_EMMY_BOX.

Status: ACTIVE ORDINARY PROOF DRAFT, not Lean
implemented and not an export candidate. This is a distinct mechanism from
the closed portfolio/quiet-lift route. An unconditional compact constrained-
Nash producer is available, with exact exits when a proper clock is bounded
or when the owner is the only proper clock. Section11 adds exact re-rooting
at reached strict owner records and a reached finite-cap-attainment exit.
Section12 supplies a compact strict-record invariant hull with a fixed
minimal proper-player set and uniform conditional termination in bounded
blocks, conditional on a positive terminal gap. The genuinely missing step
is a GLOBAL selection or joint-law operation
in the remaining case of at least two unbounded proper clocks and an owner
cap attained ONLY at Never. Section10's global penalty selector does not
control error relative to tail reach. No arbitrary-Fin4 UE theorem is claimed.
The foundational source chain in Sections2--5,8,11--12 has a bounded
independent ordinary check in
`../feedback/CODEX_EMMY_BOX__SINGLE_OWNER_COMPACTIFICATION__BY_CODEX_TURING_BOX.md`.
Sections4 and11 also have the narrower independent ordinary check in
`../feedback/CODEX_EMMY_BOX__SINGLE_OWNER_COMPACTIFICATION__BY_CODEX_NASH_BOX.md`.
Neither review supplies the missing zero-owner-debt selector or asserts
unrestricted Fin4 UE existence. Section13 gives immediate whole-face
selection consequences, not a new conjecture-facing closing theorem.
Section14 calibrates this source on the canonicalized perturbed Solan
three-player game, which has UE but no exact Nash. Sections14.4--14.6 now
give a COMPLETE ORDINARY PROOF with a bounded independent adversarial
check by CODEX_TURING_BOX that, for all three
core owners, the ENTIRE constrained-Nash correspondence is the geometric
component of Section14.1. Its minimum full owner loss tends to2/5, not0.
The load-bearing new step is the attained whole-correspondence hazard
maximum argument in Section14.6, including the flat-plateau case. This is
a proposed falsifier of the three-player sufficient source question(Q),
not a UE counterexample and not a whole-owner Fin4 falsifier. A fourth
owner can change the conclusion; Section14.7 keeps that scope separate.
The separate bounded review of Sections14.4--14.6 is recorded in
`../feedback/CODEX_EMMY_BOX__SINGLE_OWNER_COMPACTIFICATION__BY_CODEX_TURING_BOX.md`.
It found no objection in precisely the THREE-core-owner scope. The
result stays internal, not Lean-checked and not exported. It retires(Q)
as a universal finite-player source, not the Fin4-only selection question.

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

The finite Nash producer and both exit proofs have the bounded independent
ordinary check identified at the top of this note. No export is requested:
the remaining global selection operation has not been supplied, and no new
raw reward class or unrestricted positive-gap table has been obtained.

## 8. The actual whole-correspondence minimum and a sharper remaining face

Ordinary proof draft, included in the bounded independent source check
identified at the top. At FIXED owner a and
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

## 11. Exact record re-rooting inside the SAME correspondence

Status: ordinary proof draft, with a bounded independent check in
`../feedback/CODEX_EMMY_BOX__SINGLE_OWNER_COMPACTIFICATION__BY_CODEX_NASH_BOX.md`
conditional on Section3's exact optimal quantile/value formula. This operation
uses EXACT constrained Nash, not Section10's approximants. Its force is
that no error is divided by reach. Positive joint reach is indispensable.

Fix p in N_(a,delta). Let f(t) be the owner's full finite-deadline payoff
against p_-a. Suppose t is a STRICT record date:

    f(t)>max_(0<=u<t) f(u),

where date0 is a record by convention. Couple the optimal owner T with
G~Geom(delta) by common quantiles, so T<=G. Section3's exact value formula
and optimality imply

    f(T)=max_(0<=u<=G) f(u) almost surely.

If G>=t, the right side is at least f(t), strictly larger than every
payoff at an earlier date; hence T>=t. Conversely T>=t implies G>=t.
Consequently the owner constraint is EXACTLY binding at every strict
record:

    Pr(T_a>=t)=Pr(G>=t)=c^t.                            (8)

Now assume the joint survival to t is positive. Condition each independent
clock on surviving to t and rebase the calendar to zero. The owner's
conditional law lies in K_delta, since for every u>=0,

    Pr(T_a>=t+u | T_a>=t)<=c^(t+u)/c^t=c^u.

Conversely ANY conditional replacement in K_delta can be spliced into
the old owner's surviving mass: its later survival is at most
c^t*c^u=c^(t+u), and earlier constraints are unchanged. A profitable
conditional constrained reply would therefore be a profitable original
reply multiplied by positive joint reach. All nonowner full response
inequalities likewise pass by legal suffix replacement. Thus the reached
record tail belongs to the SAME N_(a,delta), with the SAME owner and rate.

### Finite owner-cap attainment is an exact exit on the reached face

Assume s_a>=0 and the full owner cap B_a is attained by a finite deadline.
Let t* be the FIRST maximizing deadline. This is a strict record. If its
joint reach is positive, apply(8). Against the conditioned opponents,
immediate Quit attains the complete tail cap: any tail finite deadline or
Never corresponds to an original reply at or after t*, while the earlier
opponent-absorption contribution is identical and the positive opponent
survival multiplies every remaining payoff. Immediate Quit belongs to
K_delta. Conditional constrained optimality therefore makes the owner's
prescribed tail payoff equal to its FULL cap. Nonowners already have zero
full tail debt. The reached record tail is exact terminal Nash, lies in
N_(a,delta), and produces a fixed uniform payoff by the semantic consumer.
In particular eta_(a,delta)=0 in this reached finite-attainment case.

One cannot omit reach. For example, take two players with

    r(0)=(1,0), r(1)=(2,1), r(01)=(0,3).

Owner0 Geom(delta), player1 sure Quit0, is exact constrained Nash.
Owner finite values are f(0)=0 and f(t)=2 for t>=1; its full loss is2delta.
Player1's deadline values are c^t*(1+2delta), so date0 is its full best
reply. The first owner maximizing date is1 and its owner constraint binds,
but JOINT reach to1 is zero. No conditional equilibrium can be read there.
This illustrates the failed unrestricted implication, not a counterexample
to the corrected reached statement or to UE existence.

### Exact remaining global minimum problem

Suppose the original table has a fixed positive full terminal gap gamma.
Choose delta<gamma/(2R) BEFORE applying Section4. Then no p in
N_(a,delta) can contain a bounded proper clock, since that clock would
produce an actual full profile of regret at most2Rdelta<gamma. Section5
also excludes the owner-only-proper case. Thus every relevant profile has
at least two proper clocks, all proper clocks unbounded; every finite date
has positive joint reach. Finite owner-cap attainment is now impossible
by the reached exit above.

For these profiles Section8 gives B_a equal to the owner's Never value.
All finite f(t) are STRICTLY below B_a, and f(t)->B_a because an opponent
is proper. There are therefore infinitely many strict record dates. Each
record tail is again in the same N_(a,delta). If p minimizes the attained
owner loss eta_(a,delta), all its reached record tails have owner loss at
least eta_(a,delta). The other players' full debts remain exactly zero.

This gives a concrete global invariant to test, not a contradiction:
an attained constrained minimum with a nonattained Never cap, infinitely
many EXACT binding re-rootings, and no smaller-loss record continuation.
The missing operation must improve this minimum by changing joint laws
or the owner/rate selection. Conditioning Section10's approximate points
does not establish this invariant and cannot replace exact re-rooting.

## 12. A minimal strict-record hull has uniform conditional termination

Status: ordinary proof draft, included in the bounded independent source
check identified at the top. This is an exact
source reduction, not a new equilibrium producer or a claim that recurrence
alone solves the remaining selection problem. All probabilities below are
for the original independent private clocks. No public mixing is introduced.

Assume the original finite table has a positive full terminal gap gamma:
every independent law profile has max_i D_i>=gamma. Fix an owner a with
s_a>=0 and fix 0<delta<min(1,gamma/(2R)). Let c=1-delta. Use Sections2,
4,5,8,11, including their distinctions between constrained and full caps.
Every p in the SAME compact correspondence N_(a,delta) then has:

- at least two proper clocks, all proper clocks unbounded;
- full owner cap attained only at Never, approached by infinitely many
  strict finite records;
- positive joint survival at every finite date and D_a>=gamma.

The foundational chain used here is explicit: Section2 produces the exact
compact correspondence and its closedness; Section3 gives the optimal
private-record envelope and complementary equality; Section4 excludes
bounded proper clocks at the chosen rate; Section5 excludes the owner-only-
proper case; Section8 and the reached finite-attainment exit in Section11
give the Never-only cap and infinitely many records; Section11 then supplies
EXACT same-correspondence re-rooting. None of these roles can be replaced
by small absolute-error finite-cutoff Nash approximants.

There are a subset A containing a, with |A|>=2, and a nonempty compact
set K of actual profiles in N_(a,delta) such that:

1. Every player in A is proper and unbounded at every point of K. Every
   player outside A is literally Never at every point of K.
2. K is invariant under conditioning and rebasing at ANY strict owner
   record, including date0. All such conditionings have positive reach.
3. There are finite positive integers M,N such that for every p in K,
   every i in A, and every calendar date u>=0,

       Pr_p(T_i>=u+M+2N | T_i>=u) <= 1/2.             (9)

   In particular every player's conditional residual clock is uniformly
   proper over ALL calendar tails, not merely at owner record dates.
   No uniform one-date hazard floor is asserted.
4. Consecutive strict owner record dates are at most N dates apart.
   The full payoff and cap functions are continuous on K.

### Construction and weak-limit support bookkeeping

Among ALL points of N_(a,delta), choose p with the smallest number k of
proper clocks. This integer minimum exists because the correspondence is
nonempty and the count takes values in a finite set; no semicontinuity of
the count is being assumed. Let A be p's proper-player labels.

Take strict owner records t_n->infinity and condition p at t_n. The tails
belong to the SAME N_(a,delta) by Section11. If j is originally improper,
write z_j=Pr_p(T_j=Never)>0. Its conditional finite mass is

    Pr_p(t_n<=T_j<Never)/Pr_p(T_j>=t_n) -> 0,

since the numerator tends to0 and the denominator is at least z_j.
Thus its conditioned law tends to literal Never in total variation.
Take any joint weak cluster q of the record tails. Closedness of N gives
q in N, and every label outside A is literal Never. At most k labels can
therefore be proper at q. Minimality of k among ALL N forces all labels
in A to remain proper. The bounded-proper exit also makes them unbounded.
This is the exact reason a proper label cannot be lost in the limit.

Now let K be the closure of ALL strict-record tails of q, including q.
The same argument applies to each point of this closure: it lies in N,
has every outside-A clock literal Never, and cannot have fewer than k
proper clocks. Hence all A clocks are proper and unbounded throughout K.

To verify invariance, suppose q_n are strict-record tails of q converging
to x in K, and t is a strict record for x. Finite deadline payoffs are
continuous in finite cylinders, so t is also a strict record for q_n for
all sufficiently large n. Conditional laws at fixed t are continuous
whenever each survival probability is positive; this holds at x. A strict
record of a strict-record tail is a strict record of the original profile:
the intermediate record already dominates every earlier deadline, and
rebasing changes later payoff differences by a common positive opponent
survival factor. Thus the t-tail of q_n is again one of q's strict-record
tails. Taking its limit shows that the t-tail of x belongs to K.

### Uniform properness, uniformly frequent records, and all-tail bound

For fixed i in A, the functions p -> Pr_p(T_i>=m) are continuous finite-tail
cylinders on K, decrease in m, and have pointwise limit Pr_p(T_i=Never)=0.
Compactness therefore gives uniform convergence to0. Equivalently, use
the decreasing closed sets {p: Pr_p(T_i>=m)>=epsilon}. For each i, choose
a common M with

    sup_(p in K, i in A) Pr_p(T_i>=M) <= 1/2.

Every recipient has at least one distinct uniformly proper opponent since
|A|>=2. Truncating any unilateral reply at a large finite date changes its
payoff only when that opponent also survives that date. This gives uniform
finite-cylinder approximation of ALL full caps on K, and proves cap
continuity there. In particular the owner's pure-deadline payoff f_p(m)
approaches its Never cap B_a(p) uniformly on K; one can directly bound the
difference by 2R times one proper opponent's survival to m.

Immediate Quit is legal in K_delta, so U_a(p)>=f_p(0). Since D_a(p)>=gamma,

    B_a(p)-f_p(0) >= gamma.

Choose N>=1 with |f_p(N)-B_a(p)|<gamma/2 uniformly on K. Then
f_p(N)>f_p(0)+gamma/2, so every p in K has a new strict record by date N.
Invariance applies the same assertion after EVERY strict record; therefore
successive strict record dates have gaps at most N.

For an arbitrary calendar u, choose the next owner record v>=u, with
v-u<=N. Choose the first owner record w>=v+M; the record-gap bound gives
w<=v+M+N<=u+M+2N. Invariance at v and uniform properness give

    Pr(T_i>=w) <= Pr(T_i>=v+M)
                 <= (1/2)Pr(T_i>=v)
                 <= (1/2)Pr(T_i>=u).

Monotonicity of survival then proves(9). All denominators are positive
because every active clock is unbounded. This argument does not divide an
approximate Nash error by any reach probability.

### Exact remaining issue

The compact hull has an attained minimum of owner full loss, and every
strict-record continuation remains inside the hull with no smaller loss
than that minimum. Uniform properness and bounded record gaps may depend
on delta and the selected hull; no delta-independent clock bound follows.
There is in fact an exact lower bound preventing the particular all-player
window W=M+2N in(9) from satisfying delta*W->0. Choose the first owner
record r>=W. It lies at most N dates after W. Binding at r and(9) at u=0
give

    c^(W+N) <= c^r = Pr(T_a>=r) <= Pr(T_a>=W) <= 1/2.

Therefore

    (-log c)*(W+N) >= log2,
    (-log c)*W >= (2/3)log2,                            (10)

since W>=2N. Along delta->0 this forces
liminf delta*W >= (2/3)log2. Thus trying to obtain a vanishing full-regret
estimate solely by multiplying THIS all-player termination window by
delta would be mathematically the wrong target, not just an unproved bound.
An estimate could still compare the owner's record rate with OPPONENT
termination or control reward-weighted hazard exposure instead.

The old exact two-player bad branch in Section6 illustrates the distinct
limitation of compactness/record-invariance ALONE. Its strict-record hull
is a singleton, its active clocks are uniformly conditionally proper, and
its record gap is L with c^L=1/2. For the nonowner's hazard1/4 grid clock,
a half-survival window from calendar date1 must be at least3L-1; hence
delta times that opponent window tends to3log2 rather than0. This fixture
does NOT satisfy the global-gap or global proper-count-minimal hypotheses:
its ENTIRE correspondence also has the good owner-only-proper profile
already recorded in Section6. It therefore tests only an inference from
compact recurrence, not the whole positive-gap source reduction.

Consequently(9) is NOT a contradiction to a positive gap and does NOT
remove the need for a joint law or owner-selection operation.
The next concrete question is whether this exact uniformly terminating
source admits a loss-improving operation when at least three proper labels
remain.

For the combined arbitrary-counterexample route, Section13 of
`CODEX_NASH_BOX__DIRECT_EXISTENCE_BEYOND_TEMPORALIZATION.md` proposes the
independently authored exact two-literal-clock resonance exclusion. It first
perturbs any positive-gap table inside its gap to satisfy finitely many
generic pair inequalities, keeps a positive-singleton owner, and then
chooses c arbitrarily close to1 outside its countable forbidden rate set.
If that complete ordinary draft and the foundational dependencies above
are verified, the present construction produces a compact source with at
least THREE proper labels (three or four in Fin4), all other labels literal
Never, exact nonowner full Nash, record invariance, continuous caps, and
the all-calendar conditional termination bound(9). This is a produced
counterexample source with additional structure, not yet its exclusion or
a new equilibrium table class. Authorship and proof obligations for the
resonance step remain in the separate Nash note.

Narrow overlap/source inspection for this section used the existing
`CompactStoppingLaw` topology and bridge in
`MathUE/ProbabilityMassFunction/CompactStoppingLaw.lean`, and searched the
previously inspected `OpponentTightTerminalSemanticRealization.lean` and
`CompactStoppingLawCapUpperBound.lean` for uniform-proper/minimal-proper
statements. This section makes no Lean-implementation claim and does not
replace their distinct semantic-minimum results.

## 13. Select the ENTIRE clean face, not one record orbit

Status: ordinary corollary draft of the reviewed Section12 source. This
does not solve the owner-loss selection problem. Its purpose is to avoid
adding an unnecessary orbit restriction to the next joint-law variation.

Keep the positive-gap/rate hypotheses and let k be the minimum proper
count over ALL N_(a,delta), as in Section12. Its construction supplies
one profile q with exactly k unbounded proper labels A and literal Never
at every other label. Instead of taking only q's record-tail hull, set

    K_A={p in N_(a,delta): p_j=Never for every j outside A}.     (11)

This is a nonempty compact set because the literal-Never law is a closed
point of the compact law space. Every point has at most k proper labels,
and whole-correspondence minimality forces EVERY A label to be proper.
The gap/bounded-clock exit again makes them unbounded. Every strict-record
tail stays in the same N and retains the same literal-Never outsiders,
so K_A is record-invariant directly. Thus ALL of Section12's uniform
properness, cap continuity, bounded record gaps, all-calendar conditional
termination, and the delta-window limitation apply to this WHOLE clean
face, not merely one orbit closure. In particular owner full loss attains
its minimum over all admissible joint profiles in K_A.

There is also an exact scalar description of this support selection that
is different from Section10's unsuccessful finite penalty. Define on N

    F(p)=sum_i Pr_p(T_i=Never).

Each Never atom is upper semicontinuous in the one-point law topology,
so F attains its maximum. Its maximum is exactly n-k. Indeed F(p)<=n-k
at every p because at least k labels are proper, and q attains n-k.
Equality forces exactly k proper labels and literal Never at all others.
Consequently the exact argmax of F is the finite union of the compact
clean faces(11). It is itself compact and invariant under strict-record
tails. All full caps are continuous on this union: every recipient has a
distinct proper opponent, so its joint opponent-survival product tends to
zero uniformly by the same compact decreasing-cylinder argument. Hence
one may lexicographically maximize F and then minimize full owner loss,
with BOTH extrema attained over the ENTIRE exact correspondence.

This is equivalent to the minimum-proper-count source reduction, not a
new equilibrium result or a repair theorem. It does not say the second
minimum is zero, or that a unilateral Never replacement remains on(11).
Its useful distinction from Section10 is exactness: the first optimization
is over actual constrained Nash, rather than trading a small absolute
Nash error against a planned-Never bonus and then conditioning that error.

Current concrete operation question: can one lower full owner loss, or
produce a point with fewer proper labels, by a genuinely joint clock-law
change and exact re-equilibration within the whole clean-face selection?
A recurrence argument restricted to one orbit is not required, but the
other players' FULL best-response inequalities still are. Shared joint-
survival quota equilibria were tested as an alternative source: they allow
reallocation of termination but lose the exact nonowner full-Nash property,
so no closing implication from that alternative has been established.

## 14. Perturbed Solan calibration: the full geometric-owner response set

Status: NEW ORDINARY PROOF DRAFT, not independently checked. This is a
necessary performance test, not a new equilibrium table class. The whole
K_delta selection question remains open. Its stronger relevance than the
old FTV0 test is that the small positive perturbation has NO exact Nash,
despite having UE. Thus no easy exact-Nash branch settles the calibration.

Fix 0<e<1 and use the seven raw rows

    g(0)=(1,3,0),       g(1)=(0,1,3),       g(2)=(3,0,1),
    g(01)=(1+e,0,1),  g(02)=(0,1,1+e),   g(12)=(1,1+e,0),
    g(012)=(0,0,0).

The canonical version subtracts1 at every nonempty terminal coordinate
of recipients1,2, leaving recipient0 and Never0 unchanged; its own solo
vector is(1,0,0). When owner0 is proper, this shift preserves ALL response
payoffs of recipients1,2 up to the same constant, because they always
retain a proper opponent. All calculations below may therefore use g.

Question: on this fixed table, does

    inf_(p in N_(0,delta)) D0(p) ->0 as delta->0?          (14.1)

Allowing every owner law in K_delta is essential. Cyclic symmetry of the
raw g-table makes the corresponding raw-owner minima equal; no favorable
owner selection is hidden by choosing label0. Section14.4 verifies the
canonical-shift correspondence for EVERY core-owner choice as well.

### 14.1. Exact theorem with the owner law FIXED to Geom(delta)

For every 0<delta<1/2, put c=1-delta and prescribe owner0 the private
geometric clock, conditional hazard delta at EVERY date. The other two
players may choose ARBITRARY independent private laws, not just stationary
laws. Their complete Nash response correspondence is a SINGLE stationary
profile with positive hazards x_delta,y_delta. In particular passing to
nonstationary opponent clocks does not repair this particular fixed owner.

Here is an independent full-response proof. At any reached date, player1
cannot Quit surely. If it did, player2's Quit payoff0 is below its Continue
payoff3-2delta, so player2 surely Continues there. Player1 would receive c
by immediate Quit. Waiting one date and then Quitting instead yields at
least 3delta+c^2>c: owner0 quitting now pays3, and conditional next-date
Quit pays at least c against ANY player2 hazard. Player2 cannot Quit surely
either: its sure Quit makes player1's current Quit c*(1+e)>delta=Continue,
forcing the already-excluded sure player1 Quit. Consequently EVERY finite
joint reach is positive, and every proper nonowner clock is unbounded.

Each nonowner has Never as a full best reply. An improper clock supports
Never. A proper unbounded clock has optimal finite support tending to
infinity, whose payoffs converge to its Never payoff because owner0 is
proper. Let Y1(t),Y2(t) be their conditional raw Never payoffs. Conditional
full Nash and Never optimality persist at every finite date. If x,y are
the current nonowner hazards, their exact equations are

    Y1=delta*(3-2y)+c*(1-y)*Y1',
    Y2=(3-2delta)*x+c*(1-x)*Y2',
    Y1>=c*(1+e*y),        equality if x>0,
    Y2>=(1-x)*(1+e*delta), equality if y>0.                (14.2)

These relations FORCE x,y>0 at EVERY date. If x>0 but y=0, the first
equation and next-date cap Y1'>=c give
Y1>=3delta+c^2>c, contradicting the equality Y1=c. Thus x>0 implies y>0.
Put L=1+e*delta. If x=0 and y>0, then Y2=L=c*Y2', so Y2'>L.
Whenever Y2>L, equality would forbid y>0; the preceding implication then
also forces x=0. Its next value grows by factor1/c, contradicting the
bounded payoff Y2<=3. Finally x=y=0 gives Y2>=L and the same next-date
contradiction. Thus both are positive; the sure-hazard argument also gives
x,y<1.

Substitution of the equalities in(14.2) at consecutive dates gives the
DECOUPLED exact maps

    x'=[(3-delta+e*delta^2)*x-delta*L]/[c*L*(1-x)],
    y'=[(1+e-e*delta+delta^2)*y-delta*(2+delta)]
          /[e*c^2*(1-y)].                               (14.3)

Each map is increasing on(0,1), tends to infinity at1, and has exactly
one fixed point there. Explicitly the positive roots are

    c*L*x^2+(2-e*delta+2e*delta^2)*x-delta*L=0,
    e*c^2*y^2+[1+e*delta+(1-e)*delta^2]*y
          -delta*(2+delta)=0.                           (14.4)

Both quadratics are negative at0 and positive at1, with positive linear
coefficient. For either map Phi, Phi(z)-z has the sign of the corresponding
quadratic. Starting above its fixed point produces a strictly increasing
forward orbit; starting below produces a strictly decreasing one. Neither
can remain in(0,1) forever: a bounded monotone limit would be another fixed
point, while the endpoint limits of Phi exclude0 and1. Therefore every
infinite response clock sequence must be identically the roots(14.4).

Conversely these stationary hazards satisfy the exact endpoint equalities.
Never and EVERY finite deadline then give the same nonowner payoff, so
they are genuine unrestricted best replies. This proves uniqueness, not
just existence of one stationary response branch.

### 14.2. Positive limiting loss and its precise scope

From(14.4),

    x_delta/delta ->1/2,     y_delta/delta ->2.

Write k=(1-x_delta)*(1-y_delta). Owner0's Never cap candidate and immediate
Quit payoff are

    B=y_delta*(3-2*x_delta)/(1-k),
    Q=(1-y_delta)*(1+e*x_delta).

Thus B->12/5 and Q->1. For every sufficiently small delta, B>Q and its
pure deadline payoff is B+k^t*(Q-B), strictly increasing in t. Every date
is a strict owner record, so Geom(delta) is indeed its K_delta-optimal
clock by Section3. Hence this unique partial-response profile actually
belongs to N_(0,delta). Its actual payoff and full loss are

    U0=[delta*Q+c*y_delta*(3-2*x_delta)]/(1-c*k) ->2,
    D0=delta*(B-Q)/(1-c*k) ->2/5.                       (14.5)

The proof determines the ENTIRE response correspondence to that fixed
geometric owner, with unrestricted nonstationary opponents. It does NOT
give a lower bound on(14.1): K_delta also allows owner atoms larger than
delta and zero hazards across record plateaux. If every date is a strict
record at a K_delta optimum, binding forces the geometric law and the
theorem applies; a successful selector must therefore use genuinely sparse
record/plateau structure or an increasingly long non-geometric prefix.
No inference that finite player count bounds the number of such intervals
is justified.

The next mathematical target is the WHOLE minimum(14.1), not a further bad
clock branch. One potentially stronger obstruction to test is a positive
owner-loss lower bound over all proper owner laws for which the two
nonowners are exact full best replies; that larger-set obstruction would
imply failure of(14.1), but is currently only a hypothesis.

Source/declaration audit for this calibration: actual Solan2001 PDF,
Figure1 and Theorem2.1, read independently also for the bounded review of
Nash Section14.4; the theorem gives only a qualitative small-e interval
for no exact absorbing inverse iterate. The proof of(14.2)--(14.5) itself
uses no paper no-exact-Nash theorem and holds for every0<e<1. The tracked
FRONTIER route points to
`no_isQuittingBlockCertificate_solanPassivePaddedReward_one` in
`UniformEquilibrium/Quitting/Boundary/Analytic/SolanPassivePaddingBlockNoGo.lean`,
whose inspected statement concerns exact finite-period certificates, not
this geometric-owner partial-response correspondence. This calibration
is not inferred from that different no-go and makes no Lean novelty claim.

### 14.3. A genuine whole-correspondence extremum for the remaining test

The sparse-record question can be sharpened to an attained maximum,
without claiming that this maximum has already been evaluated. For the
canonical game above, put

    m_delta=max_(p in N_(0,delta)) Pr_p(T0=0).             (14.6)

The maximum exists by the unconditional compact producer; m_delta>=delta
by the budget at1. The sure-hazard exclusions of Nash Section14.4 carry
unchanged to K_delta, since their only budget input was
S0(t+1)<=c^(t+1), and the resulting minimum hazard against a sure nonowner
is at most delta. Thus every finite joint reach is positive here.

Any BINDING date, not only a strict record, re-roots into the SAME N:
if S0(t)=c^t, conditioning gives S_tail(u)<=c^u and every K_delta tail
replacement splices back legally. Full nonowner inequalities pass through
positive reach exactly as in Section11. Therefore

    m_delta=delta ==> EVERY owner law in N is Geom(delta). (14.7)

Indeed every source has root hazard at least delta and at most m_delta,
so equality gives S0(1)=c. Re-root there; the new root again has hazard
delta. Induction gives the claimed entire geometric law. Section14.1
then forces the unique nonowner response profile. For small delta the
ENTIRE N would be that singleton and its minimum owner loss would tend
to2/5.

This yields the concrete maximum principle tested below:

    Does the perturbed Solan game force m_delta=delta
    for all sufficiently small delta?                    (MP)

A proof with a bounded independent check is supplied in Section14.6. Conversely
any profile improving on(14.5) necessarily has m_delta>delta. An optimal
owner can allocate its deadline mass across WEAK record plateaux, not
just use the first-argmax representative; replacing it by that
representative while keeping opponents fixed need not preserve the
opponents' exact best replies. Section14.6 instead controls the maximum
hazard over the ENTIRE correspondence and ALL calendar dates.

For the cyclic RAW three-player table the three owner choices are symmetric.
For the canonical Fin4 table with an extra zero-singleton label, excluding
owner0 alone would NOT exclude every owner permitted in Section1. No
all-owner Fin4 falsification is claimed here.

### 14.4. Properness and the exact three-core-owner quantifiers

Status: ORDINARY PROOF, bounded independently checked by CODEX_TURING_BOX
as part of Sections14.4--14.6. Fix
0<e<1 and 0<delta<1/2. Every source in N_(0,delta) for the raw
three-player table has ALL THREE clocks proper and unbounded.

First the sure-hazard exclusions used in Section14.3 can be stated without
fixing the owner clock. If owner0 quits surely at a reached date, player1
strictly Continues and player2 strictly Quits. Owner0 then strictly prefers
Continue, and may choose the minimum budget-compatible hazard, which is
at most delta<1. If player1 quits surely, player2 strictly Continues and
owner0 strictly Quits, giving the already excluded case. If player2 quits
surely, owner0 strictly Continues and therefore uses a hazard at most
delta; player1's Quit-minus-Continue difference is
1+e-h*(2+e)>0, giving the excluded sure player1 case. All finite joint
reaches are positive. In particular a proper clock cannot be bounded.

Every nonowner has Never as a full best reply: an improper clock actually
supports Never, while a proper unbounded clock supports arbitrarily late
optimal finite dates, whose payoffs converge to Never because owner0 is
proper. Let Y1(t),Y2(t) be the resulting conditional raw Never values.
If player1 were improper, its conditional finite mass would tend to zero.
Then Y2(t) would tend to zero, since raw player2 receives zero when only
owner0 quits. But its immediate Quit payoff
(1-x(t))*(1+e*h(t)) tends to at least1. This contradicts Never optimality.
Thus player1 is proper. If player2 were improper, its conditional finite
mass would tend to zero and Y1(t) would tend to3, because owner0 remains
proper in every finite tail. Its immediate Quit payoff is at most1+e<3.
Consequently x(t)=0 at every sufficiently late date, contradicting the
proper unbounded player1 clock. Thus player2 is proper as well.

Now choose ANY core owner a in {0,1,2}. On the entire constrained product
K_(a,delta) times the two unrestricted nonowner-law spaces, absorption is
almost sure, simply because the chosen owner is proper. The canonical
shift subtracts exactly1 from prescribed payoffs of recipients1,2 and
zero from recipient0, independently of the profile. The same constants
apply to EVERY legal constrained-owner competitor and EVERY complete
nonowner deviation: either the deviator remains proper by K_delta, or a
distinct proper owner is retained. Hence the ENTIRE constrained Nash
correspondence is identical before and after the canonical shift, for
every core owner. This argument does not presuppose opponent properness.

Raw cyclic symmetry and the preceding properness result now imply that
all source clocks are proper for each core-owner choice. Consequently
EVERY unrestricted owner deviation also retains a distinct proper clock;
the full owner cap and its actual payoff shift by the same constant.
The three complete owner-loss minima, and not merely their constrained
payoff objectives, are therefore equal. An owner0 obstruction would cover
all three CORE owner choices. A fourth padded owner is still a separate
quantifier and is not silently removed by this argument.

### 14.5. An exact zero-hazard lemma removes owner payoff dips

Status: ORDINARY PROOF, bounded independently checked by CODEX_TURING_BOX
as part of Sections14.4--14.6. Here assume
0<e<=1/2. The following is a two-stage calculation, not an inference from
negative periodic searches. It uses full nonowner best replies, including
Never, at both stages.

Local lemma. Suppose the owner's current hazard is0 and its next hazard
is b in(0,1). Let x,y and x',y' be the current and next nonowner hazards,
all less than1. Let Y1,Y2 and Y1',Y2' be their raw Never values in[0,3]. Assume
the exact recursions and full-response support inequalities

    Y1=(1-y)*Y1',             Y2=3*x+(1-x)*Y2',
    Y1>=1+e*y,               equality if x>0,
    Y2>=1-x,                 equality if y>0,
    Y1'>=(1-b)*(1+e*y'),      equality if x'>0,
    Y2'>=(1-x')*(1+e*b),      equality if y'>0.           (14.8)

The owner's conditional gain from Quitting at the next rather than the
current stage is

    L=y*(3-2*x)+(1-x)*(1-y)*(1-y')*(1+e*x')
         -(1-y)*(1+e*x).                                (14.9)

Then L<=0. Equality is possible ONLY when x=y=x'=y'=0.
Thus if either stage has nonowner activity, L<0.

Proof. The common algebraic bound is easiest to isolate. For
0<=x<=1/4 and 0<=y<1 put

    A=(1+e*y)/(1-y),          B=(1-4*x)/(1-x),
    z(b)=(A/(1-b)-1)/e,      w(b)=1-B/(1+e*b),
    F(b)=y*(3-2*x)+(1-x)*(1-y)*(1-z(b))*(1+e*w(b))
            -(1-y)*(1+e*x).

Whenever 0<=z(b)<=1, the product in F is strictly decreasing in b:
its first factor has derivative -A/[e*(1-b)^2]<=-1/e,
its second factor is at least1 and has derivative
e^2*B/(1+e*b)^2<=e^2, and its first factor belongs to[0,1].
Therefore its derivative is at most -1/e+e^2<0.
At b=0 direct expansion gives

    F(0)=(2*e-1)*x+(2-1/e)*y+(1/e-3-5*e)*x*y<=0.       (14.10)

Indeed the x coefficient is nonpositive. If the xy coefficient is
nonpositive, both remaining terms are nonpositive. Otherwise x<=1/4
bounds the total y coefficient by
(5-3/e-5*e)/4<0, since 3/e+5*e>=2*sqrt(15)>5.
For b>0 this gives F(b)<0 whenever the expression is feasible.

If y>0, (14.8) gives Y2'=B in[0,1], hence x<=1/4,
and Y1'>=A>1. Both next nonowner hazards must be positive: y'=0
would force x'>0 from Y2'<=1<1+e*b and then Y1'=1-b<1;
x'=0 with y'>0 would give Y2'=1+e*b>1. Thus
x'=w(b) and y'>=z(b). Feasibility gives 0<=z(b)<=y'<1,
so (14.9) is at most F(b)<0.

If y=0 and x>0, then Y1'=1. If x'=0, (14.9) is at most
-(1+e)*x<0. Otherwise y'=b/[e*(1-b)]>0, and
Y2'>=B gives x'<=w(b). For x<=1/4 the same F(b) bound applies.
For x>1/4 the crude bound (1-y')*(1+e*x')<1+e gives

    L<e-(1+2*e)*x<=(2*e-1)/4<=0.

Finally let x=y=0. Then Y1',Y2'>=1. If x'>0, both next
hazards are positive and (14.8) gives
y'>=b/[e*(1-b)] and x'<=e*b/(1+e*b); this is again
the strictly negative F(b) bound with x=y=0. If x'=0,
then L=-y'<=0, with equality exactly when y'=0. This proves
the local lemma, including all zero-support cases.

Application to the ENTIRE source. At a K_delta-optimal owner clock,
every positive finite owner atom is at a weak running record of its
pure-deadline payoff f, by the exact quantile equality in Section3.
All source clocks are proper and unbounded by Section14.4.
Suppose h(t)=0 and let u>t be the first subsequent positive owner
hazard; it exists by properness. If there is a nonowner-active date in
[t,u), choose the LAST such date v. Every intervening date between
v and u is completely quiet, so its removal identifies the values and
Quit endpoint immediately after v with those at u. The local lemma
then says f(u)<f(v), contradicting the weak-record requirement at u.
Thus every nonowner hazard in[t,u) is zero. Applying the quiet case
of the same lemma across this completely quiet block gives
f(u)<=f(t), with equality only if both nonowner hazards at u are zero.
The weak-record requirement forces equality. In particular

    h(t)=0 ==> x(t)=y(t)=0,                             (14.11)

and the first subsequent positive owner date is also nonowner-quiet.
No calendar deletion or change of probability mode has been asserted
to preserve the constrained equilibrium; quiet stages are identified
only inside this exact comparison of payoffs and Never values.

It follows that the ENTIRE sequence f(t) is nondecreasing.
Two consecutive positive owner dates are weak records, so their f values
cannot decrease. A zero-owner run is completely quiet, including its
first subsequent positive owner date; f is constant through that run,
and the endpoint is a weak record. This also covers a positive owner
date immediately preceding the run. Therefore

    f(t+1)>=f(t) for EVERY calendar date t.               (14.12)

Consequently every strict increase is a strict owner record and binds
S0(t+1)=c^(t+1). In particular

    f(t+1)>f(t) ==> h(t)<=delta.                         (14.13)

All remaining non-geometric freedom is on genuinely FLAT payoff
plateaux. A hypothesized escape by a dip followed by record recovery
is impossible on this exact source. This is a source refinement, not
a proof that all flat-plateau allocations are geometric.

There is also an attained, rather than merely supremal, global object.
For a sufficiently small fixed e for which the bounded form of the
paper's no-exact-Nash conclusion applies, every p in N has its owner
cap only at Never: a reached finite cap maximizer would give exact
full Nash by Section11. All source clocks are proper, and compactness
of N therefore makes their properness uniform on the WHOLE N.
The full owner cap is continuous there by uniform opponent censoring.
Every profile has a next strict owner record. The open sets
{p:f_p(j)>f_p(0)}, j finite, cover compact N, so some finite J_delta
bounds the next strict-record date uniformly. Exact record re-rooting
in the same N then bounds every successive strict-record gap by
J_delta. Every calendar hazard is consequently a hazard at an offset
at most J_delta from a strict-record tail belonging to N. The finitely
many offset hazard functions are continuous on compact N, since all
their finite survival denominators are positive. Hence

    H_delta=max_(p in N, t>=0) h_p(t)                    (14.14)

is actually attained. Always H_delta>=m_delta>=delta.
By(14.13), any hypothetical H_delta>delta must occur on a FLAT
payoff plateau. Proving that such a global maximum cannot occur on
a flat plateau would give H_delta=delta, all owner hazards equal
delta by the survival budget, and the whole-correspondence obstruction
described in(14.7). Section14.6 gives a bounded independently checked proof for
that final maximum principle. The local lemma alone does not authorize
an earliest-atom redistribution while keeping nonowner best replies fixed.

### 14.6. Whole-correspondence maximum principle, including flat plateaux

Status: COMPLETE ORDINARY PROOF, with a bounded independent adversarial
check by CODEX_TURING_BOX recorded in the feedback file named above.
No Lean implementation or export claim. The check covers all THREE core
owners, not an arbitrary fourth padded owner. Fix

    0<e<min(1/10,e0),       0<delta<1/2,

where e0>0 is any qualitative interval on which the bounded no-actual-
exact-Nash conclusion of Solan2001 applies. No numerical value of e0 is
claimed. This uses the paper only for nonexistence of an ACTUAL Nash
profile with bounded continuation payoffs, not the literal unrestricted
continuation formulation discussed above.

Claim. For owner0, EVERY point of N_(0,delta) has owner clock
Geom(delta). Its nonowner clocks are therefore the unique response laws
in Section14.1. In particular the whole correspondence is a singleton
and its minimum full owner loss tends to2/5 as delta decreases to0.
By Section14.4 the same statement, with cyclic relabeling, holds for
each of the THREE core owners of both the raw and canonical tables.

All maxima and suprema below range over the ENTIRE correspondence and
ALL calendar dates, not over one selected equilibrium branch. Write h,x,y
for the conditional hazards of owner0, player1 and player2. Let Y1,Y2
be the conditional raw Never values of the two nonowners. At every stage
they belong to[0,3], and their exact recursions and support inequalities are

    Y1=h*(3-2*y)+(1-h)*(1-y)*Y1',
    Y2=(3-2*h)*x+(1-h)*(1-x)*Y2',
    Y1>=(1-h)*(1+e*y),       equality if x>0,
    Y2>=(1-x)*(1+e*h),       equality if y>0.             (14.15)

Define the owner's Quit endpoint, opponent stopping contribution and
joint opponent survival by

    Q=(1-y)*(1+e*x),   O=y*(3-2*x),   k=(1-x)*(1-y).

The difference between its pure deadlines at this and the next date,
divided by the positive joint reach to this date, is

    C-Q,             C=O+k*Q'.                           (14.16)

Section14.5 gives C>=Q at EVERY stage. If h>delta then C=Q: a strict
increase would bind the next survival budget and imply h<=delta.

The compact finite-offset representation at the end of Section14.5
applies not only to h but also to x,y,Q,Y1,Y2. Their fixed-offset
conditional functions are continuous on compact N, all finite survival
denominators are positive, and record re-rooting stays in N. Consequently
the calendar extrema

    H=max h,       X=max x,       Y=max y,       q=max Q

are attained. We can use M1=sup Y1 as well. Sure hazards are excluded,
so H<1. The date-zero survival budget of every source gives its initial
hazard at least delta, hence H>=delta. No conditional hazard floor at
arbitrary dates is assumed.

Step1: Q<=1 throughout the correspondence. Suppose its attained global
maximum q exceeded1. At that stage x>0 and
y<e*x/(1+e*x). Since Q'<=q, (14.16) gives

    C-q <= y*(3-2*x)-q*(x+y-x*y)
         < y*(2-x)-x
         < x*(e*(2-x)/(1+e*x)-1) < 0.

The last inequality holds for e<=1/2 and x>0. This contradicts C>=Q=q.
Thus Q<=1. In particular

    x>0 ==> y>0.                                        (14.17)

Step2: Y2<=L_H:=1+e*H throughout. If Y2 at some stage exceeded L_H,
then y=0 there by its support equality in(14.15), and x=0 by(14.17).
Its recursion would give Y2'=Y2/(1-h)>=Y2>L_H. Repeating forces
x=y=0 forever after that stage and gives
Y2(t+n)=Y2(t)/product_(j=t)^(t+n-1)(1-h(j)). Owner properness makes
this product tend to0. This contradicts the bound Y2<=3.

Step3: a uniform bound on X. At a stage with x=X>0, (14.17) gives
y>0, so Y2=(1-X)*(1+e*h). Its recursion and the next-stage floor
Y2'>=(1-x')*(1+e*h')>=1-X imply

    X/(1-X)
      <= ((1+e)*h+(1-h)*X)/(3-2*h)
      <= ((1+e)*H+(1-H)*X)/(3-2*H).

The last ratio increases with h; its derivative numerator is
3*(1+e)-X>0. Rearranging gives

    (1-H)*X^2+(2+e*H)*X <= (1+e)*H,
    hence X <= (1+e)*H/2.                               (14.18)

This remains true when X=0.

Step4: if H>delta, its attaining stage must have H<1/2. Assume H>delta
and work at that stage. It is flat by(14.16). If x=0, then the floor
Y2>=L_H contradicts Y2=(1-H)*Y2'<=(1-H)*L_H. Thus x>0 and y>0.
The player1 support equality and the next-stage floor Y1'>=1-H give

    (1-H)*(1+e*y)
      >= H*(3-2*y)+(1-H)^2*(1-y),
    y >= H*(2+H)/(1+e*(1-H)+H^2).                       (14.19)

Flatness also gives Q>=O, hence

    y <= (1+e*x)/(4+(e-2)*x) <= (1+e)/(2+e) <= 11/21.

If H>=1/2, (14.19) instead gives
y>=(5/4)/(21/10)=25/42>11/21. Here H<=1 bounds the denominator
by2+e<=21/10. This contradiction proves H<1/2 in the hypothesized
H>delta case.

Step5: a uniform bound on Y. When x(t)>0, the support equality gives
Y1(t)<=(1+e*Y). When x(t)=0, let u>t be the first subsequent date
with x(u)>0; it exists because player1 is proper. Write A for owner
conditional survival from t through the dates before u. The player2
recursion through this x=0 interval gives Y2(t)=A*Y2(u). The floor
Y2(t)>=1 and Step2 imply A>=1/(1+e*H). Before u, player1's Never
payoff is at most3 on owner stopping and0 on player2 stopping; its
continuation contribution is at most A*Y1(u), since raw Y1(u)>=0.
Therefore

    Y1(t) <= 3*(1-A)+A*(1+e*Y)
           <= (1+e*Y+3*e*H)/(1+e*H)=:Mbar.

Since 1+e*Y<3, the expression decreases with A. This bound also covers
x(t)>0. Thus M1<=Mbar=1+e*(Y+2*H)/(1+e*H).
Use this in the player1 recursion and floor at an arbitrary stage.
With z=h/(1-h),

    y*(e+Mbar+2*z) <= 3*z+Mbar-1.

The resulting ratio increases with z, since its derivative has positive
numerator 3*e+Mbar+2. Put Z=H/(1-H), and take the maximum of y.
With E=Mbar-1=e*(Y+2*H)/(1+e*H), this yields

    Y*(1+e+2*Z) <= 3*Z+E,
    Y*(1+2*Z+e^2*H/(1+e*H))
       <= 3*Z+2*e*H/(1+e*H).

In the first line we only dropped the nonnegative term Y*E. Multiplying
by1-H and dividing gives the exact convenient bound

    Y <= H*[3+2*e*(1-H)/(1+e*H)]
              /[1+H+e^2*H*(1-H)/(1+e*H)]
       <= H*(3+2*e)/(1+H) <= (16/5)*H.                 (14.20)

Step6: the attained maximum cannot be flat. Retain the hypothetical
H>delta, so Step4 gives0<H<1/2. At its attaining stage (14.19) implies
y>=(9/5)*H. Indeed replacing e by1/10 in the denominator only lowers
that bound, and

    5*(2+H)-9*[1+(1/10)*(1-H)+H^2]
       =1/10+(59/10)*H-9*H^2 > 0  for 0<H<1/2.

By(14.18), x<=(11/20)*H<=(3/5)*H. Also Q'>=1-Y. Hence

    C-Q
      >= y*(3-2*x)-(1-y)*[(1+e)*x+Y*(1-x)]
      >= y*(3-(6/5)*H)-(1-y)*(193/50)*H.

For the second inequality, bound the negative bracket separately by
(11/10)*(3/5)*H+(16/5)*H=(193/50)*H. This does not assume
that the crude bound (16/5)*H is at most1. The last expression increases
with y, so it is at least

    (9/5)*H*(3-(6/5)*H)-(1-(9/5)*H)*(193/50)*H
      =H*[77/50+(1197/250)*H] > 0.

This contradicts the flat equality C=Q. Thus H<=delta. Since every
INITIAL date-zero hazard is at least delta, H=delta. All hazards in every source are
at most delta, so their survival products are at least c^t; the K_delta
budget makes them at most c^t. Equality and induction force every hazard
to be delta. Section14.1 determines the remaining clocks uniquely and
computes the loss limit2/5. Section14.4 transfers the full conclusion to
each core-owner choice. This completes the ordinary proof.

Independent check scope. CODEX_TURING_BOX checked Steps1--6, the calendar
attainment input from Section14.5, all zero-support cases of the two-stage
lemma, core-owner canonical transport, and fixed-geometric response
uniqueness/loss. No objection was found. Its wording clarification about
the INITIAL hazard budget has been incorporated above. No claim about
every possible fourth-owner padding follows from this three-player proof.

### 14.7. Why a fourth owner is a separate selection quantifier

The result proposed in Section14.6 covers all THREE original owners.
It must not be described as a whole-owner Fin4 obstruction merely by
adding a label. In particular, a dummy with reward-1 whenever it joins
(including when it quits alone) and0 otherwise, whose presence does not
change core rewards, turns its independent Geom(delta) into realized
discounting of the core by alpha=1-delta. Its singleton is negative, so
that literal padding lies outside Section1's nonnegative-singleton scope.

There is a distinct nonnegative-singleton variant: add1 to this dummy's
reward at EVERY finite nonempty coalition, giving dummy reward1 when
absent and0 when joining, including alone. Because the K_delta dummy
is proper, that shift is constant under EVERY legal constrained-source
comparison; the entire dummy-owner constrained correspondence is
unchanged. Core rewards are left unchanged. At a proper-core component,
the dummy's full Never cap becomes1 and its full debt still equals the
probability that it quits no later than the core. A good discounted-core
component can consequently give a good fourth-owner source even when
the core-owner branches are bad. This is not the different padding in
Nash Section14.4, and it is not an asserted constant-shift transport of
the canonicalized CORE rewards under dummy-first stopping.

The exact discounted-core connection is being checked separately with
CODEX_TURING_BOX. Its role is to protect the fourth-owner quantifier,
not to weaken or strengthen the three-core-owner claim above.
