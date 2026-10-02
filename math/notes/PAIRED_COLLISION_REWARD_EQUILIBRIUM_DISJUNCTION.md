# Paired collision rewards: a periodic–stationary equilibrium disjunction

Author: CODEX_NOETHER_SUPPORT.
Independent reviews: [CODEX_RADO_BOUNDARY](../feedback/CODEX_NOETHER_SUPPORT__PAIRED_PAIR_REWARD_DISJUNCTION__BY_CODEX_RADO_BOUNDARY.md),
[CODEX_TARSKI_PREMIUM](../feedback/CODEX_NOETHER_SUPPORT__PAIRED_PAIR_REWARD_DISJUNCTION__BY_CODEX_TARSKI_PREMIUM.md).
The direct censored finite-horizon estimate below was suggested by
CODEX_RADO_BOUNDARY and independently verified in the accompanying proof.

The one-parameter ORIGINAL-table family below has a uniform-equilibrium
payoff for every real parameter. The new calculation
joins an adaptive two-phase construction to a full-support stationary
construction; it does not solve the arbitrary 44-coordinate collision
cylinder. Existing results supply the low-parameter exit.

## 1. Supplied data and exact conclusion

Players are 0,1,2,3. Live and Never payoff are zero. Players use independent
private behavioral randomization; one deviation can replace that player's
ENTIRE behavioral strategy. Payoff recipients index columns in this
table. Fix any real c and use these literal terminal rewards:

| Quitting coalition | Reward vector |
| --- | --- |
| 0 | (1,4,0,0) |
| 1 | (4,1,0,0) |
| 2 | (0,0,1,4) |
| 3 | (0,0,4,1) |
| 01 | (c,c,1,1) |
| 02 | (c,1,c,0) |
| 03 | (c,0,1,c) |
| 12 | (0,c,c,1) |
| 13 | (1,c,0,c) |
| 23 | (1,1,c,c) |
| 012 | (1,0,0,0) |
| 013 | (0,1,0,0) |
| 023 | (0,0,0,1) |
| 123 | (0,0,1,0) |
| 0123 | (−1,−1,−1,−1) |

Strings denote sets of players. Only the twelve pair-MEMBER coordinates
vary. In particular this does not vary passive pair rewards with c. The
own-singleton levels are 1 and the singleton-difference matrix is always

    Γ=[0 3 −1 −1; 3 0 −1 −1; −1 −1 0 3; −1 −1 3 0].

Theorem. Every real c has a fixed uniform-equilibrium payoff, by the
following overlapping, nonoptimized disjunction on the SAME reward table.
The only input is the displayed raw table and its real parameter: rates,
continuation values, full caps, and the applicable actual exit are all
produced below. No supplied equilibrium, favorable continuation, or open
strategic producer hypothesis is assumed.

- c≤1: the existing unit-singleton/capped-joint-exit theorem applies.
- 1≤c≤2: an exact two-phase equilibrium has continuation parameters
  1/4<b<a<9/10. Keeping K≥1 whole cycles and censoring each player's
  later clock independently to Never gives actual finite laws with
  full exploitability at most 8(9/10)^(4K).
- 2≤c≤4: an exact full-support stationary equilibrium has one common
  quitting hazard q in (1/100,1/2).
- c≥4: the pure date-zero coalition 01 is an exact terminal equilibrium.

For a complete profile σ, U_i(σ) is the expected reward of the first
nonempty quitting coalition, with value zero if no player ever quits.
Let B_i(σ)=sup_τ U_i(τ_i,σ_−i), where τ ranges over all complete
behavioral replacements, and E(σ)=max_i(B_i(σ)−U_i(σ)). The supremum
includes every finite stopping date, unbounded randomized stopping laws,
and Never. Behavioral observations before absorption reveal only continued
live play; no player observes another player's future private clock.

A fixed uniform-equilibrium payoff v means that for every ε>0 there
are one profile σ and an integer N₀ such that, for EVERY N≥N₀,
its N-stage expected average payoff differs from v by at most ε in
each coordinate and every complete unilateral behavioral deviation has
N-stage gain at most ε. The table and v precede the accuracy; the
profile and threshold may depend on it.

In the periodic branch, a,b are selected ONCE from c, before the truncation
count or accuracy. The displayed finite laws control every complete
behavioral deviation, including all dates after their support and Never.

## 2. Existing exits and the source discipline

For c≤1, every member of every coalition is paid at most 1 and each own
singleton pays 1. These are exactly the two hypotheses of the existing
fixed-payoff theorem, with no restriction on the sign of c or on passive
rewards. Section 7 records the precise source and its fixed-target bridge.

For c≥4, the sure coalition 01 pays its members c and the two outsiders
1. A member who continues instead receives 4 from the other sure member;
an outsider who joins gets 0 from its triple. Thus no complete deviation
improves: another sure player screens every member's response, and both
sure players screen each outsider. Never is included. The fixed uniform
payoff is (c,c,1,1).

For 1≤c<4, there is no pure terminal equilibrium. Singletons admit a
cross-pair join with gain c; the pairs 01 and 23 admit a member leave with
gain 4−c; each cross pair has an outsider join with gain 1; each triple
has a zero-paid member who can leave for at least 1; grand-coalition
members can leave from −1 to 0. All-Never has singleton gain 1. At any
earliest stopping date these same toggles defeat a deterministic profile,
not only a date-zero profile.

Punishment normality P_i≤s_i=1 holds for every c: all-Never opponents
give best reply value 1. The positive-owner all-rates solo/join test also
holds on c≥1, since a cross recipient has gain
(1−h)+hc≥1 at every rate h∈(0,1]. These checks do not supply the
periodic construction; they prevent replacing its incentive checks by
an absent pure exit or a normalization assumption.

## 3. Two phases and all four active equations

Fix 1≤c≤2. Phase A activates players 0 and 2 with continuation
probabilities a and b respectively. Phase B activates 1 and 3 with the
same respective continuation probabilities. All inactive players
Continue. Repeat A,B forever, with independent private draws.

Call players 0,1 primary and players 2,3 secondary. Define

    P=c−(c−1)b,             R=c−(c−1)a.                 (1)

These are the respective active Quit endpoints: the cross opponent's
singleton pays the queried owner zero, while the owner's singleton pays
1 and a joint pair pays c. The proposed phase payoffs are

    V^A=(P, P/b, R, R/a),
    V^B=(P/b, P, R/a, R).                               (2)

At its active phase a primary owner who continues gets b(P/b)=P;
a secondary owner gets a(R/a)=R. Its own mixing probability is irrelevant
to these equalities. At its quiet phase the original passive pair rewards
are 1 for primary owners and 0 for secondary owners. Their prescribed
Continue equations are therefore exactly

    P/b=(1−a)(1+3b)+abP,
    R/a=4a(1−b)+abR.                                   (3)

Equivalently, the two residuals are

    F=P(1−ab²)−b(1−a)(1+3b)=0,
    G=R(1−a²b)−4a²(1−b)=0.                            (4)

Each equation serves both owners of its type in their respective phases.
They are prescribed-payoff equations, not a menu-Nash proxy. Inactive
joining responses still have to be checked after producing a,b.

## 4. Actual production of an admissible zero

For a∈[0,1], put R(a)=c−(c−1)a. The function

    f(a)=4a²−R(a)

has a unique zero a₀ in [1/2,2/3): f(1/2)=(1−c)/2≤0,
f(2/3)=(10−3c)/9≥4/9>0, and f is strictly increasing on
[1/2,1]. Define, for a∈[a₀,1],

    b(a)=(4a²−R(a))/(a²(4−R(a))).                      (5)

Here 1≤R≤2, so the denominator is strictly positive. Equation G=0
holds identically. We have b(a₀)=0 and, for a₀<a<1,
0<b(a)<1; the upper bound follows because numerator minus denominator
is −R(1−a²)<0.

To obtain the additional ordering b<a, use

    g(a)=4a²−R(a)(1+a+a²)
        =(c−1)a³+3a²−a−c,
    b(a)−a=(1−a)g(a)/(a²(4−R(a))).                    (6)

At a₀, g=−R(a₀)(a₀+a₀²)<0. On [a₀,1],
g'=3(c−1)a²+6a−1≥2. Also g(9/10)≥259/1000>0; its
minimum over 1≤c≤2 occurs at c=2. Thus a unique a₁ satisfies

    a₀<a₁<9/10,       g(a₁)=0,

and 0<b(a)<a for a₀<a<a₁, with b(a₁)=a₁.

Now insert b(a) into F. This is continuous on [a₀,a₁], even though
the proposed value P/b is not defined at the left endpoint: the
multiplied residual F itself is defined there and equals c>0. At a₁,
b=a and G=0 give

    F=4a²(1−a)−a(1−a)(1+3a)=−a(1−a)²<0.             (7)

The intermediate value theorem gives a zero strictly between these
endpoints. Hence it supplies an actual a,b with 0<b<a<9/10, not an
extraneous eliminated root at all-Continue or at b=0.

Finally b>1/4. Since P≥1, equation F=0 implies

    1−b²≤P(1−ab²)=b(1−a)(1+3b)≤b+3b²,

so 1≤b+4b², impossible when b≤1/4. Also a>a₀≥1/2. All
claimed rate bounds have now been proved without uniqueness of F's zero.

## 5. Quiet joins, Never, and complete finite laws

At a primary owner's inactive phase, its full immediate-Quit endpoint is

    T_p=c(a+b)+(1−2c)ab.

It includes the all-opponents-Continue singleton, both joining pairs,
and the joining triple of reward 0. At a secondary owner's inactive
phase, the joining triple pays 1, giving

    T_s=1+(c−1)(a+b−2ab),       T_s−T_p=(1−a)(1−b).      (8)

Define the quiet Continue-minus-Quit slacks
S_p=P/b−T_p and S_s=R/a−T_s. Substituting (5) gives the exact identity

    S_s=−(1−a)R L/[a²(4−R)],
    L=(c−1)(a²+2a−1)−3a.                              (9)

For 1≤c≤2 and 0<a<1, L<0. If a²+2a−1≤0, this follows
from −3a<0. Otherwise c−1≤1 gives
L≤a²−a−1<0. Thus S_s>0. The other slack is larger, since

    S_p−S_s=c(a−b)/(ab)+(1−a)(1−b)>0.                 (10)

All four active endpoints tie and all four inactive Continue endpoints
strictly dominate Quit in the ORIGINAL table. Equations (3) identify
the prescribed recursion. Joint continuation over a full cycle is
C=a²b²<1, so its iteration identifies (2) with the actual payoff.

For a queried primary player the three fixed opponents survive a cycle
with probability ab²; for a secondary player it is a²b. Both are below
(9/10)^3. Iterate the one-stage endpoint inequalities against any
complete behavioral deviation. The bounded surviving remainder tends
to zero at this rate, so the deviation payoff is at most the corresponding
coordinate of (2). Prescribed play attains equality. This caps ALL finite
dates and Never, not merely two-periodic responses. In particular the
literal Never response is controlled by the same iteration; it is not
assigned payoff zero when opponents absorb.

The same profile delivers its fixed uniform payoff: a finite bound on
terminal rewards and the geometric opponent survival bound give a
uniform O(1/N) difference between terminal and N-stage Cesàro payoff,
for every unilateral deviation. Stationarity of the two-phase schedule
modulo phase gives the same argument at every suffix.

There is also an exact finite-law account. Fix K≥1, keep dates
0,...,2K−1 and move every later finite clock to Never independently.
Explicitly, for k=0,...,K−1 the retained independent marginal atoms are

    Pr(T_0=2k)=Pr(T_1=2k+1)=(1−a)a^k,
    Pr(T_2=2k)=Pr(T_3=2k+1)=(1−b)b^k,

with Never masses a^K for players 0,1 and b^K for players 2,3.
Each marginal is sampled privately; this notation does not couple the
different players' draws. Write v=V^A. Every coordinate of both phase
values is at least 1, and v_i<8 because 1≤P,R≤2 and b>1/4, a>1/2.
Renewal gives

    U_i^K=(1−C^K)v_i.                                  (11)

Every pure response before the cutoff has unchanged payoff. A later
finite date pays singleton 1 after the opponents survive the cutoff;
Never pays zero on that event. Both are bounded by waiting to the cutoff
against the infinite opponents and then resuming prescribed play, whose
conditional payoff is v_i≥1. Thus B_i^K≤v_i for every complete response.
Conversely, quit at the owner's first active date, 0 or 1. Prior
prescribed actions were Continue and the active Quit endpoint ties, so
this legal retained date attains the initial value v_i. Therefore

    B_i^K=v_i,
    E^K=C^K max_i v_i≤8(9/10)^(4K).                    (12)

This includes previously unlisted after-support dates. It is an actual
finite-law producer, not cap-preserving compression of arbitrary laws.

There is also a direct uniform-horizon bound for these FINITE laws, without
applying infinite-opponent contraction after censoring. Write W_i^N for
the N-stage expected average payoff, with N≥1. On every path absorbed
at a retained date t<2K, at most 2K initial stage rewards differ from
the terminal reward. Throughout 1≤c≤2 all reward magnitudes are at
most 4, so the pathwise difference is at most 8K/N.

Under prescribed censored play, every path either absorbs at such a date
or has value zero forever. Consequently
|W_i^N(σ^K)−U_i^K|≤8K/N. Under a unilateral deviation, on the remaining
paths the opponents never quit: any later absorption is the deviator's
singleton of reward 1. Its average contribution is at most its terminal
contribution, including if it quits after N or uses Never. Combining this
one-sided comparison with the early-path bound gives

    W_i^N(τ_i,σ^K_−i)≤U_i(τ_i,σ^K_−i)+8K/N.

The bound is uniform over all complete τ. Therefore

    max_i sup_τ [W_i^N(τ_i,σ^K_−i)−W_i^N(σ^K)]
        ≤E^K+16K/N,
    max_i |W_i^N(σ^K)−v_i|≤E^K+8K/N.                 (12a)

Choose K≥1 so the bound in (12) is at most ε/2, then take every
N≥max(1,⌈32K/ε⌉). The SAME censored law then satisfies both required
uniform-payoff inequalities at target v. This is not geometric absorption
of the censored opponents: their Never mass is positive and was retained
explicitly in the one-sided argument.

## 6. The full-support stationary branch

For 2≤c≤4 let every player use the same quitting hazard q at every
date, and put x=1−q. Each queried owner has the same eight Quit rewards:
singleton 1, three pairs c, one triple 1, two triples 0, and grand −1.
Its nonempty Continue outcomes have singleton sum 4, pair sum 2, and
triple reward 0. Thus

    Q=x³+3cqx²+q²x−q³,
    H=4qx²+2q²x,
    α=x³,
    D(q)=(1−α)Q−H.                                    (13)

The exact arithmetic is

    D(1/2)=(21c−41)/64≥1/64,
    D(1/100)|_(c=4)=−7087044691/10^12<0.                (14)

D is increasing in c at each q∈(0,1), since its c coefficient is
3qx²(1−x³)>0. Hence D(1/100)<0 throughout 2≤c≤4. A zero exists
in (1/100,1/2). For this q, H/(1−α)=Q.

The exact stationary full cap is max(Q,H/(1−α)). Indeed a finite
deadline t yields H(1−α^t)/(1−α)+α^tQ, while Never yields
H/(1−α); the same Bellman bound controls every behavioral replacement.
Both endpoints equal Q at the selected zero. The prescribed stationary
payoff is also Q by its absorbing Bellman fixed point. This proves exact
terminal Nash and the fixed uniform payoff (Q,Q,Q,Q), with all-player
opponent survival at most (99/100)^3 per date. No positivity assumption
on Q or artificial terminal-payoff shift is needed.

Thus the stationary branch is already available at the periodic
branch's chosen upper endpoint c=2. Failure of the periodic construction
outside its proved interval does not leave a stranded rate-family
obstruction: at every c≥2 an actual stationary or pure exit applies.

## 7. Source correspondence and conjecture-facing change

The supplied family is not assumed to come from an arbitrary table by a
UE-preserving transformation. It is a literal one-dimensional subfamily
of the positive-determinant paired singleton cylinder. It adapts c from
the INPUT data and then selects the appropriate actual strategy.

The bounded source audit inspected the following declarations and inputs.

- `QuittingUnitSoloExit` and `QuittingCappedJointExit` in
  `UniformEquilibrium/Quitting/Classification/SoloExitPreference.lean`
  require respectively own singleton 1 and member rewards at most 1.
  Thus c≤1 is covered and every c>1 fails capped joint exit.
- `quittingCappedJointExitUniformεExistence_holds` and
  `exists_uniformEquilibriumPayoff_of_soloExitPreference` in
  `UniformEquilibrium/Quitting/Classification/Existence/PerfectSequenceExtraction.lean`
  discharge the existence law internally and yield one fixed uniform
  payoff. The profile-per-error versus fixed-target bridge is explicit in
  `UniformEquilibrium/Quitting/Classification/SoloExitPreferenceExistence.lean`;
  no externally assumed extraction law remains in the cited consumer.
- The more general `HasLowActiveQuittingRootQuitPayoff` in
  `UniformEquilibrium/Quitting/Classification/Existence/PerfectAbsorbingRow.lean`
  also fails for c>1:
  activate only a pair with both positive hazards. Each active owner's
  Quit endpoint is 1+h(c−1)>1. The other two players are inactive and
  cannot witness the predicate. Hence its current existence consumer in
  `PerfectSequenceExtraction.lean` does not subsume this interval.
- `PairedCycle.RawRegion` in
  `UniformEquilibrium/Quitting/Cycles/PairedCycleSchedule.lean` uses
  `Math.PairedAffine.OwnBounds` and `PassiveBounds` in
  `MathUE/PairedAffineIntervalEstimates.lean`. The latter require BOTH
  quiet singleton rewards in [19/10,21/10], and a quiet tie near zero.
  Here every recipient has only one positive singleton comparison and
  two negative ones. Cross-pair schedules give quiet singletons 4 and 0;
  a within-partner schedule gives an active partner reward 4 rather than
  near zero. No relabeling supplies that interval source. The signed
  passive-tie allowance does not repair these singleton failures.
- The signed-cycle and cyclic open-sign sources require a different
  directed singleton sign pattern, as checked in
  [the preceding cylinder audit](../notes/CODEX_NOETHER_SUPPORT__PAIRED_SINGLETON_CYLINDER_AND_GLOBAL_TWO_PHASE_TEST.md).
- `periodTwoProfile_isExactTerminalNash` and
  `periodTwo_isUniformEquilibriumPayoff` in
  `UniformEquilibrium/Quitting/Examples/BlockPair/FourPlayerPairedSingletonPeriodTwo.lean`
  supply the literal c=1 completion, not the c-family. Equations
  (1)–(4) reduce to that source's active identities at c=1.
- The ordinary-math
  [asymmetric paired-region note](../notes/CODEX_TARSKI_PREMIUM__ASYMMETRIC_PAIRED_CYCLE_EXACT_CAP_SELECTOR.md)
  has the same incompatible quiet-singleton interval hypotheses.
  The [tracked-corpus open-ball result](../notes/CODEX_DESCENDANT__TRACKED_CORPUS_ALTERNATING_PAIR_EQUILIBRIA.md)
  already covers a small neighborhood of the normalized c=1 seed;
  its 10^−7 reward ball does not cover the full interval 1<c<2.
  The generic two-phase compiler, local persistence, and finite truncation
  argument are not new mechanisms here.
- `quittingContinuationBestResponseValue_stationary_eq_max_quitNow_never`
  in `UniformEquilibrium/Quitting/Stationary/CompleteBehavioralCap.lean`
  and `isUniformEquilibriumPayoff_of_stationaryEndpointCertificate_contracts`
  in `UniformEquilibrium/Quitting/Stationary/EndpointCompiler.lean`
  consume the actual stationary root supplied by (13)–(14).

Further cheap class checks do not turn this into a payoff-exclusion example.
At uniform stationary hazards tending to zero, actual payoff tends to
the singleton average 5/4 for EVERY player, independently of each fixed
c. Thus weak singleton payoff exclusion fails. The singleton matrix,
its full normal core and its positive degree remain unchanged; the
negative-index source does not supply this cylinder.

The mathematical increment is the globally c-adapted disjunction and
the admissible, all-response-safe zero construction on 1≤c≤2. It is not
a claim that every table outside previous classes is covered, nor an
exhaustive audit of all possible derived consumers. No arbitrary own
singleton levels, arbitrary passive rewards, or arbitrary triples are
quantified in this theorem.

## 8. Exact checks and boundary tests

Exact symbolic rational calculations independently verified: G=0 after
(5); the sign identity (6); the endpoint identity (7); the inactive
factorization (9); the slack comparison (10); and both values in (14).
Direct enumeration of the original table independently checked all
sixteen phase/owner/Quit-or-Continue identities before imposing F=G=0.
The displayed analytic inequalities, not numerical root searches, prove
existence for every c in each stated interval. The all-Continue point
a=b=1 and the b=0 elimination boundary are explicitly excluded before
defining the payoff vector.

At c=1 the construction agrees with the existing nonstationary boundary
calibration. At c=2 the periodic and stationary branches BOTH apply.
At c=4 the stationary and pure-pair branches BOTH apply; the pure
members' Continue comparison is equality, which is sufficient. Arbitrarily
negative c is handled by the existing signed capped-joint consumer, not
by extrapolating the periodic formulas.

## 9. Actual-data adapter, consumers, and narrow Lean handoff

The input is c and literal equality with the fifteen displayed reward
vectors on the four named players. No new parameter range, affine reward
transformation, or changed Never convention
is part of the adapter. First decide one of the four overlapping parameter
ranges. The low-c range supplies exactly the two existing table hypotheses.
The middle ranges supply actual product laws from the IVT constructions.
The high-c range supplies the literal sure-pair profile.

For 1≤c≤2, equations (11)–(12) give one fixed target v and, at
every positive accuracy, both terminal Nash error and coordinatewise
delivery error below that accuracy. This is exactly the input of
`quittingGame_isUniformEquilibriumPayoff_of_terminalTargetAcceptance`
in
`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`.
That declaration was inspected in its actual fixed-target form. Equation
(12a) also proves the conclusion directly, with a finite support controller
for each accuracy and unrestricted deviations. For the stationary range,
the actual cap and fixed-point inputs go to the contracting stationary
endpoint consumer named in Section 7. The pure pair needs only immediate
absorption and the explicit full comparisons in Section 2.

A narrow formalization can keep the parameterized table and its root
identities beside the existing four-player paired examples. Suggested
mathematical declaration boundaries are:

- the literal table, c=1 equality, constant singleton matrix, and existing
  capped-joint/pure-pair adapters;
- an admissible-rate existence lemma producing 1/4<b<a<9/10 and
  F=G=0 from 1≤c≤2, proved by the two IVT steps and denominator bounds;
- the two actual root sequences, phase payoffs, four active ties, and
  four quiet endpoint inequalities;
- the exact all-suffix terminal equilibrium and fixed-payoff consumer,
  reusing the current periodic behavioral telescope rather than assuming
  it as a new structure field;
- independent censoring, the exact U^K and B^K identities, and the complete
  after-support/Never argument;
- the common-hazard stationary Q,H,α identities and two IVT sign tests;
- finally, the all-real-c disjunction of the existing and constructed exits.

The field polynomial identities are ring calculations with explicitly
positive denominators. Existence uses scalar continuity and IVT, not
a uniqueness theorem, numerical solver, or a chosen equilibrium germ.
Proof fields must not assume existence of the required rates, quiet
incentives, or complete caps. The finite-support and finite-horizon
quantifier order should be stated separately from exact infinite play.

The manuscript is ordinary mathematical evidence, not a Lean validation
claim. No Lean files or exports were edited while preparing it, and no
Lean build was run.

## 10. Scope and nonclaims

The completed improvement is a supplied-collision-parameter disjunction
covering every real c in ONE literal subfamily, including the previously
uncovered periodic interval above capped joint exit. Its rates and strategy
format are selected from the original table, and a stationary/pure exit
covers every parameter beyond the proved periodic range.

The arbitrary 44-coordinate collision cylinder, arbitrary own singleton
levels, and arbitrary passive or triple rewards remain outside the theorem.
The proof neither shows that exact period two always suffices nor that its
chosen periodic rates exist outside 1≤c≤2. It does not infer a no-UE
residual from failure of a rate family. The numerical overlap endpoints
are sufficient, not optimized. Existing periodic compilers, local
persistence results, and the established low-c existence theorem are
dependencies, not claimed new mathematics.
