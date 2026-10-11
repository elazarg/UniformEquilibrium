# Bounded assessment of the exact constrained source and strict-record hull

Reviewer: CODEX_TURING_BOX.

Reviewed notebook:
`notes/CODEX_EMMY_BOX__SINGLE_OWNER_COMPACTIFICATION.md`, SHA-256
`4fc00e4abed645cfcf668769f227f314f3f568d56182d26ee27be159602159d6`.
Scope: Sections2--5,8,11--12, with the literal-two-clock companion in
CODEX_NASH_BOX's Section13 assessed separately under that notebook's
feedback stem. This is one bounded adversarial ordinary-mathematics
assessment, not a Lean check, complete export audit or proof of UE.

Verdict: no mathematical objection found in this exact source chain with
its stated hypotheses. In particular I tried to break the compact-limit
proper-label bookkeeping, record-hull invariance, constrained suffix
agency and all-calendar clock bound. The claimed conclusions survive
those tests. Neither the hull nor its termination window is a zero-debt
producer.

## 1. Nonempty compact constrained Nash really is produced

The finite tails including Never are clopen in the one-point law topology,
so S_a(t)<=c^t is a closed constraint. Their conjunction forces owner
Never mass zero and is convex. Censoring the owner's mass after H to H
changes each prescribed payoff by at most2R*c^(H+1), uniformly over all
unrestricted nonowner laws. The censored game absorbs by H and is a finite-
cylinder continuous function. Thus continuity is genuine on the ENTIRE
constrained product, not inferred from continuity at one proper profile.

At finite H the owner-law domain is a finite polytope. A mixed strategy on
its vertices is exactly one admissible law because own utility is linear;
the vertex mixture is private, with independent nonowner mixtures. This
introduces no common randomization. Ordinary finite mixed Nash applies.
For an arbitrary owner competitor, censoring it to H remains admissible
and converges to it; the uniform error passes that competitor's response
inequality to a compact cluster. For a fixed nonowner deadline or Never,
the inequality also passes. Affinity then covers its entire replacement
law. In fact, while the owner is censored to H, every nonowner deadline
after H has exactly the Never value, since the owner forces absorption
by H. No omitted late menu response is being assumed harmless in the
uncensored game.

For a FIXED owner and rate, each exact response inequality is closed in
the compact product. Their possibly infinite intersection is closed, so
the produced correspondence N_(a,delta) is nonempty and compact. This is
not a compactness statement uniform in delta and not exact full Nash.

## 2. The envelope and complementary equality are exact

Stochastic dominance supplies a monotone coupling T<=G for every owner
law in K_delta. Pointwise f(T)<=max_(u<=G)f(u) proves one direction of
the value formula. Privately selecting a maximizing u through G attains
the other direction and remains in K_delta. Every optimal owner law,
in its monotone coupling, has equality almost surely: the pointwise
nonnegative difference has expectation zero. In particular a positive
owner atom must be a weak record. This applies to ALL optimal laws, not
only the special first-maximizer selector used to prove attainment.

The condition s_a>=0 is used substantively. Late finite deadlines have
limit Never plus the opponents' joint Never mass times s_a, so Never
does not exceed the finite-deadline supremum. With a proper opponent,
the extra term is zero. Nothing here silently changes original Never0.

At a strict record t, equality in the coupling forces the exact event
identity {T>=t}={G>=t}; hence S_a(t)=c^t. At positive joint reach this
is precisely the equality needed for BOTH directions of suffix agency:
the conditioned prescribed law is in K_delta, and any new K_delta suffix
splices into surviving mass c^t without violating any original bound.
All earlier tail constraints are unchanged. Payoff differences have a
positive JOINT-reach multiplier, preserving exact optimality. The
nonowner splice has no constraint. No error/reach division occurs.

## 3. The exits cover their full stated caps

At the earliest final support date H of ANY bounded proper clock, every
player has positive survival to H; otherwise an earlier bounded proper
clock would exist. Nonowner optimality therefore passes to the tail.
If the owner quits surely there, a sufficiently small atom can be moved
to ANY later finite date t, legally choosing its size at most c^t.
Owner optimality excludes every later improvement; nonnegative s_a and
the late-limit identity include Never. If a nonowner quits surely at H,
all later owner deadlines and Never share one Continue endpoint C.
In the profitable-delay case, slack in the constraint at H+1 would
permit an improving transfer. Thus h=max(0,1-c^(H+1)/S_a(H))<=delta,
and the full tail loss is at most2R*delta. No lower bound on reach or
upper bound on H is missing.

When only the owner is proper, every late nonowner conditional law tends
in total variation to literal Never. The owner conditional clock remains
proper and earns s_a against those limiting opponents. Coupling bounds
both its prescribed value and EVERY deviation value uniformly. This
really gives full terminal approximate Nash on reached tails, not just
finite deadlines or an approximation of the prescribed payoff alone.

At first finite owner-cap attainment, the date is a strict record. The
conditional finite and Never responses share their earlier opponent-
absorption contribution, so immediate Quit attains the full tail cap.
It is a legal constrained response. The reached re-root is therefore
exact full Nash. The positive-reach qualification is essential and is
correctly retained in the notebook's exact counterexample.

## 4. Minimal proper COUNT removes the weak-limit loophole

Under a GLOBAL gap gamma and 2R*delta<gamma, the exits imply that EVERY
point of the SAME N has at least two proper clocks, all unbounded. This
whole-correspondence quantifier is indispensable.

Minimize the integer proper count over all N, not over one chosen branch
or an unproved closed proper-count stratum. If p has minimal label set A,
its strict-record tails remain in N. Each originally improper label
converges to literal Never in total variation, because its positive Never
mass stays in the denominator. A compact cluster q therefore has no
proper labels outside A. If any A label became improper, q in N would
contradict the global integer minimum. Thus all A labels remain proper;
the bounded-clock exit makes them unbounded. This does NOT assume
properness is weakly closed. The same count argument works throughout
the closure K of all record tails of q.

Record invariance survives this closure. For x in K a fixed strict record
t is stable under nearby finite-cylinder payoffs. Conditioning at fixed
t is continuous because all survivals at x are positive. A strict record
of a record tail is a strict record of q: later deadline differences are
scaled by the same positive opponent survival, and the earlier record
already beats every deadline preceding it. Hence conditional limits are
again limits of q's record tails. This establishes invariance of K,
not merely that it contains some unrelated conditional profiles.

## 5. Uniform all-tail termination and its exact limitation

For each A label, the continuous finite tails S_i(m) decrease pointwise
to0 on compact K. The decreasing-closed-set/Dini argument gives uniform
properness at the initial date. Every recipient has a distinct uniformly
proper opponent, since |A|>=2. Thus arbitrary late responses and Never
have uniformly small tail errors, proving continuity of full caps on K.

Since immediate Quit is legal, U_a>=f(0); the GLOBAL gap gives
B_a-f(0)>=gamma. Uniform convergence of f(N) to the Never cap B_a then
forces a new strict record by one common N. Exact record invariance
repeats this bound after every record. For any calendar u, a record
v in[u,u+N] and uniform properness of its re-root give the notebook's
half-survival bound at u+M+2N. The extra selected record w is legitimate;
no unconditioned properness estimate is being applied at a nonrecord
tail. Every denominator is positive by unboundedness.

The lower bound on this particular window W=M+2N also checks. At the
first owner record r>=W, one has r<=W+N and S_a(r)=c^r. The half-tail
bound at0 yields c^(W+N)<=1/2. Since W>=2N,
(-log c)W>=(2/3)log2. Therefore delta*W cannot vanish as delta tends
to0. The note does not misread its delta-dependent compactness constants
as a small-regret bound.

## 6. Significance and precise surviving obligation

This produces more than a description of an arbitrarily selected bad
branch. Under a hypothetical global gap it produces, from the ENTIRE
exact constrained correspondence, a compact record-invariant source with
all retained clocks uniformly conditionally terminating and all discarded
labels literal Never. The real work beyond compactness is exact Nash,
strict-record saturation of the owner envelope, the reached bounded-clock
exit, and integer minimization over the whole correspondence.

Together with the separately assessed nonresonant two-clock argument,
it excludes the previously surviving minimum-proper-count-two source
mode after a gap-preserving generic reward perturbation and rate choice.
It does NOT yet exclude any raw reward-table counterexample class: every
remaining table might still produce a three/four-proper source. It does
not show that the owner deficiency tends to0, that an owner-only point
exists, or that replacing one Never-indifferent player by Never preserves
the other response caps. Those are genuine missing global operations.

The next mathematical test should use this produced three/four-clock
source to improve full owner loss or force a legal support reduction.
Another arbitrary bad equilibrium or a delta-dependent recurrence estimate
alone cannot answer that question.

## Exact tracked source boundary inspected

The ordinary producer/hull above is not claimed as existing Lean code.
I inspected `CompactStoppingLaw`, `compactStoppingLawEquivPMF`,
`compactStoppingTime_finiteSingleton_isClopen`,
`compactStoppingTime_tail_isClopen`,
`CompactStoppingLaw.tendsto_realMass_of_isClopen` and
`CompactStoppingLaw.tendsto_tail_realMass_top`
(`MathUE/ProbabilityMassFunction/CompactStoppingLaw.lean`);
`quittingTerminalPayoff_update_finiteTime_tendsto_never_add_opponentNever_mul_singleton`
and `quittingCompactStoppingLawProfile_cap_le_finiteBound_add_opponentNeverProduct_mul_negPart`
(`UniformEquilibrium/Quitting/Terminal/CompactStoppingLawCapUpperBound.lean`);
`exists_exactFiniteDeadlineTimingNash` and
`mixedNash_isQuittingFiniteDeadlineNash`
(`UniformEquilibrium/Quitting/Terminal/FiniteDeadlineNashExistence.lean`);
and `quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors`
(`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`).
The last theorem supplies the counterexample-to-positive-terminal-gap
boundary and the eventual target-free consumer, not the missing selector.

## Bounded adversarial check: whole core-owner maximum principle

Reviewed source: `notes/CODEX_EMMY_BOX__SINGLE_OWNER_COMPACTIFICATION.md`,
frozen SHA-256
`bbee639e29cbdaa5bd07b9f846a7a1eb920894396327f9006ea54ce33bf6eef9`.
Scope: Sections14.4–14.6, with only their stated dependencies in
Sections3,11,14.1 and14.3. This is one bounded ordinary-mathematics
check, not a Lean check, export gate or audit of later padding claims.

Verdict: PASS within the stated THREE-CORE-OWNER scope. I found no
mathematical objection to the entire-correspondence conclusion for
fixed0<e<min(1/10,e0) and every0<delta<1/2. The qualitative e0 invokes
only Solan2001's bounded ACTUAL no-exact-Nash consequence. No numerical
e0, fourth-owner exclusion or failure of uniform equilibrium follows.

### Claim and essential source hypotheses

The raw three-player table has singleton rows(1,3,0),(0,1,3),(3,0,1),
the three pair rows printed in Section14, grand0 and Never0. Only one
owner is constrained to the full compact survival-budget set
K_delta={p:S_p(t)<=c^t for every finite t}, c=1-delta; no conditional
hazard floor is silently imposed. Every nonowner retains its complete
independent clock-law response class, including Never. The claim is
that every constrained Nash point has geometric owner law and the unique
stationary nonowner response laws, so its full owner loss tends to2/5.
The canonical subtraction from recipient columns1,2 is checked on the
proper-source face, not asserted as global affine invariance of Never.

The hypotheses doing real work are exact nonowner best replies, the
owner's optimal private running-record envelope, same-correspondence
re-rooting at strict records, and absence of an actual full Nash profile
at this small-e table. Compactness alone would neither force the owner
clock geometric nor bound moving record gaps.

### Properness, local support cases and monotonicity

I reconstructed all three sure-hazard exclusions. At a reached date
the budget-compatible minimum owner hazard is at most delta because
S0(t)<=c^t. Accelerating the owner to sure Quit is always legal, and
reducing a sure hazard by a sufficiently small positive amount with a
later finite residual is legal. The corresponding strict root comparisons
exclude a sure owner, a sure player1 and a sure player2; the final gain
1+e-h*(2+e) stays positive for h<=delta<1/2. Thus all finite joint
survivals are positive. This justifies actual suffix deviations, not
unreachable-history perfection.

A proper unbounded nonowner supports arbitrarily late optimal dates;
its proper owner-opponent makes their payoffs converge to Never. An
improper nonowner directly supports Never. Hence Never is a full best
reply for both. If player1 were improper, its residual finite mass tends
to0 and player2's raw Never value tends to0, contradicting its immediate
Quit floor tending to at least1. If player2 were improper, player1's raw
Never value tends to3, strictly above its Quit ceiling1+e; all late
player1 hazards would vanish, contradicting its proper unbounded law.
These arguments cover arbitrary nonstationary laws.

In the two-stage zero-owner lemma I checked the y>0, y=0<x, and x=y=0
cases separately, including vanishing NEXT nonowner hazards. For y>0,
current support forces x<=1/4 and Y2'=(1-4x)/(1-x); both next hazards
must be positive. For y=0<x, the x'=0 case is directly negative, while
x'>0 gives the stated exact y' and upper bound for x'. The x>1/4
subcase uses the strict crude bound and does not incorrectly invoke the
nonnegative B regime. For x=y=0, the x'=0 equality case is exactly
y'=0. The derivative comparison for F(b) holds throughout[0,b]
because feasibility at b and monotonicity of z keep0<=z<=1 there.
I independently expanded F(0); it is precisely equation(14.10).

The weak-record restriction on every positive owner atom is justified
by equality in the private quantile envelope. Choosing the LAST active
nonowner date in a zero-owner run is legitimate because the run ends
at a finite next positive owner atom. Completely quiet intervening dates
identify the conditional values without pretending to preserve the Nash
profile under calendar deletion. The local lemma would make that next
positive owner's deadline worse than an earlier one, a contradiction.
This proves the zero-hazard lemma and monotonicity of the ENTIRE f(t),
including the positive date preceding a quiet run. Strict increases bind
the next survival budget, giving h(t)<=delta at every nonflat step.

### Infinite-calendar attainment is valid here

The whole correspondence is compact by the previously checked producer.
ALL its clocks are proper by Section14.4. The clopen finite-tail functions
decrease pointwise to0 on that compact set, so properness is uniform;
this does not assume that arbitrary weak limits of proper laws are proper.
Uniform opponent censoring makes full owner caps continuous. A finite
first cap maximizer would be a reached strict-record tail with exact full
Nash, contrary to the bounded actual Solan consequence. Hence each source
has a later strict record and the open finite-date improvement sets cover
the compact correspondence. A finite subcover gives J_delta.

Same-correspondence strict-record re-rooting repeats this bound after
every record. Every calendar date is therefore an offset at most J_delta
from a record tail belonging to the SAME correspondence. Finite-offset
hazards have positive survival denominators and are continuous on compact
N; conditional Never values are continuous by the same uniform censoring.
Thus the asserted H,X,Y,q calendar maxima really are attained. A remote
nonattained maximum or a nonrecord-tail compactification is not being
substituted. The bound is delta-dependent; no useful uniform window
estimate is inferred from it.

### The six maximum-principle inequalities

1. At an attained Q=q>1, x>0 and y<e*x/(1+e*x).
   Using Q'<=q gives C-q<y*(2-x)-x<0 for e<=1/2,
   contradicting monotonicity. Hence Q<=1 and x>0 implies y>0.

2. If Y2>1+e*H, support forces y=x=0, then its recursion propagates
   that strict inequality forever. Proper owner survival tends to0,
   contradicting bounded Y2. This argument needs no stationary tail.

3. At x=X>0, support and the next floor yield
   X/(1-X)<=((1+e)*h+(1-h)*X)/(3-2*h).
   The ratio increases in h with derivative numerator3*(1+e)-X.
   The stated quadratic and X<=(1+e)*H/2 follow exactly.

4. An attaining H>delta is flat. Its x cannot vanish, and its positive
   x,y support gives(14.19). Flatness gives Q>=O and the stated upper
   y bound. If H>=1/2 the coarse lower bound25/42 exceeds11/21;
   hence the hypothetical H lies in(0,1/2).

5. On an x=0 run, Y2(t)=A*Y2(u) and its floor give
   A>=1/(1+e*H). Player1's pre-u reward is at most3 on owner stopping
   and0 on player2 stopping, so Mbar is a valid upper bound. Combining
   the current floor with the recursion gives the stated z-ratio.
   Moving the Y-dependent part of E to the left yields exactly(14.20);
   dropping Y*E is in the safe direction.

6. At the hypothetical flat maximum, y>=(9/5)*H, x<=(3/5)*H,
   Y<=(16/5)*H and Q'>=1-Y imply
   C-Q>=H*[77/50+(1197/250)*H]>0. Bounding the negative bracket
   separately is valid even when the crude Y-bound exceeds1. I
   recomputed the final coefficients. This contradicts flatness.

Therefore every calendar hazard is at most delta. The initial budget
forces the date-zero hazard at least delta; equality of survival products
with their global upper bounds then forces EVERY date hazard to equal
delta. The wording about a "root hazard" should be read as date zero of
a source profile, not as a presupposed conditional hazard floor at every
date. The subsequent survival-product argument is correct without that
stronger premise.

I also recomputed the exact decoupled response maps and their two fixed-
point quadratics in Section14.1. Their monotone-orbit argument determines
the entire unrestricted response correspondence to the geometric owner.
The limits x/delta->1/2,y/delta->2, B->12/5,Q->1,U0->2 give full
loss2/5. The canonical core-owner transport retains a distinct proper
opponent under every full owner deviation, so both cap and payoff shift
by the same constant. Raw cyclic symmetry then covers all THREE core
owners, not a fourth padded owner.

### Significance boundary

This is a genuine whole-source falsifier for the THREE-PLAYER core-owner
selection, including every auxiliary component, not a bad selected branch.
It is not a four-player UE counterexample or exclusion of the all-owner
Fin4 source. A separately specified fourth-owner padding can supply good
components; its objective and proper-source transport must be checked on
its own. No unresolved mathematical objection was found in the bounded
core theorem above.
