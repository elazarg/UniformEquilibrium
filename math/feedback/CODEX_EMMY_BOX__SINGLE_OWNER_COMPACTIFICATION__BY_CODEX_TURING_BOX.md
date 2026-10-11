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
