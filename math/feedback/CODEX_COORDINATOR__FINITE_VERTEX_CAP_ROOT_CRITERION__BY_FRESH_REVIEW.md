# Independent whole review of the canonical finite-vertex criterion

Reviewer: I2_ACTIVATION. I did not author or contribute to this proof.
Reviewed artifact: math/notes/CODEX_COORDINATOR__FINITE_VERTEX_CAP_ROOT_CRITERION.md.
SHA256: 29b3fc26ea5bbc2d488b1d9b34ced4ee3e825b1ea76197a81c6ad26ea2fea635.

**Verdict: PASS for the complete mathematical theorem as stated.** No
unresolved mathematical objection was found. This is not export admission:
new coverage and overlap with previous stationary/raw existence criteria
remain unresolved in the artifact and were not supplied by this review.

## Raw criterion and root production

I checked the generalized certificate with an arbitrary explicitly specified
invertible entrywise nonnegative T. The vector G(x)=x-T C(x) is multiaffine;
linear mixing introduces no repeated-variable monomials. The stated corner
weights are nonnegative and sum to one, so both vertex bounds hold throughout
the box. Since 0<=Tv<=TH for 0<=v<=H, F_v(x)=Tv+G(x) is a continuous
self-map of that box. Brouwer gives x with T[C(x)-v]=0, and invertibility
of T gives C(x)=v. Because C(0)=0, a nonzero v excludes x=0. No L inverse
is used or silently assumed in this generalized argument.

Finite positive xbar makes every q=x/(1+x) proper even when some coordinates
vanish. The exact joining identity gives indifference for EVERY player,
including those with zero hazard. Thus the full nontrivial Nash root is
produced for every required cap. The raw vertex inequalities are linear in T
when the rewards and xbar are fixed; its invertibility remains a separate
explicit test, as stated. I compared the canonical artifact with the earlier
reviewed version and reread the entire consumer: the carrier, shifted-pivot
minimum, signed-offset, and horizon arguments remain unchanged.

The specialization T=A=L^-1 gives G=AR exactly. Its monotone adapter
follows by multiplying C(xbar)>=H by A and using coefficientwise
monotonicity of R. The option xbar=2AH is valid under
its stated strict positivity and R(2AH)<=H. For the cyclic adapter, the
factorization L=(D-N)P has N>=0, and Lxbar>0 gives a strict weighted-row
bound on D^-1N. Its Neumann series has nonnegative entries, proving the
required inverse sign. I recalculated the canonical xbar=2 values: the
minimum coordinate is 2M-126, while H=M-1, so strict acceptance is M>125.
This confirms nonemptiness, not new coverage.

## Carrier and positive-minimum contradiction

The all-marginal-finite carrier is compact as a finite-dimensional closure
of bounded tuples. Every actual prescribed payoff and every unilateral
replacement payoff is bounded by the finite reward range. In particular
B_i<=H_i. Every debt is nonnegative and the property passes to the closure.
Fixed root prefixing preserves this carrier because each prefixed marginal
remains almost surely finite. The explicit max/affine map is continuous,
so no realization of the minimizing closure point is used.

The nonempty observer-exact slice is correctly constructed: force the pivot
to quit at date0 and choose an ordinary finite-game Nash equilibrium among
the other players. Prescribing date1 quit to any observer who Continues
makes every marginal law finite. Against any one observer's deviation the
pivot still quits at date0, so its entire behavioral response menu reduces
to the two priced endpoint actions. The pivot debt may be nonzero, as
allowed by the slice.

I verified the exact debt recursion, including roots with sure quitters.
For a full Nash root at B-a e_p, observers have zero root regret at B.
At the pivot the regret bound a q_p h_p holds in all three cases q_p=0,
0<q_p<1, and q_p=1. Global slice minimality then gives exactly

 m(1-h_p)+(m-a)q_p h_p<=0.

For 0<=a<m, both terms are nonnegative. Hence h_p=1 and q_p=0, which means
all players Continue. Its Nash conditions imply B_i>=0 for observers and
B_p>=a. Letting a approach m proves B_p>=m>0. No genericity, positive
singleton inverse column, local tail minimality, or unconstrained source
replacement was inserted into this argument.

At that same global minimum, the produced nontrivial full Nash root has
all root regrets zero and joint survival c<1. It preserves the observer-
exact slice and replaces pivot debt m by cm<m. This is a strict global
contradiction. Therefore actual all-marginal-finite profiles have total
native debt arbitrarily close to zero. No recurrence, finite calendar,
strategic continuation, or successful selector is left as an unproduced
input.

## Full behavioral, signed-offset, and uniform-target endpoint

The distinction between joint absorption and all marginals finite is used
correctly. For n>=2, after any unilateral replacement there is a prescribed
opponent with almost surely finite quitting time. Thus absorption remains
almost sure under every response. Every terminal outcome gets the same
recipient offset kappa_i, so d_i^r=sigma_i d_i^Z exactly even for negative
offsets. This reasoning would fail for n=1, which is expressly excluded.

Fixing private randomness turns a complete behavioral deviation into a
quitting deadline or Never along the unique live history. The opponent
clock laws are unaffected by that choice. Consequently the absorption time
is bounded by T_-i, uniformly over all such responses. The displayed
2R E[min(T_-i+1,H)/H] bound therefore controls the terminal-to-Cesaro error
uniformly over the complete unilateral menu, and it tends to zero by
dominated convergence. No uniform integrability or finite mean quitting
time is needed.

The compact payoff subsequence fixes u_* before accuracy. For any accuracy,
select one profile having small terminal debt and payoff close to u_*, then
choose a horizon threshold using its fixed opponent laws. The same profile
works for every larger horizon and every behavioral deviation. All target,
profile, and horizon quantifiers are in the required order.

## Source inspection, attempted falsification, and admission limit

I inspected exists_isZeroQuittingRootNash in
UniformEquilibrium/Quitting/Root/NashExistence.lean; arbitrary signed
continuations are allowed. I also checked the diagonal prefix bridge in
UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean and the full
response recursion quittingContinuationBestResponseValue_rootThenContinuation_eq_max
in UniformEquilibrium/Quitting/Root/TerminalDebtPrefix.lean. No Lean build
or new formalization claim is made.

Attempted objections included singular or sign-indefinite L under the new
certificate, zero coordinates in H and x, nonrealization of the minimum,
sure roots in the shifted-cap argument, signed offsets under Never deviations,
and heavy-tailed prescribed clocks. Each is handled by
the stated argument. For n=2, the test reduces to positive reciprocal
joining increments, consistent with the elementary absorbing both-Quit
profile; this is a sanity check rather than a separating example.

The existing CYCLIC_JOINING_CAP_REGION note already contains the monotone
supersolution map for a positive cap region. The new artifact applies a
whole-reward-box condition and an all-marginal-finite minimum argument.
Whether its raw class is already absorbed by a previous UE or stationary
producer requires a separate complete overlap audit. I found no proof here
that the vertex condition forces stationarity, and I did not establish a
separating raw table. The positive theorem is mathematically sound, but
its export coverage gate remains open.

The canonical opening carefully treats the numerical stationary controls as
uncertified coverage separators. I did not independently reproduce those
numerical searches; they are not used anywhere in the mathematical proof.
The final-artifact PASS is for the complete stated UE criterion, not an
assertion that it closes a previously surviving reward-table class.
