# Independent adversarial review of the finite vertex criterion

Reviewer: LARGE_ROOT_SUCCESSOR. I did not contribute to this positive proof.
Ordinary mathematical review; no Lean file was edited or built.

Reviewed artifact: math/notes/CODEX_COORDINATOR__FINITE_VERTEX_CAP_ROOT_CRITERION.md.
SHA256: 29b3fc26ea5bbc2d488b1d9b34ced4ee3e825b1ea76197a81c6ad26ea2fea635.

Verdict: PASS for the complete mathematical theorem as stated. No unresolved
mathematical objection remains. The raw criterion produces all strategic
objects needed for the native all-marginal-finite approximation and arbitrary
signed-offset uniform-equilibrium conclusion. This verdict does NOT establish
new coverage against earlier criteria or authorize export; the manuscript
correctly leaves that separate overlap question pending.

## General preconditioned vertex producer

This review covers the final generalization to any explicitly specified
invertible entrywise-nonnegative T. No equality T=L^{-1} is used in the main
root argument, and L need not be assumed invertible. I checked the replacement
step directly, rather than transferring approval from the older specialization.

C is multiaffine because all its monomials are squarefree; hence
G(x)=x-T C(x) is multiaffine as well, regardless of coefficient signs.
The stated product-box interpolation weights are nonnegative and sum to one.
Thus the two vertex inequalities hold throughout the box. For 0<=v<=H,
entrywise nonnegativity of T gives 0<=Tv<=TH, so
F_v(x)=G(x)+Tv maps the nonempty compact convex box into itself. Brouwer gives
x=F_v(x), and invertibility of T gives C(x)=v. Since C(0)=0, any nonzero v
forces x nonzero. Positive finite xbar makes all resulting hazards proper;
nonzero x makes joint survival strictly less than one. Vanishing coordinates
of x are allowed and cause no support gap in the proof.

The offer identity is correct for native own-singleton zero. Q_i-P_i is the
opponent-product average of joining increments, with zero empty-coalition
coefficient. Dividing by positive opponent survival gives C_i(x). Equality
C_i(x)=v_i makes every player indifferent, including every inactive player,
and therefore supplies a full Nash root. No root or strategic continuation
witness was assumed as part of the vertex criterion.

For fixed xbar and raw rewards, both sides of the vertex inequalities are
affine in T; checking invertibility is correctly left as a separate finite
algebraic condition. The specialization T=L^{-1}>=0 reduces exactly to the
older G=A R calculation. The generalization does not alter any source or
consumer hypothesis downstream.

## All-marginal-finite carrier

The carrier's generating class is nonempty and every terminal payoff and full
response cap lies between finite raw reward bounds and zero. In particular
B_i<=H_i. Closing this bounded set in finite-dimensional (U,B) space is compact;
no assertion that a closure point itself is an actual law is made.

Prefixing a fixed independent root to an actual all-marginal-finite profile
retains that property for EVERY player, including a player with zero or sure
root hazard. The displayed full-cap recursion is continuous and therefore
preserves the closure as well. Direct subtraction gives exactly
 d'_i=c d_i+R_i^root,
with the stated nonnegative normal-form regret. The cap maximizes Quit now
against Continue followed by a complete optimal-response supremum, so it
covers Never and arbitrary behavioral replacement, not only prescribed tails.

The observer-exact slice C_p is genuinely produced. Fixing p to quit at date0
reduces every observer's complete response menu to Quit at0 or Continue at0.
A mixed Nash equilibrium of the n-1 observer finite game prices both options.
Giving each continuing observer the complete clock value1 makes every marginal
law finite, without changing any observer comparison against p's sure date0.
The pivot is unconstrained, as required. Thus C_p is nonempty before taking
its minimum; no unsupported partial-equilibrium existence is assumed.

## Global-minimum descent

Assuming a positive minimum g of total debt gives m>=g>0 on compact C_p.
For an observer-Nash root the observer debts remain zero and the pivot debt
recursion implies m(1-c)<=R_p. At continuation B-a e_p with 0<=a<m, finite
Nash existence is valid for arbitrary signed continuation data. I checked
all three pivot-hazard cases: q_p=0 gives regret0 at B; an interior q_p gives
exactly a q_p h_p; q_p=1 gives at most a h_p. Thus
 m(1-h_p)<=(a-m)q_p h_p.
Nonnegative left side and strictly negative coefficient a-m force h_p=1,
then q_p=0. Every opponent also has zero hazard. AllContinue being Nash at
the shifted continuation proves B_observers>=0 and B_p>=a. Taking a up to m
therefore proves B>=0 with B_p>=m>0, without realizing the minimizing pair.

The raw producer applies because this B is nonzero and B<=H. Its full Nash
root has all regrets zero and c<1, so the prefixed pair is in C_p with pivot
debt c m<m. This is an exact contradiction, not merely an asymptotic descent.
It establishes zero minimum total native debt on the same strengthened carrier.
Approximation by its defining actual profiles therefore yields the claimed
all-marginal-finite profiles at every error.

## Signed offsets, full deviations, and fixed target

For n>=2, under every unilateral replacement at least one prescribed opponent
still has a finite clock almost surely. The terminal coalition is therefore
nonempty almost surely for BOTH prescribed play and each response. Recipient
row offsets consequently add exactly kappa_i, including negative offsets;
positive scales commute with the response supremum. The identity
 d_i^r=sigma_i d_i^Z
is exact. Joint absorption alone would not suffice, but the produced stronger
marginal property supplies the needed opponent absorption.

A bounded terminal-payoff sequence has a subsequential target u_* fixed before
accuracy. For a fixed chosen profile, absorption under any deviation occurs
no later than the first opposing finite clock. The displayed Cesaro-versus-
terminal bound with T_-i is therefore uniform over all deviations. Dominated
convergence applies to that fixed, almost surely finite opposing clock even
without an integrable expected time. Taking the maximum of finitely many
player thresholds gives one profile working for all sufficiently large horizons.
The triangle inequalities for target error and regret can use arbitrarily small
fractions of the requested error, since native error was arbitrary.

The theorem requires finite clocks almost surely, not finitely supported
calendars. Its direct dominated-convergence argument needs no omitted calendar
truncation. No finite-support strengthening is assumed in this review.

## Adapters and source audit

For nonpositive higher joining increments, R and A R have nonnegative
coefficients. The raw supersolution C(xbar)>=H implies the top vertex bound,
which then bounds every smaller vertex. The option xbar=2AH is valid whenever
strictly positive and R(2AH)<=H. For the one-positive-per-row permutation
adapter, L=(D-N)P is the correct factorization. A positive y=P xbar with
D^{-1}N y<y gives a weighted max-norm contraction and the displayed nonnegative
Neumann inverse. Hence inverse nonnegativity is produced from the strict raw
inequalities, not an extra unverified hypothesis of that adapter. The canonical
calculation at xbar=2*1 gives (2M-122,2M-124,2M-126,2M-124), and M>125 is
exactly sufficient against H=(M-1)*1. I checked that arithmetic independently.

I inspected exists_isZeroQuittingRootNash in
UniformEquilibrium/Quitting/Root/NashExistence.lean, the exact diagonal-prefix
and continuity interfaces in UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean,
and the full response recursion in UniformEquilibrium/Quitting/Root/TerminalDebtPrefix.lean.
The named fixed-target endpoint is in
UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean.
These are existing interfaces, not formalization of this new argument.
The separate question whether an older stationary or other raw producer
already covers every passing table remains unresolved by this review.

## Final-artifact check

I reread the complete canonical proof. Beyond the general T root producer,
its all-marginal-finite carrier, exact global-minimum argument, signed-offset
identity, and fixed-target uniform-horizon consumer are unchanged and valid.
Its status correctly separates a complete existence theorem from unresolved
coverage beyond existing criteria. Numerical stationary controls are not
presented as certified frontier separators. This verdict is for the exact
canonical bytes pinned above, not only for individual components.
