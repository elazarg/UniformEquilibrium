# Adversarial review of the diffuse-flow unequal-premium theorem

Reviewer: CODEX_COLLAR_ADVERSARY. **Mathematical verdict: PASS. Export-gate verdict: PASS.** No unresolved
mathematical objection remains. The review independently checks the full
raw-table producer, unrestricted behavioral consumer, boundary parameters,
and stated coverage comparisons. No other review of this candidate was read.
This is ordinary mathematical review, not Lean verification.

Reviewed byte artifact: `/tmp/FIN4_DIFFUSE_THREE_FLOW_CANDIDATE.md`, for promotion as
`math/exports/THREE_DIFFUSE_FLOWS_UNEQUAL_PREMIUM_UNIFORM_EQUILIBRIUM.md`.
Exact SHA256:
    6bea1cfd33408258ac51ef966cd72f7886448fc37ce6049c442138a139f989e8

## Exact accepted claim

One positive beta threshold works on every compact subset of
    0<=a<3, 0<c<=1,
    Delta(a,c)=21c-6+8a(19c+1)>=0.

For the specified singleton matrix, seven passive entries, nine core
participant entries, and row0 upper bounds, every smaller positive beta
gives a uniform-equilibrium payoff against all unilateral behavioral
replacements. All unlisted nonsingleton coordinates and all own levels
are arbitrary finite data. The beta threshold is independent of those free
coordinates; the flow mesh and horizon threshold may depend on them.

This includes one common threshold on 0<=a<=2, 2/7<=c<=1, and covers the
previously unresolved direction (a,c)=(1/10,1). The theorem does not assert
a threshold on the whole noncompact region, arbitrary-table closure or exact Nash.

## Parametric graph: the main analytic audit

The local inverse of I_beta exists uniformly because G is invertible.
The cap-map derivative is beta N(Id+beta N)^(-1). Its distinguished negative
eigenvalue is simple and uniformly separated on each parameter compact, including
a=0, where the other eigenvalues are zero and positive. The proof never
inverts the tangent block: it uses only its norm O(beta), while the normal
multiplier is comparable to beta. Thus the zero tangent eigenvalue causes
no singularity, and the stated plane remains nonvertical.

The holomorphic graph transform is valid on a sufficiently small fixed
polydisc. In the norm |h(s)|/|s| squared, its three difference terms are
respectively O(radius), O(beta), and O(beta radius squared). Cauchy estimates
apply at the contracted arguments, inside a smaller polydisc. The nonlinear
maps have the common beta factor, and the composition h(beta psi) has a
beta-squared factor, so the apparent singularity at beta=0 is removable.
Uniform contraction gives joint parameter holomorphy and the uniform
spatial C2 and parameter-derivative bounds used later. No comparison of
the negative eigenvalue's modulus with the positive block is needed.

At c=1, the exact line u=0,t=v is invariant. The graph iteration preserves
zero normal coordinate on it, proving T_beta(0,v)=v. Parameter regularity
then gives the stronger remainder O((1-c)v squared), not merely O(v squared).
Combining it with the exact critical-axis formula proves physicality
uniformly through c=1, including arbitrarily small u/v. The u derivative has
a uniform positive margin because a stays below 3 on the chosen compact.
The hazards are nonnegative and the graph output contracts by C beta.
At a=0,c=1 the later wash becomes the permitted solo1 axis.

The total core hazard O(u+v) controls cumulative passive0 change, preserves
positivity and every quiet0 guard. The uniform geometric tail bound proves
continuity of the produced axis limit.

## Joined return, gluing and exact certificates

The raw identity p(-1/8)=Delta/64 gives r>=1/8, hence 8k+9l>=6.
The general three-flow formulas are exact with alpha*v=0. When alpha=0
the third flow is omitted and v may be positive; when alpha>0 its owner's
input cap is zero. Every flow segment is nonnegative.

The exact positive-beta factorizations show that choosing
y=max(yzero,yseam) enforces v>=0,alpha>=0,alpha*v=0, with no approximate
complementarity. I reproduced both factorizations, including the pair
chart's subtraction 3 beta sigma from the seam numerator at z=0.
The inactive2 guard there is exactly beta sigma, including sigma=0.

The direct and diffuse return arms join at the isolated cubic root z_star.
Their derivatives satisfy w_direct'<1<w_diffuse'. Thus d=w-z parameterizes
one continuous joined arc, and the return residual has strictly negative
z derivative at fixed d on both branches. The branches agree at the maximum
switch. Their common local derivative bound gives strict monotonicity
through that switch, without assuming differentiability there. The moving
z=0 endpoint is transverse; its derivative sign keeps the retained curve
physical. The other endpoint stays in the diffuse chart. The pair-sigma
segment attaches at the same z=0 root by uniqueness.

The axis function has a uniformly convergent holomorphic series on a
complex neighborhood, giving the C1 convergence needed for this gluing.
Off the graph, the return residual explicitly replaces coordinate2 by
T_beta before evaluating the axis. This is an auxiliary projection, which
equals the actual macro output only at the graph-entry zero. No fictitious
continuation is executed. The opposite entry signs follow from 8k+9l>=6
and the exact endpoint inequalities, so IVT supplies both equations.

Independent exact arithmetic reproduced the seam and return identities,
corner factorization, all derivative Bernstein bounds, root-isolation signs,
w_L and the two endpoint inequalities. The calculations used the printed
formulas, not an author's checker or numerical trajectory. The macro0
guard has a uniform gap: 257/500<3/5, with an even larger diffuse-arm margin.
All estimates persist uniformly on each compact raw parameter subset.

## Complete reward-query census

At a core root, player0 never quits. Its prescribed payoff uses its four
specified passive core entries; its own possible deviation uses its six
bounded proper participant entries and grand reward. A core player's
prescribed payoff and own deviation use its three specified participant
entries, singleton entries and single specified passive pair.

At a solo arc, a deviator can add only itself. Its pair reward with the solo
owner enters only the mesh constant. Other free coordinates are unqueried
in that player's prescribed or unilateral payoff. This verifies the query
census and independence of beta0 from all free reward magnitudes.

## Finite meshes and unrestricted deviations

Subdividing a singleton arc preserves survival and the prescribed endpoint.
The active owner's annotation stays zero. An inactive native Quit payoff is
its pair reward times one mesh hazard, with excess bounded by eta_n tending
to zero; the Continue equation remains exact.

A deviator quits at most once while the game is live, so eta_n is charged
once. Equivalently, adding eta_n to every annotation gives a response
supersolution at every nonseam row, pricing arbitrary stopping laws and Never.

The single empty seam has policy and Continue error at most E_N. In every
period the opponents of player0 absorb with probability at least R>=x;
every other deviator faces owner0's aggregate hazard x. These bounds are
unchanged by the deviator's entire law. Thus the expected number of seam
visits is at most 1/x, and the stated estimates follow:

    payoff error <= E_N/x,
    full terminal exploitability <= eta_n+2E_N/x.

All surviving remainders vanish by geometric opponent absorption.
The return datum and target ell+V precede the choices of N and mesh.
Expected pre-absorption time is bounded by period length divided by x
uniformly over deviations, giving the uniform finite-horizon approximation.
Every unilateral replacement absorbs almost surely, so signed own levels
are added exactly; literal Never payoffs are never translated.

In particular, the zero player3 cap violates an exact solo0 guard, but its
finite-mesh error is charged once. No exact finite-mesh equilibrium is assumed.

## Coverage audit and export gate

The calibration specifies all sixty rewards. The displayed hard direction
has a positive beta below both the produced threshold and 1/2000; no
unproved numerical threshold is needed. It fails the quantitative
relative-premium, signed-chamber, pair-contraction, equal-premium,
cone-ratio and closed-wedge tests for the explicit reasons given.
The signed-chamber role census leaves only the identity embedding.
The row-scaling calculation is valid: the relevant small-premium constants
depend on normalized rows1,3 and the scaling of row2, not on row0 scaling.

I checked the complete stationary and sure-owner support arguments,
including the stationary separating bounds and the arbitrary feasible
punishment-tail lower bound. The protected-set and nonnegative-weight
arguments quantify over all choices in the stated criteria. The child
table exhausts all fourteen proper nonempty children: its exact profiles
are Nash against complete laws, while the remaining child's subdivided
cycle has vanishing full debt and a fixed positive outsider gap. The
outsider gap for child123 was reproduced symbolically; the child023
Bellman cycle and terminal singleton probabilities were checked directly.

Exact rational matrix checks reproduced the principal minors, offset-one
support census, inverse-triple obstruction and all thirteen nontrivial
multi-block quotient determinants. The remaining one-block row sums
also exclude positive row-rescaled identification. These comparisons
exclude the named selectors, not every conceivable certificate language.

The construction adds a previously surviving existence class with an actual
raw-table adapter, produced invariant graph and macro return, and complete
behavioral consumer. No strategic root, continuation, favorable child, cycle,
period, invariant set or response selection remains an unproduced hypothesis.
This meets the export gate and narrows the possible counterexample class.

The packet is self-contained. Tracked Lean terminal, flow, supersolution and
classification interfaces match their uses. No Lean commands ran; the producer
remains ordinary mathematics, and Fin4 remains open.
