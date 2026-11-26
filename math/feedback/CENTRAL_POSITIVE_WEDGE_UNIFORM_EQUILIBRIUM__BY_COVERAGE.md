# Independent full review of the central positive-wedge producer

Reviewer: SINGLETON_CHAMBER_COVERAGE.

Artifact reviewed: [CENTRAL_POSITIVE_WEDGE_UNIFORM_EQUILIBRIUM](../exports/CENTRAL_POSITIVE_WEDGE_UNIFORM_EQUILIBRIUM.md), 862 lines,
SHA256 `afa63bbe45f0c5560123e7d92e0f3dca54488aef1ffe498a73bad297597d5a41`.

Verdict: PASS for the complete ordinary-mathematical theorem, its full
behavioral consumer, fixed-target quantifiers, and conjecture-facing export
gate. This is not a Lean compilation or formalization result. The verdict
applies to these exact bytes, not to a later changed proof.

## Claim checked

For the complete stated raw native family, there exist finite C>=100 and
beta0>0 such that every K>=C, 0<=p<=beta0 K has a uniform-equilibrium payoff.
The seven row0 upper bounds,21 free joining entries and arbitrary original
own-singleton levels retain their stated scope. Constants need not be
computed and do not depend on those free entries. Neither arbitrary Fin4 nor
robustness under arbitrary changes of the other displayed coefficients is
claimed.

I read the complete artifact, including the newly inserted long-core lemma,
and independently checked its strategic and algebraic interfaces. I also
read the exact declarations
`quittingContinuationBestResponseValue_rootThenContinuation_eq_max`
(`UniformEquilibrium/Quitting/Root/TerminalDebtPrefix.lean`) and
`quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors`
(`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`).
Both files are tracked. The packet supplies its own mathematical consumer;
it does not infer new checked Lean facts from those declarations.

## Backward map, scaled limit, and physical core

The six displayed Q/F formulas agree with the raw table and independent
opponent-coalition enumeration. At alpha=0, setting u=w/(1-w) gives
Z=L-97u and Y=(101Z-100Z')/2. Substitution in the second equation gives
(4-9797beta/2)u=X-beta(101L-100Z')/2, exactly the printed analytic map.
The denominator remains nonzero for small beta. Its normal matrix in both
orders of (w,Y-Z/2) agrees with direct differentiation.

The zero fast eigenvalue at beta=0 does not require an inverse map. The
argument uses forward iterations of the backward interface map. A fixed
number of iterations brings the entire compact terminal section into a
uniform contracting tube. Summable center increments construct the invariant
projection; their differentiated recurrences give the stated finite smoothness.
The fiber change produces an exactly invariant center coordinate.

The terminal section is completely produced: at beta=0 its Z derivative
is (1-w)/(1+3w)>0, so the uniform implicit-function theorem selects the
stated Z_beta(J,theta). Keeping this Z,w fixed and changing only terminal
Y to its exact alpha-dependent formula gives the bounded O(alpha) section
variation used by the long-iterate proof.

The choice max(delta)<q<1, q^2<min(delta), max|kappa|<q^2 is possible near
beta=0. It gives a convergent leading-amplitude series and controls all
parameter derivatives by summable polynomial-times-geometric bounds.
Crucially t=delta(beta,J)^(N-1) uses the independent unknown J. This avoids
the unbounded derivative incurred by freezing the rate at a limiting J.

The alpha variation has stable normal forcing, despite O(N) center drift.
Its limiting normal response is independent of terminal phase. The Taylor
remainder O(alpha^2 poly(N)), after division by t and alpha=t Lambda,
tends to zero with its stated derivatives. At beta=0 the physical forcing
is -alpha J/4 under multiplier3/4, so the limiting shift is -alpha J.
This independently checks b_0(J)=J and the scaled entrance equation.

The aggregate estimate is also checked independently. The omitted
unperturbed tail has summable O(delta^n) hazard mass. Finite perturbations
have O(poly(n)alpha) errors per state, while the additional physical hazards
are O(alpha). Survival products remain uniformly bounded above and away
from zero near this orbit; their affine payoff derivatives are controlled
by those products. Telescoping over n roots therefore costs a polynomial
factor, not exponential growth. Parameter derivatives add polynomial factors.
This justifies the unscaled O(poly(n)t) entrance/aggregate estimate needed
by the outer equations and phase derivative.

The physical-sign proof addresses a substantive possible failure: the fast
eigenvalue is negative for beta>0, and pointwise continuity for fixed N
would not suffice. Estimate(11), split into finitely many terminal indices
and the uniformly controlled long tail, leaves a positive gap at every
index before the exact zero w_first. The fixed factor1-delta_max makes the
last positive root uniform. The fast recurrence and w_first=0 then give
Y_first-Z_first/2=O(alpha), which is exactly the precision needed by the
pair guard. Positivity of nonterminal Y,Z follows from the explicit beta=0
orbit, compact finite continuity, and the positive fixed line; terminal Y
has exactly terminal Z's sign. No negative hazard is used.

## Outer return and length coverage

The singular-limit aggregate equations retain the finite beta Y contribution
in row2 even though the corresponding physical hazard tends to zero. Omitting
that contribution would change the return; the packet keeps it correctly.
Multiplication by core survival removes terminal phase from both outer
returns. I independently recomputed their beta=0 root and Jacobian:

 J=3/4, T0=5/4,
 D_(J,T0)H=[[5/2,-45/14],[0,-10/7]], det=-25/7.

An exact symbolic calculation also reproduces J_*'=-183/160 and
T_*'=-57/64. The outer equations have O(poly(N)t) errors, so the selected
J_N has phase derivative of that order. Therefore its rate dependence adds
only an O(poly(N)t) term to the logarithmic phase derivative of K_N;
physical K_N is strictly decreasing for every sufficiently large N.

The endpoint equations have simple zeros at the stated distinct phases.
At the upper endpoint the last root is literally solo3. Deleting it sends
x_old=100w and E2_old=3w to the exact wash equality. Direct substitution
shows each outer return is multiplied by1-w. The shortened core has the
same first root, pair entrance, alpha and beta, and lies in the same compact
branch neighborhoods; uniqueness identifies the adjacent lower endpoint.
The new explicit rescaling check is correct: pi is invariant at alpha=0,
A(Tx)=delta A(x), the perturbed center parameter changes by O(alpha), and
Lambda_short/Lambda_long=delta+O(poly(N)t). Thus deletion really lands in
the unique neighboring branch's scaled neighborhood.
This is an exact overlap argument, not an asymptotic claim that intervals
are merely close. Compactness of beta supplies one finite lower threshold,
and the joined intervals cover the entire claimed unbounded wedge.

## Pair prefix and unrestricted consumer

The active pair recurrences telescope to the printed survival S_n. The
coalition masses follow from the two active payoff identities and total
probability; they have the printed analytic limit at beta=0. Player0's
four bilinear corners are correct and remain strictly positive.

I independently expanded player3's surplus recurrence. Its coefficient of
cd is exactly95+201/K+202/p+202/(pK). The first-ratio estimate uses the
O(alpha) near-line control and gives the stated positive numerator
alpha[2-beta(100+2B+C_z)-200alpha-2B C_z beta alpha]. The argument therefore
works uniformly when p=beta/alpha grows without bound. It does not silently
apply a bounded-p estimate. Later ratios decrease, so every finite word is
legal. The p=0 solo2 induction is handled separately and correctly.

Every strategic witness is produced: a finite triple core, exact wash,
limiting pair entrance, finite pair approximants, outer parameters and solo
subdivisions. The only interface residual is at the solo2 root leading into
the finite pair approximant. All other active and passive identities are
exact. The reference A is fixed before approximation accuracy.

The full-cap maximum prices every deadline and Never. Deleted-opponent
survival contracts by at least min(a,b), which remains positive for each
fixed game; this validates the e+2eta/rho debt bound over the repeated finite
calendar. Quit errors enter a maximum, not an accumulating sum. Proper
opponents make the native shift exactly kappa_i for every complete deviation.
The opponents-only absorption-time bound is uniform over deviations and
supplies the claimed single threshold for all larger finite horizons.

## Coverage and attempted falsification

I reran the exact standard-library rational checker for the p=1 uniform-K
ray: 80 stationary supports are excluded in862 nodes and65 sure-root patterns
in371 nodes. The monotonic-K relaxation keeps the factor(1-H1) for stationary
F1 and omits it for the root polynomial, correctly. The direct F2 exclusion,
sign-consistent inverse combinations, recomputed origin bounds and exact
Bernstein subdivision are sound. No unresolved box is accepted.

The p=1 ray lies in the new wedge for every sufficiently large K, regardless
of the uncomputed threshold. It is outside the previous fixed-K, negative-p
and outer-positive-cone conditions. I checked the stated full-selection
comparisons: ordered anchors/positive core weights, mixed-trap joining charge,
all passive-child choices, attached-pair labeling, all three pair partitions,
all signed inverse columns and the signed-cycle graph obstruction remain
valid along this ray. The packet does not claim that these form a complete
classification of every possible theorem.

The attempted falsifiers were: freezing the normal rate at limiting J;
using fixed-N positivity with a negative fast eigenvalue; ignoring the beta
term in the aggregate row2 identity; dividing an unscaled orbit error by t;
applying a bounded-p pair estimate to p proportional to K; approximate rather
than exact length gluing; and choosing the payoff target from each finite
pair approximation. The proof explicitly avoids all seven failures.

The packet is self-contained relative to its named tracked Lean interfaces,
contains the complete finite certificate rules and raw data, and has no
proof dependency on another conference artifact or temporary script. Its
increment is a new raw UE region with an actual producer and full behavioral
consumer. I found no unresolved mathematical objection to export promotion
of the reviewed bytes, subject to the required second independent full review.
