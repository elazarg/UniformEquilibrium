# Bounded review: sole-owner guard, boundary examples, and discounted scope

## Verdict and reviewed bytes

**PASS in the stated bounded scope. No unresolved objection.**

Reviewed packet:
`formalized/STATIONARY_RESPONSE_QUOTIENT_DEGREE_ESCAPE.md`.
Final SHA-256:
`49f0efacc29a683d421c82180f4781376a43a36e6c824f2468a8856af71136ac`.

The review checked the definitions needed for the optional negative
sole-owner exclusion (SG), its complete behavioral and uniform-payoff
consequences, the negative-owner and canonical-table boundary examples,
and the discounted scope. The added discounted-owner paragraph was
spot-checked at these final bytes. This is not a repeated review of the
core degree construction or its algebraic root/Jacobian computations.

## Exact scope of the optional guard

For q=h e_i, 0<h<=1, the owner has alpha_i=1 and Delta_i=0. Every
outsider j has alpha_j=1-h and

    Delta_j=h[(1-h)s_j+h r_j({i,j})-r_j({i})].

The inactive-player fixed-point condition Delta_j<=0 is therefore
exactly (SG). The sole-owner profile is block-constant exactly when i
belongs to a singleton block. Consequently infeasibility of (SG) for
every negative singleton-block owner excludes precisely the produced
sole-owner roots whose own Never deviation defeats terminal Nash.

Every remaining nonzero root has either two positive original hazards,
so every opponent-deleted clock contracts, or a nonnegative sole owner.
These are exactly the cases covered by the displayed complete-cap proof.
The guard is a finite raw-table condition; it supplies no assumed
equilibrium, continuation value, or response strategy. If it fails, a
bad root is permitted, not necessarily the absence of every good root.

The tracked boundary matches this reasoning:
`IsQuittingStationaryBoundaryAdmissible` and
`isZeroAsymptoticNash_stationary_iff_endpointNash_and_boundary`
in `UniformEquilibrium/Quitting/Stationary/EndpointCompiler.lean`
require max(0,s_i)<=v_i when every opponent surely Continues.
The exact declarations were read and the source path was verified as
tracked. No Lean compilation was performed for this bounded review.

## Boundary examples and interpretation

For the two-player negative-owner table in Section 8.1, the root
q*=(0,1/4) has payoff (1/2,-1/2), but the sole owner's Never response
pays zero. For q^t=(t,1/4), t>0, direct expectation gives that same
payoff; the caps are 1/2 and -1/2+3t/2. Thus E(q^t)=3t/2 whereas
E(q*)=1/2. The punishment-value argument correctly uses an infimum,
not attainment. The guard for owner 1 is 1/2>=1-2h, feasible for
h>=1/4, and therefore correctly does not certify every root as exact.

The canonical-table example in Section 7.4 does not silently preserve
the game under a terminal-only shift. Subtracting b_i from every
nonempty terminal reward changes Q_i by -b_i and H_i by
-(1-alpha_i)b_i, so Delta_i is unchanged. The same three-active-player
root still has contracting deleted clocks. Its prescribed payoff and
complete cap therefore shift by -b_i, proving exactness again in the
new literal game. All nonempty membership-toggle differences remain
unchanged; the pivot still defeats all-Never. The subsequent positive
scaling and the advertised bound of four are consistent with the table.

The full-dimensional persistence claim has the correct strategic
consumer: three interior active hazards and a strict inactive residual
retain opponent-deleted contraction, hence exact terminal Nash and a
same-profile uniform payoff after the stated local root construction.
This does not claim that the response-invariant identity itself is open
under arbitrary reward perturbations.

## Discounted and finite-horizon conclusions

When alpha_i<1, any complete response absorbs by the first opponent
quit time L_i, with E[L_i+1]=1/(1-alpha_i). The inequalities for the
finite-average and normalized discounted weights give, uniformly over
all responses, regret bounds

    2M/[H(1-alpha_i)],
    2M(1-d)/(1-alpha_i).

The final added paragraph correctly handles the remaining nonnegative
sole owner. Every discounted response pays at most s_i. Under own
hazard h>0, its prescribed discounted payoff is

    s_i h d/[1-(1-h)d].

Its delivery shortfall is
s_i(1-d)/[1-(1-h)d]<=M(1-d)/h, which also bounds its regret.
Outsiders use the already proved contracting-clock estimate. The
same-profile discounted scope is therefore supported, including h=1
and s_i=0; it does not require a rate uniform over all possible roots.

The signed Fin4 conclusion remains ordinary uniform-payoff existence
through the stated same-table normality and punishment construction.
It has not been strengthened into unconditional exact stationary
equilibrium for every signed table in the quotient class.
