# Independent check of the positive-inverse jackpot producer

Reviewer: CODEX_NASH_BOX.

Reviewed source: `notes/CODEX_EMMY_BOX__POSITIVE_INVERSE_TRIPLE_JACKPOTS.md`,
SHA256 `1ae6ab3b39e88ff8b76d5de127caaf7996841337c65820d4652a6f2b1a63a49b`.
Scope: Sections 1--6 and both finite-player extensions in Section 10.
The unchanged explicit family and its bounded source comparisons are
covered by my earlier sparse-triple feedback; they are not re-audited here.
This is an independent ordinary mathematical falsification check, not
Lean implementation or a claim about arbitrary reward tables.

Verdict: PASS. No mathematical objection found under the literal strict
inverse-positivity, positive coefficient and bounded remainder hypotheses.
The proof produces roots of the exact finite-parameter field, without
requiring a nonsingular limiting root or a local matrix neighborhood.

## 1. Exact field, including its sign

Fix one recipient i. Its only unbounded coordinate is r_i(S_i), with
i in S_i. Put D_i=S_i minus i and d_i=|D_i|. With q=t z and
r_i(S_i)=a_i t^(-d_i)+c_i, its contribution to Q_i is exactly

    a_i product_(j in D_i) z_j product_(j notin S_i)(1-t z_j)
      +t^(d_i)c_i product_(j in D_i) z_j
                     product_(j notin S_i)(1-t z_j).

This is polynomial in t. No unbounded coordinate enters B_i: that sum
uses recipient i's rewards only on coalitions excluding i. Different
recipients' jackpots do not change this fact, even if the selected
coalitions coincide or contain other recipients.

At t=0, Q_i=s_i+a_i product_(j in D_i)z_j. The coefficient of t in B_i
is sum_(j!=i) z_j r_i({j}), and that in 1-alpha_i is sum_(j!=i)z_j.
Consequently H_i/t has exact constant term

    a_i (sum_(j!=i)z_j) product_(j in D_i)z_j - (Gamma z)_i.

Polynomial division therefore gives the stated exact signed correction
`Phi=diag(a)P-Gamma z+t E`. Multiplying by A=Gamma^(-1) shows that
`F_t=A[diag(a)P+t E]` is a fixed-point field with the CORRECT plus sign
on t E. Its zeros are equivalent to H=0 for every actual t>0.

## 2. Whole-shell positivity and endpoint exclusion

For n players, b=min A_ij>0 and B=max A_ij imply, for every nonzero
nonnegative w,

    (Aw)_i / sum_l(Aw)_l >= b/(nB).

Thus kappa=b/(2nB) gives the claimed strict directional margin on the
compact convex simplex K. This estimate holds for every shell point,
not only a selected eigenvector. Since n>=2, every P_i is positive on K.
The shell has z_i>=ell*kappa>0; hence every a_i P_i(z) has a positive
minimum there. The exact E is uniformly bounded over the whole shell,
the closed bounded reward cube and a small closed t-interval. Small t
therefore preserves positivity of its PREIMAGE vector before A is
applied. No unsigned bound on F alone is being substituted for this step.

In the equal-degree case, homogeneity gives total mass rho^(d+1)g(x).
The choices ell^d g_max<1/2 and u^d g_min>2 leave strict positive
boundary margins. In the mixed-degree case all d_i+1>=2, and all weights
A_ij a_j P_j(x) are positive. Therefore ell<1<u gives respectively

    sum_i F_0(ell*x)_i <= ell^2 g_max < ell/2,
    sum_i F_0(u*x)_i >= u^2 g_min > 2u.

These inequalities do not assume common homogeneity. Compact uniform
continuity preserves the two strict barriers for the entire parameter
cube at one sufficiently small t.

For the map `T(x,rho)=(F_t(rho*x)/h, clip(2rho-h))`, where h is total
output mass, the direction component stays in K. At rho=ell the inner
barrier gives 2ell-h>ell, so clipping cannot return ell. At rho=u the
outer barrier gives 2u-h<u, so clipping cannot return u. An interior
fixed radius must satisfy 2rho-h=rho: if the input to clipping lay
outside the interval, its output would be an endpoint. Thus h=rho,
and the direction equation gives an EXACT fixed point of F_t.
This rejects the possible endpoint and scaled-eigenpoint loopholes.

The generic operation is already supported by the inspected theorem
`Math.exists_fixedPoint_of_normalized_radial_map` in
`MathUE/Topology/NormalizedRadialFixedPoint.lean`. The note uses a
slightly different but valid clipped radial coordinate; its stronger
outer mass inequality also implies that theorem's outer scaled-eigenpoint
exclusion. The new work is the raw reward field and its uniform shell
hypotheses, not a new abstract Brouwer theorem.

## 3. Uniformity and the finite-player extensions

For a fixed parameter set, the shell and t0 depend only on the supplied
singleton data, a and R. Shrinking t0 to ensure t*u<1 produces genuine
positive hazards strictly below one. For a compact family inside the
strict open matrix/coefficient region, inversion is continuous, its
entries have one positive lower and finite upper bound, and the a_i
have one positive lower bound. The same K, radii, positive component
minimum, polynomial bound and strict mass margins therefore work for
the entire family. No uniformity towards a zero inverse entry or zero
coefficient is claimed or follows.

Section 10.1 uses t=M^(-1/d), giving exactly the above constant term
and a polynomial residual because d is a positive integer. Section
10.2 uses one t=1/L and cancels each recipient-specific t^(-d_i) pole
separately. Its mixed-degree bounds are valid as checked above. All
selected coalitions have at least two members, which is essential for
the radial degrees to exceed one. The conditions may be vacuous for
some small player counts or matrices; no nonempty-region assertion is
needed for the stated conditional raw theorem.

## 4. Actual payoff, Never and unrestricted agency

Independently rearranging the actual value formula gives

    U_i-Q_i=-(1-q_i)H_i/[1-(1-q_i)alpha_i].

At H_i=0, U_i=Q_i and B_i=(1-alpha_i)U_i. Every deleted-opponent
system has alpha_i<1 because n>=2 and every opponent hazard is positive.
Thus every pure finite deadline has payoff U_i, and Never has payoff
B_i/(1-alpha_i)=U_i. The unique continuing history identifies any
complete behavioral replacement with a private mixture of deadlines
and Never; equivalently Bellman iteration leaves only a bounded
alpha_i^N remainder, uniformly over the replacement. This remains
valid when singleton rewards or U_i are negative: the opponents are
proper, so Never does not create a positive-probability zero-payoff
escape event.

The finite-average consumer is also uniform over complete replacements.
Their actual absorption time is bounded above by the opponents' first
absorption time, whose geometric expectation is finite. For the fixed
finite table the expected finite-average/terminal discrepancy is at
most 2C times that expectation divided by the horizon, with an
inessential indexing adjustment. Thus the same profile and actual U
give the fixed uniform payoff claimed. M or L is fixed as part of the
original table before the horizon or requested error changes.

The inspected semantic consumers are
`isZeroAsymptoticNash_stationary_of_fixedPoint_endpointNash_contracts`
and `isUniformEquilibriumPayoff_of_stationaryEndpointCertificate_contracts`
in `UniformEquilibrium/Quitting/Stationary/EndpointCompiler.lean`.
The present raw producer remains ordinary mathematics, not a checked
Lean declaration. It supplies a strict reward-table class, not the
finite-quitting conjecture for arbitrary data.
