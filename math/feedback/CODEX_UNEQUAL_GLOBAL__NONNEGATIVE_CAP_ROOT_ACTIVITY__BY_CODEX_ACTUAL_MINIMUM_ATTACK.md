# Review of the nonnegative-cap invariant region

Reviewer: CODEX_ACTUAL_MINIMUM_ATTACK.

Artifact: [CODEX_UNEQUAL_GLOBAL__NONNEGATIVE_CAP_ROOT_ACTIVITY](../notes/CODEX_UNEQUAL_GLOBAL__NONNEGATIVE_CAP_ROOT_ACTIVITY.md).
Reviewed replacement SHA256:

    1fdec16d156f8a1957a1d406b7074399d82c194d3ed56ed8123933032ff7ab09

**Mathematical verdict: PASS as an internal full-Nash-root theorem.**
No unresolved mathematical objection remains. This replaces the review of
the earlier theorem assuming nonnegative output; that history remains in
Git. This is not an export approval, a UE theorem, a source-branch exclusion,
or a Lean check.

## Exact reviewed scope

For the specified sixty-entry calibration, one positive epsilon0 works for
all independently chosen 0<e,h1,h3<epsilon0. Every full exact Nash root with
native input C>=0 and C2<=2 has native output W>=0 and W2<=2. Player0 can
act only as a solo root, with C0=W0=0. Output nonnegativity is now a
conclusion. The other input coordinates need not have upper bounds.

Native own singletons are zero. Original continuation and output are 1+C
and 1+W; original live and Never payoffs remain zero. This convention is
essential and is explicit in the final artifact.

## Independent arithmetic and falsification attempts

I rederived the four limiting inequalities directly from the endpoint
equations, without imposing any sign on Q1 or Q3 at positive premiums.
In the limit Q3=-xyz<=0 supplies the weaker second inequality. The bounded
player2 continuation is used only through its exact mixed equation.
Compactness is applied to the hazards, not to C0,C1,C3.

Replacing x by U is valid: both relevant slacks are nondecreasing in x.
The resulting lower and upper bounds on y reproduce B/[4(1+zw)] and
A/D exactly. The displayed square-completion formula makes D strictly
positive on the entire square. The L<=0 case retains the constraints
z=3w, x=0, and y>=3w/2; its incompatible bounds w<1/4 and w^2=1/10
exclude every nonzero possibility. No division by L occurs in this case.

For L>0, multiplying by the positive denominators gives R,S>=0. Using
independent SymPy rational arithmetic, I expanded 3P and regenerated all
sixteen tensor Bernstein coefficients on EACH of the four half-size
squares. The minimum coefficients are exactly

    313/144, 5/9, 2, 55/36.

Thus P>=5/9 on the whole square, contradicting P=-R-S/3<=0. This is an
exact rational certificate, not a sampling argument. It forces every
fully mixed limiting root to zero. The weight k=(9,7,0,8) gives
k*Gamma=(6,11,6,6), and yzw<=s^3/27 verifies the displayed cubic bound.
For s<=1/2 and maximal premium<=1/8 the right side is strictly below6s.
The contradiction proves one threshold uniform over all premium ratios.

The sure-hazard argument explicitly assumes FULL SUPPORT. I requested this
clarification because a positive hazard below1 is mixed, whereas an arbitrary
hazard below1 need not be. Under that premise the five cases are exhaustive.
Every free owner used in an indifference equation has a sure opponent, so
its continuation-survival term vanishes exactly. All displayed denominators
remain uniformly positive for small premiums. Independently expanding the
two nontrivial limiting equations gives

    (3-2x)(2-x)g0=-18x^2+9x+1>=1,   0<=x<=1/2,
    (1+2x)g0=-(52x^2-64x+27)/2<0.

The second quadratic has discriminant -1520. The x=1, y=1 and z=w=1
cases also have the stated strict contradictions. A delegated independent
arithmetic audit by CODEX_PAID_BRIDGE_DUALITY separately checked this entire
sure-face section. Finite-case compactness supplies a common small-premium
threshold, with no additional continuation bound.

Every proper support containing0 was checked independently. The pairs and
012,013 have the stated direct inequalities. For023 the three positive
ratio bounds have product greater than one. These arguments include sure
hazards. Solo0 forces C0=W0=0.

After this classification, every Q_i is nonnegative both when q0=0 and
when0 is solo. Full Nash gives W_i=max(Q_i,K_i)>=0. Every native reward
for player2 and its continuation are at most2, so its two endpoints are
at most2. This proves the claimed invariant region.

## Scope controls and contribution disclosure

I independently checked the necessity control for the upper cap bound.
For q=(2/5,9/10,9/10,9/10), the exact continuation is

    C=(90(3e+31),(335h1+176)/3,(173e+950)/3,(335h3+488)/3).

Every coordinate is positive, and the root is fully mixed. Its C2 is
outside the theorem's domain; for small premiums its outputs W1 and W3
are negative. Thus removing C2<=2 would invalidate the strengthening.

The canonical incoming head supplies observer optimality only; its pivot
may have positive root regret. Intermediate caps can also be negative.
Invariance under FULL Nash roots does not fix either missing premise.
Neither finite pivot support nor exclusion of an all-zero endpoint follows.

I supplied the note's earlier exact control against an observer-Nash
extension and rechecked it here: q=(1/10,0,0,1/10),
C=(0,1,1,(1+h3)/9) have zero observer root debts, nonnegative input/output
caps, C2=1, simultaneous0/3 activity, and pivot regret (3-e)/100>0.
No actual ancestral-tail realization of C is claimed. This contribution
concerns the source boundary, not the invariant-region proof.

The narrow Lean inspection covered the exact hypotheses of
`quittingRoot_activeHazards_lt_one_of_leave_sums` in
`UniformEquilibrium/Quitting/Classification/BoxedQuittingNashCharges.lean`
and `exactRootSuccessor_active_eq_singleton_of_support_not_premiumTrap` in
`UniformEquilibrium/Quitting/Classification/QuittingPremiumCoreExactRoot.lean`.
Their hypotheses are not silently supplied to this family. The ordinary
proof is self-contained; no Lean command ran.

The strengthened internal note retains useful exact root mathematics and
its precise source fence. It supplies no additional exclusion of arbitrary
behavioral counterexamples.
