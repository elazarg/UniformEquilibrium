# Independent review: complete responses across a negative return boundary

Reviewer: CLOCK_CONTRACTION. Ordinary mathematics; no Lean build.

Final artifact reviewed: `math/exports/FINITE_SINGLETON_SPLIT_UNIFORM_EQUILIBRIUM.md`,
assembled at `/tmp/FINITE_SINGLETON_SPLIT_UNIFORM_EQUILIBRIUM.md`, SHA256
`16c3ad54f6d442d0440f8e3a5e29ed06bd81101b2dd054cb3dea6fa4a93519b8`.

**Verdict: mathematical PASS.** I reviewed the entire final artifact, including
the finite-core producer, the complete parameter interval, all behavioral
responses, the negative-boundary timing restriction, and the coverage
appendix. No unresolved mathematical objection remains. This produces UE
on the stated raw class; it does not prove arbitrary Fin4.

## Raw input and internal selection

The eight singleton signs make the displayed denominators positive once
C>0. They give 0<C<k and 0<a,b<1. The two strict C,J inequalities give
A1>0 and A2>0 without any sign assumption on B1. The interval in Section1
is a genuine finite affine raw-data test; midpoint selection internally
supplies its hazard. The sufficient closed formulas for L,U imply L<U
and U<=a, and correctly handle B1>=0 as a sufficient, not necessary, test.

The ten core remainders, seven bounded row0 joining cells, three newly
queried joining cells and eighteen free nonpivot joining cells account for
all44 higher-coalition rewards. The supplied data are reward entries only.
No successful continuation, Nash root, cycle, or limiting orbit is assumed.

The weak inequality zeta2<=f is sound even at equality. The finite core
has C_N2=0 exactly and the solo2 root preserves B_N2=0 exactly. Thus the
new root has X_N2=x*f, and its row2 comparison is exact for every finite N.
It does not rely on a strict limit inequality surviving approximation.

## Finite-core production and coverage of all large K

I checked the root payoff equations, the theta/Jcore coordinate change,
and the backwards Y equation. In particular C4 follows directly by setting
the current required row3 successor equal to the next immediate-Quit value;
its denominator is positive near the reference data and its backwards
linear coefficient is u/(u+d1)<1. The reference Y,Z sign argument remains
valid for negative v as written, and does not use Gamma12>0.

The Banach array estimates have a uniform contraction bound because Nt
vanishes geometrically. The separate convolution estimate C7, with eta
larger than both delta and the backwards contraction, justifies the scaled
entrance C8. This does not assume that the backwards contraction is faster
than delta. I independently checked the first-order fcore coefficient at
t=theta=0; the beta terms cancel and the coefficient is precisely the
printed -h*Lambda*Gamma21*m*J/c.

The entrance coefficient in C9 is uniformly positive under q0>a0*Gamma21.
The two outer equations reduce to the displayed affine equation in C and
linear equation in J. Their Jacobian and the positive C-to-E0 derivative
are independent of B1's sign. The finite-dimensional implicit selection
therefore supplies the actual branches on the full compact phase and h
rectangle.

The physical-hazard argument C14 uses the uniform sign of
q-a0*Gamma21 and is valid also at p=0 and at the compactification endpoint.
Only h>0 is executed. Terminal Y,Z boundary signs, the finite solo3 wash,
and the exact deletion of the last pure3 root supply the joined K intervals.
The proof supplies every sufficiently large K/(1+|p|), not only a sequence.
The selected split changes neither the entrance nor either outer equation,
so deletion and gluing remain literal identities.

## Exact concentrated step and the negative boundary

I independently verified in exact rational arithmetic

    F2^(5/9)(5/4,-7/8,0,0)=(0,-1/9,0,5/9),
    F0^(1/10)(0,-1/9,0,5/9)=(0,1/10,1/5,2/5),
    F0^(2/7)(0,1/10,1/5,2/5)=(0,9/14,5/7,0).

The three finite0 offers are (-1/10,-1,1/10), with the printed strict
margins (1/5,6/5,3/10). The finite2 offer -5K/9 is below -1/9 for K>=1/5.
These checks are for the limiting calibration; the theorem correctly uses
the strict margins and finite-core convergence for its existential threshold.
It does not infer that K=100 lies above that threshold.

In the general construction, multiplying the two solo0 survival factors
gives exactly 1-a_N. Hence the new execution preserves all payoff and return
identities. Its thin part has nonnegative annotations throughout, because
its quiet values are affine in cumulative survival between two nonnegative
endpoint vectors. The only negative row1 annotation lies after the retained
finite0 date and before the retained finite2 date. The proof does not insert
an extra date there. Immediate quitting there means joining the actual
finite2 hazard, with offer -K*b_N; it does not give the free singleton zero.
This timing distinction is essential and is correctly retained.

The interval -1/6<ell<4 was checked independently from the rational formulas
C=5/4, J=1-ell/4 and B1=(6ell-4)/9. No core estimate uses ell>0 separately.
The lower split endpoint and upper joining endpoint coincide at ell=-1/6;
the theorem makes no boundary or uniform-threshold assertion there.

## Full behavioral and fixed-target audit

For a fixed game, the finite core and reference payoff A_N are selected
before the refinement accuracy. Only the two indicated thin blocks are
subdivided; the finite roots remain adjacent. All prescribed payoff equations
remain exact. At each refined root, the active owner is indifferent, and
only the thin0 quiet joining comparisons can have the stated mesh error.

Against the literal periodic law, a complete unilateral behavioral strategy
is a mixture of pure stopping deadlines and Never. The Bellman maximum
therefore prices every deviation. At each root its excess over the reference
value is bounded by the maximum of the local error and the opponents-only
survival times the next excess. Over a period every player faces opponent
absorption at least min(a_N,b_N)>0: player0 faces finite2, and each other
player faces the combined solo0 mass. Thus the stated scalar cap inequality
forces full regret at most the mesh error, with no accumulation in period
length. Proper absorption also identifies the exact prescribed payoff with
the reference annotations.

Adding original own levels is justified only after this opponent absorption
has been proved; every prescribed and deviating terminal outcome absorbs.
The finite-horizon estimate is uniform over complete deviations because
opponents alone have a geometric period survival bound. The target
kappa+A_N remains fixed while mesh and horizon threshold vary. This proves
the intended uniform-payoff quantifiers.

The artifact correctly declines to use the stronger singleton-floor
hypothesis of MixedCycleSoloMesh.SourceCertificate at the negative boundary.
I inspected that declaration and its explicit singleton_floor field, as well
as the cited complete root-cap and terminal-selection interfaces. No new
Lean verification is claimed.

## Complete coverage appendix

I audited the stationary and sure-root necessary systems, including the
original-game AllNever comparison: subtracting the own level one gives -1
on that event, so L_i=min(-1, passive native rewards) is the correct lower
bound for an arbitrary actual continuation cap. The K-monotonicity formulas
relax only row1, and the single-owner and q0=0 mixed2 exclusions do not use
an omitted constraint. The inverse-combination origin estimate is valid
because the relevant relaxed inverse column is nonnegative.

The Bernstein conversion, positive-denominator clearing, exact subdivision
and strict sign rejection are sound. I reran

    python /tmp/split_coverage_independent.py --uniform-k 0 10

and obtained the advertised 862 stationary nodes and365 sure-root nodes,
with all80 and all65 patterns excluded. I also inspected that checker's
complete rational table and polynomial construction.

I also checked the final stationary-approximation paragraph. At a nonzero
hazard limit, the exact stationary payoff identity and the Quit/Never tests
give the required F signs whenever H_i<1; if H_i=1 then F_i=0 directly.
At a zero-hazard limit, normalization by total hazard makes prescribed native
payoffs tend to Gamma*x. Immediate quitting gives Gamma*x>=0, and Never
forces complementarity on every positive coordinate when the support has
size at least two. A singleton support fails a negative column entry, and
all larger supports fail principal nonsingularity. This proves a positive
stationary regret floor for each FIXED table; no floor uniform in K is
claimed or inferred.

Separate exact matrix calculations verified the displayed inverse, the
unique required-sign labeling among all24 permutations, the sole
nonnegative-inverse child023 and its outside row(-7/10,9/10,-1/5).
The ledger exclusions, intersecting reciprocal pairs and three alternating-
pair failures were checked directly from the table. Their scope is the named
raw producers, not every possible nonstationary architecture. The checked
interface comparisons are stated with their actual hypotheses.

The result is consequently an actual new raw-class exclusion, rather than
a local optimization result or a conditional continuation verifier. Numerical
finite-clock experiments played no role in this review's proof acceptance.
