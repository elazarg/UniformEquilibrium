# Quotient and secant reductions: immediate refinements and theorem value

## Scope

The two complete proof reviews stand. The refinements below are immediate
consequences of those proofs, not a new route to the conjecture. Final
assembly must preserve their quantifiers and distinguish a raw-table UE
producer from a counterexample-preserving source reduction.

## 1. Arbitrary finite polynomial avoidance at the secant entrance

The secant construction may require in advance

    P_1(b) != 0, ..., P_l(b) != 0

for any supplied finite collection of nonzero rational polynomials in
the 56 frozen coordinates. No particular screened-root polynomial is
needed for this conclusion.

Proof: single-pivot normalization and a sufficiently small common positive
scale provide a pair (b_0,t_0) in the open unit box, with t_0>0,
three other own singletons zero, and eta(r_(b_0)^(t_0))>0. Uniform reward
continuity supplies an open product neighborhood U times V on which the
gap stays positive and the same unit bounds and singleton signs hold.
The product P_1 ... P_l is nonzero. Its zero set has empty interior:
a real polynomial vanishing on an open box is the zero polynomial,
as follows by applying the univariate identity theorem successively
to its coordinates. Its complement is also open. Therefore U contains
a nonempty open subset avoiding every zero set and hence contains a
rational b avoiding them. Independently choose rational t in V.

The function e, descending window, tilt, limiting xi, and entire
common-calendar source are then constructed afresh for this b. All
original secant conclusions follow unchanged. This does not perturb
an already selected optimum or assert stability of its chosen weights.

The safe scope is finite polynomial conditions on the 56 frozen entries.
Arbitrary countable families cannot be substituted while demanding
rational b: the polynomials b_1-q for all rational q already exclude
every rational b. Conditions identically zero on the allowed parameter
slice cannot be avoided. No polynomial avoidance at the final, possibly
irrational xi follows. This refinement supplies no screened-root gap
unless the corresponding polynomial's separate mathematical property
is also proved.

## 2. A weaker raw guard for the quotient's exact-stationary conclusion

Assume the quotient root-producer hypotheses RI, R0 of A, and
kappa(A) != 1. Replace the requirement that every singleton-block
player have a nonnegative own singleton by the following weaker guard:

For each singleton-block player i with s_i<0, there is no h satisfying

    0 < h <= 1,
    r_j({i}) >= (1-h)s_j + h r_j({i,j})  for every j != i.  (G)

This is a finite collection of one-variable linear feasibility tests
with one strict endpoint constraint. Under this guard, every nonzero
fixed point of the quotient map is an exact stationary terminal Nash
equilibrium against all behavioral replacements, and the same profile
is uniform at its payoff.

Indeed a sole-owner hazard q=h e_i has Delta_i=0 and

    Delta_j = h[(1-h)s_j+h r_j({i,j})-r_j({i})], j != i.

Thus its inactive-player endpoint conditions are exactly (G).
A sole owner of a block-constant root must belong to a singleton
block. The guard excludes precisely the negative sole-owner roots,
which are the only produced Nash--Bellman roots with a missing Never
inequality. Every remaining root has either at least two positive
original hazards, so all deleted clocks contract, or a nonnegative
sole owner. The existing complete-cap and finite-average arguments
then apply directly.

The original nonnegative-singleton-block hypothesis makes this guard
vacuous. Failure of the guard does not imply failure of exact stationary
equilibrium: it permits a bad sole-owner root but does not exclude
other good roots. The signed Fin4 UE consequence needs no change.

The tracked interface is `IsQuittingStationaryBoundaryAdmissible` and
the exact endpoint/boundary characterization in
`UniformEquilibrium/Quitting/Stationary/EndpointCompiler.lean`.
This refinement uses its existing boundary distinction, not a new
strategy-class completeness claim.

## 3. Export value and exact remaining claims

The quotient result is a raw-table producer: RI is a finite linear
coefficient test on reward data, the quotient is explicitly constructed,
and its degree mismatch produces the stationary root. Under the stated
finite-player boundary conditions, or unconditionally for signed Fin4
through the existing contrary no-UE normality source, an ordinary UE
payoff follows. No favorable stationary witness is supplied as an input.
The paired completion class lies strictly inside the full-matrix R0,
degree +1 residual and leaves 33 nonsingleton coordinates and four own
singletons free. Neither all completions of its matrix nor all degree
+1 matrices are covered.

The ambient zero-discount min-map degree argument already occurs in
the internal stationary-repair account. The additional contribution is
the response-invariant partition, its quotient obstruction, and the
resulting strict degree-one class. A narrow search of the tracked
Stationary and LCP classification subtrees found no matching quotient
criterion. This is a bounded source comparison, not a priority claim.

The secant result is a genuine counterexample-preserving reduction.
From any hypothetical Fin4 counterexample it produces the allowed
single-pivot table, a universal pivot-singleton secant bound, and actual
near-minimizers with their own tester weights, strict pivot pressure,
and a finite nearly best pivot reply. No favorable profile, pressure
field, limiting law, or response is an unexplained premise.

Its value is not an unconditional UE class. The produced delay-only
move loses a fixed amount of pivot singleton mass while nearly
preserving the pivot payoff and exactly preserving its cap. The other
three complete caps remain uncontrolled, so the source is not known
to regenerate, lower complete maximum regret, or define a renewable
rank. Strict pivot pressure replaces rather than augments the old
nonpositive total-pressure conclusion.

Both results therefore have meaningful but different gate value. The
quotient is a sufficient raw-table UE theorem; the secant is a source
reduction with an explicit unresolved consumer. Their assembled packets
must be self-contained about those mathematical statements and must not
inherit specific untracked generic-polynomial properties or amplify the
direct-map argument into an unsupported novelty claim.
